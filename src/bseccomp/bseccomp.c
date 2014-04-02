/*
 * This is the kernel stub for supporting binary seccomp filters.
 *
 * It creates the following files under /proc/seccomp.
 * 
 * enabled: write 1/0 into it to enable/disable binary filters.
 * binary_filter: write a binary filter for the calling process.
 *
 * When `enabled' is set, this module intercepts sk_run_filter()
 * if the calling function is __secure_computing(), and invokes
 * a binary filter rather than BPF.
 */

#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/init.h>
#include <linux/ftrace.h>
#include <linux/proc_fs.h>
#include <linux/seq_file.h>
#include <linux/slab.h>
#include <linux/uaccess.h>

#define BASE_DIR "seccomp"

static int enabled;

static DEFINE_MUTEX(enabled_mutex);

static int enabled_show(struct seq_file *m, void *dummy)
{
	seq_putc(m, '0' + enabled);
	seq_putc(m, '\n');
	return 0;
}

static int enabled_open(struct inode *inode, struct file *file)
{
	return single_open(file, enabled_show, NULL);
}

/* this is compatible with the original struct */
struct seccomp_filter {
	atomic_t usage;
	struct seccomp_filter *prev;
	unsigned short len;
	void *insns;
};

static int binary_run_filter(void *dummy, void *insns)
{
	pr_info("%s\n", __func__);
	// TODO: maybe set some magic number - pad nops or allocate
	// code at some specific address, and we can run it as either
	// binary or BPF.
	return SECCOMP_RET_ALLOW;
}

static void notrace seccomp_ftrace_handler(
        unsigned long ip, unsigned long parent_ip,
        struct ftrace_ops *op, struct pt_regs *regs)
{
	char str[KSYM_SYMBOL_LEN];

	sprint_symbol_no_offset(str, parent_ip);
	/* skip if not calling from seccomp (e.g., packet_rcv) */
	if (strcmp(str, "__secure_computing"))
		return;

	preempt_disable_notrace();
	/* hijack sk_run_filter */
	regs->ip = (unsigned long)binary_run_filter;
	preempt_enable_notrace();
}

static struct ftrace_ops seccomp_ftrace_ops __read_mostly = {
	.func = seccomp_ftrace_handler,
	.flags = FTRACE_OPS_FL_SAVE_REGS,
};

static int seccomp_ftrace_enabled;

#define secure_computing_name "sk_run_filter"
static unsigned long secure_computing_addr;

/* called with enabled_mutex */
static int arm_seccomp(void)
{
	int ret;

	ret = ftrace_set_filter_ip(&seccomp_ftrace_ops, secure_computing_addr, 0, 0);
	if (ret) {
		pr_warn("%s: ftrace_set_filter_ip failed, return %d\n", __func__, ret);
		return ret;
	}
	if (++seccomp_ftrace_enabled == 1) {
		ret = register_ftrace_function(&seccomp_ftrace_ops);
		if (ret) {
			pr_warn("%s: register_ftrace_function failed\n", __func__);
			return ret;
		}
	}
	pr_info("%s: `%s' armed\n", __func__, secure_computing_name);
	return 0;
}

/* called with enabled_mutex */
static int disarm_seccomp(void)
{
	int ret = 0;

	if (!--seccomp_ftrace_enabled) {
		ret = unregister_ftrace_function(&seccomp_ftrace_ops);
		if (ret) {
			pr_warn("%s: unregister_ftrace_function failed, return %d\n", __func__, ret);
			return ret;
		}
	}
	ret = ftrace_set_filter_ip(&seccomp_ftrace_ops, secure_computing_addr, 1, 0);
	if (ret) {
		pr_warn("%s: ftrace_set_filter_ip failed, return %d", __func__, ret);
		return ret;
	}
	pr_info("%s: `%s' disarmed\n", __func__, secure_computing_name);
	return 0;
}

static ssize_t enabled_write(struct file *file, const char __user *user_buf,
			     size_t count, loff_t *off)
{
	char buf[4];
	size_t buf_size = min(count, (sizeof(buf) - 1));
	bool bv;
	ssize_t ret;
	int armed;

	if (*off)
		return -EINVAL;
	if (copy_from_user(buf, user_buf, buf_size))
		return -EFAULT;
	buf[buf_size] = 0;
	if (strtobool(buf, &bv))
		return -EINVAL;

	mutex_lock(&enabled_mutex);

	ret = count;
	/* already done */
	if (enabled == bv)
		goto out;

	if (bv)
		armed = arm_seccomp();		/* install jprobe */
	else
		armed = disarm_seccomp();	/* uninstall jprobe */
	if (armed) {
		ret = armed;
		goto out;
	}

	/* succeed */
	enabled = bv;

out:
	mutex_unlock(&enabled_mutex);
	return ret;
}

static const struct file_operations enabled_fops = {
	.open		= enabled_open,
	.read		= seq_read,
	.llseek		= seq_lseek,
	.release	= single_release,
	.write		= enabled_write,
};

static int bfilter_show(struct seq_file *m, void *dummy)
{
	return 0;
}

static int bfilter_open(struct inode *inode, struct file *file)
{
	return single_open(file, bfilter_show, NULL);
}

static ssize_t bfilter_write(struct file *file, const char __user *buf, size_t count, loff_t *off)
{
	struct seccomp_filter *filter;

	/* enable first */
	if (!enabled)
		return -EPERM;
	/* code too large */
	if (count > USHRT_MAX)
		return -EINVAL;
	/* offset must be zero */
	if (*off)
		return -EINVAL;

	filter = kzalloc(sizeof(struct seccomp_filter) + count, GFP_KERNEL | __GFP_NOWARN);
	if (!filter)
		return -ENOMEM;

	atomic_set(&filter->usage, 1);
	filter->len = (unsigned short)count;
	if (copy_from_user(filter->insns, buf, count)) {
		kfree(filter);
		return -EFAULT;
	}

	/* is it really useful to support multiple filters? */
	filter->prev = current->seccomp.filter;
	current->seccomp.filter = filter;
	return count;
}

static const struct file_operations bfilter_fops = {
	.open		= bfilter_open,
	.read		= seq_read,
	.llseek		= seq_lseek,
	.release	= single_release,
	.write		= bfilter_write,
};

static int __init bseccomp_init(void)
{
	struct proc_dir_entry *base_dir;

	secure_computing_addr = kallsyms_lookup_name(secure_computing_name);
	if (!secure_computing_addr) {
		pr_info("%s: failed to locate `%s'\n", __func__, secure_computing_name);
		return -ENOTSUPP;
	}

	base_dir = proc_mkdir(BASE_DIR, NULL);
	if (!base_dir)
		return -ENOMEM;
	if (!proc_create("enabled", 0000, base_dir, &enabled_fops))
		goto cleanup;
	if (!proc_create("binary_filter", 0000, base_dir, &bfilter_fops))
		goto cleanup;
	return 0;

cleanup:
	remove_proc_subtree(BASE_DIR, NULL);
	return -ENOMEM;
}

static void __exit bseccomp_cleanup(void)
{
	remove_proc_subtree(BASE_DIR, NULL);
}

module_init(bseccomp_init);
module_exit(bseccomp_cleanup);

MODULE_LICENSE("GPL");
