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
#include <linux/filter.h>
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
	u8 insns[];
};

#define SYM_RUN_FILTER			"sk_run_filter"
#define SYM_PARENT_RUN_FILTER		"__secure_computing"
#define SYM_ATTACH_FILTER		"seccomp_attach_user_filter"
#define SYM_PARENT_ATTACH_FILTER	"prctl_set_seccomp"
static unsigned long addr_run_filter;
static unsigned long addr_parent_run_filter;
static unsigned long size_parent_run_filter;
static unsigned long addr_attach_filter;
static unsigned long addr_parent_attach_filter;
static unsigned long size_parent_attach_filter;

static int binary_run_filter(void *dummy, void *insns)
{
	pr_info("%s\n", __func__);
	// TODO: maybe set some magic number - pad nops or allocate
	// code at some specific address, and we can run it as either
	// binary or BPF.
	/* no infinite recusion - parent_ip checking */
	return sk_run_filter(dummy, insns);
}

static long binary_attach_filter(char __user *user_filter)
{
	typedef long (*attach_filter_t)(char __user *user_filter);
	attach_filter_t orig_attach = (attach_filter_t)addr_attach_filter;

	pr_info("%s\n", __func__);
	return orig_attach(user_filter);
}

static void notrace run_ftrace_handler(
        unsigned long ip, unsigned long parent_ip,
        struct ftrace_ops *op, struct pt_regs *regs)
{
	/* skip if not calling from seccomp (e.g., packet_rcv) */
	if (parent_ip < addr_parent_run_filter ||
	    parent_ip >= addr_parent_run_filter + size_parent_run_filter)
		return;

	preempt_disable_notrace();
	/* hijack sk_run_filter */
	regs->ip = (unsigned long)binary_run_filter;
	preempt_enable_notrace();
}

static void notrace attach_ftrace_handler(
        unsigned long ip, unsigned long parent_ip,
        struct ftrace_ops *op, struct pt_regs *regs)
{
	/* avoid recursive calls */
	if (parent_ip < addr_parent_attach_filter ||
	    parent_ip >= addr_parent_attach_filter + size_parent_attach_filter)
		return;

	preempt_disable_notrace();
	/* hijack seccomp_attach_user_filter */
	regs->ip = (unsigned long)binary_attach_filter;
	preempt_enable_notrace();
}


static struct ftrace_ops run_ftrace_ops __read_mostly = {
	.func = run_ftrace_handler,
	.flags = FTRACE_OPS_FL_SAVE_REGS,
};

static struct ftrace_ops attach_ftrace_ops __read_mostly = {
	.func = attach_ftrace_handler,
	.flags = FTRACE_OPS_FL_SAVE_REGS,
};

/* called with enabled_mutex */
static int arm_seccomp(struct ftrace_ops *fops, unsigned long ip, const char *sym)
{
	int ret;

	ret = ftrace_set_filter_ip(fops, ip, 0, 0);
	WARN(ret, "%s: ftrace_set_filter_ip `%s' failed (%d)\n", __func__, sym, ret);
	ret = register_ftrace_function(fops);
	WARN(ret, "%s: register_ftrace_function `%s' failed (%d)\n", __func__, sym, ret);
	pr_info("%s: `%s' armed\n", __func__, sym);
	return 0;
}

/* called with enabled_mutex */
static int disarm_seccomp(struct ftrace_ops *fops, unsigned long ip, const char *sym)
{
	int ret;

	ret = unregister_ftrace_function(fops);
	WARN(ret, "%s: unregister_ftrace_function `%s' failed (%d)\n", __func__, sym, ret);
	ret = ftrace_set_filter_ip(fops, ip, 1, 0);
	WARN(ret, "%s: ftrace_set_filter_ip `%s' failed (%d)", __func__, sym, ret);
	pr_info("%s: `%s' disarmed\n", __func__, sym);
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

	if (bv) {
		armed =	arm_seccomp(&run_ftrace_ops, addr_run_filter, SYM_RUN_FILTER) ||
			arm_seccomp(&attach_ftrace_ops, addr_attach_filter, SYM_ATTACH_FILTER)
			;
	} else {
		armed = disarm_seccomp(&run_ftrace_ops, addr_run_filter, SYM_RUN_FILTER) ||
			disarm_seccomp(&attach_ftrace_ops, addr_attach_filter, SYM_ATTACH_FILTER)
			;
	}
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

#define kallsyms_lookup_size_offset ((lookup_size_offset_t)(addr_lookup_size_offset))
typedef int (*lookup_size_offset_t)(unsigned long, unsigned long *, unsigned long *);
static unsigned long addr_lookup_size_offset;

static unsigned long kallsyms_lookup_name_size(const char *name, unsigned long *symbolsize)
{
	unsigned long addr = kallsyms_lookup_name(name);

	if (addr) {
		unsigned long offset;
		int ret;

		ret = kallsyms_lookup_size_offset(addr, symbolsize, &offset);
		WARN(ret || offset, "kallsyms_lookup_size_offset `%s' (%d)", name, ret);
	}
	return addr;
}

static int __init bseccomp_init(void)
{
	struct proc_dir_entry *base_dir;

	addr_lookup_size_offset = kallsyms_lookup_name("kallsyms_lookup_size_offset");
	addr_run_filter = kallsyms_lookup_name(SYM_RUN_FILTER);
	addr_parent_run_filter = kallsyms_lookup_name_size(SYM_PARENT_RUN_FILTER, &size_parent_run_filter);
	addr_attach_filter = kallsyms_lookup_name(SYM_ATTACH_FILTER);
	addr_parent_attach_filter = kallsyms_lookup_name_size(SYM_PARENT_ATTACH_FILTER, &size_parent_attach_filter);
	if (!addr_run_filter ||
	    !addr_parent_run_filter ||
	    !addr_attach_filter ||
	    !addr_parent_attach_filter) {
		pr_info("%s: failed to locate symbols\n", __func__);
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
