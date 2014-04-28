#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/init.h>
#include <linux/debugfs.h>
#include <linux/filter.h>
#include <linux/slab.h>
#include <linux/uaccess.h>
#include <linux/kallsyms.h>

#define bpf_jit_compile	f_bpf_jit_compile
#define bpf_jit_free	f_bpf_jit_free
static void (*f_bpf_jit_compile)(struct sk_filter *fp);
static void (*f_bpf_jit_free)(struct sk_filter *fp);

static ssize_t jit_write(struct file *file, const char __user *user_buf, size_t count, loff_t *ppos)
{
	char *buf = file->private_data;
	u32 nbytes = buf ? *(u32 *)buf : 4;

	pr_info("bpftest: jit_write: %zd\n", count);

	if (count > UINT_MAX - nbytes)
		return -EINVAL;

	buf = krealloc(buf, nbytes + count, GFP_KERNEL); 
	if (!buf)
		return -ENOMEM;

	if (copy_from_user(buf + nbytes, user_buf, count)) {
		kfree(buf);
		file->private_data = NULL;
		return -EFAULT;
	}

	*(u32 *)buf = (u32)(nbytes + count);
	file->private_data = buf;

	*ppos += count;
	return count;
}

static int jit_release(struct inode *inode, struct file *file)
{
	char *buf = file->private_data;
	u32 nbytes, ninsns;
	struct sk_filter *fp;
	int ret;

	if (!buf)
		return 0;
	nbytes = *(u32 *)buf;
	nbytes -= 4;
	buf += 4;

	pr_info("bpftest: bpf %u bytes\n", nbytes);

	if (nbytes % sizeof(struct sock_filter)) {
		pr_warn("bpftest: incorrect size\n");
		return -EINVAL;
	}

	ninsns = nbytes / sizeof(struct sock_filter);
	pr_info("bpftest: bpf %u instructions\n", ninsns);

	ret = -ENOMEM;
	fp = kzalloc(sizeof(struct sk_filter) + nbytes, GFP_KERNEL);
	if (!fp)
		goto out;
	atomic_set(&fp->refcnt, 1);
	fp->len = ninsns;
	memcpy(fp->insns, buf, nbytes);

	/* otherwise bpf_jit_free() will go crazy */
	fp->bpf_func = sk_run_filter;

	bpf_jit_compile(fp);
	bpf_jit_free(fp);
	ret = 0;
out:
	kfree(buf);
	file->private_data = NULL;
	return ret;
}

static const struct file_operations jit_fops = {
	.owner		= THIS_MODULE,
	.open		= simple_open,
	.write		= jit_write,
	.release	= jit_release,
};

static struct dentry *bpf_debugfs_root;

static int __init bpftest_init(void)
{
	int ret = -ENOMEM;
	struct dentry *jit;

	bpf_debugfs_root = debugfs_create_dir("bpf", NULL);
	if (!bpf_debugfs_root)
		goto dir_fail;

	jit = debugfs_create_file("jit", 0666, bpf_debugfs_root, NULL, &jit_fops);
	if (!jit)
		goto fail;

	ret = -EINVAL;
	f_bpf_jit_compile = (void *)kallsyms_lookup_name("bpf_jit_compile");
	f_bpf_jit_free = (void *)kallsyms_lookup_name("bpf_jit_free");
	if (!f_bpf_jit_compile || !f_bpf_jit_free)
		goto fail;

	return 0;
fail:
	debugfs_remove_recursive(bpf_debugfs_root);
dir_fail:
	return ret;
}

static void __exit bpftest_cleanup(void)
{
	debugfs_remove_recursive(bpf_debugfs_root);
}

module_init(bpftest_init);
module_exit(bpftest_cleanup);

MODULE_LICENSE("GPL");
