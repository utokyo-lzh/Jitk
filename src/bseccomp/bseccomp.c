#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/init.h>
#include <linux/filter.h>
#include <linux/seq_file.h>
#include <linux/slab.h>
#include <linux/uaccess.h>

#include <linux/file.h>
#include <linux/fs.h>
#include <linux/kmod.h>
#include <linux/pipe_fs_i.h>
#include <linux/kallsyms.h>
#include <linux/kthread.h>

#define replace_fd		m_replace_fd
#define create_pipe_files	m_create_pipe_files
#define flush_delayed_fput	m_flush_delayed_fput
static int (*m_replace_fd)(unsigned fd, struct file *file, unsigned flags);
static int (*m_create_pipe_files)(struct file **, int);
static void (*m_flush_delayed_fput)(void);

struct umh_params {
	struct file *stdin;
	struct file *stdout;
};

static int umh_pipe_setup(struct subprocess_info *info, struct cred *cred)
{
	struct file *ins[2], *outs[2];
	int err, fd;
	struct umh_params *up = (struct umh_params *)info->data;

	err = create_pipe_files(ins, 0);
	if (err) {
		pr_info("%s: create_pipe_files failed %d\n", __func__, err);
		return err;
	}

	err = create_pipe_files(outs, 0);
	if (err) {
		pr_info("%s: create_pipe_files failed %d\n", __func__, err);
		goto put_ins;
	}

	/* replace stdin */
	fd = replace_fd(0, ins[0], 0);
	if (fd < 0) {
		pr_info("%s: replace_fd failed %d\n", __func__, err);
		err = fd;
		goto put_outs;
	}

	/* replace stdout */
	fd = replace_fd(1, outs[1], 0);
	if (fd < 0) {
		pr_info("%s: replace_fd failed %d\n", __func__, err);
		err = fd;
		goto put_outs;
	}

	fput(ins[0]);
	up->stdin = ins[1];

	fput(outs[1]);
	up->stdout = outs[0];

	return 0;

put_outs:
	fput(outs[0]);
	fput(outs[1]);

put_ins:
	fput(ins[0]);
	fput(ins[1]);
	return err;
}

static void test_upcall(void)
{
	char *argv[] = {
		"/bin/bash",
		"-c",
		"/bin/sed 's/abc/123/g'",
		NULL,
	};
	char *envp[] = {
		NULL,
	};
	struct umh_params up = {NULL, NULL};
	loff_t offset = 0;
	int ret = -ENOMEM;

	struct subprocess_info *sub_info;

	sub_info = call_usermodehelper_setup(
		argv[0], argv, envp, GFP_KERNEL,
		umh_pipe_setup, NULL, &up);

	if (sub_info)
		ret = call_usermodehelper_exec(sub_info, UMH_WAIT_EXEC);

	if (ret) {
		pr_info("call_usermodehelper failed %d\n", ret);
		return;
	}

	//file_start_write(up.stdin);
	ret = kernel_write(up.stdin, "abcdef\n", 7, 0);
	pr_info("kernel_write: %d\n", ret);
	//file_end_write(up.stdin);
	fput(up.stdin);
	flush_delayed_fput();

	for (;;) {
		char buf[256];

		ret = kernel_read(up.stdout, offset, buf, sizeof(buf) - 1);
		pr_info("kernel_read %d\n", ret);
		if (ret <= 0)
			break;
		offset += ret;
		buf[ret] = 0;
		pr_info("userspace: %s", buf);
	}

	fput(up.stdout);
}

static int tester_thread(void *data)
{
	test_upcall();
	do_exit(0);
}

static int __init bseccomp_init(void)
{
	m_replace_fd = (void *) kallsyms_lookup_name("replace_fd");
	m_create_pipe_files = (void *) kallsyms_lookup_name("create_pipe_files");
	m_flush_delayed_fput = (void *) kallsyms_lookup_name("flush_delayed_fput");

	printk(KERN_ERR "replace_fd: %p\n", m_replace_fd);
	printk(KERN_ERR "create_pipe_files: %p\n", m_create_pipe_files);
	printk(KERN_ERR "flush_delayed_fput: %p\n", m_flush_delayed_fput);

	kthread_run(&tester_thread, NULL, "bseccomp_test");

	return 0;
}

static void __exit bseccomp_cleanup(void)
{
}

module_init(bseccomp_init);
module_exit(bseccomp_cleanup);

MODULE_LICENSE("GPL");
