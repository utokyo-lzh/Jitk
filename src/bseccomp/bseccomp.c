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

#define replace_fd		m_replace_fd
#define create_pipe_files	m_create_pipe_files
static int (*m_replace_fd)(unsigned fd, struct file *file, unsigned flags);
static int (*m_create_pipe_files)(struct file **, int);

struct umh_params {
	struct file *stdin;
	struct file *stdout;
};

static int umh_pipe_setup(struct subprocess_info *info, struct cred *cred)
{
	struct file *outs[2];
	int err, fd;
	struct umh_params *up = (struct umh_params *)info->data;

	err = create_pipe_files(outs, 0);
	if (err) {
		pr_info("%s: create_pipe_files failed %d\n", __func__, err);
		return err;
	}

	up->stdout = outs[0];

	fd = replace_fd(1, outs[1], 0);
	fput(outs[1]);

	if (fd < 0) {
		pr_info("%s: replace_fd failed %d\n", __func__, err);
		err = fd;
	}

	return err;
}

static void test_upcall(void)
{
	char *argv[] = {
		"/bin/bash",
		"-c",
		"/bin/date",
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
}

static int __init bseccomp_init(void)
{
	m_replace_fd = (void *)0xc1190510;
	m_create_pipe_files = (void *)0xc117e240;

	test_upcall();

	return 0;
}

static void __exit bseccomp_cleanup(void)
{
}

module_init(bseccomp_init);
module_exit(bseccomp_cleanup);

MODULE_LICENSE("GPL");
