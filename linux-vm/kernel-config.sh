#!/bin/sh
#
# Run this script in the top-level directory in the jitk-linux repo,
# then run "make".
#

make defconfig
echo CONFIG_64BIT=n >> .config
echo CONFIG_SMP=n >> .config
make olddefconfig

# shrinking the kernel
echo CONFIG_PARTITION_ADVANCED=n >> .config
echo CONFIG_SUSPEND=n >> .config
echo CONFIG_HIBERNATION=n >> .config
echo CONFIG_ACPI=n >> .config
echo CONFIG_CPU_FREQ=n >> .config
echo CONFIG_YENTA=n >> .config
echo CONFIG_IPV6=n >> .config
echo CONFIG_NET_SCHED=n >> .config
echo CONFIG_HAMRADIO=n >> .config
echo CONFIG_CFG80211=n >> .config
echo CONFIG_AGP=n >> .config
echo CONFIG_DRM=n >> .config
echo CONFIG_FB=n >> .config
echo CONFIG_SOUND=n >> .config
echo CONFIG_USB=n >> .config
echo CONFIG_I2C=n >> .config
echo CONFIG_HID=n >> .config
echo CONFIG_SECURITY_SELINUX=n >> .config
make olddefconfig
