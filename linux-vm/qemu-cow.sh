#!/bin/sh

qemu-img create -f qcow2 -b fs.img temp.img
trap "rm -f temp.img" 0 1 2 3 14 15

qemu-system-x86_64 \
    -hda ./temp.img \
    -kernel ../../jitk-linux/arch/x86/boot/bzImage \
    -append "root=/dev/sda init=/init.sh" \
    -m 128 \
    -redir tcp:9922::22 \
    -serial telnet:localhost:12345,server,nowait

