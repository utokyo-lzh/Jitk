#!/usr/bin/env bash

for f in *.bpf
do
	r=`../../tools/bpf/bpf_asm -h $f | ../../src/linux/bpf_jit_arm 2> /dev/null | wc -c`
	n=`basename $f .bpf`
	printf "\\\\newcommand{\\\\nbyteslinuxarm%s}{%'d}\n" $n $r
done
