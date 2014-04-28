#!/usr/bin/env bash

for f in *.bpf
do
	r=`../../tools/bpf/bpf_asm -c $f | ../../src/linux-arm/bpf_jit 2> /dev/null | wc -c`
	n=`basename $f .bpf`
	printf "\\\\newcommand{\\\\nbyteslinuxarm%s}{%'d}\n" $n $r
done
