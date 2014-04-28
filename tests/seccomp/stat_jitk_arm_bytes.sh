#!/usr/bin/env bash

for f in *.bpf
do
	r=`../../tools/bpf/bpf_asm -c $f | ../gen-arm.sh /proc/self/fd/0 | wc -c`
	n=`basename $f .bpf`
	printf "\\\\newcommand{\\\\nbytesjitkarm%s}{%'d}\n" $n $r
done
