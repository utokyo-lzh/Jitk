#!/usr/bin/env bash

for f in *.bpf
do
	r=`../../tools/bpf/bpf_asm -n $f | ../gen-ppc.sh /proc/self/fd/0 | wc -c`
	n=`basename $f .bpf`
	printf "\\\\newcommand{\\\\nbytesjitkppc%s}{%'d}\n" $n $r
done
