#!/usr/bin/env bash

for f in *.bpf
do
	r=`../../tools/bpf/bpf_asm -c $f | wc -c`
	n=`basename $f .bpf`
	printf "\\\\newcommand{\\\\nbytesbpf%s}{%'d}\n" $n $r
done
