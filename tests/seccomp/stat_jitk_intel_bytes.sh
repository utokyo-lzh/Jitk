#!/usr/bin/env bash

for f in *.bpf
do
	r=`../../tools/bpf/bpf_asm -c $f | ../gen-i386.sh /proc/self/fd/0 | wc -c`
	n=`basename $f .bpf`
	printf "\\\\newcommand{\\\\nbytesjitkintel%s}{%'d}\n" $n $r
done
