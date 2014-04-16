#!/bin/sh
objfile=$(mktemp)

./test_gen.native "$1" | gcc -x assembler - -c -o $objfile
objcopy -O binary -j .text $objfile /proc/self/fd/1

rm -f $objfile
