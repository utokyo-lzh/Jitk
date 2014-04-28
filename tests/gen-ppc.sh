#!/bin/sh
objfile=$(mktemp)
prefix="powerpc-linux-gnu-"

$(dirname "$0")/test_gen.native "$1" | ${prefix}as -o $objfile -
${prefix}objcopy -O binary -j .text $objfile /proc/self/fd/1

rm -f $objfile
