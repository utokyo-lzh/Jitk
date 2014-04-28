#!/bin/sh
objfile=$(mktemp)

$(dirname "$0")/test_gen.native "$1" | as --32 -n -o $objfile -
objcopy -O binary -j .text $objfile /proc/self/fd/1

rm -f $objfile
