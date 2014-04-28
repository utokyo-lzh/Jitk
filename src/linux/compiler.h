#pragma once

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <err.h>

typedef uint8_t		u8;
typedef uint16_t	u16;
typedef uint32_t	u32;
typedef uint64_t	u64;

#define __read_mostly
#define __user
#define __maybe_unused

#define likely(x)	(x)
#define unlikely(x)	(x)

#define ARRAY_SIZE(x)	(sizeof(x)/sizeof(x[0]))

#define GFP_KERNEL	0

#define kzalloc(size, dummy)	calloc(1, size)
#define module_alloc(size)	malloc(size)
#define module_free(dummy, p)	free(p)
#define kfree(p)		free(p)

#define ENOTSUPP	1

extern unsigned int elf_hwcap;

#define HWCAP_IDIVA	(1 << 17)

static inline u32 rol32(u32 word, unsigned int shift)
{
	return (word << shift) | (word >> (32 - shift));
}

static inline u32 ror32(u32 word, unsigned int shift)
{
	return (word >> shift) | (word << (32 - shift));
}

#define fls __fls

static inline int __fls(int x)
{
	return x ? sizeof(x) * 8 - __builtin_clz(x) : 0;
}

/* little endian */
#define __opcode_to_mem_arm(x)	(x)
