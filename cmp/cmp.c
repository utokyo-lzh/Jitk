#include <stddef.h>

int bcmp(const unsigned char *s1, const unsigned char *s2, size_t n)
{
	size_t i;

	for (i = 0; i < n; ++i) {
		if (s1[i] != s2[i])
			return 1;
	}
	return 0;
}

int hashcmp(const unsigned char *s1, const unsigned char *s2, size_t n)
{
	size_t i;
	int diff = 0;

	for (i = 0; i < n; ++i)
		diff |= s1[i] ^ s2[i];
	return diff;
}
