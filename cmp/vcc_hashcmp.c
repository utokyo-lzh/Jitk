#include <vcc.h>
#include <stddef.h>

int bcmp(const unsigned char *s1, const unsigned char *s2, size_t n)
  _(requires \thread_local_array(s1, n))
  _(requires \thread_local_array(s2, n))
  _(ensures \result == 0 <==>
            \forall size_t i; 0 <= i && i < n ==> s1[i] == s2[i])
{
	size_t i;
	int diff = 0;

	_(assert :bv \forall int a; int b; (a ^ b) == 0 <==> (a == b))
	_(assert :bv \forall int a; int b; (a | b) == 0 <==> (a == 0 && b == 0))

	for (i = 0; i < n; ++i)
	  _(invariant 0 <= i && i <= n)
	  _(invariant diff == 0 <==> \forall size_t j; j < i ==> s1[j] == s2[j])
		diff |= s1[i] ^ s2[i];
	return diff;
}
