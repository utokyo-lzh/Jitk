#include <vcc.h>
#include <stddef.h>

int bcmp(const unsigned char *s1, const unsigned char *s2, size_t n)
  _(requires \thread_local_array(s1, n))
  _(requires \thread_local_array(s2, n))
  _(ensures (\result == 0) <==>
     (\forall size_t i; 0 <= i && i < n ==> s1[i] == s2[i])
{
        size_t i;

        for (i = 0; i < n; ++i) _(invariant \forall size_t j; j < i ==> p1[j] == p2[j])
        {
                if (s1[i] != s2[i])
                        return 1;
        }
        return 0;
}

