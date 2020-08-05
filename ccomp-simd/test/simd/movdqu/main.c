#include <immintrin.h>

__m128i copy(__m128i a, __m128i b)
{
  __m128i c, d, f;
  c = _mm_set_epi32(0x1,0x2,0x3,0x4);
  d = _mm_set_epi32(0x4,0x3,0x2,0x1);

  f = c;
  _mm_xor_si128(f,d);
  _mm_xor_si128(f,a);
  _mm_xor_si128(f,b);

  return f;
}

int
main (int argc, char *argv[])
{
  __m128i a, b, f;
  a = _mm_set_epi32(0xa,0xb,0xc,0xd);
  b = _mm_set_epi32(0xd,0xc,0xb,0xa);
  f = copy(a, b);

  return 0;
}
