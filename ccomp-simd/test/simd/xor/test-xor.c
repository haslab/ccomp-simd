#include <stdint.h>
#include <string.h>
#include <stdio.h>
#include <assert.h>
#include <immintrin.h>

/*
_mm_xor_si128
_mm_setzero_si128
_mm_storeu_si128
_mm_set_epi8
_mm_shuffle_epi8
_mm_set_epi32
_mm_loadu_si128 
*/

#define block __m128i
#define vxor(x,y) _mm_xor_si128(x,y)
#define zero _mm_setzero_si128()

static void print_uint8(uint8_t *a, size_t l)
{ size_t i;
  for(i=0;i<l;i++)
    printf("%02x ", a[i]);
  printf("\n");
}

static void print_m128i(int n, __m128i value)
{ uint8_t p[16];
  _mm_storeu_si128((__m128i*)p,value);
  printf("%4d: ",n); print_uint8(p, 16);
}

static __m128i bswap16(__m128i b)
{ const __m128i t = _mm_set_epi8(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15);
  return _mm_shuffle_epi8(b,t);
}

#if 1
block zero_set_byte(char val, unsigned idx) {
    block tmp = zero; ((char *)&tmp)[idx] = val; return tmp;
}

#else
block zero_set_byte(char val, unsigned idx) {
    uint8_t p[16];
    memset(p, 0, sizeof(uint8_t)*16);
    p[idx] = val;
    return _mm_loadu_si128((__m128i*)p);
}
#endif 


block test_xor(
  int nbytes,
  block v1,
  block v2,
  block v3,
  block v4,
  block v5,
  block v6,
  block v7)
{
  block sum, offset, tmp;
  block I=v1, L=v2, J=v3;
  block Jfordoubling = bswap16(v4); 
  block J8 = bswap16(Jfordoubling);
  block L2 = bswap16(tmp = bswap16(L));
  block L4 = bswap16(tmp = bswap16(tmp));
print_m128i(0,I);
print_m128i(1,L);
print_m128i(2,J);
print_m128i(3,Jfordoubling);
print_m128i(4,J8);
print_m128i(5,L2);
print_m128i(6,L4);

  /* process abytes and nonce */
  offset = vxor(L,J8);
print_m128i(6,offset); // <-- TODO: CHECKME

  tmp = zero_set_byte((char)(8*16),14); // FAIL in 2nd 6
  /*  tmp = _mm_set_epi32(0xabcdef12,0x12345678,0x45679abc,0x11112222); //DOES NOT FAIL in 2nd 6 */
print_m128i(7,tmp);

  sum = vxor(vxor(vxor(vxor(vxor(offset,tmp),J),I),L),offset);
print_m128i(8,sum);

    offset = L2;
print_m128i(9,offset);

    if(nbytes==16) offset = vxor(offset, v6);
print_m128i(10,offset);

    tmp = v7;
print_m128i(11,tmp);

    sum = vxor(sum, vxor(vxor(vxor(vxor(vxor(offset,tmp),J),I),L),offset));
print_m128i(12,sum);

  return vxor(sum,v5);
}

int
main (int argc, char *argv[])
{

  block v1 = _mm_set_epi32(0xabcdef12,0x12345678,0x45679abc,0x11112222);
  block v2 = _mm_set_epi32(0x12345678,0xabcdef12,0x11112222,0x45679abc);
  block v3 = _mm_set_epi32(0xa765dabe,0x20193821,0x78231608,0xbdf58378);
  block v4 = _mm_set_epi32(0x092138ab,0x12345678,0x45679abc,0x69843421);
  block v5 = _mm_set_epi32(0x47398571,0x29381342,0x45679abc,0xcafe2981);
  block v6 = _mm_set_epi32(0x12387124,0x89473891,0x45679abc,0x09374313);
  block v7 = _mm_set_epi32(0x29471023,0x92049132,0x45679abc,0xebda0987);
  block t;

  t = test_xor(
    16,
    v1,
    v2,
    v3,
    v4,
    v5,
    v6,
    v7);

  print_m128i(999,t);

  return 0;
}


