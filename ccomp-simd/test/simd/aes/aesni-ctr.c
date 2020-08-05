#include <stdio.h>
#include <stdlib.h>

#if defined (__COMPCERT__)
typedef __builtin_t128 __m128i;
typedef __builtin_t128 __m128d;
typedef __builtin_t128 __v2di;
typedef __builtin_t128 __v2df;
typedef __builtin_t128 __v4si;
typedef __builtin_t128 __v16qi;

__v16qi __builtin_ia32_loaddqu (char *);
void __builtin_ia32_storedqu (char *, __v16qi);
__v2di __builtin_ia32_pslldqi128 (__v2di, const int);
__v2di __builtin_ia32_psrldqi128 (__v2di, const int);
__m128i __builtin_ia32_pshufd (__v4si, const int);
__m128i __builtin_ia32_pshufb128 (__v16qi, __v16qi);
__m128d __builtin_ia32_shufpd (__v2df, __v2df, const int);
__m128i __builtin_ia32_pxor128 (__v2di, __v2di);
__m128i __builtin_ia32_paddq128 (__v2di, __v2di);
__m128i __builtin_ia32_aesdec128 (__v2di, __v2di);
__m128i __builtin_ia32_aesdeclast128 (__v2di, __v2di);
__m128i __builtin_ia32_aesenc128 (__v2di, __v2di);
__m128i __builtin_ia32_aesenclast128 (__v2di, __v2di);
__m128i __builtin_ia32_aesimc128 (__v2di);
__m128i __builtin_ia32_aeskeygenassist128 (__v2di, const int);

static inline __m128i _mm_setzero_si128 (void)
{ __m128i res;
  ((int*)&res)[0] = 0;
  ((int*)&res)[1] = 0;
  ((int*)&res)[2] = 0;
  ((int*)&res)[3] = 0;
  return res;
}

static inline __m128i _mm_set_epi32 (int x3, int x2, int x1, int x0)
{ __m128i res;
  ((int*)&res)[0] = x0;
  ((int*)&res)[1] = x1;
  ((int*)&res)[2] = x2;
  ((int*)&res)[3] = x3;
  return res;
}

static inline __m128i _mm_setr_epi8 (char x0, char x1, char x2, char x3,
				     char x4, char x5, char x6, char x7,
				     char x8, char x9, char xA, char xB,
				     char xC, char xD, char xE, char xF)
{ __m128i res;
  ((char*)&res)[0] = x0;
  ((char*)&res)[1] = x1;
  ((char*)&res)[2] = x2;
  ((char*)&res)[3] = x3;
  ((char*)&res)[4] = x4;
  ((char*)&res)[5] = x5;
  ((char*)&res)[6] = x6;
  ((char*)&res)[7] = x7;
  ((char*)&res)[8] = x8;
  ((char*)&res)[9] = x9;
  ((char*)&res)[10] = xA;
  ((char*)&res)[11] = xB;
  ((char*)&res)[12] = xC;
  ((char*)&res)[13] = xD;
  ((char*)&res)[14] = xE;
  ((char*)&res)[15] = xF;
  return res;
}

static inline __m128i _mm_insert_epi32 (__m128i a, int b, const int i)
{ __m128i res;
  res = a;
  ((int*)&res)[i] = b;
  return res;
}

static inline __m128i _mm_loadu_si128 (__m128i const *__P)
{ return (__m128i) __builtin_ia32_loaddqu ((char *)__P); }

static inline void _mm_storeu_si128 (__m128i *__P, __m128i __B)
{
  __builtin_ia32_storedqu ((char *)__P, __B);
}

/* Create a selector for use with the SHUFPD instruction.  */
#define _MM_SHUFFLE2(fp1,fp0) \
 (((fp1) << 1) | (fp0))

#define _mm_shuffle_epi32(__A, __B) ((__m128i)__builtin_ia32_pshufd ((__v4si)__A, __B))

#define _mm_shuffle_pd(__A, __B, __C) ((__m128d)__builtin_ia32_shufpd ((__v2df)__A, (__v2df)__B, (__C)))

static inline __m128i _mm_shuffle_epi8 (__m128i __X, __m128i __Y)
{
  return (__m128i) __builtin_ia32_pshufb128 ((__v16qi)__X, (__v16qi)__Y);
}

#define _mm_slli_si128(__A, __B) ((__m128i)__builtin_ia32_pslldqi128 (__A, __B))
#define _mm_srli_si128(__A, __B) ((__m128i)__builtin_ia32_psrldqi128 (__A, __B))

static inline __m128i _mm_xor_si128 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_pxor128 ((__v2di)__A, (__v2di)__B);
}

static inline __m128i _mm_add_epi64 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_paddq128 ((__v2di)__A, (__v2di)__B);
}

static inline __m128i _mm_aesdec_si128 (__m128i __X, __m128i __Y)
{
  return (__m128i) __builtin_ia32_aesdec128 ((__v2di)__X, (__v2di)__Y);
}

static inline __m128i _mm_aesdeclast_si128 (__m128i __X, __m128i __Y)
{
  return (__m128i) __builtin_ia32_aesdeclast128 ((__v2di)__X, (__v2di)__Y);
}

static inline __m128i _mm_aesenc_si128 (__m128i __X, __m128i __Y)
{
  return (__m128i) __builtin_ia32_aesenc128 ((__v2di)__X, (__v2di)__Y);
}

static inline __m128i _mm_aesenclast_si128 (__m128i __X, __m128i __Y)
{
  return (__m128i) __builtin_ia32_aesenclast128 ((__v2di)__X, (__v2di)__Y);
}

static inline __m128i _mm_aesimc_si128 (__m128i __X)
{
  return (__m128i) __builtin_ia32_aesimc128 ((__v2di)__X);
}

#define _mm_aeskeygenassist_si128(X, C)					\
  ((__m128i) __builtin_ia32_aeskeygenassist128 ((__v2di)(__m128i)(X), (int)(C)))

#else
#include <wmmintrin.h>
#include <emmintrin.h>
#include <smmintrin.h>
#endif

#if !defined (ALIGN16)
# if defined (__COMPCERT__)
# define ALIGN16 __attribute ( (aligned (16)))
# elif defined (__GNUC__)
# define ALIGN16 __attribute__ ( (aligned (16)))
# else
# define ALIGN16 __declspec (align (16))
# endif
#endif

#include "../check_cpu.h"
#include "../timer.h"

#include "aesni-keygen.c"

void AES_CTR_encrypt (const __m128i *in,
		      __m128i *out,
		      const unsigned char ivec[8],
		      const unsigned char nonce[4],
		      unsigned long length,
		      const __m128i *key,
		      int number_of_rounds)
{
  __m128i ctr_block, tmp, ONE, BSWAP_EPI64;
  
  int i,j;

  if (length%16)
    length = length/16 + 1;
  else
    length/=16;

  ONE = _mm_set_epi32(0,1,0,0);
  BSWAP_EPI64 = _mm_setr_epi8(7,6,5,4,3,2,1,0,15,14,13,12,11,10,9,8);
  ctr_block = _mm_setzero_si128();
  /* obs: available only in x64
  ctr_block = _mm_insert_epi64(ctr_block, *(long long*)ivec, 1);
  */
  ctr_block = _mm_insert_epi32(ctr_block, ((long*)ivec)[0], 2);
  ctr_block = _mm_insert_epi32(ctr_block, ((long*)ivec)[1], 3);

  ctr_block = _mm_insert_epi32(ctr_block, *(long*)nonce, 1);
  ctr_block = _mm_srli_si128(ctr_block, 4);
  ctr_block = _mm_shuffle_epi8(ctr_block, BSWAP_EPI64);
  ctr_block = _mm_add_epi64(ctr_block, ONE);
  for(i=0; i < length; i++){
    tmp = _mm_shuffle_epi8(ctr_block, BSWAP_EPI64);
    ctr_block = _mm_add_epi64(ctr_block, ONE);
    tmp = _mm_xor_si128(tmp, key[0]);
    for(j=1; j <number_of_rounds; j++) {
      tmp = _mm_aesenc_si128 (tmp, key[j]);
    };
    tmp = _mm_aesenclast_si128 (tmp, key[j]);
    out[i] = _mm_xor_si128(tmp,in[i]);
  }
}


/*test vectors were taken from http://w3.antd.nist.gov/iip_pubs/rfc3602.txt*/
const uint8_t AES128_TEST_KEY[] = {0x7E,0x24,0x06,0x78,0x17,0xFA,0xE0,0xD7,
				     0x43,0xD6,0xCE,0x1F,0x32,0x53,0x91,0x63};
const uint8_t AES192_TEST_KEY[] = {0x7C,0x5C,0xB2,0x40,0x1B,0x3D,0xC3,0x3C,
				     0x19,0xE7,0x34,0x08,0x19,0xE0,0xF6,0x9C,
				     0x67,0x8C,0x3D,0xB8,0xE6,0xF6,0xA9,0x1A};
const uint8_t AES256_TEST_KEY[] = {0xF6,0xD6,0x6D,0x6B,0xD5,0x2D,0x59,0xBB,
				     0x07,0x96,0x36,0x58,0x79,0xEF,0xF8,0x86,
				     0xC6,0x6D,0xD5,0x1A,0x5B,0x6A,0x99,0x74,
				     0x4B,0x50,0x59,0x0C,0x87,0xA2,0x38,0x84};
const uint8_t AES_TEST_VECTOR[] = {0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,
				     0x08,0x09,0x0A,0x0B,0x0C,0x0D,0x0E,0x0F,
				     0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17,
				     0x18,0x19,0x1A,0x1B,0x1C,0x1D,0x1E,0x1F};
const uint8_t CTR128_IV[] = {0xC0,0x54,0x3B,0x59,0xDA,0x48,0xD9,0x0B};
const uint8_t CTR192_IV[] = {0x02,0x0C,0x6E,0xAD,0xC2,0xCB,0x50,0x0D};
const uint8_t CTR256_IV[] = {0xC1,0x58,0x5E,0xF1,0x5A,0x43,0xD8,0x75};
const uint8_t CTR128_NONCE[] = {0x00,0x6C,0xB6,0xDB};
const uint8_t CTR192_NONCE[] = {0x00,0x96,0xB0,0x3B};
const uint8_t CTR256_NONCE[] = {0x00,0xFA,0xAC,0x24};
const uint8_t CTR128_EXPECTED[] = {0x51,0x04,0xA1,0x06,0x16,0x8A,0x72,0xD9,
				     0x79,0x0D,0x41,0xEE,0x8E,0xDA,0xD3,0x88,
				     0xEB,0x2E,0x1E,0xFC,0x46,0xDA,0x57,0xC8,
                                     0xFC,0xE6,0x30,0xDF,0x91,0x41,0xBE,0x28};
const uint8_t CTR192_EXPECTED[] = {0x45,0x32,0x43,0xFC,0x60,0x9B,0x23,0x32,
				     0x7E,0xDF,0xAA,0xFA,0x71,0x31,0xCD,0x9F,
				     0x84,0x90,0x70,0x1C,0x5A,0xD4,0xA7,0x9C,
                                     0xFC,0x1F,0xE0,0xFF,0x42,0xF4,0xFB,0x00};
const uint8_t CTR256_EXPECTED[] = {0xF0,0x5E,0x23,0x1B,0x38,0x94,0x61,0x2C,
				     0x49,0xEE,0x00,0x0B,0x80,0x4E,0xB2,0xA9,
				     0xB8,0x30,0x6B,0x50,0x8F,0x83,0x9D,0x6A,
                                     0x55,0x30,0x83,0x1D,0x93,0x44,0xAF,0x1C};

/*****************************************************************************/

void print_m128i_with_string(char* string,__m128i data) {
  unsigned char *pointer = (unsigned char*)&data;
  int i;
  printf("%-40s[0x",string);
  for (i=0; i<16; i++)
    printf("%02x",pointer[i]);
  printf("]\n");
}

/*****************************************************************************/

const char progname[] = "aesni-ctr";

void do_test(int keysize) {
  __m128i key[15];
  int nrounds;
  const uint8_t *cipher_key;
  __m128i *plaintext, *ciphertext;
  const uint8_t *IV, *NONCE;
  const uint8_t *expected_ciphertext;
  int i;
  int enc_chk;
  int nblocks;

  nblocks = sizeof(AES_TEST_VECTOR)/16;

  switch (keysize) {
  case 128:
    IV = CTR128_IV;
    NONCE = CTR128_NONCE;
    cipher_key = AES128_TEST_KEY;
    expected_ciphertext = CTR128_EXPECTED;
    break;
  case 192:
    IV = CTR192_IV;
    NONCE = CTR192_NONCE;
    cipher_key = AES192_TEST_KEY;
    expected_ciphertext = CTR192_EXPECTED;
    break;
  case 256:
    IV = CTR256_IV;
    NONCE = CTR256_NONCE;
    cipher_key = AES256_TEST_KEY;
    expected_ciphertext = CTR256_EXPECTED;
    break;
  default:
    fprintf(stderr, "Wrong key size (expected 128|192|256)\n");
    exit(1);
  }

  // Setup buffers
  posix_memalign((void**)&plaintext, 16, nblocks*16);
  posix_memalign((void**)&ciphertext, 16, nblocks*16);
  for (i=0; i<nblocks; i++) {
    plaintext[i] = _mm_loadu_si128(&((__m128i*)AES_TEST_VECTOR)[i]);
  }

  nrounds = AES_set_encrypt_key(cipher_key, keysize, key);
  AES_CTR_encrypt(plaintext, ciphertext, IV, NONCE, nblocks*16, key, nrounds);

  enc_chk = 1;
  for(i=0; i<sizeof(AES_TEST_VECTOR); i++)
    enc_chk &= (((char*)ciphertext)[i] == ((char*)expected_ciphertext)[i]);

  printf("\n ===== Performing %s with keysize %d =====\n\n", progname, keysize);
  printf("The Key Schedule:\n");
  for (i=0; i<= nrounds; i++)
    print_m128i_with_string("",key[i]);

  printf("The PLAINTEXT:\n");
  for (i=0; i< sizeof(AES_TEST_VECTOR)/16; i++)
    print_m128i_with_string("",plaintext[i]);

  printf("The CIPHERTEXT:\n");
  for (i=0; i< sizeof(AES_TEST_VECTOR)/16; i++)
    print_m128i_with_string("",ciphertext[i]);

  printf("Encryption test: %s\n", enc_chk ? "passed" : "FAILED");

  free(plaintext);
  free(ciphertext);
}

void do_bench(int nblocks, int nrep, int keysize) {
  int nrounds, i;
  const uint8_t * cipherkey;
  __m128i key[15];
  __m128i *plaintext, *ciphertext;
  const uint8_t *IV, *NONCE;
  timer_info keygen_t, enc_t;

  switch (keysize) {
  case 128:
    IV = CTR128_IV;
    NONCE = CTR128_NONCE;
    cipherkey = AES128_TEST_KEY;
    break;
  case 192:
    IV = CTR192_IV;
    NONCE = CTR192_NONCE;
    cipherkey = AES192_TEST_KEY;
    break;
  case 256:
    IV = CTR256_IV;
    NONCE = CTR256_NONCE;
    cipherkey = AES256_TEST_KEY;
    break;
  default:
    fprintf(stderr, "Wrong key size (expected 128|192|256)\n");
    exit(1);
  }

  timer_init(&keygen_t);
  timer_init(&enc_t);

  posix_memalign((void**)&plaintext, 16, nblocks*16);
  posix_memalign((void**)&ciphertext, 16, nblocks*16);

  timer_start(&keygen_t);
  for (i=nrep; i>0; i--) {
    nrounds = AES_set_encrypt_key(cipherkey, keysize, key);
  }
  timer_stop(&keygen_t);

  timer_start(&enc_t);
  for (i=nrep; i>0; i--)
    AES_CTR_encrypt(plaintext, ciphertext, IV, NONCE, nblocks*16, key, nrounds);
  timer_stop(&enc_t);

  free(plaintext);
  free(ciphertext);

  printf("%s%d, %d, %d, %lld, %lld, %lf\n",
	 progname, keysize, nrep, nblocks,
	 timer_get_ticks(&keygen_t),
	 timer_get_ticks(&enc_t),
	 (timer_get_time(&keygen_t)+
	  timer_get_time(&enc_t))
	 );
} 

int main(int argc,char *argv[]){
  int keysize, nblocks, nrep;

  if (!Check_CPU_support_AES()){
    fprintf(stderr, "Cpu does not support AES instruction set. Bailing out.\n");
    return 1;
  }

  if (argc<2) {
    fprintf(stderr, "usage: %s <keysize> [num-blocks] [[nrep]]\n", argv[0]);
    exit(1);
  }

  keysize = atoi(argv[1]);
  nblocks = 0;
  if (argc>2) nblocks = atoi(argv[2]);
  nrep = 1;
  if (argc>3) nrep = atoi(argv[3]);

  if (argc > 2) {
    if (nblocks <= 0) {
      printf("prog-name, nrep, nblocks, keygen, enc, total-time(msecs)\n");
      exit(0);
    }
    do_bench(nblocks, nrep, keysize);
  } else
    do_test(keysize);
  return 0;
}
