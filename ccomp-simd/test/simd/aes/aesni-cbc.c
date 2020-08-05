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
__m128i __builtin_ia32_pshufd (__v4si, const int);
__m128d __builtin_ia32_shufpd (__v2df, __v2df, const int);
__m128i __builtin_ia32_pxor128 (__v2di, __v2di);
__m128i __builtin_ia32_aesdec128 (__v2di, __v2di);
__m128i __builtin_ia32_aesdeclast128 (__v2di, __v2di);
__m128i __builtin_ia32_aesenc128 (__v2di, __v2di);
__m128i __builtin_ia32_aesenclast128 (__v2di, __v2di);
__m128i __builtin_ia32_aesimc128 (__v2di);
__m128i __builtin_ia32_aeskeygenassist128 (__v2di, const int);

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

#define _mm_slli_si128(__A, __B) ((__m128i)__builtin_ia32_pslldqi128 (__A, __B))

static inline __m128i _mm_xor_si128 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_pxor128 ((__v2di)__A, (__v2di)__B);
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

void AES_CBC_encrypt(const __m128i *in,
                     __m128i *out,
                     const __m128i* ivec,
                     unsigned long length,
                     const __m128i *key,
		     int number_of_rounds)
{
  __m128i feedback;

  int i,j;

  if (length%16)
    length = length/16+1;
  else
    length /= 16;

  feedback = ivec[0];
  for(i=0; i < length; i++){
    feedback = _mm_xor_si128 (in[i],feedback);
    feedback = _mm_xor_si128 (feedback,key[0]);
    for(j=1; j <number_of_rounds; j++)
      feedback = _mm_aesenc_si128 (feedback,key[j]);
    feedback = _mm_aesenclast_si128 (feedback,key[j]);
    out[i] = feedback;
  }
}

void AES_CBC_decrypt(const __m128i *in,
		     __m128i *out,
		     const __m128i* ivec,
		     unsigned long length,
		     __m128i *key,
		     int number_of_rounds)
{
  __m128i data,feedback,last_in; int i,j;

  if (length%16)
    length = length/16+1;
  else
    length = length/16;

  feedback = ivec[0];
  for(i=0; i < length; i++){
    last_in = in[i];
    data = _mm_xor_si128 (last_in,key[0]);
    for(j=1; j <number_of_rounds; j++){
      data = _mm_aesdec_si128 (data,key[j]);
    }
    data = _mm_aesdeclast_si128 (data,key[j]);
    data = _mm_xor_si128 (data,feedback);
    out[i] = data;
    feedback=last_in;
  }
}

/*test vectors were taken from http://csrc.nist.gov/publications/nistpubs/800- 38a/sp800-38a.pdf*/
const uint8_t AES128_TEST_KEY[] = {0x2b,0x7e,0x15,0x16,0x28,0xae,0xd2,0xa6,
				   0xab,0xf7,0x15,0x88,0x09,0xcf,0x4f,0x3c};
const uint8_t AES192_TEST_KEY[] = {0x8e,0x73,0xb0,0xf7,0xda,0x0e,0x64,0x52,
				   0xc8,0x10,0xf3,0x2b,0x80,0x90,0x79,0xe5,
				   0x62,0xf8,0xea,0xd2,0x52,0x2c,0x6b,0x7b};
const uint8_t AES256_TEST_KEY[] = {0x60,0x3d,0xeb,0x10,0x15,0xca,0x71,0xbe,
				   0x2b,0x73,0xae,0xf0,0x85,0x7d,0x77,0x81,
                                   0x1f,0x35,0x2c,0x07,0x3b,0x61,0x08,0xd7,
				   0x2d,0x98,0x10,0xa3,0x09,0x14,0xdf,0xf4};
const uint8_t AES_TEST_VECTOR[] = {0x6b,0xc1,0xbe,0xe2,0x2e,0x40,0x9f,0x96,
				   0xe9,0x3d,0x7e,0x11,0x73,0x93,0x17,0x2a,
                                   0xae,0x2d,0x8a,0x57,0x1e,0x03,0xac,0x9c,
                                   0x9e,0xb7,0x6f,0xac,0x45,0xaf,0x8e,0x51,
                                   0x30,0xc8,0x1c,0x46,0xa3,0x5c,0xe4,0x11,
                                   0xe5,0xfb,0xc1,0x19,0x1a,0x0a,0x52,0xef,
                                   0xf6,0x9f,0x24,0x45,0xdf,0x4f,0x9b,0x17,
                                   0xad,0x2b,0x41,0x7b,0xe6,0x6c,0x37,0x10};
ALIGN16 const uint8_t CBC_IV[] = {0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07, 
				  0x08,0x09,0x0a,0x0b,0x0c,0x0d,0x0e,0x0f};
const uint8_t CBC128_EXPECTED[] = {0x76,0x49,0xab,0xac,0x81,0x19,0xb2,0x46,
				   0xce,0xe9,0x8e,0x9b,0x12,0xe9,0x19,0x7d,
				   0x50,0x86,0xcb,0x9b,0x50,0x72,0x19,0xee,
				   0x95,0xdb,0x11,0x3a,0x91,0x76,0x78,0xb2,
				   0x73,0xbe,0xd6,0xb8,0xe3,0xc1,0x74,0x3b,
				   0x71,0x16,0xe6,0x9e,0x22,0x22,0x95,0x16,
				   0x3f,0xf1,0xca,0xa1,0x68,0x1f,0xac,0x09,
				   0x12,0x0e,0xca,0x30,0x75,0x86,0xe1,0xa7};
const uint8_t CBC192_EXPECTED[] = {0x4f,0x02,0x1d,0xb2,0x43,0xbc,0x63,0x3d,
				   0x71,0x78,0x18,0x3a,0x9f,0xa0,0x71,0xe8,
				   0xb4,0xd9,0xad,0xa9,0xad,0x7d,0xed,0xf4,
				   0xe5,0xe7,0x38,0x76,0x3f,0x69,0x14,0x5a,
				   0x57,0x1b,0x24,0x20,0x12,0xfb,0x7a,0xe0,
				   0x7f,0xa9,0xba,0xac,0x3d,0xf1,0x02,0xe0,
				   0x08,0xb0,0xe2,0x79,0x88,0x59,0x88,0x81,
				   0xd9,0x20,0xa9,0xe6,0x4f,0x56,0x15,0xcd};
const uint8_t CBC256_EXPECTED[] = {0xf5,0x8c,0x4c,0x04,0xd6,0xe5,0xf1,0xba,
				   0x77,0x9e,0xab,0xfb,0x5f,0x7b,0xfb,0xd6,
				   0x9c,0xfc,0x4e,0x96,0x7e,0xdb,0x80,0x8d,
				   0x67,0x9f,0x77,0x7b,0xc6,0x70,0x2c,0x7d,
				   0x39,0xf2,0x33,0x69,0xa9,0xd9,0xba,0xcf,
				   0xa5,0x30,0xe2,0x63,0x04,0x23,0x14,0x61,
				   0xb2,0xeb,0x05,0xe2,0xc3,0x9b,0xe9,0xfc,
				   0xda,0x6c,0x19,0x07,0x8c,0x6a,0x9d,0x1b};

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

const char progname[] = "aesni-cbc";

void do_test(int keysize) {
  __m128i key[15], deckey[15];
  int nrounds;
  const uint8_t *cipher_key;
  __m128i *plaintext, *ciphertext, *decryptedtext, *IV;
  const uint8_t *expected_ciphertext;
  int i;
  int enc_chk, dec_chk;
  int nblocks;

  nblocks = sizeof(AES_TEST_VECTOR)/16;
  IV = (__m128i*)CBC_IV;

  switch (keysize) {
  case 128:
    cipher_key = AES128_TEST_KEY;
    expected_ciphertext = CBC128_EXPECTED;
    break;
  case 192:
    cipher_key = AES192_TEST_KEY;
    expected_ciphertext = CBC192_EXPECTED;
    break;
  case 256:
    cipher_key = AES256_TEST_KEY;
    expected_ciphertext = CBC256_EXPECTED;
    break;
  default:
    fprintf(stderr, "Wrong key size (expected 128|192|256)\n");
    exit(1);
  }

  // Setup buffers
  posix_memalign((void**)&plaintext, 16, nblocks*16);
  posix_memalign((void**)&ciphertext, 16, nblocks*16);
  posix_memalign((void**)&decryptedtext, 16, nblocks*16);
  for (i=0; i<nblocks; i++) {
    plaintext[i] = _mm_loadu_si128(&((__m128i*)AES_TEST_VECTOR)[i]);
  }

  nrounds = AES_set_encrypt_key(cipher_key, keysize, key);
  AES_set_decrypt_key(nrounds, key, deckey);
  AES_CBC_encrypt(plaintext, ciphertext, IV, nblocks*16, key, nrounds);
  AES_CBC_decrypt(ciphertext, decryptedtext, IV, nblocks*16, deckey, nrounds);

  enc_chk = dec_chk = 1;
  for(i=0; i<sizeof(AES_TEST_VECTOR); i++)
    enc_chk &= (((char*)ciphertext)[i] == ((char*)expected_ciphertext)[i]);
  for(i=0; i<sizeof(AES_TEST_VECTOR); i++)
    dec_chk &= (((char*)decryptedtext)[i] == ((char*)plaintext)[i]);

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

  printf("The DECRYPTEDTEXT:\n");
  for (i=0; i< sizeof(AES_TEST_VECTOR)/16; i++)
    print_m128i_with_string("",decryptedtext[i]);

  if (enc_chk) {
    printf("Encryption test: PASSED!\n");
    if (dec_chk)
      printf("Decryption test: PASSED!\n");
  } else {
    printf("Encryption test: FAILED!!!\n");
  }

  free(plaintext);
  free(ciphertext);
  free(decryptedtext);
}

void do_bench(int nblocks, int nrep, int keysize) {
  int nrounds, i;
  const uint8_t * cipherkey;
  __m128i key[15], deckey[15];
  __m128i *plaintext, *ciphertext, *IV;
  timer_info keygen_t, enc_t, dec_t;

  IV = (__m128i*)CBC_IV;

  switch (keysize) {
  case 128:
    cipherkey = AES128_TEST_KEY;
    break;
  case 192:
    cipherkey = AES192_TEST_KEY;
    break;
  case 256:
    cipherkey = AES256_TEST_KEY;
    break;
  default:
    fprintf(stderr, "Wrong key size (expected 128|192|256)\n");
    exit(1);
  }

  timer_init(&keygen_t);
  timer_init(&enc_t);
  timer_init(&dec_t);

  posix_memalign((void**)&plaintext, 16, nblocks*16);
  posix_memalign((void**)&ciphertext, 16, nblocks*16);

  timer_start(&keygen_t);
  for (i=nrep; i>0; i--) {
    nrounds = AES_set_encrypt_key(cipherkey, keysize, key);
    AES_set_decrypt_key(nrounds, key, deckey);
  }
  timer_stop(&keygen_t);

  timer_start(&enc_t);
  for (i=nrep; i>0; i--)
    AES_CBC_encrypt(plaintext, ciphertext, IV, nblocks*16, key, nrounds);
  timer_stop(&enc_t);

  timer_start(&dec_t);
  for (i=nrep; i>0; i--)
    AES_CBC_decrypt(ciphertext, plaintext, IV, nblocks*16, deckey, nrounds);
  timer_stop(&dec_t);
  
  free(plaintext);
  free(ciphertext);

  printf("%s%d, %d, %d, %lld, %lld, %lld, %lf\n",
	 progname, keysize, nrep, nblocks,
	 timer_get_ticks(&keygen_t),
	 timer_get_ticks(&enc_t),
	 timer_get_ticks(&dec_t),
	 (timer_get_time(&keygen_t)+
	  timer_get_time(&enc_t)+
	  timer_get_time(&dec_t))
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
      printf("prog-name, nrep, nblocks, keygen, enc, dec, total-time(msecs)\n");
      exit(0);
    }
    do_bench(nblocks, nrep, keysize);
  } else
    do_test(keysize);
  return 0;
}
