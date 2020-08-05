#include <stdint.h>
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

#include "../check_cpu.h"
#include "../timer.h"

#include "aesni-keygen.c"

/* Note – the length of the output buffer is assumed to be a multiple of 16 bytes */
void AES_ECB_encrypt(const __m128i *in,	//pointer to the PLAINTEXT
		     __m128i *out,	//pointer to the CIPHERTEXT buffer
		     unsigned long length,	//text length in bytes
		     const __m128i *const key,	//pointer to the expanded key schedule
		     int number_of_rounds)	//number of AES rounds 10,12 or 14
{
  __m128i tmp; int i,j;

  if(length%16)
    length = length/16+1;
  else
    length = length/16;
  for(i=0; i < length; i++){
    tmp = _mm_xor_si128 (in[i],key[0]);
    for(j=1; j <number_of_rounds; j++){
      tmp = _mm_aesenc_si128 (tmp,key[j]);
    }
    out[i] = _mm_aesenclast_si128 (tmp,key[j]);
  }
}


void AES_ECB_decrypt(const __m128i *in,	//pointer to the CIPHERTEXT
		     __m128i *out,	//pointer to the DECRYPTED TEXT buffer
		     unsigned long length,	//text length in bytes
		     const __m128i *const key,	//pointer to the expanded key schedule
		     int number_of_rounds)	//number of AES rounds 10,12 or 14
{
  __m128i tmp;
  int i,j;

  if(length%16)
    length = length/16+1;
  else
    length = length/16;

  for(i=0; i < length; i++){
    tmp = _mm_xor_si128 (in[i],key[0]);
    for(j=1; j<number_of_rounds; j++){
      tmp = _mm_aesdec_si128 (tmp,key[j]);
    }
    out[i] = _mm_aesdeclast_si128 (tmp,key[j]);
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
const uint8_t ECB128_EXPECTED[] = {0x3a,0xd7,0x7b,0xb4,0x0d,0x7a,0x36,0x60, 
				   0xa8,0x9e,0xca,0xf3,0x24,0x66,0xef,0x97,
				   0xf5,0xd3,0xd5,0x85,0x03,0xb9,0x69,0x9d,
				   0xe7,0x85,0x89,0x5a,0x96,0xfd,0xba,0xaf,
				   0x43,0xb1,0xcd,0x7f,0x59,0x8e,0xce,0x23,
				   0x88,0x1b,0x00,0xe3,0xed,0x03,0x06,0x88,
				   0x7b,0x0c,0x78,0x5e,0x27,0xe8,0xad,0x3f,
				   0x82,0x23,0x20,0x71,0x04,0x72,0x5d,0xd4};
const uint8_t ECB192_EXPECTED[] = {0xbd,0x33,0x4f,0x1d,0x6e,0x45,0xf2,0x5f,
				   0xf7,0x12,0xa2,0x14,0x57,0x1f,0xa5,0xcc,
				   0x97,0x41,0x04,0x84,0x6d,0x0a,0xd3,0xad,
				   0x77,0x34,0xec,0xb3,0xec,0xee,0x4e,0xef,
				   0xef,0x7a,0xfd,0x22,0x70,0xe2,0xe6,0x0a,
				   0xdc,0xe0,0xba,0x2f,0xac,0xe6,0x44,0x4e,
				   0x9a,0x4b,0x41,0xba,0x73,0x8d,0x6c,0x72,
				   0xfb,0x16,0x69,0x16,0x03,0xc1,0x8e,0x0e};
const uint8_t ECB256_EXPECTED[] = {0xf3,0xee,0xd1,0xbd,0xb5,0xd2,0xa0,0x3c,
				   0x06,0x4b,0x5a,0x7e,0x3d,0xb1,0x81,0xf8,
				   0x59,0x1c,0xcb,0x10,0xd4,0x10,0xed,0x26,
				   0xdc,0x5b,0xa7,0x4a,0x31,0x36,0x28,0x70,
				   0xb6,0xed,0x21,0xb9,0x9c,0xa6,0xf4,0xf9,
				   0xf1,0x53,0xe7,0xb1,0xbe,0xaf,0xed,0x1d,
				   0x23,0x30,0x4b,0x7a,0x39,0xf9,0xf3,0xff,
				   0x06,0x7d,0x8d,0x8f,0x9e,0x24,0xec,0xc7};

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

const char progname[] = "aesni-ecb";

void do_test(int keysize) {
  __m128i key[15], deckey[15];
  int nrounds;
  const uint8_t *cipher_key;
  __m128i *plaintext, *ciphertext, *decryptedtext;
  const uint8_t *expected_ciphertext;
  int i;
  int enc_chk, dec_chk;
  int nblocks;

  nblocks = sizeof(AES_TEST_VECTOR)/16;

  switch (keysize) {
  case 128:
    cipher_key = AES128_TEST_KEY;
    expected_ciphertext = ECB128_EXPECTED;
    break;
  case 192:
    cipher_key = AES192_TEST_KEY;
    expected_ciphertext = ECB192_EXPECTED;
    break;
  case 256:
    cipher_key = AES256_TEST_KEY;
    expected_ciphertext = ECB256_EXPECTED;
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
  AES_ECB_encrypt(plaintext, ciphertext, nblocks*16, key, nrounds);
  AES_ECB_decrypt(ciphertext, decryptedtext, nblocks*16, deckey, nrounds);

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
  __m128i *plaintext, *ciphertext;
  timer_info keygen_t, enc_t, dec_t;

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
    AES_ECB_encrypt(plaintext, ciphertext, nblocks*16, key, nrounds);
  timer_stop(&enc_t);

  timer_start(&dec_t);
  for (i=nrep; i>0; i--)
    AES_ECB_decrypt(ciphertext, plaintext, nblocks*16, deckey, nrounds);
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

  if (nblocks <= 0) {
    printf("prog-name, nrep, nblocks, keygen, enc, dec, total-time(msecs)\n");
    exit(0);
  }

  if (argc > 2)
    do_bench(nblocks, nrep, keysize);
  else
    do_test(keysize);
  return 0;
}

