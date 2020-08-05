#include <stdint.h>
#if !defined CT_ANALYSIS
#include <assert.h>
#endif
#include <immintrin.h>

typedef struct { __m128i key[11]; } AES_KEY;

/** utils *********************************************************************/
static inline uint8_t *blk_xor(
  uint8_t *c,
  uint8_t *a,
  uint8_t *b
)
{
  unsigned int i;

  /* TODO: missing blk_xor */

  for (i=0; i < 16; i++ )
    { c[i] = a[i]^b[i]; }

  return c;
}

/** aes block decrypt *********************************************************/
void AES_decrypt(
  const uint8_t *in,	/* pointer to the CIPHERTEXT            */
  uint8_t *out,	      /* pointer to the DECRYPTED TEXT buffer */
  AES_KEY *k)	        /* pointer to the expanded key schedule */
{
  __m128i tmp;
  __m128i *key = (__m128i*) k;

  tmp = _mm_loadu_si128((__m128i*)in);
  tmp = _mm_xor_si128 (tmp,key[0]);
  tmp = _mm_aesdec_si128 (tmp,key[1]);
  tmp = _mm_aesdec_si128 (tmp,key[2]);
  tmp = _mm_aesdec_si128 (tmp,key[3]);
  tmp = _mm_aesdec_si128 (tmp,key[4]);
  tmp = _mm_aesdec_si128 (tmp,key[5]);
  tmp = _mm_aesdec_si128 (tmp,key[6]);
  tmp = _mm_aesdec_si128 (tmp,key[7]);
  tmp = _mm_aesdec_si128 (tmp,key[8]);
  tmp = _mm_aesdec_si128 (tmp,key[9]);
  tmp = _mm_aesdeclast_si128 (tmp,key[10]);
  _mm_storeu_si128((__m128i*)out, tmp);
}

int crypto_block_decrypt(
  unsigned char *out,
  const unsigned char *in,
  const unsigned char *k)
{
  AES_decrypt(in,out,(AES_KEY*) k);
  return 0;
}

/** aes key setup *************************************************************/
static inline __m128i AES_128_ASSIST(
  __m128i temp1,
  __m128i temp2
)
{
  __m128i temp3;
  temp2 = _mm_shuffle_epi32 (temp2 ,0xff);
  temp3 = _mm_slli_si128 (temp1, 0x4);
  temp1 = _mm_xor_si128 (temp1, temp3);
  temp3 = _mm_slli_si128 (temp3, 0x4);
  temp1 = _mm_xor_si128 (temp1, temp3);
  temp3 = _mm_slli_si128 (temp3, 0x4);
  temp1 = _mm_xor_si128 (temp1, temp3);
  temp1 = _mm_xor_si128 (temp1, temp2);
  return temp1;
}

void AES_128_Key_Expansion(
  const uint8_t *userkey,
  __m128i *key
)
{
  __m128i temp1, temp2;
  temp1 = _mm_loadu_si128((__m128i*)userkey);
  key[0] = temp1;
  temp2 = _mm_aeskeygenassist_si128 (temp1 ,0x1);
  temp1 = AES_128_ASSIST(temp1, temp2);
  key[1] = temp1;
  temp2 = _mm_aeskeygenassist_si128 (temp1,0x2);
  temp1 = AES_128_ASSIST(temp1, temp2);
  key[2] = temp1;
  temp2 = _mm_aeskeygenassist_si128 (temp1,0x4);
  temp1 = AES_128_ASSIST(temp1, temp2);
  key[3] = temp1;
  temp2 = _mm_aeskeygenassist_si128 (temp1,0x8);
  temp1 = AES_128_ASSIST(temp1, temp2);
  key[4] = temp1;
  temp2 = _mm_aeskeygenassist_si128 (temp1,0x10);
  temp1 = AES_128_ASSIST(temp1, temp2);
  key[5] = temp1;
  temp2 = _mm_aeskeygenassist_si128 (temp1,0x20);
  temp1 = AES_128_ASSIST(temp1, temp2);
  key[6] = temp1;
  temp2 = _mm_aeskeygenassist_si128 (temp1,0x40);
  temp1 = AES_128_ASSIST(temp1, temp2);
  key[7] = temp1;
  temp2 = _mm_aeskeygenassist_si128 (temp1,0x80);
  temp1 = AES_128_ASSIST(temp1, temp2);
  key[8] = temp1;
  temp2 = _mm_aeskeygenassist_si128 (temp1,0x1b);
  temp1 = AES_128_ASSIST(temp1, temp2);
  key[9] = temp1;
  temp2 = _mm_aeskeygenassist_si128 (temp1,0x36);
  temp1 = AES_128_ASSIST(temp1, temp2);
  key[10] = temp1;
}

int AES_set_decrypt_key(
  const uint8_t *key,
  int key_length,
  AES_KEY *decrypt_key
)
{
  int i;

  __m128i *kexp = (__m128i*) decrypt_key;
  __m128i tmp[11];

  assert (key_length==128);
  AES_128_Key_Expansion(key, tmp);
  kexp[0] = tmp[10];
  for (i=1; i<10; i++) {
    kexp[i] = _mm_aesimc_si128(tmp[10-i]);
  }
  kexp[10] = tmp[0];
  return 0;
}

static inline int crypto_block_expand_deckey(
  const unsigned char *k,
  AES_KEY *kexp
)
{
  return AES_set_decrypt_key(k, 128, kexp);
}

/**S - stream decrypt *********************************************************/
int crypto_stream_decrypt(
  uint8_t *out,
  const uint8_t *cipher,
  const long in_len,
  const uint8_t *iv,
  const uint8_t *k
)
{
  unsigned long j, nblocks;
  AES_KEY kexp;

  nblocks = in_len / 16;

  crypto_block_expand_deckey(k, &kexp);

  if(nblocks > 0)
  {
    /* compute 1st plaintext block */
    crypto_block_decrypt(out, cipher, (uint8_t*) &kexp);
    blk_xor((uint8_t*)out, (uint8_t*)iv, (uint8_t*)out);

    for(j=1; j < nblocks; ++j)
    {
      /* compute jth plaintext block */
      crypto_block_decrypt(out + j*16, cipher + j*16, (uint8_t*)&kexp);
      blk_xor((uint8_t*)(out + j*16), (uint8_t*)(cipher + (j-1)*16), (uint8_t*)(out+j*16));
    }
  }

  return 1;
}

/**S - remove padding *********************************************************/
int crypto_pad_remove(
  long *out_len,
  const uint8_t *in,
  long in_len
)
{
  #define shift_right_partial(var,shift,bit,cshift){\
    zmsk = _mm_set1_epi8(0-((shift>>bit)&1));\
    temp = var;\
    temp = _mm_srli_si128(temp, cshift);\
    var  = _mm_xor_si128(_mm_andnot_si128(zmsk, var),\
                         _mm_and_si128(zmsk, temp));}

  #define shift_right(var,shift){\
    shift_right_partial(var,shift,0,1 );\
    shift_right_partial(var,shift,1,2 );\
    shift_right_partial(var,shift,2,4 );\
    shift_right_partial(var,shift,3,8 );\
    shift_right_partial(var,shift,4,16);}

  __m128i padding, expected_padding;
  __m128i zmsk, temp;
  uint8_t padding_shift;
  int equal;

  padding_shift = 16 - in[in_len - 1];

  padding = _mm_loadu_si128((__m128i*) (in + in_len - 16));
  expected_padding = _mm_set1_epi8(in[in_len - 1]);

  shift_right(padding, padding_shift);
  shift_right(expected_padding, padding_shift);

  padding = _mm_xor_si128(padding, expected_padding);
  equal = _mm_testz_si128(padding, padding);

  *out_len = in_len - (in[in_len - 1] & (0 - equal));
  return equal;

  #undef shift_right
  #undef shift_right_partial
}

/**S - decrypt and remove padding *********************************************/

/* decrypts to out, out_len with in, in_len sk, iv                    */
/*   returns 1 for success, 0  failure                                */
/*   on returning 0 *out_len is equal to in_len (assume 0 length pad) */
int decrypt(
  uint8_t *out,
  long *out_len,
  const uint8_t *in,
  long in_len,
  const uint8_t *iv,
  const uint8_t *sk
)
{
  if(crypto_stream_decrypt(out, in, in_len, iv, sk))
    return crypto_pad_remove(out_len,out,in_len);

  return 0;
}

