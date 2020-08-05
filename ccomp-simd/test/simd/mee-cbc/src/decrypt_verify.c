#include <stdint.h>
#if !defined CT_ANALYSIS
#include <assert.h>
#endif
#include <stdio.h>
#include <immintrin.h>

#define HEADER_LENGTH 13
#define CRYPTO_BYTES 32

/* aes128.c */
extern int decrypt(
  uint8_t *out,
  long *out_len,
  const uint8_t *in,
  long in_len,
  const uint8_t *iv,
  const uint8_t *sk
);

/* sha256.c or sha256-msha.c */
int crypto_hashblocks(
  unsigned char *statebytes,
  const unsigned char *data,
  unsigned long input_len
);


static const uint8_t hash_iv[32] =
{
  0x6a,0x09,0xe6,0x67,
  0xbb,0x67,0xae,0x85,
  0x3c,0x6e,0xf3,0x72,
  0xa5,0x4f,0xf5,0x3a,
  0x51,0x0e,0x52,0x7f,
  0x9b,0x05,0x68,0x8c,
  0x1f,0x83,0xd9,0xab,
  0x5b,0xe0,0xcd,0x19,
};

int crypto_auth_ct(
  uint8_t *out,
  const uint8_t *in,
  long publen,
  long inlen,
  const uint8_t *key
)
{
  #define copy_hash_iv(ptr){\
    st0 = _mm_loadu_si128((__m128i*) (hash_iv   ));\
    st1 = _mm_loadu_si128((__m128i*) (hash_iv+16));\
    _mm_storeu_si128 ((__m128i*) (ptr     ), st0);\
    _mm_storeu_si128 ((__m128i*) (ptr + 16), st1);}

  #define load_si128(v,p,o){\
    v = _mm_loadu_si128 ((__m128i*) (p + o));}

  #define store_si128(p,o,v){\
    _mm_storeu_si128 ((__m128i*) (p + o), v);}

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

  #define is_any_bit_set(r,a){\
    r=a; r|=(a>>3); r|=(r>>2); r|=(r>>1); r&=1;}

  __m128i key0, key1, ipad;
  __m128i st0, st1;
  __m128i ot0, ot1;
  __m128i in0, zr0;
  __m128i zmsk, temp; /* shift_right variables */
  __m128i mask;

  uint8_t block[64+64];
  uint8_t state[32];
  long pub_bytes;
  int pad_len, i;
  uint64_t processed_blocks;
  uint64_t private_blocks, public_blocks;
  uint64_t in_first, exec_second;
  uint64_t bit_len;
  uint64_t *block_u64_1, *block_u64_2;

  /* key `xor` ipad */
    load_si128(key0,key,0 )
    load_si128(key1,key,16)
    ipad = _mm_set1_epi8(0x36);

  key0 = _mm_xor_si128(key0,ipad);
  key1 = _mm_xor_si128(key1,ipad);

    store_si128(block,0 ,key0)
    store_si128(block,16,key1)
    store_si128(block,32,ipad)
    store_si128(block,48,ipad)
  
  /* init state and digest first block */
    copy_hash_iv(state)
  crypto_hashblocks(state,block,64);

  /* calculate the number of public bytes            */
  /*   public bytes is equal to (public blocks * 64) */
  /*     publen = 13 + |M| + 32 + (16-(|M|%16))      */
  /*     min(publen) = 13 + 0 + 32 + 16 = 61         */
  /*                 13 + 1 + 32 + 15 = 61           */
  pub_bytes = (publen - 32 - 16) & (-64);
  crypto_hashblocks(state,in,pub_bytes);
  in = in + pub_bytes;

  /* clear block[128] */
  zr0 = _mm_setzero_si128();
    store_si128(block,0 ,zr0) store_si128(block,16 ,zr0)
    store_si128(block,32,zr0) store_si128(block,48 ,zr0)
    store_si128(block,64,zr0) store_si128(block,80 ,zr0)
    store_si128(block,96,zr0) store_si128(block,112,zr0)

  /* copy all remaining bytes minus the last 16 */
  pub_bytes = (publen - 32 - 16) & ( 63);
  for(i=0; i<pub_bytes; i++)
    block[i] = in[i];
  in += pub_bytes;

  /* load the last 16 bytes      */
  /*   bytes of padding: [1..16] */
  /*   padding bytes are in the msb     */
    load_si128(in0,in,0)

  pad_len = publen - inlen;
  mask = _mm_set1_epi8(0xFF);
  shift_right(mask,pad_len);

  /* clear padding bytes from in0 */
  in0 = _mm_and_si128(in0, mask);

  /* set 0x80 */
  mask = _mm_set_epi64x(0x8000000000000000,0x0);
  shift_right(mask,(pad_len-1));
  in0 = _mm_or_si128(in0,mask);

  /* save in0 */
    store_si128(block,pub_bytes,in0);

  /* create mask that indicates if length should be */
  /* in the first or second block                   */
    /*  private_blocks  = ((uint64_t)(0 - ((inlen  - 32 + 1 + 8) & 63))) >> 63;*/
    /*  private_blocks += (inlen - 32 + 1 + 8) >> 6;*/

  processed_blocks = (((publen - 32 - 16) & (-64)) >> 6);

  private_blocks    = ((0 - ((((uint64_t)inlen)  - 32 + 1 + 8) & 63))) >> 63;
  private_blocks   += (inlen  - 32 + 1 + 8) >> 6;

  public_blocks     = ((0 - ((((uint64_t)publen) - 32 + 1 + 8) & 63))) >> 63;
  public_blocks    += (publen - 32 + 1 + 8) >> 6;

  in_first    =   0 - ((processed_blocks - private_blocks) & 0x1);
  exec_second = ~(0 - ((processed_blocks - public_blocks ) & 0x1));

  bit_len = 512 + ((inlen - 32) << 3);
  #if defined (__COMPCERT__)
    bit_len = ((bit_len & (uint64_t)0xFF00000000000000) >> 56) |
              ((bit_len & (uint64_t)0x00FF000000000000) >> 40) |
              ((bit_len & (uint64_t)0x0000FF0000000000) >> 24) |
              ((bit_len & (uint64_t)0x000000FF00000000) >> 8 ) |
              ((bit_len & (uint64_t)0x00000000FF000000) << 8 ) |
              ((bit_len & (uint64_t)0x0000000000FF0000) << 24) |
              ((bit_len & (uint64_t)0x000000000000FF00) << 40) |
              ((bit_len & (uint64_t)0x00000000000000FF) << 56);
  #else
    bit_len = __builtin_bswap64(bit_len);
  #endif

  block_u64_1 = (uint64_t*) (block + 56);
  block_u64_2 = (uint64_t*) (block + 120);

  (*block_u64_1) |= (bit_len & ( in_first));
  (*block_u64_2) |= (bit_len & (~in_first));
  
  crypto_hashblocks(state,block,64);

  /* copy state */
    load_si128(st0,state,0 )
    load_si128(st1,state,16)
    store_si128(out,0 ,st0)
    store_si128(out,16,st1)

  if(exec_second != 0)
  {
    crypto_hashblocks(state,block+64,64);

    /* merge out and state */
    mask = _mm_set1_epi8(in_first & 0xFF);
      load_si128(st0,state,0 )
      load_si128(st1,state,16)
      load_si128(ot0,out,0 )
      load_si128(ot1,out,16)

    ot0 = _mm_xor_si128(_mm_andnot_si128(mask, st0),
                        _mm_and_si128(mask, ot0));
    ot1 = _mm_xor_si128(_mm_andnot_si128(mask, st1),
                        _mm_and_si128(mask, ot1));

    store_si128(out,0 ,ot0)
    store_si128(out,16,ot1)
  }

  /* ************************************************************************ */
  /* key `xor` opad */
    load_si128(key0,key,0 )
    load_si128(key1,key,16)
    ipad = _mm_set1_epi8(0x5c);

  key0 = _mm_xor_si128(key0,ipad);
  key1 = _mm_xor_si128(key1,ipad);

    store_si128(block,0 ,key0)
    store_si128(block,16,key1)
    store_si128(block,32,ipad)
    store_si128(block,48,ipad)

  /* copy previously calculated hash */
    load_si128(ot0,out,0 )
    load_si128(ot1,out,16)
    store_si128(block,64,ot0)
    store_si128(block,80,ot1)

  /* zero padding */
    zr0 = _mm_setzero_si128();
    store_si128(block,96 ,zr0)
    store_si128(block,112,zr0)

    block[96]  = 0x80;
    block[126] = 0x03;

    copy_hash_iv(out)
  crypto_hashblocks(out,block,128);

  return 1;

  #undef shift_right_partial
  #undef shift_right
  #undef load_si128
  #undef store_si128
  #undef copy_32
}

int crypto_auth_verify(
  const uint8_t *in,
  long publen,
  long inlen,
  const uint8_t *key
)
{
  #define shift_bytes(bit,v1,v2){\
    mask = _mm_set1_epi8(0-((shift>>bit)&1));\
    s2 = m2; s1 = m1; s0 = m0;\
    s2 = _mm_alignr_epi8(s2, s1, v2);\
    s1 = _mm_alignr_epi8(s1, s0, v2);\
    s0 = _mm_slli_si128(s0, v1);\
    m2 = _mm_xor_si128(_mm_andnot_si128(mask, m2),\
                       _mm_and_si128(mask, s2));\
    m1 = _mm_xor_si128(_mm_andnot_si128(mask, m1),\
                       _mm_and_si128(mask, s1));\
    m0 = _mm_xor_si128(_mm_andnot_si128(mask, m0),\
                       _mm_and_si128(mask, s0));\
  }

  __m128i m0,  m1, m2;
  __m128i s0,  s1, s2;
  __m128i cm0, cm1;
  __m128i mask;
  uint8_t mac[32];
  long shift;
  int equal;
  
  assert(48 <= publen);

  crypto_auth_ct(
    mac,
    in,
    publen,
    inlen,
    key);

  m0 = _mm_loadu_si128((__m128i*) (in+publen-48));
  m1 = _mm_loadu_si128((__m128i*) (in+publen-32));
  m2 = _mm_loadu_si128((__m128i*) (in+publen-16));

  shift = (publen - inlen) & 31;

  shift_bytes(4, 16, 0 );
  shift_bytes(3, 8,  8 );
  shift_bytes(2, 4,  12);
  shift_bytes(1, 2,  14);
  shift_bytes(0, 1,  15);

  equal = 1;

  /* load previously calculated mac */
  cm0 = _mm_loadu_si128((__m128i*) (mac + 0 ));
  cm1 = _mm_loadu_si128((__m128i*) (mac + 16));

  /* compare calculated mac with mac */
  m1 = _mm_xor_si128(m1, cm0);
  m2 = _mm_xor_si128(m2, cm1);
  equal &= _mm_testz_si128(m1, m1);
  equal &= _mm_testz_si128(m2, m2);

  return equal;
  
  #undef shift_bytes
}

int decrypt_then_verify(
  uint8_t *out,
  long *out_len,
  const uint8_t *in,
  long in_len,
  const uint8_t *iv,
  const uint8_t *enc_sk,
  const uint8_t *mac_sk)
{
  int i, r;

  assert(0 == ((in_len - HEADER_LENGTH) % 16));

  for(i=0; i<HEADER_LENGTH; i++)
    { out[i] = in[i]; }

  r  = decrypt(
         out + HEADER_LENGTH,
         out_len,
         in  + HEADER_LENGTH,
         in_len - HEADER_LENGTH,
         iv,
         enc_sk); 

  r &= crypto_auth_verify(
         out,                        /* decrypted input                         */
         in_len,                     /* public length = |HDR|+|MSG|+|MAC|+|PAD| */
         (*out_len) + HEADER_LENGTH, /* secret length = |HDR|+|MSG|+|MAC|       */
         mac_sk);                    /* mac secret key  |mac_sk| == 32          */

  /* set ouput */
  r  = (0 - r); 
  *out_len = ((*out_len) + HEADER_LENGTH - CRYPTO_BYTES) & r;

  /* set out to zero if r == 0 */
  for(i=0; i<32; i++)
    { out[i] = out[i] & r; }

  return r & 1;
}

