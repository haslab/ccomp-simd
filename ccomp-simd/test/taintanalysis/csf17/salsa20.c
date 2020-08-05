/*
salsa20-ref.c version 20051118
D. J. Bernstein
Public domain.
*/

#include <stdio.h>
#include "ecrypt-sync.h"

#define printf(...)
#define fflush(...)

#define ROTATE(v,c) (ROTL32(v,c))
#define XOR(v,w) ((v) ^ (w))
#define PLUS(v,w) (U32V((v) + (w)))
#define PLUSONE(v) (PLUS((v),1))

u8 output[64];

static void salsa20_wordtobyte(u8 output[64],const u32 input[16])
{
  u32 x[16];
  int i;

  for (i = 0;i < 16;++i) { __builtin_annot("unroll", 0); x[i] = input[i]; }
  __builtin_annot("eol", 0);
  for (i = 20;i > 0;i -= 2) {
    x[ 4] = XOR(x[ 4],ROTATE(PLUS(x[ 0],x[12]), 7));
    x[ 8] = XOR(x[ 8],ROTATE(PLUS(x[ 4],x[ 0]), 9));
    x[12] = XOR(x[12],ROTATE(PLUS(x[ 8],x[ 4]),13));
    x[ 0] = XOR(x[ 0],ROTATE(PLUS(x[12],x[ 8]),18));
    x[ 9] = XOR(x[ 9],ROTATE(PLUS(x[ 5],x[ 1]), 7));
    x[13] = XOR(x[13],ROTATE(PLUS(x[ 9],x[ 5]), 9));
    x[ 1] = XOR(x[ 1],ROTATE(PLUS(x[13],x[ 9]),13));
    x[ 5] = XOR(x[ 5],ROTATE(PLUS(x[ 1],x[13]),18));
    x[14] = XOR(x[14],ROTATE(PLUS(x[10],x[ 6]), 7));
    x[ 2] = XOR(x[ 2],ROTATE(PLUS(x[14],x[10]), 9));
    x[ 6] = XOR(x[ 6],ROTATE(PLUS(x[ 2],x[14]),13));
    x[10] = XOR(x[10],ROTATE(PLUS(x[ 6],x[ 2]),18));
    x[ 3] = XOR(x[ 3],ROTATE(PLUS(x[15],x[11]), 7));
    x[ 7] = XOR(x[ 7],ROTATE(PLUS(x[ 3],x[15]), 9));
    x[11] = XOR(x[11],ROTATE(PLUS(x[ 7],x[ 3]),13));
    x[15] = XOR(x[15],ROTATE(PLUS(x[11],x[ 7]),18));
    x[ 1] = XOR(x[ 1],ROTATE(PLUS(x[ 0],x[ 3]), 7));
    x[ 2] = XOR(x[ 2],ROTATE(PLUS(x[ 1],x[ 0]), 9));
    x[ 3] = XOR(x[ 3],ROTATE(PLUS(x[ 2],x[ 1]),13));
    x[ 0] = XOR(x[ 0],ROTATE(PLUS(x[ 3],x[ 2]),18));
    x[ 6] = XOR(x[ 6],ROTATE(PLUS(x[ 5],x[ 4]), 7));
    x[ 7] = XOR(x[ 7],ROTATE(PLUS(x[ 6],x[ 5]), 9));
    x[ 4] = XOR(x[ 4],ROTATE(PLUS(x[ 7],x[ 6]),13));
    x[ 5] = XOR(x[ 5],ROTATE(PLUS(x[ 4],x[ 7]),18));
    x[11] = XOR(x[11],ROTATE(PLUS(x[10],x[ 9]), 7));
    x[ 8] = XOR(x[ 8],ROTATE(PLUS(x[11],x[10]), 9));
    x[ 9] = XOR(x[ 9],ROTATE(PLUS(x[ 8],x[11]),13));
    x[10] = XOR(x[10],ROTATE(PLUS(x[ 9],x[ 8]),18));
    x[12] = XOR(x[12],ROTATE(PLUS(x[15],x[14]), 7));
    x[13] = XOR(x[13],ROTATE(PLUS(x[12],x[15]), 9));
    x[14] = XOR(x[14],ROTATE(PLUS(x[13],x[12]),13));
    x[15] = XOR(x[15],ROTATE(PLUS(x[14],x[13]),18));
  }
  for (i = 0;i < 16;++i) x[i] = PLUS(x[i],input[i]);
  for (i = 0;i < 16;++i) U32TO8_LITTLE(output + 4 * i,x[i]);
}

void ECRYPT_init(void)
{
  return;
}

static const char sigma_tau[32] = "expand 32-byte kexpand 16-byte k";
#define sigma (sigma_tau + 0)
#define tau (sigma_tau + 16)

void ECRYPT_keysetup(ECRYPT_ctx *x,const u8 *k,u32 kbits,u32 ivbits)
{
  const char *constants;

  x->input[1] = U8TO32_LITTLE(k + 0);
  x->input[2] = U8TO32_LITTLE(k + 4);
  x->input[3] = U8TO32_LITTLE(k + 8);
  x->input[4] = U8TO32_LITTLE(k + 12);
  if (kbits == 256) { /* recommended */
    k += 16;
    constants = sigma;
  } else { /* kbits == 128 */
    constants = tau;
  }
  x->input[11] = U8TO32_LITTLE(k + 0);
  x->input[12] = U8TO32_LITTLE(k + 4);
  x->input[13] = U8TO32_LITTLE(k + 8);
  x->input[14] = U8TO32_LITTLE(k + 12);
  x->input[0] = U8TO32_LITTLE(constants + 0);
  x->input[5] = U8TO32_LITTLE(constants + 4);
  x->input[10] = U8TO32_LITTLE(constants + 8);
  x->input[15] = U8TO32_LITTLE(constants + 12);
}

void ECRYPT_ivsetup(ECRYPT_ctx *x,const u8 *iv)
{
  x->input[6] = U8TO32_LITTLE(iv + 0);
  x->input[7] = U8TO32_LITTLE(iv + 4);
  x->input[8] = 0;
  x->input[9] = 0;
}

void ECRYPT_encrypt_bytes(ECRYPT_ctx *x,const u8 *m,u8 *c,u32 bytes)
{
  int i;

  if (!bytes) return;
  for (;;) {
    salsa20_wordtobyte(output,x->input);
    x->input[8] = PLUSONE(x->input[8]);
    if (!x->input[8]) {
      x->input[9] = PLUSONE(x->input[9]);
      /* stopping at 2^70 bytes per nonce is user's responsibility */
    }
    /*verasco_assert (bytes <= 64);*/ {
      for (i = 0;i < bytes;++i) c[i] = m[i] ^ output[i];
      return;
    }
    for (i = 0;i < 64;++i) c[i] = m[i] ^ output[i];
    bytes -= 64;
    c += 64;
    m += 64;
  }
}

void ECRYPT_encrypt_bytes0(ECRYPT_ctx *x,const u8 *m,u8 *c,u32 bytes)
{ ECRYPT_encrypt_bytes(x,m,c,bytes); }

void ECRYPT_decrypt_bytes(ECRYPT_ctx *x,const u8 *c,u8 *m,u32 bytes)
{
  ECRYPT_encrypt_bytes(x,c,m,bytes);
}

void ECRYPT_keystream_bytes(ECRYPT_ctx *x,u8 *stream,u32 bytes)
{
  u32 i;
  for (i = 0;i < bytes;++i) stream[i] = 0;
  ECRYPT_encrypt_bytes(x,stream,stream,bytes);
}

#if ! defined N
// 4096
# define N 64
#endif

u8 mcd[3 * N];
#define m (mcd + 0)
#define c (mcd + N)
#define d (mcd + 2 * N)
u8 k[32];
u8 v[8];

int main(void)
{
  ECRYPT_ctx x;
  int i;
  int bytes;
  int loop;

  for (loop = 0;loop < 10;++loop) {
    /*verasco_unroll(1);*/
    for (bytes = 0;bytes <= N;++bytes) {
      /*verasco_unroll(1);*/
      if (loop & 1)
        ECRYPT_keysetup(&x,k,256,64);
      else
        ECRYPT_keysetup(&x,k,128,64);
      ECRYPT_ivsetup(&x,v);
      ECRYPT_encrypt_bytes0(&x,m,c,bytes);
      ECRYPT_ivsetup(&x,v);
      ECRYPT_decrypt_bytes(&x,c,d,bytes);
      for (i = 0;i < bytes;++i)
        ; //if (d[i] != m[i]) printf("mismatch at position %d/%d\n",i,bytes);
      switch(bytes % 3) {
  case 0: for (i = 0;(i < bytes) && (i < 32);++i) { u8 ki = k[i], ci = c[i]; k[i] = ki ^ ci; } break;
  case 1: for (i = 0;(i < bytes) && (i < 8);++i) { u8 vi = v[i], ci = c[i]; v[i] = vi ^ ci; } break;
  case 2: for (i = 0;i < bytes;++i) { u8 ci = c[i]; m[i] = ci; } break;
      }
    }
    for (i = 0;i < 32;++i) printf("%02x",k[i]); printf("\n"); fflush(stdout);
  }

  for (loop = 0;loop < 134217728;++loop) {
    ECRYPT_encrypt_bytes0(&x,c,c,N);
  }
  for (i = 0;i < 16;++i) printf("%02x",k[i]); printf("\n"); fflush(stdout);

  return 0;
}
