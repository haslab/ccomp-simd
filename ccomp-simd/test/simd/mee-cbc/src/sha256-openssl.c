#include <stdint.h>
#include <string.h>
#include <openssl/sha.h>

SHA256_CTX context;

int crypto_hashblocks(
  uint8_t *statebytes,
  const uint8_t *input,
  unsigned long input_len
)
{
  #define load_state(p,o)(\
    (p[o+3]<<0 ) | \
    (p[o+2]<<8 ) | \
    (p[o+1]<<16) | \
    (p[o]  <<24)   \
    )

  #define save_state(v,o,p) {\
    v[o]   = (p >> 24) & 0xff;\
    v[o+1] = (p >> 16) & 0xff;\
    v[o+2] = (p >> 8 ) & 0xff;\
    v[o+3] = (p >> 0 ) & 0xff;} 

  context.h[0] = load_state(statebytes,0 );
  context.h[1] = load_state(statebytes,4 );
  context.h[2] = load_state(statebytes,8 );
  context.h[3] = load_state(statebytes,12);
  context.h[4] = load_state(statebytes,16);
  context.h[5] = load_state(statebytes,20);
  context.h[6] = load_state(statebytes,24);
  context.h[7] = load_state(statebytes,28);
  context.md_len = SHA256_DIGEST_LENGTH;

  SHA256_Update(&context, (unsigned char*)input, input_len);

  save_state(statebytes,0 ,context.h[0]);
  save_state(statebytes,4 ,context.h[1]);
  save_state(statebytes,8 ,context.h[2]);
  save_state(statebytes,12,context.h[3]);
  save_state(statebytes,16,context.h[4]);
  save_state(statebytes,20,context.h[5]);
  save_state(statebytes,24,context.h[6]);
  save_state(statebytes,28,context.h[7]);

  return 1;

  #undef save_state
  #undef load_state
}

