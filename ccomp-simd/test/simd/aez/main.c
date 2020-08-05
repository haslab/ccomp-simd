#include <stdio.h>
#include <string.h>

#if 0
int crypto_aead_encrypt(
    unsigned char *c,unsigned long long *clen,
    const unsigned char *m,unsigned long long mlen,
    const unsigned char *ad,unsigned long long adlen,
    const unsigned char *nsec,
    const unsigned char *npub,
    const unsigned char *k
)
   ...
   ... the code for the cipher implementation goes here,
   ... generating a ciphertext c[0],c[1],...,c[*clen-1]
   ... from a plaintext m[0],m[1],...,m[mlen-1]
   ... and associated data ad[0],ad[1],...,ad[adlen-1]
   ... and secret message number nsec[0],nsec[1],...
   ... and public message number npub[0],npub[1],...
   ... and secret key k[0],k[1],...
   ...
#endif


extern int crypto_aead_encrypt(
    unsigned char *c,unsigned long long *clen,
    const unsigned char *m,unsigned long long mlen,
    const unsigned char *ad,unsigned long long adlen,
    const unsigned char *nsec,
    const unsigned char *npub,
    const unsigned char *k
);

extern int crypto_aead_decrypt(
    unsigned char *m,unsigned long long *mlen,
    unsigned char *nsec,
    const unsigned char *c,unsigned long long clen,
    const unsigned char *ad,unsigned long long adlen,
    const unsigned char *npub,
    const unsigned char *k
);

int
main (int argc, char *argv[])
{
  int r, i;

  unsigned char c[1000];
  unsigned long long clen = 1000;
  memset(c, 0x0, clen*sizeof(unsigned char));

  unsigned char m[10];
  unsigned long long mlen = 10;
  memset(m, 0x1, mlen*sizeof(unsigned char));

  unsigned char om[100];
  unsigned long long omlen = 100;
  memset(om, 0x0, omlen*sizeof(unsigned char));

  unsigned char ad[10];
  unsigned long long adlen = 10;
  memset(ad, 0x2, adlen*sizeof(unsigned char));

  unsigned char nsec[16];
  unsigned char npub[16];
  unsigned char k[48];

  memset(nsec, 0x3, 16*sizeof(unsigned char));
  memset(npub, 0x4, 16*sizeof(unsigned char));
  memset(k,    0x5, 48*sizeof(unsigned char));

  long l;
  for(l=0; l<1/****/; l++)
  {
      r = crypto_aead_encrypt(c, &clen, m, mlen, ad, adlen, nsec, npub, k);
/*      for(i=0;i<clen;i++)*/
/*        printf("%02x ", c[i]);*/
/*      printf("r=%d\n",r);*/

      r = crypto_aead_decrypt(om, &omlen, nsec, c, clen, ad, adlen, npub, k);
/*      for(i=0;i<omlen;i++)*/
/*        printf("%02x ", om[i]);*/
/*      printf("r=%d\n",r);*/
  }

  for(i=0;i<omlen;i++)
    printf("%02x ", om[i]);
  printf("r=%d\n",r);

  return 0;
}

