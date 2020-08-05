#include "aez_ni.c"

#if ! defined N
# define N 4
#endif

unsigned char c[N + 16];
unsigned char m[N];
unsigned char t[N + 16];
unsigned char ad[10] = {0};
unsigned char npub[16];
unsigned char k[48];

volatile
long long public;
volatile
long long secret;

#define input_array(a, src) \
	do { \
		for (int i = 0; i < sizeof(a) / sizeof(a[0]); ++i) \
		{ \
			__builtin_annot("unroll", 0); \
			a[i] = src; \
		} \
		__builtin_annot("eol", 0); \
	} while(0)

void
init()
{
	input_array(m, public);
	input_array(k, secret);
}

int
main(void)
{
    init();
	int r = 0;
	r += crypto_aead_encrypt(c, 0, m, sizeof(m), ad, sizeof(ad), 0, npub, k);
	r += crypto_aead_decrypt(t, 0, 0, c, sizeof(c), ad, sizeof(ad), npub, k);
	return r;
}
