#include "aezv4/encrypt.c"

#if ! defined N
# define N 4
#endif

unsigned char c[N + 16];
unsigned char m[N];
unsigned char t[N + 16];
unsigned char ad[4] = {0};
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
init(void)
{
	input_array(m, public);
	input_array(k, secret);
}

int
get_ad_size(void)
{
	int sz = public;
	if (sz <= 0) return 0;
	if (sizeof(ad) < sz) return sizeof(ad);
	return sz;
}

int
main(void)
{
	init();
	int r = 0;
	int ad_size = get_ad_size();
	int mlen = sizeof(m);
	int clen = mlen + 16;
	r += crypto_aead_encrypt(c, 0, m, mlen, ad, ad_size, 0, npub, k);
	r += crypto_aead_decrypt(t, 0, 0, c, clen, ad, ad_size, npub, k);
	return r;
}
