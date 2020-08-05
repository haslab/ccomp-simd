#define CT_ANALYSIS
#define assert(...)

#include "src/aes128.c"
#include "src/sha256-msha.c"
#include "src/decrypt_verify.c"

#if ! defined N
# define N 1
#endif
#define SZ (((N) << 4) + HEADER_LENGTH)

uint8_t plain[SZ];
uint8_t _seq_header_ciphertext[SZ];
uint8_t _enc_iv[16];
uint8_t _enc_key[16];
uint8_t _mac_key[32];

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
	input_array(_seq_header_ciphertext, secret);
	input_array(_enc_iv, secret);
	input_array(_enc_key, secret);
	input_array(_mac_key, secret);
}

int
main(void)
{
	long plain_len = SZ;
	return
	decrypt_then_verify(
		plain,
		&plain_len,
		_seq_header_ciphertext,
		sizeof(plain),
		_enc_iv,
		_enc_key,
		_mac_key);
}
