#ifndef SMULT_H
#define SMULT_H

//#include "crypto_scalarmult.h"
#define smult crypto_scalarmult
#define smult_base crypto_scalarmult_base

int smult_base(unsigned char *q, const unsigned char *n);

#endif
