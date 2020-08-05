#include <stdint.h>
#include <immintrin.h>
/*#include "align.h"*/

/*uint64_t k1[2]      ALIGN16 = {0x0405060700010203ull,0x0c0d0e0f08090a0bull};*/
/*uint64_t k2[2]      ALIGN16 = {0x71374491428A2F98ull,0xE9B5DBA5B5C0FBCFull};*/
/*uint64_t k3[2]      ALIGN16 = {0x59F111F13956C25Bull,0xAB1C5ED5923F82A4ull};*/
/*uint64_t k4[2]      ALIGN16 = {0x12835B01D807AA98ull,0x550C7DC3243185BEull};*/
/*uint64_t k5[2]      ALIGN16 = {0x80DEB1FE72BE5D74ull,0xC19BF1749BDC06A7ull};*/
/*uint64_t k6[2]      ALIGN16 = {0xEFBE4786E49B69C1ull,0x240CA1CC0FC19DC6ull};*/
/*uint64_t k7[2]      ALIGN16 = {0x4A7484AA2DE92C6Full,0x76F988DA5CB0A9DCull};*/
/*uint64_t k8[2]      ALIGN16 = {0xA831C66D983E5152ull,0xBF597FC7B00327C8ull};*/
/*uint64_t k9[2]      ALIGN16 = {0xD5A79147C6E00BF3ull,0x1429296706CA6351ull};*/
/*uint64_t k10[2]     ALIGN16 = {0x2E1B213827B70A85ull,0x53380D134D2C6DFCull};*/
/*uint64_t k11[2]     ALIGN16 = {0x766A0ABB650A7354ull,0x92722C8581C2C92Eull};*/
/*uint64_t k12[2]     ALIGN16 = {0xA81A664BA2BFE8A1ull,0xC76C51A3C24B8B70ull};*/
/*uint64_t k13[2]     ALIGN16 = {0xD6990624D192E819ull,0x106AA070F40E3585ull};*/
/*uint64_t k14[2]     ALIGN16 = {0x1E376C0819A4C116ull,0x34B0BCB52748774Cull};*/
/*uint64_t k15[2]     ALIGN16 = {0x4ED8AA4A391C0CB3ull,0x682E6FF35B9CCA4Full};*/
/*uint64_t k16[2]     ALIGN16 = {0x78A5636F748F82EEull,0x8CC7020884C87814ull};*/
/*uint64_t k17[2]     ALIGN16 = {0xA4506CEB90BEFFFAull,0xC67178F2BEF9A3F7ull};*/
/*uint64_t swaps_0[2] ALIGN16 = {0x0001020304050607ull,0x08090A0B0C0D0E0Full};*/
/*uint64_t swaps_1[2] ALIGN16 = {0x08090A0B0C0D0E0Full,0x0001020304050607ull};*/
/*uint64_t swaps_2[2] ALIGN16 = {0x0405060700010203ull,0x0C0D0E0F08090A0Bull};*/

uint64_t k1[2]      = {0x0405060700010203ull,0x0c0d0e0f08090a0bull};
uint64_t k2[2]      = {0x71374491428A2F98ull,0xE9B5DBA5B5C0FBCFull};
uint64_t k3[2]      = {0x59F111F13956C25Bull,0xAB1C5ED5923F82A4ull};
uint64_t k4[2]      = {0x12835B01D807AA98ull,0x550C7DC3243185BEull};
uint64_t k5[2]      = {0x80DEB1FE72BE5D74ull,0xC19BF1749BDC06A7ull};
uint64_t k6[2]      = {0xEFBE4786E49B69C1ull,0x240CA1CC0FC19DC6ull};
uint64_t k7[2]      = {0x4A7484AA2DE92C6Full,0x76F988DA5CB0A9DCull};
uint64_t k8[2]      = {0xA831C66D983E5152ull,0xBF597FC7B00327C8ull};
uint64_t k9[2]      = {0xD5A79147C6E00BF3ull,0x1429296706CA6351ull};
uint64_t k10[2]     = {0x2E1B213827B70A85ull,0x53380D134D2C6DFCull};
uint64_t k11[2]     = {0x766A0ABB650A7354ull,0x92722C8581C2C92Eull};
uint64_t k12[2]     = {0xA81A664BA2BFE8A1ull,0xC76C51A3C24B8B70ull};
uint64_t k13[2]     = {0xD6990624D192E819ull,0x106AA070F40E3585ull};
uint64_t k14[2]     = {0x1E376C0819A4C116ull,0x34B0BCB52748774Cull};
uint64_t k15[2]     = {0x4ED8AA4A391C0CB3ull,0x682E6FF35B9CCA4Full};
uint64_t k16[2]     = {0x78A5636F748F82EEull,0x8CC7020884C87814ull};
uint64_t k17[2]     = {0xA4506CEB90BEFFFAull,0xC67178F2BEF9A3F7ull};
uint64_t swaps_0[2] = {0x0001020304050607ull,0x08090A0B0C0D0E0Full};
uint64_t swaps_1[2] = {0x08090A0B0C0D0E0Full,0x0001020304050607ull};
uint64_t swaps_2[2] = {0x0405060700010203ull,0x0C0D0E0F08090A0Bull};

int crypto_hashblocks(
  unsigned char *statebytes,
  const unsigned char *data,
  unsigned long input_len
)
{
   uint32_t num_blks;

   __m128i swaps0, swaps1, swaps2;
   __m128i state0, state1;
   __m128i msg;
   __m128i msgtmp0, msgtmp1, msgtmp2, msgtmp3;
   __m128i tmp;
   __m128i shuf_mask;
   __m128i abef_save, cdgh_save;

   /* Load initial hash values */
   /* Need to reorder these appropriately */
   /* DCBA, HGFE -> ABEF, CDGH */
   swaps0 = _mm_load_si128((__m128i*) swaps_0);
   swaps1 = _mm_load_si128((__m128i*) swaps_1);
   tmp    = _mm_loadu_si128((__m128i*) (statebytes+0));
   state1 = _mm_loadu_si128((__m128i*) (statebytes+16));

   tmp    = _mm_shuffle_epi8(tmp, swaps0);
   state1 = _mm_shuffle_epi8(state1, swaps1);

   state0 = _mm_alignr_epi8(tmp, state1, 8);    /* ABEF */
   state1 = _mm_blend_epi16(state1, tmp, 0xF0); /* EF(GH) (+b+) (CD)AB => CDGH */

   shuf_mask = _mm_load_si128((__m128i*) k1);

   num_blks = input_len >> 6;
   while (num_blks > 0)
   {
      /* Save hash values for addition after rounds */
      abef_save = state0;
      cdgh_save = state1;

      /* Rounds 0-3 */
      msg     = _mm_loadu_si128((__m128i*) data);
      msgtmp0 = _mm_shuffle_epi8(msg, shuf_mask);
         msg    = _mm_add_epi32(msgtmp0, _mm_load_si128((__m128i*) k2));
         state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
         msg    = _mm_shuffle_epi32(msg, 0x0E);
         state0 = _mm_sha256rnds2_epu32(state0, state1, msg);

      /* Rounds 4-7 */
      msgtmp1 = _mm_loadu_si128((__m128i*) (data+16));
      msgtmp1 = _mm_shuffle_epi8(msgtmp1, shuf_mask);
         msg    = _mm_add_epi32(msgtmp1, _mm_load_si128((__m128i*) k3));
         state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
         msg    = _mm_shuffle_epi32(msg, 0x0E);
         state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
      msgtmp0 = _mm_sha256msg1_epu32(msgtmp0, msgtmp1);

      /* Rounds 8-11 */
      msgtmp2 = _mm_loadu_si128((__m128i*) (data+32));
      msgtmp2 = _mm_shuffle_epi8(msgtmp2, shuf_mask);
         msg    = _mm_add_epi32(msgtmp2, _mm_load_si128((__m128i*) k4));
         state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
         msg    = _mm_shuffle_epi32(msg, 0x0E);
         state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
      msgtmp1 = _mm_sha256msg1_epu32(msgtmp1, msgtmp2);


      /* Rounds 12-15 */
      msgtmp3 = _mm_loadu_si128((__m128i*) (data+48));
      msgtmp3 = _mm_shuffle_epi8(msgtmp3, shuf_mask);
         msg    = _mm_add_epi32(msgtmp3, _mm_load_si128((__m128i*) k5));
         state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
      tmp     = _mm_alignr_epi8(msgtmp3, msgtmp2, 4);
      msgtmp0 = _mm_add_epi32(msgtmp0, tmp);
      msgtmp0 = _mm_sha256msg2_epu32(msgtmp0, msgtmp3);
         msg    = _mm_shuffle_epi32(msg, 0x0E);
         state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
      msgtmp2 = _mm_sha256msg1_epu32(msgtmp2, msgtmp3);


      /* Rounds 16-19 */
         msg    = _mm_add_epi32(msgtmp0, _mm_load_si128((__m128i*) k6));
         state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
      tmp     = _mm_alignr_epi8(msgtmp0, msgtmp3, 4);
      msgtmp1 = _mm_add_epi32(msgtmp1, tmp);
      msgtmp1 = _mm_sha256msg2_epu32(msgtmp1, msgtmp0);
         msg    = _mm_shuffle_epi32(msg, 0x0E);
         state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
      msgtmp3 = _mm_sha256msg1_epu32(msgtmp3, msgtmp0);

      /* Rounds 20-23 */
         msg    = _mm_add_epi32(msgtmp1, _mm_load_si128((__m128i*) k7));
         state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
      tmp     = _mm_alignr_epi8(msgtmp1, msgtmp0, 4);
      msgtmp2 = _mm_add_epi32(msgtmp2, tmp);
      msgtmp2 = _mm_sha256msg2_epu32(msgtmp2, msgtmp1);
         msg    = _mm_shuffle_epi32(msg, 0x0E);
         state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
      msgtmp0 = _mm_sha256msg1_epu32(msgtmp0, msgtmp1);

      /* Rounds 24-27 */
         msg    = _mm_add_epi32(msgtmp2, _mm_load_si128((__m128i*) k8));
         state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
      tmp     = _mm_alignr_epi8(msgtmp2, msgtmp1, 4);
      msgtmp3 = _mm_add_epi32(msgtmp3, tmp);
      msgtmp3 = _mm_sha256msg2_epu32(msgtmp3, msgtmp2);
         msg    = _mm_shuffle_epi32(msg, 0x0E);
         state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
      msgtmp1 = _mm_sha256msg1_epu32(msgtmp1, msgtmp2);

      /* Rounds 28-31 */
         msg    = _mm_add_epi32(msgtmp3, _mm_load_si128((__m128i*) k9));
         state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
      tmp     = _mm_alignr_epi8(msgtmp3, msgtmp2, 4);
      msgtmp0 = _mm_add_epi32(msgtmp0, tmp);
      msgtmp0 = _mm_sha256msg2_epu32(msgtmp0, msgtmp3);
         msg    = _mm_shuffle_epi32(msg, 0x0E);
         state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
      msgtmp2 = _mm_sha256msg1_epu32(msgtmp2, msgtmp3);

      /* Rounds 32-35 */
         msg    = _mm_add_epi32(msgtmp0, _mm_load_si128((__m128i*) k10));
         state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
      tmp     = _mm_alignr_epi8(msgtmp0, msgtmp3, 4);
      msgtmp1 = _mm_add_epi32(msgtmp1, tmp);
      msgtmp1 = _mm_sha256msg2_epu32(msgtmp1, msgtmp0);
         msg    = _mm_shuffle_epi32(msg, 0x0E);
         state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
      msgtmp3 = _mm_sha256msg1_epu32(msgtmp3, msgtmp0);

      /* Rounds 36-39 */
         msg    = _mm_add_epi32(msgtmp1, _mm_load_si128((__m128i*) k11));
         state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
      tmp     = _mm_alignr_epi8(msgtmp1, msgtmp0, 4);
      msgtmp2 = _mm_add_epi32(msgtmp2, tmp);
      msgtmp2 = _mm_sha256msg2_epu32(msgtmp2, msgtmp1);
         msg    = _mm_shuffle_epi32(msg, 0x0E);
         state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
      msgtmp0 = _mm_sha256msg1_epu32(msgtmp0, msgtmp1);

      /* Rounds 40-43 */
         msg    = _mm_add_epi32(msgtmp2, _mm_load_si128((__m128i*) k12));
         state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
      tmp     = _mm_alignr_epi8(msgtmp2, msgtmp1, 4);
      msgtmp3 = _mm_add_epi32(msgtmp3, tmp);
      msgtmp3 = _mm_sha256msg2_epu32(msgtmp3, msgtmp2);
         msg    = _mm_shuffle_epi32(msg, 0x0E);
         state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
      msgtmp1 = _mm_sha256msg1_epu32(msgtmp1, msgtmp2);

      /* Rounds 44-47 */
         msg    = _mm_add_epi32(msgtmp3, _mm_load_si128((__m128i*) k13));
         state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
      tmp     = _mm_alignr_epi8(msgtmp3, msgtmp2, 4);
      msgtmp0 = _mm_add_epi32(msgtmp0, tmp);
      msgtmp0 = _mm_sha256msg2_epu32(msgtmp0, msgtmp3);
         msg    = _mm_shuffle_epi32(msg, 0x0E);
         state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
      msgtmp2 = _mm_sha256msg1_epu32(msgtmp2, msgtmp3);

      /* Rounds 48-51 */
         msg    = _mm_add_epi32(msgtmp0, _mm_load_si128((__m128i*) k14));
         state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
      tmp     = _mm_alignr_epi8(msgtmp0, msgtmp3, 4);
      msgtmp1 = _mm_add_epi32(msgtmp1, tmp);
      msgtmp1 = _mm_sha256msg2_epu32(msgtmp1, msgtmp0);
         msg    = _mm_shuffle_epi32(msg, 0x0E);
         state0 = _mm_sha256rnds2_epu32(state0, state1, msg);
      msgtmp3 = _mm_sha256msg1_epu32(msgtmp3, msgtmp0);

      /* Rounds 52-55 */
         msg    = _mm_add_epi32(msgtmp1, _mm_load_si128((__m128i*) k15));
         state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
      tmp     = _mm_alignr_epi8(msgtmp1, msgtmp0, 4);
      msgtmp2 = _mm_add_epi32(msgtmp2, tmp);
      msgtmp2 = _mm_sha256msg2_epu32(msgtmp2, msgtmp1);
         msg    = _mm_shuffle_epi32(msg, 0x0E);
         state0 = _mm_sha256rnds2_epu32(state0, state1, msg);

      /* Rounds 56-59 */
         msg    = _mm_add_epi32(msgtmp2, 
                  _mm_load_si128((__m128i*) k16));
         state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
      tmp     = _mm_alignr_epi8(msgtmp2, msgtmp1, 4);
      msgtmp3 = _mm_add_epi32(msgtmp3, tmp);
      msgtmp3 = _mm_sha256msg2_epu32(msgtmp3, msgtmp2);
         msg    = _mm_shuffle_epi32(msg, 0x0E);
         state0 = _mm_sha256rnds2_epu32(state0, state1, msg);

      /* Rounds 60-63 */
         msg    = _mm_add_epi32(msgtmp3, _mm_load_si128((__m128i*) k17));
         state1 = _mm_sha256rnds2_epu32(state1, state0, msg);
         msg    = _mm_shuffle_epi32(msg, 0x0E);
         state0 = _mm_sha256rnds2_epu32(state0, state1, msg);

      /* Add current hash values with previously saved */
      state0 = _mm_add_epi32(state0, abef_save);
      state1 = _mm_add_epi32(state1, cdgh_save);

      data += 64;
      num_blks--;
   }

   /* Write hash values back in the correct order */
   tmp    = _mm_shuffle_epi32(state0, 0x1B);    /* FEBA */
   state1 = _mm_shuffle_epi32(state1, 0xB1);    /* DCHG */
   state0 = _mm_blend_epi16(tmp, state1, 0xF0); /* DCBA */
   state1 = _mm_alignr_epi8(state1, tmp, 8);    /* ABEF */

  swaps2 = _mm_load_si128((__m128i*) swaps_2);
  state0 = _mm_shuffle_epi8(state0,  swaps2);
  state1 = _mm_shuffle_epi8(state1,  swaps2);

   _mm_storeu_si128((__m128i*) statebytes,      state0);
   _mm_storeu_si128((__m128i*) (statebytes+16), state1);

  return 1;
}

