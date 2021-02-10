#include "myneon.h"

// test vget_low/vget_high/vcombine

__builtin_t128 f(__builtin_t128 q0, double d0) {
  double d1, d2, d3, d4;
  int32x4_t q1, q2, q3, q4;

  d1 = 1.1; d2 = 2.2; q1 = vcombine_u32(d1,d2);
  d3 = vget_low_u32(q1); d4 = vget_high_u32(q1); q2 = vcombine_u32(d3,d4);

  return vaddq_u32(q1,q2);
}
