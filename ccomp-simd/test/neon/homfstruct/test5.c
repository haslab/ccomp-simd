#include "myneon.h"

// test vget_low/vget_high/vcombine

__builtin_t128 f(__builtin_t128 q0) {
  double d0, d1;
  int32x4_t q1, q2, q3, q4;

  q1 = q0;
  q2 = q1;
  q3 = q2;
  q4 = q3;
/*
  d0 = 1.1; d1 = 2.2; q1 = vcombine_u32(d0,d1);
  d0 = vget_low_u32(q1); d1 = vget_high_u32(q1); q2 = vcombine_u32(d0,d1);

  return vaddq_u32(q2,q2);
*/
  return q4;
}
