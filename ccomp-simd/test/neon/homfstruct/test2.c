#include "myneon.h"

__builtin_t128 f(__builtin_t128 x, __builtin_t128 y) {
  uint32x4x2_t sq1, sq2, sq3, sq4;
  __builtin_t128 v0, v1, v2, v3, v4, v5, v6, v7, v8, v9;

  sq1 = vtrnq_u32(v0, v1);
  sq2 = vtrnq_u32(v3, v2);
  sq3 = vtrnq_u32(v6, v3);
  sq4 = vswpq(v5, v8);
  return sq4.val1;
}
