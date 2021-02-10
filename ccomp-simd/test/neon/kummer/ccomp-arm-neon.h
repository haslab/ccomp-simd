#ifndef _COMPCERT_ARM_NEON_H

#define _COMPCERT_ARM_NEON_H

#ifndef __ARM_NEON__
#error You must enable NEON instructions (e.g. -mneon) to use arm_neon.h
#else

#include <stdint.h>

/************************
Builtin type declarations
*************************/

/* PREDEFINED TYPES */
typedef float __builtin_t32;
typedef double __builtin_t64;
//typedef struct __builtin_t64x2 {__builtin_t64 val[2];} __builtin_t64x2;
//typedef struct __builtin_t64x3 {__builtin_t64 val[3];} __builtin_t64x3;
//typedef struct __builtin_t64x4 {__builtin_t64 val[4];} __builtin_t64x3;
//typedef __builtin_t128;
//typedef struct __builtin_t128x2 {__builtin_t128 val[2];} __builtin_t128x2;
//typedef struct __builtin_t128x3 {__builtin_t128 val[3];} __builtin_t128x3;
//typedef struct __builtin_t128x4 {__builtin_t128 val[4];} __builtin_t128x4;

typedef __builtin_t64 int8x8_t, int16x4_t, int32x2_t, int64x1_t;
typedef __builtin_t64 float32x2_t, poly8x8_t, poly16x4_t, uint8x8_t;
typedef __builtin_t64 uint16x4_t, uint32x2_t, uint64x1_t;
typedef __builtin_t128 int8x16_t, int16x8_t, int32x4_t, int64x2_t;
typedef __builtin_t128 float32x4_t, poly8x16_t, poly16x8_t;
typedef __builtin_t128 uint8x16_t, uint16x8_t, uint32x4_t, uint64x2_t;

typedef float float32_t;
typedef unsigned char poly8_t;
typedef unsigned short poly16_t;

typedef struct __builtin_t64x2 int8x8x2_t,int16x4x2_t,int32x2x2_t,int64x1x2_t;
typedef struct __builtin_t64x2 uint8x8x2_t,uint16x4x2_t,uint32x2x2_t,uint64x1x2_t;
typedef struct  __builtin_t64x2 float32x2x2_t,poly8x8x2_t,poly16x4x2_t;
typedef struct  __builtin_t128x2 int8x16x2_t,int16x8x2_t,int32x4x2_t,int64x2x2_t;
typedef struct  __builtin_t128x2 uint8x16x2_t,uint16x8x2_t,uint32x4x2_t,uint64x2x2_t;
typedef struct  __builtin_t128x2 float32x4x2_t,poly8x16x2_t,poly16x8x2_t;

typedef struct  __builtin_t64x3 int8x8x3_t,int16x4x3_t,int32x2x3_t,int64x1x3_t;
typedef struct  __builtin_t64x3 uint8x8x3_t,uint16x4x3_t,uint32x2x3_t,uint64x1x3_t;
typedef struct  __builtin_t64x3 float32x2x3_t,poly8x8x3_t,poly16x4x3_t;
typedef struct  __builtin_t128x3 int8x16x3_t,int16x8x3_t,int32x4x3_t,int64x2x3_t;
typedef struct  __builtin_t128x3 uint8x16x3_t,uint16x8x3_t,uint32x4x3_t,uint64x2x3_t;
typedef struct  __builtin_t128x3 float32x4x3_t, poly8x16x3_t, poly16x8x3_t;

typedef struct  __builtin_t64x4 int8x8x4_t,int16x4x4_t,int32x2x4_t,int64x1x4_t;
typedef struct  __builtin_t64x4 uint8x8x4_t,uint16x4x4_t,uint32x2x4_t,uint64x1x4_t;
typedef struct  __builtin_t64x4 float32x2x4_t,poly8x8x4_t,poly16x4x4_t;
typedef struct  __builtin_t128x4 int8x16x4_t,int16x8x4_t,int32x4x4_t,int64x2x4_t;
typedef struct  __builtin_t128x4 uint8x16x4_t,uint16x8x4_t,uint32x4x4_t,uint64x2x4_t;
typedef struct  __builtin_t128x4 float32x4x4_t,poly8x16x4_t,poly16x8x4_t;

/***************************
Additional Compcert Builtins
****************************/
#define vswp_s8(__a, __b) __builtin_vswp(__a, __b)
#define vswp_s16(__a, __b) __builtin_vswp(__a, __b)
#define vswp_s32(__a, __b) __builtin_vswp(__a, __b)
#define vswp_s64(__a, __b) __builtin_vswp(__a, __b)
#define vswp_u8(__a, __b) __builtin_vswp(__a, __b)
#define vswp_u16(__a, __b) __builtin_vswp(__a, __b)
#define vswp_u32(__a, __b) __builtin_vswp(__a, __b)
#define vswp_u64(__a, __b) __builtin_vswp(__a, __b)
#define vswp_f32(__a, __b) __builtin_vswp(__a, __b)
#define vswp_p8(__a, __b) __builtin_vswp(__a, __b)
#define vswp_p16(__a, __b) __builtin_vswp(__a, __b)

#define vswpq_s8(__a, __b) __builtin_vswpq(__a, __b)
#define vswpq_s16(__a, __b) __builtin_vswpq(__a, __b)
#define vswpq_s32(__a, __b) __builtin_vswpq(__a, __b)
#define vswpq_s64(__a, __b) __builtin_vswpq(__a, __b)
#define vswpq_u8(__a, __b) __builtin_vswpq(__a, __b)
#define vswpq_u16(__a, __b) __builtin_vswpq(__a, __b)
#define vswpq_u32(__a, __b) __builtin_vswpq(__a, __b)
#define vswpq_u64(__a, __b) __builtin_vswpq(__a, __b)
#define vswpq_f32(__a, __b) __builtin_vswpq(__a, __b)
#define vswpq_p8(__a, __b) __builtin_vswpq(__a, __b)
#define vswpq_p16(__a, __b) __builtin_vswpq(__a, __b)

#define vset_low_s8(__a,__b) __builtin_vset_low(__a,__b)
#define vset_low_s16(__a,__b) __builtin_vset_low(__a,__b)
#define vset_low_s32(__a,__b) __builtin_vset_low(__a,__b)
#define vset_low_s64(__a,__b) __builtin_vset_low(__a,__b)
#define vset_low_u8(__a,__b) __builtin_vset_low(__a,__b)
#define vset_low_u16(__a,__b) __builtin_vset_low(__a,__b)
#define vset_low_u32(__a,__b) __builtin_vset_low(__a,__b)
#define vset_low_u64(__a,__b) __builtin_vset_low(__a,__b)
#define vset_low_p8(__a,__b) __builtin_vset_low(__a,__b)
#define vset_low_p16(__a,__b) __builtin_vset_low(__a,__b)
#define vset_low_f16(__a,__b) __builtin_vset_low(__a,__b)
#define vset_low_f32(__a,__b) __builtin_vset_low(__a,__b)

#define vset_high_s8(__a,__b) __builtin_vset_high(__a,__b)
#define vset_high_s16(__a,__b) __builtin_vset_high(__a,__b)
#define vset_high_s32(__a,__b) __builtin_vset_high(__a,__b)
#define vset_high_s64(__a,__b) __builtin_vset_high(__a,__b)
#define vset_high_u8(__a,__b) __builtin_vset_high(__a,__b)
#define vset_high_u16(__a,__b) __builtin_vset_high(__a,__b)
#define vset_high_u32(__a,__b) __builtin_vset_high(__a,__b)
#define vset_high_u64(__a,__b) __builtin_vset_high(__a,__b)
#define vset_high_p8(__a,__b) __builtin_vset_high(__a,__b)
#define vset_high_p16(__a,__b) __builtin_vset_high(__a,__b)
#define vset_high_f16(__a,__b) __builtin_vset_high(__a,__b)
#define vset_high_f32(__a,__b) __builtin_vset_high(__a,__b)

/**********************
Intrinsics declarations
***********************/

#define vget_low_s8(__a) __builtin_vget_low(__a)
#define vget_low_s16(__a) __builtin_vget_low(__a)
#define vget_low_s32(__a) __builtin_vget_low(__a)
#define vget_low_s64(__a) __builtin_vget_low(__a)
#define vget_low_u8(__a) __builtin_vget_low(__a)
#define vget_low_u16(__a) __builtin_vget_low(__a)
#define vget_low_u32(__a) __builtin_vget_low(__a)
#define vget_low_u64(__a) __builtin_vget_low(__a)
#define vget_low_p8(__a) __builtin_vget_low(__a)
#define vget_low_p16(__a) __builtin_vget_low(__a)
#define vget_low_f16(__a) __builtin_vget_low(__a)
#define vget_low_f32(__a) __builtin_vget_low(__a)

#define vget_high_s8(__a) __builtin_vget_high(__a)
#define vget_high_s16(__a) __builtin_vget_high(__a)
#define vget_high_s32(__a) __builtin_vget_high(__a)
#define vget_high_s64(__a) __builtin_vget_high(__a)
#define vget_high_u8(__a) __builtin_vget_high(__a)
#define vget_high_u16(__a) __builtin_vget_high(__a)
#define vget_high_u32(__a) __builtin_vget_high(__a)
#define vget_high_u64(__a) __builtin_vget_high(__a)
#define vget_high_p8(__a) __builtin_vget_high(__a)
#define vget_high_p16(__a) __builtin_vget_high(__a)
#define vget_high_f16(__a) __builtin_vget_high(__a)
#define vget_high_f32(__a) __builtin_vget_high(__a)

#define vcombine_s8(__a, __b) __builtin_vcombine(__a, __b)
#define vcombine_s16(__a, __b) __builtin_vcombine(__a, __b)
#define vcombine_s32(__a, __b) __builtin_vcombine(__a, __b)
#define vcombine_s64(__a, __b) __builtin_vcombine(__a, __b)
#define vcombine_u8(__a, __b) __builtin_vcombine(__a, __b)
#define vcombine_u16(__a, __b) __builtin_vcombine(__a, __b)
#define vcombine_u32(__a, __b) __builtin_vcombine(__a, __b)
#define vcombine_u64(__a, __b) __builtin_vcombine(__a, __b)
#define vcombine_p8(__a, __b) __builtin_vcombine(__a, __b)
#define vcombine_p16(__a, __b) __builtin_vcombine(__a, __b)
#define vcombine_f16(__a, __b) __builtin_vcombine(__a, __b)
#define vcombine_f32(__a, __b) __builtin_vcombine(__a, __b)

#define vtrn_u32(__a, __b) __builtin_vtrn_u32(__a, __b)
#define vtrnq_u32(__a, __b) __builtin_vtrnq_u32(__a, __b)

#define vld1q_u8(__a) __builtin_vld1q_u8 (__a)
#define vst1q_u8(__a, __b) __builtin_vst1q_u8(__a, __b)
#define vmovq_n_u32(__a) __builtin_vmovq_n_u32(__a)
#define vdupq_n_u64(__a) __builtin_vdupq_n_u64(__a)
#define vextq_u32(__a, __b, __c) __builtin_vextq_u32(__a, __b, __c)
#define veorq_u8(__a, __b) __builtin_veorq(__a, __b)
#define vandq_u8(__a, __b) __builtin_vandq(__a, __b)

#define vmull_u32(__a, __b) __builtin_vmull_u32(__a, __b)
#define vmlal_u32(__a, __b, __c) __builtin_vmlal_u32(__a, __b, __c)
#define vsubq_u32(__a, __b) __builtin_vsubq_u32(__a, __b);
#define vaddq_u32(__a, __b) __builtin_vaddq_u32(__a, __b)
#define vaddq_u64(__a, __b) __builtin_vaddq_u64(__a, __b)

#define vshlq_n_u32(__a, __b) __builtin_vshlq_n_u32(__a, __b)
#define vshlq_n_u64(__a, __b) __builtin_vshlq_n_u64(__a, __b)
#define vshrq_n_u64(__a, __b) __builtin_vshrq_n_u64(__a, __b)

/*********************
type reinterpretations
**********************/

#define vreinterpret_p8_s8(__a) __a
#define vreinterpret_p8_s16(__a) __a
#define vreinterpret_p8_s32(__a) __a
#define vreinterpret_p8_s64(__a) __a
#define vreinterpret_p8_f32(__a) __a
#define vreinterpret_p8_u8(__a) __a
#define vreinterpret_p8_u16(__a) __a
#define vreinterpret_p8_u32(__a) __a
#define vreinterpret_p8_u64(__a) __a
#define vreinterpret_p8_p16(__a) __a
#define vreinterpretq_p8_s8(__a) __a
#define vreinterpretq_p8_s16(__a) __a
#define vreinterpretq_p8_s32(__a) __a
#define vreinterpretq_p8_s64(__a) __a
#define vreinterpretq_p8_f32(__a) __a
#define vreinterpretq_p8_u8(__a) __a
#define vreinterpretq_p8_u16(__a) __a
#define vreinterpretq_p8_u32(__a) __a
#define vreinterpretq_p8_u64(__a) __a
#define vreinterpretq_p8_p16(__a) __a
#define vreinterpret_p16_s8(__a) __a
#define vreinterpret_p16_s16(__a) __a
#define vreinterpret_p16_s32(__a) __a
#define vreinterpret_p16_s64(__a) __a
#define vreinterpret_p16_f32(__a) __a
#define vreinterpret_p16_u8(__a) __a
#define vreinterpret_p16_u16(__a) __a
#define vreinterpret_p16_u32(__a) __a
#define vreinterpret_p16_u64(__a) __a
#define vreinterpret_p16_p8(__a) __a
#define vreinterpretq_p16_s8(__a) __a
#define vreinterpretq_p16_s16(__a) __a
#define vreinterpretq_p16_s32(__a) __a
#define vreinterpretq_p16_s64(__a) __a
#define vreinterpretq_p16_f32(__a) __a
#define vreinterpretq_p16_u8(__a) __a
#define vreinterpretq_p16_u16(__a) __a
#define vreinterpretq_p16_u32(__a) __a
#define vreinterpretq_p16_u64(__a) __a
#define vreinterpretq_p16_p8(__a) __a
#define vreinterpret_f32_s8(__a) __a
#define vreinterpret_f32_s16(__a) __a
#define vreinterpret_f32_s32(__a) __a
#define vreinterpret_f32_s64(__a) __a
#define vreinterpret_f32_u8(__a) __a
#define vreinterpret_f32_u16(__a) __a
#define vreinterpret_f32_u32(__a) __a
#define vreinterpret_f32_u64(__a) __a
#define vreinterpret_f32_p8(__a) __a
#define vreinterpret_f32_p16(__a) __a
#define vreinterpretq_f32_s8(__a) __a
#define vreinterpretq_f32_s16(__a) __a
#define vreinterpretq_f32_s32(__a) __a
#define vreinterpretq_f32_s64(__a) __a
#define vreinterpretq_f32_u8(__a) __a
#define vreinterpretq_f32_u16(__a) __a
#define vreinterpretq_f32_u32(__a) __a
#define vreinterpretq_f32_u64(__a) __a
#define vreinterpretq_f32_p8(__a) __a
#define vreinterpretq_f32_p16(__a) __a
#define vreinterpret_s64_s8(__a) __a
#define vreinterpret_s64_s16(__a) __a
#define vreinterpret_s64_s32(__a) __a
#define vreinterpret_s64_f32(__a) __a
#define vreinterpret_s64_u8(__a) __a
#define vreinterpret_s64_u16(__a) __a
#define vreinterpret_s64_u32(__a) __a
#define vreinterpret_s64_u64(__a) __a
#define vreinterpret_s64_p8(__a) __a
#define vreinterpret_s64_p16(__a) __a
#define vreinterpretq_s64_s8(__a) __a
#define vreinterpretq_s64_s16(__a) __a
#define vreinterpretq_s64_s32(__a) __a
#define vreinterpretq_s64_f32(__a) __a
#define vreinterpretq_s64_u8(__a) __a
#define vreinterpretq_s64_u16(__a) __a
#define vreinterpretq_s64_u32(__a) __a
#define vreinterpretq_s64_u64(__a) __a
#define vreinterpretq_s64_p8(__a) __a
#define vreinterpretq_s64_p16(__a) __a
#define vreinterpret_u64_s8(__a) __a
#define vreinterpret_u64_s16(__a) __a
#define vreinterpret_u64_s32(__a) __a
#define vreinterpret_u64_s64(__a) __a
#define vreinterpret_u64_f32(__a) __a
#define vreinterpret_u64_u8(__a) __a
#define vreinterpret_u64_u16(__a) __a
#define vreinterpret_u64_u32(__a) __a
#define vreinterpret_u64_p8(__a) __a
#define vreinterpret_u64_p16(__a) __a
#define vreinterpretq_u64_s8(__a) __a
#define vreinterpretq_u64_s16(__a) __a
#define vreinterpretq_u64_s32(__a) __a
#define vreinterpretq_u64_s64(__a) __a
#define vreinterpretq_u64_f32(__a) __a
#define vreinterpretq_u64_u8(__a) __a
#define vreinterpretq_u64_u16(__a) __a
#define vreinterpretq_u64_u32(__a) __a
#define vreinterpretq_u64_p8(__a) __a
#define vreinterpretq_u64_p16(__a) __a
#define vreinterpret_s8_s16(__a) __a
#define vreinterpret_s8_s32(__a) __a
#define vreinterpret_s8_s64(__a) __a
#define vreinterpret_s8_f32(__a) __a
#define vreinterpret_s8_u8(__a) __a
#define vreinterpret_s8_u16(__a) __a
#define vreinterpret_s8_u32(__a) __a
#define vreinterpret_s8_u64(__a) __a
#define vreinterpret_s8_p8(__a) __a
#define vreinterpret_s8_p16(__a) __a
#define vreinterpretq_s8_s16(__a) __a
#define vreinterpretq_s8_s32(__a) __a
#define vreinterpretq_s8_s64(__a) __a
#define vreinterpretq_s8_f32(__a) __a
#define vreinterpretq_s8_u8(__a) __a
#define vreinterpretq_s8_u16(__a) __a
#define vreinterpretq_s8_u32(__a) __a
#define vreinterpretq_s8_u64(__a) __a
#define vreinterpretq_s8_p8(__a) __a
#define vreinterpretq_s8_p16(__a) __a
#define vreinterpret_s16_s8(__a) __a
#define vreinterpret_s16_s32(__a) __a
#define vreinterpret_s16_s64(__a) __a
#define vreinterpret_s16_f32(__a) __a
#define vreinterpret_s16_u8(__a) __a
#define vreinterpret_s16_u16(__a) __a
#define vreinterpret_s16_u32(__a) __a
#define vreinterpret_s16_u64(__a) __a
#define vreinterpret_s16_p8(__a) __a
#define vreinterpret_s16_p16(__a) __a
#define vreinterpretq_s16_s8(__a) __a
#define vreinterpretq_s16_s32(__a) __a
#define vreinterpretq_s16_s64(__a) __a
#define vreinterpretq_s16_f32(__a) __a
#define vreinterpretq_s16_u8(__a) __a
#define vreinterpretq_s16_u16(__a) __a
#define vreinterpretq_s16_u32(__a) __a
#define vreinterpretq_s16_u64(__a) __a
#define vreinterpretq_s16_p8(__a) __a
#define vreinterpretq_s16_p16(__a) __a
#define vreinterpret_s32_s8(__a) __a
#define vreinterpret_s32_s16(__a) __a
#define vreinterpret_s32_s64(__a) __a
#define vreinterpret_s32_f32(__a) __a
#define vreinterpret_s32_u8(__a) __a
#define vreinterpret_s32_u16(__a) __a
#define vreinterpret_s32_u32(__a) __a
#define vreinterpret_s32_u64(__a) __a
#define vreinterpret_s32_p8(__a) __a
#define vreinterpret_s32_p16(__a) __a
#define vreinterpretq_s32_s8(__a) __a
#define vreinterpretq_s32_s16(__a) __a
#define vreinterpretq_s32_s64(__a) __a
#define vreinterpretq_s32_f32(__a) __a
#define vreinterpretq_s32_u8(__a) __a
#define vreinterpretq_s32_u16(__a) __a
#define vreinterpretq_s32_u32(__a) __a
#define vreinterpretq_s32_u64(__a) __a
#define vreinterpretq_s32_p8(__a) __a
#define vreinterpretq_s32_p16(__a) __a
#define vreinterpret_u8_s8(__a) __a
#define vreinterpret_u8_s16(__a) __a
#define vreinterpret_u8_s32(__a) __a
#define vreinterpret_u8_s64(__a) __a
#define vreinterpret_u8_f32(__a) __a
#define vreinterpret_u8_u16(__a) __a
#define vreinterpret_u8_u32(__a) __a
#define vreinterpret_u8_u64(__a) __a
#define vreinterpret_u8_p8(__a) __a
#define vreinterpret_u8_p16(__a) __a
#define vreinterpretq_u8_s8(__a) __a
#define vreinterpretq_u8_s16(__a) __a
#define vreinterpretq_u8_s32(__a) __a
#define vreinterpretq_u8_s64(__a) __a
#define vreinterpretq_u8_f32(__a) __a
#define vreinterpretq_u8_u16(__a) __a
#define vreinterpretq_u8_u32(__a) __a
#define vreinterpretq_u8_u64(__a) __a
#define vreinterpretq_u8_p8(__a) __a
#define vreinterpretq_u8_p16(__a) __a
#define vreinterpret_u16_s8(__a) __a
#define vreinterpret_u16_s16(__a) __a
#define vreinterpret_u16_s32(__a) __a
#define vreinterpret_u16_s64(__a) __a
#define vreinterpret_u16_f32(__a) __a
#define vreinterpret_u16_u8(__a) __a
#define vreinterpret_u16_u32(__a) __a
#define vreinterpret_u16_u64(__a) __a
#define vreinterpret_u16_p8(__a) __a
#define vreinterpret_u16_p16(__a) __a
#define vreinterpretq_u16_s8(__a) __a
#define vreinterpretq_u16_s16(__a) __a
#define vreinterpretq_u16_s32(__a) __a
#define vreinterpretq_u16_s64(__a) __a
#define vreinterpretq_u16_f32(__a) __a
#define vreinterpretq_u16_u8(__a) __a
#define vreinterpretq_u16_u32(__a) __a
#define vreinterpretq_u16_u64(__a) __a
#define vreinterpretq_u16_p8(__a) __a
#define vreinterpretq_u16_p16(__a) __a
#define vreinterpret_u32_s8(__a) __a
#define vreinterpret_u32_s16(__a) __a
#define vreinterpret_u32_s32(__a) __a
#define vreinterpret_u32_s64(__a) __a
#define vreinterpret_u32_f32(__a) __a
#define vreinterpret_u32_u8(__a) __a
#define vreinterpret_u32_u16(__a) __a
#define vreinterpret_u32_u64(__a) __a
#define vreinterpret_u32_p8(__a) __a
#define vreinterpret_u32_p16(__a) __a
#define vreinterpretq_u32_s8(__a) __a
#define vreinterpretq_u32_s16(__a) __a
#define vreinterpretq_u32_s32(__a) __a
#define vreinterpretq_u32_s64(__a) __a
#define vreinterpretq_u32_f32(__a) __a
#define vreinterpretq_u32_u8(__a) __a
#define vreinterpretq_u32_u16(__a) __a
#define vreinterpretq_u32_u64(__a) __a
#define vreinterpretq_u32_p8(__a) __a
#define vreinterpretq_u32_p16(__a) __a

#endif // ARM_NEON
#endif // _COMPCERT_ARM_NEON_H
