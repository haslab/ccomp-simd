#ifndef _KUMMER_NEON_H
#define _KUMMER_NEON_H

#ifdef __COMPCERT__
#include "ccomp-arm-neon.h"
#else // __GNUC__
#include <arm_neon.h>
#endif // __COMPCERT__

// add primitives not intrinsiced in GCC
#ifdef __COMPCERT__
#define vswp(__a,__b,__c) __a = vswp_u32(__b,__c);
#else // __GNUC__
#define vset_low_u8(__a,__b) vcombine_u8(__b,vget_high_u8(__a))
#define vset_high_u8(__a,__b) vcombine_u8(vget_low_u8(__a),__b)
#define vswp(__a,__b,__c) {__a.val[0]=__c; __a.val[1]=__b;}
#endif // __COMPCERT__

#define load128(a,b)  a = vld1q_u8((uint8_t*)b)
#define set4x(a,b)    a = vreinterpretq_u8_u32(vmovq_n_u32 (b))
#define xor128(a,b,c) a = veorq_u8(b,c)
#define and128(a,b,c) a = vandq_u8(b,c)
#define store128(a,b) vst1q_u8 ((uint8_t*)a,b)

#ifdef __COMPCERT__
#define set2x(a,b) a = __builtin_vmovq_imm_u64(b)
#else
#define set2x(a,b) a = vreinterpretq_u8_u64(vdupq_n_u64(b))
//#define set2x(a,b) a = vreinterpretq_u8_u64(vcombine_u64(b,b)) //does not work in ccomp
#endif //__COMPCERT__

#define shiftl4x_in(a,b) a = vreinterpretq_u8_u32(vshlq_n_u32(vreinterpretq_u32_u8(a),b))
#define shiftur2x_in(a,b) a = vreinterpretq_u8_u64(vshrq_n_u64(vreinterpretq_u64_u8(a),b))
#define shiftur2x(a,b,c) a = vreinterpretq_u8_u64(vshrq_n_u64(vreinterpretq_u64_u8(b),c))
#define shiftl2x(a,b,c) a = vreinterpretq_u8_u64(vshlq_n_u64(vreinterpretq_u64_u8(b),c))

#define add2x(a,b,c) a = vreinterpretq_u8_u64(vaddq_u64(vreinterpretq_u64_u8(b),vreinterpretq_u64_u8(c)))
#define add4x(a,b,c) a = vreinterpretq_u8_u32(vaddq_u32(vreinterpretq_u32_u8(b),vreinterpretq_u32_u8(c)))
#define sub4x(a,b,c) a = vreinterpretq_u8_u32(vsubq_u32(vreinterpretq_u32_u8(b),vreinterpretq_u32_u8(c)))
#define mul2x32_0101(a,b,c) a = vreinterpretq_u8_u64( \
                  vmull_u32(vget_low_u32(vreinterpretq_u32_u8(b)), \
                            vget_low_u32(vreinterpretq_u32_u8(c))))
#define mul2x32_0123(a,b,c) a = vreinterpretq_u8_u64( \
                  vmull_u32(vget_low_u32(vreinterpretq_u32_u8(b)), \
                            vget_high_u32(vreinterpretq_u32_u8(c))))
#define mul2x32_2301(a,b,c) a = vreinterpretq_u8_u64( \
                  vmull_u32(vget_high_u32(vreinterpretq_u32_u8(b)), \
                            vget_low_u32(vreinterpretq_u32_u8(c))))
#define mul2x32_2323(a,b,c) a = vreinterpretq_u8_u64( \
                  vmull_u32(vget_high_u32(vreinterpretq_u32_u8(b)), \
                            vget_high_u32(vreinterpretq_u32_u8(c))))
#define mul2x32_0123_ac(a,b,c) a = vreinterpretq_u8_u64( \
                          vmlal_u32(vreinterpretq_u64_u8(a), \
                                 vget_low_u32(vreinterpretq_u32_u8(b)), \
                                 vget_high_u32(vreinterpretq_u32_u8(c))))
#define mul2x32_2301_ac(a,b,c) a = vreinterpretq_u8_u64( \
                          vmlal_u32(vreinterpretq_u64_u8(a), \
                                 vget_high_u32(vreinterpretq_u32_u8(b)), \
                                 vget_low_u32(vreinterpretq_u32_u8(c))))
#define mul2x32_0101_ac(a,b,c) a = vreinterpretq_u8_u64( \
                          vmlal_u32(vreinterpretq_u64_u8(a), \
                                 vget_low_u32(vreinterpretq_u32_u8(b)), \
                                 vget_low_u32(vreinterpretq_u32_u8(c))))
#define mul2x32_2323_ac(a,b,c) a = vreinterpretq_u8_u64( \
                          vmlal_u32(vreinterpretq_u64_u8(a), \
                                 vget_high_u32(vreinterpretq_u32_u8(b)), \
                                 vget_high_u32(vreinterpretq_u32_u8(c))))

#ifdef __GNUC__

#define permute32_3012(a,b){\
	  a = vreinterpretq_u8_u32(vextq_u32(vreinterpretq_u32_u8(b),vreinterpretq_u32_u8(b),3)); \
} // //p4 = q0[3]q0[0,1,2] //vext.32 q2,q1,q1,#3

#define mix32_11121320(a,b,c){\
	  a = vreinterpretq_u8_u32(vextq_u32(vreinterpretq_u32_u8(b),vreinterpretq_u32_u8(c),1)); \
} //p5 = n2[1,2,3]h4[0] //vext.32 q3,q3,q6,#1

#define mix32_00100212_01110313(a,b) __asm__ volatile("vtrn.32 %q0,%q1"       :"+w"(a),"+w"(b))       //a b = a[0]b[0]a[2]b[2] a[1]b[1]a[3]b[3]
#define mix32_00010212_10110323(a,b) __asm__ volatile("vtrn.32 %f0,%f1"       :"+w"(a),"+w"(b))       //a b = a[0]a[1]a[2]b[2] b[0]b[1]a[3]b[3]
	//#define mix32_11121320(a,b,c)        __asm__ volatile("vext.32 %q0,%q1,%q2,#1":"+w"(a):"w"(b),"w"(c)) //a   = b[1,2,3]c[0]

#define permute32_0213(a)    __asm__ volatile("vtrn.32 %e0,%f0":"+w"(a))                      //a = a[0,2,1,3]
	// #define permute32_3012(a,b)  __asm__ volatile("vext.32 %q0,%q1,%q1,#3":"+w"(a):"w"(b))     //a = b[3]c[0,1,2]

#define swap64_00100111(a,b) __asm__ volatile("vswp %f0,%e1":"+w"(a),"+w"(b)) //a b = a[0]b[0] a[1]b[1]
#define swap64_00111001(a,b) __asm__ volatile("vswp %f0,%f1":"+w"(a),"+w"(b)) //a b = a[0]b[1] b[0]a[1]
#define swap64_10010011(a,b) __asm__ volatile("vswp %e0,%e1":"+w"(a),"+w"(b)) //a b = b[0]a[1] a[0]b[1]

#else

#define mix32_00100212_01110313(a,b) {\
  uint32x4x2_t _ab; _ab = vtrnq_u32(vreinterpretq_u32_u8(a),vreinterpretq_u32_u8(b));\
  a = vreinterpretq_u8_u32(_ab.val[0]);\
  b = vreinterpretq_u8_u32(_ab.val[1]);\
}
//__asm__ volatile("vtrn.32 %q0,%q1"       :"+w"(a),"+w"(b))       //a b = a[0]b[0]a[2]b[2] a[1]b[1]a[3]b[3]


// uint32x2x2_t  vtrn_u32(uint32x2_t a, uint32x2_t b);
#define mix32_00010212_10110323(a,b)  {\
  uint32x2x2_t _ab; _ab = vtrn_u32(vget_high_u32(vreinterpretq_u32_u8(a)),vget_high_u32(vreinterpretq_u32_u8(b)));\
  a = vset_high_u8(a, vreinterpret_u8_u32(_ab.val[0]));\
  b = vset_high_u8(b, vreinterpret_u8_u32(_ab.val[1]));\
}
//__asm__ volatile("vtrn.32 %f0,%f1"       :"+w"(a),"+w"(b))       //a b = a[0]a[1]a[2]b[2] b[0]b[1]a[3]b[3]

#define mix32_11121320(a,b,c){\
  a = vreinterpretq_u8_u32(vextq_u32(vreinterpretq_u32_u8(b),vreinterpretq_u32_u8(c),1)); \
} //p5 = n2[1,2,3]h4[0] //vext.32 q3,q3,q6,#1

// uint32x2x2_t vtrn_u32 (uint32x2_t, uint32x2_t) 
#define permute32_0213(a)  {\
  uint32x2x2_t _aa; _aa = vtrn_u32(vget_low_u32(vreinterpretq_u32_u8(a)),vget_high_u32(vreinterpretq_u32_u8(a)));\
  a = vcombine_u8(vreinterpret_u8_u32(_aa.val[0]), vreinterpret_u8_u32(_aa.val[1]));\
}
//__asm__ volatile("vtrn.32 %e0,%f0":"+w"(a))                      //a = a[0,2,1,3]

#define permute32_3012(a,b){\
  a = vreinterpretq_u8_u32(vextq_u32(vreinterpretq_u32_u8(b),vreinterpretq_u32_u8(b),3)); \
} // //p4 = q0[3]q0[0,1,2] //vext.32 q2,q1,q1,#3

// Apparently vswp is not instrinsicced in gcc
#define swap64_00100111(a,b) {\
  uint32x2x2_t _ab; vswp(_ab,vget_low_u32(vreinterpretq_u32_u8(b)),vget_high_u32(vreinterpretq_u32_u8(a))); \
  a = vset_high_u8(a, vreinterpret_u8_u32(_ab.val[1]));\
  b = vset_low_u8(b, vreinterpret_u8_u32(_ab.val[0]));\
}
//__asm__ volatile("vswp %f0,%e1":"+w"(a),"+w"(b)) //a b = a[0]b[0] a[1]b[1]


// Apparently vswp is not instrinsicced in gcc
#define swap64_00111001(a,b) {\
  uint32x2x2_t _ab; vswp(_ab,vget_high_u32(vreinterpretq_u32_u8(b)),vget_high_u32(vreinterpretq_u32_u8(a))); \
  a = vset_high_u8(a, vreinterpret_u8_u32(_ab.val[1]));\
  b = vset_high_u8(b, vreinterpret_u8_u32(_ab.val[0]));\
}
//__asm__ volatile("vswp %f0,%f1":"+w"(a),"+w"(b)) //a b = a[0]b[1] b[0]a[1]


// Apparently vswp is not instrinsicced in gcc
#define swap64_10010011(a,b) {\
  uint32x2x2_t _ab; vswp(_ab,vget_low_u32(vreinterpretq_u32_u8(b)),vget_low_u32(vreinterpretq_u32_u8(a))); \
  a = vset_low_u8(a, vreinterpret_u8_u32(_ab.val[1]));\
  b = vset_low_u8(b, vreinterpret_u8_u32(_ab.val[0]));\
}
//__asm__ volatile("vswp %e0,%e1":"+w"(a),"+w"(b)) //a b = b[0]a[1] a[0]b[1]

#endif // __INSLINE_ASM__


#define set_lane_64_0010(a,b) a=vcombine_u8(vget_low_u8(a),vget_low_u8(b))
//      a = vreinterpretq_u8_u64(vsetq_lane_u64(vgetq_lane_u64(vreinterpretq_u64_u8(b),0), vreinterpretq_u64_u8(a),1)); \
//} 

#define set_lane_64_1001(a,b) a=vcombine_u8(vget_low_u8(b),vget_high_u8(a))
//      a = vreinterpretq_u8_u64(vsetq_lane_u64(vgetq_lane_u64(vreinterpretq_u64_u8(b),0), vreinterpretq_u64_u8(a),0)); \
//}

#define set_lane_64_0011(a,b) a=vcombine_u8(vget_low_u8(a),vget_high_u8(b))
//      a = vreinterpretq_u8_u64(vsetq_lane_u64(vgetq_lane_u64(vreinterpretq_u64_u8(b),1), vreinterpretq_u64_u8(a),1)); \
//} ////h0 = h0[0]n0[1] //vmov d15,d5

typedef uint32_t int32;
typedef uint8x16_t int128;
typedef uint8_t* mem128;
typedef unsigned char* address;


#endif // _KUMMER_NEON_H
