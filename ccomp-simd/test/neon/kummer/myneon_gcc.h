#include "arm_neon.h"

// ref: http://hardwarebug.org/2010/07/06/arm-inline-asm-secrets/
//#define __INLINE_ASM__

// uint8x16_t vld1q_u8 (const uint8_t *) 
#define load128(a,b)  a = vld1q_u8 (b)

// uint32x4_t vmovq_n_u32 (uint32_t) 
#define set4x(a,b)    a = vreinterpretq_u8_u32(vmovq_n_u32 (b))

// uint8x16_t veorq_u8 (uint8x16_t, uint8x16_t) 
#define xor128(a,b,c) a = veorq_u8(b,c)

// uint8x16_t vandq_u8 (uint8x16_t, uint8x16_t) 
#define and128(a,b,c) a = vandq_u8(b,c)

//void vst1q_u8 (uint8_t *, uint8x16_t) 
#define store128(a,b) vst1q_u8 (a,b)

//uint64x2_t  vdupq_n_u64(uint64_t value); 
#define set2x(a,b) a = vreinterpretq_u8_u64(vdupq_n_u64(b))

// uint32x4_t vshlq_n_u32(uint32x4_t a, __constrange(0,31) int b); 
#define shiftl4x_in(a,b) a = vreinterpretq_u8_u32(vshlq_n_u32(vreinterpretq_u32_u8(a),b))

//uint64x2_t vshrq_n_u64(uint64x2_t a, __constrange(1,64) int b); 
#define shiftur2x_in(a,b) a = vreinterpretq_u8_u64(vshrq_n_u64(vreinterpretq_u64_u8(a),b))

// uint64x2_t vshrq_n_u64(uint64x2_t a, __constrange(1,64) int b); 
#define shiftur2x(a,b,c) a = vreinterpretq_u8_u64(vshrq_n_u64(vreinterpretq_u64_u8(b),c))

// uint64x2_t vshlq_n_u64(uint64x2_t a, __constrange(1,64) int b); 
#define shiftl2x(a,b,c) a = vreinterpretq_u8_u64(vshlq_n_u64(vreinterpretq_u64_u8(b),c))

//uint64x2_t  vaddq_u64(uint64x2_t a, uint64x2_t b);  
#define add2x(a,b,c) a = vreinterpretq_u8_u64(vaddq_u64(vreinterpretq_u64_u8(b),vreinterpretq_u64_u8(c)))

//uint32x4_t  vaddq_u32(uint32x4_t a, uint32x4_t b);  
#define add4x(a,b,c) a = vreinterpretq_u8_u32(vaddq_u32(vreinterpretq_u32_u8(b),vreinterpretq_u32_u8(c)))

//uint32x4_t  vsubq_u32(uint32x4_t a, uint32x4_t b);  
#define sub4x(a,b,c) a = vreinterpretq_u8_u32(vsubq_u32(vreinterpretq_u32_u8(b),vreinterpretq_u32_u8(c)))

//uint64x2_t vmull_u32 (uint32x2_t, uint32x2_t) 
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

//uint64x2_t vmlal_u32(uint64x2_t a, uint32x2_t b, uint32x2_t c);
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

#define permute32_3012(a,b){\
	  a = vreinterpretq_u8_u32(vextq_u32(vreinterpretq_u32_u8(b),vreinterpretq_u32_u8(b),3)); \
} // //p4 = q0[3]q0[0,1,2] //vext.32 q2,q1,q1,#3

#define mix32_11121320(a,b,c){\
	  a = vreinterpretq_u8_u32(vextq_u32(vreinterpretq_u32_u8(b),vreinterpretq_u32_u8(c),1)); \
} //p5 = n2[1,2,3]h4[0] //vext.32 q3,q3,q6,#1


// SWAPS
#ifdef __INLINE_ASM__

	#define mix32_00100212_01110313(a,b) __asm__ volatile("vtrn.32 %q0,%q1"       :"+w"(a),"+w"(b))       //a b = a[0]b[0]a[2]b[2] a[1]b[1]a[3]b[3]
	#define mix32_00010212_10110323(a,b) __asm__ volatile("vtrn.32 %f0,%f1"       :"+w"(a),"+w"(b))       //a b = a[0]a[1]a[2]b[2] b[0]b[1]a[3]b[3]
	//#define mix32_11121320(a,b,c)        __asm__ volatile("vext.32 %q0,%q1,%q2,#1":"+w"(a):"w"(b),"w"(c)) //a   = b[1,2,3]c[0]

	#define permute32_0213(a)    __asm__ volatile("vtrn.32 %e0,%f0":"+w"(a))                      //a = a[0,2,1,3]
	// #define permute32_3012(a,b)  __asm__ volatile("vext.32 %q0,%q1,%q1,#3":"+w"(a):"w"(b))     //a = b[3]c[0,1,2]

	#define swap64_00100111(a,b) __asm__ volatile("vswp %f0,%e1":"+w"(a),"+w"(b)) //a b = a[0]b[0] a[1]b[1]
	#define swap64_00111001(a,b) __asm__ volatile("vswp %f0,%f1":"+w"(a),"+w"(b)) //a b = a[0]b[1] b[0]a[1]
	#define swap64_10010011(a,b) __asm__ volatile("vswp %e0,%e1":"+w"(a),"+w"(b)) //a b = b[0]a[1] a[0]b[1]

#else

	// uint32x4x2_t vtrnq_u32 (uint32x4_t, uint32x4_t) 
	#define mix32_00100212_01110313(a,b) { \
		 uint32x4x2_t x = vtrnq_u32(vreinterpretq_u32_u8(a),vreinterpretq_u32_u8(b)); \
		 a = vreinterpretq_u8_u32(x.val[0]); \
		 b = vreinterpretq_u8_u32(x.val[1]); \
	} //h0 h1 = h0[0]h1[0]h0[2]h1[2] h0[1]h1[1]h0[3]h1[3]

	// uint32x2x2_t  vtrn_u32(uint32x2_t a, uint32x2_t b);
	#define mix32_00010212_10110323(a,b) { \
		 uint32x2x2_t x = vtrn_u32( \
		              vget_high_u32(vreinterpretq_u32_u8(a)), \
		              vget_high_u32(vreinterpretq_u32_u8(b))); \
		 a = vreinterpretq_u8_u64(vsetq_lane_u64(vreinterpret_u64_u32(x.val[0]), vreinterpretq_u64_u8(a),1)); \
		 b = vreinterpretq_u8_u64(vsetq_lane_u64(vreinterpret_u64_u32(x.val[1]), vreinterpretq_u64_u8(b),1)); \
	} //b1 b4 = b1[0]b1[1]b1[2]b4[2] b4[0]b4[1]b1[3]b4[3]

	// uint32x2x2_t vtrn_u32 (uint32x2_t, uint32x2_t) 
	#define permute32_0213(a) { \
		 uint32x2x2_t x = vtrn_u32( \
		              vget_low_u32(vreinterpretq_u32_u8(a)), \
		              vget_high_u32(vreinterpretq_u32_u8(a))); \
		 a = vreinterpretq_u8_u32(vcombine_u32(x.val[0],x.val[1])); \
	}


	// Apparently vswp is not instrinsicced in gcc
	#define swap64_00100111(a,b) { \
			 uint64x1_t __a0 = vget_low_u64(vreinterpretq_u64_u8(a)); \
			 uint64x1_t __a1 = vget_high_u64(vreinterpretq_u64_u8(a)); \
			 uint64x1_t __b0 = vget_low_u64(vreinterpretq_u64_u8(b)); \
			 uint64x1_t __b1 = vget_high_u64(vreinterpretq_u64_u8(b)); \
			 a = vreinterpretq_u8_u64(vcombine_u64 (__a0,__b0)); \
			 b = vreinterpretq_u8_u64(vcombine_u64 (__a1,__b1)); \
		} //sum1 b2 = sum1[0]b2[0] sum1[1]b2[1]

	// Apparently vswp is not instrinsicced in gcc
	#define swap64_00111001(a,b) { \
		 uint64x1_t __a0 = vget_low_u64(vreinterpretq_u64_u8(a)); \
		 uint64x1_t __a1 = vget_high_u64(vreinterpretq_u64_u8(a)); \
		 uint64x1_t __b0 = vget_low_u64(vreinterpretq_u64_u8(b)); \
		 uint64x1_t __b1 = vget_high_u64(vreinterpretq_u64_u8(b)); \
		 a = vreinterpretq_u8_u64(vcombine_u64 (__a0,__b1)); \
		 b = vreinterpretq_u8_u64(vcombine_u64 (__b0,__a1)); \
	} //dif1 b2 = dif1[0]b2[1] b2[0]dif1[1]


	// Apparently vswp is not instrinsicced in gcc
	#define swap64_10010011(a,b) { \
		 uint64x1_t __a0 = vget_low_u64(vreinterpretq_u64_u8(a)); \
		 uint64x1_t __a1 = vget_high_u64(vreinterpretq_u64_u8(a)); \
		 uint64x1_t __b0 = vget_low_u64(vreinterpretq_u64_u8(b)); \
		 uint64x1_t __b1 = vget_high_u64(vreinterpretq_u64_u8(b)); \
		 a = vreinterpretq_u8_u64(vcombine_u64 (__b0,__a1)); \
		 b = vreinterpretq_u8_u64(vcombine_u64 (__a0,__b1)); \
	} // a1 a2 = a2[0]a1[1] a1[0]a2[1]
#endif


#define set_lane_64_0010(a,b) { \
      a = vreinterpretq_u8_u64(vsetq_lane_u64(vgetq_lane_u64(vreinterpretq_u64_u8(b),0), vreinterpretq_u64_u8(a),1)); \
} 

#define set_lane_64_1001(a,b) { \
      a = vreinterpretq_u8_u64(vsetq_lane_u64(vgetq_lane_u64(vreinterpretq_u64_u8(b),0), vreinterpretq_u64_u8(a),0)); \
}

#define set_lane_64_0011(a,b) { \
      a = vreinterpretq_u8_u64(vsetq_lane_u64(vgetq_lane_u64(vreinterpretq_u64_u8(b),1), vreinterpretq_u64_u8(a),1)); \
} ////h0 = h0[0]n0[1] //vmov d15,d5

typedef uint32_t int32;
typedef uint8x16_t int128;
typedef uint8_t* mem128;
typedef unsigned char* address;
