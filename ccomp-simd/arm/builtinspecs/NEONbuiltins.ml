open C
open Ctypes
open Cutil

open NEONtypes

(*
open Absolute_difference
open Addition
open Combining_vectors
open Comparison
open Converting_vectors
open Extended_table_look_up
open Extracting_lanes_from_a_vector_into_a_register
open Folding_maximum
open Folding_minimum
open Initializing_a_vector_from_a_literal_bit_pattern
open Loading_an_N_element_structure
open Loading_a_single_lane_of_a_vector_from_a_literal
open Loading_a_single_vector_or_lane
open Logical_operations
open Maximum_and_minimum
open Multiplication
open Operations_with_a_scalar_value
open Other_single_operand_arithmetic
open Pairwise_addition
open Reciprocal_and_sqrt
open Reversing_vector_elements__swap_endianness
open Setting_all_lanes_to_the_same_value
open Shifts_by_a_constant
open Shifts_by_signed_variable
open Shifts_with_insert
open Splitting_vectors
open Storing_a_single_vector_or_lane
open Subtraction
open Table_look_up
open Transposition_operations
open Vector_cast_operations
open Vector_extraction
*)

(** * Moves *)
(** builtins that are handled specially by the register allocator...
   assembly string is ignored)
*)
let move_builtins =
  [
   ( "__builtin_vget_low"
   , (builtin64_t, [builtin128_t])
   , cNEON
   , 0
   , false
   , None
   , ["VMOV %0, %1"]
   )
  ;
   ( "__builtin_vget_high"
   , (builtin64_t, [builtin128_t])
   , cNEON
   , 0
   , false
   , None
   , ["VMOV %0, %2"]
   )
  ;
   ( "__builtin_vcombine"
   , (builtin128_t, [builtin64_t; builtin64_t])
   , cNEON
   , 0
   , false
   , None
   , ["VMOV %0, %2"; "VMOV %1, %3"]
   )
  ]

(** * Specific *)
(** builtins added to compcert that are not standard... *)
let extra_builtins_gen () =
  let builtin64x2_t = TStruct(Builtins.get_ident "__builtin_t64x2",[])
  and builtin128x2_t = TStruct(Builtins.get_ident "__builtin_t128x2",[]) in
  [
   ( "__builtin_vset_low"
   , (builtin128_t, [builtin128_t; builtin64_t])
   , cNEON
   , 0
   , true
   , None
   , ["VMOV %0, %2"]
   )
  ;
   ( "__builtin_vset_high"
   , (builtin128_t, [builtin128_t; builtin64_t])
   , cNEON
   , 0
   , true
   , None
   , ["VMOV %1, %2"]
   )
  ;
   ( "__builtin_vmovq_imm_u64"
   , (uint64x2_t, [t_const (t_long)])
   , cNEON
   , 1
   , false
   , None
   , ["VMOV.I64 %Q0, #%2"]
   )
  ;
   ( "__builtin_vswp"
   , (builtin64x2_t, [builtin64_t; builtin64_t])
   , cNEON
   , 0
   , true
   , None
   , ["VSWP %0, %1"]
   )
  ;
   (* uint32x4x2_t  vswap_u32(uint32x2_t a, uint32x2_t b) *)
   ( "__builtin_vswpq"
   , (builtin128x2_t, [builtin128_t; builtin128_t])
   , cNEON
   , 0
   , true
   , None
   , ["VSWP %Q0, %Q2"]
   )
  ]


(** * Kummer *)
(** builtins needed to compile Kummer... *)
let kummer_builtins_gen () =
  let uint32x2x2_t = TStruct(Builtins.get_ident "__builtin_t64x2",[]) in
  let uint32x4x2_t = TStruct(Builtins.get_ident "__builtin_t128x2",[]) in
  [
   (* uint32x2x2_t  vtrn_u32(uint32x2_t a, uint32x2_t b) *)
   ( "__builtin_vtrn_u32"
   , (uint32x2x2_t, [uint32x2_t; uint32x2_t])
   , cNEON
   , 0
   , true
   , None
   , ["VTRN.32 %0, %1"]
   )
  ;
   (* uint32x4x2_t  vtrnq_u32(uint32x4_t a, uint32x4_t b) *)
   ( "__builtin_vtrnq_u32"
   , (uint32x4x2_t, [uint32x4_t; uint32x4_t])
   , cNEON
   , 0
   , true
   , None
   , ["VTRN.32 %Q0, %Q2"]
   )
  ;
   (* void vst1q_u8 (uint8_t *, uint8x16_t) *)
   ( "__builtin_vst1q_u8"
   , (t_void, [t_ptr uint8_t; uint8x16_t])
   , cNEON
   , 0
   , false
   , None
   , ["VST1.8 {%1,%2}, [%0]"]
   )
  ;
   (* uint8x16_t vld1q_u8 (const uint8_t* ) *)
   ( "__builtin_vld1q_u8"
   , (uint8x16_t, [t_ptr uint8_t])
   , cNEON
   , 0
   , false
   , None
   , ["VLD1.8 {%0,%1}, [%2]"]
   )
  ;
   (* uint8x16_t vmovq_n_u8 (uint8_t)  *)
   ( "__builtin_vmovq_n_u8"
   , (uint8x16_t, [uint8_t])
   , cNEON
   , 0
   , false
   , None
   , ["VDUP.8 %Q0, %2"]
   )
  ;
   (* uint16x8_t vmovq_n_u16 (uint16_t)  *)
   ( "__builtin_vmovq_n_u16"
   , (uint16x8_t, [uint16_t])
   , cNEON
   , 0
   , false
   , None
   , ["VDUP.16 %Q0, %2"]
   )
  ;
   (* uint32x4_t vmovq_n_u32 (uint32_t)  *)
   ( "__builtin_vmovq_n_u32"
   , (uint32x4_t, [uint32_t])
   , cNEON
   , 0
   , false
   , None
   , ["VDUP.32 %Q0, %2"]
   )
  ;
   (* uint64x2_t vdupq_n_u64 (uint64_t)  *)
   ( "__builtin_vdupq_n_u64"
   , (uint64x2_t, [uint64_t])
   , cNEON
   , 0	
   , false
   , None
   , ["VMOV %0, %3, %2"; "VMOV %1, %3, %2"]		
   )
  ;
   (* uint32x4_t vextq_u32(uint32x4_t a, uint32x4_t b, __constrange(0,3) int c  *)
   ( "__builtin_vextq_u32"
   , (uint32x4_t, [uint32x4_t; uint32x4_t; t_const (t_int)])
   , cNEON
   , 1
   , false
   , None
   , ["VEXT.32 %Q0, %Q2, %Q4, #%6"]
   )
  ;
   (* uint8x16_t vaddq_u8 (uint8x16_t, uint8x16_t)  *)
   ( "__builtin_vaddq_u8"
   , (uint8x16_t, [uint8x16_t; uint8x16_t])
   , cNEON
   , 0
   , false
   , None
   , ["VADD.I8 %Q0, %Q2, %Q4"]
   )
  ;
   (* uint16x8_t vaddq_u16 (uint16x8_t, uint16x8_t)  *)
   ( "__builtin_vaddq_u16"
   , (uint16x8_t, [uint16x8_t; uint16x8_t])
   , cNEON
   , 0
   , false
   , None
   , ["VADD.I16 %Q0, %Q2, %Q4"]
   )
  ;
   (* uint32x4_t vaddq_u32 (uint32x4_t, uint32x4_t)  *)
   ( "__builtin_vaddq_u32"
   , (uint32x4_t, [uint32x4_t; uint32x4_t])
   , cNEON
   , 0
   , false
   , None
   , ["VADD.I32 %Q0, %Q2, %Q4"]
   )
  ;
   (* uint64x2_t vaddq_u64 (uint64x2_t, uint64x2_t)  *)
   ( "__builtin_vaddq_u64"
   , (uint64x2_t, [uint64x2_t; uint64x2_t])
   , cNEON
   , 0
   , false
   , None
   , ["VADD.I64 %Q0, %Q2, %Q4"]
   )
  ;
   (* uint8x16_t vsubq_u8 (uint8x16_t, uint8x16_t)  *)
   ( "__builtin_vsubq_u8"
   , (uint8x16_t, [uint8x16_t; uint8x16_t])
   , cNEON
   , 0
   , false
   , None
   , ["VSUB.I8 %Q0, %Q2, %Q4"]
   )
  ;
   (* uint16x8_t vsubq_u16 (uint16x8_t, uint16x8_t)  *)
   ( "__builtin_vsubq_u16"
   , (uint16x8_t, [uint16x8_t; uint16x8_t])
   , cNEON
   , 0
   , false
   , None
   , ["VSUB.I16 %Q0, %Q2, %Q4"]
   )
  ;
   (* uint32x4_t  vsubq_u32(uint32x4_t a, uint32x4_t b)  *)
   ( "__builtin_vsubq_u32"
   , (uint32x4_t, [uint32x4_t; uint32x4_t])
   , cNEON
   , 0
   , false
   , None
   , ["VSUB.I32 %Q0, %Q2, %Q4"]
   )
  ;
   (* uint64x2_t vsubq_u64 (uint64x2_t, uint64x2_t)  *)
   ( "__builtin_vsubq_u64"
   , (uint64x2_t, [uint64x2_t; uint64x2_t])
   , cNEON
   , 0
   , false
   , None
   , ["VSUB.I64 %Q0, %Q2, %Q4"]
   )
  ;
   (* uint8x16_t veorq_u8(uint8x16_t a, uint8x16_t b) *)
   ( "__builtin_veorq"
   , (uint8x16_t, [uint8x16_t; uint8x16_t])
   , cNEON
   , 0
   , false
   , None
   , ["VEOR %Q0, %Q2, %Q4"]
   )
  ;
   (* uint8x16_t vandq_u8(uint8x16_t a, uint8x16_t b) *)
   ( "__builtin_vandq"
   , (uint8x16_t, [uint8x16_t; uint8x16_t])
   , cNEON
   , 0
   , false
   , None
   , ["VAND %Q0, %Q2, %Q4"]
   )
  ;
   (* uint64x2_t vmull_u32(uint32x2_t a, uint32x2_t b) *)
   ( "__builtin_vmull_u32"
   , (uint64x2_t, [uint32x2_t; uint32x2_t])
   , cNEON
   , 0
   , false
   , None
   , ["VMULL.U32 %Q0, %2, %3"]
   )
  ;
   (* uint64x2_t vmlal_u32(uint64x2_t a, uint32x2_t b, uint32x2_t c) *)
   ( "__builtin_vmlal_u32"
   , (uint64x2_t, [uint64x2_t; uint32x2_t; uint32x2_t])
   , cNEON
   , 0
   , true
   , None
   , ["VMLAL.U32 %Q0, %2, %3"]
   )
  ;
   (* uint32x4_t vshlq_n_u32(uint32x4_t a, __constrange(0,31) int b) *)
   ( "__builtin_vshlq_n_u32"
   , (uint32x4_t, [uint32x4_t; t_const (t_int)])
   , cNEON
   , 1
   , false
   , None
   , ["VSHL.I32 %Q0, %Q2, #%4"]
   )
  ;
   (* uint64x2_t vshlq_n_u64(uint64x2_t a, __constrange(0,63) int b) *)
   ( "__builtin_vshlq_n_u64"
   , (uint64x2_t, [uint64x2_t; t_const (t_int)])
   , cNEON
   , 1
   , false
   , None
   , ["VSHL.I64 %Q0, %Q2, #%4"]
   )
  ;
   (* uint64x2_t vshrq_n_u64(uint64x2_t a, __constrange(1,64) int b) *)
   ( "__builtin_vshrq_n_u64"
   , (uint64x2_t, [uint64x2_t; t_const (t_int)])
   , cNEON
   , 1
   , false
   , None
   , ["VSHR.U64 %Q0, %Q2, #%4"]
   )
  ]


(** * All NEON builtins *)
(** aggregation of all available builtins (in case of repetitions, firsts
  on the list have precedence...)                                        *)
let simd_builtins_gen () =
  move_builtins
  @ extra_builtins_gen ()
  @ kummer_builtins_gen ()
  @ Absolute_difference.builtins_gen ()
(*
  @ Addition.builtins_gen ()
  @ Combining_vectors.builtins_gen ()
  @ Comparison.builtins_gen ()
  @ Converting_vectors.builtins_gen ()
  @ Extended_table_look_up.builtins_gen ()
  @ Extracting_lanes_from_a_vector_into_a_register.builtins_gen ()
  @ Folding_maximum.builtins_gen ()
  @ Folding_minimum.builtins_gen ()
  @ Initializing_a_vector_from_a_literal_bit_pattern.builtins_gen ()
  @ Loading_an_N_element_structure.builtins_gen ()
  @ Loading_a_single_lane_of_a_vector_from_a_literal.builtins_gen ()
  @ Loading_a_single_vector_or_lane.builtins_gen ()
  @ Logical_operations.builtins_gen ()
  @ Maximum_and_minimum.builtins_gen ()
  @ Multiplication.builtins_gen ()
  @ Operations_with_a_scalar_value.builtins_gen ()
  @ Other_single_operand_arithmetic.builtins_gen ()
  @ Pairwise_addition.builtins_gen ()
  @ Reciprocal_and_sqrt.builtins_gen ()
  @ Reversing_vector_elements__swap_endianness.builtins_gen ()
  @ Setting_all_lanes_to_the_same_value.builtins_gen ()
  @ Shifts_by_a_constant.builtins_gen ()
  @ Shifts_by_signed_variable.builtins_gen ()
  @ Shifts_with_insert.builtins_gen ()
  @ Splitting_vectors.builtins_gen ()
  @ Storing_a_single_vector_or_lane.builtins_gen ()
  @ Subtraction.builtins_gen ()
  @ Table_look_up.builtins_gen ()
  @ Transposition_operations.builtins_gen ()
  @ Vector_cast_operations.builtins_gen ()
  @ Vector_extraction.builtins_gen ()
 *)
