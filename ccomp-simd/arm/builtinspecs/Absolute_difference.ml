(** Absolute_difference.ml *)
open C
open Ctypes
open Cutil

open NEONtypes

(*
 modificadores são funções:
  - e.g. t_const(uint32_t)
  - e.g. t_ptr(uint8_t)
  - e.g. t_transfsize(16, t_ptr(uint32x4_t))
 *)

let builtins_gen () =
  let t64x2_t = TStruct(Builtins.get_ident "__builtin_t64x2",[])
  and t64x3_t = TStruct(Builtins.get_ident "__builtin_t64x3",[])
  and t64x4_t = TStruct(Builtins.get_ident "__builtin_t64x4",[])
  and t128x2_t = TStruct(Builtins.get_ident "__builtin_t128x2",[])
  and t128x3_t = TStruct(Builtins.get_ident "__builtin_t128x3",[])
  and t128x4_t = TStruct(Builtins.get_ident "__builtin_t128x4",[]) in
  let int8x8x2_t = t64x2_t and int16x4x2_t = t64x2_t
  and int32x2x2_t = t64x2_t and int64x1x2_t = t64x2_t
  and uint8x8x2_t = t64x2_t and uint16x4x2_t = t64x2_t 
  and uint32x2x2_t = t64x2_t and uint64x1x2_t = t64x2_t
  and float32x2x2_t = t64x2_t and poly8x8x2_t = t64x2_t
  and poly16x4x2_t = t64x2_t in
  let int8x16x2_t = t128x2_t and int16x8x2_t = t128x2_t
  and int32x4x2_t = t128x2_t and int64x2x2_t = t128x2_t
  and uint8x16x2_t = t128x2_t and uint16x8x2_t = t128x2_t
  and uint32x4x2_t = t128x2_t and uint64x2x2_t = t128x2_t
  and float32x4x2_t = t128x2_t and poly8x16x2_t = t128x2_t
  and poly16x8x2_t = t128x2_t in
  let int8x8x3_t = t64x3_t and int16x4x3_t = t64x3_t
  and int32x2x3_t = t64x3_t and int64x1x3_t = t64x3_t
  and uint8x8x3_t = t64x3_t and uint16x4x3_t = t64x3_t 
  and uint32x2x3_t = t64x3_t and uint64x1x3_t = t64x3_t
  and float32x2x3_t = t64x3_t and poly8x8x3_t = t64x3_t
  and poly16x4x3_t = t64x3_t in
  let int8x16x3_t = t128x3_t and int16x8x3_t = t128x3_t
  and int32x4x3_t = t128x3_t and int64x2x3_t = t128x3_t
  and uint8x16x3_t = t128x3_t and uint16x8x3_t = t128x3_t
  and uint32x4x3_t = t128x3_t and uint64x2x3_t = t128x3_t
  and float32x4x3_t = t128x3_t and poly8x16x3_t = t128x3_t
  and poly16x8x3_t = t128x3_t in
  let int8x8x4_t = t64x4_t and int16x4x4_t = t64x4_t
  and int32x2x4_t = t64x4_t and int64x1x4_t = t64x4_t
  and uint8x8x4_t = t64x4_t and uint16x4x4_t = t64x4_t 
  and uint32x2x4_t = t64x4_t and uint64x1x4_t = t64x4_t
  and float32x2x4_t = t64x4_t and poly8x8x4_t = t64x4_t
  and poly16x4x4_t = t64x4_t in
  let int8x16x4_t = t128x4_t and int16x8x4_t = t128x4_t
  and int32x4x4_t = t128x4_t and int64x2x4_t = t128x4_t
  and uint8x16x4_t = t128x4_t and uint16x8x4_t = t128x4_t
  and uint32x4x4_t = t128x4_t and uint64x2x4_t = t128x4_t
  and float32x4x4_t = t128x4_t and poly8x16x4_t = t128x4_t
  and poly16x8x4_t = t128x4_t in
  [
   (* uint32x2_t  vget_high_u32(uint32x4_t a) *)
   ( "__builtin_vget_high"
   , (uint32x2_t, [uint32x4_t])
   , cNEON
   , 0
   , false
   , None
   , ["VMOV %0, %2"]
   )
  ;
   (* uint32x4_t  vcombine_u32(uint32x2_t low, uint32x2_t high) *)
   ( "__builtin_vcombine"
   , (uint32x4_t, [uint32x2_t; uint32x2_t])
   , cNEON
   , 0
   , false
   , None
   , ["VMOV %0, %2"; "VMOV %1, %3"]
   )
  ]


(*
let int8x8_t 
and int16x4_t
and int32x2_t
and int64x1_t
and uint8x8_t
and uint16x4_t
and uint32x2_t
and uint64x1_t
and float32x2_t
and poly8x8_t
and poly16x4_t

let int8x16_t
and int16x8_t
and int32x4_t
and int64x2_t
and uint8x16_t
and uint16x8_t
and uint32x4_t
and uint64x2_t
and float32x4_t
and poly8x16_t
and poly16x8_t
 *)
