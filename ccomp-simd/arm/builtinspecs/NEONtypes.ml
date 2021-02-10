(* NEONtypes.ml
   ============
  Standard NEON types required to specify the intrinsics                *)
open C
open Ctypes
open Cutil

(* Classes of simd-instructions: *)
let cNEON = 1

(* attributes/modifiers are handled by specific functions *)
let t_tranfsize (n,ty) = ty
let t_ptr ty = TPtr (ty, [])
let t_const ty = add_attributes_type [AConst] ty

(* C types *)
let t_void = TVoid []
let t_float = TFloat (FFloat,[])
let t_double = TFloat (FDouble,[])
let t_char = TInt (IChar,[])
let t_uchar = TInt (IUChar,[])
let t_short = TInt (IShort,[])
let t_ushort = TInt (IUShort,[])
let t_int = TInt (IInt,[])
let t_uint = TInt (IUInt,[])
let t_long = TInt (ILong,[])
let t_ulong = TInt (IULong,[])
let t_longlong = TInt (ILongLong,[])
let t_ulonglong = TInt (IULongLong,[])

(* standard types *)
let int8_t = TInt (IChar,[])
let uint8_t = TInt (IUChar,[])
let int16_t = TInt (IShort,[])
let uint16_t = TInt (IUShort,[])
let int32_t = TInt (IInt,[])
let uint32_t = TInt (IUInt,[])
let int64_t = TInt (ILongLong,[])
let uint64_t = TInt (IULongLong,[])

(* simd types *)
let builtin64_t = TFloat (FDouble,[])
let builtin128_t = TVecdata []

(* NEON types *)
let int8x8_t = builtin64_t
let int16x4_t = builtin64_t
let int32x2_t = builtin64_t
let int64x1_t = builtin64_t
let uint8x8_t = builtin64_t
let uint16x4_t = builtin64_t
let uint32x2_t = builtin64_t
let uint64x1_t = builtin64_t
let float16x4_t = builtin64_t
let float32x2_t = builtin64_t
let poly8x8_t = builtin64_t
let poly16x4_t = builtin64_t

let int8x16_t = builtin128_t
let int16x8_t = builtin128_t
let int32x4_t = builtin128_t
let int64x2_t = builtin128_t
let uint8x16_t = builtin128_t
let uint16x8_t = builtin128_t
let uint32x4_t = builtin128_t
let uint64x2_t = builtin128_t
let float16x8_t = builtin128_t
let float32x4_t = builtin128_t
let poly8x16_t = builtin128_t
let poly16x8_t = builtin128_t

