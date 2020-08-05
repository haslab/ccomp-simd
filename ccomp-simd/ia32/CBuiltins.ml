(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Processor-dependent builtin C functions *)

open C
open Clflags
open Builtins
open CXBuiltins


let t_ul = TInt(IULongLong, [])
let t_sl = TInt(ILongLong, [])
let t_f = TFloat(FDouble, [])
let t_s = TFloat(FFloat, [])
let t_ui = TInt(IUInt, [])

let ia32_i64_builtins =
  [
    "__builtin_negl", (t_sl, [t_sl], false)
  ; "__builtin_addl", (t_sl, [t_sl; t_sl], false)
  ; "__builtin_subl", (t_sl, [t_sl; t_sl], false)
  ; "__builtin_mull", (t_sl, [t_sl; t_sl], false)
  ]

let ia32_i64_helpers =
  [
    "__i64_dtos", (t_sl, [t_f], false)
  ; "__i64_dtou", (t_ul, [t_f], false)
  ; "__i64_stod", (t_f, [t_sl], false)
  ; "__i64_utod", (t_f, [t_ul], false)
  ; "__i64_stof", (t_s, [t_sl], false)
  ; "__i64_utof", (t_s, [t_ul], false)
  ; "__i64_sdiv", (t_sl, [t_sl; t_sl], false)
  ; "__i64_udiv", (t_ul, [t_ul; t_ul], false)
  ; "__i64_smod", (t_sl, [t_sl; t_sl], false)
  ; "__i64_umod", (t_ul, [t_ul; t_ul], false)
  ; "__i64_shl", (t_ul, [t_ul; t_ui], false)
  ; "__i64_shr", (t_ul, [t_ul; t_ui], false)
  ; "__i64_sar", (t_sl, [t_sl; t_ui], false)
  ]

let ia32_builtins = {
  Builtins.typedefs = [
    "__builtin_va_list", TPtr(TVoid [], [])
  ];
  Builtins.functions =
    ia32_i64_builtins @ 
    ia32_i64_helpers @ 
    [
    (* Integer arithmetic *)
    "__builtin_bswap",
      (TInt(IUInt, []), [TInt(IUInt, [])], false);
    "__builtin_bswap32",
      (TInt(IUInt, []), [TInt(IUInt, [])], false);
    "__builtin_bswap64",
      (TInt(IULongLong, []), [TInt(IULongLong, [])], false);
    "__builtin_bswap16",
      (TInt(IUShort, []), [TInt(IUShort, [])], false);
    (* Float arithmetic *)
    "__builtin_fsqrt",
      (TFloat(FDouble, []), [TFloat(FDouble, [])], false);
    "__builtin_fmax",
      (TFloat(FDouble, []), [TFloat(FDouble, []); TFloat(FDouble, [])], false);
    "__builtin_fmin",
      (TFloat(FDouble, []), [TFloat(FDouble, []); TFloat(FDouble, [])], false);
    (* Memory accesses *)
    "__builtin_read16_reversed",
      (TInt(IUShort, []), [TPtr(TInt(IUShort, [AConst]), [])], false);
    "__builtin_read32_reversed",
      (TInt(IUInt, []), [TPtr(TInt(IUInt, [AConst]), [])], false);
    "__builtin_write16_reversed",
      (TVoid [], [TPtr(TInt(IUShort, []), []); TInt(IUShort, [])], false);
    "__builtin_write32_reversed",
      (TVoid [], [TPtr(TInt(IUInt, []), []); TInt(IUInt, [])], false);
    (* Access to RDTSC counter *)
    "__builtin_rdtsc",
      (TInt(IULongLong, []), [], false);
  ]
}

let simd_builtins =
 { Builtins.typedefs = [ "__builtin_t128", TVecdata [] ]
 ; Builtins.functions = List.map (fun x->(x.bname, x.bsig)) 
				 CXBuiltins.simd_builtins
 }


let builtins = 
  { Builtins.typedefs = ia32_builtins.typedefs @ simd_builtins.typedefs
  ; Builtins.functions = ia32_builtins.functions @ simd_builtins.functions
  }

let size_va_list = 4
let va_list_scalar = true
