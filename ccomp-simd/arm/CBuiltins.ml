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

open Builtins
open CXBuiltins

let arm_builtins = {
  Builtins.typedefs = [
    "__builtin_va_list", TPtr(TVoid [], [])
  ];
  Builtins.functions = fun () -> [
    (* Integer arithmetic *)
    "__builtin_bswap",
      (TInt(IUInt, []), [TInt(IUInt, [])], false);
    "__builtin_bswap32",
      (TInt(IUInt, []), [TInt(IUInt, [])], false);
    "__builtin_bswap16",
      (TInt(IUShort, []), [TInt(IUShort, [])], false);
    "__builtin_cntlz",
      (TInt(IUInt, []), [TInt(IUInt, [])], false);
    (* Float arithmetic *)
    "__builtin_fsqrt",
      (TFloat(FDouble, []), [TFloat(FDouble, [])], false);
    (* Memory accesses *)
    "__builtin_read16_reversed",
      (TInt(IUShort, []), [TPtr(TInt(IUShort, [AConst]), [])], false);
    "__builtin_read32_reversed",
      (TInt(IUInt, []), [TPtr(TInt(IUInt, [AConst]), [])], false);
    "__builtin_write16_reversed",
      (TVoid [], [TPtr(TInt(IUShort, []), []); TInt(IUShort, [])], false);
    "__builtin_write32_reversed",
      (TVoid [], [TPtr(TInt(IUInt, []), []); TInt(IUInt, [])], false);
  ]
}

let fake_ident s = {name= s; stamp= 0}
let simd_builtins =
 { Builtins.typedefs =
     [ "__builtin_t128", TVecdata []
     ; "__builtin_t32x2_s", TStruct(fake_ident "__builtin_t32x2",[])
     ; "__builtin_t32x2_s", TStruct(fake_ident "__builtin_t32x3",[])
     ; "__builtin_t32x2_s", TStruct(fake_ident "__builtin_t32x4",[])
     ; "__builtin_t64x2_s", TStruct(fake_ident "__builtin_t64x2",[])
     ; "__builtin_t64x2_s", TStruct(fake_ident "__builtin_t64x3",[])
     ; "__builtin_t64x2_s", TStruct(fake_ident "__builtin_t64x4",[])
     ; "__builtin_t128x2_s", TStruct(fake_ident "__builtin_t128x2",[])
     ; "__builtin_t128x2_s", TStruct(fake_ident "__builtin_t128x3",[])
     ; "__builtin_t128x2_s", TStruct(fake_ident "__builtin_t128x4",[])
     ]
 ; Builtins.functions = fun () -> List.map (fun x->(x.bname, x.bsig)) 
					   (CXBuiltins.simd_builtins ())
 }

let builtins = 
  { Builtins.typedefs = arm_builtins.typedefs @ simd_builtins.typedefs
  ; Builtins.functions = fun () -> arm_builtins.functions ()
				   @ simd_builtins.functions ()
  }

let size_va_list = 4
let va_list_scalar = true
