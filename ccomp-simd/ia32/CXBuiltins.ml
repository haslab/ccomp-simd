open C
open Cutil
open Camlcoq
open Ctypes

open Printf

open SSEbuiltins
(* obs: simd-classes (-m options) and type abbrevs. are defined in
  SSEbuiltins. *)

(* Handling of -m options *)

let ia32_mopts =
[ "-mpclmul", "enable PCLMUL support", cPCLMUL, ["__PCLMUL__"], None
; "-mmmx", "enable mmx support", cMMX, ["__MMX__"], None (** NOTE: CHECKME **)
; "-maes", "enable AESNI support", cAES, ["__AES__"], None
; "-msse42", "enable SSE4.2 support", cSSE42, ["__SSE4_2__"], Some "-msse41"
; "-msse41", "enable SSE4.1 support", cSSE41, ["__SSE4_1__"], Some "-mssse3"
; "-mssse3", "enable SSSE3 support", cSSSE3, ["__SSSE3__"], Some "-msse3"
; "-msse3", "enable SSE3 support", cSSE3, ["__SSE3__"], Some "-msse2"
; "-msse2", "enable SSE2 support", cSSE2, ["__SSE2__"], Some "-msse"
; "-msse", "enable SSE support", cSSE, ["__SSE__"], None
]

type builtin_spec = { bname: string;		(* builtin name *)
		      bsig: C.typ * C.typ list * bool;		(* signature *)
		      bmsize: (bool*int) option;(* type/size of mem access *)
		      bclass: int;		(* simd class *)
		      bimmargs: int list;	(* immediate args *)
		      basm: string;		(* asm instruction *)
		      btwoaddr: bool		(* two-addr. instr. *)
		    }

(** Main builtin table *)

let simd_builtin_functions : (AST.ident, builtin_spec) Hashtbl.t =
  Hashtbl.create 103

let simd_builtin_find id =
 try Some (Hashtbl.find simd_builtin_functions id)
 with Not_found -> None

(** Extracting Security-type info from a builtin... *)

(* List of unsupported builtins (names)... *)
let simd_builtin_blacklist = []

let simd_infer_stype blt args =
  let rec split_ptr_args targs rargs =
    match targs, rargs with
    | [], ys -> (None, [])
    | xs, [] -> (None, []) (* dangerous! relying on the fact that immargs are always the last parameters... *)
    | x::xs, y::ys ->
       (match x, split_ptr_args xs ys with 
	| TPtr (ty,_), (None, l) -> (Some y, l)
	| TPtr _, (Some _, l) -> assert false
	| _, (p,l) -> (p,y::l)
       )
  in let name = blt.bname
     and (tres, targs, _) = blt.bsig
  in let (ptr,rargs) = split_ptr_args targs args
  in if List.mem name simd_builtin_blacklist
     then None (* UNSUPPORTED *)
     else match ptr with
	  | None -> (* THIS IS A PURE BUILTIN *)
	     Some (args, None)
	  | Some ptrreg -> (* THIS IS A MEM ACCESS *)
	     match blt.bmsize with
	     | Some (b,0) -> Some (args,None) (* explicit PURE *)
	     | Some (b,size) -> Some (rargs, Some (b,(ptrreg,size)))
	     | _ -> assert false

let simd_builtin_infer_stype blt args =
  match simd_builtin_find blt with
  | Some bspec ->
     (match simd_infer_stype bspec args with
      | Some (rargs, Some (wr,(ptrref, size))) ->
	 Some (rargs, Some (wr,(ptrref,Z.of_uint size)))
      | Some (rargs, None) -> Some (rargs, None)
      | None -> None)
  | None -> None

(** Build builtin table... *)

let dbg_stype_info blt =
  (*printf "%s \t" blt.bname;*)
  let stype_info = simd_infer_stype blt [1;2;3;4;5;6;7;8;9;10] in
  match stype_info with
  | None -> printf "UNSUPPORTED\n"
  | Some (rargs, None) -> (*printf "PURE\n"*) ()
  | Some (rargs, Some (false, (ptr, size))) -> 
     printf "LOAD  %2d bytes - %s\n" size blt.bname
  | Some (rargs, Some (true, (ptr, size))) -> 
     printf "STORE %2d bytes - %s\n" size blt.bname


let simd_builtins_set mmask builtins =
  List.fold_left (fun a b -> 
                    if ((1 lsl b.bclass) land mmask)!=0
		    then Hashtbl.replace simd_builtin_functions
					 (intern_string b.bname) b
		    else ()) () builtins
  (*; Hashtbl.iter (fun a b -> dbg_stype_info b) simd_builtin_functions*)

let simd_builtins_printall () = 
  Hashtbl.iter (fun a b -> printf "%s " b.bname) simd_builtin_functions

let sse_builtins =
  let mkblt =
    function (n,s,c,i,a,t) ->
     {bname=n; bsig=s; bmsize=None; bclass=c; bimmargs=i; basm=a; btwoaddr=t}
  in List.map mkblt simd_builtins_gen

let sse_builtins_replace =
[
   { bname = "__builtin_ia32_loadupd"
   ; bsig = (t_v2df, [t_ptr (t_double)], false)
   ; bmsize = Some (false, 16)
   ; bclass = cSSE2
   ; bimmargs = []		
   ; basm = "movupd (%1), %0"
   ; btwoaddr = false
   }
;  { bname = "__builtin_ia32_loadlpd"
   ; bsig = (t_v2df, [t_v2df;t_ptr (t_const (t_double))], false)
   ; bmsize = Some (false, 8)
   ; bclass = cSSE2
   ; bimmargs = []		
   ; basm = "movlpd (%2), %1"
   ; btwoaddr = true
   }
;  { bname = "__builtin_ia32_loadhpd"
   ; bsig = (t_v2df, [t_v2df;t_ptr (t_const (t_double))], false)
   ; bmsize = Some (false, 8)
   ; bclass = cSSE2
   ; bimmargs = []		
   ; basm = "movhpd (%2), %1"
   ; btwoaddr = true
   }
;  { bname = "__builtin_ia32_loaddqu"
   ; bsig = (t_v16qi, [t_ptr (t_const (t_char))], false)
   ; bmsize = Some (false, 16)
   ; bclass = cSSE2
   ; bimmargs = []		
   ; basm = "movdqu (%1), %0"
   ; btwoaddr = false
   }
;  { bname = "__builtin_ia32_loadups"
   ; bsig = (t_v4sf, [t_ptr (t_float)], false)
   ; bmsize = Some (false, 16) 
   ; bclass = cSSE
   ; bimmargs = []		
   ; basm = "movups (%1), %0"	
   ; btwoaddr = false
   }
;  { bname = "__builtin_ia32_lddqu"
   ; bsig = (t_v16qi, [t_ptr (t_const (t_char))], false)
   ; bmsize = Some (false, 16)
   ; bclass = cSSE3
   ; bimmargs = []		
   ; basm = "lddqu (%1), %0"	
   ; btwoaddr = false
   }
;  { bname = "__builtin_ia32_loadss"
   ; bsig = (t_v4sf, [t_ptr (t_float)], false)
   ; bmsize = Some (false, 4)
   ; bclass = cSSE
   ; bimmargs = []		
   ; basm = "movss (%1), %0"
   ; btwoaddr = false
   }
;  { bname = "__builtin_ia32_monitor"
   ; bsig = (t_void, [t_ptr (t_void);t_uint;t_uint], false)
   ; bmsize = Some (true, 0)
   ; bclass = cSSE3
   ; bimmargs = []		
   ; basm = "nyi"	
   ; btwoaddr = true
   }
;  { bname = "__builtin_ia32_mwait"
   ; bsig = (t_void, [t_uint;t_uint], false)
   ; bmsize = Some (true,0)
   ; bclass = cSSE3
   ; bimmargs = []		
   ; basm = "nyi"
   ; btwoaddr = true
   }
;  { bname = "__builtin_ia32_storeups"
   ; bsig = (t_void, [t_ptr (t_float);t_v4sf], false)
   ; bmsize = Some (true, 16)
   ; bclass = cSSE
   ; bimmargs = []		
   ; basm = "movups %2, (%1)"	
   ; btwoaddr = true
   }
;  { bname = "__builtin_ia32_storedqu"
   ; bsig = (t_void, [t_ptr (t_char);t_v16qi], false)
   ; bmsize = Some (true, 16)
   ; bclass = cSSE2
   ; bimmargs = []		
   ; basm = "movdqu %2, (%1)"
   ; btwoaddr = true
   }
;  { bname = "__builtin_ia32_storeupd"
   ; bsig = (t_void, [t_ptr (t_double);t_v2df], false)
   ; bmsize = Some (true, 16)
   ; bclass = cSSE2
   ; bimmargs = []		
   ; basm = "movupd %2, (%1)"	
   ; btwoaddr = true
   }
;  { bname = "__builtin_ia32_clflush"					(* wrong *)
   ; bsig = (t_void, [(*0*)t_ptr (t_const (t_void))], false)
   ; bmsize = Some (true,0)
   ; bclass = cSSE2
   ; bimmargs = []		
   ; basm = "clflush (%1)"
   ; btwoaddr = true		
   }
;  { bname = "__builtin_ia32_movntps"					(* wrong *)
   ; bsig = (t_void, [t_ptr t_float; t_v4sf], false)
   ; bmsize = Some (true,16)
   ; bclass = cSSE
   ; bimmargs = []		
   ; basm = "movntps %2, (%1)"
   ; btwoaddr = true		
   }
;  { bname = "__builtin_ia32_movnti"					(* wrong *)
   ; bsig = (t_void, [t_ptr (t_int);t_int], false)
   ; bmsize = Some (true,4)
   ; bclass = cSSE2
   ; bimmargs = []		
   ; basm = "movnti %2, (%1)"
   ; btwoaddr = true		
   }
;  { bname = "__builtin_ia32_movnti64"					(* wrong *)
   ; bsig = (t_void, [t_ptr (t_longlong);t_longlong], false)
   ; bmsize = Some (true,8)
   ; bclass = cSSE2
   ; bimmargs = []		
   ; basm = "nyi" (*"movnti %2, (%1)"*)
   ; btwoaddr = true		
   }
;  { bname = "__builtin_ia32_movntpd"					(* wrong *)
   ; bsig = (t_void, [t_ptr (t_double);t_v2df], false)
   ; bmsize = Some (true,16)
   ; bclass = cSSE2
   ; bimmargs = []		
   ; basm = "movntpd %2, (%1)"
   ; btwoaddr = true		
   }
;  { bname = "__builtin_ia32_movntdq"					(* wrong *)
   ; bsig = (t_void, [t_ptr (t_v2df);t_v2df], false)
   ; bmsize = Some (true,16)
   ; bclass = cSSE2
   ; bimmargs = []		
   ; basm = "movntdq %2, (%1)"		
   ; btwoaddr = true		
   }
;  { bname = "__builtin_ia32_maskmovdqu"				(* wrong *)
   ; bsig = (t_void, [t_v16qi; t_v16qi; t_ptr t_v16qi], false)
   ; bmsize = Some (true,16)
   ; bclass = cSSE2
   ; bimmargs = []		
   ; basm = "MASKMOVDQU %1, %0"		
   ; btwoaddr = true		
   }
;  { bname = "__builtin_ia32_storess"				(* missing *)
   ; bsig = t_void, [t_ptr (t_float);t_v4sf], false
   ; bmsize = Some (true,4)
   ; bclass = cSSE
   ; bimmargs = []
   ; basm = "MOVSS %2, (%1)"
   ; btwoaddr = true
   }
;  { bname = "__builtin_ia32_stmxcsr"				(* missing *)
   ; bsig = t_void, [t_ptr t_uint], false
   ; bmsize = Some (true,4)
   ; bclass = cSSE
   ; bimmargs = []
   ; basm = "STMXCSR (%0)"
   ; btwoaddr = true
   }
;  { bname = "__builtin_ia32_ldmxcsr"				(* missing *)
   ; bsig = t_void, [t_ptr t_uint], false
   ; bmsize = Some (false,4)
   ; bclass = cSSE
   ; bimmargs = []
   ; basm = "LDMXCSR (%0)"
   ; btwoaddr = true
   }
;  { bname = "__builtin_ia32_pause"				(* missing *)
   ; bsig = t_void, [], false
   ; bmsize = None
   ; bclass = cSSE2
   ; bimmargs = []
   ; basm = "PAUSE"
   ; btwoaddr = false
   }
;  { bname = "__builtin_ia32_paddsb128"				(* missing *)
   ; bsig = t_v16qi, [t_v16qi; t_v16qi], false
   ; bmsize = None
   ; bclass = cSSE2
   ; bimmargs = []
   ; basm = "PADDSB"
   ; btwoaddr = true
   }
;  { bname = "__builtin_ia32_paddsw128"				(* missing *)
   ; bsig = t_v8hi, [t_v8hi; t_v8hi], false
   ; bmsize = None
   ; bclass = cSSE2
   ; bimmargs = []
   ; basm = "PADDSW"
   ; btwoaddr = true
   }
;  { bname = "__builtin_ia32_paddusb128"			(* missing *)
   ; bsig = t_v16qi, [t_v16qi; t_v16qi], false
   ; bmsize = None
   ; bclass = cSSE2
   ; bimmargs = []
   ; basm = "PADDUSB"
   ; btwoaddr = true
   }
;  { bname = "__builtin_ia32_paddusw128"			(* missing *)
   ; bsig = t_v8hi, [t_v8hi; t_v8hi], false
   ; bmsize = None
   ; bclass = cSSE2
   ; bimmargs = []
   ; basm = "PADDUSW"
   ; btwoaddr = true
   }
;  { bname = "__builtin_ia32_psubsb128"				(* missing *)
   ; bsig = t_v16qi, [t_v16qi; t_v16qi], false
   ; bmsize = None
   ; bclass = cSSE2
   ; bimmargs = []
   ; basm = "PSUBSB"
   ; btwoaddr = true
   }
;  { bname = "__builtin_ia32_psubsw128"				(* missing *)
   ; bsig = t_v8hi, [t_v8hi; t_v8hi], false
   ; bmsize = None
   ; bclass = cSSE2
   ; bimmargs = []
   ; basm = "PSUBSW"
   ; btwoaddr = true
   }
;  { bname = "__builtin_ia32_psubusb128"			(* missing *)
   ; bsig = t_v16qi, [t_v16qi; t_v16qi], false
   ; bmsize = None
   ; bclass = cSSE2
   ; bimmargs = []
   ; basm = "PSUBUSB"
   ; btwoaddr = true
   }
;  { bname = "__builtin_ia32_psubusw128"			(* missing *)
   ; bsig = t_v8hi, [t_v8hi; t_v8hi], false
   ; bmsize = None
   ; bclass = cSSE2
   ; bimmargs = []
   ; basm = "PSUBUSW"
   ; btwoaddr = true
   }
(* not handled by procSSEbuiltins.py
__builtin_ia32_vec_set_v4sf
__builtin_ia32_vec_ext_v16qi 
__builtin_ia32_vec_set_v16qi
__builtin_ia32_vec_set_v4si
__builtin_ia32_vec_set_v2di
__builtin_ia32_vec_ext_v4sf
__builtin_ia32_vec_ext_v4si
__builtin_ia32_vec_ext_v2di
 *)

(** NOTE: _m64 vars not supported **)
;  { bname = "__builtin_ia32_vec_ext_v2df"			(* missing *)
   ; bsig = t_double, [t_v2df; t_const t_int], false
   ; bmsize = None
   ; bclass = cSSE41	(* for convenience!!! *)
   ; bimmargs = [1]
   ; basm = "nyi"
   ; btwoaddr = false
   }
(** NOTE: new supported builtin : __builtin_ia32_storeh_pd **)
;  { bname = "__builtin_ia32_storeh_pd"
   ; bsig = t_void, [t_ptr t_double; t_v2df], false
   ; bmsize = Some (true,8)
   ; bclass = cSSE41	(* for convenience!!! *)
   ; bimmargs = []
   ; basm = "movhpd %2, (%1)"
   ; btwoaddr = false
   }
;  { bname = "__builtin_ia32_vec_set_v2df"			(* missing *)
   ; bsig = t_v2df, [t_v2df; t_double; t_const t_int], false
   ; bmsize = None
   ; bclass = cSSE41	(* for convenience!!! *)
   ; bimmargs = [2]
   ; basm = "nyi"
   ; btwoaddr = true
   }
(* requires x64 support!!! replace by _loadl_epi64 and _loadhpi
;  { bname = "__builtin_ia32_vec_ext_v2di"			(*nothandled*)
   ; bsig = t_longlong, [t_v2di; t_const t_int], false
   ; bclass = cSSE41	(* for convenience!!! *)
   ; bimmargs = [1]
   ; basm = "nyi"
   ; btwoaddr = false
   }
 *)
;  { bname = "__builtin_ia32_loadl_epi64"
   ; bsig = t_v2di, [t_ptr t_longlong], false
   ; bmsize = Some (false, 8)
   ; bclass = cSSE2
   ; bimmargs = []
   ; basm = "movq (%1), %0"
   ; btwoaddr = false
   }
(* ESTRANHO!!! o i64 deve ser partido em dois! Que tal passar para t_double?*)
;  { bname = "__builtin_ia32_storel_epi64"
   ; bsig = t_void, [(*D*)t_ptr t_longlong; t_v2di], false
   ; bmsize = Some (true,8)
   ; bclass = cSSE2
   ; bimmargs = []
   ; basm = "movq %2, (%1)"
   ; btwoaddr = true
   }
;  { bname = "__builtin_ia32_vec_set_v2di"			(*nothandled*)
   ; bsig = t_v2di, [t_v2di; t_longlong; t_const t_int], false
   ; bmsize = None
   ; bclass = cSSE41	(* for convenience!!! *)
   ; bimmargs = [2]
   ; basm = "nyi"
   ; btwoaddr = true
   }
(** NOTE: _mm_cvtsi128_si32 **)
;  { bname = "__builtin_ia32_vec_ext_v4si"
   ; bsig = t_int, [t_v4si; t_const t_int], false
   ; bmsize = None
   ; bclass = cSSE41	(* for convenience!!! *)
   ; bimmargs = [1]
   ; basm = "movd %1, %0"
   ; btwoaddr = false
   }
(** NOTE: _mm_insert_epi32 **)
;  { bname = "__builtin_ia32_vec_set_v4si"
   ; bsig = t_v4si, [t_v4si; t_int; t_const t_int], false
   ; bmsize = None
   ; bclass = cSSE41	(* for convenience!!! *)
   ; bimmargs = [2]
   ; basm = "pinsrd"
   ; btwoaddr = true
   }
;  { bname = "__builtin_ia32_vec_ext_v4sf"			(*nothandled*)
   ; bsig = t_float, [t_v4sf; t_const t_int], false
   ; bmsize = None
   ; bclass = cSSE41	(* for convenience!!! *)
   ; bimmargs = [1]
   ; basm = "nyi"
   ; btwoaddr = false
   }
;  { bname = "__builtin_ia32_vec_set_v4sf"			(*nothandled*)
   ; bsig = t_v4sf, [t_v4sf; t_float; t_const t_int], false
   ; bmsize = None
   ; bclass = cSSE41	(* for convenience!!! *)
   ; bimmargs = [2]
   ; basm = "nyi"
   ; btwoaddr = true
   }
(** NOTE: _mm_extract_epi16 **)
;  { bname = "__builtin_ia32_vec_ext_v8hi"
   ; bsig = t_short, [t_v8hi; t_const t_int], false
   ; bmsize = None
   ; bclass = cSSE41	(* for convenience!!! *)
   ; bimmargs = [1]
   ; basm = "pextrw"
   ; btwoaddr = false
   }
(** NOTE: _mm_insert_epi16 **)
;  { bname = "__builtin_ia32_vec_set_v8hi"
   ; bsig = t_v8hi, [t_v8hi; t_short; t_const t_int], false
   ; bmsize = None
   ; bclass = cSSE41	(* for convenience!!! *)
   ; bimmargs = [2]
   ; basm = "pinsrw"
   ; btwoaddr = true
   }
(** NOTE: _mm_extract_epi8 **)
;  { bname = "__builtin_ia32_vec_ext_v16qi"
   ; bsig = t_char, [t_v16qi; t_const t_int], false
   ; bmsize = None
   ; bclass = cSSE41	(* for convenience!!! *)
   ; bimmargs = [1]
   ; basm = "pextrb"
   ; btwoaddr = false
   }
(** NOTE: _mm_insert_epi8 **)
;  { bname = "__builtin_ia32_vec_set_v16qi"			(*nothandled*)
   ; bsig = t_v16qi, [t_v16qi; t_char; t_const t_int], false
   ; bmsize = None
   ; bclass = cSSE41	(* for convenience!!! *)
   ; bimmargs = [2]
   ; basm = "pinsrb"
   ; btwoaddr = true
   }
]

let simd_builtins = sse_builtins @ sse_builtins_replace

