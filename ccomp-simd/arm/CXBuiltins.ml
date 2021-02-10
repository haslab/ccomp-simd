open Builtindata
open C
open Cutil
open Ctypes
open Camlcoq
open NEONbuiltins
open Machregs
open Printf

type builtin_spec =
  { bname: string			(* builtin name *)
  ; bsig: C.typ * C.typ list * bool	(* signature *)
  ; bclass: int				(* simd class *)
  ; bimmargs: int			(* immediate args *)
  ; btwoaddr: bool			(* two-addr. instr. *)
  ; bdestr: (string list) option	(* destroyed regs (precolored) *)
  ; basm: string list;			(* asm instructions *)
  }

let builtin_spec_eq b1 b2 =
  b1.bname = b2.bname  && b1.bsig = b2.bsig && b1.bclass = b2.bclass &&
  b1.bimmargs = b2.bimmargs && b1.btwoaddr = b2.btwoaddr &&
  b1.bdestr = b2.bdestr && b1.basm = b2.basm 
  

let mkBlt_data blt immargs = { blt_class = blt.bclass
			     ; blt_asm = blt.basm
			     ; blt_imms = blt.bimmargs
			     ; blt_immargs = immargs
			     ; blt_destr = blt.bdestr
			     ; blt_twoaddr = blt.btwoaddr
			     }

let simd_builtin_functions : (AST.ident, builtin_spec) Hashtbl.t =
  Hashtbl.create 103

(* first elements in list have precedence over remaining ones... *)
let simd_builtins_set mmask builtins =
  List.fold_right (fun b a -> if ((1 lsl b.bclass) land mmask)!=0
			      then Hashtbl.replace simd_builtin_functions
					      (intern_string b.bname) b
			      else ()) builtins ()

let simd_builtin_find id =
 try Some (Hashtbl.find simd_builtin_functions id)
 with Not_found -> None

let simd_builtins_printall () = 
  Hashtbl.iter (fun a b -> printf "%s " b.bname) simd_builtin_functions

let list_take n l =
  let rec loop n = function
    | h :: t when n > 0 ->
      h::loop (n - 1) t
    | _ -> []
  in loop n l

let simd_builtins () =
  let mkblt = function (n,(res,args),c,i,t,d,a) ->
	       { bname=n; bsig=(res,args,false); bclass=c; bimmargs=i;
                 btwoaddr=t; bdestr=d; basm=a}
  in List.map mkblt (simd_builtins_gen ())
