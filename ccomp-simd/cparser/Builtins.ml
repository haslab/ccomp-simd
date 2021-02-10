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

(* Compiler built-ins *)

open C
open Cutil

let env = ref Env.empty
let idents = ref []
let decls = ref []

let environment () = !env
let identifiers () = !idents
let declarations () = List.rev !decls

let get_ident s =
  let rec get = function
      [] -> assert false
    | (i::is) -> if i.name = s then i else get is
  in get !idents

(*
let rec homfstruct_fieldlist t i n =
  if n > 0
  then { fld_name = "val"^(string_of_int i);
	 fld_typ = t;
	 fld_bitfield = None } :: homfstruct_fieldlist t (i+1) (n-1)
  else []
 *)
let add_typedef (s, ty) =
  let ty =
    match ty with
    | TStruct(id,a) ->
        let idlen = String.length id.name in
	let pref = String.sub id.name 0 (idlen-1) in
	let tbase = if pref = "__builtin_t32x"
		    then (TFloat(FFloat,[]))
		    else if pref = "__builtin_t64x"
		    then (TFloat(FDouble,[]))
		    else if pref = "__builtin_t128x"
		    then (TVecdata [])
		    else assert false in
	let n = Char.code(id.name.[idlen-1]) - Char.code('0') in
	let fld = [{ fld_name = "val"
		   ; fld_typ = TArray(tbase,Some (Int64.of_int n),[])
		   ; fld_bitfield = None}] in
	  (*homfstruct_fieldlist tbase 0 n in*)
	let ci = Cutil.composite_info_def !env Struct [] fld in
	let (id, env') = Env.enter_composite !env id.name ci in
	assert (n>0 && n<=4);
	env := env';
	idents := id :: !idents;
	decls := {gdesc = Gcompositedef(Struct, id, [], fld);
		  gloc = no_loc } :: !decls;
	TStruct(id,a)
    | _ -> ty
  in
  let (id, env') = Env.enter_typedef !env s ty in
  env := env';
  idents := id :: !idents;
  decls := {gdesc = Gtypedef(id, ty); gloc = no_loc} :: !decls

let add_function (s, (res, args, va)) =
  let ty =
    TFun(res,
         Some (List.map (fun ty -> (Env.fresh_ident "", ty)) args),
         va, []) in
  let (id, env') = Env.enter_ident !env s Storage_extern ty in
  env := env';
  idents := id :: !idents;
  decls := {gdesc = Gdecl(Storage_extern, id, ty, None); gloc = no_loc} :: !decls

type t = {
  typedefs: (string * C.typ) list;
  functions: unit -> (string * (C.typ * C.typ list * bool)) list
}

let set blt =
  env := Env.empty;
  idents := [];
  List.iter add_typedef blt.typedefs;
  List.iter add_function (blt.functions ())
