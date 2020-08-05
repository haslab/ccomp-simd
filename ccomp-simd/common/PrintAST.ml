(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Useful functions for pretty-printers *)

open Printf
open Camlcoq
open AST

let name_of_type = function
  | Tint -> "int"
  | Tfloat -> "float"
  | Tlong -> "long"
  | Tsingle -> "single"
  | T128 -> "t128"

let name_of_chunk = function
  | Mint8signed -> "int8s"
  | Mint8unsigned -> "int8u"
  | Mint16signed -> "int16s"
  | Mint16unsigned -> "int16u"
  | Mint32 -> "int32"
  | Mint64 -> "int64"
  | Mint128 -> "int128"
  | Mfloat32 -> "float32"
  | Mfloat64 -> "float64"

let rec sprintf_seplist sep l =
  match l with
  | [] -> ""
  | [x] -> sprintf "%s" x
  | x::xs -> sprintf "%s%s %s" x sep (sprintf_seplist sep xs)

let name_of_external = function
  | EF_external(name, sg) -> sprintf "extern “%s”" (extern_atom name)
  | EF_builtin(name, imms, sg) -> sprintf "builtin “%s” <%s>" (extern_atom name) (sprintf_seplist "," (List.map Z.to_string imms))
  | EF_vload chunk -> sprintf "volatile load %s" (name_of_chunk chunk)
  | EF_vstore chunk -> sprintf "volatile store %s" (name_of_chunk chunk)
  | EF_vload_global(chunk, id, ofs) ->
      sprintf "volatile load %s global “%s” %ld"
              (name_of_chunk chunk) (extern_atom id) (camlint_of_coqint ofs)
  | EF_vstore_global(chunk, id, ofs) ->
      sprintf "volatile store %s global “%s” %ld"
              (name_of_chunk chunk) (extern_atom id) (camlint_of_coqint ofs)
  | EF_malloc -> "malloc"
  | EF_free -> "free"
  | EF_memcpy(sz, al) ->
      sprintf "memcpy size %s align %s " (Z.to_string sz) (Z.to_string al)
  | EF_annot(text, targs) -> sprintf "annot “%s”" (extern_atom text)
  | EF_annot_val(text, targ) ->  sprintf "annot_val “%s”" (extern_atom text)
  | EF_inline_asm text -> sprintf "inline_asm “%s”" (extern_atom text)
