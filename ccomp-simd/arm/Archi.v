(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Jacques-Henri Jourdan, INRIA Paris-Rocquencourt            *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Architecture-dependent parameters for ARM *)

Require Import ZArith.
Require Import Fappli_IEEE.
Require Import Fappli_IEEE_bits.
Require Import Integers.

Definition big_endian := false.

Notation align_int64 := 8%Z (only parsing).
Notation align_float64 := 8%Z (only parsing).

Program Definition default_pl : bool * nan_pl 53 := (false, nat_iter 51 xO xH).

Definition choose_binop_pl (s1: bool) (pl1: nan_pl 53) (s2: bool) (pl2: nan_pl 53) :=
  (** Choose second NaN if pl2 is sNaN but pl1 is qNan.
      In all other cases, choose first NaN *)
  (Pos.testbit (proj1_sig pl1) 51 &&
   negb (Pos.testbit (proj1_sig pl2) 51))%bool.

Global Opaque big_endian default_pl choose_binop_pl.

(** compcert-simd: vector types in low-level languages 
  obs: 64bit vector operations are typed with Tfloat (since
   both share the same FPU registers)
*)
Local Open Scope Z_scope.

(* Inductive vec_variant_t : Type := T128.
   obs: but it seems to break "decide equality" !!! :-( *)
Definition vec_variant : Type := unit.

Lemma vec_typ_eq: forall (t1 t2: vec_variant), {t1=t2} + {t1<>t2}.
Proof. decide equality. Defined.

(* remark: typesize is specified in 32bit units (to be compatible
  with Locations.v *)
Definition vec_typesize (t:vec_variant) : Z := 4.

Lemma vec_typesize_pos: forall t, vec_typesize t > 0.
Proof. destruct t; unfold vec_typesize; omega. Qed.

Definition vec_variant_sem (t:vec_variant) : Type := Int128.int.

Definition vec_intval {t} (v:vec_variant_sem t) : Z := Int128.unsigned v.

Definition vec_repr {t} (v:Z) : vec_variant_sem t := Int128.repr v.

(* for the sake of somplicity, we consider a chunk-definition
 for each of the vec-variants available...
Definition vec_chunk : Type := unit.

Definition vec_type_of_chunk (c:vec_chunk) : vec_variant := tt.
Definition vec_chunk_of_type (c:vec_variant) : vec_chunk := tt.
*)

(* alignment is specified in bytes --- we adopt the same alignment
 as for Tfloat *)
Definition vec_align_chunk (t:vec_variant) : Z := align_float64.

(*Notation align_vec128 := 16%Z (only parsing).*)

Lemma vec_align_chunk_pos: forall t, vec_align_chunk t > 0.
Proof. destruct t; unfold vec_align_chunk; omega. Qed.

Lemma vec_align_le_divides: forall t, 
  (vec_align_chunk t | 4 * vec_typesize t).
Proof.
destruct t; unfold vec_align_chunk, vec_typesize; simpl.
exists 2; omega.
Qed.

(** [vec_low_off] should be [x-1] when [x] is the size of the second
  biggest slot-size *)
Definition vec_low_off := 7.

Definition vec_widest := tt.

Hint Unfold vec_widest vec_low_off.

(** remark: [vec_variant_index] should be monotonic wrt [typesize] *)
Definition vec_variant_index (t:vec_variant) : positive := 1%positive.


(** Homogeneous aggregates maximum size *)
Definition hom_fstruct_size := 4%nat.
