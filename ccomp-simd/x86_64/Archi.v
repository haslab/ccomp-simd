(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                Xavier Leroy, INRIA Paris                            *)
(*                Jacques-Henri Jourdan, INRIA Paris                   *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Architecture-dependent parameters for x86 in 64-bit mode *)

Require Import ZArith List.
(*From Flocq*)
Require Import Binary Bits.

Definition ptr64 := true.

Definition big_endian := false.

Definition align_int64 := 8%Z.
Definition align_float64 := 8%Z.

Definition splitlong := negb ptr64.

Lemma splitlong_ptr32: splitlong = true -> ptr64 = false.
Proof.
  unfold splitlong. destruct ptr64; simpl; congruence.
Qed.

Definition default_nan_64 := (true, iter_nat 51 _ xO xH).
Definition default_nan_32 := (true, iter_nat 22 _ xO xH).

(* Always choose the first NaN argument, if any *)

Definition choose_nan_64 (l: list (bool * positive)) : bool * positive :=
  match l with nil => default_nan_64 | n :: _ => n end.

Definition choose_nan_32 (l: list (bool * positive)) : bool * positive :=
  match l with nil => default_nan_32 | n :: _ => n end.

Lemma choose_nan_64_idem: forall n,
  choose_nan_64 (n :: n :: nil) = choose_nan_64 (n :: nil).
Proof. auto. Qed.

Lemma choose_nan_32_idem: forall n,
  choose_nan_32 (n :: n :: nil) = choose_nan_32 (n :: nil).
Proof. auto. Qed.

Definition fma_order {A: Type} (x y z: A) := (x, y, z).

Definition fma_invalid_mul_is_nan := false.

Definition float_of_single_preserves_sNaN := false.

Global Opaque ptr64 big_endian splitlong
              default_nan_64 choose_nan_64
              default_nan_32 choose_nan_32
              fma_order fma_invalid_mul_is_nan
              float_of_single_preserves_sNaN.


(** SIMD support *)

Inductive vec_typ : Type :=
 | T128		(**r 128bit wide vectores *)
 | T256.        (**r 256bit wide vectores *)

Lemma vec_typ_eq: forall (t1 t2: vec_typ), {t1=t2} + {t1<>t2}.
Proof. decide equality. Defined.

(** Type rank of vector extensions *)
Definition vec_typ_rnk ty :=
 match ty with
 | T128 => 2
 | T256 => 3
 end.

(*
Inductive vec_chunk :=
 | M128		(**r 128bit wide memory chunk *)
 | M256.	(**r 256bit wide memory chunk *)

Definition vec_type_of_chunk (c:vec_chunk) : vec_typ :=
 match c with
 | M128 => T128
 | M256 => T256
 end.

Definition vec_chunk_of_type (ty:vec_typ) : vec_chunk :=
 match ty with
 | T128 => M128
 | T256 => M256
 end.
*)



(*
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
*)


