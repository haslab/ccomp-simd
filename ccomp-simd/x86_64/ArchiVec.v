(** Architecture-dependent parameters for x86 in 64-bit mode *)

Require Import ZArith List.

Open Scope Z_scope.

Require Import Archi Integers AST.

Definition vec_typ_sem (t:vec_typ) : Type :=
 match t with
 | T128 => Int128.int
 | T256 => Int256.int
 end.

Definition vec_intval {t}: vec_typ_sem t -> Z :=
 match t with
 | T128 => Int128.unsigned
 | T256 => Int256.unsigned
 end.

Definition vec_repr {t}: Z -> vec_typ_sem t :=
 match t with
 | T128 => Int128.repr
 | T256 => Int256.repr
 end.

Lemma vec_eq (ty: vec_typ): forall (x y: vec_typ_sem ty), {x=y} + {x<>y}.
Proof.
destruct ty; unfold vec_typ_sem; intros.
- apply Int128.eq_dec.
- apply Int256.eq_dec.
Qed.

(*
Definition vec_typ_align (t:vec_typ) : Z := 4 * two_power_nat (vec_typ_rnk t).

Lemma vec_align_chunk_pos: forall t, vec_typ_align t > 0.
Proof. destruct t; unfold vec_typ_align; omega. Qed.

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


