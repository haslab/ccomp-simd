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

Definition vec_align (t:vec_typ) : Z := typesize (Tvec t).

Lemma vec_align_pos: forall t, vec_align t > 0.
Proof. intro t; exact (typesize_pos (Tvec t)). Qed.

Lemma vec_align_divides_typesize: forall t, 
  (vec_align t | typesize (Tvec t)).
Proof.
intro t; unfold vec_align; exists 1; omega.
Qed.

Lemma vec_align_8divides t: (8 | vec_align t).
Proof.
destruct t; unfold vec_align, typesize, typelocsize, typerank,
vec_typ_rnk; simpl.
- exists 2; omega.
- exists 4; omega.
Qed.

Lemma vec_align_le_divides t1 t2:
 vec_align t1 <= vec_align t2 -> (vec_align t1 | vec_align t2).
Proof.
destruct t1; destruct t2; unfold vec_align, typesize, typelocsize,
typerank, vec_typ_rnk; simpl; intros.
- exists 1; omega.
- exists 2; omega.
- contradiction.
- exists 1; omega.
Qed.

(*
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


