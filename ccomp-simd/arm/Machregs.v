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

Require Import OrderedType.
Require Import Ordered.
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Op.

Require Import Archi.

(** ** Machine registers *)

(** The following type defines the machine registers that can be referenced
  as locations.  These include:
- Integer registers that can be allocated to RTL pseudo-registers ([Rxx]).
- Floating-point registers that can be allocated to RTL pseudo-registers 
  ([Fxx]).

  The type [mreg] does not include reserved machine registers
  such as the stack pointer, the link register, and the condition codes. *)

Inductive mreg: Type :=
  (** Allocatable integer regs *)
  | R0: mreg  | R1: mreg  | R2: mreg  | R3: mreg
  | R4: mreg  | R5: mreg  | R6: mreg  | R7: mreg
  | R8: mreg  | R9: mreg  | R10: mreg | R11: mreg
  | R12: mreg
  (** Allocatable double-precision float regs *)
  | F0: mreg  | F1: mreg  | F2: mreg  | F3: mreg
  | F4: mreg  | F5: mreg  | F6: mreg  | F7: mreg
  | F8: mreg  | F9: mreg  | F10: mreg | F11: mreg
  | F12: mreg | F13: mreg | F14: mreg | F15: mreg
  | F16: mreg  | F17: mreg  | F18: mreg  | F19: mreg
  | F20: mreg  | F21: mreg  | F22: mreg  | F23: mreg
  | F24: mreg  | F25: mreg  | F26: mreg | F27: mreg
  | F28: mreg | F29: mreg | F30: mreg | F31: mreg
  (** Allocatable double-precision float regs *)
  | Q0: mreg  | Q1: mreg  | Q2: mreg  | Q3: mreg
  | Q4: mreg  | Q5: mreg  | Q6: mreg  | Q7: mreg
  | Q8: mreg  | Q9: mreg  | Q10: mreg | Q11: mreg
  | Q12: mreg | Q13: mreg | Q14: mreg | Q15: mreg.

Lemma mreg_eq: forall (r1 r2: mreg), {r1 = r2} + {r1 <> r2}.
Proof. decide equality. Defined.
Global Opaque mreg_eq.

Definition mreg_type (r: mreg): typ :=
  match r with
  | R0 => Tint  | R1 => Tint  | R2 => Tint  | R3 => Tint
  | R4 => Tint  | R5 => Tint  | R6 => Tint  | R7 => Tint
  | R8 => Tint  | R9 => Tint  | R10 => Tint | R11 => Tint
  | R12 => Tint
  | F0 | F1 | F2 | F3 | F4 | F5 | F6 | F7
  | F8 | F9 | F10 | F11 | F12 | F13 | F14 | F15
  | F16 | F17 | F18 | F19 | F20 | F21 | F22 | F23
  | F24 | F25 | F26 | F27 | F28 | F29 | F30 | F31 => Tfloat
  | Q0 | Q1 | Q2 | Q3 | Q4 | Q5 | Q6 | Q7
  | Q8 | Q9 | Q10 | Q11 | Q12 | Q13 | Q14 | Q15 => Tvec tt
  end.

Open Scope positive_scope.

(** [mreg_idx] assign a bit-mask to every register such that,
  if two registers overlap, their bitwise-and is not zero *)
Definition mreg_idx (r: mreg) : bool * positive :=
  match r with
  | R0 => (false,1)  |R1 => (false,2)  |R2 => (false,4)   | R3 => (false,8)
  | R4 => (false,16) |R5 => (false,32) |R6 => (false,64)  | R7 => (false,128)
  | R8 => (false,256)|R9 => (false,512)|R10 =>(false,1024)|R11 =>(false,2048)
  | R12 =>(false,4096)
  | F0 => (true, xH)
  | F1 => (true, xO xH)
  | F2 => (true, xO(xO xH))
  | F3 => (true, xO(xO(xO xH)))
  | F4 => (true, xO(xO(xO(xO xH))))
  | F5 => (true, xO(xO(xO(xO(xO xH)))))
  | F6 => (true, xO(xO(xO(xO(xO(xO xH))))))
  | F7 => (true, xO(xO(xO(xO(xO(xO(xO xH)))))))
  | F8 => (true, xO(xO(xO(xO(xO(xO(xO(xO xH))))))))
  | F9 => (true, xO(xO(xO(xO(xO(xO(xO(xO(xO xH)))))))))
  | F10 => (true,xO(xO(xO(xO(xO(xO(xO(xO(xO(xO xH))))))))))
  | F11 => (true,xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO xH)))))))))))
  | F12 => (true,xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO xH))))))))))))
  | F13 => (true,xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO xH)))))))))))))
  | F14 => (true,xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO xH))))))))))))))
  | F15 => (true,xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO xH)))))))))))))))
  | F16 => (true,xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO xH))))))))))))))))
  | F17 => (true,xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO xH)))))))))))))))))
  | F18 => (true,xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO xH))))))))))))))))))
  | F19 => (true,xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO xH)))))))))))))))))))
  | F20 => (true,xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO xH))))))))))))))))))))
  | F21 => (true,xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO xH)))))))))))))))))))))
  | F22 => (true,xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO xH))))))))))))))))))))))
  | F23 => (true,xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO xH)))))))))))))))))))))))
  | F24 => (true,xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO xH))))))))))))))))))))))))
  | F25 => (true,xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO xH)))))))))))))))))))))))))
  | F26 => (true,xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO xH))))))))))))))))))))))))))
  | F27 => (true,xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO xH)))))))))))))))))))))))))))
  | F28 => (true,xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO xH))))))))))))))))))))))))))))
  | F29 => (true,xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO xH)))))))))))))))))))))))))))))
  | F30 => (true,xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO xH))))))))))))))))))))))))))))))
  | F31 => (true,xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO xH)))))))))))))))))))))))))))))))
  | Q0 => (true, xI xH)
  | Q1 => (true, xO(xO(xI xH)))
  | Q2 => (true, xO(xO(xO(xO(xI xH)))))
  | Q3 => (true, xO(xO(xO(xO(xO(xO(xI xH)))))))
  | Q4 => (true, xO(xO(xO(xO(xO(xO(xO(xO(xI xH)))))))))
  | Q5 => (true,xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xI xH)))))))))))
  | Q6 => (true,xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xI xH)))))))))))))
  | Q7 => (true,xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xI xH)))))))))))))))
  | Q8 => (true,xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xI xH)))))))))))))))))
  | Q9 => (true,xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xI xH)))))))))))))))))))
  | Q10 => (true,xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xI xH)))))))))))))))))))))
  | Q11 => (true,xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xI xH)))))))))))))))))))))))
  | Q12 => (true,xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xI xH)))))))))))))))))))))))))
  | Q13 => (true,xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xI xH)))))))))))))))))))))))))))
  | Q14 => (true,xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xI xH)))))))))))))))))))))))))))))
  | Q15 => (true,xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xO(xI xH)))))))))))))))))))))))))))))))
  end.

Lemma mreg_idx_inj: forall r1 r2,
 mreg_idx r1 = mreg_idx r2 -> r1 = r2.
Proof.
destruct r1; destruct r2; intro H; inv H; auto.
Qed.

(** [andpos_nzero] returns [true] when the bitwise and of two positives is
  non-zero *)
Fixpoint andpos_nzero (p1 p2:positive) : bool :=
 match p1, p2 with
 | xH, xO _ => false
 | xH, _ => true
 | xO _, xH => false
 | _, xH => true
 | xO q1, xO q2 => andpos_nzero q1 q2
 | xO q1, xI q2 => andpos_nzero q1 q2
 | xI q1, xO q2 => andpos_nzero q1 q2
 | xI _, xI _ => true
 end.

(*
Lemma andpos_nzero_refl: forall p,
 andpos_nzero p p = true.
Proof. induction p; simpl; auto. Qed.

Lemma andpos_nzero_sym: forall p1 p2,
 andpos_nzero p1 p2 = andpos_nzero p2 p1.
Proof. induction p1; induction p2; simpl; auto. Qed.
*)

(** [mreg_overlap] checks if two registers are in conflict *)
Definition mreg_overlap (r1 r2: mreg) : bool :=
 match mreg_idx r1, mreg_idx r2 with
 | (b1,p1), (b2,p2) => andb (bool_eq b1 b2) (andpos_nzero p1 p2)
 end.

Definition mreg_diff_bool (r1 r2: mreg) : bool := negb (mreg_overlap r1 r2).

Lemma mreg_diff_bool_refl: forall r, mreg_diff_bool r r = false.
Proof. destruct r; vm_compute; reflexivity. Qed.

Lemma mreg_diff_bool_sym: forall r1 r2,
 mreg_diff_bool r1 r2 = mreg_diff_bool r2 r1.
Proof. destruct r1; destruct r2; vm_compute; reflexivity. Qed.

Definition mreg_diff r1 r2 := mreg_diff_bool r1 r2 = true.

Lemma mreg_diff_refl: forall r, ~mreg_diff r r.
Proof.
intros; unfold mreg_diff; rewrite mreg_diff_bool_refl; auto.
Qed.

Lemma mreg_diff_sym: forall r1 r2,
 mreg_diff r1 r2 -> mreg_diff r2 r1.
Proof.
intros; unfold mreg_diff; rewrite mreg_diff_bool_sym; auto.
Qed.

Definition mreg_diff_dec: forall r1 r2,
 {mreg_diff r1 r2}+{~mreg_diff r1 r2}.
Proof.
intros; case_eq (mreg_diff_bool r1 r2); intro H.
 left; apply H.
right; unfold mreg_diff; intros E; rewrite H in E; discriminate E.
Defined.

Module OrderedMreg <: OrderedType.
  Definition t := mreg.
  Definition eq (x y: t) := x = y.
  Definition lt (x y: t) :=
    match mreg_idx x, mreg_idx y with
    | (false,_), (true,_) => True
    | (true,_), (false,_) => False
    | (_,p1), (_,p2) => Plt p1 p2
    end.
  Lemma eq_refl : forall x : t, eq x x.
  Proof (@refl_equal t). 
  Lemma eq_sym : forall x y : t, eq x y -> eq y x.
  Proof (@sym_equal t).
  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof (@trans_equal t).
  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt; intros x y z. 
    case (mreg_idx x); intros b1 p1.
    case (mreg_idx y); intros b2 p2.
    case (mreg_idx z); intros b3 p3.
    case b1; case b2; case b3; try tauto.
     apply Plt_trans.
    apply Plt_trans.
  Qed.
  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    unfold lt, eq; intros; red; intros. subst y. 
    generalize H; clear H; case (mreg_idx x); intros b p.
    case b; apply Plt_strict.
  Qed.
  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    intros.
    case_eq (mreg_idx x); intros b1 p1 Hx.
    case_eq (mreg_idx y); intros b2 p2 Hy.
    destruct b1; destruct b2.
    - destruct (OrderedPositive.compare p1 p2).
     + apply LT; red.
       rewrite Hx, Hy; auto.
     + apply EQ; red.
       apply mreg_idx_inj; rewrite Hx, Hy; f_equal; auto.
     + apply GT; red.
       rewrite Hx, Hy; auto.
    - apply GT; red.
       rewrite Hx, Hy; auto.
    - apply LT; red.
       rewrite Hx, Hy; auto.
    - destruct (OrderedPositive.compare p1 p2).
     + apply LT; red.
       rewrite Hx, Hy; auto.
     + apply EQ; red.
       apply mreg_idx_inj; rewrite Hx, Hy; f_equal; auto.
     + apply GT; red.
       rewrite Hx, Hy; auto.
  Defined.
  Definition eq_dec := mreg_eq.

(** Connection between the ordering and the [mreg_diff] predicate.  *)

Definition mreg_high_bound (r:mreg) : mreg :=
 match r with
 | F0  | F1  => Q0
 | F2  | F3  => Q1
 | F4  | F5  => Q2
 | F6  | F7  => Q3
 | F8  | F9  => Q4
 | F10 | F11 => Q5
 | F12 | F13 => Q6
 | F14 | F15 => Q7
 | F16 | F17 => Q8
 | F18 | F19 => Q9
 | F20 | F21 => Q10
 | F22 | F23 => Q11
 | F24 | F25 => Q12
 | F26 | F27 => Q13
 | F28 | F29 => Q14
 | F30 | F31 => Q15
 | _ => r
 end.

Definition mreg_low_bound (r:mreg) : mreg :=
 match r with
 | Q0  => F0
 | Q1  => F2
 | Q2  => F4
 | Q3  => F6
 | Q4  => F8
 | Q5  => F10
 | Q6  => F12
 | Q7  => F14
 | Q8  => F16
 | Q9  => F18
 | Q10 => F20
 | Q11 => F22
 | Q12 => F24
 | Q13 => F26
 | Q14 => F28
 | Q15 => F30
 | _ => r
 end.

Lemma outside_interval_mreg: forall r r',
 lt r' (mreg_low_bound r) \/ lt (mreg_high_bound r) r' 
 -> mreg_diff r r'.
Proof.
unfold mreg_diff.
destruct r; destruct r'; vm_compute; intros [H|H]; inv H; auto.
Qed.
End OrderedMreg.

(*
Module IndexedMreg <: INDEXED_TYPE.
  Definition t := mreg.
  Definition eq := mreg_eq.
  Definition index (r: mreg): positive :=
    match r with
    | R0 => 1  | R1 => 2  | R2 => 3  | R3 => 4
    | R4 => 5  | R5 => 6  | R6 => 7  | R7 => 8
    | R8 => 9  | R9 => 10 | R10 => 11 | R11 => 12
    | R12 => 13
    | F0 => 14 | F1 => 15 | F2 => 16  | F3 => 17
    | F4 => 18 | F5 => 19 | F6 => 20  | F7 => 21
    | F8 => 22 | F9 => 23 | F10 => 24 | F11 => 25
    | F12 => 26 | F13 => 27 | F14 => 28 | F15 => 29
    end.
  Lemma index_inj:
    forall r1 r2, index r1 = index r2 -> r1 = r2.
  Proof.
    destruct r1; destruct r2; simpl; intro; discriminate || reflexivity.
  Qed.
End IndexedMreg.
*)

Definition is_stack_reg (r: mreg) : bool := false.

(** ** Destroyed registers, preferred registers *)

Definition destroyed_by_op (op: operation): list mreg :=
  match op with
  | Odiv | Odivu => R0 :: R1 :: R2 :: R3 :: R12 :: nil
  | Ointoffloat | Ointuoffloat => F6 :: nil
  | _ => nil
  end.

Definition destroyed_by_load (chunk: memory_chunk) (addr: addressing): list mreg :=
  nil.

Definition destroyed_by_store (chunk: memory_chunk) (addr: addressing): list mreg :=
  match chunk with
  | Mfloat32 => F6 :: nil
  | _ => nil
  end.

Definition destroyed_by_cond (cond: condition): list mreg :=
  nil.

Definition destroyed_by_jumptable: list mreg :=
  nil.

Definition destroyed_by_builtin (ef: external_function): list mreg :=
  match ef with
  | EF_memcpy sz al => if zle sz 32 then nil else R2 :: R3 :: R12 :: nil
  | EF_vload Mfloat32 => F6 :: nil
  | EF_vload_global Mfloat32 _ _ => F6 :: nil
  | EF_vstore Mfloat32 => F6 :: nil
  | EF_vstore_global Mfloat32 _ _ => F6 :: nil
  | _ => nil
  end.

Definition destroyed_by_setstack (ty: typ): list mreg :=
  match ty with
  | Tsingle => F6 :: nil
  | _ => nil
  end.

Definition destroyed_at_function_entry: list mreg :=
  R12 :: nil.

Definition temp_for_parent_frame: mreg :=
  R12.

Definition mregs_for_operation (op: operation): list (option mreg) * option mreg :=
  match op with
  | Odiv | Odivu => (Some R0 :: Some R1 :: nil, Some R0)
  | Ofloatofint | Ofloatofintu => (None :: nil, Some F6)
  | _ => (nil, None)
  end.

Definition mregs_for_builtin (ef: external_function): list (option mreg) * list(option mreg) :=
  match ef with
  | EF_memcpy sz al =>
      if zle sz 32 then (nil, nil) else (Some R3 :: Some R2 :: nil, nil)
  | _ => (nil, nil)
  end.

Global Opaque
    destroyed_by_op destroyed_by_load destroyed_by_store
    destroyed_by_cond destroyed_by_jumptable destroyed_by_builtin
    destroyed_by_setstack destroyed_at_function_entry temp_for_parent_frame
    mregs_for_operation mregs_for_builtin.

(** Two-address operations.  Return [true] if the first argument and
  the result must be in the same location *and* are unconstrained
  by [mregs_for_operation].  There are none for ARM. *)

Definition two_address_op (op: operation) : bool :=
  false.

Global Opaque two_address_op.

