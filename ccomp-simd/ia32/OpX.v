Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Ctypes.

Set Implicit Arguments.

(* SHALL WE NEED COMPARISONS??? *)

Inductive operationX : Type :=
 | OXzero: operationX           (**r [rd = 0] (integer) *)
 | OXone: operationX            (**r [rd = 1] (integer) *)
(*
 (* logical operations *)
 | OXIxor: operationX		(**r [rd = r1 ^ r2] (integer) *)
 | OXFxor: operationX		(**r [rd = r1 ^ r2] (float) *)
 | OXIand: operationX		(**r [rd = r1 & r2] (integer) *)
 | OXFand: operationX		(**r [rd = r1 & r2] (integer) *)
 | OXIandnot: operationX	(**r [rd = r1 & r2] (integer) *)
 | OXFandnot: operationX	(**r [rd = r1 & r2] (integer) *)
 | OXIor: operationX		(**r [rd = r1 & r2] (integer) *)
 | OFor: operationX		(**r [rd = r1 & r2] (integer) *)
 (** arithmetic operations *)
 (* additions *)
 | OXI16add: operationX		(**r [rd = r1 + r2] (int8) *)
 | OXI8add: operationX		(**r [rd = r1 + r2] (int16) *)
 | OXI4add: operationX		(**r [rd = r1 + r2] (int32) *)
 | OXI2add: operationX		(**r [rd = r1 + r2] (int64) *)
 | OXF4add1: operationX		(**r [rd = r1 + r2] (1st Fsingle) *)
 | OXF4add: operationX		(**r [rd = r1 + r2] (Fsingle) *)
 (* saturated additions ??? *)

 | OXI16adds: operationX	(**r [rd = r1 + r2] (int8) *)
 | OXI8adds: operationX		(**r [rd = r1 + r2] (int16) *)
 | OXI4adds: operationX		(**r [rd = r1 + r2] (int32) *)
 | OXI2adds: operationX		(**r [rd = r1 + r2] (int64) *)
 (* *)
 | O16Fands: operationX		(**r [rd = r1 & r2] (integer) *)

obs: this list never ends --- should it be generated?
*)
.

Definition eq_operationX (x y: operationX): {x=y} + {x<>y}.
Proof.
decide equality.
Defined. 

Definition eval_xor128 (v1 v2:val) : option val :=
 match v1, v2 with
 | V128 x, V128 y => Some (V128 (Int128.xor x y))
 | _, _ => None
 end.

Definition eval_operationX
    (F V: Type) (genv: Genv.t F V) (sp: val)
    (op: operationX) (vl: list val) (m: mem): option val :=
  match op, vl with
  | OXzero, nil => Some (V128 (Int128.zero))
  | OXone, nil => Some (V128 (Int128.one))
(*
  | (OXIxor|OXFxor), v1::v2::nil => eval_xor128 v1 v2
  | (OXIand|OXFand), v1::v2::nil => eval_and128 v1 v2
  | (OXIandnot|OXFandnot), v1::v2::nil => eval_andnot128 v1 v2
  | (OXIor|OXFor) v1::v2::nil => eval_or128 v1 v2
*)
  | _, _ => None
  end.

Definition tvec := Tvecdata.

Definition ctype_of_operationX (op:operationX) : typelist*type :=
  match op with 
  | OXzero => (Tnil, tvec)
  | OXone => (Tnil, tvec)
(*
  | (OXIxor|OXFxor(*|OXIand|OXFand|OXIandnot|OXFandnot*)) =>
     (Tcons tvec (Tcons tvec Tnil), tvec)
*)
  end.

Definition type_of_operationX (op: operationX) : list typ * typ :=
  (typlist_of_typelist (fst (ctype_of_operationX op)),
   typ_of_type (snd (ctype_of_operationX op))).

Definition two_address_opX (op: operationX) : bool := 
 match op with
(* | OXIxor | OXFxor => true *)
 | _ => false
 end.

Lemma type_of_operationX_sound:
  forall F V (genv:Genv.t F V) op vl sp v m,
  eval_operationX genv sp op vl m = Some v ->
  Val.has_type v (snd (type_of_operationX op)).
Proof.
intros F V penv op vl x y m.
destruct op;
repeat (destruct vl; simpl; intros; try discriminate H);
inversion_clear H; constructor.
Qed.

Definition opX_depends_on_memory (op: operationX) : bool :=
  match op with
  | _ => false
  end.

Lemma opX_depends_on_memory_correct:
  forall (F V: Type) (ge: Genv.t F V) sp op args m1 m2,
  opX_depends_on_memory op = false ->
  eval_operationX ge sp op args m1 = eval_operationX ge sp op args m2.
Proof.
  intros until m2. destruct op; simpl; try congruence.
Qed.

Lemma eval_operationX_inj:
  forall F V (genv:Genv.t F V) (m1 m2:mem) (f:meminj) op sp1 vl1 sp2 vl2 v1,
  val_inject f sp1 sp2 ->
  val_list_inject f vl1 vl2 ->
  eval_operationX genv sp1 op vl1 m1 = Some v1 ->
  exists v2, eval_operationX genv sp2 op vl2 m2 = Some v2 /\ val_inject f v1 v2.
Proof.
intros F V genv m1 m2 f o _sp1 vl1 _sp2 vl2 v Hinj Hinjl.
destruct o; destruct vl1; simpl; intro H; simplify_eq H; clear H; intro E;
rewrite E; exists v; subst; destruct vl2; auto;
inversion Hinjl.
Qed.

Lemma eval_operationX_lessdef:
  forall F V (genv:Genv.t F V) (m1 m2:mem) (f:meminj) sp op vl1 vl2 v1 m1 m2,
  Val.lessdef_list vl1 vl2 ->
  Mem.extends m1 m2 ->
  eval_operationX genv sp op vl1 m1 = Some v1 ->
  exists v2, eval_operationX genv sp op vl2 m2 = Some v2 /\ Val.lessdef v1 v2.
Proof.
intros F V genv _m1 _m2 minj sp op vl1 vl2 v1 m1 m2 Hless Hext.
destruct op; simpl; destruct vl1; intro H; simplify_eq H; clear H; intro E;
rewrite E; exists v1; subst; destruct vl2; auto;
inversion_clear Hless.
Qed.
