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

Require Import String.
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import OpX Op.

(** ** Machine registers *)

(** The following type defines the machine registers that can be referenced
  as locations.  These include:
- Integer registers that can be allocated to RTL pseudo-registers.
- Floating-point registers that can be allocated to RTL pseudo-registers.
- SSE registers that can be allocated to RTL pseudo-registers.
- The special [FP0] register denoting the top of the X87 float stack.

  The type [mreg] does not include special-purpose or reserved
  machine registers such as the stack pointer and the condition codes. *)

Inductive mreg: Type :=
  (** Allocatable integer regs *)
  | AX: mreg | BX: mreg | CX: mreg | DX: mreg | SI: mreg | DI: mreg | BP: mreg
  (** Allocatable float regs *)
  | X0: mreg | X1: mreg | X2: mreg | X3: mreg 
  | X4: mreg | X5: mreg | X6: mreg | X7: mreg
  (** Allocatable SSE regs *)
  | Y0: mreg | Y1: mreg | Y2: mreg | Y3: mreg 
  | Y4: mreg | Y5: mreg | Y6: mreg | Y7: mreg
  (** Special float reg *)
  | FP0: mreg (**r top of x87 FP stack *).

(** Leibniz equality *)
Lemma mreg_eq: forall (r1 r2: mreg), {r1 = r2} + {r1 <> r2}.
Proof. decide equality. Defined.
Global Opaque mreg_eq.

Definition mreg_type (r: mreg): typ :=
  match r with
  | AX => Tint | BX => Tint | CX => Tint | DX => Tint
  | SI => Tint | DI => Tint | BP => Tint
  | X0 => Tfloat | X1 => Tfloat | X2 => Tfloat | X3 => Tfloat
  | X4 => Tfloat | X5 => Tfloat | X6 => Tfloat | X7 => Tfloat
  | Y0 => T128 | Y1 => T128 | Y2 => T128 | Y3 => T128
  | Y4 => T128 | Y5 => T128 | Y6 => T128 | Y7 => T128
  | FP0 => Tfloat
  end.

(** We allow machine registers to overlap (e.g. ia32 SSE registers
  are modeled as X0..7 when used as floating-point registers,
  and Y0..7 as proper SSE registers). These two classes of registers
  are identified by the operation [mreg_eqnorm]. *)
Definition mreg_eqnorm (r: mreg) : mreg :=
  match r with
  | Y0 => X0 | Y1 => X1 | Y2 => X2 | Y3 => X3
  | Y4 => X4 | Y5 => X5 | Y6 => X6 | Y7 => X7
  | other => other
  end.

(** Semantic equality *)
Definition mreg_seq r1 r2 := mreg_eqnorm r1 = mreg_eqnorm r2.

Lemma mreg_seq_dec: forall r1 r2,
  {mreg_seq r1 r2}+{~mreg_seq r1 r2}.
Proof.
intros; destruct r1; destruct r2; apply mreg_eq.
Qed.

Local Open Scope positive_scope.


(** Indexes are assigned in a way that reseting the least significant bit
  lead to the index of the [mreg_eqnorm]. *)
Module IndexedMreg <: INDEXED_TYPE.
  Definition t := mreg.
  Definition eq := mreg_eq.
  Definition index (r: mreg): positive :=
    match r with
    | AX => 2 | BX => 4 | CX => 6 | DX => 8 | SI => 10 | DI => 12 | BP => 14
    | X0 => 16 | X1 => 18 | X2 => 20 | X3 => 22
    | X4 => 24 | X5 => 26 | X6 => 28 | X7 => 30
    | Y0 => 17 | Y1 => 19 | Y2 => 21 | Y3 => 23
    | Y4 => 25 | Y5 => 27 | Y6 => 29 | Y7 => 31
    | FP0 => 32
    end.
  Lemma index_inj:
    forall r1 r2, index r1 = index r2 -> r1 = r2.
  Proof.
    destruct r1; destruct r2; simpl; intro; discriminate || reflexivity.
  Qed.

  Definition inv_index (p:positive) : mreg :=
    (match p with
     | 2 => AX | 4 => BX | 6 => CX | 8 => DX | 10 => SI | 12 => DI | 14 => BP
     | 16 => X0 | 18 => X1 | 20 => X2 | 22 => X3
     | 24 => X4 | 26 => X5 | 28 => X6 | 30 => X7
     | 17 => Y0 | 19 => Y1 | 21 => Y2 | 23 => Y3
     | 25 => Y4 | 27 => Y5 | 29 => Y6 | 31 => Y7
     | _ => FP0
     end)%positive.

  Lemma inv_index_spec: forall r,
   inv_index (index r) = r.
  Proof. intro r; destruct r; auto. Qed.

  (** characterisation of [mreg_seq] through [index] computations *) 
  Lemma index_seq: forall r1 r2,
   Pdiv2 (index r1) = Pdiv2 (index r2)  <-> mreg_seq r1 r2.
  Proof.
  unfold mreg_seq; split.
   intros; destruct r1; destruct r2; simpl in *; try inv H; auto.
  intros; destruct r1; destruct r2; inv H; auto.
  Qed.

  Lemma index_low_check: forall r,
   ~Plt (index r) (index (inv_index (Pos.div2 (index r))~0)).
  Proof. intros r H; destruct r; inv H. Qed.

  Lemma index_high_check: forall r,
   ~Plt (index (inv_index (Pos.div2 (index r))~1)) (index r).
  Proof. intros r H; destruct r; inv H. Qed.

End IndexedMreg.

Definition is_stack_reg (r: mreg) : bool :=
  match r with FP0 => true | _ => false end.

(** ** Destroyed registers, preferred registers *)

Definition destroyed_by_op (op: operation): list mreg :=
  match op with
  | Omove => FP0 :: nil
  | Ocast8signed | Ocast8unsigned | Ocast16signed | Ocast16unsigned => AX :: nil
  | Omulhs => AX :: DX :: nil
  | Omulhu => AX :: DX :: nil
  | Odiv => AX :: DX :: nil
  | Odivu => AX :: DX :: nil
  | Omod => AX :: DX :: nil
  | Omodu => AX :: DX :: nil
  | Oshrximm _ => CX :: nil
  | Ocmp _ => AX :: CX :: nil
  | _ => nil
  end.

Definition destroyed_by_load (chunk: memory_chunk) (addr: addressing): list mreg :=
  nil.

Definition destroyed_by_store (chunk: memory_chunk) (addr: addressing): list mreg :=
  match chunk with
  | Mint8signed | Mint8unsigned => AX :: CX :: nil
  | Mint16signed | Mint16unsigned | Mint32 | Mint64 | Mint128 => nil
  | Mfloat32 => X7 :: nil
  | Mfloat64 => FP0 :: nil
  end.

Definition destroyed_by_cond (cond: condition): list mreg :=
  nil.

Definition destroyed_by_jumptable: list mreg :=
  nil.

Local Open Scope string_scope.

Definition builtin_write16_reversed := ident_of_string "__builtin_write16_reversed".
Definition builtin_write32_reversed := ident_of_string "__builtin_write32_reversed".
Definition builtin_rdtsc := ident_of_string "__builtin_rdtsc".
Definition builtin_maskmovdqu := ident_of_string "__builtin_ia32_maskmovdqu".
Definition builtin_vec_ext_v2di := ident_of_string "__builtin_ia32_vec_ext_v2di".
Definition builtin_vec_set_v2di := ident_of_string "__builtin_ia32_vec_set_v2di".

Definition destroyed_by_builtin (ef: external_function): list mreg :=
  match ef with
  | EF_memcpy sz al =>
      if zle sz 32 then CX :: X7 :: nil else CX :: SI :: DI :: nil
  | EF_vstore (Mint8unsigned|Mint8signed) => AX :: CX :: nil
  | EF_vstore Mfloat32 => X7 :: nil
  | EF_vstore_global (Mint8unsigned|Mint8signed) _ _ => AX :: nil
  | EF_vstore_global Mfloat32 _ _ => X7 :: nil
  | EF_builtin id imms sg =>
      if ident_eq id builtin_write16_reversed
      || ident_eq id builtin_write32_reversed
      then CX :: DX :: nil
      else if ident_eq id builtin_rdtsc then BX :: CX :: nil else nil
  | _ => nil
  end.

Definition destroyed_at_function_entry: list mreg :=
  DX :: FP0 :: nil.   (* must include destroyed_by_op Omove *)

Definition destroyed_by_setstack (ty: typ): list mreg :=
  match ty with
  | Tfloat => FP0 :: nil
  | Tsingle => X7 :: nil
  | _ => nil
  end.

Definition temp_for_parent_frame: mreg :=
  DX.

Definition mregs_for_operationX (op: operationX): list (option mreg) * option mreg :=
  match op with
  | _ => (nil, None)
  end.

Definition mregs_for_operation (op: operation): list (option mreg) * option mreg :=
  match op with
  | Omulhs => (Some AX :: None :: nil, Some DX)
  | Omulhu => (Some AX :: None :: nil, Some DX)
  | Odiv => (Some AX :: Some CX :: nil, Some AX)
  | Odivu => (Some AX :: Some CX :: nil, Some AX)
  | Omod => (Some AX :: Some CX :: nil, Some DX)
  | Omodu => (Some AX :: Some CX :: nil, Some DX)
  | Oshl => (None :: Some CX :: nil, None)
  | Oshr => (None :: Some CX :: nil, None)
  | Oshru => (None :: Some CX :: nil, None)
  | Oshrximm _ => (Some AX :: nil, Some AX)
  | OX op => mregs_for_operationX op
  | _ => (nil, None)
  end.

Definition builtin_negl := ident_of_string "__builtin_negl".
Definition builtin_addl := ident_of_string "__builtin_addl".
Definition builtin_subl := ident_of_string "__builtin_subl".
Definition builtin_mull := ident_of_string "__builtin_mull".

Definition builtin_bswap64 := ident_of_string "__builtin_bswap64".

(** NOTE : register allocation restriction on sha256rnds2 and pblendvb128 instructions **)
Definition builtin_ia32_sha256rnds2 := ident_of_string "__builtin_ia32_sha256rnds2".
Definition builtin_ia32_pblendvb128 := ident_of_string "__builtin_ia32_pblendvb128".

Definition mregs_for_builtin (ef: external_function): list (option mreg) * list (option mreg) :=
  match ef with
  | EF_memcpy sz al =>
     if zle sz 32 then (Some AX :: Some DX :: nil, nil) else (Some DI :: Some SI :: nil, nil)
  | EF_builtin id imms sg =>
     if ident_eq id builtin_negl then
       (Some DX :: Some AX :: nil, Some DX :: Some AX :: nil)
     else if ident_eq id builtin_addl || ident_eq id builtin_subl then
       (Some DX :: Some AX :: Some CX :: Some BX :: nil, Some DX :: Some AX :: nil)
     else if ident_eq id builtin_mull then
       (Some AX :: Some DX :: nil, Some DX :: Some AX :: nil)
     else if ident_eq id builtin_bswap64 then
       (Some AX :: Some DX :: nil, Some DX :: Some AX :: nil)
     else if ident_eq id builtin_rdtsc then
       (nil, Some DX :: Some AX :: nil)
     else if ident_eq id builtin_maskmovdqu then
       (nil, None :: None :: Some DI :: nil)
     else if ident_eq id builtin_vec_set_v2di then
       (Some DX :: Some AX :: nil, None :: nil)
     else if ident_eq id builtin_vec_ext_v2di then
       (None:: nil, Some DX :: Some AX :: nil)

     (** NOTE : register allocation restriction on sha256rnds2 and pblendvb128 instructions **)
     else if ident_eq id builtin_ia32_sha256rnds2 then
       (None:: None:: Some Y0:: nil, nil)
     else if ident_eq id builtin_ia32_pblendvb128 then
       (None:: None:: Some Y0:: nil, nil)

     else
       (nil, nil)
  | _ => (nil, nil)
  end.

Global Opaque
    destroyed_by_op destroyed_by_load destroyed_by_store
    destroyed_by_cond destroyed_by_jumptable destroyed_by_builtin
    destroyed_by_setstack destroyed_at_function_entry temp_for_parent_frame
    mregs_for_operation mregs_for_builtin.

(** Two-address operations.  Return [true] if the first argument and
  the result must be in the same location *and* are unconstrained
  by [mregs_for_operation]. *)

Definition two_address_op (op: operation) : bool :=
  match op with
  | Omove => false
  | Ointconst _ => false
  | Ofloatconst _ => false
  | Oindirectsymbol _ => false
  | Ocast8signed => false
  | Ocast8unsigned => false
  | Ocast16signed => false
  | Ocast16unsigned => false
  | Oneg => true
  | Osub => true
  | Omul => true
  | Omulimm _ => true
  | Omulhs => false
  | Omulhu => false
  | Odiv => false
  | Odivu => false
  | Omod => false
  | Omodu => false
  | Oand => true
  | Oandimm _ => true
  | Oor => true
  | Oorimm _ => true
  | Oxor => true
  | Oxorimm _ => true
  | Oshl => true
  | Oshlimm _ => true
  | Oshr => true
  | Oshrimm _ => true
  | Oshrximm _ => false
  | Oshru => true
  | Oshruimm _ => true
  | Ororimm _ => true
  | Oshldimm _ => true
  | Olea addr => false
  | Onegf => true
  | Oabsf => true
  | Oaddf => true
  | Osubf => true
  | Omulf => true
  | Odivf => true
  | Osingleoffloat => false
  | Ointoffloat => false
  | Ofloatofint => false
  | Omakelong => false
  | Olowlong => false
  | Ohighlong => false
  | Ocmp c => false
  | OX op => two_address_opX op
  end.

