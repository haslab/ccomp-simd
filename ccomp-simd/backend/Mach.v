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

(** The Mach intermediate language: abstract syntax.

  Mach is the last intermediate language before generation of assembly
  code.  
*)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Import Conventions.
Require Stacklayout.

(** * Abstract syntax *)

(** Like Linear, the Mach language is organized as lists of instructions
  operating over machine registers, with default fall-through behaviour
  and explicit labels and branch instructions.  

  The main difference with Linear lies in the instructions used to
  access the activation record.  Mach has three such instructions:
  [Mgetstack] and [Msetstack] to read and write within the activation
  record for the current function, at a given word offset and with a
  given type; and [Mgetparam], to read within the activation record of
  the caller. 

  These instructions implement a more concrete view of the activation
  record than the the [Lgetstack] and [Lsetstack] instructions of
  Linear: actual offsets are used instead of abstract stack slots, and the
  distinction between the caller's frame and the callee's frame is
  made explicit. *)

Definition label := positive.

Inductive instruction: Type :=
  | Mgetstack: int -> typ -> mreg -> instruction
  | Msetstack: mreg -> int -> typ -> instruction
  | Mgetparam: int -> typ -> mreg -> instruction
  | Mop: operation -> list mreg -> mreg -> instruction
  | Mload: memory_chunk -> addressing -> list mreg -> mreg -> instruction
  | Mstore: memory_chunk -> addressing -> list mreg -> mreg -> instruction
  | Mcall: signature -> mreg + ident -> instruction
  | Mtailcall: signature -> mreg + ident -> instruction
  | Mbuiltin: external_function -> list mreg -> list mreg -> instruction
  | Mannot: external_function -> list annot_param -> instruction
  | Mlabel: label -> instruction
  | Mgoto: label -> instruction
  | Mcond: condition -> list mreg -> label -> instruction
  | Mjumptable: mreg -> list label -> instruction
  | Mreturn: instruction

with annot_param: Type :=
  | APreg: mreg -> annot_param
  | APstack: memory_chunk -> Z -> annot_param.

Definition code := list instruction.

Record function: Type := mkfunction
  { fn_sig: signature;
    fn_code: code;
    fn_stacksize: Z;
    fn_link_ofs: int;
    fn_retaddr_ofs: int }.

Definition fundef := AST.fundef function.

Definition program := AST.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => fn_sig f
  | External ef => ef_sig ef
  end.

Definition genv := Genv.t fundef unit.

(** * Operational semantics *)

(** The semantics for Mach is close to that of [Linear]: they differ only
  on the interpretation of stack slot accesses.  In Mach, these
  accesses are interpreted as memory accesses relative to the
  stack pointer.  More precisely:
- [Mgetstack ofs ty r] is a memory load at offset [ofs * 4] relative
  to the stack pointer.
- [Msetstack r ofs ty] is a memory store at offset [ofs * 4] relative
  to the stack pointer.
- [Mgetparam ofs ty r] is a memory load at offset [ofs * 4]
  relative to the pointer found at offset 0 from the stack pointer.
  The semantics maintain a linked structure of activation records,
  with the current record containing a pointer to the record of the
  caller function at offset 0.

In addition to this linking of activation records, the
semantics also make provisions for storing a back link at offset
[f.(fn_link_ofs)] from the stack pointer, and a return address at
offset [f.(fn_retaddr_ofs)].  The latter stack location will be used
by the Asm code generated by [Asmgen] to save the return address into
the caller at the beginning of a function, then restore it and jump to
it at the end of a function.  The Mach concrete semantics does not
attach any particular meaning to the pointer stored in this reserved
location, but makes sure that it is preserved during execution of a
function.  The [return_address_offset] parameter is used to guess the
value of the return address that the Asm code generated later will
store in the reserved location.
*)

Definition load_stack (m: mem) (sp: val) (ty: typ) (ofs: int) :=
  Mem.loadv (chunk_of_type ty) m (Val.add sp (Vint ofs)).

Definition store_stack (m: mem) (sp: val) (ty: typ) (ofs: int) (v: val) :=
  Mem.storev (chunk_of_type ty) m (Val.add sp (Vint ofs)) v.

Module RegEq.
  Definition t := mreg.
  Definition eq := mreg_eq.
End RegEq.

Module Regmap := EMap(RegEq).

Definition regset := Regmap.t val.

Notation "a ## b" := (List.map a b) (at level 1).
Notation "a # b <- c" := (Regmap.set b c a) (at level 1, b at next level).

Fixpoint undef_regs (rl: list mreg) (rs: regset) {struct rl} : regset :=
  match rl with
  | nil => rs
  | r1 :: rl' => Regmap.set r1 Vundef (undef_regs rl' rs)
  end.

Lemma undef_regs_other:
  forall r rl rs, ~In r rl -> undef_regs rl rs r = rs r.
Proof.
  induction rl; simpl; intros. auto. rewrite Regmap.gso. apply IHrl. intuition. intuition.
Qed.

Lemma undef_regs_same:
  forall r rl rs, In r rl -> undef_regs rl rs r = Vundef.
Proof.
  induction rl; simpl; intros. tauto.
  destruct H. subst a. apply Regmap.gss.
  unfold Regmap.set. destruct (RegEq.eq r a); auto. 
Qed.

Fixpoint set_regs (rl: list mreg) (vl: list val) (rs: regset) : regset :=
  match rl, vl with
  | r1 :: rl', v1 :: vl' => set_regs rl' vl' (Regmap.set r1 v1 rs)
  | _, _ => rs
  end.

Definition is_label (lbl: label) (instr: instruction) : bool :=
  match instr with
  | Mlabel lbl' => if peq lbl lbl' then true else false
  | _ => false
  end.

Lemma is_label_correct:
  forall lbl instr,
  if is_label lbl instr then instr = Mlabel lbl else instr <> Mlabel lbl.
Proof.
  intros.  destruct instr; simpl; try discriminate.
  case (peq lbl l); intro; congruence.
Qed.

Fixpoint find_label (lbl: label) (c: code) {struct c} : option code :=
  match c with
  | nil => None
  | i1 :: il => if is_label lbl i1 then Some il else find_label lbl il
  end.

Lemma find_label_incl:
  forall lbl c c', find_label lbl c = Some c' -> incl c' c.
Proof.
  induction c; simpl; intros. discriminate.
  destruct (is_label lbl a). inv H. auto with coqlib. eauto with coqlib. 
Qed.

Section RELSEM.

Variable return_address_offset: function -> code -> int -> Prop.

Variable ge: genv.

Definition find_function_ptr
        (ge: genv) (ros: mreg + ident) (rs: regset) : option block :=
  match ros with
  | inl r =>
      match rs r with
      | Vptr b ofs => if Int.eq ofs Int.zero then Some b else None
      | _ => None
      end
  | inr symb =>
      Genv.find_symbol ge symb
  end.

(** Extract the values of the arguments to an external call. *)

Inductive extcall_arg: regset -> mem -> val -> loc -> val -> Prop :=
  | extcall_arg_reg: forall rs m sp r,
      extcall_arg rs m sp (R r) (rs r)
  | extcall_arg_stack: forall rs m sp ofs ty v,
      load_stack m sp ty (Int.repr (Stacklayout.fe_ofs_arg + 4 * ofs)) = Some v ->
      extcall_arg rs m sp (S Outgoing ofs ty) v.

Definition extcall_arguments
    (rs: regset) (m: mem) (sp: val) (sg: signature) (args: list val) : Prop :=
  list_forall2 (extcall_arg rs m sp) (loc_arguments sg) args.

(** Extract the values of the arguments to an annotation. *)

Inductive annot_arg: regset -> mem -> val -> annot_param -> val -> Prop :=
  | annot_arg_reg: forall rs m sp r,
      annot_arg rs m sp (APreg r) (rs r)
  | annot_arg_stack: forall rs m stk base chunk ofs v,
      Mem.load chunk m stk (Int.unsigned base + ofs) = Some v ->
      annot_arg rs m (Vptr stk base) (APstack chunk ofs) v.

Definition annot_arguments
   (rs: regset) (m: mem) (sp: val) (params: list annot_param) (args: list val) : Prop :=
  list_forall2 (annot_arg rs m sp) params args.

(** Mach execution states. *)

(** Mach execution states. *)

Inductive stackframe: Type :=
  | Stackframe:
      forall (f: block)       (**r pointer to calling function *)
             (sp: val)        (**r stack pointer in calling function *)
             (retaddr: val)   (**r Asm return address in calling function *)
             (c: code),       (**r program point in calling function *)
      stackframe.

Inductive state: Type :=
  | State:
      forall (stack: list stackframe)  (**r call stack *)
             (f: block)                (**r pointer to current function *)
             (sp: val)                 (**r stack pointer *)
             (c: code)                 (**r current program point *)
             (rs: regset)              (**r register state *)
             (m: mem),                 (**r memory state *)
      state
  | Callstate:
      forall (stack: list stackframe)  (**r call stack *)
             (f: block)                (**r pointer to function to call *)
             (rs: regset)              (**r register state *)
             (m: mem),                 (**r memory state *)
      state
  | Returnstate:
      forall (stack: list stackframe)  (**r call stack *)
             (rs: regset)              (**r register state *)
             (m: mem),                 (**r memory state *)
      state.

Definition parent_sp (s: list stackframe) : val :=
  match s with
  | nil => Vzero
  | Stackframe f sp ra c :: s' => sp
  end.

Definition parent_ra (s: list stackframe) : val :=
  match s with
  | nil => Vzero
  | Stackframe f sp ra c :: s' => ra
  end.

Inductive step: state -> trace -> state -> Prop :=
  | exec_Mlabel:
      forall s f sp lbl c rs m,
      step (State s f sp (Mlabel lbl :: c) rs m)
        E0 (State s f sp c rs m)
  | exec_Mgetstack:
      forall s f sp ofs ty dst c rs m v,
      load_stack m sp ty ofs = Some v ->
      step (State s f sp (Mgetstack ofs ty dst :: c) rs m)
        E0 (State s f sp c (rs#dst <- v) m)
  | exec_Msetstack:
      forall s f sp src ofs ty c rs m m' rs',
      store_stack m sp ty ofs (rs src) = Some m' ->
      rs' = undef_regs (destroyed_by_setstack ty) rs ->
      step (State s f sp (Msetstack src ofs ty :: c) rs m)
        E0 (State s f sp c rs' m')
  | exec_Mgetparam:
      forall s fb f sp ofs ty dst c rs m v rs',
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      load_stack m sp Tint f.(fn_link_ofs) = Some (parent_sp s) ->
      load_stack m (parent_sp s) ty ofs = Some v ->
      rs' = (rs # temp_for_parent_frame <- Vundef # dst <- v) ->
      step (State s fb sp (Mgetparam ofs ty dst :: c) rs m)
        E0 (State s fb sp c rs' m)
  | exec_Mop:
      forall s f sp op args res c rs m v rs',
      eval_operation ge sp op rs##args m = Some v ->
      rs' = ((undef_regs (destroyed_by_op op) rs)#res <- v) ->
      step (State s f sp (Mop op args res :: c) rs m)
        E0 (State s f sp c rs' m)
  | exec_Mload:
      forall s f sp chunk addr args dst c rs m a v rs',
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      rs' = ((undef_regs (destroyed_by_load chunk addr) rs)#dst <- v) ->
      step (State s f sp (Mload chunk addr args dst :: c) rs m)
        E0 (State s f sp c rs' m)
  | exec_Mstore:
      forall s f sp chunk addr args src c rs m m' a rs',
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a (rs src) = Some m' ->
      rs' = undef_regs (destroyed_by_store chunk addr) rs ->
      step (State s f sp (Mstore chunk addr args src :: c) rs m)
        E0 (State s f sp c rs' m')
  | exec_Mcall:
      forall s fb sp sig ros c rs m f f' ra,
      find_function_ptr ge ros rs = Some f' ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      return_address_offset f c ra ->
      step (State s fb sp (Mcall sig ros :: c) rs m)
        E0 (Callstate (Stackframe fb sp (Vptr fb ra) c :: s)
                       f' rs m)
  | exec_Mtailcall:
      forall s fb stk soff sig ros c rs m f f' m',
      find_function_ptr ge ros rs = Some f' ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      load_stack m (Vptr stk soff) Tint f.(fn_link_ofs) = Some (parent_sp s) ->
      load_stack m (Vptr stk soff) Tint f.(fn_retaddr_ofs) = Some (parent_ra s) ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step (State s fb (Vptr stk soff) (Mtailcall sig ros :: c) rs m)
        E0 (Callstate s f' rs m')
  | exec_Mbuiltin:
      forall s f sp rs m ef args res b t vl rs' m',
      external_call' ef ge rs##args m t vl m' ->
      rs' = set_regs res vl (undef_regs (destroyed_by_builtin ef) rs) ->
      step (State s f sp (Mbuiltin ef args res :: b) rs m)
         t (State s f sp b rs' m')
  | exec_Mannot:
      forall s f sp rs m ef args b vargs t v m',
      annot_arguments rs m sp args vargs ->
      external_call' ef ge vargs m t v m' ->
      step (State s f sp (Mannot ef args :: b) rs m)
         t (State s f sp b rs m')
  | exec_Mgoto:
      forall s fb f sp lbl c rs m c',
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      step (State s fb sp (Mgoto lbl :: c) rs m)
        E0 (State s fb sp c' rs m)
  | exec_Mcond_true:
      forall s fb f sp cond args lbl c rs m c' rs',
      eval_condition cond rs##args m = Some true ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      step (State s fb sp (Mcond cond args lbl :: c) rs m)
        E0 (State s fb sp c' rs' m)
  | exec_Mcond_false:
      forall s f sp cond args lbl c rs m rs',
      eval_condition cond rs##args m = Some false ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      step (State s f sp (Mcond cond args lbl :: c) rs m)
        E0 (State s f sp c rs' m)
  | exec_Mjumptable:
      forall s fb f sp arg tbl c rs m n lbl c' rs',
      rs arg = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some lbl ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      rs' = undef_regs destroyed_by_jumptable rs ->
      step (State s fb sp (Mjumptable arg tbl :: c) rs m)
        E0 (State s fb sp c' rs' m)
  | exec_Mreturn:
      forall s fb stk soff c rs m f m',
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      load_stack m (Vptr stk soff) Tint f.(fn_link_ofs) = Some (parent_sp s) ->
      load_stack m (Vptr stk soff) Tint f.(fn_retaddr_ofs) = Some (parent_ra s) ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      step (State s fb (Vptr stk soff) (Mreturn :: c) rs m)
        E0 (Returnstate s rs m')
  | exec_function_internal:
      forall s fb rs m f m1 m2 m3 stk rs',
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      Mem.alloc m 0 f.(fn_stacksize) = (m1, stk) ->
      let sp := Vptr stk Int.zero in
      store_stack m1 sp Tint f.(fn_link_ofs) (parent_sp s) = Some m2 ->
      store_stack m2 sp Tint f.(fn_retaddr_ofs) (parent_ra s) = Some m3 ->
      rs' = undef_regs destroyed_at_function_entry rs ->
      step (Callstate s fb rs m)
        E0 (State s fb sp f.(fn_code) rs' m3)
  | exec_function_external:
      forall s fb rs m t rs' ef args res m' lres,
      Genv.find_funct_ptr ge fb = Some (External ef) ->
      extcall_arguments rs m (parent_sp s) (ef_sig ef) args ->
      external_call' ef ge args m t res m' ->
      loc_result (ef_sig ef) = Some lres ->
      rs' = set_regs (lres) res rs ->
      step (Callstate s fb rs m)
         t (Returnstate s rs' m')
  | exec_return:
      forall s f sp ra c rs m,
      step (Returnstate (Stackframe f sp ra c :: s) rs m)
        E0 (State s f sp c rs m).

End RELSEM.

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall fb m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some fb ->
      initial_state p (Callstate nil fb (Regmap.init Vundef) m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r retcode,
      loc_result signature_main = Some (r :: nil) ->
      rs r = Vint retcode ->
      final_state (Returnstate nil rs m) retcode.

Definition semantics (rao: function -> code -> int -> Prop) (p: program) :=
  Semantics (step rao) (initial_state p) final_state (Genv.globalenv p).