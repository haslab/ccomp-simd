Require Mach.
Require Import Extra.
Import Coqlib Maps.
Import AST Op Events.
Import Memory.
Import Values Integers.
Import Mach.
Import Machregs.
Import Conventions1.
Import Smallstep.

Unset Elimination Schemes.

Definition node := positive.

Inductive instruction: Type :=
  | MIgetparam : int → typ → mreg → node → instruction
  | MIop : operation → list mreg → mreg → node → instruction
  | MIload : memory_chunk → addressing → list mreg → mreg → node → instruction
  | MIstore : memory_chunk → addressing → list mreg → mreg → node → instruction
  | MIcall : signature → mreg + ident → node → instruction
  | MItailcall : signature → mreg + ident → instruction
  | MIbuiltin : external_function → list mreg → list mreg → node → instruction
  | MIannot : external_function → list annot_param → node → instruction
  | MIgoto : node → instruction
  | MIcond : condition → list mreg → node → node → instruction
  | MIjumptable : mreg → list node → instruction
  | MIreturn : instruction
.

Definition code := PTree.t instruction.

Record function: Type := mkfunction
  { fn_sig: signature;
    fn_code: code;
    fn_entrypoint : node;
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

Definition successors (i: instruction) : list node :=
  match i with
  | MIop _ _ _ s
  | MIload _ _ _ _ s
  | MIstore _ _ _ _ s
  | MIbuiltin _ _ _ s
  | MIannot _ _ s
  | MIgetparam _ _ _ s
  | MIcall _ _ s
  | MIgoto s => s :: nil
  | MIcond _ _ ifso ifnot => ifso :: ifnot :: nil
  | MItailcall _ _
  | MIreturn => nil
  | MIjumptable _ tbl => tbl
  end.

Import Globalenvs.

Definition genv := Genv.t fundef unit.

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

Section SMALL_STEP.

  Record stackframe := SF
    { sf_f : block ; sf_sp : val ; sf_retaddr: val ; sf_pc : node }.

  Definition parent_sp stk :=
    match stk with
    | nil => Vzero
    | sf :: _ => sf_sp sf
    end.

  Definition parent_ra stk :=
    match stk with
    | nil => Vzero
    | sf :: _ => sf_retaddr sf
    end.

  Inductive state :=
  | State `(list stackframe) `(block) `(val) `(node) `(regset) `(mem)
  | Callstate `(list stackframe) `(block) `(regset) `(mem)
  | Returnstate `(list stackframe) `(regset) `(mem)
  .

  Context (return_address_offset: function → node → int → Prop).
  Context (ge: genv).

  Definition step (s: state) (tr: trace) (s': state) : Prop :=
    match s with
    | Callstate stk fb rs m =>
      match Genv.find_funct_ptr ge fb with
      | None => False
      | Some (External ef) =>
        ∃ args res m',
          extcall_arguments rs m (parent_sp stk) (ef_sig ef) args ∧
          external_call' ef ge args m tr res m' ∧
          s' = Returnstate stk (set_regs (loc_result (ef_sig ef)) res rs) m'
      | Some (Internal f) =>
        let '(m1, spb) := Mem.alloc m 0 f.(fn_stacksize) in
        let sp := Vptr spb Int.zero in
        ∃ m2 m3,
          store_stack m1 sp Tint f.(fn_link_ofs) (parent_sp stk) = Some m2 ∧
          store_stack m2 sp Tint f.(fn_retaddr_ofs) (parent_ra stk) = Some m3 ∧
          tr = E0 ∧
          s' = State stk fb sp f.(fn_entrypoint) (undef_regs destroyed_at_function_entry rs) m3
      end

    | Returnstate stk rs m =>
      tr = E0 ∧
      ∃ sf stk', stk = sf :: stk' ∧ s' = State stk' (sf_f sf) (sf_sp sf) (sf_pc sf) rs m

    | State stk fb sp pc rs m =>
      ∃ f, Genv.find_funct_ptr ge fb = Some (Internal f) ∧
           match (fn_code f) ! pc with
           | None => False
           | Some i =>
             match i with
             | MIgetparam ofs ty dst pc' =>
               ∃ v,
               load_stack m sp Tint f.(fn_link_ofs) = Some (parent_sp stk) ∧
               load_stack m (parent_sp stk) ty ofs = Some v ∧
               tr = E0 ∧
               s' = State stk fb sp pc' (rs # temp_for_parent_frame <- Vundef # dst <- v) m
             | MIop op args dst pc' =>
               ∃ v,
                 eval_operation ge sp op rs##args m = Some v ∧
                 tr = E0 ∧
                 s' = State stk fb sp pc' ((undef_regs (destroyed_by_op op) rs)#dst <- v) m
             | MIload ϰ addr args dst pc' =>
               ∃ a v,
                   eval_addressing ge sp addr rs##args = Some a ∧
                   Mem.loadv ϰ m a = Some v ∧
                   tr = E0 ∧
                   s' = State stk fb sp pc' ((undef_regs (destroyed_by_load ϰ addr) rs)#dst <- v) m
             | MIstore ϰ addr args src pc' =>
               ∃ a m',
                 eval_addressing ge sp addr rs##args = Some a ∧
                 Mem.storev ϰ m a (rs src) = Some m' ∧
                 tr = E0 ∧
                 s' = State stk fb sp pc' (undef_regs (destroyed_by_store ϰ addr) rs) m'
             | MIcall sg ros pc' =>
               ∃ f' ra,
                   find_function_ptr ge ros rs = Some f' ∧
                   return_address_offset f pc' ra ∧
                   tr = E0 ∧
                   s' = Callstate (SF fb sp (Vptr fb ra) pc' :: stk) f' rs m
             | MItailcall sg ros =>
               ∃ sbk soff, sp = Vptr sbk soff ∧
               ∃ f' m',
                 find_function_ptr ge ros rs = Some f' ∧
                 load_stack m (Vptr sbk soff) Tint f.(fn_link_ofs) = Some (parent_sp stk) ∧
                 load_stack m (Vptr sbk soff) Tint f.(fn_retaddr_ofs) = Some (parent_ra stk) ∧
                 Mem.free m sbk 0 f.(fn_stacksize) = Some m' ∧
                 tr = E0 ∧
                 s' = Callstate stk f' rs m'
             | MIbuiltin ef args res pc' =>
               ∃ vl m',
                 external_call' ef ge rs##args m tr vl m' ∧
                 s' = State stk fb sp pc' (set_regs res vl (undef_regs (destroyed_by_builtin ef) rs)) m'
             | MIannot ef args pc' =>
               ∃ vargs v m',
                 annot_arguments rs m sp args vargs ∧
                 external_call' ef ge vargs m tr v m' ∧
                 s' = State stk fb sp pc' rs m'
             | MIgoto pc' => tr = E0 ∧ s' = State stk fb sp pc' rs m
             | MIcond cond args ifso ifnot =>
               ∃ b,
                 eval_condition cond rs##args m = Some b ∧
                 tr = E0 ∧
                 s' = State stk fb sp (if b then ifso else ifnot) (undef_regs (destroyed_by_cond cond) rs) m
             | MIjumptable arg tbl =>
               ∃ n pc',
                   rs arg = Vint n ∧
                   list_nth_z tbl (Int.unsigned n) = Some pc' ∧
                   (* TODO: (fn_code f) ! pc' ≠ None ∧ *)
                   tr = E0 ∧
                   s' = State stk fb sp pc' (undef_regs destroyed_by_jumptable rs) m
             | MIreturn =>
               ∃ sbk soff, sp = Vptr sbk soff ∧
               ∃ m',
                 load_stack m (Vptr sbk soff) Tint f.(fn_link_ofs) = Some (parent_sp stk) ∧
                 load_stack m (Vptr sbk soff) Tint f.(fn_retaddr_ofs) = Some (parent_ra stk) ∧
                 Mem.free m sbk 0 f.(fn_stacksize) = Some m' ∧
                 tr = E0 ∧
                 s' = Returnstate stk rs m'
             end
           end
    end.

End SMALL_STEP.

Definition initial_state (p: program) (s: state) : Prop :=
  let ge := Genv.globalenv p in
  ∃ m fb,
    Genv.init_mem p = Some m ∧
    Genv.find_symbol ge p.(prog_main) = Some fb ∧
    s = Callstate nil fb (Regmap.init Vundef) m.

Definition final_state (s: state) (v: int) : Prop :=
  ∃ rs m r,
    loc_result signature_main = r :: nil ∧
    rs r = Vint v ∧
    s = Returnstate nil rs m.

Definition semantics (rao: function → node → int → Prop) (p: program) :=
  Semantics (step rao) (initial_state p) final_state (Genv.globalenv p).

Lemma semantics_receptive rao p:
  receptive (semantics rao p).
Proof.
  Hint Constructors external_call'.
  split.
  - intros s t1 s1 t2 H H0.
    assert (t1 = E0 → ∃ s', step rao (Genv.globalenv p) s t2 s').
    { intros ->. inv H0. exists s1. exact H. }
    destruct s; simpl in *; hsplit;
      repeat
      match goal with
      | H : False |- _ => destruct H
      | H : ?a = ?b |- _ => subst a || subst b
      | H : _ ∧ _ |- _ => destruct H
      | H : ∃ a, _ |- _ => destruct H
      | H : match ?a with _ => _ end |- _ => destruct a eqn: ?
      | H : external_call' _ _ _ _ _ _ _ |- _ => inversion H; clear H
      | H : external_call _ _ _ _ _ _ _,
            M: match_traces _ _ _
        |- _ => pose proof (external_call_receptive _ _ _ _ _ H M); clear H M
      end; eauto 10;
        try (eexists _, f; match goal with H : _ ! _ = Some _ |- _ => rewrite H end; split; eauto 42).
  - intros s tr s' H. destruct s; simpl in *; hsplit;
      repeat
      match goal with
      | H : False |- _ => destruct H
      | H : ?a = ?b |- _ => subst a || subst b
      | H : _ ∧ _ |- _ => destruct H
      | H : ∃ a, _ |- _ => destruct H
      | H : match ?a with _ => _ end |- _ => destruct a eqn: ?
      | H : external_call' _ _ _ _ _ _ _ |- _ => inversion H; clear H; eapply external_call_trace_length; eauto
    end; simpl; try omega.
Qed.

Lemma annot_arguments_determ {rs m sp args vargs vargs'} :
  annot_arguments rs m sp args vargs →
  annot_arguments rs m sp args vargs' →
  vargs = vargs'.
Proof.
  intros H; revert vargs'; elim H; clear. inversion 1; auto.
  intros ap args v vargs H REC IH vargs'.
  inversion 1; subst.
  specialize (IH _ H5). apply f_equal2; auto.
  repeat match goal with H: annot_arg _ _ _ _ _ |- _ => inversion H; clear H; subst end.
  auto. congruence.
Qed.

Lemma extcall_arguments_determ {rs m sp sg args args'} :
  extcall_arguments rs m sp sg args →
  extcall_arguments rs m sp sg args' →
  args = args'.
Proof.
  unfold extcall_arguments.
  generalize (loc_arguments sg). intros params.
  intros H; revert args'; elim H; clear. inversion 1; auto.
  intros ap args v vargs H REC IH vargs'.
  inversion 1; subst.
  specialize (IH _ H5). apply f_equal2; auto.
  repeat match goal with H: extcall_arg _ _ _ _ _ |- _ => inversion H; clear H; subst end.
  auto. congruence.
Qed.

Lemma semantics_determinate (rao: function → node → int → Prop) p:
  (∀ f n o o', rao f n o → rao f n o' → o = o') →
  determinate (semantics rao p).
Proof.
  Hint Constructors match_traces.
  intros RAO.
  split; simpl.
  - intros s t1 s1 t2 s2 H H'.
    destruct s; simpl in *;
      repeat
      match goal with
      | H : False |- _ => destruct H
      | H : ?a = ?b |- _ => subst a || subst b
      | H : _ ∧ _ |- _ => destruct H
      | H : ∃ a, _ |- _ => destruct H
      | H : match ?a with _ => _ end, R : ?a = _ |- _ => rewrite R in H
      | A : ?a = Some _, B : ?a = Some _ |- _ => rewrite A in B; apply some_eq_inv in B
      | H : Internal _ = Internal _ |- _ => inversion H; clear H
      | H : Vptr _ _ = Vptr _ _ |- _ => inversion H; clear H
      | H : rao ?a ?b _, K: rao ?a ?b _ |- _ => pose proof (RAO _ _ _ _ H K); clear K
      | H : external_call' _ _ _ _ _ _ _ |- _ => inversion H; clear H
      | H : external_call _ _ _ _ _ _ _, K : external_call _ _ _ _ _ _ _ |- _ =>
        generalize (external_call_determ _ _ _ _ _ _ _ _ _ _ H K);
        generalize (external_call_determ _ _ _ _ _ _ _ _ _ _ K H);
        clear K; intros ? ?
      | H : annot_arguments _ _ _ _ _, K : annot_arguments _ _ _ _ _ |- _ =>
        generalize (annot_arguments_determ H K); clear K; intro
      | H : extcall_arguments _ _ _ _ _, K : extcall_arguments _ _ _ _ _ |- _ =>
        generalize (extcall_arguments_determ H K); clear K; intro
      | H : match ?a with _ => _ end |- _ => destruct a eqn: ?
      end; auto.
    intuition (subst; auto).
    intuition (subst; auto).
    intuition (subst; auto). congruence.
    intuition (subst; auto).
    intuition (subst; auto). congruence.
  - apply semantics_receptive.
  - unfold initial_state. intros; hsplit. congruence.
  - unfold final_state, nostep. intros; hsplit. subst. simpl. intro; hsplit. congruence.
  - unfold final_state. intros; hsplit. congruence.
Qed.

(* ********* *)
(** Translation from Mach *)

(* Precomputes the position of each label, and the size of the code *)
Definition compute_labels_aux (i: Mach.instruction) (ms: PTree.t node * positive) :=
  let '(m, s) := ms in
  let s' := Pos.succ s in
  (match i with Mlabel lbl => PTree.set lbl s m | _ => m end, s').

Definition compute_labels : Mach.code → PTree.t node * positive :=
  List.fold_right compute_labels_aux
    (PTree.empty _, xH).

Definition plen {X} (m: list X) : positive := Pos.of_succ_nat (length m).

Lemma compute_labels_correct_aux m' s' :
  ∀ c m s,
  fold_right compute_labels_aux (m', s') c = (m, s) →
  s = Pos.pred (s' + plen c) ∧
  ∀ lbl,
    (∀ c', find_label lbl c = Some c' → m ! lbl = Some (Pos.pred (s' + plen c'))) ∧
    (∀ n, m ! lbl = Some n → m' ! lbl = Some n ∨ ∃ c', find_label lbl c = Some c' ∧ n = Pos.pred (s' + plen c')).
Proof.
  intros c; elim c; clear c.
  - intros m s H; apply pair_eq_inv in H. destruct H as [ <- <- ].
    split. symmetry. rewrite Pos.add_1_r. apply Pos.pred_succ.
    intros lbl. split. intros c. refine (None_eq_Some_inv _).
    intuition.
  - intros i c IH m s. simpl.
    destruct (fold_right _ _ _) as (m'', s'') eqn: EQ.
    specialize (IH _ _ eq_refl). destruct IH as ( -> & IH ).
    intros H. apply pair_eq_inv in H.
    destruct H as (<- & <-). split.
    + unfold plen. simpl. rewrite Pos.add_succ_r, Pos.pred_succ.
      apply Pos.succ_pred. zify. romega.
    + intros lbl; specialize (IH lbl); destruct IH as [ IH IH' ]; split.
      * intros c' H. specialize (IH c').
        destruct i; auto. simpl in H. destruct peq. apply some_eq_inv in H. subst.
        apply PTree.gss.
        rewrite PTree.gso; auto.
      * intros n H. specialize (IH' n).
        destruct i; auto.
        rewrite PTree.gsspec in H. destruct peq.
        apply some_eq_inv in H. subst. right.
        exists c. split. simpl. rewrite peq_true. reflexivity. reflexivity.
        simpl. rewrite peq_false; auto.
Qed.

Lemma compute_labels_correct c m s :
  compute_labels c = (m, s) →
  s = plen c ∧
  ∀ lbl,
    (∀ c', find_label lbl c = Some c' → m ! lbl = Some (plen c')) ∧
    (∀ n, m ! lbl = Some n → ∃ c', find_label lbl c = Some c' ∧ n = plen c').
Proof.
  intros H.
  destruct (compute_labels_correct_aux _ _ _ _ _ H) as [ A B ]. clear H.
  rewrite Pos.add_1_l, Pos.pred_succ in A.
  refine (conj A _). clear A.
  intros lbl. specialize (B lbl). destruct B as [B C]. split.
  intros c' H. rewrite (B c' H).
  rewrite Pos.add_1_l, Pos.pred_succ. reflexivity.
  intros n H. destruct (C n H) as [X|(c' & X & Y)].
  rewrite PTree.gempty in X. exact (None_eq_Some_inv _ X).
  exists c'. refine (conj X _). rewrite Y.
  rewrite Pos.add_1_l, Pos.pred_succ. reflexivity.
Qed.

Section TRANSL_CODE.
Context (label_map: PTree.t node).

Definition transl_instr (pc': node) (i: Mach.instruction) : instruction :=
  let pc_of_label lbl :=
      match label_map ! lbl with Some pc' => pc' | None => pc' end in
  match i with
  | Mgetstack ofs ty dst => MIload (chunk_of_type ty) (Ainstack ofs) nil dst pc'
  | Msetstack src ofs ty => MIstore (chunk_of_type ty) (Ainstack ofs) nil src pc'
  | Mgetparam ofs ty dst => MIgetparam ofs ty dst pc'
  | Mop op args dst => MIop op args dst pc'
  | Mload ϰ addr args dst => MIload ϰ addr args dst pc'
  | Mstore ϰ addr args src => MIstore ϰ addr args src pc'
  | Mcall sg f => MIcall sg f pc'
  | Mtailcall sg f => MItailcall sg f
  | Mbuiltin ef args dst => MIbuiltin ef args dst pc'
  | Mannot ef args => MIannot ef args pc'
  | Mlabel _ => MIgoto pc'
  | Mgoto lbl => MIgoto (pc_of_label lbl)
  | Mcond cond args lbl => MIcond cond args (pc_of_label lbl) pc'
  | Mjumptable arg tbl => MIjumptable arg (List.map pc_of_label tbl)
  | Mreturn => MIreturn
  end.

Definition transl_code_aux i ms :=
  let '(m, pc') := ms in
  let pc := Pos.succ pc' in
  let j := transl_instr pc' i in
  (PTree.set pc j m, pc).

Definition transl_code (c: Mach.code) :=
  List.fold_right transl_code_aux
    (PTree.empty _, xH)
    c.

Lemma transl_code_correct_aux m' s' c :
  ∀ m s,
    fold_right transl_code_aux (m', s') c = (m, s) →
    s = Pos.pred (s' + plen c) ∧
    (∀ pc j,
      m ! pc = Some j →
      m' ! pc = Some j ∨
      ∃ i c', nlast (Pos.to_nat pc - Pos.to_nat s') c = (O, i :: c') ∧ j = transl_instr (Pos.pred pc) i)
    ∧
    (∀ pc i c',
        nlast (Pos.to_nat (Pos.succ pc) - Pos.to_nat s') c = (O, i :: c') →
        m ! (Pos.succ pc) = Some (transl_instr pc i) ∨ (pc < s')%positive
    )
.
Proof.
  elim c; clear c.
  - intros m s H; apply pair_eq_inv in H. destruct H as [ <- <- ].
    split. rewrite Pos.pred_sub. symmetry. apply Pos.add_sub.
    split. auto. discriminate.
  - intros i c IH m s.
    simpl fold_right. destruct (fold_right _ _ _) as (m'', s'') eqn: EQ. intros H.
    specialize (IH _ _ eq_refl). destruct IH as [ -> (IH & IH') ].
    apply pair_eq_inv in H; destruct H as [ <- <- ].
    refine (conj _ (conj _ _)).
    + unfold plen; simpl; fold (plen c).
      rewrite Pos.add_succ_r.
      rewrite Pos.pred_succ.
      apply Pos.succ_pred.
      zify; omega.
    + intros pc j.
      rewrite PTree.gsspec.
      rewrite Pos.succ_pred by (zify; omega).
      destruct peq.
      * intros H; apply some_eq_inv in H; subst pc j.
        right. eexists _, _. refine (conj _ eq_refl).
        unfold plen. rewrite Pos2Nat.inj_add, SuccNat2Pos.id_succ.
        rewrite nlast_all. f_equal. simpl. omega. simpl. omega.
      * intros H.
        specialize (IH _ _ H). destruct IH as [ IH | (i' & c' & IH & ->) ].
        left; exact IH.
        right. exists i', c'. refine (conj _ eq_refl).
        simpl. rewrite IH. reflexivity.
    + intros pc i' c' H. specialize (IH' pc i' c'). clear EQ.
      rewrite Pos.succ_pred by (zify; omega).
      rewrite PTree.gsspec. case peq.
      intros EQ; rewrite <- EQ, Pos.pred_succ. left. f_equal. f_equal.
      rewrite nlast_all in H. congruence.
      clear -EQ. simpl. unfold plen in EQ. zify. omega.
      intros NE. case (plt pc s'). auto. intros GE.
      simpl in H. destruct (nlast _ _) as ([| n'], m) eqn: Hm.
      specialize (IH' H). auto.
      elim NE; clear NE.
      clear IH IH'. apply pair_eq_inv in H.
      generalize (nlast_len c (Pos.to_nat (Pos.succ pc) - Pos.to_nat s')). rewrite Hm.
      clear Hm.
      unfold fst. unfold snd. destruct H as [ -> _ ].
      intros [H H']. unfold plen. zify. omega.
Qed.

Lemma transl_code_correct m s c :
    transl_code c = (m, s) →
    s = plen c ∧
    (∀ pc j,
      m ! pc = Some j →
      ∃ i c', nlast (Pos.to_nat pc - 1) c = (O, i :: c') ∧ j = transl_instr (Pos.pred pc) i)
    ∧
    (∀ pc i c',
        nlast (Pos.to_nat pc) c = (O, i :: c') →
        m ! (Pos.succ pc) = Some (transl_instr pc i)
    ).
Proof.
  intros H.
  generalize (transl_code_correct_aux _ _ _ _ _ H). clear H.
  intros [ -> (H & K) ]. refine (conj _ (conj _ _)).
  - rewrite Pos.add_1_l; apply Pos.pred_succ.
  - intros pc j H'. specialize (H _ j H').
    destruct H as [ H | H ].
    rewrite PTree.gempty in H. refine (None_eq_Some_inv _ H).
    auto.
  - intros pc i c' H'. specialize (K pc i c').
    rewrite Pos2Nat.inj_succ in K; simpl in K; rewrite <- minus_n_O in K.
    destruct (K H'). auto. zify. omega.
Qed.

End TRANSL_CODE.

Definition transl_function (f: Mach.function) : function :=
  let c := Mach.fn_code f in
  let '(label_map, s) := compute_labels c in
  let '(c', _) := transl_code label_map c in
  {|
    fn_sig := f.(Mach.fn_sig);
    fn_code := c';
    fn_entrypoint := s;
    fn_stacksize := f.(Mach.fn_stacksize);
    fn_link_ofs := f.(Mach.fn_link_ofs);
    fn_retaddr_ofs := f.(Mach.fn_retaddr_ofs)
  |}.

Lemma transl_function_correct f :
  let f' := transl_function f in
  let c := Mach.fn_code f in
  let '(label_map, _) := compute_labels c in
  fn_entrypoint f' = plen c ∧
  (∀ pc j,
      (fn_code f') ! pc = Some j →
      ∃ i c', nlast (Pos.to_nat pc - 1) c = (O, i :: c') ∧ j = transl_instr label_map (Pos.pred pc) i)
  ∧
  (∀ pc i c',
      nlast (Pos.to_nat pc) c = (O, i :: c') →
      (fn_code f') ! (Pos.succ pc) = Some (transl_instr label_map pc i)
  ).
Proof.
  unfold transl_function. subst.
  destruct (compute_labels _) as (label_map, s) eqn: Hlab.
  generalize (compute_labels_correct _ _ _ Hlab). clear Hlab.
  intros (-> & Hlab).
  destruct (transl_code _ _) as (c', s') eqn: Hc'. simpl.
  generalize (transl_code_correct _ _ _ _ Hc'). clear Hc'.
  intros [ -> H ]. auto.
Qed.

Definition transl_fundef (fd: Mach.fundef) : fundef :=
  match fd with
  | Internal fn => Internal (transl_function fn)
  | External ef => External ef
  end.

Definition transl_program : Mach.program → program :=
  transform_program transl_fundef.

(** Simulations *)
Section SIMULATION.

Context (return_address_offset: Mach.function → Mach.code → int → Prop).

Definition match_pc (f: Mach.function) (c: Mach.code) (pc: node) : Prop :=
  nlast (Pos.to_nat pc - 1) (Mach.fn_code f) = (O, c).

Definition return_address_offset' (f': function) (pc: node) (ofs: int) : Prop :=
  ∃ f c,
    transl_function f = f' ∧
    match_pc f c pc ∧
    return_address_offset f c ofs.

Context (p: Mach.program).

Let p' := transl_program p.
Let ge := Genv.globalenv p.
Let ge' := Genv.globalenv p'.

Definition match_fun_block fb c pc : Prop :=
  ∃ f,
    Genv.find_funct_ptr ge fb = Some (Internal f) ∧
    Genv.find_funct_ptr ge' fb = Some (Internal (transl_function f)) ∧
    match_pc f c pc.

Definition match_stackframe (sf: Mach.stackframe) (sf': stackframe) : Prop :=
  let 'Stackframe fb sp ra c := sf in
  let 'SF fb' sp' ra' pc := sf' in
  fb = fb' ∧ sp = sp' ∧ ra = ra' ∧ match_fun_block fb c pc.

Definition match_stack := Forall2 match_stackframe.

Definition match_state (s: Mach.state) (s': state) : Prop :=
  match s with
  | Mach.State stk fb sp c rs m =>
    ∃ stk' pc,
    match_stack stk stk' ∧
    match_fun_block fb c pc ∧
    s' = State stk' fb sp pc rs m
  | Mach.Callstate stk fb rs m =>
    ∃ stk',
    match_stack stk stk' ∧
    s' = Callstate stk' fb rs m
  | Mach.Returnstate stk rs m =>
    ∃ stk',
    match_stack stk stk' ∧
    s' = Returnstate stk' rs m
end.

Lemma match_pc_has_instr f i c pc :
  match_pc f (i :: c) pc →
  (fn_code (transl_function f)) ! pc = Some (transl_instr (fst (compute_labels (Mach.fn_code f))) (Pos.pred pc) i)
  ∧ match_pc f c (Pos.pred pc).
Proof.
  unfold match_pc. intros H.
  assert (∃ pc', pc = Pos.succ pc').
  { exists (Pos.pred pc). symmetry.
    apply Pos.succ_pred. intros ->.
    simpl in H.
    generalize (nlast_len (Mach.fn_code f) O).
    rewrite H. simpl. omega. }
  hsplit; subst pc.
  generalize (transl_function_correct f). simpl.
  destruct (compute_labels _) as (label_map, s) eqn: Hlab.
  intros (_ & _ & K).
  rewrite Pos2Nat.inj_succ in H. simpl in H. rewrite <- minus_n_O in H.
  rewrite Pos.pred_succ.
  split. exact (K _ _ _ H).
  eauto using nlast_m1.
Qed.

Lemma fn_link_ofs_transl_function f :
  fn_link_ofs (transl_function f) = Mach.fn_link_ofs f.
Proof.
  unfold transl_function.
  destruct (compute_labels _). destruct (transl_code _ _). reflexivity.
Qed.

Lemma fn_retaddr_ofs_transl_function f :
  fn_retaddr_ofs (transl_function f) = Mach.fn_retaddr_ofs f.
Proof.
  unfold transl_function.
  destruct (compute_labels _). destruct (transl_code _ _). reflexivity.
Qed.

Lemma fn_stacksize_transl_function f :
  fn_stacksize (transl_function f) = Mach.fn_stacksize f.
Proof.
  unfold transl_function.
  destruct (compute_labels _). destruct (transl_code _ _). reflexivity.
Qed.

Lemma fn_entrypoint_transl_function f :
  fn_entrypoint (transl_function f) = plen (Mach.fn_code f).
Proof.
  unfold transl_function.
  generalize (compute_labels_correct (Mach.fn_code f)).
  destruct (compute_labels _). intros H. specialize (H _ _ eq_refl).
  destruct H as [ H _ ].
  destruct (transl_code _ _). exact H.
Qed.

Lemma match_stack_parent_sp {stk stk'} :
  match_stack stk stk' →
  parent_sp stk' = Mach.parent_sp stk.
Proof.
  intros (). reflexivity.
  intros (). intros f sp retaddr c (). simpl. intuition.
Qed.

Lemma match_stack_parent_ra {stk stk'} :
  match_stack stk stk' →
  parent_ra stk' = Mach.parent_ra stk.
Proof.
  intros (). reflexivity.
  intros (). intros f sp retaddr c (). simpl. intuition.
Qed.

Lemma find_function_ptr_preserved ros rs :
  find_function_ptr ge' ros rs = Mach.find_function_ptr ge ros rs.
Proof.
  destruct ros as [ r | s ]. reflexivity.
  apply Genv.find_symbol_transf.
Qed.

Lemma return_address_offset_preserved {f c pc} :
  match_pc f c pc →
  ∀ ra, return_address_offset f c ra →
        return_address_offset' (transl_function f) pc ra.
Proof.
  unfold return_address_offset'. eauto.
Qed.

Lemma find_label_nlast lbl c c' :
  find_label lbl c = Some c' →
  nlast (length c') c = (O, c').
Proof.
  revert c'. elim c; clear.
  intros ?; refine (None_eq_Some_inv _).
  intros i c IH c'.
  destruct i;
    try (intros H; specialize (IH _ H); simpl; rewrite IH; auto).
  simpl. case peq. intros -> H. apply some_eq_inv in H. subst c'.
  rewrite nlast_all, minus_diag; reflexivity.
  intros _ H; specialize (IH _ H); rewrite IH; auto.
Qed.

Lemma match_find_label q lbl f c' :
  find_label lbl (Mach.fn_code f) = Some c' →
  match_pc f c' match (fst (compute_labels (Mach.fn_code f))) ! lbl with Some pc' => pc' | None => q end.
Proof.
  generalize (compute_labels_correct (Mach.fn_code f)).
  destruct (compute_labels _) as (lab, s).
  intros H. specialize (H _ _ eq_refl). destruct H as [-> H].
  specialize (H lbl). destruct H as [H H'].
  intros K. specialize (H _ K). simpl. rewrite H. red.
  unfold plen. rewrite SuccNat2Pos.id_succ. simpl. rewrite <- minus_n_O.
  eauto using find_label_nlast.
Qed.

Theorem simulation_to_IR  :
  forward_simulation (Mach.semantics return_address_offset p)
                     (semantics return_address_offset' (transl_program p)).
Proof.
  refine
    (forward_simulation_step
       (Mach.semantics return_address_offset p)
       (semantics return_address_offset' (transl_program p))
       _ match_state _ _ _).
  - apply Genv.find_symbol_transf.
  - intros s H; inv H. simpl.
    refine (ex_intro _ _
                     (conj _
                           (ex_intro _ nil (conj (Forall2_nil _) eq_refl)))).
    exists m0, fb. split. eauto using Genv.init_mem_transf.
    refine (conj _ eq_refl). simpl.
    unfold transl_program. rewrite Genv.find_symbol_transf. auto.
  - simpl.
    intros s s' r M H; inv H. simpl in M. hsplit. subst. inv M.
    eexists. eauto.
  - simpl.
    Hint Unfold match_fun_block load_stack store_stack.
    Hint Resolve match_find_label.
    intros s tr s' STEP q M.
    inv STEP; simpl in M; unfold match_fun_block in M; hsplit; subst; simpl;
      fold p'; fold ge';
        repeat match goal with H : _ = Some _, K : _ = Some _ |- _ => try fold ge in H; rewrite H in K; inversion K; clear K; subst end;
        try
        match goal with
        | M : match_pc _ _ _ |- _ => destruct (match_pc_has_instr _ _ _ _ M)
        end;
    try (
      eexists; split;
      [
        eexists; split; [ eassumption | ];
        try rewrite fn_link_ofs_transl_function;
        try rewrite fn_retaddr_ofs_transl_function;
        try rewrite fn_stacksize_transl_function;
        repeat match goal with
            | H : match_stack _ _ |- _ => rewrite (match_stack_parent_sp H)
            | H : match_stack _ _ |- _ => rewrite (match_stack_parent_ra H)
            | H : eval_operation _ _ _ _ _ = Some _ |- _ =>
              rewrite <- (eval_operation_preserved _ _ (Genv.find_symbol_transf transl_fundef _)) in H; fold transl_program in H; fold p' in H; fold ge' in H
            | H : eval_addressing _ _ _ _ = Some _ |- _ =>
              rewrite <- (eval_addressing_preserved _ _ (Genv.find_symbol_transf transl_fundef _)) in H; fold transl_program in H; fold p' in H; fold ge' in H
            | H : match_pc _ _ _, K : return_address_offset _ _ _ |- _ =>
               apply (return_address_offset_preserved H) in K
            | H : Mach.find_function_ptr _ _ _ = Some _ |- _ =>
              rewrite <- (find_function_ptr_preserved) in H
            | H : external_call' _ _ _ _ _ _ _ |- _ =>
              pose proof (external_call_symbols_preserved' _ H (Genv.find_symbol_transf transl_fundef _) (Genv.find_var_info_transf transl_fundef _)); clear H
            end;
        match goal with
        | H : _ ! _ = Some _ |- _ => rewrite H; simpl; eauto 12
        end
      | eauto 10]).
    eexists _, _. split. eauto. split. eauto.
    f_equal. f_equal. clear. destruct ty; reflexivity.
    eexists; split; eauto. econstructor; eauto.
    simpl. unfold match_fun_block. eauto 10.
    eexists _, _. split. eauto. split.
    rewrite list_nth_z_map. setoid_rewrite H0. reflexivity.
    eauto.

    + unfold ge', p', transl_program.
      rewrite (Genv.find_funct_ptr_transf transl_fundef p _ H). simpl.
      rewrite fn_stacksize_transl_function, fn_link_ofs_transl_function, fn_retaddr_ofs_transl_function.
      rewrite H0.
      rewrite (match_stack_parent_sp M).
      rewrite (match_stack_parent_ra M).
      eexists. split. eauto 10.
      eexists _, (plen (Mach.fn_code f)). split. eauto. split.
      red. eexists. split. eassumption. split.
      apply (Genv.find_funct_ptr_transf transl_fundef p _ H).
      red. etransitivity. apply nlast_all.
      unfold plen. zify. omega. f_equal. unfold plen. zify. omega.
      rewrite fn_entrypoint_transl_function. reflexivity.

    + unfold ge', p', transl_program.
      rewrite (Genv.find_funct_ptr_transf transl_fundef p _ H). simpl.
      repeat
      match goal with
      | H : match_stack _ _ |- _ => rewrite (match_stack_parent_sp H)
      | H : external_call' _ _ _ _ _ _ _ |- _ =>
        pose proof (external_call_symbols_preserved' _ H (Genv.find_symbol_transf transl_fundef _) (Genv.find_var_info_transf transl_fundef _)); clear H
      end.
      eauto 10.

    + inv M. simpl in H1. destruct y. hsplit. subst.
      eauto 11.
Qed.

Corollary bw_simulation_to_IR  :
  receptive (Mach.semantics return_address_offset p) →
  (∀ f c o o', return_address_offset' f c o → return_address_offset' f c o' → o = o') →
  backward_simulation (Mach.semantics return_address_offset p)
                     (semantics return_address_offset' (transl_program p)).
Proof.
  intros REC DET.
  apply forward_to_backward_simulation.
  apply simulation_to_IR.
  apply REC.
  apply semantics_determinate. apply DET.
Qed.

Lemma match_program_from_IR :
  match_program (λ x y, x = transl_fundef y) eq nil (prog_main p) (transl_program p) p.
Proof.
  constructor; auto.
  exists (prog_defs p). split. 2: symmetry; apply app_nil_r.
  simpl. generalize (prog_defs p). clear p p' ge ge'.
  intros defs; elim defs; clear defs. constructor.
  intros (g, gd) defs IH.
  constructor. 2: exact IH. clear IH.
  destruct gd as [ [fd | ef] | () ]; constructor; reflexivity.
Qed.

Lemma match_pc_first_instr {f c pc j} :
  match_pc f c pc →
  (fn_code (transl_function f)) ! pc = Some j →
  ∃ i c',
  c = i :: c'
  ∧ j = transl_instr (fst (compute_labels (Mach.fn_code f))) (Pos.pred pc) i
  ∧ match_pc f c' (Pos.pred pc).
Proof.
  unfold match_pc. intros H Hj.
  generalize (transl_function_correct f). simpl.
  destruct (compute_labels _) as (label_map, s) eqn: Hlab.
  intros (Hlen & X & _).
  specialize (X _ _ Hj).
  destruct X as (i & c' & Hi & Hj').
  exists i, c'. split. congruence.
  apply (conj Hj').
  eapply nlast_m1.
  rewrite Pos2Nat.inj_pred, pred_of_minus. exact Hi.
  generalize (nlast_len (Mach.fn_code f) (Pos.to_nat pc - 1)).
  rewrite Hi. simpl. zify. omega.
Qed.

Lemma option_map_inv {A B} {f: A → B} {oa ob} :
  option_map f oa = ob →
  match ob with
  | Some b => ∃ a, oa = Some a ∧ f a = b
  | None => oa = None
  end.
Proof.
  destruct oa; intros <-; simpl; eauto.
Qed.

(* The MachIR program can be well defined whereas the Mach program has gotos without the corresponding label.
 Therefore, to prove the converse simulation we must assume that all gotos/if/switch target a label.
 *)

Definition labels_in_instruction (i: Mach.instruction) : label → Prop :=
  match i with
  | Mcond _ _ n
  | Mgoto n => eq n
  | Mjumptable _ tgt => λ lbl, In lbl tgt
  | _ => λ _, False
  end.

Definition jump_target (f: Mach.function) (lbl: label) : Prop :=
  ∃ i, In i (Mach.fn_code f) ∧ labels_in_instruction i lbl.

Definition labels (f: Mach.function) (lbl: label) : Prop :=
  In (Mlabel lbl) (Mach.fn_code f).

Lemma labels_find_label f lbl :
  labels f lbl →
  ∃ c, find_label lbl (Mach.fn_code f) = Some c.
Proof.
  unfold labels. generalize (Mach.fn_code f). intros c.
  elim c; clear. intros ().
  intros i c IH [ -> | IN ]; simpl.
  rewrite peq_true; eauto.
  case is_label; eauto.
Qed.

Hypothesis valid_targets :
  ∀ b f,
    Genv.find_funct_ptr ge b = Some (Internal f) →
    ∀ lbl, jump_target f lbl → labels f lbl.

Lemma match_pc_find_label {b f i c pc} :
    Genv.find_funct_ptr ge b = Some (Internal f) →
    match_pc f (i :: c) pc →
    ∀ lbl,
      labels_in_instruction i lbl →
      ∃ c', find_label lbl (Mach.fn_code f) = Some c'
                ∧ match_pc f c' (plen c').
Proof.
  intros Hf M lbl Hi.
  generalize (nlast_incl (Mach.fn_code f) (Pos.to_nat pc - 1)). rewrite M.
  intros IN.
  specialize (IN i (or_introl _ eq_refl)).
  generalize (valid_targets _ _ Hf lbl (ex_intro _ i (conj IN Hi))).
  intros H; destruct (labels_find_label _ _ H) as (c' & Hc').
  exists c'. apply (conj Hc').
  apply find_label_nlast in Hc'.
  red. unfold plen. rewrite SuccNat2Pos.id_succ.
  simpl. rewrite <- minus_n_O. exact Hc'.
Qed.

Lemma find_label_compute_labels {lbl c c'} :
  find_label lbl c = Some c' →
  (fst (compute_labels c)) ! lbl = Some (plen c').
Proof.
  intros H.
  generalize (compute_labels_correct c). case (compute_labels _).
  intros m s X; specialize (X m s eq_refl). destruct X as (_ & X).
  specialize (X lbl). destruct X as (X & _).
  simpl. auto.
Qed.

Hypothesis return_address_offset_preserved' : ∀ f c pc,
  match_pc f c pc →
  ∀ ra, return_address_offset' (transl_function f) pc ra →
        return_address_offset f c ra.

Theorem simulation_from_IR  :
  forward_simulation (semantics return_address_offset' (transl_program p))
                     (Mach.semantics return_address_offset p).
Proof.
  refine
    (forward_simulation_step
       (semantics return_address_offset' (transl_program p))
       (Mach.semantics return_address_offset p)
       _ (λ x y, match_state y x) _ _ _).
  - symmetry; apply Genv.find_symbol_transf.
  - simpl. unfold initial_state. intros; hsplit; subst.
    exists (Mach.Callstate nil fb (Regmap.init Vundef) m).
    split. 2: exists nil; split; eauto; constructor.
    constructor.
    2: unfold transl_program in *; rewrite Genv.find_symbol_transf in H0; auto.
    refine (Genv.init_mem_match match_program_from_IR _ H).
    intros ? ? ().
  - simpl.
    unfold final_state. intros; hsplit; subst.
    destruct s2; simpl in *; hsplit; try discriminate. inv H2. inv H.
    econstructor; eauto.
  - simpl.
    intros ().
    + intros stk fb sp pc rs m tr s1'. simpl. intros (f & Hf & STEP).
      intros (); simpl; intros; hsplit; try discriminate.
      inv H1.
      destruct ((fn_code f) ! pc0) as [ j | ] eqn: Hj. 2: easy.
      destruct H0 as (f' & Hf' & Hf'' & MPC).
      fold p' in Hf. fold ge' in Hf. rewrite Hf in Hf''. inv Hf''.
      destruct (match_pc_first_instr MPC Hj) as (i & c' & -> & -> & MPC').
      destruct i; hsplit; subst; simpl in STEP; hsplit;
        repeat match goal with
               | H : ?a = ?b |- _ => subst a || subst b
               | H : Some _ = Some _ |- _ => apply some_eq_inv in H
               | H : appcontext[ fn_link_ofs ] |- _ => rewrite fn_link_ofs_transl_function in H
               | H : appcontext[ fn_stacksize ] |- _ => rewrite fn_stacksize_transl_function in H
               | H : appcontext[ fn_retaddr_ofs ] |- _ => rewrite fn_retaddr_ofs_transl_function in H
               | H : appcontext[ parent_sp ] |- _ => erewrite match_stack_parent_sp in H by eassumption
               | H : appcontext[ parent_ra ] |- _ => erewrite match_stack_parent_ra in H by eassumption
               | H : eval_operation _ _ _ _ _ = Some _ |- _ =>
                 unfold transl_program in H;
                 rewrite (eval_operation_preserved _ _ (Genv.find_symbol_transf transl_fundef _)) in H
               | H : eval_addressing _ _ _ _ = Some _ |- _ =>
                 unfold transl_program in H;
                 rewrite (eval_addressing_preserved _ _ (Genv.find_symbol_transf transl_fundef _)) in H
               | H : find_function_ptr _ _ _ = Some _ |- _ => rewrite find_function_ptr_preserved in H
               | H : external_call' _ _ _ _ _ _ _ |- _ =>
                 pose proof (external_call_symbols_preserved' _ H (λ s, eq_sym (Genv.find_symbol_transf transl_fundef _ s)) (λ b, eq_sym (Genv.find_var_info_transf transl_fundef _ b))); clear H
               | H : list_nth_z (_ ## _) _ = Some _ |- _ => rewrite list_nth_z_map in H; apply option_map_inv in H; simpl in H; hsplit
               | H : eval_condition _ _ _ = Some true |- _ => idtac
               | H : eval_condition _ _ _ = Some false |- _ => idtac
               | H : eval_condition _ _ _ = Some ?b |- _ => destruct b
               end;
      try (eexists; split; [ econstructor (eauto; fail) | red; eauto 9; fail ]).
      * eexists. split. econstructor (eauto).
        eexists _, _.
        split. eassumption.
        split. eauto. destruct t; reflexivity.
      * eexists. split. econstructor (eauto).
        eexists (SF _ _ _ _ :: _). split. constructor; eauto. constructor; eauto 10. reflexivity.

      * clear MPC'.
        edestruct (match_pc_find_label Hf' MPC) as (tl & Htl & MPC'). simpl; eauto.
        eexists. split. econstructor (eauto).
        eexists _, _.
        rewrite (find_label_compute_labels Htl). eauto 7.
      * clear MPC'.
        edestruct (match_pc_find_label Hf' MPC) as (tl & Htl & MPC'). simpl; eauto.
        eexists. split. econstructor (eauto).
        eexists _, _.
        rewrite (find_label_compute_labels Htl). eauto 7.
      * clear MPC'.
        edestruct (match_pc_find_label Hf' MPC) as (tl & Htl & MPC'). simpl; eauto using list_nth_z_in.
        eexists. split. econstructor (eauto).
        eexists _, _.
        rewrite (find_label_compute_labels Htl). eauto 7.

    + intros stk b rs m tr s'. simpl.
      destruct (Genv.find_funct_ptr _ _) eqn: H. 2: intros ().
      generalize (Genv.find_funct_ptr_match match_program_from_IR _ H). clear H.
      intros (f' & Hf' & ->).
      intros H (); simpl; try (intros; hsplit; discriminate).
      intros stk' b' rs' m' (istk & MSTK & K). inv K.
      destruct f' as [ fd | ef ]; simpl in H; hsplit.
      destruct (Mem.alloc _ _ _) as (m & q) eqn: X. hsplit. subst.
      eexists. split.
      * rewrite fn_link_ofs_transl_function in *.
        rewrite fn_stacksize_transl_function in *.
        rewrite fn_retaddr_ofs_transl_function in *.
        erewrite match_stack_parent_ra in H0 by eassumption.
        erewrite match_stack_parent_sp in H by eassumption.
        econstructor (eauto; fail).
      * eexists _, _. repeat (split; eauto).
        eexists _. repeat (split; eauto).
        exact (Genv.find_funct_ptr_transf transl_fundef _ _ Hf').
        red.
        rewrite fn_entrypoint_transl_function; unfold plen; rewrite SuccNat2Pos.id_succ.
        rewrite nlast_all. f_equal. omega. omega.
      * subst.
        erewrite match_stack_parent_sp in H by eassumption.
        eexists. split. econstructor; eauto. 2: simpl; eauto.
        eapply external_call_symbols_preserved'. eassumption.
        eauto using Genv.find_symbol_transf.
        eauto using Genv.find_var_info_transf.

    + intros stk rs m tr s' (-> & sf & stk' & -> & ->).
      intros (); try (simpl; intros; hsplit; discriminate).
      intros stk rs' m' (stk'' & MS & H); inv H.
      destruct stk as [ | () stk ]; inv MS. destruct sf. simpl in *. hsplit; subst.
      eexists. split. econstructor. simpl; eauto.
Qed.

Corollary bw_simulation_from_IR :
  determinate (Mach.semantics return_address_offset p) →
  backward_simulation (semantics return_address_offset' (transl_program p))
                      (Mach.semantics return_address_offset p).
Proof.
  intros DET.
  apply forward_to_backward_simulation.
  apply simulation_from_IR.
  apply semantics_receptive.
  apply DET.
Qed.

End SIMULATION.

(*
Definition is_label_spec lbl i :
  reflect (i = Mlabel lbl) (is_label lbl i).
Proof.
  destruct i; try (constructor; discriminate).
  simpl. case peq; constructor; congruence.
Qed.
*)
