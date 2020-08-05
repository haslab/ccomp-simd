Require Import AssocList.
Require Import AbCell.
Require MachIR.
Require Import Registers.
Require Import ClassifyBuiltIns.
Import Util.
Import String.
Import Coqlib.
Import AST.
Import Machregs.
Import Globalenvs.
Import Op.
Import Integers.
Import Values.
Import Memory.
Import Mach.
Import MachIR.
Import Maps.
Import Utf8.
Import RelationClasses.
Import Morphisms.
Import FSetAVL.
Require Import ToString.

Unset Elimination Schemes.

Module SetProp (A: FSetInterface.S).
  Lemma mem_In x s : reflect (A.In x s) (A.mem x s).
  Proof.
    generalize (@A.mem_1 s x), (@A.mem_2 s x).
    case A.mem. vauto.
    intros H _. constructor. intros X; specialize (H X); eq_some_inv.
  Qed.

  Instance string_of_t `(ToString A.elt) : ToString A.t := λ s,
  "{ " ++ A.fold (λ x, String.append (to_string x ++ "; ")) s "}".

End SetProp.

Instance mreg_eq_dec : EqDec mreg := mreg_eq.

Definition register_names_rev :=
   ("EAX", AX) :: ("EBX", BX) :: ("ECX", CX) :: ("EDX", DX) ::
   ("ESI", SI) :: ("EDI", DI) :: ("EBP", BP) ::
   ("XMM0", X0) :: ("XMM1", X1) :: ("XMM2", X2) :: ("XMM3", X3) ::
   ("XMM4", X4) :: ("XMM5", X5) :: ("XMM6", X6) :: ("XMM7", X7) ::
   ("YMM0", Y0) :: ("YMM1", Y1) :: ("YMM2", Y2) :: ("YMM3", Y3) ::
   ("YMM4", Y4) :: ("YMM5", Y5) :: ("YMM6", Y6) :: ("YMM7", Y7) ::
   ("ST0", FP0) :: nil.

Definition register_names := Eval vm_compute in
      rev_map (λ x, let '(s, r) := x in (r, s)) register_names_rev.

Instance string_of_mreg : ToString mreg := λ r,
  match assoc r register_names with
  | Some s => s
  | None => "?"
  end.

(* Security levels *)
Inductive sec_level := Low | High.

Definition Low_not_High (P: Prop) (EQ: Low = High) : P :=
  let 'eq_refl := EQ in I.

Definition max_sec_level (l1 l2:sec_level) : sec_level :=
  match l1 with
    | High => l1
    | _ => l2
  end.

Notation "l1 ∪ l2" := (max_sec_level l1 l2) (at level 19).

Lemma max_sec_level_comm x y : x ∪ y = y ∪ x.
Proof. case x; case y; reflexivity. Qed.

Module Type AB_REG_MAP.
  Axiom t : Type.
  Axiom eq : t → t → Prop.
  Declare Instance equiv : Equivalence eq.
  Axiom t_dec : ∀ x x', { eq x x' } + { ¬ eq x x' }.
  Axiom empty : t.
  Axiom get : t -> mreg -> sec_level.
  Axiom set : t -> mreg -> sec_level -> t.
  Axiom union : t → t → t.

  Declare Instance get_m : Proper (eq ==> Logic.eq ==> Logic.eq) get.
  Axiom gempty : ∀ r, get empty r = Low.
  Axiom gs : ∀ x r v r', get (set x r v) r' = if mreg_eq r r' then v else get x r'.
  Axiom gunion : ∀ x y r, get (union x y) r = get x r ∪ get y r.

  Declare Instance string_of_t : ToString t.
End AB_REG_MAP.

Module MREG_ordered <: OrderedType.OrderedType.
  Definition t := mreg.
  Definition eq := @eq mreg.
  Definition eq_refl := @eq_refl mreg.
  Definition eq_sym := @eq_sym mreg.
  Definition eq_trans := @eq_trans mreg.
  Definition lt x y := Plt (IndexedMreg.index x) (IndexedMreg.index y).
  Definition lt_trans := fun x y z => Plt_trans (IndexedMreg.index x) (IndexedMreg.index y) (IndexedMreg.index z).
  Definition lt_not_eq : forall x y, lt x y -> ~ eq x y.
  Proof. intros. red; intros. inv H0. red in H. xomega. Defined.
  Definition eq_dec := mreg_eq.
  Definition compare : forall x y, OrderedType.Compare lt eq x y.
  Proof.
    intros. destruct (eq_dec x y).
    - constructor 2; auto.
    - destruct (plt (IndexedMreg.index x) (IndexedMreg.index y)).
      + constructor 1; auto.
      + constructor 3; auto. destruct (peq (IndexedMreg.index x) (IndexedMreg.index y)).
        * elim n. eapply IndexedMreg.index_inj; auto.
        * red. xomega. Defined.
End MREG_ordered.
  
Module AbRegMap : AB_REG_MAP.
  (*Definition t : Type := set mreg.
  Definition empty : t := {}.
  Definition get (s: t) (r: mreg) : sec_level :=
    if mem r s then High else Low.
  Definition set (s: t) (r: mreg) (v: sec_level) : t :=
    match v with
    | Low => remove r s
    | High => add r s
    end.*)
  Module A := FSetAVL.Make MREG_ordered.
  Module AP := SetProp A.
  Definition t := A.t.
  Definition eq := A.eq.
  Instance equiv : Equivalence eq.
  Proof. split. exact A.eq_refl. exact A.eq_sym. exact A.eq_trans. Defined.
  Definition t_dec := A.eq_dec.
  Definition empty := A.empty.
  Definition get (s: t) (r: mreg) : sec_level :=
    if A.mem r s then High else Low.
  Definition set (s: t) (r: mreg) (v: sec_level) : t :=
    match v with
    | Low => A.remove r s
    | High => A.add r s
    end.

  Definition union := A.union.

  Instance get_m : Proper (eq ==> Logic.eq ==> Logic.eq) get.
  Proof.
    intros s s' EQ r ? <-.
    unfold get. rewrite EQ. reflexivity.
  Qed.

  Definition gempty r : get empty r = Low := eq_refl.

  Lemma gs x r v r' : get (set x r v) r' = if mreg_eq r r' then v else get x r'.
  Proof.
    unfold get, set.
    case mreg_eq. intros <-.
    case v; case AP.mem_In; auto.
    intros H; elim (A.remove_1 eq_refl H).
    intros H; elim (H (A.add_1 _ eq_refl)).
    intros NE.
    case v; repeat case AP.mem_In; auto.
    intros K H. elim (K (A.remove_3 H)).
    intros H K. elim (K (A.remove_2 NE H)).
    intros K H. elim (K (A.add_3 NE H)).
    intros H K. elim (K (A.add_2 _ H)).
  Qed.

  Lemma gunion x y r : get (union x y) r = get x r ∪ get y r.
  Proof.
    unfold get, union.
    case AP.mem_In.
    intros H; apply A.union_1 in H; destruct H as [ H | H ]; rewrite (reflect_iff _ _ (AP.mem_In _ _)) in H; rewrite H.
    reflexivity. rewrite max_sec_level_comm. reflexivity.
    intros H.
    case AP.mem_In. intros K; elim (H (A.union_2 _ K)). intros _.
    case AP.mem_In. intros K; elim (H (A.union_3 _ K)). reflexivity.
  Qed.

  Instance string_of_t : ToString t := _.
End AbRegMap.

Local Coercion AbRegMap.get : AbRegMap.t >-> Funclass.

Module Type AB_MEM_MAP.
  Axiom t : Type.
  Axiom eq : t → t → Prop.
  Declare Instance equiv : Equivalence eq.
  Axiom t_dec : ∀ x x', { eq x x' } + { ¬ eq x x' }.
  Axiom empty : t.
  Axiom get : t -> ab_cell -> sec_level.
  Axiom set : t -> ab_cell -> sec_level -> t.
  Axiom union : t → t → t.
  Axiom push : t -> t.
  Axiom pop : t -> t.

  Declare Instance get_m : Proper (eq ==> Logic.eq ==> Logic.eq) get.
  Axiom gempty : ∀ r, get empty r = Low.
  Axiom gunion : ∀ x y r, get (union x y) r = get x r ∪ get y r.

  Axiom gpush : ∀ x r, get (push x) r = match r with Global _ _ => get x r |
                                                Stack (S n) ofs => get x (Stack n ofs) |
                                                Stack O _ => Low end.
  Axiom gpop : ∀ x r, get (pop x) r = match r with Global _ _ => get x r |
                                              Stack n ofs => get x (Stack (S n) ofs) end.

  Declare Instance string_of_t : ToString t.
End AB_MEM_MAP.

Module AbMemMap : AB_MEM_MAP.
  Module PZ_ordered := OrderedTypeEx.PairOrderedType (OrderedTypeEx.Positive_as_OT) (OrderedTypeEx.Z_as_OT).
  Module A := FSetAVL.Make PZ_ordered.
  Module B := FSetAVL.Make OrderedTypeEx.Z_as_OT.

  Definition t := (A.t * list B.t)%type.
  Definition eq := fun x y => A.eq (fst x) (fst y) /\ list_forall2 B.eq (snd x) (snd y).
  Lemma list_forall2_dec:
    forall A B (R: A -> B -> Prop ) (R_dec: forall x y, { R x y } + { ~ R x y }) l1 l2,
      { list_forall2 R l1 l2 } + { ~ list_forall2 R l1 l2 }.
  Proof.
    induction l1; intros.
    - destruct l2.
      + left; constructor.
      + right; red; intros; inv H.
    - destruct l2.
      + right; red; intros; inv H.
      + destruct (IHl1 l2).
        * destruct (R_dec a b).
          { left; constructor; auto. }
          { right; red; intros; inv H; auto. }
        * right; red; intros; inv H; auto.
  Qed.
  Lemma t_dec : forall x y, { eq x y } + { ~ eq x y }.
  Proof.
    intros; destruct (A.eq_dec (fst x) (fst y)).
    - destruct (list_forall2_dec _ _ B.eq B.eq_dec (snd x) (snd y)).
      + left; split; auto.
      + right; red; intros; destruct H; auto.
    - right; red; intros; destruct H; auto.
  Defined.
  Lemma list_forall2_sym:
    forall A (R: A -> A -> Prop) (R_sym: forall a b, R a b -> R b a) l1 l2,
      list_forall2 R l1 l2 ->
      list_forall2 R l2 l1.
  Proof. induction l1; intros; inv H; constructor; auto. Qed.
  Lemma list_forall2_trans:
    forall A (R: A -> A -> Prop) (R_trans: forall a b c, R a b -> R b c -> R a c) l1 l2 l3,
      list_forall2 R l1 l2 ->
      list_forall2 R l2 l3 ->
      list_forall2 R l1 l3.
  Proof. induction l1; intros; inv H; inv H0; constructor; eauto. Qed.
  Instance equiv: Equivalence eq.
  Proof.
    split.
    - red; intros; split.
      + apply A.eq_refl.
      + induction (snd x); constructor; auto.
        apply B.eq_refl.
    - red; intros; destruct H; split.
      + apply A.eq_sym; auto.
      + apply list_forall2_sym; auto. exact B.eq_sym.
    - red; intros. destruct H; destruct H0; split.
      + eapply A.eq_trans; eauto.
      + eapply list_forall2_trans; eauto. exact B.eq_trans.
  Defined.
  Definition empty := (A.empty, @nil B.t).
  Definition get (s: t) (r: ab_cell): sec_level :=
    match r with
    | Global id ofs => if A.mem (id, ofs) (fst s) then High else Low
    | Stack n ofs => match nth_error (snd s) n with
                    | None => Low
                    | Some s => if B.mem ofs s then High else Low
                    end
    end.
  (* Not tail recursive ! *)
  Fixpoint change_stack (k: Z -> B.t -> B.t) (n: nat) (ofs: Z) (l: list B.t): list B.t :=
    match l with
    | nil => nil
    | s::l => match n with
             | O => (k ofs s)::l
             | S n => s::(change_stack k n ofs l)
             end
    end.
  Definition set (s: t) (r: ab_cell) (v: sec_level): t :=
    match v with
    | Low =>
      match r with
      | Global id ofs => (A.remove (id, ofs) (fst s), snd s)
      | Stack n ofs => (fst s, change_stack B.remove n ofs (snd s))
      end
    | High =>
      match r with
      | Global id ofs => (A.add (id, ofs) (fst s), snd s)
      | Stack n ofs => (fst s, change_stack B.add n ofs (snd s))
      end
    end.
  Fixpoint map2 { A } (f: A -> A -> A) (l1 l2: list A): list A :=
    match l1 with
    | nil => l2
    | a::l1 => match l2 with
              | nil => a::l1
              | b::l2 => (f a b)::(map2 f l1 l2)
              end
    end.
  Definition union (x y: t): t := (A.union (fst x) (fst y), map2 B.union (snd x) (snd y)).
  Definition push (x: t): t := (fst x, B.empty::(snd x)).
  Definition pop (x: t): t :=
    match snd x with
    | nil => x
    | a::l => (fst x, l)
    end.
  Lemma list_forall2_nth_error:
    forall A B (R: A -> B -> Prop) l1 n l2,
      list_forall2 R l1 l2 ->
      match nth_error l1 n with
      | Some x => exists y, nth_error l2 n = Some y /\ R x y
      | None => nth_error l2 n = None
      end.
  Proof.
    induction l1; intros.
    - inv H. destruct n; simpl; auto.
    - inv H. destruct n; simpl; eauto.
      eapply IHl1; eauto.
  Qed.
  Instance get_m : Proper (eq ==> Logic.eq ==> Logic.eq) get.
  Proof.
    intros s s' EQ r ? <-.
    destruct s, s'; destruct EQ.
    unfold get; destruct r; simpl in *.
    - rewrite H; auto.
    - generalize (list_forall2_nth_error _ _ _ _ H1 _ H0).
      destruct (nth_error l H1); intros.
      + destruct H3 as [y [X Y]]. rewrite X; rewrite Y; auto.
      + rewrite H3; auto.
  Defined.
  Definition gempty : ∀ r, get empty r = Low.
  Proof.
    unfold empty, get; simpl; intros.
    destruct r; auto. destruct H; reflexivity.
  Defined.
  Lemma nth_error_map2:
    forall A (f: A -> A -> A) l1 n l2,
      match nth_error (map2 f l1 l2) n with
      | Some x => (exists a b, nth_error l1 n = Some a /\ nth_error l2 n = Some b /\ f a b = x) \/
                 (nth_error l1 n = None /\ nth_error l2 n = Some x) \/
                 (nth_error l1 n = Some x /\ nth_error l2 n = None)
      | None => nth_error l1 n = None /\ nth_error l2 n = None
      end.
  Proof.
    induction l1; simpl; intros.
    - destruct n; simpl; auto.
      + destruct l2; simpl; auto.
      + destruct l2; simpl; auto. destruct (nth_error l2 n); auto.
    - destruct l2; simpl; auto.
      + destruct n; simpl; auto.
        destruct (nth_error l1 n); auto.
      + destruct n; simpl; auto.
        * left; eauto.
        * eapply IHl1; eauto.
  Qed.
  Definition gunion : ∀ x y r, get (union x y) r = get x r ∪ get y r.
  Proof.
    unfold get, union; simpl; intros; destruct r.
    - case_eq (A.mem (H, H0) (fst x)); intros.
      + simpl. generalize (A.mem_2 H1); intros.
        generalize (A.union_2 (fst y) H2); intros.
        generalize (A.mem_1 H3); intros. rewrite H4; auto.
      + case_eq (A.mem (H, H0) (fst y)); intros.
        * simpl. generalize (A.mem_2 H2); intros.
          generalize (A.union_3 (fst x) H3); intros.
          generalize (A.mem_1 H4); intros. rewrite H5; auto.
        * simpl. case_eq (A.mem (H, H0) (A.union (fst x) (fst y))); intros; auto.
          apply A.mem_2 in H3. apply A.union_1 in H3.
          destruct H3; apply A.mem_1 in H3; congruence.
    - generalize (nth_error_map2 _ B.union (snd x) H (snd y)); intros.
      destruct (nth_error (map2 B.union (snd x) (snd y)) H).
      + destruct H1 as [H1 | [H1 | H1]].
        * destruct H1 as [a [b [H1 [H2 H3]]]]. rewrite H1, H2, <- H3.
          case_eq (B.mem H0 a); intros.
          { simpl. generalize (B.mem_2 H4); intros.
            generalize (B.union_2 b H5); intros.
            generalize (B.mem_1 H6); intros. rewrite H7; auto. }
          { simpl. case_eq (B.mem H0 b); intros.
            - simpl. generalize (B.mem_2 H5); intros.
              generalize (B.union_3 a H6); intros.
              generalize (B.mem_1 H7); intros. rewrite H8; auto.
            - simpl. case_eq (B.mem H0 (B.union a b)); intros; auto.
              apply B.mem_2 in H6. apply B.union_1 in H6.
              destruct H6; apply B.mem_1 in H6; congruence. }
        * destruct H1 as [H1 H2]; rewrite H1, H2. simpl; auto.
        * destruct H1 as [H1 H2]; rewrite H1, H2. simpl; auto.
          destruct (B.mem H0 t0); simpl; auto.
      + destruct H1 as [H1 H2]. rewrite H1, H2; simpl; auto.
  Defined.
  Definition gpush : ∀ x r, get (push x) r = match r with Global _ _ => get x r |
                                                     Stack (S n) ofs => get x (Stack n ofs) |
                                                     Stack O _ => Low end.
  Proof.
    unfold push; destruct r; intros; simpl; auto.
    destruct H; auto.
  Defined.
  Definition gpop : ∀ x r, get (pop x) r = match r with Global _ _ => get x r |
                                                   Stack n ofs => get x (Stack (S n) ofs) end.
  Proof.
    unfold pop; destruct r; intros; simpl; auto.
    - destruct x. destruct l; simpl; auto.
    - destruct x; simpl; auto. destruct l; simpl; auto.
      destruct H; auto.
  Defined.

  Module BP := SetProp B.
  Instance string_of_t : ToString t :=
    λ x, to_string (snd x).

End AbMemMap.

Definition stealth_var := Regset.t.

Definition sec_le (s1 s2:sec_level) : Prop :=
  s1=Low \/ s2=High.

Definition get_args_level (rm: AbRegMap.t) (args: list mreg) : sec_level :=
  fold_left (λ v r, v ∪ rm r) args Low.

Notation "vl '##t' x " := (get_args_level vl x) (at level 1).

Definition max_levels (l:list sec_level) : sec_level :=
  fold_left max_sec_level l Low.

Module Inference.

Require Import Lattice.
Require Import Kildall.

Definition call_site : Type := (ident * node)%type.

Record state : Type := State {
    reg: AbRegMap.t;
    mem: AbMemMap.t;
    context: list call_site; (* the call stack, to use context-sensitive points-to information *)
    alarms: list Errors.errmsg
  }.

(* Discriminate between an empty list of alarms and a non-empty one.
It is OK to forget some alarms, but not all. *)
Definition alarms_eq {X} (a a': list X) : Prop :=
  match a, a' with
  | nil, nil | _ :: _, _ :: _ => True
  | _, _ => False
  end.

Instance alarms_equiv {X} : Equivalence (@alarms_eq X).
Proof.
  constructor.
  - intros (); vauto.
  - intros [ | a b ] [ | a' b' ]; exact id.
  - intros [ | a b ] [ | a' b' ] z (); destruct z as [ | ? ? ]; exact id.
Qed.

Definition alarms_eqb {X} (a a': list X) : bool :=
  if a then if a' then true else false else if a' then false else true.

Remark alarmsP {X} (a a': list X) : reflect (alarms_eq a a') (alarms_eqb a a').
Proof. case a, a'; vauto. Defined.

Definition state_eq (s s': state) : Prop :=
  AbRegMap.eq (reg s) (reg s') ∧
  AbMemMap.eq (mem s) (mem s') ∧
  context s = context s' ∧
  alarms_eq (alarms s) (alarms s').

Instance  state_equiv : Equivalence state_eq.
Proof.
  constructor.
  - intros x. repeat split; reflexivity.
  - intros x y EQ. repeat split; symmetry; apply EQ.
  - intros x y z Hxy Hyz. repeat split; (etransitivity; [ apply Hxy | apply Hyz ]).
Qed.

Definition state_eq_dec (s s': state) : { state_eq s s' } + { ¬ state_eq s s' }.
Proof.
  refine (
  let 'State r m c a := s in
  let 'State r' m' c' a' := s' in
  _).
  unfold state_eq. simpl.
  case (AbRegMap.t_dec r r').
  2: clear; intros NE; right; abstract (intros (K & _); auto).
  intros EQr.
  case (AbMemMap.t_dec m m').
  2: clear; intros NE; right; abstract (intros (_ & K & _); auto).
  intros EQm.
  case (list_eq_dec eq_dec c c').
  2: clear; intros NE; right; abstract (intros (_ & _ & K & _); auto).
  intros EQc.
  generalize (reflect_iff _ _ (alarmsP a a')).
  case (alarms_eqb a a').
  2: clear; intros [NE _]; right; abstract (intros (_ & _ & _ & K); specialize (NE K); eq_some_inv).
  intros [_ EQa]. specialize (EQa eq_refl).
  auto.
Defined.

Definition state_ge (s s': state) : Prop :=
  (∀ r, reg s' r = High → reg s r = High) ∧
  (∀ c, AbMemMap.get (mem s') c = High → AbMemMap.get (mem s) c = High).

Definition empty_state : state :=
  {| reg := AbRegMap.empty;
     mem := AbMemMap.empty;
     context := nil;
     alarms := nil |}.

Definition upd_reg (s: state) (f: AbRegMap.t → AbRegMap.t) : state :=
  {| reg := f (reg s); mem := mem s; context := context s; alarms := alarms s |}.

Definition upd_mem (s: state) (f: AbMemMap.t → AbMemMap.t) : state :=
  {| reg := reg s; mem := f (mem s); context := context s; alarms := alarms s |}.

Definition upd_alarms (s: state) (f: list Errors.errmsg → list Errors.errmsg) : state :=
  {| reg := reg s; mem := mem s; context := context s; alarms := f (alarms s) |}.

Definition push (f: ident) (n: node) (s: state) : state :=
  {| reg := reg s; mem := AbMemMap.push (mem s); context := (f, n) :: context s; alarms := alarms s |}.

Definition pop (s s': state) : state :=
  {| reg := reg s'; mem := AbMemMap.pop (mem s'); context := context s; alarms := alarms s' |}.

Module D0 : SEMILATTICE
                     with Definition t := state
.

  Definition t : Type := state.
  Definition eq := state_eq.

  Instance eq_refl : Reflexive eq := _.
  Instance eq_sym : Symmetric eq := _.
  Instance eq_trans : Transitive eq := _.

  Definition beq (s s': t) : bool := state_eq_dec s s'.

  Lemma beq_correct s s' : beq s s' = true → eq s s'.
  Proof.
    unfold beq. case state_eq_dec; simpl. auto.
    intros; eq_some_inv.
  Qed.

  Definition ge := state_ge.

  Lemma ge_refl s s' : eq s s' → ge s s'.
  Proof.
    intros (EQr & EQm & EQc). repeat split.
    - intros r H. rewrite EQr. exact H.
    - intros c H. rewrite EQm. exact H.
  Qed.

  Instance ge_trans : Transitive ge.
  Proof.
    intros x y z (Hr & Hm) (Hr' & Hm').
    repeat split; firstorder.
  Qed.

  Definition bot : state := empty_state.

  Lemma ge_bot x : ge x bot.
  Proof.
    unfold bot, empty_state.
    repeat split; simpl.
    - intros r. rewrite AbRegMap.gempty. apply Low_not_High.
    - intros c. rewrite AbMemMap.gempty. apply Low_not_High.
  Qed.

  Definition lub (s s': t) : t :=
    {| reg := AbRegMap.union (reg s) (reg s');
       mem := AbMemMap.union (mem s) (mem s');
       context := context s;
       alarms := rev_append (alarms s) (alarms s') (* TODO: this might introduce repetitions *)
    |}.

  Lemma ge_lub_left s s' : ge (lub s s') s.
  Proof.
    repeat split; simpl.
    - intros r H. rewrite AbRegMap.gunion, H; reflexivity.
    - intros r H. rewrite AbMemMap.gunion, H; reflexivity.
  Qed.

  Lemma ge_lub_right s s' : ge (lub s s') s'.
  Proof.
    repeat split; simpl.
    - intros r H. rewrite AbRegMap.gunion, H, max_sec_level_comm; reflexivity.
    - intros r H. rewrite AbMemMap.gunion, H, max_sec_level_comm; reflexivity.
  Qed.

End D0.

Module D : SEMILATTICE with Definition t := option state :=
  LOption D0.

Module DS := Dataflow_Solver(D)(NodeSetForward).

Section FOR_LOOP.
  Context {X : Type}
          (body : Z → X → X)
          (hi : Z).

  Function for_loop (lo: Z) (x: X) {measure (λ lo, Z.to_nat (hi - lo)) lo} : X :=
    if lo <? hi
    then for_loop (Z.succ lo) (body lo x)
    else x.
  Proof.
    abstract (
    intros lo _;
    case Z.ltb_spec;
      [ intros LT _; apply Z2Nat.inj_lt; Psatz.lia
      | intros _ K; exact (let 'eq_refl := K in I) ]
      ).
  Defined.
  
End FOR_LOOP.

Definition split_cell (c: ab_cell) : Z * (Z → ab_cell) :=
  match c with
  | Global s o => (o, Global s)
  | Stack n o => (o, Stack n)
  end.

Definition load_cells (mm: AbMemMap.t) (κ: Z) (v: sec_level) (h: points_to_hint) : sec_level :=
  let '(c, sz) := h in
  let '(base, c) := split_cell c in
  for_loop
    (λ ofs v,
     v ∪ AbMemMap.get mm (c ofs)
    ) (base + sz + κ) base v.

Definition load_all (mm: AbMemMap.t) (κ: Z) :
  list points_to_hint → sec_level → sec_level :=
  List.fold_left (load_cells mm κ).

Definition set_cells (v: sec_level) (κ: Z) (mm: AbMemMap.t) (h: points_to_hint) : AbMemMap.t :=
  let '(c, sz) := h in
  let '(base, c) := split_cell c in
  for_loop
    (λ ofs mm,
     AbMemMap.set mm (c ofs) v
    ) (base + sz + κ) base mm.

Definition is_strong_update (h: list points_to_hint) : option points_to_hint :=
  match h with
  | (c, 0) as x :: nil => Some x
  | _ => None
  end.

Definition store_all (mm: AbMemMap.t) (h: list points_to_hint) (κ: Z) (v: sec_level) :
  AbMemMap.t :=
  match v with
  | Low =>
    match is_strong_update h with
    | None => mm
    | Some x => set_cells Low κ mm x
    end
  | High => List.fold_left (set_cells High κ) h mm
  end.

Definition resolve_function_symbol (ge: Genv.t _ unit) (f: ident) : option fundef :=
  match Genv.find_symbol ge f with
  | None => None
  | Some b => Genv.find_funct_ptr ge b 
  end.

Section GE.

Variable prog : MachIR.program.
Variable ge: Genv.t fundef unit.

Definition is_volatile (g: ident) : bool :=
  match assoc g (prog_defs prog) with
  | Some (Gvar gv) => gvar_volatile gv
  | _ => false
  end.

Variable level_of_global : ident → sec_level.
Variable white_list : ident → bool.

Context (points_to:
           list call_site → (* context *)
           ident → node → (* current program point *)
           Op.addressing → list mreg → (* address *)
           option (list points_to_hint)).

Section ANALYZE.
Variable analyze : ident → function → D.t → D.t.

Context (curr: ident).

Definition set_regs (s: state) dst v :=
  upd_reg s (List.fold_left (λ rm d, AbRegMap.set rm d v) dst).

Definition transfer (f: function) (pc: node) (is: D.t) : D.t :=
  match is with None => is | Some s =>
  match (fn_code f)!pc with
  | None => is
  | Some i =>
    match i with
    | MIop op args dest _ => Some (upd_reg s (λ rm, AbRegMap.set rm dest (rm##t args)))
    | MIload κ addr args dst _ =>
      let v := match points_to (context s) curr pc addr args with
               | None => High
               | Some src => load_all (mem s) (size_chunk κ) src ((reg s) ##t args)
               end in
      Some (upd_reg s (λ rm, AbRegMap.set rm dst v))
    | MIstore κ addr args src _ =>
      match points_to (context s) curr pc addr args with
      | None => None
      | Some dst =>
        let rg := reg s in
        let v := rg src ∪ rg ##t args in
        Some (upd_mem s (λ mm, store_all mm dst (size_chunk κ) v))
      end
    | MIgetparam ofs ty dst _ =>
      match
        match context s with
        | (caller, _) :: _ => resolve_function_symbol ge caller
        | _ => None
        end
      with
      | Some (Internal caller) =>
      let src := (Stack 1 (Int.unsigned ofs), 0) :: nil in
      let κ := chunk_of_type ty in
      let v := load_all (mem s) (size_chunk κ) src Low in
      Some (upd_reg s (λ rm, AbRegMap.set rm dst v))
      | _ => None
      end
    | MIcall sg (inr callee_name) _ =>
      match resolve_function_symbol ge callee_name with
      | None => is
      | Some (Internal callee) =>
        option_map (pop s) (analyze callee_name callee (Some (push curr pc s)))
      | Some (External (EF_external ef _)) =>
        if white_list ef then is else None
      | Some (External ef) => None
      end
    | MIcall _ (inl _) _ => None
    | MIbuiltin (EF_external _ _ | EF_malloc | EF_free | EF_memcpy _ _ | EF_inline_asm _) _ _ _
      => None
    | MIbuiltin (EF_builtin b imms sg) args dst _ =>
      match classify_builtin b imms sg dst args with
      | BuiltinPure args dst => 
        let v := (reg s) ##t args in
        Some (set_regs s dst v)
      | BuiltinLoad ptr sz ar _ =>
        match dst with
        | dst :: nil =>
          let v := match points_to (context s) curr pc (Aindexed Int.zero) (ptr :: nil) with
                   | None => High
                   | Some src => load_all (mem s) sz src ((reg s) ##t args)
                   end in
          Some (upd_reg s (λ rm, AbRegMap.set rm dst v))
        | _ => None end
      | BuiltinStore ptr sz ar _ =>
        match ar with
        | src :: nil =>
        match points_to (context s) curr pc (Aindexed Int.zero) (ptr :: nil) with
        | None => None
        | Some dst =>
          let rg := reg s in
          let v := rg src ∪ rg ##t args in
          Some (upd_mem s (λ mm, store_all mm dst sz v))
        end
        | _ => None end
      | BuiltinUnknown
      | BuiltinUnsupported => None
      end
    | MIbuiltin (EF_annot _ _) _ _ _ => is
    | MIbuiltin (EF_vload_global _ g _) _ dst _ =>
      if is_volatile g
      then Some (set_regs s dst (level_of_global g))
      else None
    | MIbuiltin (EF_vload _) _ _ _ => None
    | MIbuiltin (EF_vstore_global _ g _) _ _ _ =>
      if is_volatile g then is else None
    | MIbuiltin (EF_vstore _) _ _ _ => None
    | MIbuiltin (EF_annot_val _ _) args dst _ =>
      let v := (reg s) ##t args in
      Some (set_regs s dst v)
    | MIannot (EF_annot _ _) _ _ => is
    | MIannot _ _ _ => None
    | MIjumptable _ _
    | MIgoto _
    | MIcond _ _ _ _
    | MIreturn
    | MItailcall _ _
      => is
    end
  end
  end.

End ANALYZE.

Definition collect_result (fn: function) (res: PMap.t D.t) : D.t :=
  PTree.fold
    (λ vl pc i,
     match i with
     | MIreturn => D.lub vl (PMap.get pc res)
     | _ => vl
     end
    )
    (fn_code fn)
    (Some empty_state).

Variable sv : stealth_var.

Definition is_stealth : list points_to_hint → bool :=
  List.forallb
    (λ h,
     match h with
     | (Global g _, _) => Regset.mem g sv
     | (Stack _ _, _) => false
     end).

Definition format_context curr pc (ctx: list call_site) : list Errors.errcode :=
  List.fold_left
    (λ r c,
     let '(f, pc) := c in
     Errors.CTX f :: Errors.MSG ": " :: Errors.POS pc :: Errors.MSG " / " :: r)
    ctx
    (Errors.CTX curr :: Errors.MSG ": " :: Errors.POS pc :: nil).

Definition error curr pc (ctx: list call_site) a :=
  (Errors.MSG "Not constant-time: " :: format_context curr pc ctx) :: a.

Definition assert_low curr (pc: node) (ctx: list call_site) (a: list Errors.errmsg) (v: sec_level) : list Errors.errmsg :=
  match v with
  | Low => a
  | High => error curr pc ctx a
  end.

Definition policy_check_one curr (res: D.t) (a: list Errors.errmsg) (pc: node) (i: instruction) : list Errors.errmsg :=
  let assert_low args :=
      match res with
      | None => error curr pc nil a
      | Some s =>
        let v := get_args_level (reg s) args in
        assert_low curr pc (context s) a v
      end
  in
  match i with
  | MIop _ _ _ _
  | MIgoto _
  | MIcall _ _ _
  | MIgetparam _ _ _ _
  | MItailcall _ _
  | MIannot _ _ _
  | MIreturn
    => a
  | MIload _ addr args _ _
  | MIstore _ addr args _ _
    =>
    match res with
    | None => error curr pc nil a
    | Some s =>
      match points_to (context s) curr pc addr args with
      | None => assert_low args
      | Some h => if is_stealth h then a else assert_low args
      end
    end
  | MIcond _ args _ _ => assert_low args
  | MIjumptable x _ => assert_low (x :: nil)
  | MIbuiltin ef args dst _ =>
    match ef with
    | EF_builtin blt imms sg =>
      match classify_builtin blt imms sg dst args with
      | BuiltinPure _ _ => a
      | BuiltinLoad ptr _ _ _
      | BuiltinStore ptr _ _ _
        =>
        match res with
        | None => error curr pc nil a
        | Some s =>
          match points_to (context s) curr pc (Aindexed Int.zero) (ptr :: nil) with
          | None => assert_low (ptr :: nil)
          | Some h => if is_stealth h then a else assert_low (ptr :: nil)
          end
        end
      | BuiltinUnsupported | BuiltinUnknown => a
      end
    | _ => (* TODO *) a
    end
  end.

Definition policy_check (curr: ident) (fn: function) (res: PMap.t D.t) : list Errors.errmsg :=
  PTree.fold (λ a pc i,
              let s := PMap.get pc res in
              policy_check_one curr s a pc i)
             (fn_code fn)
             nil.

Fixpoint iter (n: nat) {struct n} :
  ident → function → D.t → D.t :=
  match n with
  | O => λ _ _ _, None
  | S n' =>
    λ curr fn init,
    match DS.fixpoint (fn_code fn) successors (transfer (iter n') curr fn) (fn_entrypoint fn) init with
    | None => None
    | Some flow_sensitive_result =>
      let a := policy_check curr fn flow_sensitive_result in
      let s := collect_result fn flow_sensitive_result in
      match a with
      | nil => s
      | _ => option_map (λ s, upd_alarms s (app a)) s
      end
    end
  end.

End GE.

Definition sizeof (p: program) (g: AST.ident) : Z :=
  match assoc g (AST.prog_defs p) with
  | Some (AST.Gvar gv) => Genv.init_data_list_size (AST.gvar_init gv)
  | _ => 1
  end.

Definition sizeof' p g : Z :=
  Z.max 0 (Z.min (sizeof p g - 1) Int.max_unsigned).

Definition init_ab_mem (p: program) (secret: list ident) :=
  List.fold_left (λ mm g, store_all mm ((Global g 0, sizeof' p g) :: nil) 1 High)
                 secret AbMemMap.empty.

Definition init_state (p: program) (secret: list ident) : D.t :=
  Some
  {| reg := AbRegMap.empty;
     mem := AbMemMap.push (init_ab_mem p secret);
     context := nil;
     alarms := nil |}.

Definition run (p: program) bal (sv: stealth_var) (secret: list ident) pth (fuel: nat) : D.t :=
  let ge := Genv.globalenv p in
  match resolve_function_symbol ge (prog_main p) with
  | Some (Internal main) =>
    let level_of_global g :=
        if In_dec eq_dec g secret then High else Low
    in
    iter p ge level_of_global bal pth sv fuel (prog_main p) main (init_state p secret)
  | _ => None
  end.

End Inference.
