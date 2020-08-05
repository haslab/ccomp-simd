(* *********************************************************************)
(*                                                                     *)
(*              The Verasco static analyzer                            *)
(*                                                                     *)
(*          Vincent Laporte, Université de Rennes 1                    *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique and Université de Rennes 1.  All rights reserved.      *)
(*  This file is distributed under the terms of the GNU General        *)
(*  Public License as published by the Free Software Foundation,       *)
(*  either version 2 of the License, or (at your option) any later     *)
(*  version.  This file is also distributed under the terms of the     *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

Require Import Utf8 List ZArith AST.
Import Coqlib.
Require Psatz.

Set Implicit Arguments.

(** * Useful tactics. *)
Ltac bif :=
  match goal with |- context[if ?a then _ else _] => destruct a end; try congruence.

Ltac bif' :=
  match goal with |- context[if ?a then _ else _] => destruct a eqn: ? end; try congruence.

Ltac vauto := (econstructor (eauto; (econstructor (eauto; fail)))) || idtac.
Ltac vauto2 := econstructor (eauto; vauto; fail).

Ltac hsplit :=
  repeat match goal with
  | H : _ ∧ _ |- _ => destruct H as (H & ?)
  | H : ∃ a , _ |- _ => let a := fresh a in destruct H as (a, H)
  end.


(** * Basic inversion principles. *)
Section INV.

  Variables A B C : Type.

  Definition some_eq_inv (x y: A) :
    Some x = Some y → x = y :=
    λ H, match H with eq_refl => eq_refl _ end.

  Lemma None_not_Some (v: A) :
    None = Some v → ∀ X : Prop, X.
  Proof (λ H, match H with eq_refl => I end).

  Definition inl_eq_inv (x y: A) :
    (inl x :A + B) = inl y → x = y :=
    λ H, match H with eq_refl => eq_refl _ end.

  Definition inr_eq_inv (x y: B) :
    (inr x :A + B) = inr y → x = y :=
    λ H, match H with eq_refl => eq_refl _ end.

  Lemma inl_not_inr (a: A) (b: B) : inl a = inr b → ∀ P : Prop, P.
  Proof (λ H, match H in _ = b return if b then _ else _ with eq_refl => I end).

  Lemma false_eq_true_False : false ≠ true.
  Proof (λ H, match H in _ = b return if b then False else True with eq_refl => I end).

  Lemma false_not_true : false = true → ∀ P : Prop, P.
  Proof (λ H, match H in _ = b return if b then _ else _ with eq_refl => I end).

  Definition pair_eq_inv (x:A) (y:B) z w :
    (x,y) = (z,w) → x = z ∧ y = w :=
    λ H, match H with eq_refl => conj eq_refl eq_refl end.

  Definition triple_eq_inv (x: A) (y: B) (z: C) x' y' z' :
    (x,y,z) = (x',y',z') → (x = x' ∧ y = y') ∧ z = z' :=
    λ H, match H with eq_refl => conj (pair_eq_inv eq_refl) eq_refl end.

  Definition cons_eq_inv (x x': A) (l l': list A) :
    x :: l = x' :: l' → x = x' ∧ l = l' :=
    λ H, match H in _ = a return match a with nil => True | y :: m => x = y ∧ l = m end with eq_refl => conj eq_refl eq_refl end.

  Definition cons_nil_inv (x : A) (l: list A) :
    x :: l = nil → ∀ P : Prop, P :=
    λ H, match H in _ = a return match a with nil => ∀ P, P | _ => True end with eq_refl => I end.

  Definition snoc_eq_inv (x x': A) (l l': list A) :
    l ++ x :: nil = l' ++ x' :: nil → l = l' ∧ x = x'.
  Proof.
    revert l'. induction l as [ | a l IH ]; intros [ | b l' ]; simpl. intuition congruence.
    intros K. apply cons_eq_inv in K. destruct K as [ _ K ].
    destruct l'; apply (cons_nil_inv (eq_sym K)).
    intros K. apply cons_eq_inv in K. destruct K as [ _ K ].
    destruct l; apply (cons_nil_inv K).
    intros K. apply cons_eq_inv in K. destruct K as (<- & K).
    apply IH in K. intuition congruence.
  Qed.

  Lemma rev_nil : ∀ l : list A, rev l = nil → l = nil.
  Proof.
    destruct l as [|x l]. reflexivity.
    simpl. destruct (rev l); simpl; refine (λ K, cons_nil_inv K _).
  Qed.

  Lemma app_nil : ∀ m n : list A, m ++ n = nil → m = nil ∧ n = nil.
  Proof.
    intros [ | a m ] [ | a' n ] X;
    exact (conj eq_refl eq_refl) || exact (cons_nil_inv X _).
  Qed.

  Definition eq_dec_of_beq (beq: A → A → bool) (beq_correct: ∀ a b : A, beq a b = true ↔ a = b)
             (x y: A) : { x = y } + { x ≠ y } :=
    (if beq x y as b return (b = true <-> x = y) → { x = y } + { x ≠ y }
     then λ H, left (proj1 H eq_refl)
     else λ H, right (λ K, false_eq_true_False (proj2 H K)))
      (beq_correct x y).

End INV.

Definition option_map_some A B (f: A → B) o b : option_map f o = Some b → ∃ a, o = Some a ∧ f a = b :=
  match o return option_map f o = Some b → _
  with Some a' => λ H: Some (f a') = Some b, ex_intro _ a' (conj eq_refl (some_eq_inv H))
  | None => λ H, None_not_Some H _ end.

Definition option_map_none A B (f: A → B) o : option_map f o = None → o = None :=
  match o return option_map f o = None → _
  with Some a' => λ H, None_not_Some (eq_sym H) _
  | None => λ H, eq_refl end.
(** * The monad type class *)

Class monad (M:Type -> Type) : Type :=
  { ret: forall {A:Type}, A -> M A;
    bind: forall {A B:Type}, M A -> (A -> M B) -> M B }.
Arguments bind {M !_ A B} !x f.
Notation "'do' X <- A ; B" :=
  (bind A (fun X => B))
    (at level 200, X ident, A at level 100, B at level 200).
Notation "'do' ( X ,  Y ) <- A ; B" := (bind A (fun XY => let '(X, Y) := XY in B))
  (at level 200, X ident, Y ident, A at level 100, B at level 200).
Definition fmap {M} {m:monad M} {A B:Type} (f:A -> B) (x:M A) : M B :=
  bind x (fun x => ret (f x)).
Arguments fmap {M !_ A B} f !x.

(** * The option monad *)

Instance option_monad : monad option :=
  { ret := @Some;
    bind A B x f :=
      match x with
      | None => None
      | Some x => f x
      end }.

Lemma do_opt_some_inv {A B} a (f: A → option B) b :
  (do x <- a; f x) = Some b →
  ∃ x, a = Some x ∧ f x = Some b.
Proof.
  destruct a as [x|]. eauto. intros X. exact (None_not_Some X _).
Qed.

Ltac eq_some_inv :=
  repeat match goal with
         | H : @bind option option_monad _ _ (Some _) _ = _ |- _ =>
           simpl in H
         | H : _ = @bind option option_monad _ _ (Some _) _ |- _ =>
           simpl in H
         | H : @bind option option_monad _ _ None _ = _ |- _ =>
           simpl in H
         | H : _ = @bind option option_monad _ _ None _|- _ =>
           simpl in H
         | H : @None _ = Some _ |- _=>
           exact (None_not_Some H _)
         | H : Some _ = @None _ |- _=>
           exact (None_not_Some (eq_sym H) _)
         | H : Some ?a = Some ?b |- _ =>
           apply (@some_eq_inv _ a b) in H
         | H : @inl _ _ _ = @inr _ _ _ |- _=>
           exact (inl_not_inr H _)
         | H : @inr _ _ _ = @inl _ _ _ |- _=>
           exact (inl_not_inr (eq_sym H) _)
         | H : @inl _ _ ?a = @inl _ _ ?b |- _=>
           apply (@inl_eq_inv _ _ a b) in H
         | H : @inr _ _ ?a = @inr _ _ ?b |- _=>
           apply (@inr_eq_inv _ _ a b) in H
         | H : _ :: _ = @nil _ |- _ =>
           exact (cons_nil_inv H _)
         | H : @nil = _ :: _ |- _ =>
           exact (cons_nil_inv (eq_sym H) _)
         | H : false = true |- _ =>
           exact (false_not_true H _)
         | H : true = false |- _ =>
           exact (false_not_true (eq_sym H) _)
         | H : (_, _) = (_, _) |- _ =>
           destruct (pair_eq_inv H); clear H
         | H : _ :: _ = _ :: _ |- _ =>
           destruct (cons_eq_inv H); clear H
         | H : _ :: _ = nil |- _ =>
           exact (cons_nil_inv H _)
         | H : nil = _ :: _ |- _ =>
           exact (cons_nil_inv (eq_sym H) _)
         | H : rev _ = nil |- _ =>
           apply rev_nil in H
         | H : map _ _ = nil |- _ =>
           apply map_eq_nil in H
         | H : option_map _ _ = Some _ |- _ =>
           apply option_map_some in H
         | H : Some _ = option_map _ _ |- _ =>
           symmetry in H; apply option_map_some in H
         | H : option_map _ _ = None |- _ =>
           apply option_map_none in H
         | H : None = option_map _ _ |- _ =>
           symmetry in H; apply option_map_none in H
         | H : _ ++ _ = nil |- _ => apply app_nil in H
         | H : nil = _ ++ _ |- _ => symmetry in H; apply app_nil in H
         end.

(** * Lemmas about lists *)

Lemma rev_inj {A} (x y: list A) : rev x = rev y → x = y.
Proof.
  intros H. rewrite <- (rev_involutive x), <- (rev_involutive y). now apply f_equal.
Qed.

Lemma fold_left_cons_map_app {A B:Type} (f: A -> B) :
  forall (l: list A) (k: list B),
    fold_left (fun acc a => f a :: acc) l k = rev (map f l) ++ k.
Proof.
  refine (rev_ind _ _ _). reflexivity.
  intros. rewrite fold_left_app, map_app, rev_app_distr. simpl. congruence.
Qed.

Lemma flat_map_app {A B: Type} (f: A -> list B) :
  forall l m,
    flat_map f (l ++ m) = flat_map f l ++ flat_map f m.
Proof. induction l. reflexivity. simpl. intros. rewrite <- app_assoc. congruence. Qed.

Lemma aux {A B C:Type} (f: A -> B -> C) :
  forall (l: list A) (m: list B) (k: list C),
    fold_left (fun acc a => rev (map (f a) m) ++ acc) l k =
    rev (flat_map (fun a => map (f a) m) l) ++ k.
Proof.
  refine (rev_ind _ _ _). reflexivity.
  intros a l IH.
  intros m k.
  rewrite fold_left_app, flat_map_app, rev_app_distr, IH.
  simpl. rewrite app_assoc. f_equal.
  now rewrite app_nil_r.
Qed.

Lemma fold_left_ext_m {A B} (f g: A → B → A) :
  (∀ u v, f u v = g u v) →
  ∀ l z, fold_left f l z = fold_left g l z.
Proof.
  intros EXT.
  induction l. reflexivity.
  simpl. congruence.
Qed.

Definition curry {A B C} (f: A → B → C) : A * B → C :=
  λ ab, let '(a, b) := ab in f a b.

Definition pair_list {A B} (a: list A) (b: list B) : list (A * B) :=
  List.flat_map (λ a, List.map (pair a) b) a.

Lemma pair_list_nil {A B} (a: list A) : pair_list a (@nil B) = nil.
Proof. elim a. reflexivity. intros ? ?; exact id. Qed.

Lemma pair_list_not_nil {A B} (a: list A) (b: list B) :
  a ≠ nil → b ≠ nil → pair_list a b ≠ nil.
Proof.
  case a. intros X _ _; apply (X eq_refl).
  intros ? ? _.
  case b. intros X _; apply (X eq_refl).
  simpl; intros ? ? _ ?; eq_some_inv.
Qed.

Lemma in_pair_list {A B} (a: list A) (b: list B) (q: A * B) :
  In (fst q) a →
  In (snd q) b →
  In q (pair_list a b).
Proof.
  intros Ha Hb.
  unfold pair_list. rewrite in_flat_map.
  exists (fst q). split. exact Ha.
  apply in_map_iff.
  exists (snd q). split.
  exact (eq_sym (surjective_pairing q)).
  exact Hb.
Qed.

Lemma in_pair_list_inv {A B} (a: list A) (b: list B) (q: A * B) :
  In q (pair_list a b) →
  In (fst q) a ∧ In (snd q) b.
Proof.
  unfold pair_list. rewrite in_flat_map.
  intros (x & Hx & H).
  apply in_map_iff in H. destruct H as (y & Q & Hy).
  subst q. split; easy.
Qed.

Section MAPS.

  Variables A B C D : Type.

  Variable e : A → B.
  Variable f : A → B → C.
  Variable g : A → B → C → D.

  Definition rev_map_app (l: list A) (acc: list B) : list B :=
    fold_left (λ acc a, e a :: acc) l acc.

  Definition rev_map (l: list A) : list B :=
    rev_map_app l nil.

  Lemma rev_map_app_correct : ∀ l l', rev_map_app l l' = rev (map e l) ++ l'.
  Proof.
    unfold rev_map_app.
    induction l as [|x l IH] using rev_ind.
    reflexivity.
    intros l'.
    rewrite fold_left_app, map_app, rev_app_distr. simpl. congruence.
  Qed.

  Lemma rev_map_correct : ∀ l, rev_map l = rev (map e l).
  Proof.
    intros. unfold rev_map. rewrite rev_map_app_correct. intuition.
  Qed.

  Definition map2 (l: list A) (m: list B) : list C :=
    fold_left (λ acc a, fold_left (λ acc b, f a b :: acc) m acc) l nil.

  Definition map2_spec (l: list A) (m: list B) : list C :=
    rev (flat_map (λ a, map (f a) m) l).

  Lemma map2_correct : ∀ l m, map2 l m = map2_spec l m.
  Proof.
    intros l m.
    unfold map2, map2_spec.
    rewrite (fold_left_ext_m _ (λ acc a, rev (map (f a) m) ++ acc)).
    now rewrite aux, app_nil_r.
    now intros; rewrite fold_left_cons_map_app.
  Qed.

  Corollary in_map2 l m a b :
    In a l → In b m → In (f a b) (map2 l m).
  Proof.
    intros L M.
    rewrite map2_correct. unfold map2_spec. rewrite <- in_rev.
    apply in_flat_map. exists a. split; auto.
    apply in_map; auto.
  Qed.

  Corollary map2_in l m a b :
    In (f a b) (map2 l m) →
    ∃ a' b', In a' l ∧ In b' m ∧ f a' b' = f a b.
  Proof.
    rewrite map2_correct. unfold map2_spec.
    rewrite <- in_rev, in_flat_map.
    intros (x & Hx & IN). rewrite in_map_iff in IN.
    destruct IN as (y & Hy & IN).
    vauto.
  Qed.

  Lemma map_cons_inv l b b' :
    map e l = b :: b' →
    ∃ a a', l = a :: a' ∧ b = e a ∧ map e a' = b'.
  Proof.
    destruct l as [|a a']; inversion 1.
    repeat econstructor.
  Qed.

  Lemma map_nil_inv l :
    map e l = nil → l = nil.
  Proof.
    destruct l. reflexivity. intros; eq_some_inv.
  Qed.

End MAPS.

Section FOLD2.
  (** Fold on two lists.
      The weak version ignores trailing elements of the longest list. *)
  Context (A B C: Type)
          (f: C → A → B → C)
          (ka: C → list A → C)
          (kb: C → list B → C).

  Fixpoint fold_left2 (la: list A) (lb: list B) (acc: C) {struct la} : C :=
    match la, lb with
    | a :: la, b :: lb => fold_left2 la lb (f acc a b)
    | nil, nil => acc
    | la, nil => ka acc la
    | nil, lb => kb acc lb
    end.

End FOLD2.

Section FORALL2.
  Context (A B: Type)
          (P: A → B → bool).

  Local Open Scope bool_scope.

  Definition forallb2 (la: list A) (lb: list B) : bool :=
    fold_left2 (λ acc a b, acc && P a b) (λ _ _, false) (λ _ _, false) la lb true.

  Lemma forallb2_forall_aux la : ∀ b lb,
    fold_left2 (λ acc a b, acc && P a b) (λ _ _, false) (λ _ _, false) la lb b = true <->
    Forall2 (λ a b, P a b = true) la lb ∧ b = true.
  Proof.
    induction la as [|a la IH].
  - intros acc [|b lb]. intuition. split. easy. intros [H _]. inversion H.
  - intros acc [|b lb]. split. now intuition. intros [H _]. inversion H.
    specialize (IH (acc && P a b) lb). destruct IH as [IH1 IH2].
    split. intros H. specialize (IH1 H).
    destruct IH1 as [X Y]. rewrite Bool.andb_true_iff in Y. destruct Y as [Y Y'].
    split. constructor; auto. auto.
    intros [H K]. inversion H. subst. simpl. apply IH2. intuition.
  Qed.

  Lemma forallb2_forall la lb : forallb2 la lb = true <-> Forall2 (λ a b, P a b = true) la lb.
  Proof.
    generalize (forallb2_forall_aux la true lb).
    intuition.
  Qed.

End FORALL2.

Lemma bool_leb_true b : Bool.leb b true.
Proof. destruct b; easy. Qed.
Lemma bool_leb_refl b : Bool.leb b b.
Proof. destruct b; easy. Qed.

Definition is_one (z: Z) : bool :=
  match z with 1 => true | _ => false end.

Lemma is_one_intro z (P: Z → bool → Prop) :
  P 1 true →
  (∀ z, z ≠ 1 → P z false) →
  P z (is_one z).
Proof.
  intros H1 H.
  destruct z as [|[z|z|]|z];
    first [ exact H1 | apply H; discriminate ].
Qed.

Lemma int_eq (x y: Integers.int) :
  Integers.Int.eq x y = true → x = y.
Proof. intros H; generalize (Integers.Int.eq_spec x y); rewrite H; exact id. Qed.

Lemma int64_eq (x y: Integers.int64) :
  Integers.Int64.eq x y = true → x = y.
Proof. intros H; generalize (Integers.Int64.eq_spec x y); rewrite H; exact id. Qed.

(** * Classe of decidable equality, and its instances *)

Class EqDec (T: Type) := eq_dec : ∀ x y : T, { x = y } + { x ≠ y }.

Instance PosEqDec : EqDec positive := Pos.eq_dec.
Instance ZEqDec : EqDec Z := Z.eq_dec.
Instance NEqDec : EqDec N := N.eq_dec.
Instance IntEqDec : EqDec Integers.int := Integers.Int.eq_dec.
Instance ProdEqDec {X Y: Type} `{EqDec X} `{EqDec Y} : EqDec (X * Y).
Proof. unfold EqDec. decide equality. Defined.

Instance ListEqDec : ∀ {X: Type} `{EqDec X}, EqDec (list X) := list_eq_dec.

Instance MCEqDec : EqDec memory_chunk := AST.chunk_eq.

Require Import Eqdep_dec.
Lemma eq_dec_true {A} `{H: EqDec A} (a: A) : eq_dec a a = left eq_refl.
Proof.
  exact match eq_dec a a as q return q = left eq_refl with
           | left EQ => f_equal left (UIP_dec H EQ eq_refl)
           | right NE => False_ind _ (NE eq_refl)
        end.
Qed.

Remark eq_dec_eq {A} `{H: EqDec A} (a a': A) :
  proj_sumbool (eq_dec a a') = true → a = a'.
Proof.
  exact match eq_dec a a' as q return proj_sumbool q = true → a = a' with
  | left EQ => λ _, EQ
  | right NE => λ K, false_not_true K _
  end.
Qed.

(** * Changing one value in an environment *)

Definition upd `{X: Type} `{EqDec X} {Y} (f: X → Y) (p: X) (v:Y) :=
  fun q => if eq_dec q p then v else f q.
Notation "f +[ p => v ] " := (upd f p v) (at level 40).

Lemma upd_s `{X: Type} `{EqDec X} {Y} (f: X → Y) p v:
  (f+[p => v] ) p = v.
Proof. unfold upd. case (eq_dec p p); tauto. Qed.

Lemma upd_o `{X: Type} `{EqDec X} {Y} (f: X → Y) p v p' :
  p' ≠ p → f +[p => v] p' = f p'.
Proof. unfold upd. case (eq_dec p' p); tauto. Qed.

Definition upd_spec `{X: Type} `{EqDec X} {Y} (f: X → Y) (p: X) (v:Y) (f': X → Y) : Prop :=
  ∀ q, f' q = if eq_dec q p then v else f q.

(** * Notations on sets *)

Notation "P1 ⊆ P2" := (forall a, P1 a -> P2 a)  (at level 20).
Notation "x ∈ P" := (P x) (at level 19, only parsing).
Notation "'𝒫' A" := (A -> Prop) (at level 0, only parsing).
Notation "f ∘ g" := (fun x => f (g x)) (at level 40, left associativity).
Notation "X ∩ Y" := (fun x => X x ∧ Y x) (at level 19).
Notation "X ∪ Y" := (fun x => X x ∨ Y x) (at level 19).
Notation "∅" := (fun _ => False).
