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

Require Import
  Utf8 Coqlib Util Maps.

Set Implicit Arguments.

Section ASSOC.

Context (A B: Type)
        `{EqDec A}
        (a: A).

Fixpoint assoc (l: list (A * B)) : option B :=
  match l with
  | cons (a', b) l' =>
    if eq_dec a' a then Some b else assoc l'
  | nil => None
  end.

Definition assoc_prop l pre (b: B) post : Prop :=
  l = pre ++ (a, b) :: post ∧
  ∀ b', ¬ In (a, b') pre.

Fixpoint assoc_dep (l : list (A * B)) :
  { res | assoc_prop l (fst (fst res)) (snd (fst res)) (snd res) } + { ∀ b, ¬ In (a, b) l}.
  refine(
  match l with
  | cons (a', b) l' =>
    match eq_dec a' a with
    | left EQ => inleft (exist _ (nil, b, l') _)
    | right NE => match assoc_dep l' with
                  | inleft (exist r R) =>
                    match r as r' return assoc_prop l' (fst (fst r')) (snd (fst r')) (snd r') → _ with
                    | (pre, b', post) => λ R', inleft (exist _ ((a', b) :: pre, b', post) _)
                    end R
                  | inright R => inright _
                  end
    end
  | nil => inright _
  end).
Proof.
  exact (λ _ K, K).
  clear -EQ. abstract (split; [rewrite EQ; reflexivity | exact (λ _ K, K)]).
  clear -NE R'. abstract (simpl in *; destruct R' as [R1 R2]; split;[simpl; congruence|
  (intros c [ K | K ];[eq_some_inv; intuition | exact (R2 _ K)])]).
  clear -NE R. abstract (intros c [K | K]; [eq_some_inv; intuition | exact (R _ K)]).
Defined.
Global Opaque assoc_dep.

Lemma assoc_in l :
  ∀ b, assoc l = Some b → In (a, b) l.
Proof.
  induction l as [|(a', b') l IH].
  exact (λ _ H, None_not_Some H _).
  intros b. simpl.
  destruct eq_dec. intro. eq_some_inv. left. subst. reflexivity.
  intuition.
Qed.

Lemma assoc_Some l :
  ∀ b,
    assoc l = Some b →
    ∃ pre post,
      l = pre ++ (a, b) :: post ∧
      ∀ b', ¬ In (a, b') pre.
Proof.
  induction l as [|(a', b') l IH].
  exact (λ _ H, None_not_Some H _).
  intros b. simpl.
  destruct eq_dec as [EQ|NE].
  intros EQ'.
  exists nil. exists l. simpl. eq_some_inv. intuition. subst. reflexivity.
  intros R. destruct (IH _ R) as (pre & post & X & Y).
  exists ((a', b') :: pre), post.
  split. simpl. subst. reflexivity.
  intros z [Q|Q]. apply pair_eq_inv in Q. intuition.
  intuition eauto.
Qed.

Lemma assoc_None l :
  assoc l = None ↔
  ∀ b, ¬ In (a, b) l.
Proof.
  induction l as [|(a', b') l IH]. intuition.
  simpl. destruct eq_dec. split. intro; eq_some_inv.
  intros K. destruct (K b'). left. congruence.
  split.
  intros K b [X|X]. eq_some_inv. auto.
  exact (proj1 IH K b X).
  intros K. firstorder.
Qed.

Lemma In_norepet_assoc (b: B) l :
  list_norepet (map fst l) →
  In (a, b) l → assoc l = Some b.
Proof.
  induction l as [|(a', b') l IH]. intros _ ().
  intros NR [IN|IN].
  eq_some_inv. simpl. subst. rewrite dec_eq_true. reflexivity.
  simpl. inv NR. rewrite dec_eq_false. apply IH; auto.
  intros ->. elim H2. rewrite in_map_iff. exists (a, b). intuition.
Qed.

Lemma assoc_app l m :
  assoc (l ++ m) = match assoc l with Some r => Some r | None => assoc m end.
Proof.
  induction l as [|(x,b) l IH]. reflexivity.
  simpl. destruct eq_dec; auto.
Qed.

Corollary assoc_iff l b :
  assoc l = Some b ↔ ∃ pre post, assoc_prop l pre b post.
Proof.
  split. apply assoc_Some.
  intros (pre & post & -> & K).
  rewrite assoc_app.
  generalize (assoc_in pre).
  destruct (assoc pre). intros X. elim (K _ (X _ eq_refl)).
  intros _. simpl. rewrite dec_eq_true. reflexivity.
Qed.

End ASSOC.

Lemma ptree_get_assoc {A: Type} (m: PTree.t A) :
  ∀ x, m ! x = assoc x (PTree.elements m).
Proof.
  intros x.
  generalize (PTree.elements_correct m x).
  generalize (PTree.elements_complete m x).
  generalize (PTree.elements_keys_norepet m).
  intros NR C I.
  destruct (m ! x). specialize (I _ eq_refl). symmetry. apply In_norepet_assoc; auto.
  generalize (assoc_in x (PTree.elements m)).
  destruct assoc; auto.
Qed.

Section NTH.

Context (A: Type).

Fixpoint nth (m: list A) (p: positive) : option A :=
  match m with
  | nil => None
  | x :: n => match p with xH => Some x | xI q => nth n (xO q) | xO q => nth n (Pos.pred_double q) end
  end.

Lemma nth_succ (m: list A) p :
  nth m (Pos.succ p) = match m with nil => None | _ :: m' => nth m' p end.
Proof.
  destruct p as [ p | p | ]; destruct m as [ | a m ]; simpl; auto.
  f_equal. apply Pos.pred_double_succ.
Qed.

Lemma nth_in p (m: list A) a :
  nth m p = Some a → In a m.
Proof.
  revert p.
  induction m as [ | b m IH ]. simpl; intros; eq_some_inv.
  intros [ f | f | ]; simpl;
  (intuition congruence) ||
  (intros H; specialize (IH _ H); auto).
Qed.

End NTH.

Section PLENGTH.

Local Open Scope positive_scope.

Context (A: Type).

Fixpoint plength_aux (m: list A) (acc: positive) : positive :=
  match m with nil => acc | _ :: m' => plength_aux m' (Pos.succ acc) end.

Definition plength (m: list A) : positive :=
  plength_aux m xH.

Lemma plength_nil : plength nil = xH.
Proof. reflexivity. Qed.

Lemma plength_aux_add (m: list A) (x y: positive) :
  plength_aux m (x + y) = plength_aux m x + y.
Proof.
  revert x.
  induction m as [ | a m IH ]; intros x.
  reflexivity.
  now simpl; rewrite <- IH, Pos.add_succ_l.
Qed.

Lemma plength_length_aux (m: list A) acc :
   Pos.pred (acc + Pos.of_succ_nat (Datatypes.length m)) = plength_aux m acc.
Proof.
  revert acc.
  induction m as [ | a m IH ]; simpl; intros acc;
  try rewrite <- IH;
  rewrite Ppred_minus; zify; rewrite ! Pos2Z.inj_sub; Psatz.lia.
Qed.

Lemma plength_length (m: list A) :
   Pos.of_succ_nat (Datatypes.length m) = plength m.
Proof.
  unfold plength. rewrite <- plength_length_aux.
  now rewrite <- Pplus_one_succ_l, Pos.pred_succ.
Qed.

Definition plength_cons (a: A) (m: list A) :
  plength (a :: m) = Pos.succ (plength m).
Proof.
  unfold plength.
  now rewrite Pplus_one_succ_r, <- plength_aux_add, <- Pplus_one_succ_r.
Qed.

Definition plength_app (m n: list A) :
  plength (m ++ n) = Pos.pred (plength m + plength n)%positive.
Proof.
  revert n.
  induction m as [ | a m IH ].
  now intros n; rewrite <- Pplus_one_succ_l, Pos.pred_succ.
  intros n. simpl app. rewrite ! plength_cons.
  rewrite IH. rewrite ! Pplus_one_succ_l, ! Ppred_minus. zify.
  repeat (rewrite ? Pos2Z.inj_add; rewrite ? Pos2Z.inj_sub; Psatz.lia).
Qed.

Definition plength_snoc (a: A) (m: list A) :
  plength (m ++ a :: nil) = Pos.succ (plength m).
Proof.
  rewrite plength_app, plength_cons, Ppred_minus, ! Pplus_one_succ_l, plength_nil.
  zify. rewrite Pos2Z.inj_sub; Psatz.lia.
Qed.

Lemma rev_plength (m: list A) :
  plength (rev m) = plength m.
Proof.
  induction m as [ | a m IH ].
  reflexivity. now simpl; rewrite plength_cons, plength_snoc; f_equal.
Qed.

End PLENGTH.

Lemma map_plength {A B} (f: A → B) (m: list A) :
  plength (map f m) = plength m.
Proof.
  induction m.
  now rewrite plength_nil.
  simpl. rewrite ! plength_cons. congruence.
Qed.
