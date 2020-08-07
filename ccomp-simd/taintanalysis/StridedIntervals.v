Require Import AdomLib.
Require Recdef.
Require Psatz.
Require Import aritmo.
Require Import ToString.
Import Coqlib.
Import Integers.

(** Numerical domain of Strided Intervals.

    Reference: Gogul Balakrishnan. “WYSINWYX: what you see is not what you eXecute.”
               PhD thesis. Madison: University of Wisconsin, 2007.

    Abstract values are triples (s, l, u) representing all integers i, s.t.

        l ≤ i ≤ u  ∧  i ≡ l (mod s).

    It is supposed to precisely capture common families of addresses,
    e.g., contiguous cells in an array.

    Since the congruence domain is not very precise on machine integers (moduli must
    be powers of two since any operation might overflow), this domain is strictly
    more precise than the reduced product of intervals and congruences on machine integers.

    Moreover, it is more precise than the projection to machine integers of the reduced
    product of the congruence domain on Z and the interval domain on Z in case of overflows.
 *)

Unset Elimination Schemes.

Local Coercion Z_of_N : N >-> Z.

(** Data type.

    Not a dependent type. In particular the type does neither enforce that bounds
    are correctly ordered nor that the upper bound is tight.
    However, some operations assume it (they are otherwise unprecise).
    The operations that would be unsound do the appropriate checks.
 *)
Record strided_interval : Type :=
  { si_stride   : N
  ; si_low_bound: Z
  ; si_up_bound : Z
  }.

Definition si_valid (s: strided_interval) : Prop :=
  s.(si_low_bound) <= s.(si_up_bound).

Definition si_reduced (s: strided_interval) : Prop :=
  (s.(si_low_bound) ≡ s.(si_up_bound) [ s.(si_stride) ])
∧ (s.(si_low_bound) = s.(si_up_bound) → s.(si_stride) = N0).


Definition si_LE (x y: strided_interval) : Prop :=
  y.(si_low_bound) <= x.(si_low_bound)
∧ x.(si_up_bound) <= y.(si_up_bound)
∧ ( y.(si_stride) | x.(si_stride) )
∧ ( x.(si_low_bound) ≡ y.(si_low_bound) [y.(si_stride)] ).

Definition si_LE_dec (x y: strided_interval) : { si_LE x y } + { ¬ si_LE x y }.
  refine (
    match zle y.(si_low_bound) x.(si_low_bound) with
    | left L =>
        match zle x.(si_up_bound) y.(si_up_bound) with
        | left U =>
          match Zdivides_dec y.(si_stride) x.(si_stride) with
          | left s =>
            match congr_dec y.(si_stride) x.(si_low_bound) y.(si_low_bound) with
            | left A => left _
            | right A => right _
            end
          | right s => right _
          end
        | right U => right _
        end
    | right L => right _
    end); abstract (unfold si_LE; intuition).
Proof.
Defined.

Definition si_join (x y: strided_interval) : strided_interval :=
  {| si_stride := N.gcd (N.gcd x.(si_stride) y.(si_stride))
                        (Nabs_diff x.(si_low_bound)  y.(si_low_bound))
   ; si_low_bound := Zmin x.(si_low_bound) y.(si_low_bound)
   ; si_up_bound := Zmax x.(si_up_bound) y.(si_up_bound)
  |}.

Program Definition si_meet (x y: strided_interval) : strided_interval+⊥ :=
  match congr_dec (N.gcd x.(si_stride) y.(si_stride)) x.(si_low_bound) y.(si_low_bound) return _ with
    | left H =>
      let A := Zmax x.(si_low_bound) y.(si_low_bound) in
      let B := Zmin x.(si_up_bound) y.(si_up_bound) in
      let m := N.lcm x.(si_stride) y.(si_stride) in
      if Z_zerop m
      then
        if Z_le_dec A B
        then NotBot {| si_stride := m; si_low_bound := A; si_up_bound := A |}
        else Bot
      else
        let (n, K) := rem_eqn_particular x.(si_low_bound) y.(si_low_bound)
                                         x.(si_stride) y.(si_stride) _ _ _
        in
        let l := A + ((n - A) mod m) in
        let u := B - ((B - n) mod m) in
        match Z_dec l u with
        | inleft (left LT) => NotBot {| si_stride := m; si_low_bound := l; si_up_bound := u |}
        | inleft (right GT) => Bot
        | inright EQ => NotBot {| si_stride := 0%N; si_low_bound := l; si_up_bound := u |}
        end
    | right _ => Bot
  end.
Next Obligation. zify; omega. Qed.
Next Obligation. zify; omega. Qed.
Next Obligation. rewrite <- Ngcd_is_Zgcd. auto. Qed.

Lemma si_meet_valid x y :
  match si_meet x y with
  | NotBot z => si_valid z
  | Bot => True
  end.
Proof.
  unfold si_meet.
  destruct congr_dec. 2: easy.
  destruct Z_zerop.
  + destruct Z_le_dec. 2: easy.
    reflexivity.
  + destruct rem_eqn_particular. destruct Z_dec as [[LT|GT]|EQ];
    unfold si_valid; simpl; intuition.
Qed.

Lemma si_meet_reduced x y :
  match si_meet x y with
  | NotBot z => si_reduced z
  | Bot => True
  end.
Proof.
  unfold si_meet.
  destruct congr_dec. 2: easy.
  destruct Z_zerop.
  + destruct Z_le_dec. 2: easy.
    split; simpl. auto with congr.
    destruct N.lcm. easy. discriminate.
  + rewrite Nlcm_is_Zlcm in *.
    set (s := Z.lcm x.(si_stride) y.(si_stride)).
    set (A := Zmax x.(si_low_bound) y.(si_low_bound)).
    set (B := Zmin x.(si_up_bound) y.(si_up_bound)).
    assert (s > 0) as Hs.
    subst s. rewrite <- Nlcm_is_Zlcm. destruct N.lcm; intuition.
    match goal with
    | |- context[rem_eqn_particular ?a ?b ?c ?d ?o1 ?o2 ?o3] =>
      destruct (smallest_solution_larger_than a b c d o1 o2 o3 A Hs) as (U & _);
      destruct (largest_solution_smaller_than a b c d o1 o2 o3 B Hs) as (U' & _);
      destruct rem_eqn_particular as (N & REQ)
    end.
    destruct Z_dec as [[LT|GT]|EQ];
      trivial; split; simpl; trivial.
    - simpl in *.
      rewrite Nlcm_is_Zlcm.
      eapply rem_eqn_all_solutions; eauto; now zify.
    - intuition.
    - rewrite EQ. auto with congr.
Qed.

Definition si_size (x : strided_interval) : N :=
  match Z_le_dec x.(si_low_bound) x.(si_up_bound) with
  | left LE =>
    match x.(si_stride) with
    | N0 => 1%N
    | Npos s => N_of_Z ((x.(si_up_bound) - x.(si_low_bound)) / (Zpos s) + 1)
    end
  | right GT => N0
  end.

Section Gamma.
  Variable interp : int → Z.
  Local Coercion interp : int >-> Z.
  Variables min max : Z.
  Hypothesis range : ∀ i : int, min <= i <= max.
  Hypothesis interpz : interp Int.zero = 0.
  Hypothesis interp_inj : ∀ x y : int, x ≠ y → interp x ≠ interp y.

  Definition si_top : strided_interval :=
    {| si_stride := 1
     ; si_low_bound := min
     ; si_up_bound  := max
    |}.

  Lemma si_top_reduced (H: min ≠ max) : si_reduced si_top.
  Proof. split; simpl. auto with congr. intros. contradiction. Qed.

  Instance si_gamma : gamma_op strided_interval int := fun x =>
    fun i => x.(si_low_bound) <= i <= x.(si_up_bound)
           ∧ x.(si_low_bound) ≡ i [ x.(si_stride) ].

  Lemma si_gamma_monotone (x y: strided_interval) :
    si_LE x y → si_gamma x ⊆ si_gamma y.
  Proof.
    intros (A&B&C&D) i (U & V). split. intuition.
    apply congr_trans with x.(si_low_bound); auto with congr.
    eapply congr_divide; eauto with congr.
  Qed.

  Lemma si_gamma_top (i: int) : si_gamma si_top i.
  Proof.
    split. apply range. auto with congr.
  Qed.

  Lemma si_join_sound (x y: strided_interval) :
    si_gamma x ∪ si_gamma y ⊆ si_gamma (si_join x y).
  Proof.
    unfold si_gamma. intros i H. split; simpl.
    apply Zmin_case_strong; apply Zmax_case_strong; intuition.
    repeat rewrite Ngcd_is_Zgcd.
    destruct H as [(X&B)|(X&B)].
    apply congr_trans with x.(si_low_bound). apply Zmin_case. auto with congr.
    destruct (Nabs_diff_case x.(si_low_bound) y.(si_low_bound)) as [(A&->)|(A&->)];
    (rewrite N_of_pos;[|intuition]);[|apply congr_sym];
    (eapply congr_divide;[apply congr_diff|]; apply Zgcd_divides_r).
    eapply congr_divide. 2: apply Zgcd_divides_l.
    eapply congr_divide. 2: apply Zgcd_divides_l. auto.
    apply congr_trans with y.(si_low_bound). apply Zmin_case; auto with congr.
    destruct (Nabs_diff_case x.(si_low_bound) y.(si_low_bound)) as [(A&->)|(A&->)];
    (rewrite N_of_pos;[|intuition]);[apply congr_sym|];
    (eapply congr_divide;[apply congr_diff|]; apply Zgcd_divides_r).
    eapply congr_divide. 2: apply Zgcd_divides_l.
    eapply congr_divide. 2: apply Zgcd_divides_r. auto.
  Qed.

  Definition si_widen heuristic (x y: strided_interval) : strided_interval :=
   let '(a, b) := heuristic x.(si_low_bound) x.(si_up_bound) y.(si_low_bound) y.(si_up_bound) in
   if zeq a b
   then {| si_stride := N0; si_low_bound := a; si_up_bound := b |}
   else {| si_stride := 1%N; si_low_bound := a; si_up_bound := b |}.

  Lemma si_widen_reduced h x y :
    si_reduced (si_widen h x y).
  Proof.
    unfold si_widen. destruct h as (m, M).
    destruct zeq. subst. split; simpl; auto with congr.
    split; simpl. auto with congr. intuition.
  Qed.

  Instance toString : ToString strided_interval :=
    { to_string i :=
      if si_LE_dec si_top i
      then "⊤"%string
      else
        match i.(si_stride) with
        | N0 => to_string i.(si_low_bound)
        | s =>
          (to_string (Z_of_N s)
          ++ "[" ++ to_string i.(si_low_bound) ++ "; "
          ++ to_string i.(si_up_bound) ++ "]")%string
        end
    }.

  (*
  Instance si_wlat : weak_lattice strided_interval :=
    {| leb x y := si_LE_dec x y
     ; top := si_top
     ; join := si_join
     ; widen := si_widen
    |}.
  Lemma si_adom : adom strided_interval int si_wlat si_gamma.
  Proof.
    split; unfold γ; simpl.
    (* γ monotone *)
    intros x y. destruct si_LE_dec. intros _. apply si_gamma_monotone; auto. intuition.
    (* γ top *)
    apply si_gamma_top.
    (* join sound *)
    apply si_join_sound.
  Qed.
   *)

  Lemma si_meet_sound (x y: strided_interval) :
    si_gamma x ∩ si_gamma y ⊆ match si_meet x y with NotBot z => si_gamma z | Bot => ∅ end.
  Proof.
    unfold si_gamma.
    intros i ((Bx & Mx)&(By & My)).
    unfold si_meet.
    generalize (si_meet_obligation_1 x y), (si_meet_obligation_2 x y), (si_meet_obligation_3 x y).
    rewrite (Ngcd_is_Zgcd (si_stride x) (si_stride y) ).
    destruct congr_dec as [H|H].
    (* gcd is ok *)
    simpl. rewrite Nlcm_is_Zlcm. intros OBL1 OBL2 OBL3.
    destruct Z_zerop as [Sz|Snz].
    (* lcm is null: one of the intervals is a singleton, i is in the other *)
    destruct Z_le_dec as [n|n]. simpl.
    2: apply n; apply Zle_trans with i;[apply Zmax_case|apply Zmin_case]; intuition.
    assert (Zmax x.(si_low_bound) y.(si_low_bound) = i) as Q.
      apply Z.lcm_eq_0 in Sz. destruct Sz as [Q|Q]; rewrite Q in *.
      rewrite (congr_0_eq _ _ Mx) in *. apply Zmax_case_strong; auto. omega.
      rewrite (congr_0_eq _ _ My) in *. apply Zmax_case_strong; auto. omega.
    rewrite <- Q. split. omega. exists 0. ring.
    (* lcm is not null *)
    set (s := Z.lcm x.(si_stride) y.(si_stride)).
    set (A := Zmax x.(si_low_bound) y.(si_low_bound)).
    set (B := Zmin x.(si_up_bound) y.(si_up_bound)).
    assert (s > 0) as Hs.
      pose proof (Z.lcm_nonneg (si_stride x) (si_stride y)). subst s. omega.
    destruct (smallest_solution_larger_than _ _ _ _
                (OBL1 H Snz) (OBL2 H Snz) (OBL3 H Snz) A Hs) as (U & V & W).
    destruct (largest_solution_smaller_than _ _ _ _
                (OBL1 H Snz) (OBL2 H Snz) (OBL3 H Snz) B Hs) as (U' & V' & W').
    destruct (rem_eqn_particular (si_low_bound x) (si_low_bound y)
              (si_stride x) (si_stride y) (OBL1 H Snz)
              (OBL2 H Snz) (OBL3 H Snz)) as (n&REQ). simpl in *.
    fold s in U, V, W.
    destruct Z_dec as [[LT|GT]|EQ]. simpl.
    split.
    split. apply W. split; auto. subst A. Psatz.lia.
    apply W'. split; auto. subst B. Psatz.lia.

    rewrite Nlcm_is_Zlcm.
    apply congr_trans with (Zmax x.(si_low_bound) y.(si_low_bound) + (n - Zmax x.(si_low_bound) y.(si_low_bound))). apply congr_plus_compat. auto with congr. apply congr_sym, congr_mod_compat. auto.
    replace (Zmax x.(si_low_bound) y.(si_low_bound) + (n - Zmax x.(si_low_bound) y.(si_low_bound)))
    with n by ring.
    eapply rem_eqn_all_solutions; try now zify. eauto.
    split; auto.

    apply (Zgt_not_le _ _ GT); clear GT.
    apply Zle_trans with i.
    apply W. split; auto. subst A. Psatz.lia.
    apply W'. split; auto. subst B. Psatz.lia.

    simpl.
    cut (A + (n - A) mod s = i). intros <-. intuition.
    apply Zle_antisym.
    apply W. split; auto. subst A. Psatz.lia.
    rewrite EQ. apply W'. split; auto. subst B. Psatz.lia.

    (* gcd is ko *)
    intros OBL1 OBL2 OBL3.
    apply H; clear H. apply congr_trans with i; eapply congr_divide; eauto.
    apply Zgcd_divides_l. apply congr_sym; eauto. apply Zgcd_divides_r.
  Qed.

  Definition si_const (i: int) : strided_interval :=
    {| si_stride := 0%N; si_low_bound := i; si_up_bound := i |}.

  Lemma si_const_sound (i: int) : si_gamma (si_const i) i.
  Proof.
    split; simpl; intuition.
  Qed.

  Lemma si_const_valid i : si_valid (si_const i).
  Proof. apply Zle_refl. Qed.

  Lemma si_const_reduced i : si_reduced (si_const i).
  Proof. split; simpl; auto with congr. Qed.

  Definition si_add (x y: strided_interval) : strided_interval :=
    let l := x.(si_low_bound) + y.(si_low_bound) in
    let u := x.(si_up_bound) + y.(si_up_bound) in
    if Z_le_dec min l
    then (* min <= l *)
      if Z_le_dec l max
      then (* l <= max *)
        if Z_le_dec u max
        then {| si_stride := N.gcd x.(si_stride) y.(si_stride)
              ; si_low_bound := l
              ; si_up_bound := u
             |}
        else si_top
      else (* max < l, u *)
        {| si_stride := N.gcd x.(si_stride) y.(si_stride)
         ; si_low_bound := l - Int.modulus
         ; si_up_bound := u - Int.modulus
        |}
    else (* l < min *)
      if Z_le_dec min u
      then si_top
      else (* l, u < min *)
        {| si_stride := N.gcd x.(si_stride) y.(si_stride)
         ; si_low_bound := l + Int.modulus
         ; si_up_bound := u + Int.modulus
        |}.

  Lemma si_add_valid x y :
    si_valid x →
    si_valid y →
    si_valid (si_add x y).
  Proof.
    unfold si_add, si_valid.
    intros X Y.
    repeat destruct Z_le_dec; simpl; auto with zarith.
    apply Zle_trans with 0; rewrite <- interpz; eapply range.
  Qed.

  Lemma si_add_reduced (H: min ≠ max) x y :
    si_valid x →
    si_valid y →
    si_reduced x →
    si_reduced y →
    si_reduced (si_add x y).
  Proof.
  Hint Resolve congr_plus_compat.
    unfold si_add, si_valid.
    intros A B.
    intros (X&X') (Y&Y').
    assert (x.(si_low_bound) ≡ x.(si_up_bound) [Zgcd x.(si_stride) y.(si_stride)]).
      eapply congr_divide. eauto. apply Zgcd_divides_l.
    assert (y.(si_low_bound) ≡ y.(si_up_bound) [Zgcd x.(si_stride) y.(si_stride)]).
      eapply congr_divide. eauto. apply Zgcd_divides_r.
    repeat destruct Z_le_dec;
      auto using si_top_reduced;
    split; simpl;
    try rewrite Ngcd_is_Zgcd;
    try unfold Zminus;
    auto with congr;
    intros EQ; rewrite X', Y'; try omega; now trivial.
  Qed.

  Definition si_is_in_itv (u v: int) (x: strided_interval) : bool :=
    (* could be refined to take stride into account *)
    Z_le_dec u x.(si_low_bound) && Z_le_dec x.(si_up_bound) v.

  Definition si_contains (i: int) (x: strided_interval) : bool :=
    match si_meet x (si_const i) with
    | Bot => false
    | NotBot _ => true
    end.

  Set Elimination Schemes.
  Function si_concretize_aux (s: positive) (base: Z) (nb: Z) (acc: list Z) {measure Zabs_nat nb} : list Z :=
    let nb := nb - Zpos s in
    match nb with
    | Zpos _ | Z0 => si_concretize_aux s base nb (base + nb :: acc)
    | Zneg _ => acc
    end.
  Proof. clear. intros; zify; intuition. clear. intros; zify; intuition. Defined.

  Definition si_concretize (x: strided_interval) : list Z :=
    match Z_le_dec x.(si_low_bound) x.(si_up_bound) with
    | left LE =>
      match x.(si_stride) with
      | N0 => x.(si_low_bound) :: nil
      | Npos s =>
        si_concretize_aux s x.(si_low_bound) ((x.(si_up_bound) - x.(si_low_bound)) / Zpos s * Zpos s + Zpos s) nil
      end
    | right GT => nil
    end.

  Lemma si_concretize_sound_aux :
    ∀ acc nb s base (i:int),
      nb ≡ 0 [Zpos s] →
      In (i:Z) (si_concretize_aux s base nb acc) <->
      In (i:Z) acc ∨ (base <= i <= base + nb - Zpos s ∧ base ≡ i [Zpos s]).
  Proof.
    intros acc nb s base.
    apply si_concretize_aux_ind; simpl.
    intros nb0 acc0 _x e H i H0.
    assert (nb0 - Zpos s ≡ 0 [Zpos s]) as Q.
      destruct H0 as (q,Q). exists (q + 1). Psatz.lia.
    specialize (H i Q).
    split. intros H1.
    destruct (proj1 H H1) as [[K|K]|K]. 2: intuition.
    right. rewrite <- K. zify. split. intuition.
    rewrite <- (Zplus_0_r base) at 1. auto with congr.
    right. zify. intuition.
    intros [A|(A,B)]; apply (proj2 H); clear H.
      now left; right.
    case (Z_eq_dec (base + (nb0 - Zpos s)) i). intuition.
    intros Hi. right. split. split. intuition. 2: intuition.
    apply le_congr. intuition.
    rewrite <- (Zplus_0_r i). auto with congr.
    intros nb0 acc0 e H i H0.
    rewrite e in *. specialize (H i (congr_refl _ _)).
    destruct H as (H1,H2).
    split. intros H3.
    destruct (H1 H3) as [[H|H]|H]. 2: intuition.
    right. rewrite <- H. zify. split. intuition.
    rewrite <- (Zplus_0_r base) at 1. auto with congr.
    right. zify. intuition.
    intros [A|(A,B)]; apply H2; clear H2. intuition.
    case (Z_eq_dec base i). intuition.
    intros Hi. right. split. split. intuition. 2: intuition.
    apply le_congr. intuition.
    rewrite <- (Zplus_0_r i). auto with congr.
    intros nb0 acc0 _x e i H. split. now left.
    intros [A|(A,B)]; auto.
    exfalso. zify. intuition.
  Qed.

  (*
  Lemma si_concretize_exact (x: strided_interval) :
    ∀ i : int, List.In (i:Z) (si_concretize x) <-> γ x i.
  Proof.
    unfold γ.
    unfold si_concretize.
    destruct Z_le_dec.
    2: intros i; split;[|simpl; unfold si_gamma]; intuition.
    case_eq (x.(si_stride)).
    intros Hs i. simpl. unfold si_gamma.
    split. intros [Hi|()]. intuition. rewrite Hi. intuition.
    rewrite Hs. simpl. intros (A,B). rewrite (congr_0_eq _ _ B). now left.
    intros s Hs i.
    set (q := (x.(si_up_bound) - x.(si_low_bound)) / Zpos s).
    assert (q * Zpos s + Zpos s ≡ 0 [Zpos s]) as Q. apply congr_sym. exists (q+1). Psatz.lia.
    destruct (si_concretize_sound_aux nil _ _ x.(si_low_bound) i Q) as (FW,BW).
    split. intros Hi.
    destruct (FW Hi) as [()|(H,H')].
    simpl. split.
    2: rewrite Hs; simpl; auto.
    generalize H. subst q. DLib.elim_div.
    intuition. Psatz.nia.
    simpl. unfold si_gamma.
    intros (A,B).
    apply BW. right. rewrite Hs in B. simpl in B.
    split. 2: easy.
    clear -A B. intuition.
    cut (i <= si_low_bound x + q * Zpos s). intuition.
    destruct B as (b,B). rewrite B in *.
    apply Zplus_le_compat. intuition.
    subst q. DLib.elim_div. zify. intros.
    apply Zmult_le_compat_r.
    Psatz.nia.
    intuition.
  Qed.
*)

End Gamma.

(** Signed SI *)
(*
Instance ssi_wlat : weak_lattice strided_interval :=
  si_wlat Int.min_signed Int.max_signed.
*)
Instance ssi_gamma : gamma_op strided_interval int :=
  si_gamma Int.signed.
(*
Lemma ssi_adom : adom strided_interval int ssi_wlat ssi_gamma.
Proof.
  apply si_adom.
  apply Int.signed_range.
  apply DLib.signed_inj.
Qed.
*)

Definition ssi_top : strided_interval := si_top Int.min_signed Int.max_signed.

Lemma ssi_top_sound :
  ∀ a, γ ssi_top a.
Proof.
  split. apply Int.signed_range. auto with congr.
Qed.

Definition ssi_neg (x: strided_interval) : strided_interval :=
  if zle x.(si_low_bound) Int.min_signed
  then if zeq x.(si_up_bound) Int.min_signed
       then si_const Int.signed (Int.repr Int.min_signed)
       else ssi_top
  else
    (* check that the input is reduced; unsound otherwise *)
    if congr_dec x.(si_stride) x.(si_low_bound) x.(si_up_bound)
    then {| si_stride := x.(si_stride)
          ; si_low_bound := - x.(si_up_bound)
          ; si_up_bound := - x.(si_low_bound)
         |}
    else ssi_top.

(** Specifications of the numerical operations on sets of concrete va    lues. *)
Definition lift_unop (op: int → int) (A:𝒫 int) : 𝒫 int :=
  fun i => ∃ j, A j ∧ i = (op j).

Definition lift_binop (op: int → int → int) (A B: 𝒫 int) : 𝒫 int :=
  fun i => ∃ a, ∃ b, A a ∧ B b ∧ i = (op a b).

Lemma ssi_neg_sound (x: strided_interval) :
  lift_unop Int.neg (γ x) ⊆ γ (ssi_neg x).
Proof.
  unfold γ, ssi_gamma.
  intros i' (i & I & ->). unfold si_gamma in *.
  unfold ssi_neg.
  destruct zle as [L|L].
    destruct zeq as [H|H].
      simpl. rewrite Int.signed_repr. 2: vm_compute; split; discriminate.
      assert (Int.signed i = Int.min_signed) as K.
        apply Zle_antisym. intuition. apply Int.signed_range.
      assert (i = Int.repr (Int.min_signed)). now rewrite <- K, Int.repr_signed.
      subst. intuition.
    apply si_gamma_top, Int.signed_range.
  destruct congr_dec. 2: apply si_gamma_top, Int.signed_range.
  simpl.
  rewrite <- (Int.repr_signed i), Int.neg_repr.
  rewrite Int.signed_repr.
    intuition.
    apply congr_opp.
    eapply congr_trans. 2: eassumption.
    auto with congr.
  unfold Int.min_signed, Int.max_signed in *.
  split.
    cut (Int.signed i <= Int.half_modulus - 1). intuition.
    apply Int.signed_range.
  cut (- Int.half_modulus + 1 <= Int.signed i); intuition.
Qed.

Lemma ssi_neg_valid x :
  si_valid x →
  si_valid (ssi_neg x).
Proof.
  unfold ssi_neg.
  destruct zle.
  destruct zeq; intros _; discriminate.
  destruct congr_dec.
  unfold si_valid.
  simpl. intuition.
  discriminate.
Qed.

Lemma ssi_neg_reduced x :
  si_reduced x →
  si_reduced (ssi_neg x).
Proof.
  unfold si_reduced. unfold ssi_neg.
  destruct zle. destruct zeq; simpl; intuition.
  discriminate.
  destruct congr_dec.
  simpl. intros. split. apply congr_opp. intuition auto with congr.
  intros. intuition.
  intros; apply si_top_reduced. discriminate.
Qed.

Definition ssi_not (i: strided_interval) : strided_interval :=
  si_add Int.min_signed Int.max_signed (ssi_neg i) (si_const Int.signed Int.mone).

Lemma ssi_not_valid x :
  si_valid x → si_valid (ssi_not x).
Proof.
  intros.
  eapply si_add_valid.
  apply Int.signed_range.
  easy.
  now apply ssi_neg_valid.
  apply si_const_valid.
Qed.

Lemma ssi_not_reduced x :
  si_valid x →
  si_reduced x →
  si_reduced (ssi_not x).
Proof.
  intros. apply (si_add_reduced Int.signed). discriminate. apply ssi_neg_valid; auto.
  discriminate. apply ssi_neg_reduced; auto.
  apply si_const_reduced.
Qed.

Definition ssi_sub (x y: strided_interval) : strided_interval :=
  si_add Int.min_signed Int.max_signed x (ssi_neg y).

Lemma ssi_sub_valid x y :
  si_valid x → si_valid y → si_valid (ssi_sub x y).
Proof.
  intros X Y. eapply si_add_valid. apply Int.signed_range. easy. easy.
  now apply ssi_neg_valid.
Qed.

Lemma ssi_sub_reduced x y :
  si_valid x → si_reduced x →
  si_valid y → si_reduced y →
  si_reduced (ssi_sub x y).
Proof.
  intros.
  apply (si_add_reduced Int.signed Int.min_signed Int.max_signed); auto. discriminate.
  apply ssi_neg_valid; auto.
  apply ssi_neg_reduced; auto.
Qed.

(* Left multiplication by a signed constant. *)
Definition ssi_mul_l (x y: strided_interval) : strided_interval :=
  match x.(si_stride) with
  | N0 =>
    let k : Z := x.(si_low_bound) in
    match k with
    | Z0 => si_const Int.signed Int.zero
    | Zpos k' =>
      let l : Z := k * y.(si_low_bound) in
      if Z_le_dec Int.min_signed l
      then let u : Z := k * y.(si_up_bound) in
           if Z_le_dec u Int.max_signed
           then {| si_stride := Npos k' * y.(si_stride)
                 ; si_low_bound := l
                 ; si_up_bound := u
                |}
           else ssi_top
      else ssi_top
    | Zneg k' =>
      let l : Z := k * y.(si_up_bound) in
      if Z_le_dec Int.min_signed l
      then let u : Z := k * y.(si_low_bound) in
           if Z_le_dec u Int.max_signed
           then
             (* For soundness, check that y is reduced *)
             if congr_dec y.(si_stride) y.(si_low_bound) y.(si_up_bound)
             then {| si_stride := Npos k' * y.(si_stride)
                   ; si_low_bound := l
                   ; si_up_bound := u
                  |}
             else ssi_top
           else ssi_top
      else ssi_top
    end
  | _ => ssi_top
  end.

Lemma ssi_mul_l_sound : ∀ x y,
  lift_binop Int.mul (γ x) (γ y) ⊆ γ (ssi_mul_l x y).
Proof.
  simpl.
  intros x y ? (i & j & (I&I') & (J&J') & ->).
  unfold ssi_mul_l.
  case_eq (x.(si_stride)).
  2: intros ? _; apply si_gamma_top, Int.signed_range.
  intros Hs. rewrite Hs in I'. rewrite (congr_0_eq _ _ I') in *.
  rewrite Int.mul_signed.
  case_eq (Int.signed i);[|intros k'|intros k']; intros Hk.
      apply si_const_sound.
    destruct Z_le_dec. 2: apply si_gamma_top, Int.signed_range.
    destruct Z_le_dec. 2: apply si_gamma_top, Int.signed_range.
    assert (Int.min_signed <= Zpos k' * Int.signed j <= Int.max_signed).
      split.
        apply Zle_trans with (Zpos k' * y.(si_low_bound)). auto.
        apply Zmult_le_compat_l; intuition.
      apply Zle_trans with (Zpos k' * y.(si_up_bound)).
        apply Zmult_le_compat_l; intuition.
      auto.
    split; rewrite Int.signed_repr; auto.
    split; apply Zmult_le_compat_l; intuition.
    unfold si_low_bound at 2.
    unfold si_stride at 1.
    rewrite Z_of_N_mult. apply congr_mult_l_compat; auto.
  destruct Z_le_dec. 2: apply si_gamma_top, Int.signed_range.
  destruct Z_le_dec. 2: apply si_gamma_top, Int.signed_range.
  destruct congr_dec as [RED|]. 2: apply si_gamma_top, Int.signed_range.
  assert (Int.min_signed <= Zneg k' * Int.signed j <= Int.max_signed) by Psatz.nia.
  Opaque Z.mul N.mul. split; simpl. Transparent Z.mul N.mul.
  rewrite Int.signed_repr; auto. Psatz.nia.
  rewrite Int.signed_repr; auto.
  rewrite Z_of_N_mult.
  eapply congr_divide. apply congr_mult_l_compat.
  eapply congr_trans. apply congr_sym. apply RED. auto.
  exists (-1). Psatz.lia.
Qed.

Lemma ssi_mul_l_valid x y:
  si_valid y →
  si_valid (ssi_mul_l x y).
Proof.
  unfold ssi_mul_l. intros H.
  destruct x.(si_stride). 2: discriminate.
  destruct x.(si_low_bound). apply si_const_valid.
  destruct Z_le_dec. 2: discriminate.
  destruct Z_le_dec. 2: discriminate.
  apply Zmult_le_compat_l; auto. intuition.
  destruct Z_le_dec. 2: discriminate.
  destruct Z_le_dec. 2: discriminate.
  destruct congr_dec. 2: discriminate.
  red. unfold si_low_bound at 1. unfold si_up_bound at 2.
  red in H. clear -H. Psatz.nia.
Qed.

Lemma ssi_mul_l_reduced x y:
  si_reduced y →
  si_reduced (ssi_mul_l x y).
Proof.
  intros RED.
  assert (si_reduced ssi_top) by (apply si_top_reduced; discriminate).
  unfold ssi_mul_l.
  destruct x.(si_stride); auto.
  destruct x.(si_low_bound). apply si_const_reduced.
  destruct Z_le_dec; auto.
  destruct Z_le_dec; auto.
  split. unfold si_low_bound at 2; unfold si_up_bound at 2. unfold si_stride at 1.
  rewrite Z_of_N_mult. apply congr_mult_l_compat, RED.
  unfold si_low_bound at 1; unfold si_up_bound at 1. unfold si_stride at 1.
  intros K. assert (y.(si_stride) = N0) as ->. apply RED.
  assert (Zpos p * (y.(si_low_bound) - y.(si_up_bound)) = 0) as Q by Psatz.lia.
  destruct (Zmult_integral _ _ Q). exfalso. discriminate.
  Psatz.lia.
  auto.
  destruct Z_le_dec; auto.
  destruct Z_le_dec; auto.
  destruct congr_dec; auto.
  split. unfold si_low_bound at 2; unfold si_up_bound at 3. unfold si_stride at 1.
  rewrite Z_of_N_mult. eapply congr_divide. apply congr_mult_l_compat, congr_sym. eapply RED.
  exists (-1). zify. Psatz.lia.
  unfold si_low_bound at 1; unfold si_up_bound at 2. unfold si_stride at 1.
  intros K. assert (y.(si_stride) = N0) as ->. apply RED.
  assert (Zneg p * (y.(si_low_bound) - y.(si_up_bound)) = 0) as Q by Psatz.lia.
  destruct (Zmult_integral _ _ Q). exfalso. discriminate.
  Psatz.lia.
  auto.
Qed.

Definition ssi_mul x y :=
  match x.(si_stride) with
  | N0 => ssi_mul_l x y
  | _ => ssi_mul_l y x
  end.

Lemma ssi_mul_valid x y :
  si_valid x →
  si_valid y →
  si_valid (ssi_mul x y).
Proof.
  intros. unfold ssi_mul. destruct x.(si_stride); apply ssi_mul_l_valid; auto.
Qed.

Lemma ssi_mul_reduced x y :
  si_reduced x →
  si_reduced y →
  si_reduced (ssi_mul x y).
Proof.
  intros. unfold ssi_mul. destruct x.(si_stride); apply ssi_mul_l_reduced; auto.
Qed.

Lemma ssi_mul_sound x y :
  lift_binop Int.mul (γ x) (γ y) ⊆ γ (ssi_mul x y).
Proof.
  unfold ssi_mul.
  case_eq (x.(si_stride)). intros Hx.
  apply ssi_mul_l_sound.
  intros ? _ ? (i & j & I & J & ->).
  apply ssi_mul_l_sound.
  exists j; exists i. intuition.
  simpl. apply Int.mul_commut.
Qed.

Definition print {X} (s: string) (x: X) : X := x.
Lemma print_id {X s x} : @print X s x = x.
Proof. reflexivity. Qed.
Global Opaque print.

Definition ssi_shl (x y: strided_interval) : strided_interval :=
  match y.(si_stride) with
  | N0 =>
    (* let y' := two_p y.(si_low_bound) in *)
    let y' := Int.shl Int.one (Int.repr y.(si_low_bound)) in
    ssi_mul_l (si_const Int.signed y') x
  | _ =>
    print
      "Warning ssi: shl"
    ssi_top
  end.

Lemma ssi_shl_sound x y :
  lift_binop Int.shl (γ x) (γ y) ⊆ γ (ssi_shl x y).
Proof.
  unfold ssi_shl.
  case_eq (y.(si_stride)). 2: rewrite print_id; intros; apply ssi_top_sound.
  intros Hy ? (i & j & I & J & ->).
  simpl. rewrite (Int.shl_mul i j).
  apply ssi_mul_l_sound.
  exists (Int.shl Int.one j). exists i. intuition.
  2: now rewrite Int.mul_commut.
  destruct J as (_ & J).
  rewrite Hy in J.
  rewrite (congr_0_eq _ _ J). clear J.
  rewrite Int.repr_signed.
  apply si_const_sound.
Qed.

Definition ssi_divs_r (x: strided_interval) (y: positive) : strided_interval :=
  let xs := Z.of_N x.(si_stride) in
  let y' := Z.pos y in
  let div x := if zlt x 0 then (x + y' - 1) / y' else x / y' in
  {| si_stride := if Zdivides_dec y' xs
                  && (zeq (Z.sgn x.(si_low_bound)) (Z.sgn x.(si_up_bound))
                   || Zdivides_dec y' x.(si_low_bound))
                  then N.div x.(si_stride) (N.pos y)
                  else 1%N
   ; si_low_bound := div x.(si_low_bound)
   ; si_up_bound := div x.(si_up_bound)
  |}.

 Ltac elim_div :=
   unfold Zdiv, Zmod;
   repeat
     match goal with
     |  H : context[ Zdiv_eucl ?X ?Y ] |-  _ =>
        generalize (Z_div_mod_full X Y) ; destruct (Zdiv_eucl X Y)
     |  |-  context[ Zdiv_eucl ?X ?Y ] =>
        generalize (Z_div_mod_full X Y) ; destruct (Zdiv_eucl X Y)
     end; unfold Remainder.
 
Lemma ssi_divs_r_valid x y :
  si_valid x →
  si_valid (ssi_divs_r x y).
Proof.
  unfold ssi_divs_r, si_valid. simpl.
  repeat destruct zlt.
  elim_div. Psatz.nia.
  elim_div. cut (z <= 0 ∨ 0 < z); Psatz.nia.
  Psatz.lia.
  elim_div. Psatz.nia.
Qed.

(*
Lemma ssi_divs_r_sound x y i j :
  γ x i →
  Int.signed j = Z.pos y →
  γ (ssi_divs_r x y) (Int.divs i j).
Proof.
  unfold γ, ssi_gamma.
  intros I K. simpl.
  destruct I as [I (β, I')].
  unfold Int.divs, si_gamma; simpl.
  rewrite Int.signed_repr.
  +
  rewrite Int.Zdiv_round_Zdiv. 2: Psatz.lia.
  rewrite K. clear K.
  split.
  repeat destruct zlt; try Psatz.lia; DLib.elim_div.
  Psatz.nia.
  split; [ | cut (z1 <= 0 ∨ 0 < z1) ]; Psatz.nia.
  split; [ cut (z1 < 0 ∨ 0 <= z1) | ]; Psatz.nia.
  Psatz.nia.

  destruct (Ndivides_dec (Npos y) (si_stride x)) as [D|D];
  destruct Zdivides_dec as [D' | ?]; simpl in *; try contradiction.
  2: auto with congr.
  clear D'.
  destruct D as (α & D). rewrite D in *.
  rewrite I' in *. clear I'.
  destruct (_ || _) eqn: Hb. 2: auto with congr.
  exists β. rewrite N2Z.inj_div. rewrite D. simpl.
  rewrite Z_div_mult_full. 2: Psatz.lia.
  destruct (zlt (si_low_bound x + _) _).
  destruct zlt; try Psatz.lia.
  DLib.elim_div. Psatz.nia.

  destruct zlt. destruct zeq. Psatz.lia. simpl in Hb.
  destruct Zdivides_dec as [(γ & D') | ?]. 2: discriminate.
  clear Hb. rewrite D' in *. clear D'.
  rewrite (Z.mul_assoc ). rewrite Z_div_plus_full. 2: Psatz.lia.
  rewrite Z_div_mult_full. 2: Psatz.lia.
  clear. DLib.elim_div. Psatz.nia.
  clear. DLib.elim_div. Psatz.nia.

+
  rewrite K in *. clear K.
  pose proof (Int.signed_range i).
  rewrite I' in *. clear i I'.
  rewrite Int.Zdiv_round_Zdiv. 2: Psatz.lia.
  assert (Int.min_signed <= 0) by now compute.
  assert (0 <= Int.max_signed) by now compute.
  destruct zlt.
  DLib.elim_div. Psatz.nia.
  DLib.elim_div. Psatz.nia.
Qed.
*)

Definition ssi_divs (x y: strided_interval) : strided_interval :=
  match y.(si_stride) with
  | N0 =>
    match y.(si_low_bound) with
    | Z.pos p => ssi_divs_r x p
    | _ => ssi_top
    end
  | _ => ssi_top
  end.

Lemma ssi_divs_valid x y : si_valid x → si_valid (ssi_divs x y).
Proof.
  unfold ssi_divs. destruct y.(si_stride). 2: now intros _; compute.
  destruct y.(si_low_bound); try now intros _; compute.
  apply ssi_divs_r_valid.
Qed.

(*
Lemma ssi_divs_sound x y : lift_binop Int.divs (γ x) (γ y) ⊆ γ (ssi_divs x y).
Proof.
  unfold ssi_divs.
  intros ? (i & j & I & J & ->).
  destruct y as [[|ys] [|yl|?] yu];
    try apply si_gamma_top, Int.signed_range.
  simpl.
  apply ssi_divs_r_sound; auto.
  destruct J as [J J']. simpl in *. now rewrite (congr_0_eq _ _ J').
Qed.
*)

(* TODO: refine the stride if possible. *)
Definition ssi_shr_l (x: strided_interval) (y: Z) : strided_interval :=
  let m := Z.shiftr x.(si_low_bound) y in
  let M := Z.shiftr x.(si_up_bound) y in
  {| si_stride := if zeq m M then 0 else 1
   ; si_low_bound := m
   ; si_up_bound  := M
  |}.

Lemma pow2_pos n : 0 <= n → 2 ^ n > 0.
Proof.
  destruct n as [|n|]; try Psatz.lia. intros _.
  simpl. unfold Z.pow_pos.
  induction n using Pos.peano_ind. reflexivity.
  rewrite Pos.iter_succ.
  intuition.
Qed.

(*
Lemma ssi_shr_l_sound x y i :
  0 <= y < Int.modulus ->
  γ x i ->
  γ (ssi_shr_l x y) (Int.shr i (Int.repr y)).
Proof.
  intros [Hy Hy'] (A, B).
  assert (y mod Int.modulus = y) as Hys by (apply Z.mod_small; auto).
  pose proof (pow2_pos y Hy) as H2y.
  rewrite Int.shr_div_two_p.
  unfold ssi_shr_l.
  rewrite ! Z.shiftr_div_pow2; auto.
  simpl. rewrite Hys, two_p_equiv.
  red. red. red. simpl.
  rewrite Int.signed_repr.
  assert (∀ A B:Prop, A → (A → B) → A ∧ B) as NS by intuition.
  apply NS.
  DLib.elim_div. Psatz.nia.
  intros K.
  destruct zeq as [EQ|NE]; auto with congr.
  exists 42. simpl. rewrite <- EQ in K. Psatz.lia.
  clear -H2y.
  generalize (Int.signed_range i).
  change Int.min_signed with (-2147483648).
  change Int.max_signed with (2147483647).
  DLib.elim_div. Psatz.nia.
Qed.
 *)

Definition ssi_shr (x y: strided_interval) : strided_interval :=
  match y.(si_stride) with
  | N0 => ssi_shr_l x (Int.unsigned (Int.repr y.(si_low_bound)))
  | _ => ssi_top
  end.

Lemma signed_mod_mod j :
  Int.signed j mod Int.modulus = Int.unsigned j.
Proof.
  unfold Int.signed. destruct zlt.
  apply Z.mod_small. auto with ints.
  rewrite Zminus_mod.
  rewrite Z.sub_0_r.
  rewrite Zmod_mod.
  apply Z.mod_small. auto with ints.
Qed.

(*
Lemma ssi_shr_sound x y i j :
  γ x i -> γ y j ->
  γ (ssi_shr x y) (Int.shr i j).
Proof.
  destruct y as [s l u].
  intros X [Y Y'].
  unfold ssi_shr. simpl in *.
  destruct s.
  + apply congr_0_eq in Y'. subst l.
    generalize (ssi_shr_l_sound x (Int.unsigned j) _ (Int.unsigned_range _) X).
    rewrite Int.repr_unsigned.
    now rewrite signed_mod_mod.
  + apply si_gamma_top, Int.signed_range.
Qed.
 *)

Definition znegb (z: Z) : { z < 0 } + { z >= 0 }.
  refine
  match z return { z < 0 } + { z >= 0 } with Z0 | Zpos _ => right _ | Zneg _ => left eq_refl end.
Proof.
  abstract Psatz.lia.
  abstract Psatz.lia.
Defined.

Definition ssi_shru (x y: strided_interval) : strided_interval :=
  match y.(si_stride) with
  | N0 =>
    let y' := Int.unsigned (Int.repr y.(si_low_bound)) in
    if Z_zerop y'
    then x
    else if znegb x.(si_low_bound)
                      (*
         then let (m, M) := Interval.shru_top y' in
              {| si_stride := 1%N; si_low_bound := m; si_up_bound := M |}
                       *)
         then ssi_top
         else ssi_shr_l x y'
  | _ => ssi_top
  end.

(*
Lemma ssi_shru_sound x y i j :
  γ x i -> γ y j ->
  γ (ssi_shru x y) (Int.shru i j).
Proof.
  destruct x as [xs xl xu].
  destruct y as [ys yl yu].
  intros [X X'] [Y Y'].
  unfold ssi_shru. simpl in *.
  destruct ys.
  + apply congr_0_eq in Y'. subst yl.
    destruct Z_zerop as [Z|NZ].
    * assert (Int.signed j = 0).
      clear -Z. generalize (Int.signed_range j).
      change Int.min_signed with (-2147483648).
      change Int.max_signed with (2147483647).
      change Int.modulus with (4294967296) in Z.
      revert Z.
      elim_div. Psatz.lia.
      assert (j = Int.repr 0). rewrite <- (Int.repr_signed j). congruence.
      subst.
      rewrite Int.shru_zero. split; auto.
    * destruct znegb.
      (*
      - generalize (Interval.shru_top_correct i _ NZ).
        destruct Interval.shru_top as [m M].
        split. easy. auto with congr.
       *)
      - apply si_gamma_top, Int.signed_range.
      - assert (Int.unsigned i = Int.signed i) as L.
        revert X. generalize (Int.unsigned_range i).
        unfold Int.signed. destruct zlt; intuition.
        rewrite <- Int.shr_shru_positive.
        rewrite signed_mod_mod.
        rewrite <- (Int.repr_unsigned j) at 2.
        apply ssi_shr_l_sound.
        auto with ints.
        split; auto.
        rewrite <- L.
        generalize (Int.unsigned_range i). Psatz.lia.
  + apply si_gamma_top, Int.signed_range.
Qed.
*)

Definition ssi_mods_r (x: strided_interval) (y: positive) : strided_interval :=
  if x.(si_stride)
  then
    let r := Z.rem x.(si_low_bound) (Zpos y) in
    {| si_stride := N0; si_low_bound := r; si_up_bound := r |}
  else
    if zle 0 x.(si_low_bound)
    then {| si_stride := 1%N; si_low_bound := 0; si_up_bound := Zpos y - 1 |}
    else print "Warning ssi: mods" ssi_top.

(*
Lemma ssi_mods_r_sound x y i j:
  i ∈ γ(x) →
  Int.signed j = Z.pos y →
  γ (ssi_mods_r x y) (Int.mods i j).
Proof.
  unfold ssi_mods_r.
  destruct x as [xs xl xu].
  intros [I I'] J. simpl in I, I'. unfold si_stride, si_low_bound.
  assert (Zpos y ≠ 0) as NZ by Psatz.lia.
  assert (Int.min_signed <= Z.rem (Int.signed i) (Z.pos y) <= Int.max_signed).
  { generalize (Int.signed_range j). rewrite J.
    generalize (Int.signed_range i). clear -NZ.
    unfold Int.min_signed, Int.max_signed, Int.half_modulus, Int.modulus. simpl.
    generalize (Z.rem_bound_abs (Int.signed i) _ NZ).
    rewrite (Z.rem_eq _ _ NZ). Psatz.lia. }
  destruct xs as [|xs].
  apply congr_0_eq in I'. subst.
  assert (Z.rem (Int.signed i) (Zpos y) = Int.signed (Int.mods i j)) as K.
  unfold Int.mods. rewrite J. rewrite Int.signed_repr. reflexivity.
  auto.
  rewrite K. split. intuition. auto with congr.
  destruct zle.
  2: try rewrite print_id; apply (gamma_top _ _ _ _ ssi_adom).
  split. 2: auto with congr.
  unfold si_low_bound, si_up_bound.
  unfold Int.mods. rewrite J. rewrite Int.signed_repr; auto.
  split. apply Z.rem_nonneg; Psatz.lia.
  generalize (Zquot.Zrem_lt_pos (Int.signed i) (Z.pos y)).
  Psatz.lia.
Qed.

Definition ssi_mods (x y: strided_interval) : strided_interval :=
  match y.(si_stride) with
  | N0 =>
    match y.(si_low_bound) with
    | Z.pos p => ssi_mods_r x p
    | _ => (⊤)
    end
  | _ => (⊤)
  end.

Lemma ssi_mods_sound x y : lift_binop Int.mods (γ x) (γ y) ⊆ γ (ssi_mods x y).
Proof.
  unfold ssi_mods.
  intros ? (i & j & I & J & ->).
  destruct y as [[|ys] [|yl|?] yu];
    try apply si_gamma_top, Int.signed_range.
  simpl.
  apply ssi_mods_r_sound; auto.
  destruct J as [J J']. simpl in *. now rewrite (congr_0_eq _ _ J').
Qed.
*)

Definition ssi_and (x y: strided_interval) : strided_interval :=
  match y.(si_stride) with
  | N0 =>
    match x.(si_stride) with
    | N0 => si_const Int.signed (Int.and (Int.repr x.(si_low_bound)) (Int.repr (y.(si_low_bound))))
    | _ =>
      match y.(si_low_bound) with
      | Zneg _ => ssi_top
      | Z0 => si_const Int.signed Int.zero
      | Zpos p =>
        {| si_stride := 1; si_low_bound := 0
         ; si_up_bound := two_power_pos (Pos.size p) - 1 |}
      end
    end
  | _ =>
    print
      "Warning ssi: and"
    ssi_top
  end.

(*
Eval vm_compute in
    ssi_and (si_top Int.min_signed Int.max_signed)
            (si_const Int.signed (Int.repr 1)).
*)

Lemma ssi_and_valid (x y: strided_interval) :
  si_valid (ssi_and x y).
Proof.
  unfold ssi_and, si_valid.
  destruct y as [s l u].
  destruct s. 2: now rewrite print_id; compute.
  destruct x.(si_stride). intuition.
  destruct l. easy.
  simpl. destruct shift_pos; intuition.
  now compute.
Qed.

Lemma ssi_and_reduced (x y: strided_interval) :
  si_reduced (ssi_and x y).
Proof.
  unfold ssi_and.
  destruct y as [s l u].
  destruct s. 2: now rewrite print_id; split; auto with congr; compute.
  destruct x.(si_stride) as [|xs]. apply si_const_reduced.
  destruct l. apply si_const_reduced.
  2: now apply si_top_reduced; compute.
  simpl. split; auto with congr. simpl.
  cut (∀ p, shift_pos p 1 > 1)%positive.
  intros K; specialize (K (Pos.size p)). destruct shift_pos; discriminate.
  clear. induction p using Pos.peano_ind. reflexivity.
  unfold shift_pos. rewrite Pos.iter_succ.
  fold (shift_pos p 1). zify. intuition.
Qed.

Definition ssi_xor_w (x y: strided_interval) : strided_interval :=
  match x.(si_stride) with
  | N0 =>
    match x.(si_stride) with
    | N0 => si_const Int.signed (Int.xor (Int.repr x.(si_low_bound)) (Int.repr y.(si_low_bound)))
    | _ => ssi_top end
  | _ => ssi_top
  end.

Notation todo2 := (fun s _ _ => print ("TODO ssi: " ++ s)%string (NotBot ssi_top)).
Notation todobw1 := (fun s x _ => print ("TODO ssi: " ++ s)%string (NotBot x)).
Notation todobw2 := (fun s x y _ => print ("TODO ssi bw2:" ++ s)%string (NotBot (x, y))).

Definition red2 {X Y} (x: X+⊥) (y: Y+⊥) : (X * Y)+⊥ :=
  match x, y with
  | Bot, _ | _, Bot => Bot
  | NotBot x', NotBot y' => NotBot (x', y')
  end.

Lemma red2_elim {X Y A B} (x: X+⊥) (y: Y+⊥) `(gamma_op X A) `(gamma_op Y B):
  ∀ a : A * B,
    fst a ∈ γ x →
    snd a ∈ γ y →
    a ∈ γ(red2 x y).
Proof.
  unfold red2.
  intros (a, b); simpl.
  destruct x as [|x']. exact (λ H _, H). intros Hx.
  destruct y as [|y']. exact id.
  exact (conj Hx).
Qed.

Global Opaque red2.

Definition ssi_backward_add (x y res: strided_interval) :=
  red2 (si_meet x (ssi_sub res y)) (si_meet y (ssi_sub res x)).

Definition ssi_backward_le (x y: strided_interval) :=
  red2
  (si_meet x {| si_stride := 1; si_low_bound := Int.min_signed; si_up_bound := y.(si_up_bound) |})
   (si_meet {| si_stride := 1; si_low_bound := x.(si_low_bound); si_up_bound := Int.max_signed |} y).

Definition cast_usi (x: strided_interval) : bool :=
  match x.(si_low_bound) with
  | Zneg _ => false
  | _ => zle x.(si_up_bound) Int.max_unsigned
  end.

Lemma cast_usi_true x :
  cast_usi x = true →
  0 <= x.(si_low_bound) ∧ x.(si_up_bound) <= Int.max_unsigned.
Proof.
  unfold cast_usi.
  destruct x as [l u s].
  simpl. destruct u; intuition;
  destruct zle; intuition.
Qed.

Lemma cast_usi_gamma x i :
  cast_usi x = true →
  γ x i →
  Int.signed i = Int.unsigned i.
Proof.
  unfold γ, ssi_gamma.
  intros H. apply cast_usi_true in H.
  unfold si_gamma.
  unfold Int.signed.
  intros [K _].
  unfold Int.half_modulus, Int.max_unsigned in *.
  destruct zlt. auto.
  exfalso.
  pose proof (Int.unsigned_range i).
  Psatz.lia.
Qed.

Definition ssi_backward_leu (x y: strided_interval) :=
  if cast_usi x && cast_usi y
  then ssi_backward_le x y
  else NotBot (x, y).

Lemma signed_inj x y :
  Int.signed x = Int.signed y →
  x = y.
Proof.
  intros H.
  rewrite <- (Int.repr_signed x), <- (Int.repr_signed y).
  exact (f_equal _ H).
Qed.

Lemma ssi_backward_le_sound x y i j :
  si_gamma Int.signed x i →
  si_gamma Int.signed y j →
  Int.lt j i = false →
  (i, j) ∈ γ (ssi_backward_le x y).
Proof.
  intros I J K.
  unfold ssi_backward_le.
  unfold Int.lt in K. destruct zlt. discriminate. clear K.
  apply red2_elim; apply si_meet_sound; auto using signed_inj; intuition;
  unfold si_gamma; simpl; intuition.
  apply Int.signed_range. apply Zle_trans with (Int.signed j); intuition. apply J.
  apply Zle_trans with (Int.signed i); intuition. apply I. apply Int.signed_range.
Qed.

Lemma ssi_backward_leu_sound x y i j :
  si_gamma Int.signed x i →
  si_gamma Int.signed y j →
  Int.ltu j i = false →
  (i, j) ∈ γ (ssi_backward_leu x y).
Proof.
  unfold ssi_backward_leu.
  case_eq (cast_usi x). intros X.
  2: now simpl; intuition; split.
  case_eq (cast_usi y); red. intros Y.
  2: now simpl; intuition; split.
  intros H H0 H1. apply ssi_backward_le_sound; auto.
  unfold Int.lt.
  rewrite (cast_usi_gamma x i); eauto.
  rewrite (cast_usi_gamma y j); eauto.
Qed.

(** Reduced valid interval as a strided interval with stride 1. *)
Definition si_interval (l u: Z) : strided_interval+⊥ :=
  match Z_dec l u with
  | inleft (left LT) => NotBot {| si_stride := 1; si_low_bound := l; si_up_bound := u |}
  | inleft (right GT) => Bot
  | inright EQ => NotBot {| si_stride := 0; si_low_bound := l; si_up_bound := l |}
  end.

Definition ssi_backward_lt (x y: strided_interval) :=
  red2
  (botbind (si_meet x) (si_interval Int.min_signed (y.(si_up_bound) - 1)))
   (botbind (si_meet y) (si_interval (x.(si_low_bound) + 1) Int.max_signed)).

Definition ssi_backward_ltu (x y: strided_interval) :=
  if cast_usi x && cast_usi y
  then ssi_backward_lt x y
  else NotBot (x, y).

Lemma ssi_backward_lt_sound x y i j :
  γ x i → γ y j →
  Int.lt i j = true →
  (i, j) ∈ γ (ssi_backward_lt x y).
Proof.
  simpl.
  intros ((I1&I2)&I3).
  intros ((J1&J2)&J3) K.
  unfold Int.lt in K. destruct zlt. 2: discriminate. clear K.
  pose proof (Int.signed_range i) as (U&V).
  pose proof (Int.signed_range j) as (U'&V').
  apply red2_elim.
  apply botbind_spec with i.
  intros. apply (si_meet_sound Int.signed). auto using signed_inj. repeat (split; auto).
  unfold si_interval.
  destruct Z_dec as [[LT|GT]|EQ]; try Psatz.lia.
  split; simpl; try split; auto with congr; Psatz.lia.
  assert (Int.min_signed = Int.signed i). intuition.
  split; simpl; try split; auto with congr; try Psatz.lia. rewrite H. auto with congr.
  apply botbind_spec with j.
  intros. apply (si_meet_sound Int.signed). auto using signed_inj. repeat (split; auto).
  unfold si_interval.
  destruct Z_dec as [[LT|GT]|EQ]; try Psatz.lia.
  split; simpl; try split; auto with congr; Psatz.lia.
  assert (Int.max_signed = Int.signed j). intuition.
  split; simpl; try split; auto with congr; try Psatz.lia. rewrite EQ, H. auto with congr.
Qed.

Lemma ssi_backward_ltu_sound x y i j :
  γ x i → γ y j →
  Int.ltu i j = true →
  (i, j) ∈ γ (ssi_backward_ltu x y).
Proof.
  unfold ssi_backward_ltu.
  case_eq (cast_usi x). intros X.
  2: now intros; split.
  case_eq (cast_usi y); red. intros Y.
  2: now intros; split.
  intros.
  apply ssi_backward_lt_sound; auto.
  unfold Int.lt.
  rewrite (cast_usi_gamma x); eauto.
  rewrite (cast_usi_gamma y); eauto.
Qed.

Definition ssi_backward_ne (x y: strided_interval) :=
  match ssi_backward_lt x y, ssi_backward_lt y x with
  | z, Bot => z
  | Bot, NotBot (y', x') => NotBot (x', y')
  | NotBot (x1, y1), NotBot (y2, x2) =>
    NotBot (si_join x1 x2, si_join y1 y2)
  end.

Lemma ssi_backward_ne_sound x y i j :
  γ x i → γ y j →
  Int.eq i j = false →
  (i, j) ∈ γ (ssi_backward_ne x y).
Proof.
  unfold ssi_backward_ne.
  intros I J NE.
  assert (Int.lt i j = true ∨ Int.lt j i = true) as K.
    generalize (Int.eq_spec i j). destruct Int.eq. discriminate. clear NE. intros NE.
    unfold Int.lt. destruct zlt. now left. destruct zlt. now right.
    absurd (Int.signed i = Int.signed j). auto using signed_inj.
    intuition.
  clear NE.
  pose proof (ssi_backward_lt_sound x y i j I J) as L.
  pose proof (ssi_backward_lt_sound y x j i J I) as R.
  destruct (ssi_backward_lt x y) as [| (x1, y1) ];
  destruct (ssi_backward_lt y x) as [| (y2, x2) ].
  intuition.
  destruct K as [K | K]. elim (L K). destruct (R K) as [U V]; exact (conj V U).
  intuition.
  split; apply si_join_sound; auto using signed_inj;
  (destruct K as [K | K]; [ specialize (L K); left; apply L | specialize (R K); right; apply R ]).
Qed.

Definition swap {A} (xy: A * A) : (A * A) :=
  let (x,y) := xy in (y, x).

Lemma swap_elim {A B} `(gamma_op A B) (x: A * A) (b: B * B):
  swap b ∈ γ x →
  b ∈ γ(swap x).
Proof.
  unfold swap.
  destruct x as (x, y), b as (a, b).
  exact (λ H, let '(conj X Y) := H in conj Y X).
Qed.
Global Opaque swap.

Definition ssi_backward_cmp (c:comparison) (x y res: strided_interval) :=
  match res.(si_stride) with
  | N0 =>
    if Z_zerop res.(si_low_bound)
    then
      (* test is false *)
      match c with
      | Cne => let ab := si_meet x y in red2 ab ab
      | Cgt => ssi_backward_le x y
      | Clt => botlift_fun1 swap (ssi_backward_le y x)
      | Cge => ssi_backward_lt x y
      | Cle => botlift_fun1 swap (ssi_backward_lt y x)
      | Ceq => ssi_backward_ne x y
      end
    else
      if Z_eq_dec res.(si_low_bound) 1
      then
        (* test is true *)
        match c with
        | Ceq => let ab := si_meet x y in red2 ab ab
        | Cle => ssi_backward_le x y
        | Cge => botlift_fun1 swap (ssi_backward_le y x)
        | Clt => ssi_backward_lt x y
        | Cgt => botlift_fun1 swap (ssi_backward_lt y x)
        | Cne => ssi_backward_ne x y
        end
      else NotBot (x, y) (* should not happen: test returned exactly not a boolean *)
  | _ => NotBot (x, y)
  end.

Definition ssi_backward_cmpu (c:comparison) (x y res: strided_interval) :=
  match res.(si_stride) with
  | N0 =>
    if Z_zerop res.(si_low_bound)
    then
      (* test is false *)
      match c with
      | Cne => let ab := si_meet x y in red2 ab ab
      | Cgt => ssi_backward_leu x y
      | Clt => botlift_fun1 swap (ssi_backward_leu y x)
      | Cge => ssi_backward_ltu x y
      | Cle => botlift_fun1 swap (ssi_backward_ltu y x)
      | Ceq => ssi_backward_ne x y
      end
    else
      if Z_eq_dec res.(si_low_bound) 1
      then
        (* test is true *)
        match c with
        | Ceq => let ab := si_meet x y in red2 ab ab
        | Cle => ssi_backward_leu x y
        | Cge => botlift_fun1 swap (ssi_backward_leu y x)
        | Clt => ssi_backward_ltu x y
        | Cgt => botlift_fun1 swap (ssi_backward_ltu y x)
        | Cne => ssi_backward_ne x y
        end
      else NotBot (x, y) (* should not happen: test returned exactly not a boolean *)
  | _ => NotBot (x, y)
  end.

Definition of_bool (b: bool): int :=
  if b then Int.one else Int.zero.

Lemma ssi_backward_cmp_sound c :
  ∀ x y z, ∀ i j,
  γ x i → γ y j → γ z (of_bool (Int.cmp c i j)) →
    (i, j) ∈ γ(ssi_backward_cmp c x y z).
Proof.
  intros x y z i j. simpl. unfold ssi_backward_cmp. intros I J (L,K').
  case_eq (z.(si_stride)). 2: now split.
  intros Hs. rewrite Hs in K'. pose proof (congr_0_eq _ _ K') as K. clear K'.
  destruct Z_zerop as [Z0|NZ0].
  - destruct c.
  + (* eq *)
  apply ssi_backward_ne_sound; auto.
  simpl in *. destruct Int.eq. rewrite Z0 in K. discriminate. easy.
  + (* ne *)
  unfold si_gamma in I, J. simpl in *.
  generalize (Int.eq_spec i j). destruct Int.eq. intros ->.
  apply red2_elim; apply si_meet_sound; auto using signed_inj.
  simpl in *. rewrite Z0 in K. discriminate.
  + (* lt *)
  assert (Int.lt i j = false) as LT.
    simpl in *. unfold Int.lt in *. destruct zlt. rewrite Z0 in K. discriminate. easy.
  eapply botlift_fun1_spec with (_, _).
  2: eapply (ssi_backward_le_sound _ _ _ _ J I LT). intuition auto using swap_elim.
  + (* le *)
  assert (Int.lt j i = true) as LT.
    simpl in *. unfold Int.lt in *. destruct zlt. easy. rewrite Z0 in K. discriminate.
  eapply botlift_fun1_spec with (_, _).
  2: eapply (ssi_backward_lt_sound _ _ _ _ J I LT). intuition auto using swap_elim.
  + (* gt *)
  assert (Int.lt j i = false) as LT.
    simpl in *. unfold Int.lt in *. destruct zlt. rewrite Z0 in K. discriminate. easy.
  eapply (ssi_backward_le_sound _ _ _ _ I J LT).
  + (* ge *)
  assert (Int.lt i j = true) as LT.
    simpl in *. unfold Int.lt in *. destruct zlt. easy. rewrite Z0 in K. discriminate.
  apply (ssi_backward_lt_sound _ _ _ _ I J LT).
  - destruct Z_eq_dec as [Z1|]. 2: now split.
  destruct c; try now split.
  + (* eq *)
  unfold si_gamma in I, J. simpl in *.
  generalize (Int.eq_spec i j). destruct Int.eq. intros ->.
    apply red2_elim; apply si_meet_sound; auto using signed_inj; intuition.
  simpl in *. rewrite Z1 in K. discriminate.
  + (* ne *)
  apply ssi_backward_ne_sound; auto.
  simpl in *. destruct Int.eq. rewrite Z1 in K. discriminate. easy.
  + (* lt *)
  assert (Int.lt i j = true) as LT.
    simpl in *. unfold Int.lt in *. destruct zlt. easy. rewrite Z1 in K. discriminate.
  apply (ssi_backward_lt_sound _ _ _ _ I J LT).
  + (* le *)
  assert (Int.lt j i = false) as LT.
    simpl in *. unfold Int.lt in *. destruct zlt. rewrite Z1 in K. discriminate. easy.
  apply (ssi_backward_le_sound _ _ _ _ I J LT).
  + (* gt *)
  assert (Int.lt j i = true) as LT.
    simpl in *. unfold Int.lt in *. destruct zlt. easy. rewrite Z1 in K. discriminate.
  eapply botlift_fun1_spec with (_, _).
  2: apply (ssi_backward_lt_sound _ _ _ _ J I LT). intuition auto using swap_elim.
  + (* ge *)
  assert (Int.lt i j = false) as LT.
    simpl in *. unfold Int.lt in *. destruct zlt. rewrite Z1 in K. discriminate. easy.
  eapply botlift_fun1_spec with (_, _).
  2: apply (ssi_backward_le_sound _ _ _ _ J I LT). intuition auto using swap_elim.
Qed.

Lemma ssi_backward_cmpu_sound c :
  ∀ x y z, ∀ i j,
    γ x i → γ y j → γ z (of_bool (Int.cmpu c i j)) →
    (i, j) ∈ γ (ssi_backward_cmpu c x y z).
Proof.
  intros x y z i j. simpl. unfold ssi_backward_cmpu. intros I J (L,K').
  case_eq (z.(si_stride)). 2: now split.
  intros Hs. rewrite Hs in K'. pose proof (congr_0_eq _ _ K') as K. clear K'.
  destruct Z_zerop as [Z0|NZ0].
  destruct c.
  (* eq *)
  apply ssi_backward_ne_sound; auto.
  simpl in *. destruct Int.eq. rewrite Z0 in K. discriminate. easy.
  (* ne *)
  unfold si_gamma in I, J. simpl in *.
  generalize (Int.eq_spec i j). destruct Int.eq. intros ->.
    apply red2_elim; apply si_meet_sound; auto using signed_inj; intuition.
  simpl in *. rewrite Z0 in K. discriminate.
  (* lt *)
  assert (Int.ltu i j = false) as LT.
    simpl in *. unfold Int.ltu in *. destruct zlt. rewrite Z0 in K. discriminate. easy.
  eapply botlift_fun1_spec with (_, _).
  2: apply (ssi_backward_leu_sound _ _ _ _ J I LT). intuition auto using swap_elim.
  (* le *)
  assert (Int.ltu j i = true) as LT.
    simpl in *. unfold Int.ltu in *. destruct zlt. easy. rewrite Z0 in K. discriminate.
  eapply botlift_fun1_spec with (_, _).
  2: apply (ssi_backward_ltu_sound _ _ _ _ J I LT). intuition auto using swap_elim.
  (* gt *)
  assert (Int.ltu j i = false) as LT.
    simpl in *. unfold Int.ltu in *. destruct zlt. rewrite Z0 in K. discriminate. easy.
  apply (ssi_backward_leu_sound _ _ _ _ I J LT).
  (* ge *)
  assert (Int.ltu i j = true) as LT.
    simpl in *. unfold Int.ltu in *. destruct zlt. easy. rewrite Z0 in K. discriminate.
  apply (ssi_backward_ltu_sound _ _ _ _ I J LT).
  destruct Z_eq_dec as [Z1|]. 2: now split.
  destruct c; try now split.
  (* eq *)
  unfold si_gamma in I, J. simpl in *.
  generalize (Int.eq_spec i j). destruct Int.eq. intros ->.
    apply red2_elim; apply si_meet_sound; auto using signed_inj; intuition.
  simpl in *. rewrite Z1 in K. discriminate.
  (* ne *)
  apply ssi_backward_ne_sound; auto.
  simpl in *. destruct Int.eq. rewrite Z1 in K. discriminate. easy.
  (* lt *)
  assert (Int.ltu i j = true) as LT.
    simpl in *. unfold Int.ltu in *. destruct zlt. easy. rewrite Z1 in K. discriminate.
  generalize (ssi_backward_ltu_sound _ _ _ _ I J LT). simpl. intuition.
  (* le *)
  assert (Int.ltu j i = false) as LT.
    simpl in *. unfold Int.ltu in *. destruct zlt. rewrite Z1 in K. discriminate. easy.
  apply (ssi_backward_leu_sound _ _ _ _ I J LT).
  (* gt *)
  assert (Int.ltu j i = true) as LT.
    simpl in *. unfold Int.ltu in *. destruct zlt. easy. rewrite Z1 in K. discriminate.
  eapply botlift_fun1_spec with (_, _).
  2: apply (ssi_backward_ltu_sound _ _ _ _ J I LT). intuition auto using swap_elim.
  (* ge *)
  assert (Int.ltu i j = false) as LT.
    simpl in *. unfold Int.ltu in *. destruct zlt. rewrite Z1 in K. discriminate. easy.
  eapply botlift_fun1_spec with (_, _).
  2: apply (ssi_backward_leu_sound _ _ _ _ J I LT). intuition auto using swap_elim.
Qed.

Definition ssi_backward_boolval (x res: strided_interval) : strided_interval+⊥ :=
  match res.(si_stride) with
  | N0 =>
    if Z_zerop res.(si_low_bound)
    then NotBot (si_const Int.signed Int.zero)
    else if si_LE_dec x {| si_stride := 1%N; si_low_bound := 0; si_up_bound := 1 |}
         then NotBot (si_const Int.signed Int.one)
         else NotBot x
  | _ => NotBot x
  end.

Definition ssi_backward_notbool (x res: strided_interval) : strided_interval+⊥ :=
  match res.(si_stride) with
  | N0 =>
    if Z_eq_dec res.(si_low_bound) 1
    then NotBot (si_const Int.signed Int.zero)
    else NotBot x
  | _ => NotBot x
  end.

Instance ssiToString : ToString strided_interval := toString Int.min_signed Int.max_signed.

Definition ssi_booleans := {| si_stride := 1%N; si_low_bound := 0; si_up_bound := 1 |}.

(*
Instance ssi_dom : num_dom strided_interval :=
  {| as_adom := pre_lattice_of_adom ssi_adom
   ; meet x := botbind (si_meet x)
   (* ; size x := Just (si_size x)
   ; concretize x := Just (IntSet.of_list (List.map Int.repr (si_concretize x))) *)
   ; const := si_const Int.signed
   ; booleans := ssi_booleans
   ; range x f := match f with
                  | Signed => NotBot (Interval.ITV x.(si_low_bound) x.(si_up_bound))
                  | Unsigned => top
                  end
   ; neg x := NotBot (ssi_neg x)
   ; not x := NotBot (ssi_not x)
   ; notbool x := (* NotBot (ssi_notbool x) *) (NotBot ssi_booleans)
   ; boolval x := (* NotBot (ssi_boolval x) *) (NotBot ssi_booleans)
   
   ; add x y := NotBot (si_add Int.min_signed Int.max_signed x y)
   ; sub x y := NotBot (ssi_sub x y)
   ; mul x y := NotBot (ssi_mul x y)
   ; divs x y := NotBot (ssi_divs x y)
   ; shl x y := NotBot (ssi_shl x y)
   ; shru x y := NotBot (ssi_shru x y)
   ; and x y := NotBot (ssi_and x y)
   ; or x y := todo2 (to_string x ++ " | " ++ to_string y)%string x y
   ; xor x y := todo2 (to_string x ++ " ^ " ++ to_string y)%string x y

   ; is_in_itv := si_is_in_itv Int.signed

   ; backward_boolval := ssi_backward_boolval
   ; backward_notbool := ssi_backward_notbool
   ; backward_neg := todobw1 "neg"%string
   ; backward_not := todobw1 "not"%string
   
  ; backward_add := ssi_backward_add
  ; backward_sub := todobw2 "sub"%string
  ; backward_cmp := ssi_backward_cmp
  ; backward_cmpu := ssi_backward_cmpu
  ; backward_and x y z := (todobw2 "and"%string x y z) :: nil
  ; backward_or x y z := (todobw2 "or"%string x y z) :: nil

  |}.
*)

Lemma ssi_is_in_itv_sound (u v: int) (x: strided_interval) :
  si_is_in_itv Int.signed u v x = true →
  ∀ i, si_gamma Int.signed x i → Int.lt v i = false ∧ Int.lt i u = false.
Proof.
  unfold si_is_in_itv, si_gamma. rewrite andb_true_iff.
  destruct Z_le_dec as [U|U]. 2: intuition.
  destruct Z_le_dec as [V|V]. 2: intuition.
  intros _ i (IR & IS).
  unfold Int.lt. destruct zlt. intuition. destruct zlt; intuition.
Qed.

Lemma ssi_add_sound (x y: strided_interval) :
  lift_binop Int.add (γ x) (γ y) ⊆ γ (si_add Int.min_signed Int.max_signed x y).
Proof.
  assert (Int.max_signed = 2147483647) by reflexivity.
  assert (Int.min_signed = -2147483648) by reflexivity.
  assert (Int.modulus = 4294967296) by reflexivity.
  unfold γ, ssi_gamma.
  intros k (i&j&I&J&->).
  unfold si_gamma, si_add in *.
  rewrite Int.add_signed.
  repeat destruct Z_le_dec; simpl.
  2: split;[apply Int.signed_range|auto with congr].
  3: split;[apply Int.signed_range|auto with congr].
  rewrite Int.signed_repr; intuition.
  rewrite Ngcd_is_Zgcd.
  apply congr_plus_compat. eapply congr_divide. eauto. apply Zgcd_divides_l.
  eapply congr_divide. eauto. apply Zgcd_divides_r.
  rewrite (Int.eqm_samerepr _ (Int.signed i + Int.signed j - Int.modulus)).
  rewrite Int.signed_repr. intuition.
  rewrite Ngcd_is_Zgcd.
  apply congr_plus_compat. apply congr_plus_compat.
  eapply congr_divide. eauto. apply Zgcd_divides_l.
  eapply congr_divide. eauto. apply Zgcd_divides_r.
  auto with congr.
  pose proof (Int.signed_range i).
  pose proof (Int.signed_range j).
  Psatz.lia.
  exists 1. auto with zarith.
  rewrite (Int.eqm_samerepr _ (Int.signed i + Int.signed j + Int.modulus)).
  rewrite Int.signed_repr. intuition.
  rewrite Ngcd_is_Zgcd.
  apply congr_plus_compat. apply congr_plus_compat.
  eapply congr_divide. eauto. apply Zgcd_divides_l.
  eapply congr_divide. eauto. apply Zgcd_divides_r.
  auto with congr.
  pose proof (Int.signed_range i).
  pose proof (Int.signed_range j).
  Psatz.lia.
  exists (-1). auto with zarith.
Qed.

Lemma ssi_not_sound x : lift_unop Int.not (si_gamma Int.signed x) ⊆ (si_gamma Int.signed (ssi_not x)).
Proof.
  intros ? (i & I & ->).
  apply ssi_add_sound. rewrite Int.not_neg.
  exists (Int.neg i). exists (Int.mone).
  intuition. apply ssi_neg_sound. eexists. simpl. intuition eauto.
  simpl. apply si_const_sound.
Qed.

Lemma ssi_sub_sound x y : lift_binop Int.sub (γ x) (γ y) ⊆ γ (ssi_sub x y).
Proof.
  intros ? (i & j & I & J & ->).
  rewrite Int.sub_add_opp.
  apply ssi_add_sound. exists i. exists (Int.neg j). intuition.
  apply ssi_neg_sound. exists j. intuition.
Qed.

Definition Zsize i :=
  match i with Zpos p => Zpos (Pos.size p) | _ => 0 end.

Definition size i := Zsize (Int.unsigned i).

Lemma Zsize_pos i : 0 <= Zsize i.
Proof. unfold Zsize; destruct i; Psatz.lia. Qed.

Lemma Zsize_unsigned i: Zsize (Int.unsigned i) = Int.size i.
Proof. reflexivity. Qed.

Lemma two_p_pos p : 0 <= p → 0 < two_p p.
Proof.
  intros H. destruct p. reflexivity. simpl. unfold two_power_pos. Psatz.lia.
  Psatz.lia.
Qed.

Lemma and_interval a b : Int.unsigned (Int.and a b) < two_p (size b).
Proof.
generalize (Int.and_interval a b); intros [_?].
assert (size b = Int.size b).
 unfold size, Int.size; auto.
rewrite H0.
assert (two_p (Z.min (Int.size a) (Int.size b)) <= two_p (size b)).
 apply two_p_monotone.
 generalize (Int.size_range a) (Int.size_range b); intros [??] [??].
 Psatz.lia.
eapply Z.lt_le_trans; eauto.
Qed.

Lemma ssi_and_sound x y : lift_binop Int.and (γ x) (γ y) ⊆ γ (ssi_and x y).
Proof.
  unfold ssi_and.
  intros ? (i & j & I & J & ->).
  destruct y as [[|ys] yl yu].
  2: simpl; rewrite print_id; apply si_gamma_top, Int.signed_range.
  destruct J as [J J']. simpl in J'. rewrite (congr_0_eq _ _ J') in *; clear J' yl.
  simpl in J.
  destruct x as [[|xs] xl xu].
  destruct I as [I I']. simpl in I'. rewrite (congr_0_eq _ _ I') in *; clear I' xl.
  simpl in I. simpl. repeat rewrite Int.repr_signed. apply si_const_sound.
  unfold si_stride, si_low_bound.
  generalize (Int.repr_signed j).
  case_eq (Int.signed j).
  intros ? <-. rewrite Int.and_zero. split; intuition.
  2: intros ? ? _; apply si_gamma_top, Int.signed_range.
  intros p H H0.
  assert (Int.signed j >= 0) as GE by Psatz.lia.
  split. 2: auto with congr.
  pose proof (Int.and_positive i j GE) as K.
  split. simpl. intuition.
  assert (Int.unsigned j = Int.signed j) as JJ.
  unfold Int.signed in *. destruct zlt. easy. exfalso. generalize (Int.unsigned_range j); intuition.
  unfold Int.signed in K |- * at 1. red. destruct zlt.
  2: exfalso; pose proof (Int.unsigned_range (Int.and i j)); intuition.
  cut (Int.unsigned (Int.and i j) < Z.pos (shift_pos (Pos.size p) 1)).
  unfold si_up_bound.
  unfold two_power_pos.
  fold (Zle (Int.unsigned (Int.and i j)) (Z.pos (shift_pos (Pos.size p) 1) - 1)). intuition.
  eapply Zlt_le_trans. apply (and_interval i j).
  fold (two_power_pos (Pos.size p)).
  fold (two_p (Z.pos (Pos.size p))).
  apply two_p_monotone.
  rewrite H in JJ.
  unfold size. rewrite JJ.
  simpl. Psatz.lia.
Qed.

Lemma add_sub: forall i1 i2:int,
    (Int.sub (Int.add i1 i2) i2) = i1.
Proof.
  intros.
  rewrite Int.add_commut.
  rewrite Int.sub_add_l.
  rewrite Int.sub_idem.
  rewrite Int.add_zero_l; auto.
Qed.

Lemma ssi_backward_add_sound :
  ∀ x y z i j,
    γ x i →
    γ y j →
    γ z (Int.add i j) →
    (i, j) ∈ γ (ssi_backward_add x y z).
Proof.
  unfold ssi_backward_add. simpl.
  intros x y z i j H H0 H1.
  apply red2_elim; apply (si_meet_sound); auto using signed_inj; split; auto;
  apply ssi_sub_sound;
  exists (Int.add i j);
  [exists j|exists i].
  auto using add_sub.
  intuition. rewrite Int.add_commut.
  auto using add_sub.
Qed.

(*
Lemma backward_boolval_sound :
  @backward_unop_correct _ as_wl _ backward_boolval
     (λ i : int, Interval.of_bool (negb (Int.eq i Int.zero))).
Proof.
  intros x y i Hi [Hyr Hym]. simpl.
  unfold ssi_backward_boolval.
  destruct (si_stride y) eqn: Hsy; auto.
  apply congr_0_eq in Hym.
  destruct (Z_zerop _) as [ Z | NZ ].
  hnf. simpl. cut (Int.signed i = 0). intros ->. split. split; easy. auto with congr.
  revert Hym. rewrite Z. apply Util.int_eq_elim. now intros ->.
  discriminate.
  generalize (gamma_monotone ssi_adom). intros X.
  specialize (X x ssi_booleans).
  destruct (_ ⊑ _); auto. specialize (X eq_refl i Hi).
  cut (i = Int.one). intros ->. split; simpl; auto with congr. Psatz.lia.
  rewrite Hym in NZ. revert NZ.
  apply Util.int_eq_elim. intros _ K; elim (K eq_refl).
  destruct X as [X _]. simpl in X.
  intros NZ _. apply signed_inj in NZ.
  assert (Int.signed i = 0 ∨ Int.signed i = 1) as D by Psatz.lia.
  destruct D as [ D | D ]. elim (NZ D).
  generalize (Int.repr_signed i). rewrite D. auto.
Qed.

Lemma backward_notbool_sound :
   @backward_unop_correct _ as_wl _ backward_notbool
     (λ i : int, Interval.of_bool (Int.eq i Int.zero)).
Proof.
  intros x y i Hi [Hyr Hym]. simpl.
  unfold ssi_backward_notbool.
  destruct (si_stride y) eqn: Hsy; auto.
  apply congr_0_eq in Hym.
  destruct (Z.eq_dec _ _) as [ Z | NZ ]; auto.
  hnf. simpl. cut (Int.signed i = 0). intros ->. split. split; easy. auto with congr.
  revert Hym. rewrite Z. apply Util.int_eq_elim. now intros ->.
  discriminate.
Qed.
*)

(*
Instance ssi_num_dom_correct : num_dom_correct ssi_dom.
Proof.
  split; try (now intros; simpl; apply si_gamma_top, Int.signed_range);
  try now repeat intro; simpl; try rewrite print_id; auto.
 intros x y a [X Y]. destruct y as [ | y ]. exact Y.
  generalize (si_meet_sound _ signed_inj x y a (conj X Y)).
  simpl. destruct (si_meet _ _); exact id.
  simpl. apply si_const_sound.
  simpl. split. split; discriminate. intuition.
  simpl. split. split; discriminate. intuition.
  intros x i [H H']. split. auto. apply Interval.ugamma_top.
  apply ssi_neg_sound.
  apply ssi_not_sound.
  simpl. intros x i H. destruct (Int.eq _ _); simpl; split. split; discriminate. intuition. split; discriminate. intuition.
  simpl. intros x i H. destruct (Int.eq _ _); simpl; split. split; discriminate. intuition. split; discriminate. intuition.
  simpl. apply ssi_add_sound.
  simpl. apply ssi_sub_sound.
  apply ssi_mul_sound.
  apply ssi_divs_sound.
  apply ssi_shl_sound.
  intros x y ? (i & j & Hi & Hj & ->). now apply ssi_shru_sound.
  apply ssi_and_sound.
  simpl. apply ssi_is_in_itv_sound.
  apply backward_boolval_sound.
  apply backward_notbool_sound.
  exact ssi_backward_add_sound.
  now repeat intro; simpl; rewrite print_id; split.
  (* cmp *)
  exact ssi_backward_cmp_sound.
  exact ssi_backward_cmpu_sound.
  now repeat intro; simpl; rewrite print_id; eexists; (split; [ left; eauto | ]; split).
  now repeat intro; simpl; rewrite print_id; eexists; (split; [ left; eauto | ]; split).
Qed.
*)

(*
(** Product of strided signed intervals and unsigned (non-strided) intervals. *)
Section SSIU.

  Require Import Intervals.
  Import DLib Interval.
  Definition reduc2unsigned (i: strided_interval) : itv :=
    let m := i.(si_low_bound) in
    let M := i.(si_up_bound) in
    if zle 0 m
    then ITV m M
    else if zlt M 0
         then ITV (m + Int.modulus) (M + Int.modulus)
         else utop.

  Definition reduc2signed (i: itv) : strided_interval :=
    match reduc2signed i with
    | ITV m M => {| si_stride := 1%N; si_low_bound := m; si_up_bound := M |}
    end.

  Lemma reduc2unsigned_correct: forall i v,
    si_gamma Int.signed i v ->
    ugamma (reduc2unsigned i) v.
  Proof.
    intros [s m M] v (A & B). simpl in *.
    pose proof (Int.signed_range v).
    pose proof (Int.unsigned_range v).
    unfold ugamma, Int.signed in *.
    unfold reduc2unsigned, utop. simpl.
    destruct zlt; destruct zle; simpl; try Psatz.lia;
    destruct zlt; simpl; try Psatz.lia;
    unfold Int.max_unsigned; Psatz.lia.
  Qed.

  Lemma reduc2signed_correct: forall i v,
    ugamma i v ->
    si_gamma Int.signed (reduc2signed i) v.
  Proof.
    unfold reduc2signed.
    intros i v H. pose proof (reduc2signed_correct i v H).
    destruct (Interval.reduc2signed).
    split; auto with congr.
  Qed.

  Instance ssiu_red : reduction strided_interval itv :=
  {| ρ := botbind2 (fun s u =>
       let s' := reduc2signed u in
       let u' := reduc2unsigned s in
       match si_meet s s', u ⊓ NotBot u' with
         | Bot, _ | _, Bot => Bot
         | NotBot a, NotBot b => NotBot (a,b)
       end)
  |}.

  Lemma ssiu_red_correct : reduction_correct ssi_gamma ugamma.
  Proof.
    Hint Resolve reduc2unsigned_correct reduc2signed_correct.
    intros [|a] [|b]; try now simpl.
    intros i (A & B).
    unfold ρ, itv_red, botbind2, botbind.
    pose proof (si_meet_sound Int.signed DLib.signed_inj a (reduc2signed b)) as X.
    pose proof (@meet_correctu b (NotBot (reduc2unsigned a))) as Y.
    simpl. destruct (si_meet a _). eapply X; eauto.
    destruct (b ⊓ NotBot (reduc2unsigned a)).
    eapply Y. simpl. split. 2: apply reduc2unsigned_correct; eauto. exact B.
    split;[apply X|apply Y]; simpl; auto.
    split; auto. now apply reduc2unsigned_correct.
  Qed.

  Instance ssiu_dom : num_dom _ :=
    @reduced_product_num_dom _ _ ssi_dom UInterval.itvu_num ssiu_red.
  Instance ssiu_dom_correct : num_dom_correct ssiu_dom :=
    reduced_product_num_dom_correct _ _ ssi_num_dom_correct UInterval.itvu_num_correct _ ssiu_red_correct.

End SSIU.
*)
