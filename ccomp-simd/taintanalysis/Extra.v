Require Export Utf8.
Require Import Coqlib.

Definition pair_eq_inv {A B} { a a' : A } { b b' : B } (p: (a, b) = (a', b')) :
  a = a' ∧ b = b' :=
  let 'eq_refl := p in conj eq_refl eq_refl.

Definition None_eq_Some_inv {A} {a: A} (P: Prop) (K: None = Some a) : P :=
  let 'eq_refl := K in I.

Definition some_eq_inv {A} {a a': A} (H: Some a = Some a') : a = a' :=
  let 'eq_refl := H in eq_refl.

Definition snd_eq_ex {A B} {p: A * B} : ∀ (b: B) (H : snd p = b), ∃ a : A, p = (a, b) :=
  let '(a, b) := p in λ b' H, ex_intro _ a (f_equal _ H).

Ltac hsplit :=
  repeat match goal with
         | H : _ ∧ _ |- _ => let K := fresh H in destruct H as [H K]
         | H : ∃ a, _ |-  _ => let a := fresh a in destruct H as [a H]
         end.

(* Keeps only the n last elements of the list m *)
Definition nlast  {A} (n: nat) (m: list A) : nat * list A :=
  fold_right
    (λ a r,
     let '(n, m) := r in
     match n with
     | O => r
     | S n' => (n', a :: m)
     end
    )
    (n, nil)
    m.

Lemma nlast_all {A} (m: list A) n :
  length m ≤ n →
  nlast n m = (n - length m, m)%nat.
Proof.
  elim m; clear.
  intros _. simpl. f_equal. omega.
  intros a m IH L. simpl. rewrite IH.
  simpl in *. destruct (n - length m)%nat as [ | n' ] eqn: H.
  omega. f_equal. omega.
  simpl in L. omega.
Qed.

Lemma nlast_len {A} (m: list A) n :
  fst (nlast n m) = (n - length m)%nat ∧ length (snd (nlast n m)) = min n (length m).
Proof.
  elim m; clear. simpl.
  split. apply minus_n_O. symmetry. apply Min.min_r; omega.
  intros a m IH. simpl.
  destruct (nlast n m) as (n', m').
  simpl in IH; destruct IH as [ -> IH ].
  destruct (n - length m)%nat eqn: H; simpl.
  split. omega. rewrite IH.
  now repeat rewrite Min.min_l by omega.
  split. omega. rewrite IH.
  now repeat rewrite Min.min_r by omega.
Qed.

Lemma nlast_m1 {A} (m: list A) n :
  ∀ a m', nlast n m = (0%nat, a :: m') → nlast (n - 1) m = (0%nat, m').
Proof.
  elim m; clear.
  discriminate.
  intros a m IH a' m'. simpl.
  generalize (nlast_len m n).
  destruct (nlast n m) as ([| n'], q) eqn: K; intros [X X'] H; apply pair_eq_inv in H;
    destruct H as [ H H' ]; subst.
  erewrite IH; reflexivity.
  inv H'. simpl in *.
  assert (n = S (length m)) by omega. clear X. subst n.
  simpl. rewrite <- minus_n_O.
  rewrite nlast_all. rewrite minus_diag.
  generalize (nlast_all m (S (length m)) (le_n_Sn _)). rewrite K.
  congruence. auto.
Qed.

Lemma nlast_incl {A} (m: list A) n :
  incl (snd (nlast n m)) m.
Proof.
  elim m; clear. intro; exact id.
  intros a m. simpl. case (nlast n m). simpl.
  intros n' m' IH. case n'.
  apply incl_tl, IH.
  simpl. intros _.
  apply incl_cons. left; reflexivity. apply incl_tl, IH.
Qed.
