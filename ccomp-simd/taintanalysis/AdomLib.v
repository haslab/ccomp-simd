Require Export Util.
Require Import ToString.
Export Utf8.

Unset Elimination Schemes.

(** * Adding a top element to an abstract domain **)
Inductive toplift (A: Type) : Type := All | Just `(A).
Arguments Just {A} _.
Arguments All {A}.
Notation "t +⊤" := (toplift t) (at level 39).

Instance string_of_toplift {A} `{ToString A} : ToString (A +⊤) :=
  λ x,
  match x with
  | All => "⊤"
  | Just a => to_string a
  end.

Definition Just_inj {A} {x y: A} (E: Just x = Just y) : x = y :=
  let 'eq_refl := E in eq_refl.

Definition All_not_Just {A} {x: A}  (P: Prop)(E: All = Just x) : P :=
  let 'eq_refl := E in I.

Instance toplift_eq_dec {A} `{EqDec A} : EqDec (A+⊤) :=
  λ x y,
  match x with
  | All => match y with All => left eq_refl | Just y' => right (All_not_Just False) end
  | Just x' =>
    match y with
    | All => right (λ K, All_not_Just _ (eq_sym K))
    | Just y' =>
      match eq_dec x' y' with
      | left E => left (f_equal Just E)
      | right NE => right (λ K, NE (Just_inj K))
      end
    end
  end.

Definition topbind {A B} (f: A → B+⊤) (m: A+⊤) : B+⊤ :=
  match m with
  | All => All
  | Just a => f a
  end.

Definition topbind2 {A B C} (f: A → B → C +⊤) (a: A+⊤) (b: B+⊤) : C+⊤ :=
  topbind (λ a, topbind (f a) b) a.

Definition toplift_fun1 {A B} (f: A → B) (m: A+⊤) : B+⊤ :=
  topbind (Just ∘ f) m.

(** * Adding a bottom element to an abstract domain **)
Inductive botlift (A:Type) : Type := Bot | NotBot (x:A).
Arguments NotBot {A} _.
Arguments Bot {A}.
Notation "t +⊥" := (botlift t) (at level 39).

Instance string_of_botlift {A} `{ToString A} : ToString (A +⊥) :=
  λ x,
  match x with
  | Bot => "⊥"
  | NotBot a => to_string a
  end.

Definition botbind {A B} (f: A → B+⊥) (a: A+⊥) : B+⊥ :=
  match a with
  | Bot => Bot
  | NotBot x => f x
  end.

Class gamma_op (A B: Type) : Type := γ : A → 𝒫 B.

Instance lift_gamma (A B: Type) `(gamma_op A B) : gamma_op (A+⊥) B :=
  λ x, match x with | Bot => ∅ | NotBot x => γ x end.

Instance pair_gamma {A B Ca Cb} (GA: gamma_op A Ca) (GB: gamma_op B Cb) : gamma_op (A * B) (Ca * Cb) :=
  λ x x', let '(a, b) := x in let '(a', b') := x' in a' ∈ γ(a) ∧ b' ∈ γ(b).

Definition botbind_spec {A A' B B':Type} {GA: gamma_op A A'} {GB: gamma_op B B'} :
  ∀ f:A→B+⊥, ∀ x y, (∀ a, x ∈ γ a -> y ∈ γ (f a)) →
                    (∀ a, x ∈ γ a -> y ∈ γ (botbind f a))
      :=
        λ f x y H a,
    match a with
    | Bot => λ K, K
    | NotBot a' => λ K, H _ K
    end.

Definition botlift_fun1 {A B:Type} (f:A->B) (x:A+⊥) : B+⊥ :=
  botbind (NotBot ∘ f) x.

Lemma botlift_fun1_spec {A A' B B':Type} {AD:gamma_op A A'} {BD: gamma_op B B'}:
  ∀ f:A→B, ∀ x y, (∀ x_ab, x ∈ γ x_ab -> y ∈ γ (f x_ab)) ->
                  (∀ x_ab, x ∈ γ x_ab -> y ∈ γ (botlift_fun1 f x_ab))    .
Proof.
  unfold botlift_fun1. intros. eapply botbind_spec, H0. apply H.
Qed.

Record wlat A : Type :=
  WL {
      wl_top: A
      ;
      wl_order: A → A → bool
      ;
      wl_join : A → A → A
      ;
      wl_widen : A → A → A
      ;
      wl_to_string:> ToString A
    }.

Arguments WL {A} _ _ _ _ _.
Arguments wl_top {A} _.
Arguments wl_order {A} _ _ _.
Arguments wl_join {A} _ _ _.
Arguments wl_widen {A} _ _ _.
Arguments wl_to_string {A} _ _.

Definition unit_wlat : wlat unit :=
  {| wl_top := tt; wl_order := λ _ _, true; wl_join := λ _, id; wl_widen := λ _, id |}.

Definition botlift_leb {A} (leb: A → A → bool) (x y: A+⊥) : bool :=
  match x with
  | Bot => true
  | NotBot x' => match y with Bot => false | NotBot y' => leb x' y' end
  end.

Definition botlift_combine {A} (j: A → A → A) (x y: A+⊥) : A+⊥ :=
  match x with
  | Bot => y
  | NotBot x' => match y with Bot => x | NotBot y' => NotBot (j x' y') end
  end.

Definition toplift_leb {A} (leb: A → A → bool) (x y: A+⊤) : bool :=
  match y with
  | All => true
  | Just y' => match x with All => false | Just x' => leb x' y' end
  end.

Definition toplift_combine {A} (j: A → A → A) (x y: A+⊤) : A+⊤ :=
  match x with
  | All => x
  | Just x' => match y with All => y | Just y' => Just (j x' y') end
  end.
