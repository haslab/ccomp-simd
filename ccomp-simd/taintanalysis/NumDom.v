Require TypeDomain.
Import Utf8.
Import Coqlib.
Import Integers.
Import AdomLib.
Import TypeDomain.

Unset Elimination Schemes.

Section NEXPR.

Context (var: Type).

Definition nexpr : Type := pexpr var.

Context (τ: var → type +⊤).

Definition ne_true : nexpr := (Op.Ointconst Int.one, nil).
Definition ne_false : nexpr := (Op.Ointconst Int.zero, nil).
Definition any_bool : list nexpr := ne_true :: ne_false :: nil.

Definition ne_of_pe (pe: pexpr var) : list nexpr :=
  let '(op, args) := pe in
  match op with
  | Op.Oindirectsymbol _ => (Op.Ointconst Int.zero, args) :: nil
  | Op.Olea addr =>
    match addr with
    | Op.Ainstack ofs
    | Op.Aglobal _ ofs => (Op.Ointconst ofs, args) :: nil
    | Op.Abased _ ofs => (Op.Olea (Op.Aindexed ofs), args) :: nil
    | Op.Abasedscaled sc _ ofs => (Op.Olea (Op.Ascaled sc ofs), args) :: nil
    | Op.Aindexed _ | Op.Aindexed2 _
    | Op.Ascaled _ _ | Op.Aindexed2scaled _ _
      => pe :: nil
    end
  | Op.Ocmp cmp =>
    match cmp with
    | Op.Ccomp _ | Op.Ccompimm _ _
    | Op.Ccompf _ | Op.Cnotcompf _
    | Op.Cmaskzero _ | Op.Cmasknotzero _
      => pe :: nil
    | Op.Ccompu c =>
      match args with
      | x :: y :: nil =>
        match τ x, τ y with
        | All, _ | _, All => any_bool
        | Just tx, Just ty =>
        match tx, ty with
        | TyInt, TyInt => pe :: nil
        | TyInt, TyZero => (Op.Ocmp (Op.Ccompuimm c Int.zero), x :: nil) :: nil
        | TyZero, TyInt => (Op.Ocmp (Op.Ccompuimm (swap_comparison c) Int.zero), y :: nil) :: nil
        | TyZero, TyZero => match c with Ceq | Cle | Cge => ne_true | _ => ne_false end :: nil
        | (TyZero | TyInt), TyPtr _
        | TyPtr _, (TyZero | TyInt)
          => match c with Ceq => ne_false :: nil | Cne => ne_true :: nil | _ => nil end
        | (TyZero | TyInt | TyIntPtr), (TyZPtr _ | TyIntPtr)
        | (TyZPtr _ | TyIntPtr), (TyZero | TyInt)
          => any_bool
        | TyPtr _, TyPtr _ =>
          match c with
          | Ceq | Cne => any_bool (* could be more precise *)
          | Cle | Cge | Cgt | Clt => pe :: nil end
        | (TyPtr _ | TyZPtr _), (TyZPtr _ | TyIntPtr)
        | (TyZPtr _ | TyIntPtr), TyPtr _
          => any_bool
        | TyFloat, _ | _, TyFloat
        | TySingle, _ | _, TySingle
        | TyL64, _ | _, TyL64
        | TyL128, _ | _, TyL128
          => nil
        end end
      | _ => pe :: nil
      end
    | Op.Ccompuimm c n =>
      match args with
      | x :: nil =>
        match τ x with
        | All => pe :: nil
        | Just tx =>
        match tx with
        | TyZero
        | TyInt
          => pe :: nil
        | TyPtr _ =>
          match c with Ceq => ne_false :: nil | Cne => ne_true :: nil | _ => nil end
        | TyZPtr _
        | TyIntPtr
          => any_bool
        | TyFloat | TySingle | TyL64 | TyL128 => nil
        end end
      | _ => pe :: nil
      end
    end
  | _ => pe :: nil
  end.

End NEXPR.

Arguments ne_of_pe {var} _ _.

Record num_dom (num: Type) (cell: Type) : Type :=
  ND {
      nd_wlat:> wlat num
      ;
      nd_concretize: nexpr cell → num → SetInterface.set Z +⊤
      ;
      nd_forget: cell → num → num+⊥
      ;
      nd_assign: cell → nexpr cell → num → num+⊥
      ;
      nd_assume: nexpr cell → int → num → num+⊥
    }.

Arguments nd_concretize {num cell} _ _ _.
Arguments nd_forget {num cell} _ _ _.
Arguments nd_assign {num cell} _ _ _ _.
Arguments nd_assume {num cell} _ _ _ _.
