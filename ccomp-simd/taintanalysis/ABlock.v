Require Import MoreMachregs.
Require Import Util.
Import Utf8.
Import OrderedTypeEx.
Import Coqlib.
Import AST.
Import ToString.

Unset Elimination Schemes.

Local Open Scope string_scope.

Inductive ablock : Type :=
| ABGlobal `(ident)
| ABStack `(positive).

Parameter string_of_ident : ident → string.

Instance string_of_ablock : ToString ablock :=
  λ a,
  match a with
  | ABGlobal g => string_of_ident g
  | ABStack n => "Stack(" ++ to_string n ++ ")"
  end.

Generate OrderedType ablock.

Inductive cell_size : Type :=
| CZ1 | CZ2 | CZ4 | CZ8 | CZ16.

Instance cell_size_dec : EqDec cell_size.
Proof.
  intros x y.
  refine match x, y with
         | CZ1, CZ1
         | CZ2, CZ2
         | CZ4, CZ4
         | CZ8, CZ8
         | CZ16, CZ16
           => left eq_refl
         | _, _ => right _
         end;
    abstract (refine (λ H, let 'eq_refl := H in I)).
Defined.

Definition fold_cell_size {A} (f: cell_size → A → A) (a: A) : A :=
  f CZ16 (f CZ8 (f CZ4 (f CZ2 (f CZ1 a)))).

Definition cell_size_of_chunk (κ: memory_chunk) :=
  match κ with
  | Mint8signed | Mint8unsigned => CZ1
  | Mint16signed | Mint16unsigned => CZ2
  | Mint32 | Mfloat32 => CZ4
  | Mint64 | Mfloat64 => CZ8
  | Mint128 => CZ16
  end.

Definition cell_size_of_typ (ty: typ) : cell_size :=
  match ty with
  | Tint | Tsingle => CZ4
  | Tlong | Tfloat => CZ8
  | T128 => CZ16
  end.

Definition N_of_cell_size (s: cell_size) : N :=
  match s with
  | CZ1 => 1
  | CZ2 => 2
  | CZ4 => 4
  | CZ8 => 8
  | CZ16 => 16
  end%N.

Instance string_of_cell_size : ToString cell_size :=
  to_string ∘ N_of_cell_size.

Generate OrderedType cell_size.

Require Sets.

Instance string_of_set {A: Type} `{OrderedType A} `{ToString A} : ToString (SetInterface.set A) :=
  λ s,
  "{" ++ SetInterface.fold (λ a r, to_string a ++ "; " ++ r) s "}".
