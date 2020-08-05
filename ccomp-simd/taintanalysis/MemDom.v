Require MachIR.
Require Import AdomLib.
Require Import Expr.
Require Import AbCell.
Import AST.
Import Machregs.
Import MachIR.

Unset Elimination Schemes.

Record memdom (A: Type) : Type :=
  MD {
      wl:> wlat A;
      init: list (ident * globdef fundef unit) → A+⊥;
      aassume: assertion → A → A+⊥;
      aassign: mreg → expr → A → A+⊥;
      astore: mreg → memory_chunk → Op.addressing → list mreg → A → A+⊥;
      abuiltin: list mreg → external_function → list mreg → A → A+⊥;
      asyscall: external_function → A → A+⊥;
      acall: A → A+⊥;
      areturn: A → A+⊥;

      aderef: A+⊥ → Op.addressing → list mreg → option (list points_to_hint)
    }.
