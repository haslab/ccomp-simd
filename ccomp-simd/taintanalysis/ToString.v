(* *********************************************************************)
(*                                                                     *)
(*              The Verasco static analyzer                            *)
(*                                                                     *)
(*          Vincent Laporte, Université de Rennes 1                    *)
(*          Jacques-Henri Jourdan, INRIA Paris-Rocquencourt            *)
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

Require Import Utf8.
Require Import Coqlib Integers.
Require Import PrintPos.
Require Export String.

Infix "∘" := (λ g f x, g (f (x))) (left associativity, at level 40).

Open Scope string_scope.

Fixpoint string_rev_append (s₁ s₂: string)  {struct s₁} : string :=
  match s₁ with "" => s₂ | String c s' => string_rev_append s' (String c s₂) end.

Definition string_append (s₁ s₂: string) : string :=
  string_rev_append (string_rev_append s₁ "") s₂.

Notation "s₁ ++ s₂" := (string_append s₁ s₂) : string_scope.

Class ToString A := to_string : A → string.
Instance UnitToString : ToString unit := λ _, "()".
Instance BoolToString : ToString bool := (λ b, if b then "true" else "false").
Instance PosToString : ToString positive := print_pos.
Instance SIntToString : ToString int := string_of_z ∘ Int.signed.
Instance SInt64ToString : ToString int64 := string_of_z ∘ Int64.signed.
Instance ZToString : ToString Z := string_of_z.
Instance NToString : ToString N := string_of_z ∘ Z.of_N.
Instance NatToString : ToString nat := string_of_z ∘ Z.of_nat.
Instance ListToString {A} `{ToString A} : ToString (list A) :=
  (λ l, List.fold_left (λ s a, s ++ to_string a ++ "; ") l "[" ++ "]").

Instance PairToString A B `{ToString A} `{ToString B} : ToString (A * B) := λ ab, let '(a, b) := ab in "(" ++ to_string a ++ ", " ++ to_string b ++ ")".

Instance SumToString A B `{ToString A} `{ToString B} : ToString (A + B) :=
  λ x,
  match x with
  | inl a => to_string a
  | inr b => to_string b
  end.

Instance OptionToString {A} `{ToString A} : ToString (option A) :=
  λ o, match o with Some a => "Some(" ++ to_string a ++ ")" | None => "None" end.

Definition new_line : string := "
".

Global Opaque String.append.
