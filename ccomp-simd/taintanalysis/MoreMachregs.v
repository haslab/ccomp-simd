Require Generate.
Require Import OrderedTypeEx.

Require Export Machregs.
Require Import ToString.
Import Utf8.

Instance string_of_mreg : ToString mreg :=
  λ r,
  match r with
  | AX => "AX"
  | BX => "BX"
  | CX => "CX"
  | DX => "DX"
  | SI => "SI"
  | DI => "DI"
  | BP => "BP"
  | X0 => "X0"
  | X1 => "X1"
  | X2 => "X2"
  | X3 => "X3"
  | X4 => "X4"
  | X5 => "X5"
  | X6 => "X6"
  | X7 => "X7"
  | Y0 => "Y0"
  | Y1 => "Y1"
  | Y2 => "Y2"
  | Y3 => "Y3"
  | Y4 => "Y4"
  | Y5 => "Y5"
  | Y6 => "Y6"
  | Y7 => "Y7"
  | FP0 => "FP0"
  end.

Generate OrderedType mreg.
