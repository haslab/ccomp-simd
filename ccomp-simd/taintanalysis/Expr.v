Require Import Machregs.
Import AST.
Import Integers.

Unset Elimination Schemes.

Inductive expr : Type :=
| EGetParam `(int) `(typ)
| ELoad `(memory_chunk) `(Op.addressing) `(list mreg)
| EOp `(Op.operation) `(list mreg)
.

Inductive assertion : Type :=
| AssertBool `(Op.condition) `(list mreg) `(bool)
| AssertNat `(mreg) `(int)
.
