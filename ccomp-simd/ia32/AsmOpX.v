Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.

Set Implicit Arguments.


(* SHALL WE NEED COMPARISONS??? *)

(*
for each operation, we need (only in non-certified side):
- name for parsing (obs: opXs só aparecem em Cminor --- no C (pelo menos para já, a associação de um tipo a T128 é feito por um pragma)
- moption_mask (positive) (* -m options restrictions ---  each op has a bit mask that is checked against the mask induced by the m-options being used
- number of immediate args (?or positions)
- print_string

for the certified side:
- assembly instruction


Translation of the arithmetic operation r <- op(args). The corresponding instructions are prepended to k.

Definition transl_op
             (op: operation) (args: list mreg) (res: mreg) (k: code) : Errors.res code :=
  | Omul, a1 :: a2 :: nil =>
      assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; OK (Pimul_rr r r2 :: k)

Lemma transl_op_correct:
  forall op args res k c (rs: regset) m v,
  transl_op op args res k = OK c ->
  eval_operation ge (rs#ESP) op (map rs (map preg_of args)) m = Some v ->
  exists rs',
     exec_straight ge fn c rs m k rs' m
  /\ Val.lessdef v rs'#(preg_of res)
  /\ forall r, data_preg r = true -> r <> preg_of res -> preg_notin r (destroyed_by_op op) -> rs' r = rs r.
*)