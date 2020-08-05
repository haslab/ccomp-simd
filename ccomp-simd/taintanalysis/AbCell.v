Require Import Util.
Import Coqlib.
Import AST.

Unset Elimination Schemes.

Inductive ab_cell : Type :=
| Global `(ident) `(Z)
| Stack `(nat) `(Z)
.

Instance ab_cell_dec : EqDec ab_cell.
Proof.
  intros (); [ intros g o | intros d o ];
  (intros (); [ intros g' o' | intros d' o' ]).
  case (eq_dec g g'); intros Hg.
  case (eq_dec o o'); intros Ho.
  left; apply f_equal2; assumption.
  right; clear -Ho; abstract congruence.
  right; abstract congruence.
  right; abstract congruence.
  right; abstract congruence.
  case (eq_nat_dec d d'); intros Hd.
  case (eq_dec o o'); intros Ho.
  left; apply f_equal2; assumption.
  right; clear -Ho; abstract congruence.
  right; abstract congruence.
Defined.

Definition points_to_hint : Type :=
  (ab_cell * Z)%type. (* base and size *)
