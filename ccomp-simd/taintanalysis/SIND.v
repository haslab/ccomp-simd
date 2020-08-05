Require Import StridedIntervals.
Require Import Box.
Import Coqlib.
Import Integers.
Import AdomLib.

Definition widen_as_join xL xU yL yU :=
  (Z.min xL yL, Z.max xU yU).

Fixpoint next_pow2_pos (p:positive) :=
  match p with
  | xH => xH
  | xI p
  | xO p => xI (next_pow2_pos p)
  end.

Definition previous_pow2_pos p :=
  let p' := next_pow2_pos p in
  match p' with
  | xI p => p
  |  _ => p' (* assert false *)
  end.

Definition next_threshold (z:Z) :=
  match z with
  | Z0 => Z0
  | Zpos xH => Zpos xH
  | Zneg xH => Zneg xH
  | Zpos p => Zpos (next_pow2_pos p)
  | Zneg p => Zneg (previous_pow2_pos p)
  end.

  Definition previous_threshold (z:Z) :=
    match z with
    | Z0 => Z0
    | Zpos xH => Zpos xH
    | Zneg xH => Zneg xH
    | Zpos p => Zpos (previous_pow2_pos p)
    | Zneg p => Zneg (next_pow2_pos p)
    end.

  Definition widen_with_threshlolds xL xU yL yU :=
    (if xL <=? yL then xL else previous_threshold yL,
     if xU <? yU then next_threshold yU else xU).

Definition widen_heuristic xL xU yL yU :=
  (if xL <=? yL then xL else Int.min_signed,
   if xU <=? yU then Int.max_signed else xU).

Definition reduce_top (x: strided_interval) : strided_interval +⊤ :=
  if si_LE_dec ssi_top x then All else Just x.

Definition si_cast (lo hi: Z) (x: strided_interval) : strided_interval +⊤ :=
    if si_LE_dec x {| si_stride := 1; si_low_bound := lo; si_up_bound := hi |}
    then Just x
    else All.

Definition p_128 : positive := 128%positive.
Definition p_127 : positive := 127%positive.
Definition p_255 : positive := (p_127~1)%positive.
Definition p_2047 : positive := (p_255~1~1~1)%positive.
Definition p_32767 : positive := (p_2047~1~1~1~1)%positive.
Definition p_65535 : positive := (p_32767~1)%positive.

Definition ssi_unop (op: iunop) (x: strided_interval) : strided_interval +⊤ :=
  match op with
  | Ishrx n =>
    reduce_top (ssi_divs x (si_const Int.signed (Int.shl Int.one n)))
  | Icast8u => si_cast 0 (Zpos p_255) x
  | Icast8s => si_cast (Zneg p_128) (Zpos p_127) x
  | Icast16u => si_cast 0 (Zpos p_65535) x
  | Icast16s => si_cast (-32768) (Zpos p_32767) x
  | _ => All
  end.

Definition ssi_binop (op: ibinop) (x y: strided_interval) : strided_interval +⊤ :=
  match op with
  | Iadd ofs =>
    Just (
        let r := si_add Int.min_signed Int.max_signed x y in
        if Int.eq ofs Int.zero then r else
          si_add Int.min_signed Int.min_signed r (si_const Int.signed ofs))
  | Iaddscaled sc ofs => (* x + y × sc + ofs *)
    Just (
        let y' := ssi_mul y (si_const Int.signed sc) in
        let r := si_add Int.min_signed Int.max_signed x y' in
        if Int.eq ofs Int.zero then r else
          si_add Int.min_signed Int.min_signed r (si_const Int.signed ofs))
  | Isub => Just (ssi_sub x y)
  | Imul => Just (ssi_mul x y)
  | Idiv s => if s then Just (ssi_divs x y) else All
  | Imod _ => All
  | Iand => Just (ssi_and x y)
  | Ixor => reduce_top (ssi_xor_w x y)
  | Ior => All
  | Ishl => Just (ssi_shl x y)
  | Ishr s => Just ((if s then ssi_shr else ssi_shru) x y)
  | Icomp _ _ => Just (ssi_booleans)
  end.

Definition of_ssi_top (x: strided_interval+⊤) : strided_interval :=
  match x with
  | All => ssi_top
  | Just s => s
  end.

Definition ssi_backward_cmp' (b: bool) (c: comparison)
           (x y: strided_interval+⊤) (z: strided_interval)
  : (strided_interval+⊤ * strided_interval+⊤)+⊥ :=
  botlift_fun1
    (λ r, let '(x', y') := r in (reduce_top x', reduce_top y'))
    ((if b then ssi_backward_cmp c else ssi_backward_cmpu c) (of_ssi_top x) (of_ssi_top y) z).

Definition set_of_list (m: list Z) : SetInterface.set Z :=
  list_fold_left SetInterface.add SetInterface.empty m.

Definition sind : int_dom strided_interval :=
  {|
    id_leb x y := if si_LE_dec x y then true else false;
    id_join x y := reduce_top (si_join x y);
    id_widen x y := reduce_top (si_widen widen_with_threshlolds x y);

    id_const := si_const Int.signed;
    id_unop := ssi_unop;
    id_binop := ssi_binop;

    id_backward_cmp := ssi_backward_cmp';

    id_concretize x :=
      (if si_size x <=? Npos p_2047
       then Just (set_of_list (si_concretize x))
       else All)%N
  |}.
