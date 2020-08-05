Require Import NumDom.
Require Import MapLattice.

Import Containers.Maps.
Import Coqlib.
Import Op.
Import Integers.
Import AdomLib.
Import ToString.

Unset Elimination Schemes.

Inductive iunop : Type :=
| Icast8s | Icast8u
| Icast16s | Icast16u
| Ineg
| Ishrx `(int) | Iror `(int) | Ishld `(int)
| Imaskzero `(bool) `(int)
.

Inductive ibinop : Type :=
| Iadd `(int) | Iaddscaled (_ _: int)
| Isub
| Imul | Idiv `(bool) | Imod `(bool)
| Iand | Ior | Ixor
| Ishl | Ishr `(bool)
| Icomp `(bool) `(comparison)
.

Record int_dom (ab_int: Type) : Type :=
  IntDom {
      id_leb: ab_int → ab_int → bool;
      id_join: ab_int → ab_int → ab_int +⊤;
      id_widen: ab_int → ab_int → ab_int +⊤;
      id_to_string:> ToString ab_int;

      id_const: int → ab_int;
      id_unop: iunop → ab_int → ab_int +⊤;
      id_binop: ibinop → ab_int → ab_int → ab_int +⊤;

      id_backward_cmp: bool → comparison → ab_int+⊤ → ab_int+⊤ → ab_int → (ab_int+⊤ * ab_int+⊤)+⊥;

      id_concretize: ab_int → SetInterface.set Z +⊤
    }.

Arguments id_leb {ab_int} _ _ _.
Arguments id_join {ab_int} _ _ _.
Arguments id_widen {ab_int} _ _ _.
Arguments id_const {ab_int} _ _.
Arguments id_unop {ab_int} _ _ _.
Arguments id_binop {ab_int} _ _ _ _.
Arguments id_backward_cmp {ab_int} _ _ _ _ _ _.
Arguments id_concretize {ab_int} _ _.

Section BOX.

Context (var: Type) (varOT: OrderedType var) (string_of_var: ToString var).
Context (ab_int: Type) (d: int_dom ab_int).

Local
Instance string_of_ab_int : ToString ab_int := d.

Definition box : Type := Map [ var, ab_int ].

Definition box_top : box := empty _.
Definition box_order : box → box → bool := map_leb (id_leb d).
Definition box_join : box → box → box := map_combine (id_join d).
Definition box_widen : box → box → box := map_combine (id_widen d).

Definition box_wlat : wlat box :=
  {|
    wl_top := box_top;
    wl_order := box_order;
    wl_join := box_join;
    wl_widen := box_widen
  |}.

Definition eval_nexpr (ne: nexpr var) (b: box) : ab_int +⊤ :=
  let '(op, args) := ne in
  let with_arg {X} (f: ab_int → X+⊤) :=
      match args with x :: nil => topbind f (map_get b x) | _ => All end in
  let with_args {X} (f: ab_int → ab_int → X+⊤) :=
      match args with x :: y :: nil => topbind2 f (map_get b x) (map_get b y) | _ => All end in
  match op with
  | Omove => with_arg Just
  | Ointconst i => Just (id_const d i)
  | Ocast8signed => with_arg (id_unop d Icast8s)
  | Ocast8unsigned => with_arg (id_unop d Icast8u)
  | Ocast16signed => with_arg (id_unop d Icast16s)
  | Ocast16unsigned => with_arg (id_unop d Icast16u)
  | Oneg => with_arg (id_unop d Ineg)
  | Osub => with_args (id_binop d Isub)
  | Omul =>  with_args (id_binop d Imul)
  | Omulimm i => with_arg (id_binop d Imul (id_const d i))
  | Odiv => with_args (id_binop d (Idiv true))
  | Odivu => with_args (id_binop d (Idiv false))
  | Omod => with_args (id_binop d (Imod true))
  | Omodu => with_args (id_binop d (Imod false))
  | Oand =>  with_args (id_binop d Iand)
  | Oandimm i => with_arg (id_binop d Iand (id_const d i))
  | Oor =>  with_args (id_binop d Ior)
  | Oorimm i => with_arg (id_binop d Ior (id_const d i))
  | Oxor =>  with_args (id_binop d Ixor)
  | Oxorimm i => with_arg (id_binop d Ixor (id_const d i))
  | Oshl =>  with_args (id_binop d Ishl)
  | Oshlimm i => with_arg (λ x, id_binop d Ishl x (id_const d i))
  | Oshr =>  with_args (id_binop d (Ishr true))
  | Oshrimm i => with_arg (λ x, id_binop d (Ishr true) x (id_const d i))
  | Oshrximm i => with_arg (id_unop d (Ishrx i))
  | Oshru =>  with_args (id_binop d (Ishr false))
  | Oshruimm i => with_arg (λ x, id_binop d (Ishr false) x (id_const d i))
  | Ororimm i => with_arg (id_unop d (Iror i))
  | Oshldimm i => with_arg (id_unop d (Ishld i))
  | Olea addr =>
    match addr with
    | Aindexed ofs => with_arg (id_binop d (Iadd Int.zero) (id_const d ofs))
    | Aindexed2 ofs => with_args (id_binop d (Iadd ofs))
    | Ascaled sc ofs => with_arg (id_binop d (Iaddscaled sc Int.zero) (id_const d ofs))
    | Aindexed2scaled sc ofs => with_args (id_binop d (Iaddscaled sc ofs))
    | Aglobal _ _ | Abased _ _ | Abasedscaled _ _ _
    | Ainstack _
      => All
    end
  | Ocmp cnd =>
    match cnd with
    | Ccomp c => with_args (id_binop d (Icomp true c))
    | Ccompu c => with_args (id_binop d (Icomp false c))
    | Ccompimm c i => with_arg (λ x, id_binop d (Icomp true c) x (id_const d i))
    | Ccompuimm c i => with_arg (λ x, id_binop d (Icomp false c) x (id_const d i))
    | Cmaskzero m => with_arg (id_unop d (Imaskzero true m))
    | Cmasknotzero m => with_arg (id_unop d (Imaskzero false m))
    | Ccompf _ | Cnotcompf _ => All
    end

  | Ofloatconst _
  | Oindirectsymbol _
  | Omulhs
  | Omulhu
  | Onegf | Oabsf
  | Oaddf | Osubf
  | Omulf | Odivf
  | Osingleoffloat
  | Ointoffloat
  | Ofloatofint
  | Omakelong
  | Olowlong | Ohighlong
  | OX _
    => All
  end.

Definition box_concretize (ne: nexpr var) (b: box) : SetInterface.set Z +⊤ :=
  topbind (id_concretize d) (eval_nexpr ne b).

Definition box_forget (v: var) (b: box) : box +⊥ :=
  NotBot (map_forget b v).

Definition box_assign (v: var) (ne: nexpr var) (b: box) : box +⊥ :=
  NotBot (map_assign b v (eval_nexpr ne b)).

Definition box_assume (ne: nexpr var) (n: int) (b: box) : box +⊥ :=
  let '(op, args) := ne in
  match op with
  | Omove => match args with x :: nil => NotBot (b [ x <- id_const d n]) | _ => Bot end
  | Ointconst i => if Int.eq i n then NotBot b else Bot
  | Ofloatconst _ | Oindirectsymbol _
    => Bot
  | Ocmp cnd =>
    match cnd with
    | Ccomp c =>
      match args with
      | x :: y :: nil => botlift_fun1
                           (λ r, let '(x', y') := r in map_assign (map_assign b x x')  y y')
                           (id_backward_cmp d true c (map_get b x) (map_get b y) (id_const d n))
      | _ => Bot
      end
    | Ccompu c =>
      match args with
      | x :: y :: nil => botlift_fun1
                           (λ r, let '(x', y') := r in map_assign (map_assign b x x')  y y')
                           (id_backward_cmp d false c (map_get b x) (map_get b y) (id_const d n))
      | _ => Bot
      end
    | Ccompimm c i =>
      match args with
      | x :: nil => botlift_fun1
                           (λ r, let '(x', _) := r in map_assign b x x')
                           (id_backward_cmp d true c (map_get b x) (Just (id_const d i)) (id_const d n))
      | _ => Bot
      end
    | Ccompuimm c i =>
      match args with
      | x :: nil => botlift_fun1
                           (λ r, let '(x', _) := r in map_assign b x x')
                           (id_backward_cmp d false c (map_get b x) (Just (id_const d i)) (id_const d n))
      | _ => Bot
      end
    | _ => NotBot b
    end
  | Ocast8signed | Ocast8unsigned
  | Ocast16signed | Ocast16unsigned
  | _ => NotBot b
  end.

Definition box_dom : num_dom box var :=
  {|
    nd_wlat := box_wlat;
    nd_concretize := box_concretize;
    nd_assume := box_assume;
    nd_forget := box_forget;
    nd_assign := box_assign
  |}.

End BOX.
