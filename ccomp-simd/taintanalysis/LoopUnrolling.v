Require Import MemDom.
Require Import MapLattice.
Import Containers.Maps.

Import Coqlib.
Import AST.
Import Integers.
Import AdomLib.
Import ToString.

Unset Elimination Schemes.

(** A simple version of the trace partitioning abstract domain
(Mauborgne et Rival, ESOP’05, TOPLAS’07)
that is specialized to loop unrolling,
in which loops are labeled with [int] values.
*)

Definition key : Type := positive.

Definition key_of_int (i: int) : key :=
  match Int.unsigned i with
  | Zpos p => Pos.succ p
  | Z0 | Zneg _ => xH
  end.

Definition int_of_key (k: key) : int :=
  Int.repr match k with xH => Z0 | xI p => Zpos p | xO p => Zpos (Pos.pred_double p) end.

Definition log : Type :=
  list (key * positive).

Instance logOT : OrderedType log := _.

Definition get_first_key (k: key) (m: log) : option (positive * log) :=
  match m with
  | nil => None
  | (k', v) :: m' => if k =? k' then Some (v, m') else None
  end%positive.

Definition push (k: key) (m: log) : log :=
  match get_first_key k m with
  | None => (k, xH) :: m
  | Some (n, m') => (k, Pos.succ n) :: m'
  end.

Definition pop (k: key) (m: log) : log :=
  match get_first_key k m with
  | None => m
  | Some (_, m') => m'
  end.

Section MEM_DOM.

Context (D: Type) (d: memdom D).

Definition partition : Type :=
  Map [ log, D ].

Let string_of_d : ToString D := d.(wl_to_string).
Existing Instance string_of_d.

Instance string_of_partition : ToString (partition+⊤) := _.

Record tpmd : Type :=
  TPMD {
      tp_md :> memdom (partition+⊤);
      tp_generate: int → partition → partition;
      tp_merge: int → partition → partition
    }.

Definition generate (i: int) (p: partition) : partition :=
  let i := key_of_int i in
  fold (λ k v r, r [ push i k <- v ]) p (empty _).

Definition merge (i: int) (p: partition) : partition :=
  let i := key_of_int i in
  fold (λ k v r, r [ pop i k <- v ]) p (empty _).

Definition partition_wlat : wlat (partition+⊤) :=
  {|
    wl_top := All;
    wl_order := toplift_leb (bmap_leb (wl_order d));
    wl_join := toplift_combine (bmap_combine (wl_join d));
    wl_widen := toplift_combine (bmap_combine (wl_widen d))
  |}.

Definition reduce_partition (m: partition) : partition+⊤+⊥ :=
  botlift_fun1 Just (bmap_to_botlift m).

Definition lift (f: D → D+⊥) (m: partition+⊤) : partition+⊤+⊥ :=
  match m with
  | All => NotBot All
  | Just m => reduce_partition (bmap_map f m)
  end.

Definition nodup_app {X} `{EqDec X} (x y: list X) : list X :=
  List.fold_left (λ y x,
                  if in_dec eq_dec x y then y else x :: y
                 ) x y.

Definition partition_deref (m: partition +⊤+⊥) (addr: Op.addressing) (args: list Machregs.mreg)
  : option (list AbCell.points_to_hint) :=
  match m with
  | Bot => aderef _ d Bot addr args
  | NotBot All => None
  | NotBot (Just m) =>
    fold
      (λ _ v r,
       match r with
       | None => None
       | Some r =>
         match aderef _ d (NotBot v) addr args with
         | None => None
         | Some y => Some (nodup_app y r)
         end
       end)
      m
      (Some nil)
  end.

Definition ulmd : tpmd :=
  {| tp_md :=
       {| wl := partition_wlat
        ; init defs := reduce_partition (bmap_assign (empty _) nil (init _ d defs))
        ; aassume e := lift (aassume _ d e)
        ; aassign dst r := lift (aassign _ d dst r)
        ; astore src ϰ addr args := lift (astore _ d src ϰ addr args)
        ; abuiltin x ef y := lift (abuiltin _ d x ef y)
        ; asyscall ef := lift (asyscall _ d ef)
        ; acall := lift (acall _ d)
        ; areturn := lift (areturn _ d)
        ; aderef := partition_deref
       |}
     ;
     tp_generate := generate
     ;
     tp_merge := merge
  |}.

End MEM_DOM.
