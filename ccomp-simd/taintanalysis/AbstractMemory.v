Require Import Expr.
Require Import NumDom.
Require Import MapLattice.
Require Import ClassifyBuiltIns.

Import Containers.Maps.
Import Coqlib.
Import AST.
Import Integers.
Import Machregs.
Import ToString.
Import AdomLib.
Import ABlock.
Import TypeDomain.

Unset Elimination Schemes.

Definition pairF {A A' A'' B B' B''}
           (f: A → A' → A'') (g: B → B' → B'')
  : A * B → A' * B' → A'' * B'' :=
  λ x y, let '(a, b) := x in let '(a', b') := y in (f a a', g b b').

Infix "×" := pairF (at level 100).

Section AMEM.

Context (num: Type).

Definition cell : Type :=
  (ablock * Z * cell_size + mreg)%type.

Instance cellOT: OrderedType cell := _.

Definition overlap_aux {A} (f: cell → A → A) (b: ablock) (ofs: Z) (sz: cell_size) (n: N) (a: A) : A :=
  let base := ofs - Z.of_N (N_of_cell_size sz) + 1 in
  N.peano_rect (λ _, A)
               a
               (λ n,
                let ofs' := base + Z.of_N n in
                f (inl (b, ofs', sz))
               )
               n.

(* All cells that overlap with a given one but are distinct from it *)
Definition overlap {A} (c: cell) (f: cell → A → A) : A → A :=
  match c with
  | inr _ => id
  | inl (b, ofs, sz) =>
    fold_cell_size
      (λ sz',
       if eq_dec sz sz'
       then
         (overlap_aux f b ofs sz (N.pred (N_of_cell_size sz))) ∘
         (overlap_aux f b (ofs + Z.of_N (N_of_cell_size sz)) sz (N.pred (N_of_cell_size sz)))
       else overlap_aux f b ofs sz' (N.pred (N_of_cell_size sz + N_of_cell_size sz'))
      )
  end.

Record amem : Type :=
  AM {
      am_types: Map [ cell, type ]
      ;
      am_num: num
      ;
      am_stack: N+⊤
    }.

Definition fake_concretize (ne: nexpr cell) (_: num) : SetInterface.set Z +⊤ :=
  let '(op, args) := ne in
  match op with
  | Op.Ointconst i => Just (SetInterface.singleton (Int.unsigned i))
  | _ => All
  end.

Context (d: num_dom num cell).

Definition am_top : amem :=
  AM (empty _) (wl_top d) All.

Definition types_wlat : wlat (Map [ cell, type ]) :=
  map_wlat type_leb type_join type_join.

Definition am_order (am am': amem) : bool :=
  let 'AM τ ν σ := am in
  let 'AM τ' ν' σ' := am' in
  match σ' with All => true | Just stk' =>
  match σ with All => false | Just stk =>
  if wl_order d ν ν' then wl_order types_wlat τ τ'
  else false
  end end.

Definition am_combine (j: num → num → num) (am am': amem) : amem :=
  let 'AM τ ν σ := am in
  let 'AM τ' ν' σ' := am' in
  if eq_dec σ σ'
  then AM (wl_join types_wlat τ τ') (j ν ν') σ
  else am_top.

Definition am_join := am_combine (wl_join d).
Definition am_widen := am_combine (wl_widen d).

Local Instance string_of_num : ToString num := wl_to_string d.

Instance string_of_amem : ToString amem :=
  λ am,
  let 'AM τ ν σ := am in
  to_string (τ, ν, σ).

Definition amem_wlat : wlat amem :=
  WL am_top am_order am_join am_widen _.

Section CONVERT.
Import Sets.

Definition cell_product_aux g κ : set Z → set cell → set cell :=
  fold (λ i s, {inl (g, Int.unsigned (Int.repr i), κ); s}).

Definition cell_product (s: set ablock) κ (ofs: set Z) : set cell +⊤ :=
  fold (λ b,
        topbind
          (λ s, Just (cell_product_aux b κ ofs s)
          )) s (Just {}).

Definition classify_ptr (ptr: type) :
  { bs | ptr = TyZPtr bs ∨ ptr = TyPtr bs } + { ptr = TyIntPtr } +
  { match ptr with TyFloat | TySingle | TyL64 | TyL128 | TyInt | TyZero => True | _ => False end } :=
  match ptr with
  | TyIntPtr => inleft (inright eq_refl)
  | TyZPtr bs => inleft (inleft (exist _ bs (or_introl eq_refl)))
  | TyPtr bs => inleft (inleft (exist _ bs (or_intror eq_refl)))
  | _ => inright I
  end.

Definition deref_pexpr (σ: N) (τ: Map [ cell, type ]) (ν: num)
           (κ: cell_size) (pe: pexpr cell) : set cell +⊤ :=
  topbind
    (λ ptr,
     match classify_ptr ptr with
     | inleft (inleft (exist bs EQ)) =>
       topbind
         (λ bs : set ablock,
          List.fold_left
            (λ (x: set cell +⊤) (ne: nexpr cell),
             topbind
               (λ x : set cell,
                topbind
                  (λ ofs : set Z,
                   topbind
                     (λ cs : set cell, Just (cs ++ x))
                     (cell_product bs κ ofs))
                  (nd_concretize d ne ν)
               )
               x)
            (ne_of_pe (map_get τ) pe)
            (Just {})
         )
         bs
     | inleft (inright EQ) => All
     | inright K => Just {}
     end)
    (eval_ptr σ (map_get τ) pe).

Let pexpr_of_cell (c: cell) : pexpr cell :=
  (Op.Omove, c :: nil).

Let cast (s: set cell) : list (pexpr cell) :=
  fold (λ c, cons (pexpr_of_cell c)) s nil.

Definition convert_address κ addr args σ τ ν :=
  deref_pexpr σ τ ν (cell_size_of_chunk κ) (Op.Olea addr, List.map inr args).

Definition convert (e: expr) (am: amem) : list (pexpr cell) +⊤ :=
  let 'AM τ ν σ := am in
  match e with
  | EGetParam ofs ty =>
    match σ with
    | All | Just N0 => All
    | Just (Npos σ) =>
    let c : cell := inl (ABStack (Pos.pred σ), Int.unsigned ofs, cell_size_of_typ ty) in
    Just (pexpr_of_cell c :: nil)
    end
  | ELoad κ addr args =>
    topbind (λ σ',
       toplift_fun1 cast (convert_address κ addr args σ' τ ν)
      ) σ
  | EOp op args => Just ((op, List.map inr args) :: nil)
  end.

End CONVERT.

Definition am_num_assign (c: cell) (e: nexpr cell) (ν: num) : num +⊥ :=
  overlap
    c
    (λ c, botbind (nd_forget d c))
    (nd_assign d c e ν).

Definition am_forget (c: cell) (am: amem) : amem +⊥ :=
  let 'AM τ ν σ := am in
  botlift_fun1
    (λ ν, AM (map_forget τ c) ν σ)
    (nd_forget d c ν).

Definition set_map_reduce {A B} {OT: OrderedType A}
           (f: A → B+⊥)
           (j: B → B → B)
           (s: SetInterface.set A)
  : B+⊥ :=
  SetInterface.fold (botlift_combine j ∘ f) s Bot.

Definition list_map_reduce {A B}
           (f: A → B+⊥)
           (j: B → B → B)
  : list A → B+⊥ :=
  list_fold_left (botlift_combine j ∘ f) Bot.

Definition am_assign_one (c: cell) τ σ res : amem +⊥ :=
  let '(ty, ν') := res in
  overlap c
    (botbind ∘ am_forget)
    (NotBot (AM (map_assign τ c ty) ν' σ)).

Definition am_assign_cells (dst: SetInterface.set cell) (e: expr) (am: amem) : amem +⊥ :=
  match convert e am with
  | All =>
    SetInterface.fold
      (λ c,
       botbind
         ((overlap c (botbind ∘ am_forget)) ∘ (am_forget c))
      ) dst (NotBot am)
  | Just pes =>
    let 'AM τ ν σ := am in
    match σ with All => NotBot am_top | Just stk =>
    set_map_reduce
      (λ c,
       botbind
         (am_assign_one c τ σ)
         (list_map_reduce
            (λ pe,
             botlift_fun1
               (λ ν', (eval_ptr stk (map_get τ) pe, ν'))
               (list_map_reduce
                  (λ ne, nd_assign d c ne ν)
                  (wl_join d)
                  (ne_of_pe (map_get τ) pe))
            )
            (topbind2 type_join × wl_join d)
            pes)
      )
      am_join
      dst
  end end.

Definition am_aassign (dst: mreg) (e: expr) (am: amem) : amem +⊥ :=
  am_assign_cells (SetInterface.singleton (inr dst)) e am.

Definition add_cast_for_chunk (κ: memory_chunk) (r: mreg) : expr :=
  EOp
  match κ with
  | Mint8signed => Op.Ocast8signed
  | Mint8unsigned => Op.Ocast8unsigned
  | Mint16signed => Op.Ocast16signed
  | Mint16unsigned => Op.Ocast16unsigned
  | Mint32 | Mint64 | Mint128
  | Mfloat32 | Mfloat64
    => Op.Omove
  end (r :: nil).

Definition am_astore (src: mreg) (κ: memory_chunk) (addr: Op.addressing) (args: list mreg) (am: amem) : amem +⊥ :=
  let 'AM τ ν σ := am in
  match σ with
  | All => NotBot am_top
  | Just σ =>
  match convert_address κ addr args σ τ ν with
  | All => NotBot am_top
  | Just dst => am_assign_cells dst (add_cast_for_chunk κ src) am
  end end.

Definition types_assume (τ: Map [ cell, type ]) (pe: pexpr cell) (n: int) : Map [ cell, type ] :=
  (* TODO *)
  τ.

Definition am_aassume (a: assertion) (am: amem) : amem +⊥ :=
  let '(pe, n) :=
      match a with
      | AssertBool op args b => ((Op.Ocmp op, List.map inr args), if b then Int.one else Int.zero)
      | AssertNat r n => ((Op.Omove, inr r :: nil), n)
      end
  in
  let 'AM τ ν σ := am in
  let nes := ne_of_pe (map_get τ) pe in
  botlift_fun1
    (λ ν', AM (types_assume τ pe n) ν' σ)
    (list_map_reduce
       (λ ne, nd_assume d ne n ν)
       (wl_join d)
       nes).

Definition am_abuiltin (dst: list mreg) (ef: external_function) (args: list mreg)
           (am: amem) : amem +⊥ :=
  match ef with
  | EF_builtin f iar sg =>
    match classify_builtin f iar sg dst args with
    | BuiltinUnsupported | BuiltinUnknown => NotBot am_top
    | BuiltinPure _ _ =>
      List.fold_left (λ am r, botbind (am_forget (inr r)) am) dst (NotBot am)
    | BuiltinLoad ptr sz ar _ =>
      match dst with
      | d :: nil =>
        (* We don’t need full precision *)
        (* am_aassign d (ELoad sz ptr ar) am *)
        am_forget (inr d) am
      | _ => Bot end
    | BuiltinStore ptr sz ar _ =>
      match ar with
      | v :: nil =>
        match
        match sz with
        | 1 => Some Mint8unsigned
        | 4 => Some Mint32
        | 8 => Some Mint64
        | 16 => Some Mint128
        | _ => None
        end
        with
        | None => NotBot am_top
        | Some κ => am_astore v κ (Op.Aindexed Int.zero) (ptr :: nil) am
        end
      | _ => Bot end
    end
  | EF_vload _
  | EF_vload_global _ _ _
    =>
    List.fold_left (λ am r, botbind (am_forget (inr r)) am) dst (NotBot am)
  | _ => NotBot am_top
  end.

Definition am_store_init_data (s: ident) (amz: (amem * Z) +⊥) (v: init_data) : (amem * Z) +⊥ :=
  let ab := ABGlobal s in
  botbind
    (λ amz,
     let '(am, z) := amz in
     let c cz := SetInterface.singleton (inl (ab, z, cz)) in
     let ret := botlift_fun1 (λ am, (am, z + Globalenvs.Genv.init_data_size v)) in
  match v with
  | Init_int8 i => ret (am_assign_cells (c CZ1) (EOp (Op.Ointconst i) nil) am)
  | Init_int16 i => ret (am_assign_cells (c CZ2) (EOp (Op.Ointconst i) nil) am)
  | Init_int32 i => ret (am_assign_cells (c CZ4) (EOp (Op.Ointconst i) nil) am)
  | Init_addrof g i => ret (am_assign_cells (c CZ4) (EOp (Op.Olea (Op.Aglobal g i)) nil) am)
  | Init_int64 _
  | Init_float32 _
  | Init_float64 _
  | Init_space _ => ret (NotBot am) (* TODO *)
  end) amz.

Definition am_alloc_global (s: ident) (gv: globvar unit) (am: amem) : amem +⊥ :=
  if gvar_volatile gv then NotBot am else
  botlift_fun1 fst (List.fold_left (am_store_init_data s) (gvar_init gv) (NotBot (am, 0))).

Definition am_alloc_globals {F} : list (ident * globdef F unit) → amem +⊥ → amem +⊥ :=
  fold_left
    (λ am sd,
     let '(s, d) := sd in
     match d with
     | Gfun _ => am
     | Gvar gv => botbind (am_alloc_global s gv) am
     end).

Definition am_init {F} (defs: list (ident * globdef F unit)) : amem +⊥ :=
  am_alloc_globals
    defs
    (NotBot {|
      am_types := empty _;
      am_num := wl_top d;
      am_stack := Just N0
    |}).

Definition am_acall (am: amem) : amem +⊥ :=
  let 'AM τ ν σ := am in
  NotBot (AM τ ν (toplift_fun1 N.succ σ)).

Definition invalid_cell_after_return (σ: positive) (c: cell) (ty: type) : bool :=
  if match c with
  | inr _ | inl (ABGlobal _, _, _) => false
  | inl (ABStack p, _, _) => Pos.eqb p σ
  end then true else
  match ty with
  | (TyFloat | TySingle | TyL64 | TyL128 | TyZero | TyInt)
    => false
  | TyIntPtr
  | TyPtr All
  | TyZPtr All
    => true
  | TyZPtr (Just bs)
  | TyPtr (Just bs)
    => SetInterface.mem (ABStack σ) bs
  end.

Definition invalid_cells_after_return (σ: positive) (τ: Map [ cell, type ]) : SetInterface.set cell :=
  fold (λ c ty,
        if invalid_cell_after_return σ c ty
        then SetInterface.add c
        else id
        ) τ SetInterface.empty.

Definition am_areturn (am: amem) : amem +⊥ :=
  let 'AM τ ν σ := am in
  match σ with
  | All => NotBot am
  | Just N0 => Bot
  | Just (Npos p) =>
    (* Forget stack-allocated values, pointers to stack *)
    let ic := invalid_cells_after_return p τ in
    SetInterface.fold
      (λ c, botbind (am_forget c))
      ic
      (NotBot (AM τ ν (Just (Pos.pred_N p))))
  end.

Require Import AbCell.

Definition relative_stack_depth (stk: N) (n: positive) : nat :=
  N.to_nat (stk - Npos n).

Definition am_aderef (am: amem +⊥) (addr: Op.addressing) (args: list mreg) : option (list (points_to_hint)) :=
  match am with
  | Bot => Some nil
  | NotBot (AM τ ν σ) =>
    match σ with
    | All => None
    | Just stk =>
      match convert_address Mint8unsigned addr args stk τ ν with
      | All => None
      | Just cs =>
        Some (
        SetInterface.fold
          (λ c acc,
           match c with
           | inr _ => acc
           | inl (ab, ofs, cz) =>
             (match ab with
              | ABGlobal g => Global g ofs
              | ABStack n => Stack (relative_stack_depth stk n) ofs
              end, Z0) :: acc
           end)
          cs
          nil
          )
      end
  end end.

End AMEM.

(* Specialized version of box_dom to the cell type, and to strided intervals. *)
Require SIND.
Definition box_dom := Box.box_dom cell _ _ _ SIND.sind.

(* Memory abstract domain, with boxes of strided intervals *)
Require Import MemDom.
Definition abstract_mem : memdom _ :=
  {|
    wl := amem_wlat _ box_dom;
    init := am_init _ box_dom;
    aassume := am_aassume _ box_dom;
    aassign := am_aassign _ box_dom;
    astore := am_astore _ box_dom;
    abuiltin := am_abuiltin _ box_dom;
    asyscall := λ _ _, NotBot (am_top _ box_dom);
    acall := am_acall _;
    areturn := am_areturn _ box_dom;

    aderef := am_aderef _ box_dom
  |}.

(* Partitioned domain *)
Require Import LoopUnrolling.
Definition partitioned_abstract_mem : tpmd _ :=
  ulmd _ abstract_mem.
