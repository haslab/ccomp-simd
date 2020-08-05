Require Import Containers.Maps.
Require Import AdomLib.
Import Utf8.
Import ToString.

Section MAP_WLAT.
  (* Lattice structure for maps with implicit binding to TOP *)
  Context {K V: Type} {Kot: OrderedType K}.
  Context `{ToString K} `{ToString V}.
  Context (order: V → V → bool) (join widen: V → V → V+⊤).

  Global
  Instance string_of_map : ToString (Map [ K, V ]) :=
    (
      λ m,
      "{" ++
          fold (λ k v s,
                to_string k ++ " ↦ " ++ to_string v ++ "; " ++ s
               ) m "}"
    )%string.

  Definition map_leb (m m': Map [ K, V ]) : bool :=
    MapFacts.for_all
      (λ k v',
       match (m)[k] with
       | None => false
       | Some v => order v v'
       end)
      m'.

  Definition map_combine (j: V → V → V+⊤) (m m': Map [ K, V ]) : Map [ K, V ] :=
    fold
      (λ k v r,
       match (m')[k] with
       | None => r
       | Some v' => match j v v' with All => r | Just s => r [k <- s] end
       end)
      m
      (empty _).

  Definition map_wlat : wlat (Map [ K, V]) :=
    WL (empty _) map_leb (map_combine join) (map_combine widen) _.

  Definition map_to_toplift (m: Map [ K, V ]) : Map [ K, V ] +⊤ :=
    if is_empty m then All else Just m.

  Definition map_get (m: Map [ K, V]) (k: K) : V+⊤ :=
    match (m)[k] with
    | None => All
    | Some v => Just v
    end.

  Definition map_forget (m: Map [ K, V ]) (k: K) : Map [ K, V ] :=
    remove k m.

  Definition map_assign (m: Map [ K, V ]) (k: K) (v: V+⊤) : Map [ K, V ] :=
    match v with
    | All => map_forget m k
    | Just v' => m [ k <- v' ]
    end.

End MAP_WLAT.

Section BMAP_WLAT.
  (* Lattice structure for maps with implicit binding to BOTTOM *)
  Context {K V: Type} {Kot: OrderedType K}.
  Context `{ToString K} `{ToString V}.
  Context (order: V → V → bool) (join widen: V → V → V).

  Definition bmap_leb (m m': Map [ K, V ]) : bool :=
    MapFacts.for_all
      (λ k v,
       match (m')[k] with
       | None => false
       | Some v' => order v v'
       end)
      m.

  Definition bmap_to_botlift (m: Map [ K, V ]) : Map [ K, V ] +⊥ :=
    if is_empty m then Bot else NotBot m.

  Definition bmap_get (m: Map [ K, V]) (k: K) : V+⊥ :=
    match (m)[k] with
    | None => Bot
    | Some v => NotBot v
    end.

  Definition bmap_assign (m: Map [ K, V ]) (k: K) (v: V+⊥) : Map [ K, V ] :=
    match v with
    | Bot => remove k m
    | NotBot v' => m [ k <- v' ]
    end.

  Definition bmap_combine (j: V → V → V) (m m': Map [ K, V ]) : Map [ K, V ] :=
    fold
      (λ k v r,
       match (m')[k] with
       | None => r [ k <- v ]
       | Some v' => r [ k <- j v v' ]
       end)
      m
      m'.

  Definition bmap_map {V': Type} (f: V → V'+⊥) (m: Map [ K, V ]) : Map [ K, V' ] :=
    fold
      (λ k v r,
       match f v with
       | Bot => r
       | NotBot v' => r [ k <- v' ]
       end)
      m
      (empty _).

End BMAP_WLAT.
