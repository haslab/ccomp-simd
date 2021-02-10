(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

open Printf
open Camlcoq
open Datatypes
open AST
open Registers
open Machregs
open Locations
open Conventions1
open Conventions
open XTL

(* Iterated Register Coalescing: George and Appel's graph coloring algorithm *)

type var_stats = {
  mutable cost: int;             (* estimated cost of a spill *)
  mutable usedefs: int           (* number of uses and defs *)
}

(* Representation of the interference graph.  Each node of the graph
   (i.e. each variable) is represented as follows. *)

type node =
  { ident: int;                         (*r unique identifier *)
    typ: typ;                           (*r its type *)
    var: var;                           (*r the XTL variable it comes from *)
    hivar: var option;			(*r hi-var in double node *)
    regclass: int;                      (*r identifier of register class *)
    mutable accesses: int;              (*r number of defs and uses *)
    mutable spillcost: float;           (*r estimated cost of spilling *)
    mutable adjlist: node list;         (*r all nodes it interferes with *)
    mutable degree: int;                (*r number of adjacent nodes *)
    mutable movelist: move list;        (*r list of moves it is involved in *)
    mutable extra_adj: node list;       (*r extra interferences (see below) *)
    mutable extra_pref: move list;      (*r extra preferences (see below) *)
    mutable alias: (node*(bool option)) option;         (*r [Some n] if coalesced with [n] *)
    mutable color: loc option;          (*r chosen color *)
    mutable nstate: nodestate;          (*r in which set of nodes it is *)
    mutable nprev: node;                (*r for double linking *)
    mutable nnext: node                 (*r for double linking *)
  }

(* These are the possible states for nodes. *)

and nodestate =
  | Colored
  | Initial
  | SimplifyWorklist
  | FreezeWorklist
  | SpillWorklist
  | CoalescedNodes
  | SelectStack

(* Each move (i.e. wish to be put in the same location) is represented
   as follows. *)

and move =
  { src: node*(bool option);                          (*r source of the move *)
    dst: node*(bool option);                          (*r destination of the move *)
    mutable mstate: movestate;          (*r in which set of moves it is *)
    mutable mprev: move;                (*r for double linking *)
    mutable mnext: move                 (*r for double linking *)
  }

(* These are the possible states for moves *)

and movestate =
  | CoalescedMoves
  | ConstrainedMoves
  | FrozenMoves
  | WorklistMoves
  | ActiveMoves

let isDoubleNode n = 
  match n.hivar with
  | Some _ -> assert (n.typ = Tfloat); true
  | _ -> match n.alias with
	 | Some (_,Some _) -> true
	 | _ -> false

let double_pair_reg r =
  match r with
  | F0 -> F1 | F2 -> F3 | F4 -> F5 | F6 -> F7 | F8 -> F9
  | F10 -> F11 | F12 -> F13 | F14 -> F15 | F16 -> F17 | F18 -> F19
  | F20 -> F21 | F22 -> F23 | F24 -> F25 | F26 -> F27 | F28 -> F29
  | F30 -> F31 | _ -> assert false

(* Note on "precolored" nodes and how they are handled:

The register allocator can express interferences and preferences between
any two values of type [var]: either pseudoregisters, to be colored by IRC,
or fixed, "precolored" locations.

I and P between two pseudoregisters are recorded in the graph that IRC
modifies, via the [adjlist] and [movelist] fields.

I and P between a pseudoregister and a machine register are also
recorded in the IRC graph, but only in the [adjlist] and [movelist]
fields of the pseudoregister.  This is the special case described
in George and Appel's papers.

I and P between a pseudoregister and a stack slot
are omitted from the IRC graph, as they contribute nothing to the
simplification and coalescing process.  We record them in the
[extra_adj] and [extra_pref] fields, where they can be honored
after IRC elimination, when assigning a stack slot to a spilled variable. *)

let name_of_loc = function
  | R r ->
      begin match Machregsaux.name_of_register r with
                | None -> "fixed-reg"
                | Some s -> s
      end
  | S (Local, ofs, ty) ->
      sprintf "L%c%ld" (PrintXTL.short_name_of_type ty) (camlint_of_coqint ofs)
  | S (Incoming, ofs, ty) ->
      sprintf "I%c%ld" (PrintXTL.short_name_of_type ty) (camlint_of_coqint ofs)
  | S (Outgoing, ofs, ty) ->
      sprintf "O%c%ld" (PrintXTL.short_name_of_type ty) (camlint_of_coqint ofs)

let name_of_node n =
  match n.var with
  | V(r, ty) -> sprintf "x%ld" (P.to_int32 r)
  | L l -> name_of_loc l

let name_of_node_slot ni =
  let (n,noff) = ni in
  match n.var with
  | V(r, ty) -> sprintf "x%ld%s" (P.to_int32 r) (match noff with None -> " "|Some b -> if b then "H" else "L")
  | L l -> sprintf "%s%s" (name_of_loc l) (match noff with None -> " "|Some b -> if b then "H" else "L")

let state_name = function
  | Colored -> "Colored"
  | Initial -> "Initial"
  | SimplifyWorklist -> "SimplifyWorkList"
  | FreezeWorklist -> "FreezeWorkList"
  | SpillWorklist -> "SpillWorklist"
  | CoalescedNodes -> "CoalescedNodes"
  | SelectStack -> "SelectStack"

let print_node n =
  let alias_s = match n.alias with None -> "None" | Some x -> name_of_node_slot x in
  let rec print_list l = match l with
    | [] -> ()
    | [x] -> printf "%s%s%s" (name_of_node x) (if isDoubleNode x then "'" else "") (if n.color<>None then "C" else "")
    | (x::xs) -> printf "%s%s%s," (name_of_node x) (if isDoubleNode x then "'" else "") (if n.color<>None then "C" else ""); print_list xs in
  printf "%s%s%s: degree=%d, alias=%s, state=%s, interfs=["
		(name_of_node n) (if isDoubleNode n then "'" else "") (if n.color<>None then "C" else "") n.degree alias_s (state_name n.nstate);
  print_list n.adjlist;
  printf "]\n"
  
(* The algorithm manipulates partitions of the nodes and of the moves
   according to their states, frequently moving a node or a move from
   a state to another, and frequently enumerating all nodes or all moves
   of a given state.  To support these operations efficiently,
   nodes or moves having the same state are put into imperative doubly-linked
   lists, allowing for constant-time insertion and removal, and linear-time
   scanning.  We now define the operations over these doubly-linked lists. *)

module DLinkNode = struct
  type t = node
  let make state =
    let rec empty =
      { ident = 0; typ = Tint; var = V(P.one, Tint); hivar = None; regclass = 0;
        adjlist = []; degree = 0; accesses = 0; spillcost = 0.0;
        movelist = []; extra_adj = []; extra_pref = [];
        alias = None; color = None;
        nstate = state; nprev = empty; nnext = empty }
    in empty
  let dummy = make Colored
  let clear dl = dl.nnext <- dl; dl.nprev <- dl
  let notempty dl = dl.nnext != dl
  let insert n dl =
    n.nstate <- dl.nstate;
    n.nnext <- dl.nnext; n.nprev <- dl;
    dl.nnext.nprev <- n; dl.nnext <- n
  let remove n dl =
    assert (n.nstate = dl.nstate);
    n.nnext.nprev <- n.nprev; n.nprev.nnext <- n.nnext
  let move n dl1 dl2 =
    remove n dl1; insert n dl2
  let pick dl =
    let n = dl.nnext in remove n dl; n
  let iter f dl =
    let rec iter n = if n != dl then (f n; iter n.nnext)
    in iter dl.nnext
  let fold f dl accu =
    let rec fold n accu = if n == dl then accu else fold n.nnext (f n accu)
    in fold dl.nnext accu
end

module DLinkMove = struct
  type t = move
  let make state =
    let rec empty =
      { src = (DLinkNode.dummy,None); dst = (DLinkNode.dummy,None); 
        mstate = state; mprev = empty; mnext = empty }
    in empty
  let dummy = make CoalescedMoves
  let clear dl = dl.mnext <- dl; dl.mprev <- dl
  let notempty dl = dl.mnext != dl
  let insert m dl =
    m.mstate <- dl.mstate;
    m.mnext <- dl.mnext; m.mprev <- dl;
    dl.mnext.mprev <- m; dl.mnext <- m
  let remove m dl =
    assert (m.mstate = dl.mstate);
    m.mnext.mprev <- m.mprev; m.mprev.mnext <- m.mnext
  let move m dl1 dl2 =
    remove m dl1; insert m dl2
  let pick dl =
    let m = dl.mnext in remove m dl; m
(*
  let find s d dl =
    let rec iter m = if m == dl
		     then None
		     else (if (m.src) = m.dst (* = s 
			      && m.dst = d*)
			   then (Printf.printf "X\n"; m.mnext.mprev <- m.mprev;
				 m.mprev.mnext <- m.mnext;
				 Some m)
			   else iter m.mnext)
    in iter dl.mnext
 *)
  let iter f dl =
    let rec iter m = if m != dl then (f m; iter m.mnext)
    in iter dl.mnext
  let fold f dl accu =
    let rec fold m accu = if m == dl then accu else fold m.mnext (f m accu)
    in fold dl.mnext accu
end

(* Auxiliary data structures *)

module IntSet = Set.Make(struct
  type t = int
  let compare (x:int) (y:int) = compare x y
end)

module IntPairs = Hashtbl.Make(struct
    type t = int * int
    let equal ((x1, y1): (int * int)) (x2, y2) = x1 = x2 && y1 = y2
    let hash = Hashtbl.hash
  end)

(* The global state of the algorithm *)

type graph = {
  (* Machine registers available for allocation *)
  caller_save_registers: mreg array array;
  callee_save_registers: mreg array array;
  num_available_registers: int array;
  start_points: int array;
  allocatable_registers: mreg list;
  (* Costs for pseudo-registers *)
  stats_of_reg: reg -> var_stats;
  (* Mapping from XTL variables to nodes *)
  varTable: (var, node*(bool option)) Hashtbl.t;
  mutable nextIdent: int;
  (* The adjacency set  *)
  mutable adjSet: unit IntPairs.t;
  (* Low-degree, non-move-related nodes *)
  simplifyWorklist: DLinkNode.t;
  (* Low-degree, move-related nodes *)
  freezeWorklist: DLinkNode.t;
  (* High-degree nodes *)
  spillWorklist: DLinkNode.t;
  (* Nodes that have been coalesced *)
  coalescedNodes: DLinkNode.t;
  (* Moves that have been coalesced *)
  coalescedMoves: DLinkMove.t;
  (* Moves whose source and destination interfere *)
  constrainedMoves: DLinkMove.t;
  (* Moves that will no longer be considered for coalescing *)
  frozenMoves: DLinkMove.t;
  (* Moves enabled for possible coalescing *)
  worklistMoves: DLinkMove.t;
  (* Moves not yet ready for coalescing *)
  activeMoves: DLinkMove.t
}

(* Register classes and reserved registers *)

let num_register_classes = 2

let class_of_type = function
  | Tint -> 0
  | Tfloat | Tsingle -> 1
  | Tlong -> assert false
  | Tvec () -> assert false

let type_of_class c =
  if c = 0 then Tint else Tfloat

let reserved_registers = ref ([]: mreg list)

let rec remove_reserved = function
  | [] -> []
  | hd :: tl ->
      if List.mem hd !reserved_registers
      then remove_reserved tl
      else hd :: remove_reserved tl

(* Apply the given function to the relevant adjacent nodes of a node *)

let iterAdjacent f n =
  List.iter
    (fun n ->
      match n.nstate with
      | SelectStack | CoalescedNodes -> ()
      | _ -> f n)
    n.adjlist

(* Determine the moves affecting a node *)

let moveIsActiveOrWorklist m =
  match m.mstate with
  | ActiveMoves | WorklistMoves -> true
  | _ -> false

let nodeMoves n =
  List.filter moveIsActiveOrWorklist n.movelist

(* Determine whether a node is involved in a move *)

let moveRelated n =
  List.exists moveIsActiveOrWorklist n.movelist

(* Check invariants *)

let degreeInvariant g n =
  let c = ref (if isDoubleNode n then 1 else 0) in
  iterAdjacent (fun x -> incr c; if isDoubleNode x then incr c) n;
  if !c <> n.degree then begin
    print_node n;
    failwith("degree invariant violated by " ^ name_of_node n^" (should be "^string_of_int !c^")")
    end

let simplifyWorklistInvariant g n =
  if n.degree < g.num_available_registers.(n.regclass)
  && not (moveRelated n)
  then ()
  else failwith("simplify worklist invariant violated by " ^ name_of_node n)

let freezeWorklistInvariant g n =
  if n.degree < g.num_available_registers.(n.regclass)
  && moveRelated n
  then ()
  else begin
      print_node n;
      printf "moveRelated=%B\n" (moveRelated n);
      failwith("freeze worklist invariant violated by " ^ name_of_node n)
    end

let spillWorklistInvariant g n =
  if n.degree >= g.num_available_registers.(n.regclass)
  then ()
  else failwith("spill worklist invariant violated by " ^ name_of_node n)
(*
    (Printf.printf "\n\n spillWorkList Invariant FAIL!!\n";
     print_node n;)
 *)

let checkInvariants g =
  DLinkNode.iter
    (fun n -> degreeInvariant g n; simplifyWorklistInvariant g n)
    g.simplifyWorklist;
  DLinkNode.iter
    (fun n -> degreeInvariant g n; freezeWorklistInvariant g n)
    g.freezeWorklist;
  DLinkNode.iter
    (fun n -> degreeInvariant g n; spillWorklistInvariant g n)
    g.spillWorklist

(* Initialize and return an empty graph *)

let init costs =
  let int_caller_save = remove_reserved int_caller_save_regs
  and float_caller_save = remove_reserved float_caller_save_regs
  and int_callee_save = remove_reserved int_callee_save_regs
  and float_callee_save = remove_reserved float_callee_save_regs in
  {
    caller_save_registers =
      [| Array.of_list int_caller_save; Array.of_list float_caller_save |];
    callee_save_registers =
      [| Array.of_list int_callee_save; Array.of_list float_callee_save |];
    num_available_registers =
      [| List.length int_caller_save + List.length int_callee_save;
         List.length float_caller_save + List.length float_callee_save |];
    start_points =
      [| 0; 0 |];
    allocatable_registers =
      int_caller_save @ int_callee_save @ float_caller_save @ float_callee_save;
    stats_of_reg = costs;
    varTable = Hashtbl.create 253;
    nextIdent = 0;
    adjSet = IntPairs.create 997;
    simplifyWorklist = DLinkNode.make SimplifyWorklist;
    freezeWorklist = DLinkNode.make FreezeWorklist;
    spillWorklist = DLinkNode.make SpillWorklist;
    coalescedNodes = DLinkNode.make CoalescedNodes;
    coalescedMoves = DLinkMove.make CoalescedMoves;
    constrainedMoves = DLinkMove.make ConstrainedMoves;
    frozenMoves = DLinkMove.make FrozenMoves;
    worklistMoves = DLinkMove.make WorklistMoves;
    activeMoves = DLinkMove.make ActiveMoves
  }
  
(* Create nodes corresponding to XTL variables *)

let weightedSpillCost st =
  if st.cost < max_int
  then float_of_int st.cost
  else infinity

let newNodeOfReg g r ty hir =
  if (ty=Tlong || ty=Tvec ()) then begin
      printf "IRC: wrong type for x%d\n" (P.to_int r);
      assert false;
    end;
  let st = (g.stats_of_reg r) in
  let (usedefs,spillcost,hivar) =
    match hir with
    | None -> st.usedefs, weightedSpillCost st, None
    | Some hr -> let st2 = g.stats_of_reg hr in
		 ((st.usedefs + st2.usedefs),
		  (if st.cost < max_int && st2.cost < max_int
		   then float_of_int (st.cost + st2.cost)
		   else infinity),
		  Some (V(hr,ty))) in
  g.nextIdent <- g.nextIdent + 1;
  { ident = g.nextIdent; typ = ty; 
    var = V(r,ty); hivar = hivar; regclass = class_of_type ty;
    accesses = usedefs;
    spillcost = spillcost;
    adjlist = []; degree = if hir<>None then 1 else 0;
    movelist = []; extra_adj = []; extra_pref = [];
    alias = None;
    color = None;
    nstate = Initial;
    nprev = DLinkNode.dummy; nnext = DLinkNode.dummy }

let newNodeOfLoc g l =
  let ty = Loc.coq_type l in  
  if (ty=Tlong || ty=Tvec ()) then begin
      printf "IRC: wrong type for location %s\n" (name_of_loc l);
      assert false;
    end;
  g.nextIdent <- g.nextIdent + 1;
  { ident = g.nextIdent; typ = ty; 
    var = L l; hivar = None; regclass = class_of_type ty;
    accesses = 0; spillcost = 0.0;
    adjlist = []; degree = 0; movelist = []; extra_adj = []; extra_pref = [];
    alias = None;
    color = Some l;
    nstate = Colored;
    nprev = DLinkNode.dummy; nnext = DLinkNode.dummy }

let nodeOfVar g v : node*(bool option) =
  try
    Hashtbl.find g.varTable v
  with Not_found ->
     match v with
     | V(r, ty) -> 
	begin match offset_pair r with
	| None -> let n = newNodeOfReg g r ty None in
		  degreeInvariant g n;
		  Hashtbl.add g.varTable v (n,None);
		  (n,None)
	| Some (lowr,hir) -> let n = newNodeOfReg g lowr ty (Some hir) in
			     Hashtbl.add g.varTable (V(lowr,ty)) (n,Some false);
			     Hashtbl.add g.varTable (V(hir,ty)) (n,Some true);
			     (n,if lowr=r then Some false else Some true)
	end
     | L l -> let n = newNodeOfLoc g l in
	      Hashtbl.add g.varTable v (n,None);
	      (n,None)

(* Determine if two nodes interfere *)

let interfere g n1 n2 =
  let i1 = n1.ident and i2 = n2.ident in
  let p = if i1 < i2 then (i1, i2) else (i2, i1) in
  IntPairs.mem g.adjSet p

(* Add an edge to the graph. *)

let recordInterf n1 n2 =
  match n2.color with
  | None | Some (R _) ->
      if n1.regclass = n2.regclass then begin
        n1.adjlist <- n2 :: n1.adjlist;
        n1.degree  <- n1.degree + (if isDoubleNode n2 then 2 else 1)
      end else begin
        n1.extra_adj <- n2 :: n1.extra_adj
      end
  | Some (S _) ->
      (*i printf "extra adj %s to %s\n" (name_of_node n1) (name_of_node n2); *)
      n1.extra_adj <- n2 :: n1.extra_adj

let addEdge g n1 n2 =
  (*assert (n1 != n2);*)
  if n1!=n2 && not (interfere g n1 n2) then begin
    (*printf "edge  %s -- %s;\n" (name_of_node n1) (name_of_node n2);*)
    let i1 = n1.ident and i2 = n2.ident in
    let p = if i1 < i2 then (i1, i2) else (i2, i1) in
    IntPairs.add g.adjSet p ();
    if n1.nstate <> Colored then recordInterf n1 n2;
    if n2.nstate <> Colored then recordInterf n2 n1
  end;
  degreeInvariant g n1;
  degreeInvariant g n2

(* Add a move preference. *)

let recordMove g src dst =
  let n1 = fst src
  and n2 = fst dst in
  let m =
    { src = src; dst = dst; mstate = WorklistMoves;
      mnext = DLinkMove.dummy; mprev = DLinkMove.dummy } in
  n1.movelist <- m :: n1.movelist;
  n2.movelist <- m :: n2.movelist;
  DLinkMove.insert m g.worklistMoves

let recordExtraPref src dst =
  let n1 = fst src in
  let m =
    { src = src; dst = dst; mstate = FrozenMoves;
      mnext = DLinkMove.dummy; mprev = DLinkMove.dummy } in
  n1.extra_pref <- m :: n1.extra_pref

let addMovePref g src dst =
  let n1 = fst src
  and n2 = fst dst in
  assert (n1.regclass = n2.regclass);
  match n1.color, n2.color with
  | None, None ->
      recordMove g src dst
  | Some (R mr1), None ->
      if List.mem mr1 g.allocatable_registers then recordMove g src dst
  | None, Some (R mr2) ->
      if List.mem mr2 g.allocatable_registers then recordMove g src dst
  | Some (S _), None ->
      recordExtraPref dst src
  | None, Some (S _) ->
      recordExtraPref src dst
  | _, _ ->
      ()

(* Initial partition of nodes into spill / freeze / simplify *)

let initialNodePartition g =
  let seen = ref IntSet.empty in
  let part_node v ni =
    let (n,_) = ni in
    if not (IntSet.mem n.ident !seen)
    then begin
      seen := IntSet.add n.ident !seen;
      degreeInvariant g n;
      match n.nstate with
      | Initial ->
         let k = g.num_available_registers.(n.regclass) in
         if n.degree >= k then
           DLinkNode.insert n g.spillWorklist
         else if moveRelated n then
           DLinkNode.insert n g.freezeWorklist
         else
           DLinkNode.insert n g.simplifyWorklist
      | Colored -> ()
      | _ -> assert false
    end in
  Hashtbl.iter part_node g.varTable


(* Enable moves that have become low-degree related *)

let enableMoves g n =
  List.iter
    (fun m ->
      if m.mstate = ActiveMoves
      then DLinkMove.move m g.activeMoves g.worklistMoves)
    (nodeMoves n)

(* Simulate the removal of a node from the graph *)

let decrementDegree g n =
  let k = g.num_available_registers.(n.regclass) in
  let d = n.degree in
  if n.nstate <> Colored then begin
      n.degree <- d - 1;
      if (n.degree < 0) then failwith ("underflow degree in "^(name_of_node n));
      if d = k then begin
	  enableMoves g n;
	  iterAdjacent (enableMoves g) n;
	  if moveRelated n
	  then DLinkNode.move n g.spillWorklist g.freezeWorklist
	  else DLinkNode.move n g.spillWorklist g.simplifyWorklist
	end
    end

(* Simulate the effect of combining nodes [n1] and [n3] on [n2],
   where [n2] is a node adjacent to [n3]. *)

let combineEdge g n3 n1 n2 =
  (*printf "Combine edge %s %s %s\n" (name_of_node n3) (name_of_node n1) (name_of_node n2);*)
  degreeInvariant g n1;
  assert (n1 != n2);
  if interfere g n1 n2 then begin
    (* The two edges n2--n3 and n2--n1 become one, so degree of n2 decreases *)
    decrementDegree g n2;
    if isDoubleNode n3 then decrementDegree g n2
  end else begin
    (* Add new edge *)
    let i1 = n1.ident and i2 = n2.ident in
    let p = if i1 < i2 then (i1, i2) else (i2, i1) in
    IntPairs.add g.adjSet p ();
    if n1.nstate <> Colored then begin
      n1.adjlist <- n2 :: n1.adjlist;
      n1.degree  <- n1.degree + (if isDoubleNode n2 then 2 else 1)
    end;
    if n2.nstate <> Colored then begin
      n2.adjlist <- n1 :: n2.adjlist;
      (* n2's degree stays the same because the old edge n2--n3 disappears
         and becomes the new edge n2--n1 *)
      n2.degree  <- n2.degree + (if isDoubleNode n1 && not (isDoubleNode n3) then 1 else 0)
    end
  end;
  degreeInvariant g n1;
  degreeInvariant g n2

(* Simplification of a low-degree node *)

let simplify g =
  checkInvariants g;
  let n = DLinkNode.pick g.simplifyWorklist in
  (*printf "Simplifying "; print_node n;*)
  n.nstate <- SelectStack;
  iterAdjacent (fun x -> decrementDegree g x; if isDoubleNode n then decrementDegree g x) n;
  checkInvariants g;
  n

(* Briggs's conservative coalescing criterion.  In the terminology of
   Hailperin, "Comparing Conservative Coalescing Criteria",
   TOPLAS 27(3) 2005, this is the full Briggs criterion, slightly
   more powerful than the one in George and Appel's paper. *)

let canCoalesceBriggs g u v =
  let diffDeg = not(isDoubleNode v) && isDoubleNode u
		|| not(isDoubleNode u) && isDoubleNode v in
  let seen = ref IntSet.empty in
  let k = g.num_available_registers.(u.regclass) in
  let c = ref 0 in
  let consider other n =
    if not (IntSet.mem n.ident !seen) then begin
      seen := IntSet.add n.ident !seen;
      (* if n interferes with both u and v, its degree will decrease by one
         after coalescing *)
      let degree_after_coalescing =
        if interfere g n other
	then n.degree - (if isDoubleNode other then 2 else 1)
	else n.degree in
      if degree_after_coalescing >= k || n.nstate = Colored then begin
        incr c;
	if isDoubleNode n then incr c;
        if !c >= k then raise Exit
      end;
      (* coalescing would affect previous classification of adjacent nodes... *)
      if diffDeg && n.degree = k-1 && not(interfere g n other) then raise Exit
    end in
  try
    iterAdjacent (consider v) u;
    iterAdjacent (consider u) v;
    (*printf "  Briggs: OK for %s(%B) and %s(%B): [%B]\n" (name_of_node u) (isDoubleNode u) (name_of_node v) (isDoubleNode v) diffDeg;*)
    true
  with Exit ->
    (*i printf "  Briggs: no\n"; *)
    false

(* George's conservative coalescing criterion: all high-degree neighbors
   of [v] are neighbors of [u]. *)

let canCoalesceGeorge g u v =
  let diffDeg = not(isDoubleNode v) && isDoubleNode u
		|| not(isDoubleNode u) && isDoubleNode v in
  let k = g.num_available_registers.(u.regclass) in
  let isOK u t =
    (* avoid interfer with previous node classification *)
    if diffDeg && t.degree=k-1 && not (interfere g t u)
    then raise Exit
    else if t.nstate = Colored then
      if u.nstate = Colored || interfere g t u then () else raise Exit
    else if t.degree < k || interfere g t u then () else raise Exit
  in
  try
    iterAdjacent (isOK u) v;
    if diffDeg && isDoubleNode v then iterAdjacent (isOK v) u;
    (*printf "  George: OK for %s(%B) and %s(%B): [%B]\n" (name_of_node u) (isDoubleNode u) (name_of_node v) (isDoubleNode v) diffDeg;*)
    true
  with Exit ->
    (*i printf "  George: no\n"; *)
    false

(* The combined coalescing criterion.  [u] can be precolored, but
   [v] is not.  According to George and Appel's paper:
-  If [u] is precolored, use George's criterion.
-  If [u] is not precolored, use Briggs's criterion.

   As noted by Hailperin, for non-precolored nodes, George's criterion 
   is incomparable with Briggs's: there are cases where G says yes
   and B says no.  Typically, [u] is a long-lived variable with many 
   interferences, and [v] is a short-lived temporary copy of [u]
   that has no more interferences than [u].  Coalescing [u] and [v]
   is "weakly safe" in Hailperin's terminology: [u] is no harder to color,
   [u]'s neighbors are no harder to color either, but if we end up
   spilling [u], we'll spill [v] as well.  So, we restrict this heuristic
   to [v] having a small number of uses.
*)

let thresholdGeorge = 3

let canCoalesce g u v =
  (*i printf "canCoalesce %s[%.2f] %s[%.2f]\n"
     (name_of_node u) u.spillcost (name_of_node v) v.spillcost; *)
  if u.nstate = Colored
  then canCoalesceGeorge g u v
  else canCoalesceBriggs g u v
       || (u.spillcost < infinity && v.spillcost < infinity &&
            ((v.accesses <= thresholdGeorge && canCoalesceGeorge g u v)
             || (u.accesses <= thresholdGeorge && canCoalesceGeorge g v u)))

(* Update worklists after a move was processed *)

let addWorkList g u =
  if (not (u.nstate = Colored))
  && u.degree < g.num_available_registers.(u.regclass)
  && (not (moveRelated u))
  then DLinkNode.move u g.freezeWorklist g.simplifyWorklist

(* Return the canonical representative of a possibly coalesced node *)

let rec getAlias ni =
  let (n,noff) = ni in
  match n.alias with
  | None -> (n,noff) 
  | Some (n', None) -> getAlias (n',noff)
  | Some (n', Some b) -> assert (noff=None); getAlias (n',Some b)

(* Combine two nodes *)

let combine g dst src =
  (*printf "Combining %s with %s\n" (name_of_node_slot src) (name_of_node_slot dst);*)
  let (u,uoff) = dst
  and (v,voff) = src in
  begin match uoff, voff with
  | None, None | Some _, None -> ()
  | _, _ -> assert false
  end;
  if u.spillcost = infinity then
    printf "Warning: combining unspillable %s\n" (name_of_node u);
  if v.spillcost = infinity then
    printf "Warning: combining unspillable %s\n" (name_of_node v);
  if v.nstate = FreezeWorklist
  then DLinkNode.move v g.freezeWorklist g.coalescedNodes
  else DLinkNode.move v g.spillWorklist g.coalescedNodes;
  v.degree <- v.degree + (if not (isDoubleNode v) && isDoubleNode u then 1 else 0);
  (* Precolored nodes often have big movelists, and if one of [u] and [v]
     is precolored, it is [u].  So, append [v.movelist] to [u.movelist]
     instead of the other way around. *)
  u.movelist <- List.rev_append v.movelist u.movelist;
  u.spillcost <- u.spillcost +. v.spillcost;
  iterAdjacent (combineEdge g v u) v;  (*r original code using [decrementDegree] is buggy *)
  v.alias <- Some (u,uoff);
  degreeInvariant g v;
  if u.nstate <> Colored then begin
    u.extra_adj <- List.rev_append v.extra_adj u.extra_adj;
    u.extra_pref <- List.rev_append v.extra_pref u.extra_pref
  end;
  enableMoves g v;                   (*r added as per Appel's book erratum *)
  if u.degree >= g.num_available_registers.(u.regclass)
  && u.nstate = FreezeWorklist
  then DLinkNode.move u g.freezeWorklist g.spillWorklist


(* Attempt coalescing *)

let coalesce g =
  let m = DLinkMove.pick g.worklistMoves in
  let x = getAlias m.src and y = getAlias m.dst in
  (* orient the move so that:
       1) single-node to multi-node moves are reversed (if destination is
         pre-colored, it will be ignored, i.e. moved to constrinedMoves)
       2) pre-colored nodes are the source  *)
  let ((u, uoff), (v, voff)) = 
    match x, y with
    | (xn, None), (yn,Some _) -> (y,x)
    | _, _ -> if (fst y).nstate = Colored
	      then (y, x)
	      else (x, y) in
  degreeInvariant g u;
  degreeInvariant g v;
  let m' =
    let cmp x y = (fst x).ident = (fst y).ident && (snd x)=(snd y) in
    begin match uoff, voff with (* try to find a pairing move *)
    | (Some bu, Some bv) when bu=bv ->
(*        printf "Try to find a pairing for %s=>%s in [" (name_of_node_slot (u, Some bu)) (name_of_node_slot (v, Some bv));
	DLinkMove.iter (fun m -> printf "%s=>%s " (name_of_node_slot m.src) (name_of_node_slot m.dst)) g.worklistMoves; printf "]\n";*)
	DLinkMove.fold (fun m r -> if cmp (getAlias m.src) (u,Some(not bu))
				      && cmp (getAlias m.dst) (v,Some(not bv))
				      || cmp (getAlias m.dst) (u,Some(not bu))
					 && cmp (getAlias m.src) (v,Some(not bv))
				   then ((*printf "FOUND\n";*) Some m)
				   else r) g.worklistMoves None 
    | _, _ -> None
  end in
(*  printf "COALESCE: attempt coalescing %s and %s\n" (name_of_node_slot (u,uoff)) (name_of_node_slot (v,voff));*)
  if u == v && uoff = voff then begin
(*    printf "COALESCE: identified %s and %s\n" (name_of_node_slot (u,uoff)) (name_of_node_slot (v,voff));*)
    DLinkMove.insert m g.coalescedMoves;
    addWorkList g u
  end else if (*u==v ||*) v.nstate = Colored || interfere g u v
	      || (match uoff,voff with
		  | Some bu, Some bv -> bu<>bv | _,_ -> false)
  then begin
(*    printf "COALESCE: give up coalescing %s and %s\n" (name_of_node_slot (u,uoff)) (name_of_node_slot (v,voff));*)
(*    if v.nstate = Colored
    then Printf.printf "cause: COLORED V\n";
    if interfere g u v
    then (Printf.printf "cause: INTERERE V\n";
	  print_node u;
	  print_node v);*)
    DLinkMove.insert m g.constrainedMoves;
    begin match m' with
	  | Some mm -> DLinkMove.move mm g.worklistMoves g.activeMoves
	  | _ -> ()
    end;
    addWorkList g u;
    addWorkList g v
  end else if (voff=None || m'<>None) && canCoalesce g u v then begin
(*      printf "COALESCE: combining %s and %s\n" (name_of_node_slot (u,uoff)) (name_of_node_slot (v,voff));*)
    DLinkMove.insert m g.coalescedMoves;
    begin match m' with
	  | Some mm -> DLinkMove.move mm g.worklistMoves g.coalescedMoves
	  | _ -> ()
    end;
    combine g (u,if m'<>None then None else uoff)
	    (v,if m'<>None then None else voff);
    addWorkList g u
  end else begin
    DLinkMove.insert m g.activeMoves;
    begin match m' with
	  | Some mm -> DLinkMove.move mm g.worklistMoves g.activeMoves
	  | _ -> ()
    end
  end

(* Freeze moves associated with node [u] *)

let freezeMoves g u =
  let (u',uoff') = getAlias (u,None) in
  let freeze m =
    let (y,yoff) = getAlias m.src in
    let (v,_) = if y == u' then getAlias m.dst else (y,yoff) in
    DLinkMove.move m g.activeMoves g.frozenMoves;
    if not (moveRelated v)
    && v.degree < g.num_available_registers.(v.regclass)
    && v.nstate <> Colored
    then DLinkNode.move v g.freezeWorklist g.simplifyWorklist in
  List.iter freeze (nodeMoves u)

(* Pick a move and freeze it *)

let freeze g =
  let u = DLinkNode.pick g.freezeWorklist in
  (*printf "Freezing %s\n" (name_of_node u);*)
  degreeInvariant g u;
  DLinkNode.insert u g.simplifyWorklist;
  freezeMoves g u

(* This is the original spill cost function from Chaitin 1982 *)

(*
let spillCost n =
  n.spillcost /. float n.degree
*)

(* This is spill cost function h_0 from Bernstein et al 1989.  It performs
   slightly better than Chaitin's and than functions h_1 and h_2. *)

(*
let spillCost n =
  let deg = float n.degree in n.spillcost /. (deg *. deg)
*)

(* Spill a node *)

let selectSpill g =
  (*printf "Attempt spilling with: ";*)
  (* Find a spillable node of minimal cost *)
  let (n, cost) =
    DLinkNode.fold
      (fun n (best_node, best_cost as best) ->
        (* Manual inlining of [spillCost] above plus algebraic simplif *)
        let deg = float n.degree in
        let deg2 = deg *. deg in
(*
printf "%s(%f:%d[%d]) " (name_of_node n) n.spillcost n.degree n.regclass;
 *)
        (* if n.spillcost /. deg2 <= best_cost *)
        if n.spillcost <= best_cost *. deg2
        then (n, n.spillcost /. deg2)
        else best)
      g.spillWorklist (DLinkNode.dummy, infinity) in
(*
printf "  class=%d; avail=%d\n" n.regclass  g.num_available_registers.(n.regclass);
 *)
  assert (n != DLinkNode.dummy);
  if cost = infinity then begin
    printf "Warning: spilling unspillable %s\n" (name_of_node n);
    printf "  spill queue is:";
    DLinkNode.iter (fun n -> printf " %s" (name_of_node n)) g.spillWorklist;
    printf "\n"
  end;
  DLinkNode.remove n g.spillWorklist;
  (*printf "Spilling %s[%d%d]\n" (name_of_node n) n.regclass (if isDoubleNode n then 1 else 0);*)
  freezeMoves g n;
  n.nstate <- SelectStack;
  iterAdjacent (fun x -> decrementDegree g x; if isDoubleNode n then decrementDegree g x) n;
  n

(* Produce the order of nodes that we'll use for coloring *)

let rec nodeOrder g stack =
  checkInvariants g;
  if DLinkNode.notempty g.simplifyWorklist then
    (let n = simplify g in nodeOrder g (n :: stack))
  else if DLinkMove.notempty g.worklistMoves then
    (coalesce g; nodeOrder g stack)
  else if DLinkNode.notempty g.freezeWorklist then
    (freeze g; nodeOrder g stack)
  else if DLinkNode.notempty g.spillWorklist then
    (let n = selectSpill g in nodeOrder g (n :: stack))
  else
    stack

(* Assign a color (i.e. a hardware register or a stack location)
   to a node.  The color is chosen among the colors that are not
   assigned to nodes with which this node interferes.  The choice
   is guided by the following heuristics: consider first caller-save
   hardware register of the correct type; second, callee-save registers;
   third, a stack location.  Callee-save registers and stack locations
   are ``expensive'' resources, so we try to minimize their number
   by picking the smallest available callee-save register or stack location.
   In contrast, caller-save registers are ``free'', so we pick an
   available one pseudo-randomly. *)
(*
module Regset =
  Set.Make(struct type t = mreg let compare = compare end)
 *)
(** SIMD 
   regset is implemented as a pair of [int64], in which each hardware
 register is associated to (possibly multiple) bits.
 Adding is implemented as a bitwise or, and checking interference
 with as a bitwise and. *)
(*
let rec printridxbits n = function
  | BinNums.Coq_xH -> (printf "%d\n" n; ())
  | BinNums.Coq_xI p -> printf "%d, " n; printridxbits (n+1) p
  | BinNums.Coq_xO p -> printridxbits (n+1) p
 *)
let regset_add (rs:int64*int64) r =
  let (b,ridx) = mreg_idx r in
(*printridxbits 0 ridx;*)
  let rbitmask = P.to_int64 ridx in
  let result = ((if b then fst rs else Int64.logor (fst rs) rbitmask),
		(if b then Int64.logor (snd rs) rbitmask else snd rs)) in
(*  printf "conflicts=(%s,%s) added %s\n" (Int64.to_string (fst result)) (Int64.to_string (snd result)) (Int64.to_string rbitmask);*)
  result

let regset_interf (rs:int64*int64) r double =
  let (b,ridx) = mreg_idx r in
  let rbitmask = P.to_int64 ridx in (* obs: pode ser pré-calculado e armazenado em g.callee_save_registers.(regclass) *)
  let rbitmask = if double
		 then Int64.logor rbitmask (Int64.mul rbitmask 
						      (Int64.of_int 2))
		 else rbitmask in
  let result = if b
	       then (Int64.logand (snd rs) rbitmask) <> Int64.zero
	       else (Int64.logand (fst rs) rbitmask) <> Int64.zero in
  result

let find_reg g conflicts regclass ty double =
  let rec find avail curr last =
    let curr = if double && curr mod 2>0 then curr+1 else curr in
    if curr >= (match ty with Tsingle -> 8 | _ -> last)
    then None
    else begin
      let r = avail.(curr) in
      if regset_interf conflicts r double (* Regset.mem r conflicts*)
      then find avail (curr + 1) last
      else Some (R r)
    end in
  let caller_save =  g.caller_save_registers.(regclass)
  and callee_save = g.callee_save_registers.(regclass)
  and start = g.start_points.(regclass) in
  match find caller_save start (Array.length caller_save) with
  | Some _ as res ->
      g.start_points.(regclass) <-
        (if start + 1 < Array.length caller_save then start + 1 else 0);
      res
  | None ->
      match find caller_save 0 start with
      | Some _ as res ->
          g.start_points.(regclass) <-
            (if start + 1 < Array.length caller_save then start + 1 else 0);
          res
      | None ->
          find callee_save 0 (Array.length callee_save)

(* Aggressive coalescing of stack slots.  When assigning a slot,
   try first the slots assigned to the pseudoregs for which we
   have a preference, provided no conflict occurs. *)

let rec reuse_slot conflicts n mvlist double =
  match mvlist with
  | [] -> None
  | mv :: rem ->
      let attempt_reuse n' =
        match n'.color with
        | Some(S(Local, _, _) as l)
          when List.for_all (Loc.diff_dec l) conflicts 
	       && isDoubleNode n = isDoubleNode n' -> Some l
        | _ -> reuse_slot conflicts n rem double in
      let (src,_) = getAlias mv.src and (dst,_) = getAlias mv.dst in
      if n == src then attempt_reuse dst
      else if n == dst then attempt_reuse src
      else reuse_slot conflicts n rem double (* should not happen? *)

(* If no reuse possible, assign lowest nonconflicting stack slot. *)

let compare_slots s1 s2 =
  match s1, s2 with
  | S(_, ofs1, _), S(_, ofs2, _) -> Z.compare ofs1 ofs2
  | _, _ -> assert false

let find_slot conflicts typ double =
  let rec find curr = 
    let curr'=Coqlib.align (Memdata.align_chunk (AST.chunk_of_type typ)) curr
    in function
    | [] ->
       S(Local, curr', typ)
    | S(Local, ofs, typ') :: l ->
       if Z.le (Z.add (if double then Z.add curr' (typesize typ) else curr') (typesize typ)) ofs then
         S(Local, curr', typ)
       else 
	 begin
           let ofs' = Z.add ofs (typesize typ') in
           find (if Z.le ofs' curr then curr else ofs') l
	 end
    | _ :: l ->
       find curr l
  in find Z.zero (List.stable_sort compare_slots conflicts)

(* Record locations assigned to interfering nodes *)

let record_reg_conflict cnf n =
  let (n',_) = getAlias (n,None) in
  match n'.color with
  | Some (R r) -> let cnf' = regset_add cnf r (* Regset.add r cnf *) in
		  if isDoubleNode n'
		  then regset_add cnf' (double_pair_reg r)
		  else cnf'
  | _ -> cnf

let record_slot_conflict cnf n =
  let (n', _) = getAlias (n,None) in
  match n'.color with
  | Some (S _ as l) -> let cnf' = l :: cnf in
		       if isDoubleNode n'
		       then begin match l with
			    | S (Local, curr, Tfloat) ->
			       S(Local, Z.add curr (typesize Tfloat), Tfloat)
			       :: cnf'
			    | _ -> assert false
			    end
		       else cnf'
  | _ -> cnf

(* Assign a location, the best we can *)
let print_conflicts rc =
  let two = Int64.of_int 2 in
  let lsb x = Int64.to_int (Int64.rem x two) in
  let rec printbits n x =
    if n>0 then begin printf "%d" (lsb x);
		      printbits (n-1) (Int64.div x two)
		end in
  printf "R"; printbits 16 (fst rc);
  printf " D"; printbits 32 (snd rc);
  printf "\n"

let assign_color g n =
  let reg_conflicts =
    List.fold_left record_reg_conflict
		   (Int64.zero,Int64.zero)  (*Regset.empty*)
		   n.adjlist in
  (* First, try to assign a register *)
  match find_reg g reg_conflicts n.regclass n.typ (isDoubleNode n) with
  | Some loc ->
(*      printf "searching %s in " (if isDoubleNode n then "11" else "1 ");
      print_conflicts reg_conflicts;*)
(*
      (let (V (v,_)) = n.var in
       let vnum = P.to_int v in
       let (R x) = loc in
       let (Some rname) = Machregsaux.name_of_register x in
       if vnum = 96 then printf "ALLOC x96 in %s\n" rname);
 *)
      n.color <- Some loc
  | None ->
      printf "Searching %s for %s in " (if isDoubleNode n then "11" else "1 ") (name_of_node n);
      print_conflicts reg_conflicts;
      print_node n;
      (* Add extra conflicts for nonallocatable and preallocated stack slots *)
      let slot_conflicts =
        List.fold_left record_slot_conflict
          (List.fold_left record_slot_conflict [] n.adjlist)
            n.extra_adj in
      (* Second, try to coalesce stack slots *)
      match reuse_slot slot_conflicts n (n.extra_pref @ n.movelist) 
                       (isDoubleNode n) with
      | Some loc ->
          n.color <- Some loc
      | None ->
          (* Last, pick a Local stack slot *)
          n.color <- Some (find_slot slot_conflicts (type_of_class n.regclass) (isDoubleNode n))

(* Extract the location of a variable *)

let print_location g n noff =
  let (n',noff') = getAlias (n,noff) in
  sprintf "%s%s @ %s%s " (name_of_node n) (match noff with None -> " " | Some b -> if b then "H" else "L") (name_of_node n') (match noff' with None -> " " | Some b -> if b then "H" else "L")

let location_of_var g v =
  match v with
  | L l -> l
  | V(r, ty) ->
      try
        let (n,noff) = Hashtbl.find g.varTable v in
(*	Printf.printf "%s\n" (print_location g n noff);*)
        let (n',noff') = getAlias (n,noff) in
        match n'.color with
        | None -> assert false
        | Some l -> begin match noff', l with
		    | Some true, R mr -> R (double_pair_reg mr)
		    | Some true, S(Local, off, Tfloat) ->
		       S(Local, Z.add off (typesize Tfloat), Tfloat)
		    | Some true, _ -> assert false
		    | _, _ -> l
		    end
      with Not_found ->
        match ty with
        | Tint -> R dummy_int_reg
        | Tfloat | Tsingle -> R dummy_float_reg
        | Tlong -> assert false
        | Tvec _ -> assert false

(* The exported interface *)

let add_interf g v1 v2 =
  addEdge g (fst (nodeOfVar g v1)) (fst (nodeOfVar g v2))

let add_pref g v1 v2 =
  addMovePref g (nodeOfVar g v1) (nodeOfVar g v2)

let coloring g =
  initialNodePartition g;
  checkInvariants g;
  List.iter (assign_color g) (nodeOrder g []);
  location_of_var g  (* total function var -> location *)
