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

(* Register allocation by coloring of an interference graph *)

(* The algorithm in a nutshell:

   - Split live ranges
   - Convert from RTL to XTL
   - Eliminate dead code
   - Repeat:
       . Construct interference graph
       . Color interference graph using IRC algorithm
       . Check for variables that were spilled and must be in registers
       . If none, convert to LTL and exit.
       . If some, insert spill and reload instructions and try again
     End Repeat
*)

open Printf
open Clflags
open Camlcoq
open Datatypes
open Coqlib
open Maps
open AST
open Memdata
open Kildall
open Registers
open Op
open Machregs
open Locations
open Conventions1
open Conventions
open IRC
open XTL

open CXBuiltins
open Builtindata

let builtin_name ef = 
  match ef with
  | EF_builtin(n,_,_) -> extern_atom n
  | _ -> ""

let list_take n l =
  let rec loop n = function
    | h :: t when n > 0 ->
      h::loop (n - 1) t
    | _ -> []
  in loop n l

let list_take_drop n l =
  let rec loop n = function
    | h :: t when n > 0 -> let (a,b) = loop (n - 1) t in (h::a,b)
    | l -> ([],l)
  in loop n l

(* Detection of 2-address operations *)

let is_two_address op args =
  if two_address_op op then
    match args with
    | [] -> assert false
    | arg1 :: argl -> Some(arg1, argl)
  else None

let is_twoaddr_builtin ef args res =
  match ef with
  | EF_builtin(id,blt,s) ->
     begin match blt with
     | None -> None
     | Some bdata ->
	if bdata.blt_twoaddr
	then let (args1,argsr) = list_take_drop (List.length res) args in
	     Some (args1, argsr)
	else None
     end
(*
     begin
      try let blt = Hashtbl.find CXBuiltins.simd_builtin_functions id in
	  let (args1,argsr) = list_take_drop blt.btwoaddr args in
	  if args1<>[] then Some (args1,argsr) else None
      with Not_found -> None
     end
 *)
  | _ -> None

let destroyed_by_builtin_aux ef =
  let rec regofstr s =
    match Machregsaux.register_by_name s with
    | None -> assert false
    | Some r -> r in
  match ef with
  | EF_builtin(id,bdata,s) ->
     begin match bdata with
     | None -> destroyed_by_builtin ef
     | Some bdata -> begin match bdata.blt_destr with
		     | Some l -> List.map regofstr l
		     | _ -> []
		     end
     end
  | _ -> []

let mregs_for_builtin_aux ef =
  let rec nthreg n l =
    match l with
    | [] -> assert false
    | (x::xx) -> if n<=0 then Some x else nthreg (n-1) xx in
  let rregs = [R0;R1;R2]
  and fregs = [F0;F1;F2;F3;F4;F5;F6;F7;F8;F9] in
  let rec getregs c1 c2 l =
    match l with
    | [] -> []
    | (x::xx) -> begin match x with
		 | Tint -> (nthreg c1 rregs)::getregs (c1+1) c2 xx
		 | Tlong -> (nthreg c1 rregs)::(nthreg (c1+1) rregs)::
			      getregs (c1+2) c2 xx
		 | Tfloat -> (nthreg c2 fregs)::getregs c1 (c2+1) xx
		 | Tsingle -> (nthreg c2 fregs)::getregs c1 (c2+1) xx
		 | Tvec () -> (nthreg c2 fregs)::(nthreg (c2+1) fregs)::
				getregs c1 (c2+2) xx
		 end in
  match ef with
  | EF_builtin(id,bdata,s) ->
     begin match bdata with
	   | None -> mregs_for_builtin ef
	   | Some bdata -> begin match bdata.blt_destr with
				 | None -> ([],[])
				 | Some _ -> (getregs 0 0 s.sig_args
					     ,getregs 0 0 s.sig_res)
			   end
     end
  | _ -> ([],[])

(* For tracing *)

let destination_alloctrace : string option ref = ref None
let pp = ref stdout

let init_trace () =
  if !option_dalloctrace && !pp == stdout then begin
    match !destination_alloctrace with
    | None -> ()  (* should not happen *)
    | Some f -> pp := open_out f
  end


(**************** Initial conversion from RTL to XTL **************)

let vreg tyenv r = V(r, tyenv r)

let vregs tyenv rl = List.map (vreg tyenv) rl

let rec expand_regs tyenv = function
  | [] -> []
  | r :: rl ->
      match tyenv r with
      | Tlong -> V(r, Tint) :: V(twin_reg r, Tint) :: expand_regs tyenv rl
      | Tvec () -> V(offset_reg r 0, Tfloat) :: V(offset_reg r 1, Tfloat) :: expand_regs tyenv rl
      | ty    -> V(r, ty) :: expand_regs tyenv rl

let constrain_reg v c =
  match c with
  | None -> v
  | Some mr -> L(R mr)

let rec constrain_regs vl cl =
  match vl, cl with
  | [], _ -> []
  | v1 :: vl', [] -> vl
  | v1 :: vl', Some mr1 :: cl' -> L(R mr1) :: constrain_regs vl' cl'
  | v1 :: vl', None :: cl' -> v1 :: constrain_regs vl' cl'

let move v1 v2 k =
  if v1 = v2 then k else Xmove(v1, v2) :: k

let rec movelist vl1 vl2 k =
  match vl1, vl2 with
  | [], [] -> k
  | v1 :: vl1, v2 :: vl2 -> move v1 v2 (movelist vl1 vl2 k)
  | _, _ -> assert false

let xparmove srcs dsts k =
  (*assert (List.length srcs = List.length dsts);*)
  match srcs, dsts with
  | _, [] -> k
  | src::_, [dst] -> Xmove(src, dst) :: k
  | _, _ -> 
     assert (List.length srcs >= List.length dsts);
     Xparmove(list_take (List.length dsts) srcs, dsts, new_temp Tint, new_temp Tfloat) :: k

(* Return the XTL basic block corresponding to the given RTL instruction.
   Move and parallel move instructions are introduced to honor calling
   conventions and register constraints on some operations.
   64-bit integer variables are split in two 32-bit halves. *)

let is_move_builtin ef args res s =
  match ef with
  | EF_builtin(id,_,_) -> 
     (*printf "%s" (extern_atom id);*)
     if id = intern_string "__builtin_vget_low"
     then begin match args,res with
		| [arg], [r] -> Some [Xmove(V(offset_reg arg 0,Tfloat),
					    V(r, Tfloat))
				     ;Xbranch s]
		| _ -> assert false;
	  end
     else if id = intern_string "__builtin_vget_high"
     then begin match args,res with
		| [arg], [r] -> Some [Xmove(V(offset_reg arg 1,Tfloat),
					    V(r, Tfloat))
				     ;Xbranch s]
		| _ -> assert false;
	  end
     else if id = intern_string "__builtin_vcombine"
     then begin match args,res with
		| [arg1;arg2], [r] -> Some [Xmove(V(arg1, Tfloat),
						  V(offset_reg r 0,Tfloat))
					   ;Xmove(V(arg2, Tfloat),
						  V(offset_reg r 1,Tfloat))
					   ;Xbranch s]
		| _ -> assert false;
	  end
(*
     else if id = intern_string "__builtin_vset_low"
     then []
     else if id = intern_string "__builtin_vset_high"
     then []
 *)
     else None
  | _ -> None

let block_of_RTL_instr funsig tyenv = function
  | RTL.Inop s ->
      [Xbranch s]
  | RTL.Iop(Omove, [arg], res, s) ->
      if tyenv arg = Tlong then
        [Xmove(V(arg, Tint), V(res, Tint));
         Xmove(V(twin_reg arg, Tint), V(twin_reg res, Tint));
         Xbranch s]
      else if tyenv arg = Tvec () then
	[Xmove(V(offset_reg arg 0, Tfloat), V(offset_reg res 0, Tfloat));
	 Xmove(V(offset_reg arg 1, Tfloat), V(offset_reg res 1, Tfloat));
	 Xbranch s]
      else	
        [Xmove(vreg tyenv arg, vreg tyenv res); Xbranch s]
  | RTL.Iop(Omakelong, [arg1; arg2], res, s) ->
      [Xmove(V(arg1, Tint), V(res, Tint));
       Xmove(V(arg2, Tint), V(twin_reg res, Tint));
       Xbranch s]
  | RTL.Iop(Olowlong, [arg], res, s) ->
      [Xmove(V(twin_reg arg, Tint), V(res, Tint)); Xbranch s]
  | RTL.Iop(Ohighlong, [arg], res, s) ->
      [Xmove(V(arg, Tint), V(res, Tint)); Xbranch s]
  | RTL.Iop(op, args, res, s) ->
      let (cargs, cres) = mregs_for_operation op in
      let args1 = vregs tyenv args 
      and res1 = vreg tyenv res
      in
      let args2 = constrain_regs args1 cargs and res2 = constrain_reg res1 cres in
      let (args3, res3) =
        match is_two_address op args2 with
        | None ->
            (args2, res2)
        | Some(arg, args2') ->
            if arg = res2 || not (List.mem res2 args2') then
              (args2, res2)
            else
              let t = new_temp (tyenv res) in (t :: args2', t) in
      movelist args1 args3 (Xop(op, args3, res3) :: move res3 res1 [Xbranch s])
  | RTL.Iload(chunk, addr, args, dst, s) ->
      if chunk = Mint64 then begin
        match offset_addressing addr (coqint_of_camlint 4l) with
        | None -> assert false
        | Some addr' ->
            [Xload(Mint32, addr, vregs tyenv args,
                   V((if Archi.big_endian then dst else twin_reg dst), Tint));
             Xload(Mint32, addr', vregs tyenv args,
                   V((if Archi.big_endian then twin_reg dst else dst), Tint));
             Xbranch s]
      end else if chunk = Mvec () then begin
        match offset_addressing addr (coqint_of_camlint 8l) with
        | None -> assert false
        | Some addr' ->
            [Xload(Mfloat64, addr, vregs tyenv args,
                   V(offset_reg dst 0, Tfloat));
             Xload(Mint32, addr', vregs tyenv args,
                   V(offset_reg dst 1, Tfloat));
             Xbranch s]
      end else
        [Xload(chunk, addr, vregs tyenv args, vreg tyenv dst); Xbranch s]
  | RTL.Istore(chunk, addr, args, src, s) ->
      if chunk = Mint64 then begin
        match offset_addressing addr (coqint_of_camlint 4l) with
        | None -> assert false
        | Some addr' ->
            [Xstore(Mint32, addr, vregs tyenv args,
                   V((if Archi.big_endian then src else twin_reg src), Tint));
             Xstore(Mint32, addr', vregs tyenv args,
                   V((if Archi.big_endian then twin_reg src else src), Tint));
             Xbranch s]
      end else if chunk = Mvec () then begin
        match offset_addressing addr (coqint_of_camlint 8l) with
        | None -> assert false
        | Some addr' ->
            [Xstore(Mfloat64, addr, vregs tyenv args,
                   V(offset_reg src 0, Tfloat));
             Xstore(Mfloat64, addr', vregs tyenv args,
                   V(offset_reg src 1, Tfloat));
             Xbranch s]
      end else
        [Xstore(chunk, addr, vregs tyenv args, vreg tyenv src); Xbranch s]
  | RTL.Icall(sg, ros, args, res, s) ->
      (match (loc_result sg) with
       | Some rr -> let args' = vlocs (loc_arguments sg)
 		    and res' = vmregs rr in
 		    xparmove (expand_regs tyenv args) args'
		     (Xcall(sg, sum_left_map (vreg tyenv) ros, args', res')::
                    xparmove res' (expand_regs tyenv res) 
		     [Xbranch s])
       | _ -> assert false)
  | RTL.Itailcall(sg, ros, args) ->
      let args' = vlocs (loc_arguments sg) in
      xparmove (expand_regs tyenv args) args'
        [Xtailcall(sg, sum_left_map (vreg tyenv) ros, args')]
  | RTL.Ibuiltin(ef, args, res, s) ->
     begin
      match is_move_builtin ef args res s with
      | Some block -> block
      | _ -> let (cargs, cres) = mregs_for_builtin_aux ef in
	     let args1 = expand_regs tyenv args
	     and res1 = expand_regs tyenv res in
	     let args2 = constrain_regs args1 cargs
	     and res2 = constrain_regs res1 cres in
	     let (args3,res3) =
	       let rec gentemps res argsi argsr =
		 match res, argsi with
		 | [], [] -> (argsr,[])
		 | (r::res'), (a::argsi') ->
		    let (aa,rr) = gentemps res' argsi' argsr in
		    if r=a || not (List.mem r (argsi'@argsr))
		    then (a::aa, r::rr)
		    else let t=new_temp (typeof r) in (t::aa, t::rr)
		 | _, _ -> printf "NOT ALL RESULTS TwoAddr in builtin %s\n" (builtin_name ef); assert false
	       in match is_twoaddr_builtin ef args2 res2 with
		  | None -> (args2,res2)
		  | Some (argsi,argsr) -> 
(*		     printf "TWO_ADDR (%s: %d)\n" (builtin_name ef) (List.length argsi);*)
		     gentemps res2 argsi argsr
	     in
(*
	     printf "%s:\n" (PrintAST.name_of_external ef);
	     printf "args1= %a\n" PrintXTL.vars args1;
	     printf "args3= %a\n" PrintXTL.vars args3;
	     printf "res3= %a\n" PrintXTL.vars res3;
	     printf "res1= %a\n" PrintXTL.vars res1;
 *)
	     movelist args1 args3
		      (Xbuiltin(ef, args3, res3) ::
			 movelist res3 res1 [Xbranch s])
     end
  | RTL.Icond(cond, args, s1, s2) ->
      [Xcond(cond, vregs tyenv args, s1, s2)]
  | RTL.Ijumptable(arg, tbl) ->
      [Xjumptable(vreg tyenv arg, tbl)]
  | RTL.Ireturn [] ->
      [Xreturn []]
  | RTL.Ireturn (arg) ->
      match (loc_result funsig) with
      | Some rr -> let args' = vmregs rr in
           xparmove (expand_regs tyenv arg) args' [Xreturn args']
      | _ -> assert false
(*      let args' = vmregs (loc_result funsig) in
      xparmove (expand_regs tyenv [arg]) args' [Xreturn args']*)

(* One above the [pc] nodes of the given RTL function *)

let next_pc f =
  PTree.fold
    (fun npc pc i -> if P.lt pc npc then npc else P.succ pc)
    f.RTL.fn_code P.one

(* Translate an RTL function to an XTL function *)

let function_of_RTL_function f tyenv =
  let xc = PTree.map1 (block_of_RTL_instr f.RTL.fn_sig tyenv) f.RTL.fn_code in
  (* Add moves for function parameters *)
  let pc_entrypoint = next_pc f in
  let b_entrypoint = 
     xparmove (vlocs (loc_parameters f.RTL.fn_sig))
              (expand_regs tyenv f.RTL.fn_params)
              [Xbranch f.RTL.fn_entrypoint] in
  { fn_sig = f.RTL.fn_sig;
    fn_stacksize = f.RTL.fn_stacksize;
    fn_entrypoint = pc_entrypoint;
    fn_code = PTree.set pc_entrypoint b_entrypoint xc }


(***************** Liveness analysis *****************)

let vset_removelist vl after = List.fold_right VSet.remove vl after
let vset_addlist vl after = List.fold_right VSet.add vl after
let vset_addros vos after =
  match vos with Coq_inl v -> VSet.add v after | Coq_inr id -> after

let live_before instr after =
  match instr with
  | Xmove(src, dst) | Xspill(src, dst) | Xreload(src, dst) ->
      if VSet.mem dst after || is_stack_reg src
      then VSet.add src (VSet.remove dst after)
      else after
  | Xparmove(srcs, dsts, itmp, ftmp) ->
      vset_addlist srcs (vset_removelist dsts after)
  | Xop(op, args, res) ->
      if VSet.mem res after
      then vset_addlist args (VSet.remove res after)
      else after
  | Xload(chunk, addr, args, dst) ->
      if VSet.mem dst after
      then vset_addlist args (VSet.remove dst after)
      else after
  | Xstore(chunk, addr, args, src) ->
      vset_addlist args (VSet.add src after)
  | Xcall(sg, ros, args, res) ->
      vset_addlist args (vset_addros ros (vset_removelist res after))
  | Xtailcall(sg, ros, args) ->
      vset_addlist args (vset_addros ros VSet.empty)
  | Xbuiltin(ef, args, res) ->
      vset_addlist args (vset_removelist res after)
  | Xbranch s ->
      after
  | Xcond(cond, args, s1, s2) ->
      List.fold_right VSet.add args after
  | Xjumptable(arg, tbl) ->
      VSet.add arg after
  | Xreturn args ->
      vset_addlist args VSet.empty

let rec live_size = function
  | [] -> 0
  | x::xs when typeof x = Tfloat || typeof x = Tsingle -> 1 + live_size xs
  | _::xs -> live_size xs

let rec live_before_block blk after =
  match blk with
  | [] -> after
  | instr :: blk -> 
     let live = live_before instr (live_before_block blk after) in
(*     printf "Lsize=%d\n" (live_size (VSet.elements live));*)
     live

let transfer_live f pc after =
  match PTree.get pc f.fn_code with
  | None -> VSet.empty
  | Some blk -> live_before_block blk after

module VSetLat = struct
  type t = VSet.t
  let beq = VSet.equal
  let bot = VSet.empty
  let lub = VSet.union
end

module Liveness_Solver = Backward_Dataflow_Solver(VSetLat)(NodeSetBackward)

let liveness_analysis f =
  match Liveness_Solver.fixpoint f.fn_code successors_block (transfer_live f) with
  | None -> assert false
  | Some lv -> lv

(* Pair the instructions of a block with their live-before sets *)

let pair_block_live blk after =
  let rec pair_rec accu after = function
  | [] -> accu
  | instr :: blk ->
      let before = live_before instr after in
      pair_rec ((instr, before) :: accu) before blk in
  pair_rec [] after (List.rev blk)


(**************** Dead code elimination **********************)

(* Eliminate pure instructions whose results are not used later. *)

let rec dce_parmove srcs dsts after =
  match srcs, dsts with
  | [], [] -> [], []
  | src1 :: srcs, dst1 :: dsts ->
      let (srcs', dsts') = dce_parmove srcs dsts after in
      if VSet.mem dst1 after || is_stack_reg src1
      then (src1 :: srcs', dst1 :: dsts')
      else (srcs', dsts')
  | _, _ -> assert false

let dce_instr instr after k =
  match instr with
  | Xmove(src, dst) ->
      if VSet.mem dst after || is_stack_reg src
      then instr :: k
      else k
  | Xparmove(srcs, dsts, itmp, ftmp) ->
      begin match dce_parmove srcs dsts after with
      | ([], []) -> k
      | ([src], [dst]) -> Xmove(src, dst) :: k
      | (srcs', dsts') -> Xparmove(srcs', dsts', itmp, ftmp) :: k
      end
  | Xop(op, args, res) ->
      if VSet.mem res after
      then instr :: k
      else k
  | Xload(chunk, addr, args, dst) ->
      if VSet.mem dst after
      then instr :: k
      else k
  | _ ->
      instr :: k

let rec dce_block blk after =
  match blk with
  | [] -> (after, [])
  | instr :: blk' ->
      let (after', tblk') = dce_block blk' after in
      (live_before instr after', dce_instr instr after' tblk')

let dead_code_elimination f liveness =
  { f with fn_code =
      PTree.map (fun pc blk -> snd(dce_block blk (PMap.get pc liveness)))
                 f.fn_code }


(*********************** Spill costs ****************************)

(* Estimate spill costs and count other statistics for every variable.
   Variables that must not be spilled are given infinite costs. *)

let spill_costs f =

  let costs = ref PTree.empty in

  let get_stats r =
    match PTree.get r !costs with
    | Some st -> st
    | None ->
        let st = {cost = 0; usedefs = 0} in
        costs := PTree.set r st !costs;
        st in

  let charge amount uses v =
    match v with
    | L l -> ()
    | V(r, ty) ->
        let st = get_stats r in
        let c1 = st.cost + amount in
        let c2 = if c1 >= 0 then c1 else max_int (* overflow *) in
        st.cost <- c2;
        st.usedefs <- st.usedefs + uses in

  let charge_list amount uses vl =
    List.iter (charge amount uses) vl in

  let charge_ros amount ros =
    match ros with Coq_inl v -> charge amount 1 v | Coq_inr id -> () in

  let charge_instr = function
    | Xmove(src, dst) ->
        charge 1 1 src; charge 1 1 dst
    | Xreload(src, dst) ->
        charge 1 1 src; charge max_int 1 dst
        (* dest must not be spilled! *)
    | Xspill(src, dst) ->
        charge max_int 1 src; charge 1 1 dst
        (* source must not be spilled! *)
    | Xparmove(srcs, dsts, itmp, ftmp) ->
        charge_list 1 1 srcs; charge_list 1 1 dsts;
        charge max_int 0 itmp; charge max_int 0 ftmp
        (* temps must not be spilled *)
    | Xop(op, args, res) ->
        charge_list 10 1 args; charge 10 1 res
    | Xload(chunk, addr, args, dst) ->
        charge_list 10 1 args; charge 10 1 dst
    | Xstore(chunk, addr, args, src) ->
        charge_list 10 1 args; charge 10 1 src
    | Xcall(sg, vos, args, res) ->
        charge_ros 10 vos
    | Xtailcall(sg, vos, args) ->
        charge_ros 10 vos
    | Xbuiltin(ef, args, res) ->
        begin match ef with
        | EF_vstore _ | EF_vstore_global _ | EF_memcpy _ ->
            (* result is not used but should not be spilled *)
            charge_list 10 1 args; charge_list max_int 0 res
        | EF_annot _ ->
            (* arguments are not actually used, so don't charge;
               result is never used but should not be spilled *)
            charge_list max_int 0 res
        | EF_annot_val _ ->
            (* like a move *)
            charge_list 1 1 args; charge_list 1 1 res
        | _ ->
            charge_list 10 1 args; charge_list 10 1 res
        end
    | Xbranch _ -> ()
    | Xcond(cond, args, _, _) ->
        charge_list 10 1 args
    | Xjumptable(arg, _) ->
        charge 10 1 arg
    | Xreturn optarg ->
        () in

  let charge_block blk = List.iter charge_instr blk in

  PTree.fold1
    (fun () blk -> charge_block blk)
    f.fn_code ();
  if !option_dalloctrace then begin
    fprintf !pp "------------------ Unspillable variables --------------\n\n";
    PTree.fold
      (fun () r st ->
        if st.cost = max_int then fprintf !pp "x%d " (P.to_int r))
      !costs ();
    fprintf !pp "\n\n"
  end;
  (* Result is cost function: pseudoreg -> stats *)
  get_stats


(********* Construction and coloring of the interference graph **************)

let chkDReg v dest =
  match v, dest with
  | V(r1,_), V(r2,_) -> r1 <> r2 && r1 <> (offset_other r2)
  | x, y -> x <> y

let add_interfs_def g res live =
  VSet.iter (fun v -> if v <> res then (IRC.add_interf g v res)) live

let add_interfs_move g src dst live =
  (*printf "[%a=>%a]" PrintXTL.var src PrintXTL.var dst;*)
  VSet.iter (fun v -> if (*v <> src && v <> dst *)
		         chkDReg v src && chkDReg v dst
		      then (IRC.add_interf g v dst)) live

let add_interfs_destroyed g live mregs =
  List.iter
    (fun mr -> VSet.iter (IRC.add_interf g (L (R mr))) live)
    mregs

let add_interfs_live g live v =
  VSet.iter (fun v' -> IRC.add_interf g v v') live

let add_interfs_list g v vl =
  List.iter (IRC.add_interf g v) vl

let rec add_interfs_pairwise g = function
  | [] -> ()
  | v1 :: vl -> add_interfs_list g v1 vl; add_interfs_pairwise g vl

let add_interfs_instr g instr live =
  match instr with
  | Xmove(src, dst) | Xspill(src, dst) | Xreload(src, dst) ->
      IRC.add_pref g src dst;
      add_interfs_move g src dst live
  | Xparmove(srcs, dsts, itmp, ftmp) ->
      List.iter2 (IRC.add_pref g) srcs dsts;
      (* Interferences with live across *)
      let across = vset_removelist dsts live in
      List.iter (add_interfs_live g across) dsts;
      add_interfs_live g across itmp; add_interfs_live g across ftmp;
      (* All destinations must be pairwise different *)
      add_interfs_pairwise g dsts;
      (* The temporaries must be different from sources and dests *)
      add_interfs_list g itmp srcs; add_interfs_list g itmp dsts;
      add_interfs_list g ftmp srcs; add_interfs_list g ftmp dsts;
      (* Take into account destroyed reg when accessing Incoming param *)
      if List.exists (function (L(S(Incoming, _, _))) -> true | _ -> false) srcs
      then add_interfs_list g (vmreg temp_for_parent_frame) dsts;
      (* Take into account destroyed reg when initializing Outgoing
         arguments of type Tsingle *)
      if List.exists
           (function (L(S(Outgoing, _, Tsingle))) -> true | _ -> false) dsts
      then
        List.iter
          (fun mr ->
            add_interfs_list g (vmreg mr) srcs;
            IRC.add_interf g (vmreg mr) ftmp)
          (destroyed_by_setstack Tsingle)
  | Xop(op, args, res) ->
      begin match is_two_address op args with
      | None ->
          add_interfs_def g res live;
      | Some(arg1, argl) ->
          (* Treat as "res := arg1; res := op(res, argl)" *)
          add_interfs_def g res live;
          IRC.add_pref g arg1 res;
          add_interfs_move g arg1 res
            (vset_addlist (res :: argl) (VSet.remove res live))
      end;
      add_interfs_destroyed g (VSet.remove res live) (destroyed_by_op op);
  | Xload(chunk, addr, args, dst) ->
      add_interfs_def g dst live;
      add_interfs_destroyed g (VSet.remove dst live) 
                              (destroyed_by_load chunk addr)
  | Xstore(chunk, addr, args, src) ->
      add_interfs_destroyed g live (destroyed_by_store chunk addr)
  | Xcall(sg, vos, args, res) ->
      add_interfs_destroyed g (vset_removelist res live) destroyed_at_call
  | Xtailcall(sg, Coq_inl v, args) ->
      List.iter (fun r -> IRC.add_interf g (vmreg r) v) int_callee_save_regs
  | Xtailcall(sg, Coq_inr id, args) ->
      ()
  | Xbuiltin(ef, args, res) ->
      (* Interferences with live across *)
      let across = vset_removelist res live in
      List.iter (add_interfs_live g across) res;
      (* All results must be pairwise different *)
      add_interfs_pairwise g res;
      add_interfs_destroyed g across (destroyed_by_builtin_aux ef);
      begin match is_twoaddr_builtin ef args res with
	    | None -> begin match ef, args, res with
			    | EF_annot_val _, [arg], [res] ->
			       IRC.add_pref g arg res (* like a move *)
			    | _ -> ()
		      end
	    | Some (argsi,argsr) ->
	       let rec f args res =
		 match args, res with
		 | [], [] -> ()
		 | (a::aa), (r::rr) -> IRC.add_pref g a r;
				       add_interfs_move g a r
					 (vset_addlist (rr@aa@argsr) live);
				       f aa rr
		 | _, _ -> assert false
	       in f argsi res
      end
  | Xbranch s ->
      ()
  | Xcond(cond, args, s1, s2) ->
      add_interfs_destroyed g live (destroyed_by_cond cond)
  | Xjumptable(arg, tbl) ->
      add_interfs_destroyed g live destroyed_by_jumptable
  | Xreturn optarg ->
      ()

let rec add_interfs_block g blk live =
  match blk with
  | [] -> live
  | instr :: blk' ->
      let live' = add_interfs_block g blk' live in
      add_interfs_instr g instr live';
      live_before instr live'

let find_coloring f liveness =
  (*type_function f;  (* for debugging *)*)
  let g = IRC.init (spill_costs f) in
  PTree.fold
    (fun () pc blk -> ignore (add_interfs_block g blk (PMap.get pc liveness)))
    f.fn_code ();
  add_interfs_destroyed g
    (transfer_live f f.fn_entrypoint (PMap.get f.fn_entrypoint liveness))
    destroyed_at_function_entry;
  IRC.coloring g


(*********** Determination of variables that need spill code insertion *****)

let is_reg alloc v =
  match alloc v with R _ -> true | S _ -> false

let add_tospill alloc v ts =
  match alloc v with R _ -> ts | S _ -> VSet.add v ts

let addlist_tospill alloc vl ts =
  List.fold_right (add_tospill alloc) vl ts

let addros_tospill alloc ros ts =
  match ros with Coq_inl v -> add_tospill alloc v ts | Coq_inr s -> ts

let tospill_instr alloc instr ts =
  match instr with
  | Xmove(src, dst) ->
      if is_reg alloc src || is_reg alloc dst || alloc src = alloc dst
      then ts
      else VSet.add src (VSet.add dst ts)
  | Xreload(src, dst) ->
(*      assert (is_reg alloc dst);*)
      assert (is_reg alloc dst);
      ts
  | Xspill(src, dst) ->
(*      assert (is_reg alloc src);*)
      assert (is_reg alloc src);
      ts
  | Xparmove(srcs, dsts, itmp, ftmp) ->
      assert (is_reg alloc itmp && is_reg alloc ftmp);
      ts
  | Xop(op, args, res) ->
      addlist_tospill alloc args (add_tospill alloc res ts)
  | Xload(chunk, addr, args, dst) ->
      addlist_tospill alloc args (add_tospill alloc dst ts)
  | Xstore(chunk, addr, args, src) ->
      addlist_tospill alloc args (add_tospill alloc src ts)
  | Xcall(sg, vos, args, res) ->
      addros_tospill alloc vos ts
  | Xtailcall(sg, vos, args) ->
      addros_tospill alloc vos ts
  | Xbuiltin(ef, args, res) ->
      begin match ef with
      | EF_annot _ -> ts
      |      _     -> addlist_tospill alloc args (addlist_tospill alloc res ts)
      end
  | Xbranch s ->
      ts
  | Xcond(cond, args, s1, s2) ->
      addlist_tospill alloc args ts
  | Xjumptable(arg, tbl) ->
      add_tospill alloc arg ts
  | Xreturn optarg ->
      ts

let rec tospill_block alloc blk ts =
  match blk with
  | [] -> ts
  | instr :: blk' -> tospill_block alloc blk' (tospill_instr alloc instr ts)

let tospill_function f alloc =
  PTree.fold1
    (fun ts blk -> tospill_block alloc blk ts)
    f.fn_code VSet.empty


(********************* Spilling ***********************)

(* We follow a semi-naive spilling strategy.  By default, we spill at
  every definition of a variable that could not be allocated a register,
  and we reload before every use.  However, we also maintain a list of
  equations of the form [spilled-var = temp] that keep track of
  variables that were recently spilled or reloaded.  Based on these
  equations, we can avoid reloading a spilled variable if its value
  is still available in a temporary register. *)

let rec find_reg_containing v = function
  | [] -> None
  | (var, temp, date) :: eqs ->
      if var = v then Some temp else find_reg_containing v eqs

let add v t eqs = (v, t, 0) :: eqs

let kill x eqs =
  List.filter (fun (v, t, date) -> v <> x && t <> x) eqs
  
let reload_var tospill eqs v =
  if not (VSet.mem v tospill) then
    (v, [], eqs)
  else
    match find_reg_containing v eqs with
    | Some t ->
        (*printf "Reusing %a for %a@ @." PrintXTL.var t PrintXTL.var v;*)
        (t, [], eqs)
    | None ->
        let t = new_temp (typeof v) in 
	(t, [Xreload(v, t)], add v t eqs)

let rec reload_vars tospill eqs vl =
  match vl with
  | [] -> ([], [], eqs)
  | v1 :: vs ->
      let (t1, c1, eqs1) = reload_var tospill eqs v1 in
      let (ts, cs, eqs2) = reload_vars tospill eqs1 vs in
      (t1 :: ts, c1 @ cs, eqs2)

let save_var tospill eqs v =
  if not (VSet.mem v tospill) then
    (v, [], kill v eqs)
  else begin
    let t = new_temp (typeof v) in
    (t, [Xspill(t, v)], add v t (kill v eqs))
  end

let rec save_vars tospill eqs vl =
  match vl with
  | [] -> ([], [], eqs)
  | v1 :: vs ->
      let (t1, c1, eqs1) = save_var tospill eqs v1 in
      let (ts, cs, eqs2) = save_vars tospill eqs1 vs in
      (t1 :: ts, c1 @ cs, eqs2)

(* Trimming equations when we have too many or when they are too old.
   The goal is to limit the live range of unspillable temporaries.
   By setting [max_age] to zero, we can effectively deactivate
   the reuse strategy and fall back to a naive "reload at every use"
   strategy. *)

let max_age = ref 0
let max_num_eqs = ref 3

let rec trim count eqs =
  if count <= 0 then [] else
    match eqs with
    | [] -> []
    | (v, t, date) :: eqs' -> 
        if date <= !max_age
        then (v, t, date + 1) :: trim (count - 1) eqs'
        else []

(* Insertion of spill and reload instructions. *)

let spill_instr tospill eqs instr =
  let eqs = trim !max_num_eqs eqs in
  match instr with
  | Xmove(src, dst) ->
      if VSet.mem src tospill && VSet.mem dst tospill then begin
        let (src', c1, eqs1) = reload_var tospill eqs src in
        (c1 @ [Xspill(src', dst)], add dst src' (kill dst eqs1))
      end else begin
        ([instr], kill dst eqs)
      end
  | Xreload(src, dst) ->
      assert false
  | Xspill(src, dst) ->
      assert false
  | Xparmove(srcs, dsts, itmp, ftmp) ->
      ([instr], List.fold_right kill dsts eqs)
  | Xop(op, args, res) ->
      begin match is_two_address op args with
      | None ->
          let (args', c1, eqs1) = reload_vars tospill eqs args in
          let (res', c2, eqs2) = save_var tospill eqs1 res in
          (c1 @ Xop(op, args', res') :: c2, eqs2)
      | Some(arg1, argl) ->
          begin match VSet.mem res tospill, VSet.mem arg1 tospill with
          | false, false ->
              let (argl', c1, eqs1) = reload_vars tospill eqs argl in
              (c1 @ [Xop(op, arg1 :: argl', res)], kill res eqs1)
          | true, false ->
              let tmp = new_temp (typeof res) in
              let (argl', c1, eqs1) = reload_vars tospill eqs argl in
              (c1 @ [Xmove(arg1, tmp); Xop(op, tmp :: argl', tmp); Xspill(tmp, res)], 
               add res tmp (kill res eqs1))
          | false, true ->
              let eqs1 = add arg1 res (kill res eqs) in
              let (argl', c1, eqs2) = reload_vars tospill eqs1 argl in
              (Xreload(arg1, res) :: c1 @ [Xop(op, res :: argl', res)],
               kill res eqs2)
          | true, true ->
              let tmp = new_temp (typeof res) in              
              let eqs1 = add arg1 tmp eqs in
              let (argl', c1, eqs2) = reload_vars tospill eqs1 argl in
              (Xreload(arg1, tmp) :: c1 @ [Xop(op, tmp :: argl', tmp); Xspill(tmp, res)],
               add res tmp (kill tmp (kill res eqs2)))
          end
      end          
  | Xload(chunk, addr, args, dst) ->
      let (args', c1, eqs1) = reload_vars tospill eqs args in
      let (dst', c2, eqs2) = save_var tospill eqs1 dst in
      (c1 @ Xload(chunk, addr, args', dst') :: c2, eqs2)
  | Xstore(chunk, addr, args, src) ->
      let (args', c1, eqs1) = reload_vars tospill eqs args in
      let (src', c2, eqs2) = reload_var tospill eqs1 src in
      (c1 @ c2 @ [Xstore(chunk, addr, args', src')], eqs2)
  | Xcall(sg, Coq_inl v, args, res) ->
      let (v', c1, eqs1) = reload_var tospill eqs v in
      (c1 @ [Xcall(sg, Coq_inl v', args, res)], [])
  | Xcall(sg, Coq_inr id, args, res) ->
      ([instr], [])
  | Xtailcall(sg, Coq_inl v, args) ->
      let (v', c1, eqs1) = reload_var tospill eqs v in
      (c1 @ [Xtailcall(sg, Coq_inl v', args)], [])
  | Xtailcall(sg, Coq_inr id, args) ->
      ([instr], [])
  | Xbuiltin(ef, args, res) ->
      begin match is_twoaddr_builtin ef args res with
      | None -> begin match ef with
                | EF_annot _ ->
		   ([instr], eqs)
		| _ ->
		   let (args', c1, eqs1) = reload_vars tospill eqs args in
		   let (res', c2, eqs2) = save_vars tospill eqs1 res in
		   (c1 @ Xbuiltin(ef, args', res') :: c2, eqs2)
		end
      | Some (argsi,argsr) ->
(*	 printf "Spilling on twoaddr: %s\n" (builtin_name ef);*)
	 let rec freload args res eqs =
	   match args, res with
	   | [], [] -> (reload_vars tospill eqs argsr, [], [])
	   | (a::aa), (r::rr) ->
	      let r' = if VSet.mem r tospill
		      then new_temp (typeof r)
		      else r in
	      let eqs = if VSet.mem a tospill
			then add a r' (kill r' eqs)
			else eqs in
	      let a' = if VSet.mem a tospill || VSet.mem r tospill
		       then r'
		       else a in
	      let ((args', c', eqs'),res', s') = freload aa rr eqs in
	      (a'::args',
	       (if VSet.mem a tospill
		then Xreload(a,r')::c'
		else c'),
	       let eqs1 = kill r' (kill r eqs) in
	       if VSet.mem a tospill then add r r' eqs1 else eqs1
	      ),
	      r'::res',
	      (if VSet.mem r tospill
	       then s'@[Xspill(r',r)]
	       else s')
	   | _, _ -> assert false
	 in let ((args',c',eqs'),res',s') = freload argsi res eqs
	    in (c'@(Xbuiltin(ef,args',res')::s'), eqs')
      end
  | Xbranch s ->
      ([instr], eqs)
  | Xcond(cond, args, s1, s2) ->
     let (args', c1, eqs1) = reload_vars tospill eqs args in
     (c1 @ [Xcond(cond, args', s1, s2)], eqs1)
  | Xjumptable(arg, tbl) ->
      let (arg', c1, eqs1) = reload_var tospill eqs arg in
      (c1 @ [Xjumptable(arg', tbl)], eqs1)
  | Xreturn optarg ->
      ([instr], [])

let rec spill_block tospill pc blk eqs =
  match blk with
  | [] -> ([], eqs)
  | instr :: blk' ->
      let (c1, eqs1) = spill_instr tospill eqs instr in
      let (c2, eqs2) = spill_block tospill pc blk' eqs1 in
      (c1 @ c2, eqs2)

(*
let spill_block tospill pc blk eqs =
  printf "@[<hov 2>spill_block: at %ld: " (camlint_of_positive pc);
  List.iter (fun (x,y,d) -> printf "@ %a=%a" PrintXTL.var x PrintXTL.var y) eqs;
  printf "@]@.";
  spill_block tospill pc blk eqs
*)

let spill_function f tospill round =
  max_num_eqs := 3;
  max_age := (if round <= 10 then 3 else if round <= 20 then 1 else 0);
  transform_basic_blocks (spill_block tospill) [] f


(***************** Generation of LTL from XTL ***********************)

(** Apply a register allocation to an XTL function, producing an LTL function.
  Raise [Bad_LTL] if some pseudoregisters were mapped to stack locations
  while machine registers were expected, or in other words if spilling
  and reloading code must be inserted. *)

exception Bad_LTL

let mreg_of alloc v = match alloc v with R mr -> mr | S _ -> raise Bad_LTL

let mregs_of alloc vl = List.map (mreg_of alloc) vl

let mros_of alloc vos = sum_left_map (mreg_of alloc) vos

let make_move src dst k =
  match src, dst with
  | R rsrc, R rdst ->
      if rsrc = rdst then k else LTL.Lop(Omove, [rsrc], rdst) :: k
  | R rsrc, S(sl, ofs, ty) ->
      LTL.Lsetstack(rsrc, sl, ofs, ty) :: k
  | S(sl, ofs, ty), R rdst ->
      LTL.Lgetstack(sl, ofs, ty, rdst) :: k
  | S _, S _ ->
      if src = dst then k else raise Bad_LTL

type parmove_status = To_move | Being_moved | Moved

let make_parmove srcs dsts itmp ftmp k =
  let src = Array.of_list srcs
  and dst = Array.of_list dsts in
  let n = Array.length src in
  assert (Array.length dst = n);
  let status = Array.make n To_move in
  let temp_for = function 
    | Tint -> itmp
    | (Tfloat|Tsingle) -> ftmp 
    | Tlong | Tvec () -> assert false in
  let code = ref [] in
  let add_move s d =
    match s, d with
    | R rs, R rd ->
        code := LTL.Lop(Omove, [rs], rd) :: !code
    | R rs, S(sl, ofs, ty) ->
        code := LTL.Lsetstack(rs, sl, ofs, ty) :: !code
    | S(sl, ofs, ty), R rd ->
        code := LTL.Lgetstack(sl, ofs, ty, rd) :: !code
    | S(sls, ofss, tys), S(sld, ofsd, tyd) ->
        let tmp = temp_for tys in
        (* code will be reversed at the end *)
        code := LTL.Lsetstack(tmp, sld, ofsd, tyd) ::
                LTL.Lgetstack(sls, ofss, tys, tmp) :: !code
    in
  let rec move_one i =
    if src.(i) <> dst.(i) then begin
      status.(i) <- Being_moved;
      for j = 0 to n - 1 do
        if src.(j) = dst.(i) then
          match status.(j) with
          | To_move ->
              move_one j
          | Being_moved ->
              let tmp = R (temp_for (Loc.coq_type src.(j))) in
              add_move src.(j) tmp;
              src.(j) <- tmp
          | Moved ->
              ()
      done;
      add_move src.(i) dst.(i);
      status.(i) <- Moved
    end in
  for i = 0 to n - 1 do
    if status.(i) = To_move then move_one i
  done;
  List.rev_append !code k

let transl_instr alloc instr k =
  match instr with
  | Xmove(src, dst) | Xreload(src, dst) | Xspill(src, dst) ->
      make_move (alloc src) (alloc dst) k
  | Xparmove(srcs, dsts, itmp, ftmp) ->
      make_parmove (List.map alloc srcs) (List.map alloc dsts)
                   (mreg_of alloc itmp) (mreg_of alloc ftmp) k
  | Xop(op, args, res) ->
      let rargs = mregs_of alloc args
      and rres  = mreg_of alloc res in
      begin match is_two_address op rargs with
      | None ->
          LTL.Lop(op, rargs, rres) :: k
      | Some(rarg1, rargl) ->
          if rarg1 = rres then
            LTL.Lop(op, rargs, rres) :: k
          else
            LTL.Lop(Omove, [rarg1], rres) :: 
            LTL.Lop(op, rres :: rargl, rres) :: k
      end
  | Xload(chunk, addr, args, dst) ->
      LTL.Lload(chunk, addr, mregs_of alloc args, mreg_of alloc dst) :: k
  | Xstore(chunk, addr, args, src) ->
      LTL.Lstore(chunk, addr, mregs_of alloc args, mreg_of alloc src) :: k
  | Xcall(sg, vos, args, res) ->
      LTL.Lcall(sg, mros_of alloc vos) :: k
  | Xtailcall(sg, vos, args) ->
      LTL.Ltailcall(sg, mros_of alloc vos) :: []
  | Xbuiltin(ef, args, res) ->
     begin match ef with
     | EF_annot _ ->
	LTL.Lannot(ef, List.map alloc args) :: k
     | _ -> let rargs = mregs_of alloc args
	    and rres  = mregs_of alloc res in
	    begin match is_twoaddr_builtin ef rargs res with
	    | None -> 
	       LTL.Lbuiltin(ef, rargs, rres) :: k
	    | Some(argsi,argsr) ->
	       let rec f args res =
		 match args, res with
		 | [], [] -> LTL.Lbuiltin(ef, rres@argsr, rres) :: k
		 | (a::aa), (r::rr) -> if a=r
				      then f aa rr
				      else LTL.Lop(Omove, [a], r) :: f aa rr
		 | _, _ -> assert false
	       in f argsi rres
	    end
     end
  | Xbranch s ->
      LTL.Lbranch s :: []
  | Xcond(cond, args, s1, s2) ->
      LTL.Lcond(cond, mregs_of alloc args, s1, s2) :: []
  | Xjumptable(arg, tbl) ->
      LTL.Ljumptable(mreg_of alloc arg, tbl) :: []
  | Xreturn optarg ->
      LTL.Lreturn :: []

let rec transl_block alloc blk =
  match blk with
  | [] -> []
  | instr :: blk' -> transl_instr alloc instr (transl_block alloc blk')

let transl_function fn alloc =
  { LTL.fn_sig = fn.fn_sig;
    LTL.fn_stacksize = fn.fn_stacksize;
    LTL.fn_entrypoint = fn.fn_entrypoint;
    LTL.fn_code = PTree.map1 (transl_block alloc) fn.fn_code 
  }


(******************* All together *********************)

exception Timeout

let rec first_round f liveness =
  if !option_dalloctrace then begin
    with_debug_string (fun s->
      let pp = open_out (s^".alloc.in0") in
      PrintXTL.print_function pp f;
      close_out pp;
      let pp = open_out (s^".alloc.live0") in
      PrintXTL.print_function pp ~live:liveness f;
      close_out pp)
  end;
  let alloc = find_coloring f liveness in
  let ts = tospill_function f alloc in
  if !option_dalloctrace then begin
    with_debug_string (fun s->
      let pp = open_out (s^".alloc.out0") in
      PrintXTL.print_function pp ~alloc:alloc f;
      fprintf pp "\nUnallocated: ";
      VSet.iter (fun v -> fprintf pp "%a "
				  PrintXTL.var v) ts;
      fprintf pp "\n";
      close_out pp)
  end;
  if !option_dalloctrace then begin
    fprintf !pp "--- Remain to be spilled:\n";
    VSet.iter (fun v -> fprintf !pp "%a " PrintXTL.var v) ts;
    fprintf !pp "\n\n"
  end;      
  if VSet.is_empty ts then success f alloc else more_rounds f ts 1

and more_rounds f ts count =
  if count >= 40 then raise Timeout;
  let f' = spill_function f ts count in
  let liveness = liveness_analysis f' in
  if !option_dalloctrace then begin
    with_debug_string (fun s->
      let pp = open_out (s^".alloc.in"
			 ^string_of_int count) in
      PrintXTL.print_function pp f';
      close_out pp;
      let pp = open_out (s^".alloc.live"
			 ^string_of_int count) in
      PrintXTL.print_function pp ~live:liveness f';
      close_out pp)
  end;
  if !option_dalloctrace then begin
    fprintf !pp "-------------- After insertion of spill code (round %d)\n\n" count;
    PrintXTL.print_function !pp ~live: liveness f'
  end;
  let alloc = find_coloring f' liveness in
  if !option_dalloctrace then begin
    fprintf !pp "-------------- After register allocation (round %d)\n\n" count;
    PrintXTL.print_function !pp ~alloc: alloc ~live: liveness f'
  end;
  let ts' = tospill_function f' alloc in
  if !option_dalloctrace then begin
    with_debug_string (fun s->
      let pp = open_out (s^".alloc.out"^string_of_int count) in
      PrintXTL.print_function pp ~alloc:alloc f;
      fprintf pp "\nUnallocated: ";
      VSet.iter (fun v -> fprintf pp "%a "
				  PrintXTL.var v) ts;
      fprintf pp "\n";
      close_out pp)
  end;
  if VSet.is_empty ts'
  then success f' alloc
  else begin
    if !option_dalloctrace then begin
      fprintf !pp "--- Remain to be spilled:\n";
      VSet.iter (fun v -> fprintf !pp "%a " PrintXTL.var v) ts';
      fprintf !pp "\n\n"
    end;      
    more_rounds f (VSet.union ts ts') (count + 1)
  end

and success f alloc =
  let f' = transl_function f alloc in
  if !option_dalloctrace then begin
    fprintf !pp "-------------- Candidate allocation\n\n";
    PrintLTL.print_function !pp P.one f'
  end;
  f'

open Errors

let regalloc f =
  init_trace();
  reset_temps();
  let f1 = Splitting.rename_function f in
  (*
  if !option_dalloctrace then begin
    with_debug_string (fun s-> 
      printf "======= PROCESSING %s ====== \n" s)
  end;
  *)
  match RTLtyping.type_function f1 with
  | Error msg ->
      Error(MSG (coqstring_of_camlstring "RTL code after splitting is ill-typed:") :: msg)
  | OK tyenv ->
      let f2 = function_of_RTL_function f1 tyenv in
      let liveness = liveness_analysis f2 in
      let f3 = dead_code_elimination f2 liveness in
      if !option_dalloctrace then begin
        with_debug_string (fun s-> 
         fprintf !pp "======= PROCESSING %s ====== \n" s);
        fprintf !pp "-------------- Pre-Initial XTL\n\n";
        PrintXTL.print_function !pp f2;
        fprintf !pp "-------------- Initial XTL\n\n";
        PrintXTL.print_function !pp f3
      end;
      try
        OK(first_round f3 liveness)
      with
      | Timeout ->
          Error(msg (coqstring_of_camlstring "Spilling fails to converge"))
      | Type_error_at pc ->
          Error [MSG(coqstring_of_camlstring "Ill-typed XTL code at PC "); 
                 POS pc]
      | Bad_LTL ->
          Error(msg (coqstring_of_camlstring "Bad LTL after spilling"))
