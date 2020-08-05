open Camlcoq
open Datatypes
open Maps
open AST
open Machregs
open MachIR
open AdomLib
open BourdoncleIterator
open MIRcfg
open MemDom
open LoopUnrolling

type 'a error = OK of 'a | Error of string

let obind f = function
  | Error _ as e -> e
  | OK x -> f x

let (>>=) m f = obind f m

let eoo msg = function
  | None -> Error msg
  | Some a -> OK a

let resolve_function ff =
  function
  | Coq_inl _ -> Error "function pointer"
  | Coq_inr s -> let s = P.to_int s in ff s >>= fun m -> OK (s, m)

type callsite = int * int
type context = callsite list
type callgraph_node = context * int

module CC = struct type t = callgraph_node let compare = compare end
module M = Map.Make(CC)

let string_of_context cc =
  "[" ^ String.concat "::" (List.rev_map (fun (s, pc) -> Printf.sprintf "%s_%d" (extern_atom (P.of_int s)) pc) cc) ^ "]"

let bdom_of_adom (ff: _) (iter: _) (ctxt: context) (curr: int) (init: 'a partition toplift) (pdom: 'a tpmd)
  : ('a partition toplift, label) adom =
  let dom = pdom.tp_md in
  {
    order = botlift_leb dom.wl.wl_order;
    join = botlift_combine dom.wl.wl_join;
    widen = botlift_combine dom.wl.wl_widen;
    to_string = (fun a -> Camlcoq.camlstring_of_coqstring (dom.wl.wl_to_string a));
    init = (fun () -> NotBot init);
    transfer = (fun pc -> function
      | Nop -> botret
      | Annot (a, ar) ->
        begin match a, ar with
          | "unroll", [AA_int n] -> (function All -> NotBot All | Just x -> reduce_partition (pdom.tp_generate n x))
          | "eol", [AA_int n] -> (function All -> NotBot All | Just x -> reduce_partition (pdom.tp_merge n x))
          | _, _ -> botret
        end
      | Assert a -> dom.aassume a
      | Assign (e, d) -> dom.aassign d e
      | Store (c, ad, ar, s) -> dom.astore s c ad ar
      | Builtin (ef, ar, d) -> dom.abuiltin d ef ar
      | Call (sg, ros) ->
        begin fun m ->
          match resolve_function ff ros with
          | Error e -> failwith e
          | OK (_, External ef) -> dom.asyscall ef m
          | OK (s, Internal fn) ->
            botbind
              (iter ((curr, pc) :: ctxt) s fn)
              (dom.acall m)
        end
      );
  }

let fold_ret (m: instruction PTree.t) cb_ret cb_tc =
  PTree.fold (fun a k i ->
      match i with
      | MIreturn -> cb_ret (int_of_point k) a
      | MItailcall (sg, ros) -> cb_tc (int_of_point k) sg ros a
      | _ -> a
    ) m

let analyze_function (ff: int -> fundef error) (adom: 'a tpmd)
    (curr: int) (fn: coq_function) (init: _ botlift) : _ botlift array M.t * _ botlift =
  let result = ref M.empty in
  let rec loop ctxt curr fn init =
    let cfg = cfg_of_function fn in
    let str = get_bourdoncle cfg in
    (*
    Printf.eprintf "Analysis of function %s (%d) in context %s from state %s with strategy:\n\t%s.\n" (extern_atom (P.of_int curr)) curr (string_of_context ctxt)
      (Camlcoq.camlstring_of_coqstring (adom.wl.wl_to_string init))
      (string_of_bourdoncle_list str);
    *)
    let bdom = bdom_of_adom ff loop ctxt curr init adom in
    let fix = run_with_bourdoncle bdom str cfg in
    result := M.add (ctxt, curr) fix !result;
    fold_ret fn.fn_code (fun i -> botlift_combine adom.tp_md.wl.wl_join (botbind adom.tp_md.areturn fix.(i))) (fun _ _ _ _ -> failwith "Tail call") Bot
  in
  let post = botbind (loop [] curr fn) init in
  !result, post

let analyze_program (p: program) (dom: 'a tpmd) =
  let defs = List.fold_left (fun r (n, d) -> match d with Gfun f -> (P.to_int n, f) :: r | Gvar _ -> r) [] (prog_defs p) in
  let find_function (f: int) = try OK (List.assoc f defs) with _ -> Error ("Not a function: " ^ (extern_atom (P.of_int f))) in
  let main = P.to_int (prog_main p) in
  find_function main >>= function
  | External _ -> Error "main is external"
  | Internal mainf -> OK begin
      let d = botbind dom.tp_md.acall (dom.tp_md.init (prog_defs p)) in
      analyze_function find_function dom main mainf d
    end
