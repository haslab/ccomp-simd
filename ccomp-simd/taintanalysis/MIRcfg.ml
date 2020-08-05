open Datatypes
open Maps
open AST
open Globalenvs
open Camlcoq
open Mach
open Machregs
open Expr
open MachIR
open BourdoncleIterator

let cons x y = x :: y
let id x = x

type label =
  | Call of signature * (mreg, ident) sum
  | Assert of assertion
  | Assign of expr * mreg
  | Store of memory_chunk * Op.addressing * mreg list * mreg
  | Builtin of external_function * mreg list * mreg list
  | Annot of string * annot_arg list
  | Nop

let int_of_point (p: node) : int =
  P.to_int p - 2

let edges_of_instruction =
  let f = int_of_point in
  function
  | MIgetparam (ofs, ty, dst, s) -> cons (f s, Assign (EGetParam (ofs, ty), dst))
  | MIop (op, args, dst, s) -> cons (f s, Assign (EOp (op, args), dst))
  | MIload (c, addr, args, dst, s) -> cons (f s, Assign (ELoad (c, addr, args), dst))
  | MIstore (c, addr, args, src, s) -> cons (f s, Store (c, addr, args, src))
  | MIannot (EF_annot (a, args), _, s) -> cons (f s, Annot (extern_atom a, args))
  | MIannot (_, _, s)
  | MIgoto s
    -> cons (f s, Nop)
  | MIbuiltin (ef, args, res, s) -> cons (f s, Builtin (ef, args, res))
  | MIcall (sg, ros, s) -> cons (f s, Call (sg, ros))
  | MIcond (cnd, args, th, el) ->
    (fun m -> (f th, Assert (AssertBool (cnd, args, true))) :: (f el, Assert (AssertBool (cnd, args, false))) :: m)
  | MIjumptable (n, dst) ->
    (fun m ->
       List.fold_left (fun (m, i) d ->
           (f d, Assert (AssertNat (n, Z.of_uint i))) :: m, i + 1
         ) (m, 0) dst |> fst
    )
  | MItailcall _
  | MIreturn
    -> id

let cfg_of_function (f: coq_function) : label cfg =
  let size = P.to_int f.fn_entrypoint - 1 in
  let succ = Array.make size [] in
  PTree.fold (fun () k i ->
      let pc = int_of_point k in
      let e = edges_of_instruction i in
      succ.(pc) <- e succ.(pc)
    ) f.fn_code ();
  { entry = size - 1; succ }

let dump_cfg oc name cfg pp_edge : unit =
  let open Printf in
  let p oc = fprintf oc "%s_%d" name in
  fprintf oc "subgraph cluster_%s {\nlabel=\"%s\"\n\n" name name;
  (* Nodes *)
  Array.iteri (fun i _ ->
      fprintf oc "%a[label=\"%d\"%s]\n" p i i
        (if i = cfg.entry then ";fillcolor=red;style=filled" else "")
    ) cfg.succ;
  (* Edges *)
  Array.iteri (fun i ->
      List.iter (fun (s, e) ->
          fprintf oc "%a -> %a[label=\"%a\"]\n" p i p s pp_edge e)
    ) cfg.succ;
  fprintf oc "}\n"

let pp_ros oc =
  let open Printf in
  function
  | Coq_inl r -> PrintMach.reg oc r
  | Coq_inr s -> fprintf oc "%s" (extern_atom s)

let pp_bool oc =
  let open Printf in
  function
  | true -> fprintf oc "true"
  | false -> fprintf oc "false"

let pp_assertion oc =
  let open Printf in
  function
  | AssertBool (cnd, args, b) ->
    fprintf oc "assert %a is %a"
    (PrintOp.print_condition PrintMach.reg) (cnd, args) pp_bool b
  | AssertNat (n, v) ->
    fprintf oc "assert %a = %d"
      PrintMach.reg n (Z.to_int v)

let pp_expr oc =
  let open Printf in
  function
  | EGetParam (ofs, ty) -> fprintf oc "GetParam[%s](%d)" (PrintAST.name_of_type ty) (Z.to_int ofs)
  | EOp (op, args) -> PrintOp.print_operation PrintMach.reg oc (op, args)
  | ELoad (c, addr, args) -> fprintf oc "%s[%a]" (PrintAST.name_of_chunk c) (PrintOp.print_addressing PrintMach.reg) (addr, args)

let pp_annot_arg oc =
  let open Printf in
  function
  | AA_arg ty -> fprintf oc "%s" (PrintAST.name_of_type ty)
  | AA_int n -> fprintf oc "%d" (Z.to_int n)
  | AA_float f -> fprintf oc "%f" (camlfloat_of_coqfloat f)

let annot_args oc =
  function
  | [] -> ()
  | [ a ] -> pp_annot_arg oc a
  | x :: r -> pp_annot_arg oc x; List.iter (Printf.fprintf oc ", %a" pp_annot_arg) r

let pp_label oc =
  let open Printf in
  function
  | Call (sg, ros) -> fprintf oc "call %a" pp_ros ros
  | Assert a -> pp_assertion oc a
  | Assign (a, dst) -> fprintf oc "%a ← %a" PrintMach.reg dst pp_expr a
  | Store (c, addr, args, src) -> fprintf oc "%s[%a] := %a"
                                    (PrintAST.name_of_chunk c) (PrintOp.print_addressing PrintMach.reg)
                                    (addr, args) PrintMach.reg src
  | Builtin (ef, args, res) -> fprintf oc "%a ← %s(%a)"
                                 PrintMach.regs res (PrintAST.name_of_external ef) PrintMach.regs args
  | Annot (a, args) -> fprintf oc "⟨%s⟩(%a)" a annot_args args
  | Nop -> fprintf oc "nop"

let dot_program (f: string) (p: program) =
  let open Printf in
  let oc = open_out f in
  fprintf oc "digraph {\n";
  List.iter (fun (n, d) ->
      match d with
      | (Gvar _ | Gfun (External _)) -> ()
      | Gfun (Internal fn) ->
        let n = extern_atom n in
        let cfg = cfg_of_function fn in
        (*
        let bdcl = BourdoncleIterator.get_bourdoncle cfg in
        printf "Bourdoncle for %s:\n%s\n<<<<\n" n (string_of_bourdoncle_list bdcl);
         *)
        dump_cfg oc n cfg pp_label
    ) (prog_defs p);
  fprintf oc "}\n";
  close_out oc
