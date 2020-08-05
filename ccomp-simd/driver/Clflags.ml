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
open Configuration

(* Command-line flags *)

let prepro_options = ref ([]: string list)
let linker_options = ref ([]: string list)
let assembler_options = ref ([]: string list)
let mach_options = ref 0
let option_flongdouble = ref false
let option_fstruct_return = ref false
let option_fbitfields = ref false
let option_fvararg_calls = ref true
let option_funprototyped = ref true
let option_fpacked_structs = ref false
let option_ffpu = ref true
let option_ffloatconstprop = ref 2
let option_ftailcalls = ref true
let option_falignfunctions = ref (None: int option)
let option_falignbranchtargets = ref 0
let option_faligncondbranchs = ref 0
let option_finline_asm = ref false
let option_Osize = ref false
let option_dparse = ref false
let option_dcmedium = ref false
let option_dclight = ref false
let option_dcminor = ref false
let option_drtl = ref false
let option_dltl = ref false
let option_dalloctrace = ref false
let option_dmach = ref false
let option_dasm = ref false
let option_sdump = ref false
let option_g = ref false
let option_o = ref (None: string option)
let option_E = ref false
let option_S = ref false
let option_c = ref false
let option_v = ref false
let option_interp = ref false
let option_small_data = 
  ref (if Configuration.arch = "powerpc"
       && Configuration.variant = "eabi"
       && Configuration.system = "diab"
       then 8 else 0)
let option_small_const = ref (!option_small_data)

(* flags concerning value and taint analyses *)
let option_dmir = ref false
let option_fva = ref false
let option_fta = ref false

(* machine-dependent option handling *)

let setbit n x  = x lor (1 lsl n)

let usage_ia32_string =
  let printmopt mopt r = let (opt,desc,mclass,cdefs,k) = mopt in
			 sprintf "%8s \t%s\n%s" opt desc r
  in "Machine-dependent options (ia32):\n" ^
       List.fold_right printmopt (List.rev CXBuiltins.ia32_mopts) ""


let mach_options_list =
  match Configuration.arch with
  | "ia32" -> List.map (fun (opt,desc,mclass,cdefs,k) -> opt)
		       CXBuiltins.ia32_mopts
  | _ -> []

let rec process_ia32_option lopts o =
  match lopts with
  | [] -> eprintf "Warning: unrecognised option '%s' \n" o
  | x::xs -> let (opt,desc,mclass,cdefs,cont) = x in
	     if opt = o
	     then (mach_options := setbit mclass !mach_options;
		   prepro_options := List.concat 
				       ((List.map (fun d->[d;"-D"]) cdefs)
					@ [!prepro_options]);
		   match cont with None -> ()
				 | Some o2 -> process_ia32_option xs o2)
	     else process_ia32_option xs o

let process_mach_option o =
  match Configuration.arch with
  | "ia32" -> process_ia32_option CXBuiltins.ia32_mopts o
  | _ -> printf "Warning: unrecognized option %s\n" o

