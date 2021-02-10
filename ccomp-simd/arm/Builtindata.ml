type builtin_data = { blt_class: int		(* simd class *)
		    ; blt_imms : int		(* # immediate args *)
		    ; blt_immargs: int64 list	(* immediate args *)
		    ; blt_twoaddr: bool		(* two-addr. instr. *)
		    ; blt_destr: (string list) option	(* destroyed regs *)
		    ; blt_asm: string list	(* asm instructions *)
		    }

let builtin_data_eq b1 b2 =
  b1.blt_class = b2.blt_class && b1.blt_imms = b2.blt_imms &&
  b1.blt_immargs = b2.blt_immargs &&
  b1.blt_asm = b2.blt_asm && b1.blt_twoaddr = b2.blt_twoaddr
  
