Require ABlock.
Import Utf8.
Import Util.
Import String.
Import Coqlib.
Import AST.
Import Integers.
Import Machregs.

Unset Elimination Schemes.

(** access SIMD builtin data *)
Parameter simd_infer_data : ident -> list mreg
                            -> option (list mreg(*args*) *
                                       option (bool(*write*)
                                               *(mreg(*ptr*)
                                                 *Z(*size*)))).

(* Pure built-ins, the list comes from SelectLongproof.v *)
Definition builtin_white_list (f: ident) : bool :=
  if in_dec string_dec (ABlock.string_of_ident f)
  ("__i64_dtos"
 :: "__i64_dtou"
 :: "__i64_stod"
 :: "__i64_utod"
 :: "__i64_stof"
 :: "__i64_utof"
 :: "__builtin_negl"
 :: "__builtin_addl"
 :: "__builtin_subl"
 :: "__builtin_mull"
 :: "__i64_sdiv"
 :: "__i64_udiv"
 :: "__i64_smod"
 :: "__i64_umod"
 :: "__i64_shl"
 :: "__i64_shr"
 :: "__i64_sar"
 :: nil)%string
  then true else false.

(** Builtin classification *)
Inductive builtin_kind : Type :=
| BuiltinPure `(list mreg(*args*), list mreg(*res*))
| BuiltinLoad `(mreg(*ptr*), Z(*size*), list mreg(*args*), list mreg(*res*))
| BuiltinStore `(mreg(*ptr*), Z(*size*), list mreg(*args*), list mreg(*res*))
| BuiltinUnsupported
| BuiltinUnknown.

Definition classify_builtin (blt: ident) (imms: list int) (sg: signature) (res args: list mreg) :=
  match simd_infer_data blt args with
  | Some (args, None) =>
    BuiltinPure args res
  | Some (args, Some (false, (ptr, size))) =>
    BuiltinLoad ptr size args res
  | Some (args, Some (true, (ptr, size))) =>
    BuiltinStore ptr size args res
  | None => (* other builtins... *)
    if builtin_white_list blt
    then BuiltinPure args res
    else BuiltinUnsupported
  end.
