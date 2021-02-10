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

(** Pulling local scalar variables whose address is not taken
  into temporary variables. *)

Require Import FSets.
Require FSetAVL.
Require Import Coqlib.
Require Import Ordered.
Require Import Errors.
Require Import AST.
Require Import Ctypes.
Require Import Cop.
Require Import Clight.

Require Import Integers.
Require Import Maps.

Open Scope error_monad_scope.
Open Scope string_scope.

(** State and error monad for generating fresh identifiers. *)

Record generator : Type := mkgenerator {
  gen_next: ident;
  gen_trail: list (ident * type)
}.

Inductive result (A: Type) (g: generator) : Type :=
  | Err: errmsg -> result A g
  | Res: A -> forall (g': generator), Ple (gen_next g) (gen_next g') -> result A g.

Implicit Arguments Err [A g].
Implicit Arguments Res [A g].

Definition mon (A: Type) := forall (g: generator), result A g.

Definition ret (A: Type) (x: A) : mon A :=
  fun g => Res x g (Ple_refl (gen_next g)).

Implicit Arguments ret [A].

Definition error (A: Type) (msg: errmsg) : mon A :=
  fun g => Err msg.

Implicit Arguments error [A].

Definition assertion_failed {A: Type} : mon A := error (msg "Assertion failed").

Notation "'assertion' A ; B" := (if A then B else assertion_failed)
  (at level 200, A at level 100, B at level 200)
  : gensym_monad_scope.

Definition bind (A B: Type) (x: mon A) (f: A -> mon B) : mon B :=
  fun g =>
    match x g with
      | Err msg => Err msg
      | Res a g' i =>
          match f a g' with
          | Err msg => Err msg
          | Res b g'' i' => Res b g'' (Ple_trans _ _ _ i i')
      end
    end.

Implicit Arguments bind [A B].

Definition bind2 (A B C: Type) (x: mon (A * B)) (f: A -> B -> mon C) : mon C :=
  bind x (fun p => f (fst p) (snd p)).

Implicit Arguments bind2 [A B C].

Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : gensym_monad_scope.
Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
   (at level 200, X ident, Y ident, A at level 100, B at level 200)
   : gensym_monad_scope.

Local Open Scope gensym_monad_scope.

Parameter first_unused_ident: unit -> ident.

Definition initial_generator (vars: list (ident*type)) : generator := 
  mkgenerator (Psucc (Pmax (first_unused_ident tt) (var_maxident vars))) nil.

Definition gensym (ty: type): mon ident :=
  fun (g: generator) => 
    Res (gen_next g)
        (mkgenerator (Psucc (gen_next g)) ((gen_next g, ty) :: gen_trail g))
        (Ple_succ (gen_next g)).

Fixpoint gensyms (tys: list type): mon (list ident) :=
 match tys with
 | nil => ret nil
 | t::ts => do i <- gensym t;
            do ii <- gensyms ts;
            ret (i::ii)
 end.

Definition reset_trail: mon unit :=
  fun (g: generator) =>
    Res tt (mkgenerator (gen_next g) nil) (Ple_refl (gen_next g)).

Definition get_trail: mon (list (ident * type)) :=
  fun (g: generator) =>
    Res (gen_trail g) g (Ple_refl (gen_next g)).

Module VSet := FSetAVL.Make(OrderedPositive).

(** [hvenv] maps identifiers of local variables of homogeneous
  aggregates to the corresponding field temporaries. *)

Definition hvenv := PTree.t (list (ident*type)). (* map variable -> id*type *)

Definition empty_hvenv: env := (PTree.empty (ident * type)).

(** The temporary environment maps local hom. structures to field temporaries. *)

Definition temp_env := PTree.t (list (ident*type)).


(** The set of local variables that can be lifted to temporaries,
  because they are scalar and their address is not taken. *)

Definition compilenv := (*VSet.t*) PTree.t (list (ident*type)).

(** Smart constructor for casts *)

Definition make_cast (a: expr) (tto: type) : expr :=
  match classify_cast (typeof a) tto with
  | cast_case_neutral => a
  | cast_case_i2i I32 _ => a
  | cast_case_f2f F64 => a
  | cast_case_l2l => a
  | cast_case_struct _ _ _ _ => a
  | cast_case_union _ _ _ _ => a
  | cast_case_void => a
  | _ => Ecast a tto
  end.

(** Rewriting of expressions and statements. *)
Fixpoint ha_selector (e:expr) : bool :=
 match e with
 | Evar _ ty => match ha_type ty with None => false | _ => true end
 | Efield e' _ _ => ha_selector e'
 | Ederef (Ebinop Oadd e' (Econst_int n _) _) _ => 
     match typeof e' with
     | Tarray _ size _ => andb (andb (Z.leb 0 (Int.intval n))
                                     (Z.ltb (Int.intval n) size))
                               (ha_selector e')
     | _ => false
     end
 | _ => false
 end.
(*
Fixpoint ha_selector (e:expr) (ty:type) : nat option :=
 match ty with
 | Tstruct _ fl _ =>
    match e with
    | Efield e' f _ => ha_selector_fl f fl
    | _ => None
    end
 | Tarray ty' size _ =>
    match e with
    | Ederef (Ebinop Oadd e' (Econst_int i _) _ => 
 | _ => 
 end
with ha_selector_fl f (l:fieldlist) :=
 match l with
 | Fnil => Some nil
 | Fcons f t fl =>
   match t with
   | Tarray t' size _ => 
     if Z.leb size (Z_of_nat n)
     then match ha_selectors_fl bt (n-Zabs_nat size) fl with
          | Some l =>
          | None =>
          end
   | Tstruct _ fl' _ =>
     match ha_selectors_fl with
     | Some =>
     | None =>
     end
   | _ => 
   end
 end.
*)

(*
Definition get_fieldtemp (cenv: compilenv) (e:expr) (ty:type) (f:ident)
: option (ident*type) :=
  match e with
  | Etempvar id t => match homogeneous_aggregate ty with
                     | None => None
                     | Some (t,fld) => if ident_eq 
  | _ => None
  end.
*)

Fixpoint ha_type_fieldnum_fl (f:ident) (fl:fieldlist) : option Z :=
 match fl with
 | Fnil => None
 | Fcons f' ty' fl' =>
     if ident_eq f f'
     then Some 0
     else match ha_type_chk ty', ha_type_fieldnum_fl f fl' with
          | Some (size,_), Some n => Some (size+n)
          | _, _ => None
          end
 end.

Definition ha_type_fieldnum (f:ident) (ty:type) : option Z :=
 match ty with
 | Tstruct _ fl _ => ha_type_fieldnum_fl f fl
 | _ => None
 end.

(* [ha_fieldnum] returns the index of a selection expression (lvalue)
  of a HA value (ensuring that it falls inside the size of the HA),
  together with the base HA variable and its size                    *)
Fixpoint ha_fieldnum (e:expr): option (Z*ident*Z) :=
 match e with
 | Efield e' f _ => 
     match ha_fieldnum e' with
     | Some (b,id,size) => match ha_type_fieldnum f (typeof e') with
                           | Some n => Some (b+n,id,size)
                           | _ => None
                           end
     | _ => None
     end
 | Ederef (Ebinop Oadd e' (Econst_int i _) _) _  =>
     match ha_fieldnum e' with
     | Some (n,id,size) => let k := n+Int.intval i in
                           if andb (Z.leb 0 k)
                                   (Z.ltb k size)
                           then Some (k,id,size)
                           else None
     | _ => None
     end
 | Evar id ty => match ha_type ty with
        | Some (size,_) => Some (0,id,size)
        | _ => None
        end
 | _ => None
 end.

Definition ha_gettemp cenv (a:expr) :=
 match ha_fieldnum a with
 | Some (n,v,_) =>
    match PTree.get v cenv with
    | Some (x::xs) => let (id',t') := @nth (ident*type) (Zabs_nat n) (x::xs) x in
                      Some (Etempvar id' t')
    | _ => None
    end
 | _ => None
 end.

Fixpoint simpl_expr (cenv: compilenv) (a: expr) : expr :=
  match ha_gettemp cenv a with
  | Some e => e
  | _ =>
     match a with
     | Econst_int _ _ => a
     | Econst_float _ _ => a
     | Econst_long _ _ => a
     | Econst_vec _ _ => a
     | Evar id ty => (*if VSet.mem id cenv then Etempvar id ty else Evar id ty*)
        match PTree.get id cenv with
        | Some nil => Etempvar id ty
        | _ => Evar id ty
        end
     | Etempvar id ty => Etempvar id ty
     | Ederef a1 ty => Ederef (simpl_expr cenv a1) ty
     | Eaddrof a1 ty => Eaddrof (simpl_expr cenv a1) ty
     | Eunop op a1 ty => Eunop op (simpl_expr cenv a1) ty
     | Ebinop op a1 a2 ty => Ebinop op (simpl_expr cenv a1) (simpl_expr cenv a2) ty
     | Ecast a1 ty => if type_eq ty (typeof a1)
                      then simpl_expr cenv a1
                      else Ecast (simpl_expr cenv a1) ty
     | Efield a1 f ty =>
         let a1' := simpl_expr cenv a1 in
(*
         match a1', homogeneous_aggregate (typeof a1) with
         | Etempvar id _, Some (t,fld) => 
            match PTree.get id cenv with
            | None => Efield a1' f ty (* should never happen *)
            | Some l => match get_field_fieldlist fld f l with
                        | Some (id',t') => Etempvar id' t'
                        | None => Efield a1' f ty (* should never happen *)
                        end
            end
         | _, _ =>*) Efield a1' f ty
     end
  end.

Definition simpl_exprlist (cenv: compilenv) (al: list expr) : list expr :=
  List.map (simpl_expr cenv) al.

Definition is_lifted_lvalue (cenv: compilenv) (a: expr) : option ident :=
  let a' := simpl_expr cenv a in
  match a' with
      | Etempvar id _ => Some id
      | _ => None
  end.

Definition check_temp (cenv: compilenv) (id: ident) : mon unit :=
(*  if VSet.mem id cenv
  then Error (MSG "bad temporary " :: CTX id :: nil)
  else OK tt.*)
  match PTree.get id cenv with
  | None => ret tt
  | Some _ => error (MSG "bad temporary " :: CTX id :: nil)
  end.

(*
Definition check_opttemp (cenv: compilenv) (optid: option ident) : mon unit :=
  match optid with
  | Some id => check_temp cenv id
  | None => ret tt
  end.
*)

Fixpoint check_listtemp (cenv: compilenv) (optid: list ident) : mon unit :=
  match optid with
  | x::xs => do a <- check_temp cenv x;
             check_listtemp cenv xs
  | nil => ret tt
  end.

Fixpoint simpl_stmt (cenv: compilenv) (s: statement) : mon statement :=
  match s with
  | Sskip => ret Sskip
  | Sassign a1 a2 =>
      match is_lifted_lvalue cenv a1 with
      | Some id =>
          ret (Sset id (make_cast (simpl_expr cenv a2) (typeof a1)))
      | None =>
          ret (Sassign (simpl_expr cenv a1) (simpl_expr cenv a2))
      end
  | Sset id a =>
      do x <- check_temp cenv id;
      ret (Sset id (simpl_expr cenv a))
  | Scall optid a al =>
      do x <- check_listtemp cenv optid;
      ret (Scall optid (simpl_expr cenv a) (simpl_exprlist cenv al))
  | Sbuiltin optid ef tyargs al =>
      do x <- check_listtemp cenv optid;
      ret (Sbuiltin optid ef tyargs (simpl_exprlist cenv al))
  | Ssequence s1 s2 =>
      do s1' <- simpl_stmt cenv s1;
      do s2' <- simpl_stmt cenv s2;
      ret (Ssequence s1' s2')
  | Sifthenelse a s1 s2 =>
      do s1' <- simpl_stmt cenv s1;
      do s2' <- simpl_stmt cenv s2;
      ret (Sifthenelse (simpl_expr cenv a) s1' s2')
  | Sloop s1 s2 =>
      do s1' <- simpl_stmt cenv s1;
      do s2' <- simpl_stmt cenv s2;
      ret (Sloop s1' s2')
  | Sbreak => ret Sbreak
  | Scontinue => ret Scontinue
  | Sreturn opta => ret (Sreturn (simpl_exprlist cenv opta))
  | Sswitch a ls =>
      do ls' <- simpl_lblstmt cenv ls;
      ret (Sswitch (simpl_expr cenv a) ls')
  | Slabel lbl s =>
      do s' <- simpl_stmt cenv s;
      ret (Slabel lbl s')
  | Sgoto lbl => ret (Sgoto lbl)
  end

with simpl_lblstmt (cenv: compilenv) (ls: labeled_statements) : mon labeled_statements :=
  match ls with
  | LSnil =>
      ret LSnil
  | LScons c s ls1 =>
      do s' <- simpl_stmt cenv s;
      do ls1' <- simpl_lblstmt cenv ls1;
      ret (LScons c s' ls1')
  end.

(** Function parameters that are not lifted to temporaries must be
  stored in the corresponding local variable at function entry. *)

Fixpoint store_params (cenv: compilenv) (params: list (ident * type))
                      (s: statement): statement :=
  match params with
  | nil => s
  | (id, ty) :: params' =>
(*
      if VSet.mem id cenv
      then store_params cenv params' s
      else Ssequence (Sassign (Evar id ty) (Etempvar id ty))
                     (store_params cenv params' s)
*)
    match PTree.get id cenv with
    | None => Ssequence (Sassign (Evar id ty) (Etempvar id ty))
                        (store_params cenv params' s)
    | Some _ => store_params cenv params' s
    end
  end.

(** Compute the set of variables whose address is taken *)

Fixpoint addr_taken_expr (a: expr): VSet.t :=
  match ha_fieldnum a with
  | Some _ => VSet.empty
  | _ =>
    match a with
    | Econst_int _ _ => VSet.empty
    | Econst_float _ _ => VSet.empty
    | Econst_long _ _ => VSet.empty
    | Econst_vec _ _ => VSet.empty
    | Evar id ty => VSet.empty
    | Etempvar id ty => VSet.empty
    | Ederef a1 ty => addr_taken_expr a1
    | Eaddrof (Evar id ty1) ty => VSet.singleton id
    | Eaddrof a1 ty => addr_taken_expr a1
    | Eunop op a1 ty => addr_taken_expr a1
    | Ebinop op a1 a2 ty => VSet.union (addr_taken_expr a1) (addr_taken_expr a2)
    | Ecast a1 ty => addr_taken_expr a1
    | Efield a1 fld ty => addr_taken_expr a1
    end
  end.

Fixpoint addr_taken_exprlist (l: list expr) : VSet.t :=
  match l with
  | nil => VSet.empty
  | a :: l' => VSet.union (addr_taken_expr a) (addr_taken_exprlist l')
  end.

Fixpoint addr_taken_stmt (s: statement) : VSet.t :=
  match s with
  | Sskip => VSet.empty
  | Sassign a b => VSet.union (addr_taken_expr a) (addr_taken_expr b)
  | Sset id a => addr_taken_expr a
  | Scall optid a bl => VSet.union (addr_taken_expr a) (addr_taken_exprlist bl)
  | Sbuiltin optid ef tyargs bl => addr_taken_exprlist bl
  | Ssequence s1 s2 => VSet.union (addr_taken_stmt s1) (addr_taken_stmt s2)
  | Sifthenelse a s1 s2 =>
      VSet.union (addr_taken_expr a) (VSet.union (addr_taken_stmt s1) (addr_taken_stmt s2))
  | Sloop s1 s2 => VSet.union (addr_taken_stmt s1) (addr_taken_stmt s2)
  | Sbreak => VSet.empty
  | Scontinue => VSet.empty
(*  | Sreturn None => VSet.empty*)
  | Sreturn a => addr_taken_exprlist a
  | Sswitch a ls => VSet.union (addr_taken_expr a) (addr_taken_lblstmt ls)
  | Slabel lbl s => addr_taken_stmt s
  | Sgoto lbl => VSet.empty
  end

with addr_taken_lblstmt (ls: labeled_statements) : VSet.t :=
  match ls with
  | LSnil => VSet.empty
  | LScons c s ls' => VSet.union (addr_taken_stmt s) (addr_taken_lblstmt ls')
  end.

(** The compilation environment for a function is the set of local variables
  that are scalars and whose addresses are not taken. *)

Fixpoint add_local_ha_temps t n : mon (list (ident*type)) :=
 match n with
 | O => ret nil
 | S n' => do id <- gensym t;
           do rem <- add_local_ha_temps t n';
           ret ((id,t)::rem)
 end.

Definition add_local_variable (atk: VSet.t) (id_ty: ident * type)
                              (cenv: compilenv) : mon compilenv :=
  let (id, ty) := id_ty in
  match access_mode ty with
  | By_value chunk => if VSet.mem id atk
                      then ret cenv
                      else (*VSet.add id cenv*) ret (PTree.set id nil cenv)
  | _ => match ha_type ty with
         | None => ret cenv
         | Some (size,bt) =>
             if VSet.mem id atk
             then ret cenv
             else do l <- add_local_ha_temps bt (Zabs_nat size);
                  ret (PTree.set id l cenv)
         end
  end.

(* obs: seria preciso adicionar a [atk] os parametros homfstruct --- mas
  a ideia é mesmo expandir esses parametros, pelo que fica assim...*)
Definition cenv_for (f: function) : mon compilenv :=
  let atk := addr_taken_stmt f.(fn_body) in
  List.fold_right (fun it r => do x <- r;
                               add_local_variable atk it x)
                  (ret (PTree.empty _)) (f.(fn_params) ++ f.(fn_vars)).

(** Transform a function *)

Definition remove_lifted (cenv: compilenv) (vars: list (ident * type)) :=
  List.filter (fun id_ty => match PTree.get (fst id_ty) cenv with
                            | None => true
                            | Some _ => false
                            end) vars.

Definition add_lifted (cenv: compilenv) (vars1 vars2: list (ident * type)) :=
  List.fold_right (fun id_ty r => match PTree.get (fst id_ty) cenv with
                                  | None => r
                                  | Some nil => id_ty::r
                                  | Some l => l++r
                                  end) nil vars1 ++ vars2.

Definition transf_function (f: function) : mon function :=
  assertion (list_disjoint_dec ident_eq (var_names f.(fn_params)) (var_names f.(fn_temps)));
  do cenv <- cenv_for f;
  do body' <- simpl_stmt cenv f.(fn_body);
  ret {| fn_return := f.(fn_return);
         fn_callconv := f.(fn_callconv);
         fn_params := f.(fn_params);
         fn_vars := remove_lifted cenv (f.(fn_params) ++ f.(fn_vars));
         fn_temps := add_lifted cenv f.(fn_vars) f.(fn_temps);
         fn_body := store_params cenv f.(fn_params) body' |}.

(** Whole-program transformation *)


Definition transf_fundef (fd: fundef) : res fundef :=
  match fd with
  | Internal f => match transf_function f (initial_generator (f.(fn_temps))) with
                  | Err msg =>
                    Error msg
                  | Res tf _ _ => OK (Internal tf)
                  end
  | External ef targs tres cconv => OK (External ef targs tres cconv)
  end.

Definition transf_program (p: program) : res program :=
  AST.transform_partial_program transf_fundef p.

