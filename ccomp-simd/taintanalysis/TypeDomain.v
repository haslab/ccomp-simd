Require Import AdomLib.
Require Import ABlock.
Import Coqlib.
Import ToString.
Import Containers.Sets.

Unset Elimination Schemes.

Definition ptset : Type := set ablock +⊤.

Definition ptset_leb (x y: ptset) : bool :=
  match y with
  | All => true
  | Just y' => match x with All => false | Just x' => subset x' y' end
  end.

Definition ptset_join (x y: ptset) : ptset :=
  match x with
  | All => y
  | Just x' => match y with All => All | Just y' => Just (union x' y') end
  end.

Inductive type : Type :=
| TyFloat | TySingle | TyL64 | TyL128
| TyZero | TyInt
| TyPtr `(ptset)
| TyZPtr `(ptset)
| TyIntPtr.

Instance string_of_type : ToString type :=
  λ ty,
  match ty with
  | TyFloat => "float"
  | TySingle => "single"
  | TyL64 => "long64"
  | TyL128 => "long128"
  | TyZero => "null"
  | TyInt => "int"
  | TyPtr bs => "ptr(" ++ to_string bs ++ ")"
  | TyZPtr bs => "null-ptr(" ++ to_string bs ++ ")"
  | TyIntPtr => "int-or-ptr"
  end%string.

Definition type_leb (x x': type) : bool :=
  match x, x' with
  | TyFloat, TyFloat
  | TySingle, TySingle
  | TyL64, TyL64
  | TyL128, TyL128
    => true
  | TyFloat, _ | _, TyFloat
  | TySingle, _ | _, TySingle
  | TyL64, _ | _, TyL64
  | TyL128, _ | _, TyL128
    => false
  | TyZero, (TyZero | TyInt | TyZPtr _ | TyIntPtr) => true
  | TyZero, TyPtr _ => false
  | TyInt, (TyInt | TyIntPtr) => true
  | TyInt, (TyZero | TyPtr _ | TyZPtr _) => false
  | TyPtr b, (TyPtr b' | TyZPtr b')
  | TyZPtr b, (TyZPtr b') => ptset_leb b b'
  | (TyPtr _ | TyZPtr _), TyIntPtr => true
  | TyPtr _, (TyZero | TyInt) => false
  | TyZPtr _, (TyZero | TyInt | TyPtr _) => false
  | TyIntPtr, TyIntPtr => true
  | TyIntPtr, (TyZero | TyInt | TyPtr _ | TyZPtr _) => false
  end.

Definition type_join (x x': type) : type+⊤ :=
  match x, x' with
  | TyFloat, TyFloat
  | TySingle, TySingle
  | TyL64, TyL64
  | TyL128, TyL128
  | TyZero, TyZero
  | TyInt, TyInt
  | TyIntPtr, TyIntPtr
    => Just x
  | TyFloat, _ | _, TyFloat
  | TySingle, _ | _, TySingle
  | TyL64, _ | _, TyL64
  | TyL128, _ | _, TyL128
    => All
  | (TyZero | TyInt), TyIntPtr
  | TyZero, TyInt
    => Just x'
  | (TyInt | TyIntPtr), TyZero
  | TyIntPtr, TyInt
    => Just x
  | (TyPtr b | TyZPtr b), TyZero
  | TyZero, (TyPtr b | TyZPtr b) => Just (TyZPtr b)
  | (TyPtr _ | TyZPtr _), (TyInt | TyIntPtr)
  | (TyInt | TyIntPtr), (TyPtr _ | TyZPtr _) => Just TyIntPtr
  | TyPtr b, TyPtr b' => Just (TyPtr (ptset_join b b'))
  | TyZPtr b, TyPtr b'
  | TyPtr b, TyZPtr b'
  | TyZPtr b, TyZPtr b'
    => Just (TyZPtr (ptset_join b b'))
  end.

Section PEXPR.

Import Integers.
Import Op.

Context (var: Type) (OT: OrderedType var).

Definition pexpr : Type :=
  (operation * list var)%type.

(* Warning: it is OK to ignore type errors unless we handle type punning,
in which case TyInt guarantees the value is not Vundef. *)
Definition eval_ptr stk (τ: var → type+⊤) (pe: pexpr) : type +⊤ :=
  let '(op, args) := pe in
  match op with
  | Omove => match args with x :: nil => τ x | _ => All end
  | Ointconst i => Just (if Int.eq i Int.zero then TyZero else TyInt)
  | Ofloatconst _ => Just TyFloat
  | Oindirectsymbol g => Just (TyPtr (Just { ABGlobal g }))
  | Ocast8signed | Ocast8unsigned
  | Ocast16signed | Ocast16unsigned
  | Oneg
  | Omul | Omulimm _
  | Omulhs | Omulhu
  | Odiv | Odivu
  | Omod | Omodu
  | Oand | Oandimm _
  | Oor | Oorimm _
  | Oxor | Oxorimm _
  | Oshl | Oshlimm _
  | Oshr | Oshrimm _ | Oshrximm _ | Oshru | Oshruimm _
  | Ororimm _
  | Oshldimm _
  | Ointoffloat
  | Olowlong | Ohighlong
  | Ocmp _
    => Just TyInt
  | Onegf | Oabsf
  | Oaddf | Osubf
  | Omulf | Odivf
  | Ofloatofint
    => Just TyFloat
  | Osingleoffloat => Just TySingle
  | Omakelong => Just TyL64
  | OX _ => Just TyL128
  | Osub =>
    match args with
    | x :: y :: nil =>
      topbind
        (λ a,
         topbind
           (λ b,
            match a, b with
            | _, TyZero
            | (TyPtr _ | TyInt), TyInt => Just a
            | TyZero, TyInt => Just b
            | (TyZPtr _ | TyIntPtr), TyInt => Just TyIntPtr
            | TyPtr bs, TyPtr bs' => Just TyInt
            | _, _ => All
            end) (τ y)
        ) (τ x)
    | _ => All
    end
  | Olea addr =>
    match addr with
    | Aindexed _ | Ascaled _ _ =>
      match args with
      | x :: nil =>
        match τ x with
        | Just TyZero => Just TyInt
        | Just (TyZPtr _) => Just TyIntPtr
        | ty => ty end
      | _ => All end
    | Aindexed2 _ | Aindexed2scaled _ _ =>
      match args with
      | x :: y :: nil =>
        topbind
          (λ tx,
           topbind
             (λ ty,
              match tx, ty with
              | (TyInt | TyZero), (TyInt | TyZero) => Just TyInt
              | (TyInt | TyZero), (TyPtr _ | TyIntPtr) => Just ty
              | (TyPtr _ | TyIntPtr), (TyInt | TyZero) => Just tx
              | (TyZero | TyInt), TyZPtr _
              | TyZPtr _, (TyZero | TyInt)
                => Just TyIntPtr
              | TyIntPtr, TyPtr _
              | (TyPtr _ | TyIntPtr), (TyZPtr _ | TyIntPtr)
              | TyZPtr _, (TyPtr _ | TyZPtr _ | TyIntPtr)
              | TyPtr _, TyPtr _ => All
              | (TyFloat | TySingle | TyL64 | TyL128), _
              | _, (TyFloat | TySingle | TyL64 | TyL128) => All
              end)
             (τ y)
          ) (τ x)
      | _ => All
      end
    | Aglobal g _ | Abased g _ | Abasedscaled _ g _
      => Just (TyPtr (Just { ABGlobal g }))
    | Ainstack _ => match stk with N0 => All | Npos stk => Just (TyPtr (Just { ABStack stk })) end
    end
  end.

End PEXPR.

Arguments eval_ptr {_} _ _ _.
