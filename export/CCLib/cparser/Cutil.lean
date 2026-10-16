/-
  Port of `cparser/Cutil.ml`: operations on C types and abstract syntax
  (attributes, typedef unrolling, type compatibility, sizes and alignments,
  struct layout, conversions, classification of types and expressions,
  smart constructors, default initializers, substitution).

  Functions that can raise an OCaml exception (`Env.Error`, `Not_found`, a
  failed `assert`) or read global state (`Machine.config`, the attribute
  table) run in the front-end monad `M` (see `Diagnostics.lean`).  The local
  exceptions `Incompat` and `No_default_init` become `OptionT M` (or `none`).

  `align x boundary` is computed as `(x + boundary - 1) / boundary * boundary`,
  which equals OCaml's `land`/`lnot` computation for the powers of two (and
  zero) that it is applied to.
-/
import CCLib.cparser.Env
import CCLib.cparser.Cprint

namespace CC
namespace CParser
namespace Cutil

open C Env Diagnostics

/-- Empty location -/
def no_loc : Location := ("", -1)

/-- Sets and maps over identifiers. -/
abbrev IdentSet := Std.HashSet Ident
abbrev IdentMap (α : Type) := Std.HashMap Ident α

/-! ### Operations on attributes -/

/-- Normalize the name of an attribute, removing starting and trailing `__` -/
def normalize_attrname (a : String) : String :=
  if a.length ≥ 4 && a.startsWith "__" && a.endsWith "__" then
    ((a.drop 2).dropEnd 2).toString
  else a

/-- Lists of attributes are kept sorted in increasing order -/
def add_attributes : Attributes → Attributes → Attributes
  | [], al2 => al2
  | al1, [] => al1
  | a1 :: al1', a2 :: al2' =>
      if a1 < a2 then a1 :: add_attributes al1' (a2 :: al2')
      else if a2 < a1 then a2 :: add_attributes (a1 :: al1') al2'
      else a1 :: add_attributes al1' al2'

/-- viewed as sets: `al1 \ al2` -/
def remove_attributes : Attributes → Attributes → Attributes
  | [], _ => []
  | al1, [] => al1
  | a1 :: al1', a2 :: al2' =>
      if a1 < a2 then a1 :: remove_attributes al1' (a2 :: al2')
      else if a2 < a1 then remove_attributes (a1 :: al1') al2'
      else remove_attributes al1' al2'

def incl_attributes : Attributes → Attributes → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a1 :: al1', a2 :: al2' =>
      if a1 < a2 then false
      else if a2 < a1 then incl_attributes (a1 :: al1') al2'
      else incl_attributes al1' al2'

def find_custom_attributes (names : List String) : Attributes → List (List AttrArg)
  | [] => []
  | .Attr name args :: tl =>
      if names.contains name then args :: find_custom_attributes names tl
      else find_custom_attributes names tl
  | _ :: tl => find_custom_attributes names tl

def remove_custom_attributes (names : List String) : Attributes → Attributes
  | [] => []
  | a :: tl =>
      match a with
      | .Attr name _ =>
          if names.contains name then remove_custom_attributes names tl
          else a :: remove_custom_attributes names tl
      | _ => a :: remove_custom_attributes names tl

/-! Classification of attributes (`attribute_class` is `AttributeClass`,
    declared in `Diagnostics.lean`) -/

def declare_attribute (name : String) (cls : AttributeClass) : M Unit :=
  modify fun s =>
    let n := normalize_attrname name
    { s with attr_class := (n, cls) :: s.attr_class.filter (·.1 != n) }

def declare_attributes (l : List (String × AttributeClass)) : M Unit :=
  l.forM fun (n, c) => declare_attribute n c

def class_of_attribute : Attribute → M AttributeClass
  | .AConst | .AVolatile | .ARestrict => pure .Attr_type
  | .AAlignas _ => pure .Attr_object
  | .Attr name _ => do
      match (← get).attr_class.lookup (normalize_attrname name) with
      | some c => pure c
      | none => pure .Attr_unknown

/-- Name for printing an attribute -/
def name_of_attribute : Attribute → String
  | .AConst => "const"
  | .AVolatile => "volatile"
  | .ARestrict => "restrict"
  | .AAlignas _ => "_Alignas"
  | .Attr name _ => name

/-- Is an attribute a ISO C standard attribute? -/
def attr_is_standard : Attribute → Bool
  | .AConst | .AVolatile | .ARestrict => true
  | .AAlignas _ | .Attr .. => false

/-- Is an attribute applicable to a whole array (true) or only to
    array elements (false)? -/
def attr_array_applicable (a : Attribute) : M Bool := do
  return (← class_of_attribute a) != .Attr_type

/-- Is an attribute of a composite type applicable to members of this type
    when they are accessed? -/
def attr_inherited_by_members : Attribute → Bool
  | .AConst | .AVolatile | .ARestrict => true
  | .AAlignas _ | .Attr .. => false

/-- Adding top-level attributes to a type.  Doesn't need to unroll defns.
    For array types, standard attrs are pushed to the element type. -/
partial def add_attributes_type (attr : Attributes) (t : Typ) : M Typ :=
  match t with
  | .TVoid a => pure (.TVoid (add_attributes attr a))
  | .TInt ik a => pure (.TInt ik (add_attributes attr a))
  | .TFloat fk a => pure (.TFloat fk (add_attributes attr a))
  | .TPtr ty a => pure (.TPtr ty (add_attributes attr a))
  | .TArray ty sz a => do
      let mut attr_arr := []
      let mut attr_elt := []
      for x in attr do
        if ← attr_array_applicable x then attr_arr := attr_arr ++ [x]
        else attr_elt := attr_elt ++ [x]
      return .TArray (← add_attributes_type attr_elt ty) sz (add_attributes attr_arr a)
  | .TFun ty params vararg a => pure (.TFun ty params vararg (add_attributes attr a))
  | .TNamed s a => pure (.TNamed s (add_attributes attr a))
  | .TStruct s a => pure (.TStruct s (add_attributes attr a))
  | .TUnion s a => pure (.TUnion s (add_attributes attr a))
  | .TEnum s a => pure (.TEnum s (add_attributes attr a))

/-- Unrolling of typedef -/
partial def unroll (env : Env.T) (t : Typ) : M Typ :=
  match t with
  | .TNamed name attr => do
      let ty ← Env.find_typedef env name
      unroll env (← add_attributes_type attr ty)
  | _ => pure t

private def catchUnboundTag {α} (x : M α) (dflt : α) : M α :=
  tryCatch x fun
    | .EnvError (.Unbound_tag _ _) => pure dflt
    | e => throw e

/-- Extracting the attributes of a type, including the attributes attached
    to typedefs, structs and unions. -/
partial def attributes_of_type (env : Env.T) (t : Typ) : M Attributes :=
  match t with
  | .TVoid a | .TInt _ a | .TFloat _ a | .TPtr _ a | .TFun _ _ _ a => pure a
  | .TArray ty _ a => do return add_attributes a (← attributes_of_type env ty)
  | .TNamed _ _ => do attributes_of_type env (← unroll env t)
  | .TStruct s a =>
      catchUnboundTag (do return add_attributes (← Env.find_struct env s).ci_attr a) a
  | .TUnion s a =>
      catchUnboundTag (do return add_attributes (← Env.find_union env s).ci_attr a) a
  | .TEnum s a =>
      catchUnboundTag (do return add_attributes (← Env.find_enum env s).ei_attr a) a

/-- Extracting the attributes of a type, excluding the attributes attached to
    typedefs, structs and unions. -/
def attributes_of_type_no_expand : Typ → Attributes
  | .TVoid a | .TInt _ a | .TFloat _ a | .TPtr _ a | .TFun _ _ _ a => a
  | .TArray ty _ a => add_attributes a (attributes_of_type_no_expand ty)
  | .TNamed _ a | .TStruct _ a | .TUnion _ a | .TEnum _ a => a

/-- Changing the attributes of a type (at top-level) -/
partial def change_attributes_type (env : Env.T) (f : Attributes → Attributes) (t : Typ) :
    M Typ :=
  match t with
  | .TVoid a => pure (.TVoid (f a))
  | .TInt ik a => pure (.TInt ik (f a))
  | .TFloat fk a => pure (.TFloat fk (f a))
  | .TPtr ty a => pure (.TPtr ty (f a))
  | .TArray ty sz a => do return .TArray (← change_attributes_type env f ty) sz (f a)
  | .TFun ty params vararg a => pure (.TFun ty params vararg (f a))
  | .TNamed _ _ => do
      let t1 ← unroll env t
      let t2 ← change_attributes_type env f t1
      return if t2 == t1 then t else t2
  | .TStruct s a => pure (.TStruct s (f a))
  | .TUnion s a => pure (.TUnion s (f a))
  | .TEnum s a => pure (.TEnum s (f a))

def remove_attributes_type (env : Env.T) (attr : Attributes) (t : Typ) : M Typ :=
  change_attributes_type env (fun a => remove_attributes a attr) t

def erase_attributes_type (env : Env.T) (t : Typ) : M Typ :=
  change_attributes_type env (fun _ => []) t

/-- Remove all attributes from type that are not contained in `attr` -/
def strip_attributes_type (t : Typ) (attr : Attributes) : Typ :=
  let strip := List.filter (fun a => attr.contains a)
  match t with
  | .TVoid at_ => .TVoid (strip at_)
  | .TInt k at_ => .TInt k (strip at_)
  | .TFloat k at_ => .TFloat k (strip at_)
  | .TPtr t at_ => .TPtr t (strip at_)
  | .TArray t s at_ => .TArray t s (strip at_)
  | .TFun t arg v at_ => .TFun t arg v (strip at_)
  | .TNamed n at_ => .TNamed n (strip at_)
  | .TStruct n at_ => .TStruct n (strip at_)
  | .TUnion n at_ => .TUnion n (strip at_)
  | .TEnum n at_ => .TEnum n (strip at_)

/-- Remove the last attribute from the toplevel and return the changed type -/
def strip_last_attribute (typ : Typ) : Option Attribute × Typ :=
  let hd_opt : Attributes → Option Attribute × Attributes
    | [] => (none, [])
    | a :: rest => (some a, rest)
  match typ with
  | .TVoid at_ => let (l, r) := hd_opt at_; (l, .TVoid r)
  | .TInt k at_ => let (l, r) := hd_opt at_; (l, .TInt k r)
  | .TFloat k at_ => let (l, r) := hd_opt at_; (l, .TFloat k r)
  | .TPtr t at_ => let (l, r) := hd_opt at_; (l, .TPtr t r)
  | .TArray t s at_ => let (l, r) := hd_opt at_; (l, .TArray t s r)
  | .TFun t arg v at_ => let (l, r) := hd_opt at_; (l, .TFun t arg v r)
  | .TNamed n at_ => let (l, r) := hd_opt at_; (l, .TNamed n r)
  | .TStruct n at_ => let (l, r) := hd_opt at_; (l, .TStruct n r)
  | .TUnion n at_ => let (l, r) := hd_opt at_; (l, .TUnion n r)
  | .TEnum n at_ => let (l, r) := hd_opt at_; (l, .TEnum n r)

/-- Check whether the attributes contain `_Alignas` attribute -/
def has_std_alignas (env : Env.T) (typ : Typ) : M Bool := do
  return (← attributes_of_type env typ).any fun | .AAlignas _ => true | _ => false

/-- Extracting alignment value from a set of attributes.  Return 0 if none. -/
def alignas_attribute (al : Attributes) : Int :=
  al.foldl (fun accu a =>
    match a with
    | .AAlignas n => max n accu
    | .Attr "aligned" [.AInt n] | .Attr "__aligned__" [.AInt n] => max n.toInt accu
    | _ => accu) 0

/-- Extracting struct packing parameters from a set of attributes. -/
def packing_parameters (al : Attributes) : Int × Int × Bool :=
  match find_custom_attributes ["packed", "__packed__"] al with
  | [[]] => (1, 0, false)
  | [[.AInt n]] => (n.toInt, 0, false)
  | [[.AInt n, .AInt p]] => (n.toInt, p.toInt, false)
  | [[.AInt n, .AInt p, .AInt q]] => (n.toInt, p.toInt, q == 1)
  | _ => (0, 0, false)

/-! ### Type compatibility -/

def enum_ikind : IKind := .IInt

inductive AttrHandling where
  | AttrCompat
  | AttrIgnoreTop
  | AttrIgnoreAll
  deriving BEq, DecidableEq, Inhabited, Repr

/-- Check that `t1` and `t2` are compatible and produce a type that combines
    the information in `t1` and `t2`. -/
partial def combine_types (mode : AttrHandling) (env : Env.T) (t1 t2 : Typ) :
    M (Option Typ) :=
  (comp mode t1 t2).run
where
  comp_attr (m : AttrHandling) (a1 a2 : Attributes) : OptionT M Attributes :=
    if a1 == a2 then pure a2 else
    match m with
    | .AttrCompat =>
        let (a1std, a1other) := a1.partition attr_is_standard
        let (a2std, a2other) := a2.partition attr_is_standard
        if a1std == a2std then pure (add_attributes a1std (add_attributes a1other a2other))
        else failure
    | .AttrIgnoreTop | .AttrIgnoreAll => pure (add_attributes a1 a2)
  comp_base {α} [BEq α] (x1 x2 : α) : OptionT M α :=
    if x1 == x2 then pure x2 else failure
  comp_array_size (sz1 sz2 : Option Int64) : OptionT M (Option Int64) :=
    match sz1, sz2 with
    | none, _ => pure sz2
    | _, none => pure sz1
    | some n1, some n2 => if n1 == n2 then pure (some n2) else failure
  comp_conv (p : Ident × Typ) : OptionT M Unit := do
    match ← (unroll env p.2 : M Typ) with
    | .TInt kind _ =>
        match kind with
        | .IBool | .IChar | .ISChar | .IUChar | .IShort | .IUShort => failure
        | _ => pure ()
    | .TFloat .FFloat _ => failure
    | _ => pure ()
  comp (m : AttrHandling) (t1 t2 : Typ) : OptionT M Typ := do
    match t1, t2 with
    | .TVoid a1, .TVoid a2 => return .TVoid (← comp_attr m a1 a2)
    | .TInt ik1 a1, .TInt ik2 a2 =>
        return .TInt (← comp_base ik1 ik2) (← comp_attr m a1 a2)
    | .TFloat fk1 a1, .TFloat fk2 a2 =>
        return .TFloat (← comp_base fk1 fk2) (← comp_attr m a1 a2)
    | .TPtr ty1 a1, .TPtr ty2 a2 =>
        let m' := if m == .AttrIgnoreTop then .AttrCompat else m
        return .TPtr (← comp m' ty1 ty2) (← comp_attr m a1 a2)
    | .TArray ty1 sz1 a1, .TArray ty2 sz2 a2 =>
        return .TArray (← comp m ty1 ty2) (← comp_array_size sz1 sz2) (← comp_attr m a1 a2)
    | .TFun ty1 params1 vararg1 a1, .TFun ty2 params2 vararg2 a2 =>
        let (params, vararg) ← (match params1, params2 with
          | none, none => pure (none, false)
          | none, some l2 => do l2.forM comp_conv; pure (params2, vararg2)
          | some l1, none => do l1.forM comp_conv; pure (params1, vararg1)
          | some l1, some l2 => do
              if l1.length != l2.length then failure
              let ps ← (l1.zip l2).mapM fun ((_, ty1), (id2, ty2)) => do
                return (id2, ← comp .AttrIgnoreTop ty1 ty2)
              pure (some ps, ← comp_base vararg1 vararg2) :
            OptionT M (Option (List (Ident × Typ)) × Bool))
        let m' := if m == .AttrIgnoreTop then .AttrCompat else m
        return .TFun (← comp m' ty1 ty2) params vararg (← comp_attr m a1 a2)
    | .TNamed .., _ => comp m (← (unroll env t1 : M Typ)) t2
    | _, .TNamed .. => comp m t1 (← (unroll env t2 : M Typ))
    | .TStruct s1 a1, .TStruct s2 a2 => return .TStruct (← comp_base s1 s2) (← comp_attr m a1 a2)
    | .TUnion s1 a1, .TUnion s2 a2 => return .TUnion (← comp_base s1 s2) (← comp_attr m a1 a2)
    | .TEnum s1 a1, .TEnum s2 a2 => return .TEnum (← comp_base s1 s2) (← comp_attr m a1 a2)
    | .TEnum s a1, .TInt ik a2 =>
        if ik == enum_ikind then return .TEnum s (← comp_attr m a1 a2) else failure
    | .TInt ik a2, .TEnum s a1 =>
        if ik == enum_ikind then return .TEnum s (← comp_attr m a1 a2) else failure
    | _, _ => failure

partial def equal_types (env : Env.T) (t1 t2 : Typ) : M Bool := do
  match t1, t2 with
  | .TVoid a1, .TVoid a2 => return a1 == a2
  | .TInt ik1 a1, .TInt ik2 a2 => return ik1 == ik2 && a1 == a2
  | .TFloat fk1 a1, .TFloat fk2 a2 => return fk1 == fk2 && a1 == a2
  | .TPtr ty1 a1, .TPtr ty2 a2 => return a1 == a2 && (← equal_types env ty1 ty2)
  | .TArray ty1 sz1 a1, .TArray ty2 sz2 a2 =>
      let size := match sz1, sz2 with
        | none, none => true
        | some s1, some s2 => s1 == s2
        | _, _ => false
      return size && a1 == a2 && (← equal_types env ty1 ty2)
  | .TFun ty1 params1 vararg1 a1, .TFun ty2 params2 vararg2 a2 =>
      let params ← match params1, params2 with
        | none, none => pure true
        | none, some _ | some _, none => pure false
        | some l1, some l2 =>
            if l1.length != l2.length then pure false
            else (l1.zip l2).allM fun ((_, t1), (_, t2)) => equal_types env t1 t2
      return params && a1 == a2 && vararg1 == vararg2 && (← equal_types env ty1 ty2)
  | .TNamed .., _ => equal_types env (← unroll env t1) t2
  | _, .TNamed .. => equal_types env t1 (← unroll env t2)
  | .TStruct s1 a1, .TStruct s2 a2 | .TUnion s1 a1, .TUnion s2 a2
  | .TEnum s1 a1, .TEnum s2 a2 => return s1 == s2 && a1 == a2
  | _, _ => return false

/-- Check whether two types are compatible. -/
def compatible_types (mode : AttrHandling) (env : Env.T) (t1 t2 : Typ) : M Bool := do
  return (← combine_types mode env t1 t2).isSome

/-! ### Sizes and alignments -/

/-- Natural alignment, in bytes -/
def alignof_ikind (ik : IKind) : M Int := do
  let c ← getConfig
  return match ik with
  | .IBool | .IChar | .ISChar | .IUChar => 1
  | .IInt | .IUInt => c.alignof_int
  | .IShort | .IUShort => c.alignof_short
  | .ILong | .IULong => c.alignof_long
  | .ILongLong | .IULongLong => c.alignof_longlong

def alignof_fkind (fk : FKind) : M Int := do
  let c ← getConfig
  return match fk with
  | .FFloat16 => 2
  | .FFloat => c.alignof_float
  | .FDouble => c.alignof_double
  | .FLongDouble => c.alignof_longdouble

/-- Return natural alignment of given type, or `none` if the type is
    incomplete -/
partial def alignof (env : Env.T) (t : Typ) : M (Option Int) := do
  let a := alignas_attribute (← attributes_of_type env t)
  if a > 0 then return some a
  let c ← getConfig
  match t with
  | .TVoid _ => return c.alignof_void
  | .TInt ik _ => return some (← alignof_ikind ik)
  | .TFloat fk _ => return some (← alignof_fkind fk)
  | .TPtr _ _ => return some c.alignof_ptr
  | .TArray ty _ _ => alignof env ty
  | .TFun .. => return c.alignof_fun
  | .TNamed _ _ => alignof env (← unroll env t)
  | .TStruct name _ => return (← Env.find_struct env name).ci_alignof
  | .TUnion name _ => return (← Env.find_union env name).ci_alignof
  | .TEnum _ _ => return some (← alignof_ikind enum_ikind)

/-- Compute the natural alignment of a struct or union. -/
def alignof_struct_union (env : Env.T) (members : List Field) : M (Option Int) := do
  let mut al : Int := 1
  for m in members do
    if m.fld_name == "" then continue
    match ← alignof env m.fld_typ with
    | none => return none
    | some a => al := max a al
  return some al

/-- `align x boundary` (boundary must be a power of 2) -/
def align (x boundary : Int) : Int :=
  (x + boundary - 1) / boundary * boundary

/-- Size of, in bytes -/
def sizeof_ikind (ik : IKind) : M Int := do
  let c ← getConfig
  return match ik with
  | .IBool | .IChar | .ISChar | .IUChar => 1
  | .IInt | .IUInt => c.sizeof_int
  | .IShort | .IUShort => c.sizeof_short
  | .ILong | .IULong => c.sizeof_long
  | .ILongLong | .IULongLong => c.sizeof_longlong

def sizeof_fkind (fk : FKind) : M Int := do
  let c ← getConfig
  return match fk with
  | .FFloat16 => 2
  | .FFloat => c.sizeof_float
  | .FDouble => c.sizeof_double
  | .FLongDouble => c.sizeof_longdouble

/-- OCaml's `max_int` (63-bit integers). -/
def max_int : Int := 2 ^ 62 - 1

/-- Overflow-avoiding multiplication of an int64 and an int, with result in
    type int. -/
def cautious_mul (a : Int64) (b : Int) : Option Int :=
  if b == 0 || a.toInt ≤ max_int / b then some (a.toInt * b) else none

/-- Return size of type, in bytes, or `none` if the type is incomplete -/
partial def sizeof (env : Env.T) (t : Typ) : M (Option Int) := do
  let c ← getConfig
  match t with
  | .TVoid _ => return c.sizeof_void
  | .TInt ik _ => return some (← sizeof_ikind ik)
  | .TFloat fk _ => return some (← sizeof_fkind fk)
  | .TPtr _ _ => return some c.sizeof_ptr
  | .TArray _ none _ => return none
  | .TArray ty (some n) _ =>
      match ← sizeof env ty with
      | none => return none
      | some s =>
        match cautious_mul n s with
        | some sz => return some sz
        | none =>
            error no_loc s!"sizeof({Cprint.toText (Cprint.typ {} t)}) overflows"
            return some 1
  | .TFun .. => return c.sizeof_fun
  | .TNamed _ _ => sizeof env (← unroll env t)
  | .TStruct name _ => return (← Env.find_struct env name).ci_sizeof
  | .TUnion name _ => return (← Env.find_union env name).ci_sizeof
  | .TEnum _ _ => return some (← sizeof_ikind enum_ikind)

/-- Compute the size of a union (max of the sizes of fields). -/
def sizeof_union (env : Env.T) (members : List Field) : M (Option Int) := do
  let mut sz : Int := 0
  for m in members do
    match ← sizeof env m.fld_typ with
    | none => return none
    | some s => sz := max sz s
  return some sz

/-- Compute the size (in bits) of a struct and the byte offset of the
    members (most recent first).  `ma` is the maximal alignment for each
    member (0: ignored). -/
def sizeof_layout_struct (env : Env.T) (members : List Field) (ma : Int) :
    M (Option (Int × List (String × Int))) := do
  let align_bit_offset (pos a : Int) : Int :=
    align pos (8 * (if ma > 0 && a > ma then ma else a))
  let record_field (name : String) (pos : Int) : M (String × Int) := do
    if pos % 8 != 0 then assertFalse "Cutil.sizeof_layout_struct"
    return (name, pos / 8)
  let rec sizeof_rec (pos : Int) (accu : List (String × Int)) :
      List Field → M (Option (Int × List (String × Int)))
    | [] => return some (pos, accu)
    | [m@{ fld_typ := .TArray _ none _, .. }] => do
        match ← alignof env m.fld_typ with
        | some a =>
            let pos := align_bit_offset pos a
            return some (pos, (← record_field m.fld_name pos) :: accu)
        | none => return none
    | m :: rem => do
        match ← alignof env m.fld_typ, ← sizeof env m.fld_typ with
        | some a, some s =>
            match m.fld_bitfield with
            | none =>
                let pos := align_bit_offset pos a
                sizeof_rec (pos + s * 8) ((← record_field m.fld_name pos) :: accu) rem
            | some width =>
                if alignas_attribute (← attributes_of_type env m.fld_typ) != 0 then
                  assertFalse "Cutil.sizeof_layout_struct (bitfield)"
                let curr := pos / (a * 8) * (a * 8)
                let next := curr + s * 8
                let pos' :=
                  if width ≤ 0 then align pos (a * 8)
                  else if pos + width ≤ next then pos + width
                  else next + width
                sizeof_rec pos' accu rem
        | _, _ => return none
  sizeof_rec 0 [] members

def sizeof_struct (env : Env.T) (members : List Field) (ma : Int) : M (Option Int) := do
  match ← sizeof_layout_struct env members ma with
  | none => return none
  | some (bitsize, _) => return some ((bitsize + 7) / 8)

/-- Compute the offsets of all non-bitfield members of a struct. -/
def struct_layout (env : Env.T) (attrs : Attributes) (members : List Field) :
    M (List (String × Int)) := do
  let (ma, _, _) := packing_parameters attrs
  match ← sizeof_layout_struct env members ma with
  | some (_, offsets) => return offsets
  | none => return []

/-- Compute the offset of a struct member -/
def offsetof (env : Env.T) (ty : Typ) (field : Field) : M Int := do
  match ← unroll env ty with
  | .TStruct id _ =>
      let str ← Env.find_struct env id
      let offsets ← struct_layout env str.ci_attr str.ci_members
      match offsets.lookup field.fld_name with
      | some o => return o
      | none => throw (.EnvError (.No_member id.name "struct" field.fld_name))
  | .TUnion .. => return 0
  | _ => assertFalse "Cutil.offsetof"

/-- Determine whether a type is incomplete -/
def incomplete_type (env : Env.T) (t : Typ) : M Bool := do
  match ← unroll env t with
  | .TVoid _ => return true
  | _ => return (← sizeof env t).isNone

/-! Computing composite_info records -/

def composite_info_decl (su : StructOrUnion) (attr : Attributes) : CompositeInfo :=
  { ci_kind := su, ci_members := [], ci_alignof := none, ci_sizeof := none,
    ci_attr := attr }

def composite_info_def (env : Env.T) (su : StructOrUnion) (attr : Attributes)
    (m : List Field) : M CompositeInfo := do
  let (max_field_align, min_struct_align, _) := packing_parameters attr
  let attr_align := alignas_attribute attr
  let natural_align ← alignof_struct_union env m
  let al :=
    if attr_align > 0 then some attr_align
    else if su == .Union then natural_align
    else match natural_align with
      | none => none
      | some a =>
          let a := if max_field_align > 0 && a > max_field_align then max_field_align else a
          let a := if min_struct_align > 0 && a < min_struct_align then min_struct_align else a
          some a
  let sz ← match su with
    | .Struct => sizeof_struct env m max_field_align
    | .Union => sizeof_union env m
  return { ci_kind := su, ci_members := m, ci_alignof := al,
           ci_sizeof := match sz, al with
             | some s, some a => some (align s a)
             | _, _ => none,
           ci_attr := attr }

/-- Is an integer `v` representable in `n` bits, signed or unsigned? -/
def int_representable (v : Int64) (nbits : Int) (sgn : Bool) : Bool :=
  if nbits ≥ 64 then true else
  if sgn then
    let p : Int64 := (1 : Int64) <<< (Int64.ofInt (nbits - 1)); Int64.neg p ≤ v && v < p
  else
    0 ≤ v && v < (1 : Int64) <<< (Int64.ofInt nbits)

def valid_array_size (env : Env.T) (ty : Typ) (v : Int64) : M Bool := do
  match ← sizeof env ty with
  | none => return true
  | some sz =>
      let sz := Int64.ofInt sz
      let ptr_bits := (← getConfig).sizeof_ptr * 8 - 1
      if sz == 0 || v ≤ Int64.maxValue / sz then
        return int_representable (sz * v) ptr_bits true
      else return false

/-- Type of a function definition -/
def fundef_typ (fd : Fundef) : Typ :=
  .TFun fd.fd_ret (some fd.fd_params) fd.fd_vararg fd.fd_attrib

/-- Signedness of integer kinds -/
def is_signed_ikind (ik : IKind) : M Bool := do
  match ik with
  | .IBool => return false
  | .IChar => return (← getConfig).char_signed
  | .ISChar => return true
  | .IUChar => return false
  | .IInt => return true
  | .IUInt => return false
  | .IShort => return true
  | .IUShort => return false
  | .ILong => return true
  | .IULong => return false
  | .ILongLong => return true
  | .IULongLong => return false

/-- Conversion to unsigned ikind -/
def unsigned_ikind_of : IKind → IKind
  | .IBool => .IBool
  | .IChar | .ISChar | .IUChar => .IUChar
  | .IInt | .IUInt => .IUInt
  | .IShort | .IUShort => .IUShort
  | .ILong | .IULong => .IULong
  | .ILongLong | .IULongLong => .IULongLong

/-- Conversion to signed ikind -/
def signed_ikind_of : IKind → IKind
  | .IBool => .IBool
  | .IChar | .ISChar | .IUChar => .ISChar
  | .IInt | .IUInt => .IInt
  | .IShort | .IUShort => .IShort
  | .ILong | .IULong => .ILong
  | .ILongLong | .IULongLong => .ILongLong

/-! Some classification functions over types -/

def is_void_type (env : Env.T) (t : Typ) : M Bool := do
  match ← unroll env t with | .TVoid _ => return true | _ => return false

def is_integer_type (env : Env.T) (t : Typ) : M Bool := do
  match ← unroll env t with
  | .TInt .. | .TEnum .. => return true
  | _ => return false

def is_float_type (env : Env.T) (t : Typ) : M Bool := do
  match ← unroll env t with | .TFloat .. => return true | _ => return false

def is_arith_type (env : Env.T) (t : Typ) : M Bool := do
  match ← unroll env t with
  | .TInt .. | .TFloat .. | .TEnum .. => return true
  | _ => return false

def is_pointer_type (env : Env.T) (t : Typ) : M Bool := do
  match ← unroll env t with | .TPtr .. => return true | _ => return false

def is_scalar_type (env : Env.T) (t : Typ) : M Bool := do
  match ← unroll env t with
  | .TInt .. | .TFloat .. | .TPtr .. | .TArray .. | .TFun .. | .TEnum .. => return true
  | _ => return false

def is_composite_type (env : Env.T) (t : Typ) : M Bool := do
  match ← unroll env t with
  | .TStruct .. | .TUnion .. => return true
  | _ => return false

def is_array_type (env : Env.T) (t : Typ) : M Bool := do
  match ← unroll env t with | .TArray .. => return true | _ => return false

def is_function_type (env : Env.T) (t : Typ) : M Bool := do
  match ← unroll env t with | .TFun .. => return true | _ => return false

def is_anonymous_composite : Typ → Bool
  | .TStruct id _ | .TUnion id _ => id.name == ""
  | _ => false

def is_anonymous_type : Typ → Bool
  | .TEnum id _ | .TStruct id _ | .TUnion id _ => id.name == ""
  | _ => false

def is_function_pointer_type (env : Env.T) (t : Typ) : M Bool := do
  match ← unroll env t with
  | .TPtr ty _ => is_function_type env ty
  | _ => return false

/-- Find the info for a field access -/
def field_of_dot_access (env : Env.T) (t : Typ) (m : String) : M Field := do
  let m ← match ← unroll env t with
    | .TStruct id _ => Env.find_struct_member env id m
    | .TUnion id _ => Env.find_union_member env id m
    | _ => assertFalse "Cutil.field_of_dot_access"
  match m.reverse with
  | f :: _ => return f
  | [] => throw (.Failure "hd")

def field_of_arrow_access (env : Env.T) (t : Typ) (m : String) : M Field := do
  match ← unroll env t with
  | .TPtr t _ | .TArray t _ _ => field_of_dot_access env t m
  | _ => assertFalse "Cutil.field_of_arrow_access"

/-- Ranking of integer kinds -/
def integer_rank : IKind → Int
  | .IBool => 1
  | .IChar | .ISChar | .IUChar => 2
  | .IShort | .IUShort => 3
  | .IInt | .IUInt => 4
  | .ILong | .IULong => 5
  | .ILongLong | .IULongLong => 6

/-- Ranking of float kinds -/
def float_rank : FKind → Int
  | .FFloat16 => 0
  | .FFloat => 1
  | .FDouble => 2
  | .FLongDouble => 3

/-- Test for qualified array types -/
def is_qualified_array : Typ → Bool
  | .TArray ty _ attr => attr.any attr_is_standard || is_qualified_array ty
  | .TPtr ty _ => is_qualified_array ty
  | .TFun ty_ret _ _ _ => is_qualified_array ty_ret
  | _ => false

/-- Array and function types "decay" to pointer types in many cases -/
def pointer_decay (env : Env.T) (t : Typ) : M Typ := do
  match ← unroll env t with
  | .TArray ty _ _ => return .TPtr ty []
  | ty@(.TFun ..) => return .TPtr ty []
  | t => return t

/-- The usual unary conversions (H&S 6.3.3) -/
def unary_conversion (env : Env.T) (t : Typ) : M Typ := do
  match ← unroll env t with
  | .TInt kind _ =>
      match kind with
      | .IBool | .IChar | .ISChar | .IUChar | .IShort | .IUShort => return .TInt .IInt []
      | _ => return .TInt kind []
  | .TEnum _ _ => return .TInt enum_ikind []
  | .TArray ty _ _ => return .TPtr ty []
  | ty@(.TFun ..) => return .TPtr ty []
  | .TFloat kind _ => return .TFloat kind []
  | .TPtr ty _ => return .TPtr ty []
  | _ => return t

/-- The usual binary conversions (H&S 6.3.4).  Applies only to arithmetic
    types.  Return the type to which both sides are to be converted. -/
def binary_conversion (env : Env.T) (t1 t2 : Typ) : M Typ := do
  let t1 ← unary_conversion env t1
  let t2 ← unary_conversion env t2
  let isIF : Typ → Bool := fun | .TInt .. | .TFloat .. => true | _ => false
  let isI : Typ → Bool := fun | .TInt .. => true | _ => false
  let u1 ← unroll env t1
  let u2 ← unroll env t2
  match u1, u2 with
  | .TFloat .FLongDouble _, _ => if isIF u2 then return t1 else assertFalse "binary_conversion"
  | _, .TFloat .FLongDouble _ => if isIF u1 then return t2 else assertFalse "binary_conversion"
  | .TFloat .FDouble _, _ => if isIF u2 then return t1 else assertFalse "binary_conversion"
  | _, .TFloat .FDouble _ => if isIF u1 then return t2 else assertFalse "binary_conversion"
  | .TFloat .FFloat _, _ => if isIF u2 then return t1 else assertFalse "binary_conversion"
  | _, .TFloat .FFloat _ => if isIF u1 then return t2 else assertFalse "binary_conversion"
  | .TFloat .FFloat16 _, _ => if isIF u2 then return t1 else assertFalse "binary_conversion"
  | _, .TFloat .FFloat16 _ => if isI u1 then return t2 else assertFalse "binary_conversion"
  | .TInt k1 _, .TInt k2 _ =>
      if k1 == k2 then return t1
      match ← is_signed_ikind k1, ← is_signed_ikind k2 with
      | true, true | false, false =>
          return if integer_rank k1 ≥ integer_rank k2 then t1 else t2
      | false, true =>
          if integer_rank k1 ≥ integer_rank k2 then return t1
          else if (← sizeof_ikind k2) > (← sizeof_ikind k1) then return t2
          else return .TInt (unsigned_ikind_of k2) []
      | true, false =>
          if integer_rank k2 ≥ integer_rank k1 then return t2
          else if (← sizeof_ikind k1) > (← sizeof_ikind k2) then return t1
          else return .TInt (unsigned_ikind_of k1) []
  | _, _ => assertFalse "binary_conversion"

/-- Conversion on function arguments (with prototypes) -/
def argument_conversion (env : Env.T) (t : Typ) : M Typ := do
  match ← unroll env t with
  | .TArray ty _ attr => return .TPtr ty attr
  | ty@(.TFun ..) => return .TPtr ty []
  | _ => return t

/-- Conversion on function arguments (old-style unprototyped, or vararg)
    (H&S 6.3.5) -/
def default_argument_conversion (env : Env.T) (t : Typ) : M Typ := do
  match ← unary_conversion env t with
  | .TFloat .FFloat attr => return .TFloat .FDouble attr
  | t' => return t'

/-- Is the type `Tptr(ty, a)` appropriate for pointer arithmetic? -/
def pointer_arithmetic_ok (env : Env.T) (ty : Typ) : M Bool := do
  match ← unroll env ty with
  | .TVoid _ | .TFun .. => return false
  | _ => return !(← incomplete_type env ty)

/-- The type of `x.fld`. -/
def type_of_member (env : Env.T) (fld : Field) : M Typ := do
  match fld.fld_bitfield with
  | none => return fld.fld_typ
  | some w =>
      let (ik, attr) ← match ← unroll env fld.fld_typ with
        | .TInt ik attr => pure (ik, attr)
        | .TEnum _ attr => pure (enum_ikind, attr)
        | _ => assertFalse "Cutil.type_of_member"
      if w < (← sizeof_ikind ik) * 8 then return .TInt (signed_ikind_of ik) attr
      else return fld.fld_typ

/-! Special types -/

def find_matching_unsigned_ikind (sz : Int) : M IKind := do
  let c ← getConfig
  if sz ≤ 0 then assertFalse "find_matching_unsigned_ikind"
  if sz == c.sizeof_short then return .IUShort
  else if sz == c.sizeof_int then return .IUInt
  else if sz == c.sizeof_long then return .IULong
  else if sz == c.sizeof_longlong then return .IULongLong
  else assertFalse "find_matching_unsigned_ikind"

def find_matching_signed_ikind (sz : Int) : M IKind := do
  let c ← getConfig
  if sz ≤ 0 then assertFalse "find_matching_signed_ikind"
  if sz == c.sizeof_int then return .IInt
  else if sz == c.sizeof_long then return .ILong
  else if sz == c.sizeof_longlong then return .ILongLong
  else assertFalse "find_matching_signed_ikind"

def wchar_ikind : M IKind := do return (← getConfig).wchar_ikind
def size_t_ikind : M IKind := do find_matching_unsigned_ikind (← getConfig).sizeof_size_t
def ptr_t_ikind : M IKind := do find_matching_unsigned_ikind (← getConfig).sizeof_ptr
def ptrdiff_t_ikind : M IKind := do find_matching_signed_ikind (← getConfig).sizeof_ptrdiff_t

/-- The type of a constant (the length of a `CStr` is its number of bytes). -/
def type_of_constant : Constant → Typ
  | .CInt _ ik _ => .TInt ik []
  | .CFloat _ fk => .TFloat fk []
  | .CStr s => .TArray (.TInt .IChar []) (some (Int64.ofNat (s.utf8ByteSize + 1))) []
  | .CWStr s ik => .TArray (.TInt ik []) (some (Int64.ofNat (s.length + 1))) []
  | .CEnum _ _ => .TInt .IInt []

/-- Check that a C expression is a lvalue -/
partial def is_lvalue (e : Exp) : Bool :=
  match e.edesc with
  | .EVar _ => true
  | .EConst (.CStr _) | .EConst (.CWStr ..) => true
  | .EUnop .Oderef _ | .EUnop (.Oarrow _) _ => true
  | .EUnop (.Odot _) e' => is_lvalue e'
  | .EBinop .Oindex _ _ _ => true
  | .ECompound .. => true
  | _ => false

/-- Is a type const-qualified (or a composite with a const member)? -/
partial def is_const_type (env : Env.T) (ty : Typ) : M Bool := do
  if (← attributes_of_type env ty).contains .AConst then return true
  match ← unroll env ty with
  | .TStruct s _ =>
      let ci ← Env.find_struct env s
      ci.ci_members.anyM fun m => is_const_type env m.fld_typ
  | .TUnion s _ =>
      let ci ← Env.find_union env s
      ci.ci_members.anyM fun m => is_const_type env m.fld_typ
  | _ => return false

/-- Check that a C expression is a modifiable l-value. -/
def is_modifiable_lvalue (env : Env.T) (e : Exp) : M Bool := do
  if !is_lvalue e then return false
  if ← incomplete_type env e.etyp then return false
  if ← is_const_type env e.etyp then return false
  match ← unroll env e.etyp with
  | .TFun .. | .TArray .. => return false
  | _ => return true

/-- Check that a C expression is the literal "0", which can be used as a
    pointer. -/
def is_literal_0 (e : Exp) : Bool :=
  match e.edesc with
  | .EConst (.CInt 0 _ _) => true
  | _ => false

/-- Check that a C statement is a debug annotation -/
def is_debug_stmt (s : Stmt) : Bool :=
  match s.sdesc with
  | .Sdo (.mk (.ECall (.mk (.EVar id) _) _) _) => id.name == "__builtin_debug"
  | _ => false

def is_call_to_fun (e : Exp) (s : String) : Bool :=
  match e.edesc with
  | .EVar id => id.name == s
  | _ => false

def is_bitfield (env : Env.T) (e : Exp) : M Bool := do
  match e.edesc with
  | .EUnop (.Odot f) b => return (← field_of_dot_access env b.etyp f).fld_bitfield.isSome
  | .EUnop (.Oarrow f) b => return (← field_of_arrow_access env b.etyp f).fld_bitfield.isSome
  | _ => return false

def contains_flex_array_mem (env : Env.T) (ty : Typ) : M Bool := do
  match ← unroll env ty with
  | .TStruct id _ =>
      let ci ← Env.find_struct env id
      let rec check_mem : List Field → Bool
        | [] => false
        | [{ fld_typ := .TArray _ none _, .. }] => true
        | _ :: rem => check_mem rem
      return check_mem ci.ci_members
  | _ => return false

/-- Assignment compatibility check over attributes. -/
def valid_assignment_attr (afrom ato : Attributes) : Bool :=
  let (afromstd, _) := afrom.partition attr_is_standard
  let (atostd, _) := ato.partition attr_is_standard
  incl_attributes afromstd atostd

/-- Check that an assignment is allowed -/
def valid_assignment (env : Env.T) (from_ : Exp) (tto : Typ) : M Bool := do
  match ← pointer_decay env from_.etyp, ← pointer_decay env tto with
  | .TInt .., .TInt .. | .TInt .., .TFloat .. | .TInt .., .TEnum ..
  | .TFloat .., .TInt .. | .TFloat .., .TFloat .. | .TFloat .., .TEnum ..
  | .TEnum .., .TInt .. | .TEnum .., .TFloat .. | .TEnum .., .TEnum .. => return true
  | .TInt .., .TPtr .. => return is_literal_0 from_
  | .TPtr ty _, .TPtr ty' _ =>
      return valid_assignment_attr (← attributes_of_type env ty) (← attributes_of_type env ty')
        && ((← is_void_type env ty) || (← is_void_type env ty')
            || (← compatible_types .AttrIgnoreTop env ty ty'))
  | .TStruct s _, .TStruct s' _ => return s == s'
  | .TUnion s _, .TUnion s' _ => return s == s'
  | _, _ => return false

/-- Check that a cast is allowed -/
def valid_cast (env : Env.T) (tfrom tto : Typ) : M Bool := do
  let f ← unroll env tfrom
  let t ← unroll env tto
  match t with
  | .TVoid _ => return true
  | _ =>
    let fromIntPtr := match f with
      | .TInt .. | .TPtr .. | .TArray .. | .TFun .. | .TEnum .. => true | _ => false
    let toIntPtr := match t with | .TInt .. | .TPtr .. | .TEnum .. => true | _ => false
    let fromArith := match f with | .TInt .. | .TFloat .. | .TEnum .. => true | _ => false
    let toArith := match t with | .TInt .. | .TFloat .. | .TEnum .. => true | _ => false
    return (fromIntPtr && toIntPtr) || (fromArith && toArith)

/-- Check that the cast from `tfrom` to `tto` is an integer to pointer
    conversion -/
def int_pointer_conversion (env : Env.T) (tfrom tto : Typ) : M Bool := do
  match ← unroll env tfrom, ← unroll env tto with
  | .TInt .., .TPtr .. | .TEnum .., .TPtr .. | .TPtr .., .TInt .. | .TPtr .., .TEnum .. =>
      return true
  | _, _ => return false

/-! Smart constructors -/

/-- Construct an integer constant -/
def intconst (v : Int64) (ik : IKind) : Exp := .mk (.EConst (.CInt v ik "")) (.TInt ik [])

/-- Construct the 0 float constant of double type -/
def floatconst0 : Exp :=
  .mk (.EConst (.CFloat { hex := false, intPart := "0", fracPart := "0", exp := "0" } .FDouble))
    (.TFloat .FDouble [])

/-- Construct a cast expression -/
def ecast (ty : Typ) (e : Exp) : Exp := .mk (.ECast ty e) ty

/-- Construct the literal "0" with void * type -/
def nullconst : Exp := ecast (.TPtr (.TVoid []) []) (intconst 0 .IInt)

/-- Construct an assignment expression -/
def eassign (e1 e2 : Exp) : Exp := .mk (.EBinop .Oassign e1 e2 e1.etyp) e1.etyp

/-- Construct a "," expression.  Reassociate to the left. -/
partial def ecomma (e1 e2 : Exp) : Exp :=
  match e2.edesc with
  | .EBinop .Ocomma e2' e2'' _ => ecomma (ecomma e1 e2') e2''
  | _ => .mk (.EBinop .Ocomma e1 e2 e2.etyp) e2.etyp

/-- Construct a cascade of "," expressions. -/
def ecommalist (el : List Exp) (e : Exp) : Exp :=
  match el with
  | [] => e
  | e1 :: el => ecomma (el.foldl ecomma e1) e

/-- Construct an address-of expression. -/
partial def eaddrof (e : Exp) : Exp :=
  match e.edesc with
  | .EUnop .Oderef e1 => e1
  | .EBinop .Ocomma e1 e2 _ => ecomma e1 (eaddrof e2)
  | .EConditional e1 e2 e3 => .mk (.EConditional e1 (eaddrof e2) (eaddrof e3)) (.TPtr e.etyp [])
  | _ => .mk (.EUnop .Oaddrof e) (.TPtr e.etyp [])

/-- Construct a sequence -/
def sseq (loc : Location) (s1 s2 : Stmt) : Stmt :=
  match s1.sdesc, s2.sdesc with
  | .Sskip, _ => s2
  | _, .Sskip => s1
  | _, .Sblock sl => .mk (.Sblock (s1 :: sl)) loc
  | _, _ => .mk (.Sseq s1 s2) loc

/-- Construct an assignment statement -/
def sassign (loc : Location) (lv rv : Exp) : Stmt := .mk (.Sdo (eassign lv rv)) loc

/-- Dummy skip statement -/
def sskip : Stmt := .mk .Sskip no_loc

/-- Print a location -/
def printloc (loc : Location) : String :=
  if loc.1 != "" then s!"{loc.1}:{loc.2}: " else ""

/-- Format a location -/
def formatloc := printloc

/-- Generate the default initializer for the given type (`none` for the
    exception `No_default_init`). -/
partial def default_init (env : Env.T) (ty : Typ) : M (Option Init) := (go ty).run
where
  go (ty : Typ) : OptionT M Init := do
    match ← (unroll env ty : M Typ) with
    | .TInt .. | .TEnum .. => return .Init_single (intconst 0 .IInt)
    | .TFloat .. => return .Init_single floatconst0
    | .TPtr .. => return .Init_single nullconst
    | .TArray .. => return .Init_array []
    | .TStruct id _ =>
        let ci ← (Env.find_struct env id : M CompositeInfo)
        let flds ← ci.ci_members.filterMapM fun f1 =>
          if f1.fld_name == "" then pure none
          else do return some (f1, ← go f1.fld_typ)
        return .Init_struct id flds
    | .TUnion id _ =>
        let ci ← (Env.find_union env id : M CompositeInfo)
        match ci.ci_members.find? (·.fld_name != "") with
        | none => failure
        | some fld => return .Init_union id fld (← go fld.fld_typ)
    | _ => failure

/-! Substitution of variables by expressions -/

mutual
partial def subst_expr (phi : IdentMap Exp) (e : Exp) : Exp :=
  match e.edesc with
  | .EConst _ | .ESizeof _ | .EAlignof _ => e
  | .EVar x => (phi.get? x).getD e
  | .EUnop op e1 => e.withDesc (.EUnop op (subst_expr phi e1))
  | .EBinop op e1 e2 ty => e.withDesc (.EBinop op (subst_expr phi e1) (subst_expr phi e2) ty)
  | .EConditional e1 e2 e3 =>
      e.withDesc (.EConditional (subst_expr phi e1) (subst_expr phi e2) (subst_expr phi e3))
  | .ECast ty e1 => e.withDesc (.ECast ty (subst_expr phi e1))
  | .ECompound ty i => e.withDesc (.ECompound ty (subst_init phi i))
  | .ECall e1 el => e.withDesc (.ECall (subst_expr phi e1) (el.map (subst_expr phi)))

partial def subst_init (phi : IdentMap Exp) : Init → Init
  | .Init_single e => .Init_single (subst_expr phi e)
  | .Init_array il => .Init_array (il.map (subst_init phi))
  | .Init_struct name fl => .Init_struct name (fl.map fun (f, i) => (f, subst_init phi i))
  | .Init_union name f i => .Init_union name f (subst_init phi i)
end

def subst_decl (phi : IdentMap Exp) : Decl → Decl
  | .mk sto name ty optinit => .mk sto name ty (optinit.map (subst_init phi))

partial def subst_stmt (phi : IdentMap Exp) (s : Stmt) : Stmt :=
  .mk (match s.sdesc with
    | .Sskip | .Sbreak | .Scontinue | .Sgoto _ => s.sdesc
    | .Sdo e => .Sdo (subst_expr phi e)
    | .Sseq s1 s2 => .Sseq (subst_stmt phi s1) (subst_stmt phi s2)
    | .Sif e s1 s2 => .Sif (subst_expr phi e) (subst_stmt phi s1) (subst_stmt phi s2)
    | .Swhile e s1 => .Swhile (subst_expr phi e) (subst_stmt phi s1)
    | .Sdowhile s1 e => .Sdowhile (subst_stmt phi s1) (subst_expr phi e)
    | .Sfor s1 e s2 s3 =>
        .Sfor (subst_stmt phi s1) (subst_expr phi e) (subst_stmt phi s2) (subst_stmt phi s3)
    | .Sswitch e s1 => .Sswitch (subst_expr phi e) (subst_stmt phi s1)
    | .Slabeled l s1 => .Slabeled l (subst_stmt phi s1)
    | .Sreturn none => s.sdesc
    | .Sreturn (some e) => .Sreturn (some (subst_expr phi e))
    | .Sblock sl => .Sblock (sl.map (subst_stmt phi))
    | .Sdecl d => .Sdecl (subst_decl phi d)
    | .Sasm attr template outputs inputs clob =>
        let op : AsmOperand → AsmOperand := fun (lbl, cstr, e) => (lbl, cstr, subst_expr phi e)
        .Sasm attr template (outputs.map op) (inputs.map op) clob) s.sloc

def is_volatile_variable (env : Env.T) (exp : Exp) : M Bool := do
  match exp.edesc with
  | .EVar _ => return (← attributes_of_type env exp.etyp).contains .AVolatile
  | _ => return false

end Cutil
end CParser
end CC
