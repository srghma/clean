/-
  The abstract domain of the value analysis — port of the abstract-value
  part of `backend/ValueDomain.v` (block classifications, `abool`, `aptr`,
  `aval` and all the abstract operators on them).  The abstract memory
  (`ablock`, `amem`), the register environments (`AE`) and the dataflow
  lattice (`VA`) are in `ValueDomainMem.lean`.

  Ported (definitions): `block_class`, `block_classification`, `bc_below`,
  `abool`, `cmatch`, `club`, `cnot`, `aptr`, `pmatch`, `pge`, `plub`,
  `pincl`, `padd`, `psub`, `poffset`, `cmp_different_blocks`, `pcmp`,
  `aval`, `Vtop`, `is_uns`, `is_sgn`, `vmatch`, `usize`, `ssize`, `urange`,
  `srange`, `provenance`, `ntop`, `ntop1`, `ntop2`, `int_provenance`,
  `long_provenance`, `uns`, `sgn`, `vge`, `uns1`, `vlub_int`, `vlub`,
  `aptr_of_aval`, `vplub`, `vpincl`, `vincl`, `genv_match`, the generic
  `unop_*`/`binop_*`, every abstract arithmetic, logical, shift,
  conversion and comparison operator (`shl` … `hiword`), `cmp_intv`,
  `zcmp`, `uintv`, `sintv`, `cmpu_bool`, `cmp_bool`, `cmplu_bool`,
  `cmpl_bool`, `cmpf_bool`, `cmpfs_bool`, `maskzero`, `of_optbool`,
  `resolve_branch`, `add_undef`, `vnormalize_type`, `select`,
  `vnormalize`, `val_of_aval`, `aval_of_val`, `of_xtype`, `pdisjoint`,
  `bc_incr`, `inj_of_bc`.
  Proved: `pge_trans`, `pmatch_ge`, `cmatch_lub_l`, `cmatch_lub_r`,
  `cnot_sound`.

  Not ported: the soundness lemmas of the abstract operators
  (`*_sound`, `vmatch_lub_*`, `vge_lub_*`, …).

  Differences from Rocq:
  * The OCaml parameter `Compopts.va_strict` is an explicit Boolean
    argument `strict` of the definitions that depend on it.
  * `Z.log2`, `two_p` and `Z.abs` are `zlog2`, `twoP` and `Int.natAbs`.
  * The `Z` bit counts given to `Int.zero_ext`/`Int.sign_ext` are
    converted with `Int.toNat` (as in `Op.lean`).
-/
import CCLib.common.Memory
import CCLib.common.Globalenvs
import CCLib.aarch64.Conventions1

namespace CC
namespace ValueDomain

/-! ## Block classification -/

/-- `ValueDomain.block_class` -/
inductive BlockClass where
  | BCinvalid
  | BCglob (id : Ident)
  | BCstack
  | BCother
  deriving DecidableEq, Repr

/-- `ValueDomain.block_classification` -/
structure BlockClassification where
  bc_img : Block → BlockClass
  bc_stack : ∀ b1 b2, bc_img b1 = .BCstack → bc_img b2 = .BCstack → b1 = b2
  bc_glob : ∀ b1 b2 id, bc_img b1 = .BCglob id → bc_img b2 = .BCglob id → b1 = b2

instance : CoeFun BlockClassification (fun _ => Block → BlockClass) := ⟨BlockClassification.bc_img⟩

/-- `ValueDomain.bc_below` -/
def bcBelow (bc : BlockClassification) (bound : Block) : Prop :=
  ∀ b, bc b ≠ .BCinvalid → b < bound

/-! ## Abstract booleans (results of conditions) -/

/-- `ValueDomain.abool` -/
inductive Abool where
  /-- always `None` (undefined) -/
  | Bnone
  /-- always `Some b` -/
  | Just (b : Bool)
  /-- either `None` or `Some b` -/
  | Maybe (b : Bool)
  /-- unknown -/
  | Btop
  deriving DecidableEq, Repr

/-- `ValueDomain.cmatch` -/
inductive Cmatch : Option Bool → Abool → Prop where
  | none : Cmatch none .Bnone
  | just (b) : Cmatch (some b) (.Just b)
  | maybe_none (b) : Cmatch none (.Maybe b)
  | maybe_some (b) : Cmatch (some b) (.Maybe b)
  | top (ob) : Cmatch ob .Btop

/-- `ValueDomain.club` -/
def club (x y : Abool) : Abool :=
  match x, y with
  | .Bnone, .Bnone => .Bnone
  | .Bnone, .Just b | .Bnone, .Maybe b => .Maybe b
  | .Just b, .Bnone | .Maybe b, .Bnone => .Maybe b
  | .Just b1, .Just b2 => if b1 == b2 then x else .Btop
  | .Maybe b1, .Maybe b2 => if b1 == b2 then x else .Btop
  | .Maybe b1, .Just b2 => if b1 == b2 then x else .Btop
  | .Just b1, .Maybe b2 => if b1 == b2 then y else .Btop
  | _, _ => .Btop

theorem cmatch_lub_l {ob : Option Bool} {x : Abool} (y : Abool) (h : Cmatch ob x) :
    Cmatch ob (club x y) := by
  cases h <;> cases y <;> simp only [club] <;>
    first
    | constructor
    | (split <;> rename_i h <;> (try simp at h) <;> (try subst h) <;> constructor)

theorem cmatch_lub_r {ob : Option Bool} (x : Abool) {y : Abool} (h : Cmatch ob y) :
    Cmatch ob (club x y) := by
  cases h <;> cases x <;> simp only [club] <;>
    first
    | constructor
    | (split <;> rename_i h <;> (try simp at h) <;> (try subst h) <;> constructor)

/-- `ValueDomain.cnot` -/
def cnot (x : Abool) : Abool :=
  match x with
  | .Just b => .Just (!b)
  | .Maybe b => .Maybe (!b)
  | _ => x

theorem cnot_sound {ob : Option Bool} {x : Abool} (h : Cmatch ob x) :
    Cmatch (ob.map not) (cnot x) := by
  cases h <;> constructor

/-! ## Abstract pointers -/

/-- `ValueDomain.aptr` -/
inductive Aptr where
  /-- empty set of pointers -/
  | Pbot
  /-- into the block of global `id` at offset `ofs` -/
  | Gl (id : Ident) (ofs : Integers.Ptrofs)
  /-- anywhere into the block of global `id` -/
  | Glo (id : Ident)
  /-- into any global variable -/
  | Glob
  /-- into the current stack frame at offset `ofs` -/
  | Stk (ofs : Integers.Ptrofs)
  /-- anywhere into the current stack frame -/
  | Stack
  /-- anywhere but into the current stack frame -/
  | Nonstack
  /-- any valid pointer -/
  | Ptop
  deriving DecidableEq, Repr

section MATCH
variable (bc : BlockClassification)

/-- `ValueDomain.pmatch` -/
inductive Pmatch (b : Block) (ofs : Integers.Ptrofs) : Aptr → Prop where
  | gl (id) : bc b = .BCglob id → Pmatch b ofs (.Gl id ofs)
  | glo (id) : bc b = .BCglob id → Pmatch b ofs (.Glo id)
  | glob (id) : bc b = .BCglob id → Pmatch b ofs .Glob
  | stk : bc b = .BCstack → Pmatch b ofs (.Stk ofs)
  | stack : bc b = .BCstack → Pmatch b ofs .Stack
  | nonstack : bc b ≠ .BCstack → bc b ≠ .BCinvalid → Pmatch b ofs .Nonstack
  | top : bc b ≠ .BCinvalid → Pmatch b ofs .Ptop

end MATCH

/-- `ValueDomain.pge` -/
inductive Pge : Aptr → Aptr → Prop where
  | top (p) : Pge .Ptop p
  | bot (p) : Pge p .Pbot
  | refl (p) : Pge p p
  | glo_gl (id ofs) : Pge (.Glo id) (.Gl id ofs)
  | glob_gl (id ofs) : Pge .Glob (.Gl id ofs)
  | glob_glo (id) : Pge .Glob (.Glo id)
  | ns_gl (id ofs) : Pge .Nonstack (.Gl id ofs)
  | ns_glo (id) : Pge .Nonstack (.Glo id)
  | ns_glob : Pge .Nonstack .Glob
  | stack_stk (ofs) : Pge .Stack (.Stk ofs)

/-- `ValueDomain.pge_trans` -/
theorem pge_trans {p q r : Aptr} (h1 : Pge p q) (h2 : Pge q r) : Pge p r := by
  cases h1 <;> cases h2 <;> constructor

/-- `ValueDomain.pmatch_ge` -/
theorem pmatch_ge {bc : BlockClassification} {b : Block} {ofs : Integers.Ptrofs} {p q : Aptr}
    (hge : Pge p q) (hm : Pmatch bc b ofs q) : Pmatch bc b ofs p := by
  have nonstack_of_glob : ∀ id, bc b = .BCglob id → Pmatch bc b ofs .Nonstack := fun id h =>
    .nonstack (by rw [h]; simp) (by rw [h]; simp)
  cases hge with
  | top =>
      apply Pmatch.top
      cases hm <;> (try (rename_i h; rw [h]; simp)) <;> assumption
  | bot => cases hm
  | refl => exact hm
  | glo_gl => cases hm with | gl _ h => exact .glo _ h
  | glob_gl => cases hm with | gl _ h => exact .glob _ h
  | glob_glo => cases hm with | glo _ h => exact .glob _ h
  | ns_gl => cases hm with | gl _ h => exact nonstack_of_glob _ h
  | ns_glo => cases hm with | glo _ h => exact nonstack_of_glob _ h
  | ns_glob => cases hm with | glob _ h => exact nonstack_of_glob _ h
  | stack_stk => cases hm with | stk h => exact .stack h

/-- `ValueDomain.plub` -/
def plub (p q : Aptr) : Aptr :=
  match p, q with
  | .Pbot, _ => q
  | _, .Pbot => p
  | .Gl id1 ofs1, .Gl id2 ofs2 =>
      if id1 = id2 then (if ofs1 = ofs2 then p else .Glo id1) else .Glob
  | .Gl id1 _, .Glo id2 => if id1 = id2 then q else .Glob
  | .Glo id1, .Gl id2 _ => if id1 = id2 then p else .Glob
  | .Glo id1, .Glo id2 => if id1 = id2 then p else .Glob
  | .Gl _ _, .Glob | .Glo _, .Glob | .Glob, .Glob => .Glob
  | .Glob, .Gl _ _ | .Glob, .Glo _ => .Glob
  | .Gl _ _, .Nonstack | .Glo _, .Nonstack | .Glob, .Nonstack | .Nonstack, .Nonstack => .Nonstack
  | .Nonstack, .Gl _ _ | .Nonstack, .Glo _ | .Nonstack, .Glob => .Nonstack
  | .Stk ofs1, .Stk ofs2 => if ofs1 = ofs2 then p else .Stack
  | .Stk _, .Stack | .Stack, .Stack => .Stack
  | .Stack, .Stk _ => .Stack
  | _, _ => .Ptop

/-- `ValueDomain.pincl` -/
def pincl (p q : Aptr) : Bool :=
  match p, q with
  | .Pbot, _ => true
  | .Gl id1 ofs1, .Gl id2 ofs2 => decide (id1 = id2) && decide (ofs1 = ofs2)
  | .Gl id1 _, .Glo id2 => decide (id1 = id2)
  | .Glo id1, .Glo id2 => decide (id1 = id2)
  | .Gl _ _, .Glob | .Glo _, .Glob | .Glob, .Glob => true
  | .Gl _ _, .Nonstack | .Glo _, .Nonstack | .Glob, .Nonstack | .Nonstack, .Nonstack => true
  | .Stk ofs1, .Stk ofs2 => decide (ofs1 = ofs2)
  | .Stk _, .Stack => true
  | .Stack, .Stack => true
  | _, .Ptop => true
  | _, _ => false

/-- `ValueDomain.padd` -/
def padd (p : Aptr) (n : Integers.Ptrofs) : Aptr :=
  match p with
  | .Gl id ofs => .Gl id (Integers.Ptrofs.add ofs n)
  | .Stk ofs => .Stk (Integers.Ptrofs.add ofs n)
  | _ => p

/-- `ValueDomain.psub` -/
def psub (p : Aptr) (n : Integers.Ptrofs) : Aptr :=
  match p with
  | .Gl id ofs => .Gl id (Integers.Ptrofs.sub ofs n)
  | .Stk ofs => .Stk (Integers.Ptrofs.sub ofs n)
  | _ => p

/-- `ValueDomain.poffset` -/
def poffset (p : Aptr) : Aptr :=
  match p with
  | .Gl id _ => .Glo id
  | .Stk _ => .Stack
  | _ => p

section STRICT
variable (strict : Bool)

/-- `ValueDomain.cmp_different_blocks` -/
def cmpDifferentBlocks (c : Comparison) : Abool :=
  match c with
  | .Ceq => .Maybe false
  | .Cne => .Maybe true
  | _ => if strict then .Bnone else .Btop

/-- `ValueDomain.pcmp` -/
def pcmp (c : Comparison) (p1 p2 : Aptr) : Abool :=
  match p1, p2 with
  | .Pbot, _ | _, .Pbot => .Bnone
  | .Gl id1 ofs1, .Gl id2 ofs2 =>
      if id1 = id2 then .Maybe (Integers.Ptrofs.cmpu c ofs1 ofs2) else .Btop
  | .Stk ofs1, .Stk ofs2 => .Maybe (Integers.Ptrofs.cmpu c ofs1 ofs2)
  | .Gl _ _, .Stk _ | .Glo _, .Stk _ | .Glob, .Stk _ | .Nonstack, .Stk _
  | .Gl _ _, .Stack | .Glo _, .Stack | .Glob, .Stack | .Nonstack, .Stack =>
      cmpDifferentBlocks strict c
  | .Stk _, .Gl _ _ | .Stk _, .Glo _ | .Stk _, .Glob | .Stk _, .Nonstack
  | .Stack, .Gl _ _ | .Stack, .Glo _ | .Stack, .Glob | .Stack, .Nonstack =>
      cmpDifferentBlocks strict c
  | _, _ => .Btop

end STRICT

/-! ## Abstract values -/

/-- `ValueDomain.aval` -/
inductive Aval where
  /-- empty set of values -/
  | Vbot
  /-- exactly `Vint n` -/
  | I (n : Integers.Int)
  /-- `Vint n` or `Vundef` -/
  | IU (n : Integers.Int)
  /-- an `n`-bit unsigned integer, or `Vundef` -/
  | Uns (p : Aptr) (n : Z)
  /-- an `n`-bit signed integer, or `Vundef` -/
  | Sgn (p : Aptr) (n : Z)
  /-- exactly `Vlong n` -/
  | L (n : Integers.Int64)
  /-- exactly `Vfloat f` -/
  | F (f : Floats.Float)
  /-- exactly `Vsingle f` -/
  | FS (f : Floats.Float32)
  /-- any number, or `Vundef` -/
  | Num (p : Aptr)
  /-- a pointer from `p`, or `Vundef` -/
  | Ptr (p : Aptr)
  /-- a pointer from `p`, or a number, or `Vundef` -/
  | Ifptr (p : Aptr)
  deriving DecidableEq, Repr

instance : Inhabited Aval := ⟨.Vbot⟩

/-- `ValueDomain.Vtop` -/
def Vtop : Aval := .Ifptr .Ptop

/-- `ValueDomain.is_uns`: the bits of `i` at positions `≥ n` are zero. -/
def IsUns (n : Z) (i : Integers.Int) : Prop :=
  ∀ m : Nat, (m : Z) < Integers.Int.zwordsize → (m : Z) ≥ n → Integers.Int.testbit i m = false

/-- `ValueDomain.is_sgn`: the bits of `i` at positions `≥ n - 1` are equal
    to the sign bit. -/
def IsSgn (n : Z) (i : Integers.Int) : Prop :=
  ∀ m : Nat, (m : Z) < Integers.Int.zwordsize → (m : Z) ≥ n - 1 →
    Integers.Int.testbit i m = Integers.Int.testbit i 31

section VMATCH
variable (bc : BlockClassification)

/-- `ValueDomain.vmatch` -/
inductive Vmatch : Val → Aval → Prop where
  | i (i) : Vmatch (.Vint i) (.I i)
  | iu (i) : Vmatch (.Vint i) (.IU i)
  | iu_undef (i) : Vmatch .Vundef (.IU i)
  | Uns (p i n) : 0 ≤ n → IsUns n i → Vmatch (.Vint i) (.Uns p n)
  | Uns_undef (p n) : Vmatch .Vundef (.Uns p n)
  | Sgn (p i n) : 0 < n → IsSgn n i → Vmatch (.Vint i) (.Sgn p n)
  | Sgn_undef (p n) : Vmatch .Vundef (.Sgn p n)
  | l (i) : Vmatch (.Vlong i) (.L i)
  | f (f) : Vmatch (.Vfloat f) (.F f)
  | s (f) : Vmatch (.Vsingle f) (.FS f)
  | num_undef (p) : Vmatch .Vundef (.Num p)
  | num_i (i p) : Vmatch (.Vint i) (.Num p)
  | num_l (i p) : Vmatch (.Vlong i) (.Num p)
  | num_f (f p) : Vmatch (.Vfloat f) (.Num p)
  | num_s (f p) : Vmatch (.Vsingle f) (.Num p)
  | ptr (b ofs p) : Pmatch bc b ofs p → Vmatch (.Vptr b ofs) (.Ptr p)
  | ptr_undef (p) : Vmatch .Vundef (.Ptr p)
  | ifptr_undef (p) : Vmatch .Vundef (.Ifptr p)
  | ifptr_i (i p) : Vmatch (.Vint i) (.Ifptr p)
  | ifptr_l (i p) : Vmatch (.Vlong i) (.Ifptr p)
  | ifptr_f (f p) : Vmatch (.Vfloat f) (.Ifptr p)
  | ifptr_s (f p) : Vmatch (.Vsingle f) (.Ifptr p)
  | ifptr_p (b ofs p) : Pmatch bc b ofs p → Vmatch (.Vptr b ofs) (.Ifptr p)

end VMATCH

/-- `ValueDomain.usize` -/
def usize (i : Integers.Int) : Z := Integers.Int.size i

/-- `ValueDomain.ssize` -/
def ssize (i : Integers.Int) : Z :=
  Integers.Int.size (if Integers.Int.lt i Integers.Int.zero then Integers.Int.not i else i) + 1

/-- `ValueDomain.urange` -/
def urange (a : Aval) : Z :=
  match a with
  | .I n | .IU n => usize n
  | .Uns _ n => n
  | _ => Integers.Int.zwordsize

/-- `ValueDomain.srange` -/
def srange (a : Aval) : Z :=
  match a with
  | .I n | .IU n => ssize n
  | .Uns _ n => n + 1
  | .Sgn _ n => n
  | _ => Integers.Int.zwordsize

/-- `ValueDomain.provenance` -/
def provenance (x : Aval) : Aptr :=
  match x with
  | .Ptr p | .Ifptr p => poffset p
  | .Uns p _ | .Sgn p _ | .Num p => p
  | _ => .Pbot

/-- `ValueDomain.ntop` -/
def ntop : Aval := .Num .Pbot
/-- `ValueDomain.ntop1` -/
def ntop1 (x : Aval) : Aval := .Num (provenance x)
/-- `ValueDomain.ntop2` -/
def ntop2 (x y : Aval) : Aval := .Num (plub (provenance x) (provenance y))

/-- `ValueDomain.int_provenance` -/
def intProvenance (strict : Bool) (i : Integers.Int) : Aptr :=
  if strict || Integers.Int.eq i Integers.Int.zero then .Pbot else .Nonstack

/-- `ValueDomain.long_provenance` -/
def longProvenance (strict : Bool) (i : Integers.Int64) : Aptr :=
  if strict || Integers.Int64.eq i Integers.Int64.zero then .Pbot else .Nonstack

/-- `ValueDomain.uns` -/
def uns (p : Aptr) (n : Z) : Aval :=
  if n ≤ 0 then .IU Integers.Int.zero
  else if n ≤ 1 then .Uns p 1
  else if n ≤ 7 then .Uns p 7
  else if n ≤ 8 then .Uns p 8
  else if n ≤ 15 then .Uns p 15
  else if n ≤ 16 then .Uns p 16
  else .Num p

/-- `ValueDomain.sgn` -/
def sgn (p : Aptr) (n : Z) : Aval :=
  if n ≤ 8 then .Sgn p 8 else if n ≤ 16 then .Sgn p 16 else .Num p

/-- `ValueDomain.vge` -/
inductive Vge : Aval → Aval → Prop where
  | bot (v) : Vge v .Vbot
  | i (i) : Vge (.I i) (.I i)
  | l (i) : Vge (.L i) (.L i)
  | f (f) : Vge (.F f) (.F f)
  | s (f) : Vge (.FS f) (.FS f)
  | iu (i) : Vge (.IU i) (.IU i)
  | iu_i (i) : Vge (.IU i) (.I i)
  | uns_i (p n i) : 0 ≤ n → IsUns n i → Vge (.Uns p n) (.I i)
  | uns_iu (p n i) : 0 ≤ n → IsUns n i → Vge (.Uns p n) (.IU i)
  | uns_uns (p1 n1 p2 n2) : n1 ≥ n2 → Pge p1 p2 → Vge (.Uns p1 n1) (.Uns p2 n2)
  | sgn_i (p n i) : 0 < n → IsSgn n i → Vge (.Sgn p n) (.I i)
  | sgn_iu (p n i) : 0 < n → IsSgn n i → Vge (.Sgn p n) (.IU i)
  | sgn_sgn (p1 n1 p2 n2) : n1 ≥ n2 → Pge p1 p2 → Vge (.Sgn p1 n1) (.Sgn p2 n2)
  | sgn_uns (p1 n1 p2 n2) : n1 > n2 → Pge p1 p2 → Vge (.Sgn p1 n1) (.Uns p2 n2)
  | num_i (p i) : Vge (.Num p) (.I i)
  | num_l (p i) : Vge (.Num p) (.L i)
  | num_f (p f) : Vge (.Num p) (.F f)
  | num_s (p f) : Vge (.Num p) (.FS f)
  | num_iu (p i) : Vge (.Num p) (.IU i)
  | num_uns (p q n) : Pge p q → Vge (.Num p) (.Uns q n)
  | num_sgn (p q n) : Pge p q → Vge (.Num p) (.Sgn q n)
  | num_num (p q) : Pge p q → Vge (.Num p) (.Num q)
  | p_p (p q) : Pge p q → Vge (.Ptr p) (.Ptr q)
  | ip_p (p q) : Pge p q → Vge (.Ifptr p) (.Ptr q)
  | ip_ip (p q) : Pge p q → Vge (.Ifptr p) (.Ifptr q)
  | ip_i (p i) : Vge (.Ifptr p) (.I i)
  | ip_l (p i) : Vge (.Ifptr p) (.L i)
  | ip_f (p f) : Vge (.Ifptr p) (.F f)
  | ip_s (p f) : Vge (.Ifptr p) (.FS f)
  | ip_iu (p i) : Vge (.Ifptr p) (.IU i)
  | ip_uns (p q n) : Pge p q → Vge (.Ifptr p) (.Uns q n)
  | ip_sgn (p q n) : Pge p q → Vge (.Ifptr p) (.Sgn q n)
  | ip_num (p q) : Pge p q → Vge (.Ifptr p) (.Num q)

/-- `ValueDomain.uns1`: like `uns` but never produces `IU Int.zero`. -/
def uns1 (p : Aptr) (n : Z) : Aval :=
  if n ≤ 1 then .Uns p 1
  else if n ≤ 7 then .Uns p 7
  else if n ≤ 8 then .Uns p 8
  else if n ≤ 15 then .Uns p 15
  else if n ≤ 16 then .Uns p 16
  else .Num p

/-- `ValueDomain.vlub_int` -/
def vlubInt (cstr : Integers.Int → Aval) (i1 i2 : Integers.Int) : Aval :=
  if Integers.Int.eq i1 i2 then cstr i1
  else if Integers.Int.lt i1 Integers.Int.zero || Integers.Int.lt i2 Integers.Int.zero
  then sgn .Pbot (max (ssize i1) (ssize i2))
  else uns1 .Pbot (max (usize i1) (usize i2))

section STRICT
variable (strict : Bool)

/-- Shared case of `vlub` (integer constant against `Uns`). -/
def vlubIUns (i : Integers.Int) (p : Aptr) (n : Z) : Aval :=
  if Integers.Int.lt i Integers.Int.zero then sgn p (max (ssize i) (n + 1))
  else uns1 p (max (usize i) n)

/-- `ValueDomain.vlub`: least upper bound of abstract values. -/
def vlub (v w : Aval) : Aval :=
  match v, w with
  | .Vbot, _ => w
  | _, .Vbot => v
  | .I i1, .I i2 => vlubInt .I i1 i2
  | .I i1, .IU i2 | .IU i1, .I i2 | .IU i1, .IU i2 => vlubInt .IU i1 i2
  | .I i, .Uns p n | .IU i, .Uns p n | .Uns p n, .I i | .Uns p n, .IU i => vlubIUns i p n
  | .I i, .Sgn p n | .IU i, .Sgn p n | .Sgn p n, .I i | .Sgn p n, .IU i =>
      sgn p (max (ssize i) n)
  | .I _, .Num p | .IU _, .Num p | .Num p, .I _ | .Num p, .IU _ => .Num p
  | .I i, .Ptr p | .I i, .Ifptr p | .IU i, .Ptr p | .IU i, .Ifptr p
  | .Ptr p, .I i | .Ifptr p, .I i | .Ptr p, .IU i | .Ifptr p, .IU i =>
      .Ifptr (plub p (intProvenance strict i))
  | .I _, .L _ | .I _, .F _ | .I _, .FS _ | .IU _, .L _ | .IU _, .F _ | .IU _, .FS _
  | .L _, .I _ | .F _, .I _ | .FS _, .I _ | .L _, .IU _ | .F _, .IU _ | .FS _, .IU _ => ntop
  | .Uns p1 n1, .Uns p2 n2 => .Uns (plub p1 p2) (max n1 n2)
  | .Uns p1 n1, .Sgn p2 n2 => sgn (plub p1 p2) (max (n1 + 1) n2)
  | .Sgn p1 n1, .Uns p2 n2 => sgn (plub p1 p2) (max n1 (n2 + 1))
  | .Sgn p1 n1, .Sgn p2 n2 => sgn (plub p1 p2) (max n1 n2)
  | .Uns p1 _, .Num p2 | .Sgn p1 _, .Num p2 | .Num p1, .Uns p2 _ | .Num p1, .Sgn p2 _ =>
      .Num (plub p1 p2)
  | .Uns p1 _, .Ptr p2 | .Uns p1 _, .Ifptr p2 | .Sgn p1 _, .Ptr p2 | .Sgn p1 _, .Ifptr p2
  | .Ptr p1, .Uns p2 _ | .Ifptr p1, .Uns p2 _ | .Ptr p1, .Sgn p2 _ | .Ifptr p1, .Sgn p2 _ =>
      .Ifptr (plub p1 p2)
  | .Uns p _, .L _ | .Uns p _, .F _ | .Uns p _, .FS _
  | .Sgn p _, .L _ | .Sgn p _, .F _ | .Sgn p _, .FS _
  | .L _, .Uns p _ | .F _, .Uns p _ | .FS _, .Uns p _
  | .L _, .Sgn p _ | .F _, .Sgn p _ | .FS _, .Sgn p _ => .Num p
  | .L i1, .L i2 => if Integers.Int64.eq i1 i2 then v else ntop
  | .L _, .Num p | .Num p, .L _ => .Num p
  | .L i, .Ptr p | .L i, .Ifptr p | .Ptr p, .L i | .Ifptr p, .L i =>
      .Ifptr (plub p (longProvenance strict i))
  | .L _, .F _ | .L _, .FS _ | .F _, .L _ | .FS _, .L _ => ntop
  | .F f1, .F f2 => if f1 = f2 then v else ntop
  | .F _, .Num p | .Num p, .F _ => .Num p
  | .F _, .Ptr p | .F _, .Ifptr p | .Ptr p, .F _ | .Ifptr p, .F _ => .Ifptr p
  | .F _, .FS _ | .FS _, .F _ => ntop
  | .FS f1, .FS f2 => if f1 = f2 then v else ntop
  | .FS _, .Num p | .Num p, .FS _ => .Num p
  | .FS _, .Ptr p | .FS _, .Ifptr p | .Ptr p, .FS _ | .Ifptr p, .FS _ => .Ifptr p
  | .Num p1, .Num p2 => .Num (plub p1 p2)
  | .Num p1, .Ptr p2 | .Num p1, .Ifptr p2 | .Ifptr p1, .Num p2 | .Ptr p1, .Num p2 =>
      .Ifptr (plub p1 p2)
  | .Ptr p1, .Ptr p2 => .Ptr (plub p1 p2)
  | .Ptr p1, .Ifptr p2 | .Ifptr p1, .Ptr p2 | .Ifptr p1, .Ifptr p2 => .Ifptr (plub p1 p2)

/-- `ValueDomain.aptr_of_aval` -/
def aptrOfAval (v : Aval) : Aptr :=
  match v with
  | .Ptr p | .Ifptr p => p
  | .Num p | .Uns p _ | .Sgn p _ => if strict then .Pbot else p
  | .I i => intProvenance strict i
  | .L i => longProvenance strict i
  | _ => .Pbot

end STRICT

/-- `ValueDomain.vplub` -/
def vplub (v : Aval) (p : Aptr) : Aptr :=
  match v with
  | .Ptr q | .Ifptr q => plub q p
  | _ => p

/-- `ValueDomain.vpincl` -/
def vpincl (v : Aval) (p : Aptr) : Bool :=
  match v with
  | .Ptr q | .Ifptr q | .Num q | .Uns q _ | .Sgn q _ => pincl q p
  | _ => true

/-- `ValueDomain.vincl` -/
def vincl (v w : Aval) : Bool :=
  match v, w with
  | .Vbot, _ => true
  | .I i, .I j => decide (i = j)
  | .I i, .IU j => decide (i = j)
  | .IU i, .IU j => decide (i = j)
  | .I i, .Uns _ n | .IU i, .Uns _ n =>
      decide (Integers.Int.zero_ext n.toNat i = i) && decide (0 ≤ n)
  | .I i, .Sgn _ n | .IU i, .Sgn _ n =>
      decide (Integers.Int.sign_ext n.toNat i = i) && decide (0 < n)
  | .Uns p n, .Uns q m => decide (n ≤ m) && pincl p q
  | .Uns p n, .Sgn q m => decide (n < m) && pincl p q
  | .Sgn p n, .Sgn q m => decide (n ≤ m) && pincl p q
  | .L i, .L j => decide (i = j)
  | .F i, .F j => decide (i = j)
  | .FS i, .FS j => decide (i = j)
  | .I _, .Num _ | .IU _, .Num _ | .L _, .Num _ | .F _, .Num _ | .FS _, .Num _
  | .I _, .Ifptr _ | .IU _, .Ifptr _ | .L _, .Ifptr _ | .F _, .Ifptr _ | .FS _, .Ifptr _ => true
  | .Uns p _, .Num q | .Sgn p _, .Num q | .Num p, .Num q => pincl p q
  | .Ptr p, .Ptr q => pincl p q
  | .Ptr p, .Ifptr q | .Ifptr p, .Ifptr q | .Num p, .Ifptr q | .Uns p _, .Ifptr q
  | .Sgn p _, .Ifptr q => pincl p q
  | _, _ => false

/-- `ValueDomain.genv_match` -/
def GenvMatch {F V : Type} (bc : BlockClassification) (ge : Genv F V) : Prop :=
  (∀ id b, Genv.findSymbol ge id = some b ↔ bc b = .BCglob id) ∧
  (∀ b, b < ge.genv_next → bc b ≠ .BCinvalid ∧ bc b ≠ .BCstack)

/-! ## Generic operations that just do constant propagation -/

/-- `ValueDomain.unop_int` -/
def unopInt (sem : Integers.Int → Integers.Int) (x : Aval) : Aval :=
  match x with
  | .I n => .I (sem n)
  | .IU n => .IU (sem n)
  | _ => ntop1 x

/-- `ValueDomain.binop_int` -/
def binopInt (sem : Integers.Int → Integers.Int → Integers.Int) (x y : Aval) : Aval :=
  match x, y with
  | .I n, .I m => .I (sem n m)
  | .I n, .IU m | .IU n, .I m | .IU n, .IU m => .IU (sem n m)
  | _, _ => ntop2 x y

/-- `ValueDomain.unop_long` -/
def unopLong (sem : Integers.Int64 → Integers.Int64) (x : Aval) : Aval :=
  match x with
  | .L n => .L (sem n)
  | _ => ntop1 x

/-- `ValueDomain.binop_long` -/
def binopLong (sem : Integers.Int64 → Integers.Int64 → Integers.Int64) (x y : Aval) : Aval :=
  match x, y with
  | .L n, .L m => .L (sem n m)
  | _, _ => ntop2 x y

/-- `ValueDomain.unop_float` -/
def unopFloat (sem : Floats.Float → Floats.Float) (x : Aval) : Aval :=
  match x with
  | .F n => .F (sem n)
  | _ => ntop1 x

/-- `ValueDomain.binop_float` -/
def binopFloat (sem : Floats.Float → Floats.Float → Floats.Float) (x y : Aval) : Aval :=
  match x, y with
  | .F n, .F m => .F (sem n m)
  | _, _ => ntop2 x y

/-- `ValueDomain.unop_single` -/
def unopSingle (sem : Floats.Float32 → Floats.Float32) (x : Aval) : Aval :=
  match x with
  | .FS n => .FS (sem n)
  | _ => ntop1 x

/-- `ValueDomain.binop_single` -/
def binopSingle (sem : Floats.Float32 → Floats.Float32 → Floats.Float32) (x y : Aval) : Aval :=
  match x, y with
  | .FS n, .FS m => .FS (sem n m)
  | _, _ => ntop2 x y

/-! ## Logical operations -/

/-- `ValueDomain.shl` -/
def shl (v w : Aval) : Aval :=
  match w with
  | .I amount =>
      if Integers.Int.ltu amount Integers.Int.iwordsize then
        match v with
        | .I i => .I (Integers.Int.shl i amount)
        | .IU i => .IU (Integers.Int.shl i amount)
        | .Uns p n => uns p (n + Integers.Int.unsigned amount)
        | .Sgn p n => sgn p (n + Integers.Int.unsigned amount)
        | _ => ntop1 v
      else ntop1 v
  | _ => ntop1 v

/-- `ValueDomain.shru` -/
def shru (v w : Aval) : Aval :=
  match w with
  | .I amount =>
      if Integers.Int.ltu amount Integers.Int.iwordsize then
        match v with
        | .I i => .I (Integers.Int.shru i amount)
        | .IU i => .IU (Integers.Int.shru i amount)
        | .Uns p n => uns p (n - Integers.Int.unsigned amount)
        | _ => uns (provenance v) (Integers.Int.zwordsize - Integers.Int.unsigned amount)
      else ntop1 v
  | _ => ntop1 v

/-- `ValueDomain.shr` -/
def shr (v w : Aval) : Aval :=
  match w with
  | .I amount =>
      if Integers.Int.ltu amount Integers.Int.iwordsize then
        match v with
        | .I i => .I (Integers.Int.shr i amount)
        | .IU i => .IU (Integers.Int.shr i amount)
        | .Uns p n => sgn p (n + 1 - Integers.Int.unsigned amount)
        | .Sgn p n => sgn p (n - Integers.Int.unsigned amount)
        | _ => sgn (provenance v) (Integers.Int.zwordsize - Integers.Int.unsigned amount)
      else ntop1 v
  | _ => ntop1 v

/-- `ValueDomain.and` -/
def and (v w : Aval) : Aval :=
  match v, w with
  | .I i1, .I i2 => .I (Integers.Int.and i1 i2)
  | .I i1, .IU i2 | .IU i1, .I i2 | .IU i1, .IU i2 => .IU (Integers.Int.and i1 i2)
  | .I i, .Uns p n | .IU i, .Uns p n | .Uns p n, .I i | .Uns p n, .IU i =>
      uns p (min n (usize i))
  | .I i, x | .IU i, x | x, .I i | x, .IU i => uns (provenance x) (usize i)
  | .Uns p1 n1, .Uns p2 n2 => uns (plub p1 p2) (min n1 n2)
  | .Uns p n, _ => uns (plub p (provenance w)) n
  | _, .Uns p n => uns (plub (provenance v) p) n
  | .Sgn p1 n1, .Sgn p2 n2 => sgn (plub p1 p2) (max n1 n2)
  | _, _ => ntop2 v w

/-- `ValueDomain.or` -/
def or (v w : Aval) : Aval :=
  match v, w with
  | .I i1, .I i2 => .I (Integers.Int.or i1 i2)
  | .I i1, .IU i2 | .IU i1, .I i2 | .IU i1, .IU i2 => .IU (Integers.Int.or i1 i2)
  | .I i, .Uns p n | .IU i, .Uns p n | .Uns p n, .I i | .Uns p n, .IU i =>
      uns p (max n (usize i))
  | .Uns p1 n1, .Uns p2 n2 => uns (plub p1 p2) (max n1 n2)
  | .Sgn p1 n1, .Sgn p2 n2 => sgn (plub p1 p2) (max n1 n2)
  | _, _ => ntop2 v w

/-- `ValueDomain.xor` -/
def xor (v w : Aval) : Aval :=
  match v, w with
  | .I i1, .I i2 => .I (Integers.Int.xor i1 i2)
  | .I i1, .IU i2 | .IU i1, .I i2 | .IU i1, .IU i2 => .IU (Integers.Int.xor i1 i2)
  | .I i, .Uns p n | .IU i, .Uns p n | .Uns p n, .I i | .Uns p n, .IU i =>
      uns p (max n (usize i))
  | .Uns p1 n1, .Uns p2 n2 => uns (plub p1 p2) (max n1 n2)
  | .Sgn p1 n1, .Sgn p2 n2 => sgn (plub p1 p2) (max n1 n2)
  | _, _ => ntop2 v w

/-- `ValueDomain.notint` -/
def notint (v : Aval) : Aval :=
  match v with
  | .I i => .I (Integers.Int.not i)
  | .IU i => .IU (Integers.Int.not i)
  | .Uns p n => sgn p (n + 1)
  | .Sgn p n => .Sgn p n
  | _ => ntop1 v

/-- `ValueDomain.rol` -/
def rol (x y : Aval) : Aval :=
  match y, x with
  | .I j, .I i => .I (Integers.Int.rol i j)
  | .I j, .IU i => .IU (Integers.Int.rol i j)
  | .I j, .Uns p n => uns p (n + Integers.Int.unsigned j)
  | .I j, .Sgn p n =>
      if n < Integers.Int.zwordsize then sgn p (n + Integers.Int.unsigned j) else ntop1 x
  | _, _ => ntop1 x

/-- `ValueDomain.ror` -/
def ror (x y : Aval) : Aval :=
  match y, x with
  | .I j, .I i => .I (Integers.Int.ror i j)
  | .I j, .IU i => .IU (Integers.Int.ror i j)
  | _, _ => ntop1 x

/-- `ValueDomain.rolm` -/
def rolm (x : Aval) (amount mask : Integers.Int) : Aval :=
  and (rol x (.I amount)) (.I mask)

/-! ## Integer arithmetic operations -/

/-- `ValueDomain.neg` -/
def neg (x : Aval) : Aval :=
  match x with
  | .I i => .I (Integers.Int.neg i)
  | .IU i => .IU (Integers.Int.neg i)
  | .Sgn p n => sgn p (n + 1)
  | _ => ntop1 x

/-- `ValueDomain.add` (`Archi.ptr64 = true` on aarch64). -/
def add (x y : Aval) : Aval :=
  match x, y with
  | .I i, .I j => .I (Integers.Int.add i j)
  | .I i, .IU j | .IU i, .I j | .IU i, .IU j => .IU (Integers.Int.add i j)
  | .I i, .Uns p n | .IU i, .Uns p n | .Uns p n, .I i | .Uns p n, .IU i =>
      uns p (max n (usize i) + 1)
  | .I i, .Sgn p n | .IU i, .Sgn p n | .Sgn p n, .I i | .Sgn p n, .IU i =>
      sgn p (max n (ssize i) + 1)
  | .Uns p1 n1, .Uns p2 n2 => uns (plub p1 p2) (max n1 n2 + 1)
  | .Sgn p1 n1, .Sgn p2 n2 => sgn (plub p1 p2) (max n1 n2 + 1)
  | .Uns p1 n1, .Sgn p2 n2 | .Sgn p2 n2, .Uns p1 n1 =>
      sgn (plub p1 p2) (max (n1 + 1) n2 + 1)
  | .Ptr p, .I i | .Ptr p, .IU i | .I i, .Ptr p | .IU i, .Ptr p =>
      .Ptr (if Archi.ptr64 then poffset p else padd p (Integers.Ptrofs.of_int i))
  | .Ptr p, _ | _, .Ptr p => .Ptr (poffset p)
  | .Ifptr p, .I i | .Ifptr p, .IU i | .I i, .Ifptr p | .IU i, .Ifptr p =>
      .Ifptr (if Archi.ptr64 then poffset p else padd p (Integers.Ptrofs.of_int i))
  | .Ifptr p, .Ifptr q => .Ifptr (plub (poffset p) (poffset q))
  | .Ifptr p, _ | _, .Ifptr p => .Ifptr (poffset p)
  | _, _ => ntop2 x y

/-- `ValueDomain.sub` -/
def sub (v w : Aval) : Aval :=
  match v, w with
  | .I i1, .I i2 => .I (Integers.Int.sub i1 i2)
  | .I i1, .IU i2 | .IU i1, .I i2 | .IU i1, .IU i2 => .IU (Integers.Int.sub i1 i2)
  | .I i, .Uns p n | .IU i, .Uns p n | .Uns p n, .I i | .Uns p n, .IU i =>
      sgn p (max (n + 1) (ssize i) + 1)
  | .I i, .Sgn p n | .IU i, .Sgn p n | .Sgn p n, .I i | .Sgn p n, .IU i =>
      sgn p (max n (ssize i) + 1)
  | .Uns p1 n1, .Uns p2 n2 => sgn (plub p1 p2) (max n1 n2 + 1)
  | .Sgn p1 n1, .Sgn p2 n2 => sgn (plub p1 p2) (max n1 n2 + 1)
  | .Uns p1 n1, .Sgn p2 n2 | .Sgn p2 n2, .Uns p1 n1 =>
      sgn (plub p1 p2) (max (n1 + 1) n2 + 1)
  | .Ptr p, .I i | .Ptr p, .IU i =>
      if Archi.ptr64 then .Ifptr (poffset p) else .Ptr (psub p (Integers.Ptrofs.of_int i))
  | .Ptr p, _ => .Ifptr (poffset p)
  | .Ifptr p, .I i | .Ifptr p, .IU i =>
      if Archi.ptr64 then .Ifptr (plub (poffset p) (provenance w))
      else .Ifptr (psub p (Integers.Ptrofs.of_int i))
  | .Ifptr p, _ => .Ifptr (plub (poffset p) (provenance w))
  | _, _ => ntop2 v w

/-- `ValueDomain.mul_base` -/
def mulBase (v w : Aval) : Aval :=
  match v, w with
  | .Uns p n1, .I n2 | .Uns p n1, .IU n2 | .I n2, .Uns p n1 | .IU n2, .Uns p n1 =>
      uns p (n1 + usize n2)
  | .Uns p1 n1, .Uns p2 n2 => uns (plub p1 p2) (n1 + n2)
  | .Sgn p n1, .I n2 | .Sgn p n1, .IU n2 | .I n2, .Sgn p n1 | .IU n2, .Sgn p n1 =>
      sgn p (n1 + ssize n2)
  | .Sgn p1 n1, .Sgn p2 n2 => sgn (plub p1 p2) (n1 + n2)
  | .Uns p1 n1, .Sgn p2 n2 => sgn (plub p1 p2) ((n1 + 1) + n2)
  | .Sgn p1 n1, .Uns p2 n2 => sgn (plub p1 p2) (n1 + (n2 + 1))
  | _, _ => ntop2 v w

/-- `ValueDomain.mul` -/
def mul (v w : Aval) : Aval :=
  match v, w with
  | .I i1, .I i2 => .I (Integers.Int.mul i1 i2)
  | .IU i1, .I i2 | .I i1, .IU i2 | .IU i1, .IU i2 => .IU (Integers.Int.mul i1 i2)
  | _, _ =>
      if vincl v (.Uns .Ptop 0) || vincl w (.Uns .Ptop 0) then .IU Integers.Int.zero
      else mulBase v w

/-- `ValueDomain.mulhs_base` -/
def mulhsBase (v w : Aval) : Aval :=
  sgn (plub (provenance v) (provenance w)) (srange v + srange w - Integers.Int.zwordsize)

/-- `ValueDomain.mulhs` -/
def mulhs (v w : Aval) : Aval :=
  match v, w with
  | .I i1, .I i2 => .I (Integers.Int.mulhs i1 i2)
  | .IU i1, .I i2 | .I i1, .IU i2 | .IU i1, .IU i2 => .IU (Integers.Int.mulhs i1 i2)
  | _, _ =>
      if vincl v (.Uns .Ptop 0) || vincl w (.Uns .Ptop 0) then .IU Integers.Int.zero
      else mulhsBase v w

/-- `ValueDomain.mulhu_base` -/
def mulhuBase (v w : Aval) : Aval :=
  uns (plub (provenance v) (provenance w)) (urange v + urange w - Integers.Int.zwordsize)

/-- `ValueDomain.mulhu` -/
def mulhu (v w : Aval) : Aval :=
  match v, w with
  | .I i1, .I i2 => .I (Integers.Int.mulhu i1 i2)
  | .I i1, .IU i2 | .IU i1, .I i2 | .IU i1, .IU i2 => .IU (Integers.Int.mulhu i1 i2)
  | _, _ =>
      if vincl v (.Uns .Ptop 1) || vincl w (.Uns .Ptop 1) then .IU Integers.Int.zero
      else mulhuBase v w

/-- `Z.log2` (`0` on non-positive arguments). -/
def zlog2 (z : Z) : Z := if z ≤ 0 then 0 else (Nat.log2 z.toNat : Z)

/-- `Zpower.two_p` (`0` on negative exponents). -/
def twoP (n : Z) : Z := if n < 0 then 0 else (2 : Z) ^ n.toNat

section STRICT
variable (strict : Bool)

/-- `if va_strict tt then Vbot else ntop` -/
def undefResult : Aval := if strict then .Vbot else ntop

/-- `ValueDomain.divs` -/
def divs (v w : Aval) : Aval :=
  match w, v with
  | .I i2, .I i1 | .I i2, .IU i1 | .IU i2, .I i1 | .IU i2, .IU i1 =>
      if Integers.Int.eq i2 Integers.Int.zero ||
          (Integers.Int.eq i1 (Integers.Int.repr Integers.Int.min_signed) &&
            Integers.Int.eq i2 Integers.Int.mone)
      then undefResult strict
      else .I (Integers.Int.divs i1 i2)
  | .I i2, _ | .IU i2, _ =>
      if Integers.Int.eq i2 Integers.Int.zero then undefResult strict
      else sgn (provenance v)
        (srange v + 1 - zlog2 ((Integers.Int.signed i2).natAbs : Z))
  | _, _ => ntop2 v w

/-- `ValueDomain.divu` -/
def divu (v w : Aval) : Aval :=
  match w with
  | .I i2 | .IU i2 =>
      if Integers.Int.eq i2 Integers.Int.zero then undefResult strict
      else
        match v with
        | .I i1 | .IU i1 => .I (Integers.Int.divu i1 i2)
        | _ => uns (provenance v) (urange v - zlog2 (Integers.Int.unsigned i2))
  | _ => ntop2 v w

/-- `ValueDomain.mods` -/
def mods (v w : Aval) : Aval :=
  match w, v with
  | .I i2, .I i1 | .I i2, .IU i1 | .IU i2, .I i1 | .IU i2, .IU i1 =>
      if Integers.Int.eq i2 Integers.Int.zero ||
          (Integers.Int.eq i1 (Integers.Int.repr Integers.Int.min_signed) &&
            Integers.Int.eq i2 Integers.Int.mone)
      then undefResult strict
      else .I (Integers.Int.mods i1 i2)
  | .I i2, _ | .IU i2, _ => sgn (provenance v) (ssize i2)
  | _, _ => ntop2 v w

/-- `ValueDomain.modu` -/
def modu (v w : Aval) : Aval :=
  match w, v with
  | .I i2, .I i1 | .I i2, .IU i1 | .IU i2, .I i1 | .IU i2, .IU i1 =>
      if Integers.Int.eq i2 Integers.Int.zero then undefResult strict
      else .I (Integers.Int.modu i1 i2)
  | .I i2, _ | .IU i2, _ => uns (provenance v) (usize i2)
  | _, _ => ntop2 v w

end STRICT

/-- `ValueDomain.shrx` -/
def shrx (v w : Aval) : Aval :=
  match v, w with
  | .I i, .I j =>
      if Integers.Int.ltu j (Integers.Int.repr 31) then .I (Integers.Int.shrx i j) else ntop
  | _, _ => ntop1 v

/-! ## 64-bit integer operations -/

/-- `ValueDomain.shift_long` -/
def shiftLong (sem : Integers.Int64 → Integers.Int → Integers.Int64) (v w : Aval) : Aval :=
  match w with
  | .I amount =>
      if Integers.Int.ltu amount Integers.Int64.iwordsize' then
        match v with
        | .L i => .L (sem i amount)
        | _ => ntop1 v
      else ntop1 v
  | _ => ntop1 v

/-- `ValueDomain.shll` -/
def shll : Aval → Aval → Aval := shiftLong Integers.Int64.shl'
/-- `ValueDomain.shrl` -/
def shrl : Aval → Aval → Aval := shiftLong Integers.Int64.shr'
/-- `ValueDomain.shrlu` -/
def shrlu : Aval → Aval → Aval := shiftLong Integers.Int64.shru'
/-- `ValueDomain.andl` -/
def andl : Aval → Aval → Aval := binopLong Integers.Int64.and
/-- `ValueDomain.orl` -/
def orl : Aval → Aval → Aval := binopLong Integers.Int64.or
/-- `ValueDomain.xorl` -/
def xorl : Aval → Aval → Aval := binopLong Integers.Int64.xor
/-- `ValueDomain.notl` -/
def notl : Aval → Aval := unopLong Integers.Int64.not

/-- `ValueDomain.rotate_long` -/
def rotateLong (sem : Integers.Int64 → Integers.Int64 → Integers.Int64) (v w : Aval) : Aval :=
  match v, w with
  | .L i, .I amount => .L (sem i (Integers.Int64.repr (Integers.Int.unsigned amount)))
  | _, _ => ntop1 v

/-- `ValueDomain.roll` -/
def roll : Aval → Aval → Aval := rotateLong Integers.Int64.rol
/-- `ValueDomain.rorl` -/
def rorl : Aval → Aval → Aval := rotateLong Integers.Int64.ror
/-- `ValueDomain.negl` -/
def negl : Aval → Aval := unopLong Integers.Int64.neg

/-- `ValueDomain.addl` -/
def addl (x y : Aval) : Aval :=
  match x, y with
  | .L i, .L j => .L (Integers.Int64.add i j)
  | .Ptr p, .L i | .L i, .Ptr p =>
      .Ptr (if Archi.ptr64 then padd p (Integers.Ptrofs.of_int64 i) else poffset p)
  | .Ptr p, _ | _, .Ptr p => .Ptr (poffset p)
  | .Ifptr p, .L i | .L i, .Ifptr p =>
      .Ifptr (if Archi.ptr64 then padd p (Integers.Ptrofs.of_int64 i) else poffset p)
  | .Ifptr p, .Ifptr q => .Ifptr (plub (poffset p) (poffset q))
  | .Ifptr p, _ | _, .Ifptr p => .Ifptr (poffset p)
  | _, _ => ntop2 x y

/-- `ValueDomain.subl` -/
def subl (v w : Aval) : Aval :=
  match v, w with
  | .L i1, .L i2 => .L (Integers.Int64.sub i1 i2)
  | .Ptr p, .L i =>
      if Archi.ptr64 then .Ptr (psub p (Integers.Ptrofs.of_int64 i)) else .Ifptr (poffset p)
  | .Ptr p, _ => .Ifptr (poffset p)
  | .Ifptr p, .L i =>
      if Archi.ptr64 then .Ifptr (psub p (Integers.Ptrofs.of_int64 i))
      else .Ifptr (plub (poffset p) (provenance w))
  | .Ifptr p, _ => .Ifptr (plub (poffset p) (provenance w))
  | _, _ => ntop2 v w

/-- `ValueDomain.mull` -/
def mull : Aval → Aval → Aval := binopLong Integers.Int64.mul
/-- `ValueDomain.mullhs` -/
def mullhs : Aval → Aval → Aval := binopLong Integers.Int64.mulhs
/-- `ValueDomain.mullhu` -/
def mullhu : Aval → Aval → Aval := binopLong Integers.Int64.mulhu

section STRICT
variable (strict : Bool)

/-- `ValueDomain.divls` -/
def divls (v w : Aval) : Aval :=
  match w, v with
  | .L i2, .L i1 =>
      if Integers.Int64.eq i2 Integers.Int64.zero ||
          (Integers.Int64.eq i1 (Integers.Int64.repr Integers.Int64.min_signed) &&
            Integers.Int64.eq i2 Integers.Int64.mone)
      then undefResult strict
      else .L (Integers.Int64.divs i1 i2)
  | _, _ => ntop2 v w

/-- `ValueDomain.divlu` -/
def divlu (v w : Aval) : Aval :=
  match w, v with
  | .L i2, .L i1 =>
      if Integers.Int64.eq i2 Integers.Int64.zero then undefResult strict
      else .L (Integers.Int64.divu i1 i2)
  | _, _ => ntop2 v w

/-- `ValueDomain.modls` -/
def modls (v w : Aval) : Aval :=
  match w, v with
  | .L i2, .L i1 =>
      if Integers.Int64.eq i2 Integers.Int64.zero ||
          (Integers.Int64.eq i1 (Integers.Int64.repr Integers.Int64.min_signed) &&
            Integers.Int64.eq i2 Integers.Int64.mone)
      then undefResult strict
      else .L (Integers.Int64.mods i1 i2)
  | _, _ => ntop2 v w

/-- `ValueDomain.modlu` -/
def modlu (v w : Aval) : Aval :=
  match w, v with
  | .L i2, .L i1 =>
      if Integers.Int64.eq i2 Integers.Int64.zero then undefResult strict
      else .L (Integers.Int64.modu i1 i2)
  | _, _ => ntop2 v w

end STRICT

/-- `ValueDomain.shrxl` -/
def shrxl (v w : Aval) : Aval :=
  match v, w with
  | .L i, .I j =>
      if Integers.Int.ltu j (Integers.Int.repr 63) then .L (Integers.Int64.shrx' i j) else ntop
  | _, _ => ntop1 v

/-- `ValueDomain.rolml` -/
def rolml (x : Aval) (amount : Integers.Int) (mask : Integers.Int64) : Aval :=
  andl (roll x (.I amount)) (.L mask)

/-! ## Pointer operations -/

/-- `ValueDomain.offset_ptr` -/
def offsetPtr (v : Aval) (n : Integers.Ptrofs) : Aval :=
  match v with
  | .Ptr p => .Ptr (padd p n)
  | .Ifptr p => .Ifptr (padd p n)
  | _ => ntop1 v

/-! ## Floating-point arithmetic operations -/

def negf : Aval → Aval := unopFloat Floats.Float.neg
def absf : Aval → Aval := unopFloat Floats.Float.abs
def addf : Aval → Aval → Aval := binopFloat Floats.Float.add
def subf : Aval → Aval → Aval := binopFloat Floats.Float.sub
def mulf : Aval → Aval → Aval := binopFloat Floats.Float.mul
def divf : Aval → Aval → Aval := binopFloat Floats.Float.div
def negfs : Aval → Aval := unopSingle Floats.Float32.neg
def absfs : Aval → Aval := unopSingle Floats.Float32.abs
def addfs : Aval → Aval → Aval := binopSingle Floats.Float32.add
def subfs : Aval → Aval → Aval := binopSingle Floats.Float32.sub
def mulfs : Aval → Aval → Aval := binopSingle Floats.Float32.mul
def divfs : Aval → Aval → Aval := binopSingle Floats.Float32.div

/-! ## Conversions -/

/-- `ValueDomain.zero_ext` -/
def zeroExt (nbits : Z) (v : Aval) : Aval :=
  match v with
  | .I i => .I (Integers.Int.zero_ext nbits.toNat i)
  | .IU i => .IU (Integers.Int.zero_ext nbits.toNat i)
  | .Uns p n => uns p (min n nbits)
  | _ => uns (provenance v) nbits

/-- `ValueDomain.sign_ext` -/
def signExt (nbits : Z) (v : Aval) : Aval :=
  if nbits ≤ 0 then .Uns (provenance v) 0
  else
    match v with
    | .I i => .I (Integers.Int.sign_ext nbits.toNat i)
    | .IU i => .IU (Integers.Int.sign_ext nbits.toNat i)
    | .Uns p n => if n < nbits then .Uns p n else sgn p nbits
    | .Sgn p n => sgn p (min n nbits)
    | _ => sgn (provenance v) nbits

/-- `ValueDomain.zero_ext_l` -/
def zeroExtL (s : Z) : Aval → Aval := unopLong (Integers.Int64.zero_ext s.toNat)
/-- `ValueDomain.sign_ext_l` -/
def signExtL (s : Z) : Aval → Aval := unopLong (Integers.Int64.sign_ext s.toNat)

/-- `ValueDomain.longofint` -/
def longofint (v : Aval) : Aval :=
  match v with
  | .I i => .L (Integers.Int64.repr (Integers.Int.signed i))
  | _ => ntop1 v

/-- `ValueDomain.longofintu` -/
def longofintu (v : Aval) : Aval :=
  match v with
  | .I i => .L (Integers.Int64.repr (Integers.Int.unsigned i))
  | _ => ntop1 v

/-- `ValueDomain.singleoffloat` -/
def singleoffloat (v : Aval) : Aval :=
  match v with
  | .F f => .FS (Floats.Float.toSingle f)
  | _ => ntop1 v

/-- `ValueDomain.floatofsingle` -/
def floatofsingle (v : Aval) : Aval :=
  match v with
  | .FS f => .F (Floats.Float.ofSingle f)
  | _ => ntop1 v

section STRICT
variable (strict : Bool)

/-- Abstract float-to-integer conversion (shared by `intoffloat` & co.). -/
private def convPartial {A : Type} (cstr : A → Aval) (r : Option A) : Aval :=
  match r with
  | some i => cstr i
  | none => undefResult strict

/-- `ValueDomain.intoffloat` -/
def intoffloat (x : Aval) : Aval :=
  match x with
  | .F f => convPartial strict .I (Floats.Float.toInt f)
  | _ => ntop1 x

/-- `ValueDomain.intuoffloat` -/
def intuoffloat (x : Aval) : Aval :=
  match x with
  | .F f => convPartial strict .I (Floats.Float.toIntu f)
  | _ => ntop1 x

/-- `ValueDomain.intofsingle` -/
def intofsingle (x : Aval) : Aval :=
  match x with
  | .FS f => convPartial strict .I (Floats.Float32.toInt f)
  | _ => ntop1 x

/-- `ValueDomain.intuofsingle` -/
def intuofsingle (x : Aval) : Aval :=
  match x with
  | .FS f => convPartial strict .I (Floats.Float32.toIntu f)
  | _ => ntop1 x

/-- `ValueDomain.longoffloat` -/
def longoffloat (x : Aval) : Aval :=
  match x with
  | .F f => convPartial strict .L (Floats.Float.toLong f)
  | _ => ntop1 x

/-- `ValueDomain.longuoffloat` -/
def longuoffloat (x : Aval) : Aval :=
  match x with
  | .F f => convPartial strict .L (Floats.Float.toLongu f)
  | _ => ntop1 x

/-- `ValueDomain.longofsingle` -/
def longofsingle (x : Aval) : Aval :=
  match x with
  | .FS f => convPartial strict .L (Floats.Float32.toLong f)
  | _ => ntop1 x

/-- `ValueDomain.longuofsingle` -/
def longuofsingle (x : Aval) : Aval :=
  match x with
  | .FS f => convPartial strict .L (Floats.Float32.toLongu f)
  | _ => ntop1 x

end STRICT

/-- `ValueDomain.floatofint` -/
def floatofint (x : Aval) : Aval :=
  match x with
  | .I i => .F (Floats.Float.ofInt i)
  | _ => ntop1 x

/-- `ValueDomain.floatofintu` -/
def floatofintu (x : Aval) : Aval :=
  match x with
  | .I i => .F (Floats.Float.ofIntu i)
  | _ => ntop1 x

/-- `ValueDomain.singleofint` -/
def singleofint (x : Aval) : Aval :=
  match x with
  | .I i => .FS (Floats.Float32.ofInt i)
  | _ => ntop1 x

/-- `ValueDomain.singleofintu` -/
def singleofintu (x : Aval) : Aval :=
  match x with
  | .I i => .FS (Floats.Float32.ofIntu i)
  | _ => ntop1 x

/-- `ValueDomain.floatoflong` -/
def floatoflong (x : Aval) : Aval :=
  match x with
  | .L i => .F (Floats.Float.ofLong i)
  | _ => ntop1 x

/-- `ValueDomain.floatoflongu` -/
def floatoflongu (x : Aval) : Aval :=
  match x with
  | .L i => .F (Floats.Float.ofLongu i)
  | _ => ntop1 x

/-- `ValueDomain.singleoflong` -/
def singleoflong (x : Aval) : Aval :=
  match x with
  | .L i => .FS (Floats.Float32.ofLong i)
  | _ => ntop1 x

/-- `ValueDomain.singleoflongu` -/
def singleoflongu (x : Aval) : Aval :=
  match x with
  | .L i => .FS (Floats.Float32.ofLongu i)
  | _ => ntop1 x

/-- `ValueDomain.floatofwords` -/
def floatofwords (x y : Aval) : Aval :=
  match x, y with
  | .I i, .I j => .F (Floats.Float.fromWords i j)
  | _, _ => ntop2 x y

/-- `ValueDomain.longofwords` -/
def longofwords (x y : Aval) : Aval :=
  match y, x with
  | .I j, .I i => .L (Integers.Int64.ofwords i j)
  | _, _ => ntop2 x y

/-- `ValueDomain.loword` -/
def loword (x : Aval) : Aval :=
  match x with
  | .L i => .I (Integers.Int64.loword i)
  | _ => ntop1 x

/-- `ValueDomain.hiword` -/
def hiword (x : Aval) : Aval :=
  match x with
  | .L i => .I (Integers.Int64.hiword i)
  | _ => ntop1 x

/-! ## Comparisons and variation intervals -/

/-- `ValueDomain.cmp_intv` -/
def cmpIntv (c : Comparison) (i : Z × Z) (n : Z) : Abool :=
  let (lo, hi) := i
  match c with
  | .Ceq => if decide (n < lo) || decide (hi < n) then .Maybe false else .Btop
  | .Cne => if decide (n < lo) || decide (hi < n) then .Maybe true else .Btop
  | .Clt => if hi < n then .Maybe true else if n ≤ lo then .Maybe false else .Btop
  | .Cle => if hi ≤ n then .Maybe true else if n < lo then .Maybe false else .Btop
  | .Cgt => if n < lo then .Maybe true else if hi ≤ n then .Maybe false else .Btop
  | .Cge => if n ≤ lo then .Maybe true else if hi < n then .Maybe false else .Btop

/-- `ValueDomain.zcmp` -/
def zcmp (c : Comparison) (n1 n2 : Z) : Bool :=
  match c with
  | .Ceq => decide (n1 = n2)
  | .Cne => !(decide (n1 = n2))
  | .Clt => decide (n1 < n2)
  | .Cle => decide (n1 ≤ n2)
  | .Cgt => decide (n2 < n1)
  | .Cge => decide (n2 ≤ n1)

/-- `ValueDomain.uintv` -/
def uintv (v : Aval) : Z × Z :=
  match v with
  | .I n => (Integers.Int.unsigned n, Integers.Int.unsigned n)
  | .Uns _ n =>
      if n < Integers.Int.zwordsize then (0, twoP n - 1) else (0, Integers.Int.max_unsigned)
  | _ => (0, Integers.Int.max_unsigned)

/-- `ValueDomain.sintv` -/
def sintv (v : Aval) : Z × Z :=
  match v with
  | .I n => (Integers.Int.signed n, Integers.Int.signed n)
  | .Uns _ n =>
      if n < Integers.Int.zwordsize then (0, twoP n - 1)
      else (Integers.Int.min_signed, Integers.Int.max_signed)
  | .Sgn _ n =>
      if n < Integers.Int.zwordsize then (let x := twoP (n - 1); (-x, x - 1))
      else (Integers.Int.min_signed, Integers.Int.max_signed)
  | _ => (Integers.Int.min_signed, Integers.Int.max_signed)

section STRICT
variable (strict : Bool)

/-- `ValueDomain.cmpu_bool` -/
def cmpuBool (c : Comparison) (v w : Aval) : Abool :=
  match v, w with
  | .I i1, .I i2 => .Just (Integers.Int.cmpu c i1 i2)
  | .I i1, .IU i2 | .IU i1, .I i2 | .IU i1, .IU i2 => .Maybe (Integers.Int.cmpu c i1 i2)
  | .Ptr _, .I i =>
      if Integers.Int.eq i Integers.Int.zero then cmpDifferentBlocks strict c else .Btop
  | .I i, .Ptr _ =>
      if Integers.Int.eq i Integers.Int.zero then cmpDifferentBlocks strict c else .Btop
  | .Ptr p1, .Ptr p2 => pcmp strict c p1 p2
  | _, .I i | _, .IU i => cmpIntv c (uintv v) (Integers.Int.unsigned i)
  | .I i, _ | .IU i, _ => cmpIntv c.swap (uintv w) (Integers.Int.unsigned i)
  | _, _ => .Btop

/-- `ValueDomain.cmplu_bool` -/
def cmpluBool (c : Comparison) (v w : Aval) : Abool :=
  match v, w with
  | .L i1, .L i2 => .Just (Integers.Int64.cmpu c i1 i2)
  | .Ptr _, .L i =>
      if Integers.Int64.eq i Integers.Int64.zero then cmpDifferentBlocks strict c else .Btop
  | .L i, .Ptr _ =>
      if Integers.Int64.eq i Integers.Int64.zero then cmpDifferentBlocks strict c else .Btop
  | .Ptr p1, .Ptr p2 => pcmp strict c p1 p2
  | _, _ => .Btop

end STRICT

/-- `ValueDomain.cmp_bool` -/
def cmpBool (c : Comparison) (v w : Aval) : Abool :=
  match v, w with
  | .I i1, .I i2 => .Just (Integers.Int.cmp c i1 i2)
  | .I i1, .IU i2 | .IU i1, .I i2 | .IU i1, .IU i2 => .Maybe (Integers.Int.cmp c i1 i2)
  | _, .I i | _, .IU i => cmpIntv c (sintv v) (Integers.Int.signed i)
  | .I i, _ | .IU i, _ => cmpIntv c.swap (sintv w) (Integers.Int.signed i)
  | _, _ => .Btop

/-- `ValueDomain.cmpl_bool` -/
def cmplBool (c : Comparison) (v w : Aval) : Abool :=
  match v, w with
  | .L i1, .L i2 => .Just (Integers.Int64.cmp c i1 i2)
  | _, _ => .Btop

/-- `ValueDomain.cmpf_bool` -/
def cmpfBool (c : Comparison) (v w : Aval) : Abool :=
  match v, w with
  | .F f1, .F f2 => .Just (Floats.Float.cmp c f1 f2)
  | _, _ => .Btop

/-- `ValueDomain.cmpfs_bool` -/
def cmpfsBool (c : Comparison) (v w : Aval) : Abool :=
  match v, w with
  | .FS f1, .FS f2 => .Just (Floats.Float32.cmp c f1 f2)
  | _, _ => .Btop

/-- `ValueDomain.maskzero` -/
def maskzero (x : Aval) (mask : Integers.Int) : Abool :=
  match x with
  | .I i => .Just (Integers.Int.eq (Integers.Int.and i mask) Integers.Int.zero)
  | .IU i => .Maybe (Integers.Int.eq (Integers.Int.and i mask) Integers.Int.zero)
  | .Uns _ n =>
      if Integers.Int.eq (Integers.Int.zero_ext n.toNat mask) Integers.Int.zero
      then .Maybe true else .Btop
  | _ => .Btop

/-- `ValueDomain.of_optbool` -/
def ofOptbool (ab : Abool) : Aval :=
  match ab with
  | .Just b => .I (if b then Integers.Int.one else Integers.Int.zero)
  | .Maybe b => .IU (if b then Integers.Int.one else Integers.Int.zero)
  | _ => .Uns .Pbot 1

/-- `ValueDomain.resolve_branch` -/
def resolveBranch (ab : Abool) : Option Bool :=
  match ab with
  | .Just b => some b
  | .Maybe b => some b
  | _ => none

/-- `ValueDomain.add_undef`: the result may also be `Vundef`. -/
def addUndef (x : Aval) : Aval :=
  match x with
  | .Vbot => ntop
  | .I i => .IU i
  | .L _ | .F _ | .FS _ => ntop
  | _ => x

/-- `ValueDomain.vnormalize_type` -/
def vnormalizeType (ty : ATyp) (x : Aval) : Aval :=
  match x, ty with
  | .Vbot, _ => .Vbot
  | .I _, .Tint => x
  | .L _, .Tlong => x
  | .F _, .Tfloat => x
  | .FS _, .Tsingle => x
  | .I _, .Tany32 | .FS _, .Tany32 => x
  | .I _, .Tany64 | .L _, .Tany64 | .F _, .Tany64 | .FS _, .Tany64 => x
  | _, _ => addUndef x

/-- `ValueDomain.select` -/
def select (strict : Bool) (ab : Abool) (x y : Aval) (ty : ATyp) : Aval :=
  match ab with
  | .Bnone => ntop
  | .Just b => vnormalizeType ty (if b then x else y)
  | .Maybe b => addUndef (vnormalizeType ty (if b then x else y))
  | .Btop => addUndef (vnormalizeType ty (vlub strict x y))

/-- `ValueDomain.vnormalize`: normalization at load time. -/
def vnormalize (chunk : Chunk) (v : Aval) : Aval :=
  match chunk, v with
  | _, .Vbot => .Vbot
  | .Mbool, .I i =>
      let j := Integers.Int.zero_ext 8 i
      if Integers.Int.eq j Integers.Int.zero || Integers.Int.eq j Integers.Int.one then .I j
      else .Uns .Pbot 1
  | .Mbool, .IU i =>
      let j := Integers.Int.zero_ext 8 i
      if Integers.Int.eq j Integers.Int.zero || Integers.Int.eq j Integers.Int.one then .IU j
      else .Uns .Pbot 1
  | .Mbool, _ => .Uns (provenance v) 1
  | .Mint8signed, .I i => .I (Integers.Int.sign_ext 8 i)
  | .Mint8signed, .IU i => .IU (Integers.Int.sign_ext 8 i)
  | .Mint8signed, .Uns _ n =>
      if n < 8 then .Uns (provenance v) n else .Sgn (provenance v) 8
  | .Mint8signed, .Sgn _ n => .Sgn (provenance v) (min n 8)
  | .Mint8signed, _ => .Sgn (provenance v) 8
  | .Mint8unsigned, .I i => .I (Integers.Int.zero_ext 8 i)
  | .Mint8unsigned, .IU i => .IU (Integers.Int.zero_ext 8 i)
  | .Mint8unsigned, .Uns _ n => .Uns (provenance v) (min n 8)
  | .Mint8unsigned, _ => .Uns (provenance v) 8
  | .Mint16signed, .I i => .I (Integers.Int.sign_ext 16 i)
  | .Mint16signed, .IU i => .IU (Integers.Int.sign_ext 16 i)
  | .Mint16signed, .Uns _ n =>
      if n < 16 then .Uns (provenance v) n else .Sgn (provenance v) 16
  | .Mint16signed, .Sgn _ n => .Sgn (provenance v) (min n 16)
  | .Mint16signed, _ => .Sgn (provenance v) 16
  | .Mint16unsigned, .I i => .I (Integers.Int.zero_ext 16 i)
  | .Mint16unsigned, .IU i => .IU (Integers.Int.zero_ext 16 i)
  | .Mint16unsigned, .Uns _ n => .Uns (provenance v) (min n 16)
  | .Mint16unsigned, _ => .Uns (provenance v) 16
  | .Mint32, .I _ | .Mint32, .IU _ | .Mint32, .Uns _ _ | .Mint32, .Sgn _ _
  | .Mint32, .Num _ => v
  | .Mint32, .Ptr _ | .Mint32, .Ifptr _ => if Archi.ptr64 then .Num (provenance v) else v
  | .Mint32, _ => .Num (provenance v)
  | .Mint64, .L _ => v
  | .Mint64, .Ptr _ | .Mint64, .Ifptr _ => if Archi.ptr64 then v else .Num (provenance v)
  | .Mint64, _ => .Num (provenance v)
  | .Mfloat32, .FS _ => v
  | .Mfloat32, _ => .Num (provenance v)
  | .Mfloat64, .F _ => v
  | .Mfloat64, _ => .Num (provenance v)
  | .Many32, .I _ | .Many32, .IU _ | .Many32, .Uns _ _ | .Many32, .Sgn _ _
  | .Many32, .FS _ => v
  | .Many32, .Ptr _ | .Many32, .Ifptr _ => if Archi.ptr64 then .Num (provenance v) else v
  | .Many32, _ => .Num (provenance v)
  | .Many64, _ => v

/-- `ValueDomain.val_of_aval` -/
def valOfAval (a : Aval) : Val :=
  match a with
  | .I n => .Vint n
  | .L n => .Vlong n
  | .F f => .Vfloat f
  | .FS f => .Vsingle f
  | _ => .Vundef

/-- `ValueDomain.aval_of_val` -/
def avalOfVal (v : Val) : Option Aval :=
  match v with
  | .Vint n => some (.I n)
  | .Vlong n => some (.L n)
  | .Vfloat f => some (.F f)
  | .Vsingle f => some (.FS f)
  | _ => none

/-- `ValueDomain.of_xtype` -/
def ofXtype (x : XType) (p : Aptr) : Aval :=
  match x with
  | .Xbool => .Uns p 1
  | .Xint8signed => .Sgn p 8
  | .Xint8unsigned => .Uns p 8
  | .Xint16signed => .Sgn p 16
  | .Xint16unsigned => .Uns p 16
  | _ => .Ifptr p

/-! ## Nonaliasing tests -/

/-- `ValueDomain.pdisjoint`: no overlap between a block of size `sz1` in
    region `p1` and a block of size `sz2` in region `p2`. -/
def pdisjoint (p1 : Aptr) (sz1 : Z) (p2 : Aptr) (sz2 : Z) : Bool :=
  match p1, p2 with
  | .Pbot, _ => true
  | _, .Pbot => true
  | .Gl id1 ofs1, .Gl id2 ofs2 =>
      if id1 = id2 then
        decide (Integers.Ptrofs.unsigned ofs1 + sz1 ≤ Integers.Ptrofs.unsigned ofs2) ||
        decide (Integers.Ptrofs.unsigned ofs2 + sz2 ≤ Integers.Ptrofs.unsigned ofs1)
      else true
  | .Gl id1 _, .Glo id2 => !(decide (id1 = id2))
  | .Glo id1, .Gl id2 _ => !(decide (id1 = id2))
  | .Glo id1, .Glo id2 => !(decide (id1 = id2))
  | .Stk ofs1, .Stk ofs2 =>
      decide (Integers.Ptrofs.unsigned ofs1 + sz1 ≤ Integers.Ptrofs.unsigned ofs2) ||
      decide (Integers.Ptrofs.unsigned ofs2 + sz2 ≤ Integers.Ptrofs.unsigned ofs1)
  | .Gl _ _, .Stk _ | .Glo _, .Stk _ | .Glob, .Stk _ | .Nonstack, .Stk _
  | .Gl _ _, .Stack | .Glo _, .Stack | .Glob, .Stack | .Nonstack, .Stack => true
  | .Stk _, .Gl _ _ | .Stk _, .Glo _ | .Stk _, .Glob | .Stk _, .Nonstack
  | .Stack, .Gl _ _ | .Stack, .Glo _ | .Stack, .Glob | .Stack, .Nonstack => true
  | _, _ => false

/-! ## Changes of block classification, injections -/

/-- `ValueDomain.bc_incr` -/
def bcIncr (bc1 bc2 : BlockClassification) : Prop :=
  ∀ b, bc1 b ≠ .BCinvalid → bc2 b = bc1 b

/-- `ValueDomain.inj_of_bc` -/
def injOfBc (bc : BlockClassification) : Block → Option (Block × Z) :=
  fun b => match bc b with
    | .BCinvalid => none
    | _ => some (b, 0)

end ValueDomain
end CC
