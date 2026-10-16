# Code in the Lean port that duplicates Mathlib, Batteries or Lean core

The `CCLib` library (`export/CCLib`) imports only Lean core. That keeps
`import CCLib` light and lets `export/lakefile.toml` build without Mathlib,
but it means the port re-implements several standard notions. This file lists
them, the library definition each one duplicates, and whether a Lean proof
connects the two.

**Bridge files.** Each entry marked *proved* has a theorem stating that the
port's definition equals (or is equivalent to) the library one:

* `export/CCLib/lib/MathlibEquiv.lean` (namespace `CC.MathlibEquiv`)
* `export/CCLib/flocq/Core/MathlibEquiv.lean` (namespace `CC.Flocq.MathlibEquiv`)

Both are part of the `CCLibReal` root (`lake build CCLibReal`). They contain
no `sorry`, and their theorems depend only on `propext`, `Classical.choice`
and `Quot.sound`. You can use these theorems to rewrite the port's
definitions into the library ones.

**How to replace them.** Swapping a definition inside `CCLib` itself means
`CCLib` has to depend on Mathlib (or Batteries). For a definition that is
used in many places, the cheapest route is a one-line change of the
definition (for example `abbrev list_disjoint := List.Disjoint`), keeping the
port's name. The bridge theorem then shows that every existing statement
keeps its meaning. Only proofs that unfold the old definition need repairs.
Definitions marked *keep* compute in the kernel (`decide`, `rfl`) in ways the
library version may not, or have different semantics. They should not be
replaced blindly.

Legend: **proved** = equivalence proved in a bridge file; **same def** = the
port already defines it through the library notion; **report only** = similar
in purpose but not definitionally the same (no equivalence theorem).

## `lib/` (Rocq `lib/`)

| Port definition (file) | Library counterpart (origin) | Status / bridge theorem | Recommendation |
|---|---|---|---|
| `ListForall2` (`lib/Coqlib.lean`) | `List.Forall₂` (Batteries) | **proved** `listForall2_iff` | replace (Batteries) |
| `OptionRel` (`lib/Coqlib.lean`) | `Option.Rel` (core) | **proved** `optionRel_iff` | replace now (core, no new dependency) |
| `zdiv` (`lib/Coqlib.lean`) | `Int.fdiv` (core), `⌊a / b⌋` (Mathlib) | **same def** (`Int.fdiv`); **proved** `zdiv_eq_floor` | keep the name, it is already `Int.fdiv` |
| `align`, `floorZ` (`lib/Coqlib.lean`) | `⌈n / a⌉ * a`, `⌊n / a⌋ * a` (Mathlib) | **proved** `align_eq_ceil`, `floorZ_eq_floor` | keep (they compute on `Int`), use the bridge for reasoning |
| `Coqlib.list_disjoint` (`lib/CoqlibMore.lean`) | `List.Disjoint` (Batteries) | **proved** `list_disjoint_iff` | replace (Batteries) |
| `Coqlib.list_norepet` (`lib/CoqlibMore.lean`) | `List.Nodup` (core) | **same def** (`abbrev`) | already done |
| `Clight.listNorepet` (`cfrontend/Clight.lean`) | `List.Nodup` (core) | **same def** (`def … := l.Nodup`, a second copy of `Coqlib.list_norepet`) | make it an `abbrev` of `List.Nodup` (or of `Coqlib.list_norepet`) |
| `Coqlib.is_tail` (`lib/CoqlibMore.lean`) | `List.IsSuffix` `<:+` (core) | the port proves `is_tail_iff_suffix` | replace now |
| `Coqlib.lex_ord` (`lib/CoqlibMore.lean`) | `Prod.Lex` (core) | **proved** `lex_ord_iff` (core also has `WellFounded.prod_lex` for `wf_lex_ord`) | replace now |
| `Coqlib.list_fold_left` (`lib/CoqlibMore.lean`) | `List.foldl` (core) | **proved** `list_fold_left_eq` | replace now |
| `Coqlib.list_nth_z` (`lib/CoqlibMore.lean`) | `l[n]?` (core) | **proved** `list_nth_z_eq` | replace now |
| `Coqlib.list_length_z` (`lib/CoqlibMore.lean`) | `List.length` (core) | the port proves `list_length_z_eq` | replace now |
| `Coqlib.list_drop` (`lib/CoqlibMore.lean`) | `List.drop` (core) | the port proves `list_drop_eq` | replace now |
| `Positive` with `toNat`, `succ` (`lib/Positive.lean`) | `PosNum` (Mathlib, the same three constructors) | **proved** `Positive.equivPosNum : Positive ≃ PosNum`, `Positive.toPosNum_toNat`, `Positive.toPosNum_succ` | keep (all of `clightgen`'s output and `PTree` keys use it), use the equivalence to import Mathlib's `PosNum` lemmas |
| `Zbits.testbit` (`lib/Zbits.lean`) | `Int.testBit` (Batteries) | **proved** `testbit_eq` | replace (Batteries) |
| `Zbits.land`, `Zbits.lor` | `Int.land`, `Int.lor` (Mathlib) | **proved** `land_eq`, `lor_eq` (they hold by `rfl`) | replace |
| `Zbits.lnot` | `Int.lnot` (Mathlib), `Int.not` (core) | **proved** `lnot_eq` | replace now (`Int.not`) |
| `Zbits.div2` | `Int.div2` (Mathlib) | **proved** `div2_eq` | replace |
| `Zbits.shiftl`, `Zbits.shiftr` (nonnegative shift) | `<<<`, `>>>` on `Int` (core) | **proved** `shiftl_eq`, `shiftr_eq` | keep (Rocq's version also takes negative amounts), use the bridge |
| `Zbits.eqmod` | `Int.ModEq` `a ≡ b [ZMOD n]` (Mathlib) | **proved** `eqmod_iff` | replace |
| `Zbits.log2` | `Nat.log 2` (Mathlib), `Nat.log2` (core) | **same def** (`Nat.log2`); **proved** `log2_eq` | already done |
| `Zbits.Zsize`, `Zbits.Pos.size` | `Nat.size` (Mathlib) | **proved** `Zsize_eq_size` | replace |
| `Intv.In` (`lib/Intv.lean`) | `Set.Ico` (Mathlib) | **proved** `Intv_In_iff` (`Iff.rfl`) | replace |
| `Parmov.Star` (`lib/Parmov.lean`) | `Relation.ReflTransGen` (Mathlib) | **proved** `Parmov_Star_iff` | replace |
| `Wfsimpl.Fix`, `unroll_Fix` (`lib/Wfsimpl.lean`) | `WellFounded.fix`, `WellFounded.fix_eq` (core) | **same def** | already done |
| `Decidableplus`, `BoolEqual` (`lib/`) | `Decidable`, `deriving DecidableEq` (core) | **same def** (the files only add a few instances) | already done |
| `Decidableplus.Finite` | `Fintype` / `Finite` (Mathlib) | report only | replace (Mathlib) if the decision procedures are needed beyond `Bool`/pairs/options |
| `Semilattice` (`lib/Lattice.lean`, `LatticeMore.lean`) | `SemilatticeSup` + `OrderBot` (Mathlib) | report only: the port's class uses a setoid `eq` and a Boolean `beq`, as in Rocq, while Mathlib's uses Lean equality | keep for the dataflow solvers; an instance from `SemilatticeSup` + `OrderBot` + `DecidableEq` would be easy to add |
| `GenIter` (`lib/Iteration.lean`) | `OrderHom.lfp` / Kleene iteration (Mathlib) | report only | keep (the solvers need `PrimIter`'s fuel-bounded, computable form) |
| `OrderedType` (`lib/Ordered.lean`) | `LinearOrder` + `compare` (Mathlib), `Std.TransCmp` (core) | report only | keep while `FSetAVL`/`Heaps` use it |
| `FSetAVL` (`lib/FSetAVL.lean`, ~Rocq's `MSetAVL`) | `Std.TreeSet` (core `Std`), `Finset` (Mathlib) | report only: a port of Rocq's standard library, with Rocq's specification names | could be replaced by `Std.TreeSet`, but `FSetAVLplus` relies on the internal tree shape |
| `SplayHeapSet` (`lib/Heaps.lean`) | `Batteries.PairingHeap`, `Batteries.BinomialHeap` | report only (different data structure) | keep (faithful to Rocq) |
| `UnionFind` (`lib/UnionFind*.lean`) | `Batteries.UnionFind` | report only: Rocq's version is persistent over `PTree`, Batteries' is array-based | keep |
| `PTree`, `PMap`, `ZMap` (`lib/Maps*.lean`) | `Std.TreeMap`, `Std.HashMap` | report only: CompCert's maps are keyed by `positive` and have extensionality lemmas | keep |
| `Integers` (`lib/Integers*.lean`) | `BitVec` (core) | **same def**: the machine integers are already built on `BitVec` | already done |

## `flocq/` (Rocq `flocq/`)

| Port definition (file) | Library counterpart (origin) | Status / bridge theorem | Recommendation |
|---|---|---|---|
| `Zpower` (`flocq/Core/Zaux.lean`) | `b ^ e.toNat` (core) | **proved** `Zpower_eq_pow` | keep (Rocq's version is `0` for negative exponents) |
| `Zeven` | `Even` (Mathlib) | **proved** `Zeven_iff_even` | replace |
| `Zeq_bool`, `Zle_bool`, `Zlt_bool`, `Rle_bool`, `Rlt_bool`, `Req_bool` | `decide` (core) | **same def** | already done |
| `Zdiv_eucl` | `Int.fdiv`, `Int.fmod` (core), `⌊a / b⌋` (Mathlib) | **same def**; **proved** `Zdiv_eucl_fst` | already done |
| `Rabs` (`flocq/Core/Raux.lean`) | `|·|` (Mathlib) | **proved** `Rabs_eq` (= `Rabs_eq_abs`) | replace |
| `Rcompare` | `compare` (core) | **proved** `Rcompare_eq` | replace |
| `Zfloor`, `Zceil` | `Int.floor`, `Int.ceil` (Mathlib), `Rat.floor`, `Rat.ceil` (core) | **same def** (`Rat.floor`); **proved** `Zfloor_eq`, `Zceil_eq` | replace |
| `Ztrunc`, `Zaway` | `Int.floor`/`Int.ceil` by sign | report only (Mathlib has no truncation for ordered fields) | keep |
| `Znearest (fun _ => true)` (`flocq/Core/Generic_fmt.lean`) | `round` (Mathlib, ties toward `+∞`) | **proved** `Znearest_true_eq_round` | keep `Znearest` (Flocq needs every tie-breaking rule) |
| `bpow` | `zpow` (core/Mathlib) | **same def** (`(r : ℚ) ^ e`); **proved** `bpow_eq_zpow` | already done |
| `mag` | `Int.log` (Mathlib): `mag r x = Int.log r |x| + 1` | **proved** `mag_eq_log` | replace |
| `Zdigits` (`flocq/Core/Digits.lean`) | `(Nat.digits b n).length` (Mathlib) | **proved** `Zdigits_eq_digits_length` | keep (it computes quickly in the kernel), use the bridge |
| `RatSqrtField`, `RatExpField` (`flocq/Core/RauxSqrt.lean`, `RauxExp.lean`) | `Real.sqrt`, `Real.exp`, `Real.log` (Mathlib) | `ℝ` is an instance of both classes (`flocq/Core/RauxReal.lean`) | done: the classes now apply to the reals |
| about 25 small `Rat` lemmas (`rat_lt_or_le`, `rat_sub_mul`, `rat_mul_le_mul`, `rat_inv_nonneg`, … in `Generic_fmt.lean`, `Raux.lean`, `Ulp.lean`, `Relative.lean`, `Div_sqrt_error.lean`) | `lt_or_ge`, `sub_mul`, `mul_le_mul`, `inv_nonneg`, … (Mathlib), or `linarith` / `field_simp` | report only | replace once Flocq imports Mathlib |

## Duplication inside the port

These are not library duplicates, but the same notion is defined more than once in the port:

| Definitions | Remark |
|---|---|
| `Clight.Star`/`Clight.Plus` (`cfrontend/Clight.lean`), `Smallstep.Star`/`Smallstep.Plus` (`common/Smallstep.lean`), `Determinism.StarE0` (`common/Determinism.lean`), `Parmov.Star` (`lib/Parmov.lean`) | four reflexive-transitive closures. `Clight.Star`/`Plus` have exactly the constructors of `Smallstep.Star`/`Plus`, restricted to Clight states. `Parmov.Star` is `Relation.ReflTransGen` (Mathlib; see `Parmov_Star_iff`), and `StarE0` is `Relation.ReflTransGen` of the silent steps |
| `Rabs_eq_abs` (`flocq/Core/RauxReal.lean`) and `Rabs_eq` (bridge) | the bridge reuses the existing theorem |

### Per-target copies of the back end (largest duplication in the port)

Rocq compiles one copy of each back-end file (`backend/*.v`) against the
target directory selected at configuration time (`aarch64/Op.v`,
`arm/Op.v`, …). The Lean port instead holds every supported target at once,
so the target-independent passes and their proofs exist up to five times:
`backend/` (the aarch64 instance) and the copies in `arm/`, `powerpc/`,
`riscV/` and `x86/`, which differ only in namespace, imports and the header
comment. `TARGET_DUPLICATION.md` (repository root) lists all 163 file names
that occur in more than one of these directories, with a similarity score
after the target names are normalized:

* 58 files are at least 95% identical across all their copies (for example
  `RTL`, `RTLgen*`, `Inlining*`, `Deadcode*`, `Unusedglob*`, `Tunneling*`,
  `Linearize`, `Liveness`, `IRC`, `XTL`, `CminorSel`, `ValueAnalysisSound*`).
  Their extra copies amount to about 63,000 non-blank lines;
* 96 files are at least 85% identical (about 108,000 non-blank lines of extra
  copies), adding for example `CSE*`, `Allocation`, `Constprop*`,
  `Debugvar*`, `LTL`, `Linear`, `Locations`, `Tailcallproof`, `Asmgenproof0`.

How to remove it: make the shared files generic in the target, i.e. take the
target's `Op`/`Machregs`/`Conventions1` definitions and lemmas as a structure
or type class argument (a Lean counterpart of Rocq's per-target
`Parameter`s), and instantiate it once per target. This is a refactor of
about 100 files per target with no library replacement; it is not done here.
