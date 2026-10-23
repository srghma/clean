/-
  Definitions of the port that duplicate Mathlib, Batteries or Lean core
  definitions, with the proofs that they agree (see `MATHLIB_DUPLICATION.md`).

  `CCLib` imports Lean core only, so a few standard notions are re-implemented
  there: `ListForall2`/`OptionRel` (Rocq's `list_forall2`/`option_rel`),
  floor division and alignment (`zdiv`, `floorZ`, `align`, from Rocq's
  `Coqlib.v`), Rocq's `positive` and Parmov's reflexive-transitive closure.
  Each theorem below identifies one of them with its library counterpart.

  This module is the root of the `CCLibMathlib` library (it imports Mathlib).
-/
import Mathlib
import CCLib.common.LinkingTheory
import CCLib.cfrontend.CtypesTheory
import CCLib.lib.Positive
import CCLib.lib.Parmov

namespace CC
namespace MathlibEquiv

/-! ### `Coqlib.v` notions defined in the port (`ListForall2`, `OptionRel` in
`common/LinkingTheory.lean`; `zdiv`, `floorZ`, `align` in `cfrontend/Ctypes.lean`) -/

/-- `Coqlib.list_forall2` is Batteries' `List.Forall₂`. -/
theorem listForall2_iff {A B : Type} (R : A → B → Prop) (l1 : List A) (l2 : List B) :
    ListForall2 R l1 l2 ↔ List.Forall₂ R l1 l2 := by
  constructor
  · intro h
    induction h with
    | nil => exact .nil
    | cons hab _ ih => exact .cons hab ih
  · intro h
    induction h with
    | nil => exact .nil
    | cons hab _ ih => exact .cons hab ih

/-- `Coqlib.option_rel` is core's `Option.Rel`. -/
theorem optionRel_iff {A B : Type} (R : A → B → Prop) (o1 : Option A) (o2 : Option B) :
    OptionRel R o1 o2 ↔ Option.Rel R o1 o2 := by
  constructor
  · rintro (_ | ⟨h⟩)
    · exact .none
    · exact .some h
  · rintro (⟨h⟩ | _)
    · exact .some h
    · exact .none

/-- `zdiv` (Rocq's `Z.div`) is floor division. -/
theorem zdiv_eq_floor (a b : ℤ) (hb : 0 < b) : zdiv a b = ⌊(a : ℚ) / b⌋ := by
  rw [zdiv_eq _ _ hb]
  have : (b : ℚ) = ((b.toNat : ℕ) : ℚ) := by exact_mod_cast (Int.toNat_of_nonneg hb.le).symm
  rw [this, Rat.floor_intCast_div_natCast]
  congr; omega

/-- `Coqlib.floor` (`floorZ`) rounds down to a multiple: `⌊n / a⌋ * a`. -/
theorem floorZ_eq_floor (n a : ℤ) (ha : 0 < a) : floorZ n a = ⌊(n : ℚ) / a⌋ * a := by
  unfold floorZ; rw [zdiv_eq_floor _ _ ha]

/-- `Coqlib.align` rounds up to a multiple: `⌈n / a⌉ * a`. -/
theorem align_eq_ceil (n a : ℤ) (ha : 0 < a) : align n a = ⌈(n : ℚ) / a⌉ * a := by
  unfold align; rw [zdiv_eq _ _ ha]
  congr 1
  symm
  rw [Int.ceil_eq_iff]
  have ha' : (0 : ℚ) < a := by exact_mod_cast ha
  have h1 := Int.mul_ediv_add_emod (n + a - 1) a
  have h2 := Int.emod_nonneg (n + a - 1) ha.ne'
  have h3 := Int.emod_lt_of_pos (n + a - 1) ha
  have i1 : ((n + a - 1) / a - 1) * a < n := by linarith
  have i2 : n ≤ (n + a - 1) / a * a := by linarith
  constructor
  · rw [lt_div_iff₀ ha']; exact_mod_cast i1
  · rw [div_le_iff₀ ha']; exact_mod_cast i2

/-! ### `Positive` (Rocq's `positive`) and Mathlib's `PosNum` -/

/-- Rocq's `positive` is Mathlib's `PosNum` (same three constructors). -/
def Positive.toPosNum : Positive → PosNum
  | .xH => .one
  | .xO p => .bit0 (Positive.toPosNum p)
  | .xI p => .bit1 (Positive.toPosNum p)

def Positive.ofPosNum : PosNum → Positive
  | .one => .xH
  | .bit0 p => .xO (Positive.ofPosNum p)
  | .bit1 p => .xI (Positive.ofPosNum p)

/-- `Positive ≃ PosNum`. -/
def Positive.equivPosNum : Positive ≃ PosNum where
  toFun := Positive.toPosNum
  invFun := Positive.ofPosNum
  left_inv p := by
    induction p with
    | xH => rfl
    | xO p ih => simp [Positive.toPosNum, Positive.ofPosNum, ih]
    | xI p ih => simp [Positive.toPosNum, Positive.ofPosNum, ih]
  right_inv p := by
    induction p with
    | one => rfl
    | bit0 p ih => simp [Positive.toPosNum, Positive.ofPosNum, ih]
    | bit1 p ih => simp [Positive.toPosNum, Positive.ofPosNum, ih]

/-- The equivalence preserves the numeric value. -/
theorem Positive.toPosNum_toNat (p : Positive) : ((Positive.toPosNum p : PosNum) : ℕ) = p.toNat := by
  induction p with
  | xH => rfl
  | xO p ih => simp [Positive.toPosNum, Positive.toNat, ih]; ring
  | xI p ih => simp [Positive.toPosNum, Positive.toNat, ih]; ring

/-- `Pos.succ` is `PosNum.succ`. -/
theorem Positive.toPosNum_succ (p : Positive) :
    Positive.toPosNum (Positive.succ p) = PosNum.succ (Positive.toPosNum p) := by
  induction p with
  | xH => rfl
  | xO p _ => rfl
  | xI p ih => simp [Positive.succ, Positive.toPosNum, PosNum.succ, ih]

/-! ### `Parmov.v` -/

/-- `Parmov.Star` (Rocq's `clos_refl_trans`) is Mathlib's `Relation.ReflTransGen`. -/
theorem Parmov_Star_iff {α : Type _} (R : α → α → Prop) (x y : α) :
    Parmov.Star R x y ↔ Relation.ReflTransGen R x y := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | step h _ ih => exact Relation.ReflTransGen.head h ih
  · intro h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact .refl _
    | head h _ ih => exact .step h ih

end MathlibEquiv
end CC
