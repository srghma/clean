/-
  Definitions of the port's `lib/` that duplicate Mathlib, Batteries or Lean
  core definitions, with the proofs that they agree.

  `CCLib` imports Lean core only, so `lib/Coqlib.lean`, `lib/CoqlibMore.lean`,
  `lib/Positive.lean`, `lib/Zbits.lean` and `lib/Intv.lean` re-implement a
  number of standard notions.  Each theorem below identifies one of them with
  its library counterpart; they are the rewriting lemmas needed to replace the
  port's definition by the library one.  See `MATHLIB_DUPLICATION.md` for the
  full list (including the duplications that are not definitional, such as
  `Lattice`, `UnionFind` or `Heaps`).
-/
import Mathlib
import CCLib.lib.Coqlib
import CCLib.lib.CoqlibMore
import CCLib.lib.Positive
import CCLib.lib.Zbits
import CCLib.lib.Intv
import CCLib.lib.Parmov

namespace CC
namespace MathlibEquiv

/-! ### `Coqlib.v` -/

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

/-! ### `Coqlib.v`, list part (`CoqlibMore.lean`) -/

/-- `Coqlib.list_disjoint` is Batteries' `List.Disjoint`. -/
theorem list_disjoint_iff {A : Type} (l1 l2 : List A) :
    Coqlib.list_disjoint l1 l2 ↔ List.Disjoint l1 l2 := by
  unfold Coqlib.list_disjoint List.Disjoint
  constructor
  · intro h a h1 h2; exact h a a h1 h2 rfl
  · rintro h x y h1 h2 rfl; exact h h1 h2

/-- `Coqlib.lex_ord` is core's `Prod.Lex`. -/
theorem lex_ord_iff {A B : Type} (ordA : A → A → Prop) (ordB : B → B → Prop) (p q : A × B) :
    Coqlib.lex_ord ordA ordB p q ↔ Prod.Lex ordA ordB p q := by
  constructor
  · rintro (⟨a1, b1, a2, b2, h⟩ | ⟨a, b1, b2, h⟩)
    · exact .left _ _ h
    · exact .right _ h
  · rintro (⟨b1, b2, h⟩ | ⟨a, h⟩)
    · exact .left _ _ _ _ h
    · exact .right _ _ _ h

/-- `Coqlib.list_fold_left` is `List.foldl` (with the arguments of `f` swapped). -/
theorem list_fold_left_eq {A B : Type} (f : A → B → B) (accu : B) (l : List A) :
    Coqlib.list_fold_left f accu l = l.foldl (fun b a => f a b) accu := by
  induction l generalizing accu with
  | nil => rfl
  | cons x l ih => exact ih _

/-- `Coqlib.list_nth_z` is list indexing `l[n]?` at a nonnegative index. -/
theorem list_nth_z_eq {A : Type} (l : List A) (n : ℤ) :
    Coqlib.list_nth_z l n = if n < 0 then none else l[n.toNat]? := by
  induction l generalizing n with
  | nil => simp [Coqlib.list_nth_z]
  | cons hd tl ih =>
    unfold Coqlib.list_nth_z
    by_cases h0 : n = 0
    · subst h0; simp
    · rw [if_neg h0, ih]
      by_cases hn : n < 0
      · rw [if_pos (by omega), if_pos hn]
      · rw [if_neg (by omega), if_neg hn]
        have : n.toNat = (n - 1).toNat + 1 := by omega
        rw [this, List.getElem?_cons_succ]

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

/-! ### `Zbits.v` -/

/-- `Z.testbit` is Batteries' `Int.testBit` (at a nonnegative index). -/
theorem testbit_eq (x : ℤ) (n : ℕ) : Zbits.testbit x n = x.testBit n := by
  unfold Zbits.testbit
  rw [if_neg (by omega)]
  cases x <;> rfl

/-- `Z.land` is Mathlib's `Int.land`. -/
theorem land_eq (x y : ℤ) : Zbits.land x y = Int.land x y := by
  cases x <;> cases y <;> rfl

/-- `Z.lor` is Mathlib's `Int.lor`. -/
theorem lor_eq (x y : ℤ) : Zbits.lor x y = Int.lor x y := by
  cases x <;> cases y <;> rfl

/-- `Z.lnot` is Mathlib's `Int.lnot` (and core's `Int.not`). -/
theorem lnot_eq (x : ℤ) : Zbits.lnot x = Int.lnot x := by
  unfold Zbits.lnot
  cases x with
  | ofNat n => simp [Int.lnot, Int.negSucc_eq]; ring
  | negSucc n => simp [Int.lnot, Int.negSucc_eq]

/-- `Z.div2` is Mathlib's `Int.div2`. -/
theorem div2_eq (x : ℤ) : Zbits.div2 x = Int.div2 x := by
  unfold Zbits.div2; rw [Int.div2_val]

/-- `Z.shiftl` by a nonnegative amount is core's `<<<`. -/
theorem shiftl_eq (x : ℤ) (n : ℕ) : Zbits.shiftl x n = x <<< n := by
  unfold Zbits.shiftl
  rw [if_pos (by omega), Int.shiftLeft_eq]
  simp

/-- `Z.shiftr` by a nonnegative amount is core's `>>>`. -/
theorem shiftr_eq (x : ℤ) (n : ℕ) : Zbits.shiftr x n = x >>> n := by
  unfold Zbits.shiftr Zbits.shiftl
  by_cases hn : n = 0
  · subst hn; simp
  · rw [if_neg (by omega), Int.shiftRight_eq_div_pow]; simp

/-- `eqmod` is Mathlib's `Int.ModEq`. -/
theorem eqmod_iff (m x y : ℤ) : Zbits.eqmod m x y ↔ x ≡ y [ZMOD m] := by
  rw [Int.modEq_comm, Int.modEq_iff_dvd]
  unfold Zbits.eqmod
  constructor
  · rintro ⟨k, rfl⟩; exact ⟨k, by ring⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by linarith⟩

/-- `Z.log2` is Mathlib's `Nat.log 2` on positive numbers. -/
theorem log2_eq (x : ℤ) (hx : 0 < x) : Zbits.log2 x = Nat.log 2 x.toNat := by
  unfold Zbits.log2
  rw [if_neg (by omega), Nat.log2_eq_log_two]

/-- `Zsize` is Mathlib's `Nat.size` on positive numbers. -/
theorem Zsize_eq_size (x : ℤ) (hx : 0 < x) : Zbits.Zsize x = Nat.size x.toNat := by
  rw [Zbits.Zsize_eq hx, Nat.log2_eq_log_two]
  have hn : x.toNat ≠ 0 := by omega
  have : Nat.size x.toNat = Nat.log 2 x.toNat + 1 := by
    apply le_antisymm
    · rw [Nat.size_le]; exact Nat.lt_pow_succ_log_self (by norm_num) _
    · rw [Nat.succ_le_iff, Nat.lt_size]; exact Nat.pow_log_le_self 2 hn
  rw [this]; push_cast; rfl

/-! ### `Intv.v` -/

/-- `Intv.In` is membership in the interval `Set.Ico`. -/
theorem Intv_In_iff (x : ℤ) (i : Intv.Interv) : Intv.In x i ↔ x ∈ Set.Ico i.1 i.2 := Iff.rfl

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
