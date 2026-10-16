/-
  Flocq definitions of the port that duplicate Mathlib / Lean core definitions,
  with the proofs that they agree.

  The Flocq port (`Zaux.lean`, `Raux.lean`, `Digits.lean`, `Generic_fmt.lean`)
  imports Lean core only, so it re-implements a number of standard functions.
  Each theorem below identifies one of them with its Mathlib (or core)
  counterpart; they are the rewriting lemmas needed to replace the port's
  definition by the library one.  See `MATHLIB_DUPLICATION.md` for the list.
-/
import Mathlib
import CCLib.flocq.Core.RauxReal
import CCLib.flocq.Core.Generic_fmtReal

namespace CC
namespace Flocq
namespace MathlibEquiv

/-! ### `Zaux.v` -/

/-- `Zpower b e` is `b ^ e` for `e ≥ 0` (Mathlib/core `HPow ℤ ℕ ℤ`). -/
theorem Zpower_eq_pow (b e : ℤ) (he : 0 ≤ e) : Zpower b e = b ^ e.toNat := by
  conv_lhs => rw [← Int.toNat_of_nonneg he]
  rfl

/-- `Zeven` is Mathlib's `Even`. -/
theorem Zeven_iff_even (x : ℤ) : Zeven x = true ↔ Even x := by
  unfold Zeven; rw [Int.even_iff]; simp

/-- The quotient of `Zdiv_eucl` (`Int.fdiv`) is floor division `⌊a / b⌋`
(for a positive divisor, it is also Lean's `a / b`). -/
theorem Zdiv_eucl_fst (a b : ℤ) (hb : 0 < b) : (Zdiv_eucl a b).1 = ⌊(a : ℚ) / b⌋ := by
  show a.fdiv b = _
  rw [Int.fdiv_eq_ediv_of_nonneg a hb.le]
  have : (b : ℚ) = ((b.toNat : ℕ) : ℚ) := by exact_mod_cast (Int.toNat_of_nonneg hb.le).symm
  rw [this, Rat.floor_intCast_div_natCast]
  congr; omega

/-! ### `Raux.v` -/

/-- `Rabs` is the absolute value `|·|`. -/
theorem Rabs_eq (q : ℚ) : Rabs q = |q| := Rabs_eq_abs q

/-- `Rcompare` is `compare`. -/
theorem Rcompare_eq (x y : ℚ) : Rcompare x y = compare x y := by
  unfold Rcompare
  rcases lt_trichotomy x y with h | h | h
  · rw [if_pos h, compare_lt_iff_lt.mpr h]
  · subst h; rw [if_neg (lt_irrefl _), if_pos rfl, compare_eq_iff_eq.mpr rfl]
  · rw [if_neg (not_lt.mpr h.le), if_neg (ne_of_gt h), compare_gt_iff_gt.mpr h]

/-- `Zfloor` is Mathlib's `Int.floor`. -/
theorem Zfloor_eq (q : ℚ) : Zfloor q = ⌊q⌋ := Zfloor_eq_floor q

/-- `Zceil` is Mathlib's `Int.ceil`. -/
theorem Zceil_eq (q : ℚ) : Zceil q = ⌈q⌉ := Zceil_eq_ceil q

/-- `bpow r e` is the integer power `(r : ℚ) ^ e` (`zpow`). -/
theorem bpow_eq_zpow (r : radix) (e : ℤ) : bpow r e = (r.radix_val : ℚ) ^ e := rfl

/-- `mag r x` is `Int.log r |x| + 1` (Mathlib's integer logarithm). -/
theorem mag_eq_log (r : radix) (q : ℚ) (hq : q ≠ 0) :
    mag r q = Int.log r.radix_val.toNat |q| + 1 := by
  have hb := radix_toNat_gt_one r
  have hcast : ((r.radix_val.toNat : ℕ) : ℚ) = (r.radix_val : ℚ) := by
    have : (0 : ℤ) ≤ r.radix_val := by have := radix_gt_1 r; omega
    exact_mod_cast Int.toNat_of_nonneg this
  apply mag_unique
  rw [Rabs_eq_abs, bpow_eq_zpow, bpow_eq_zpow, add_sub_cancel_right, ← hcast]
  exact ⟨Int.zpow_log_le_self hb (abs_pos.mpr hq), Int.lt_zpow_succ_log_self hb _⟩

/-! ### `Generic_fmt.v` -/

/-- Rounding to nearest with ties away from zero on nonnegative numbers, i.e.
`Znearest (fun _ => true)`, is Mathlib's `round` (ties go up). -/
theorem Znearest_true_eq_round (q : ℚ) : Znearest (fun _ => true) q = _root_.round q := by
  rw [Znearest_eq, round_eq, Zfloor_eq, Zceil_eq]
  have h0 := Int.floor_le q
  have h1 := Int.lt_floor_add_one q
  simp only [if_true]
  split_ifs with ha
  · symm; rw [Int.floor_eq_iff]; constructor <;> linarith
  all_goals
    have hge : 1 / 2 ≤ q - ⌊q⌋ := not_lt.mp ha
    have hc : ⌈q⌉ = ⌊q⌋ + 1 := by
      rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
    rw [hc]; symm; rw [Int.floor_eq_iff]; push_cast
    constructor <;> linarith

/-! ### `Digits.v` -/

/-- `Zdigits beta n` is the length of the base-`beta` digit list of `|n|`
(Mathlib's `Nat.digits`). -/
theorem Zdigits_eq_digits_length (beta : radix) (n : ℤ) :
    Zdigits beta n = ((Nat.digits beta.radix_val.toNat n.natAbs).length : ℤ) := by
  by_cases hn : n = 0
  · subst hn; simp [Zdigits]
  have hb := radix_toNat_gt_one beta
  have hN : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn
  have hpow : ∀ k : ℤ, 0 ≤ k →
      Zpower beta.radix_val k = ((beta.radix_val.toNat ^ k.toNat : ℕ) : ℤ) := by
    intro k hk
    rw [Zpower_eq_pow _ _ hk]; push_cast
    rw [Int.toNat_of_nonneg (by have := radix_gt_1 beta; omega)]
  have hd := Zdigits_gt_0 beta n hn
  obtain ⟨c1, c2⟩ := Zdigits_correct beta n
  rw [hpow _ (by omega)] at c1
  rw [hpow _ (by omega)] at c2
  rw [Nat.length_digits _ _ hb hN]
  have hlog : Nat.log beta.radix_val.toNat n.natAbs = (Zdigits beta n - 1).toNat := by
    rw [Nat.log_eq_iff (Or.inr ⟨hb, hN⟩)]
    refine ⟨by exact_mod_cast c1, ?_⟩
    have : (Zdigits beta n - 1).toNat + 1 = (Zdigits beta n).toNat := by omega
    rw [this]; exact_mod_cast c2
  rw [hlog]; push_cast; omega

end MathlibEquiv
end Flocq
end CC
