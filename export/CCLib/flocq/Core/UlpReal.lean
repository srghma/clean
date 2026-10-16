/-
  Port of the error bounds of Flocq's `Core/Ulp.v` (Flocq 4, as shipped with
  CompCert) for arbitrary real arguments, over Mathlib's `ℝ`.

  Copyright (C) 2010-2018 Sylvie Boldo, Guillaume Melquiond (Flocq, LGPL-3.0+).

  `Ulp.lean` proves the theory over `Rat`.  Here:
  * `ulpR` is Rocq's `ulp` on `R`, and `ulpR_cast` says that it agrees with the
    rational `ulp` on rationals;
  * `error_lt_ulpR`, `error_le_ulpR` and `error_le_half_ulpR` are Rocq's
    `error_lt_ulp`, `error_le_ulp` and `error_le_half_ulp` for every real
    argument (with a rounding function `ℝ → ℤ` satisfying `Valid_rndR`, resp.
    `ZnearestR choice`).
-/
import CCLib.flocq.Core.Generic_fmtRealRound
import CCLib.flocq.Core.Ulp

namespace CC
namespace Flocq

noncomputable section

section Fcore_ulp
variable (beta : radix) (fexp : ℤ → ℤ)

open Classical in
/-- `Ulp.ulp` on `R`. -/
def ulpR (x : ℝ) : ℝ :=
  if x = 0 then
    match negligible_exp fexp with
    | some n => bpowR beta (fexp n)
    | none => 0
  else bpowR beta (cexpR beta fexp x)

theorem ulpR_neq_0 (x : ℝ) (hx : x ≠ 0) : ulpR beta fexp x = bpowR beta (cexpR beta fexp x) := by
  unfold ulpR; rw [if_neg hx]

theorem ulpR_ge_0 (x : ℝ) : 0 ≤ ulpR beta fexp x := by
  unfold ulpR
  split
  · split
    · exact (bpowR_pos beta _).le
    · exact le_refl 0
  · exact (bpowR_pos beta _).le

/-- On rationals, the real `ulp` is the rational `ulp`. -/
theorem ulpR_cast (q : ℚ) : ulpR beta fexp q = ((ulp beta fexp q : ℚ) : ℝ) := by
  unfold ulpR ulp
  by_cases hq : q = 0
  · subst hq
    simp only [Rat.cast_zero, if_true]
    rcases negligible_exp fexp with _ | n <;> simp [bpow_cast]
  · have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
    rw [if_neg hq', if_neg hq, bpow_cast, cexpR_cast]

/-- `Ulp.error_lt_ulp` on `ℝ`. -/
theorem error_lt_ulpR (rnd : ℝ → ℤ) [Valid_rndR rnd] (x : ℝ) (hx : x ≠ 0) :
    |roundR beta fexp rnd x - x| < ulpR beta fexp x := by
  rw [ulpR_neq_0 beta fexp x hx, roundR_sub, abs_mul, abs_of_pos (bpowR_pos beta _)]
  have := ZrndR_abs_sub_lt rnd (scaled_mantissaR beta fexp x)
  have hB := bpowR_pos beta (cexpR beta fexp x)
  nlinarith

/-- `Ulp.error_le_ulp` on `ℝ`. -/
theorem error_le_ulpR (rnd : ℝ → ℤ) [Valid_rndR rnd] (x : ℝ) :
    |roundR beta fexp rnd x - x| ≤ ulpR beta fexp x := by
  by_cases hx : x = 0
  · rw [hx, roundR_0, sub_zero, abs_zero]; exact ulpR_ge_0 beta fexp 0
  · exact (error_lt_ulpR beta fexp rnd x hx).le

/-- `Ulp.error_le_half_ulp` on `ℝ`. -/
theorem error_le_half_ulpR (choice : ℤ → Bool) (x : ℝ) :
    |roundR beta fexp (ZnearestR choice) x - x| ≤ 1 / 2 * ulpR beta fexp x := by
  by_cases hx : x = 0
  · rw [hx, roundR_0, sub_zero, abs_zero]
    have := ulpR_ge_0 beta fexp 0
    positivity
  · rw [ulpR_neq_0 beta fexp x hx, roundR_sub, abs_mul, abs_of_pos (bpowR_pos beta _)]
    have := ZnearestR_abs_sub_le choice (scaled_mantissaR beta fexp x)
    have hB := bpowR_pos beta (cexpR beta fexp x)
    nlinarith

end Fcore_ulp

end

end Flocq
end CC
