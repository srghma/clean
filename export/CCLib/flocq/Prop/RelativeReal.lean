/-
  Port of the relative-error bounds of Flocq's `Prop/Relative.v` (Flocq 4, as
  shipped with CompCert) for arbitrary real arguments, over Mathlib's `ℝ`.

  Copyright (C) 2010-2018 Sylvie Boldo, Guillaume Melquiond (Flocq, LGPL-3.0+).

  `Relative.lean` proves these bounds over `Rat`.  Here they hold for every
  real `x` (with `roundR`, `ZnearestR` and `Valid_rndR` from
  `Core/Generic_fmtRealRound.lean`):
  * `relative_errorR`, `relative_errorR_ex`, `relative_error_NR`,
    `relative_error_NR_ex` (Rocq's `relative_error`, `relative_error_ex`,
    `relative_error_N`, `relative_error_N_ex`) for a generic format;
  * their FLX instances `relative_error_FLXR`, `relative_error_FLXR_ex`,
    `relative_error_N_FLXR`, `relative_error_N_FLXR_ex`;
  * their FLT instances `relative_error_FLTR`, `relative_error_N_FLTR`
    (above the underflow threshold `bpow (emin + prec - 1)`).
-/
import CCLib.flocq.Core.UlpReal
import CCLib.flocq.Core.FLX
import CCLib.flocq.Core.FLT

namespace CC
namespace Flocq

noncomputable section

section Fprop_relative_generic
variable (beta : radix) (fexp : ℤ → ℤ) (emin p : ℤ)

/-- The `ulp` of `x` is at most `bpow (-p + 1) * |x|` when the format has at
least `p` digits above `emin`. -/
theorem relative_ulpR_le (Hmin : ∀ k, emin < k → p ≤ k - fexp k) (x : ℝ)
    (Hx : bpowR beta emin ≤ |x|) : ulpR beta fexp x ≤ bpowR beta (-p + 1) * |x| := by
  have hx : x ≠ 0 := by
    intro h; rw [h, abs_zero] at Hx; exact absurd Hx (not_le.mpr (bpowR_pos beta _))
  obtain ⟨h1, h2⟩ := magR_spec beta x hx
  have he : emin < magR beta x := by
    have := (bpowR_lt_iff beta _ _).1 (lt_of_le_of_lt Hx h2); exact this
  have hp := Hmin _ he
  rw [ulpR_neq_0 beta fexp x hx]
  calc bpowR beta (cexpR beta fexp x)
      ≤ bpowR beta (-p + 1 + (magR beta x - 1)) := bpowR_mono beta (by unfold cexpR; omega)
    _ = bpowR beta (-p + 1) * bpowR beta (magR beta x - 1) := (bpowR_plus beta _ _)
    _ ≤ bpowR beta (-p + 1) * |x| := mul_le_mul_of_nonneg_left h1 (bpowR_pos beta _).le

/-- `Relative.relative_error` on `ℝ`. -/
theorem relative_errorR (Hmin : ∀ k, emin < k → p ≤ k - fexp k) (rnd : ℝ → ℤ) [Valid_rndR rnd]
    (x : ℝ) (Hx : bpowR beta emin ≤ |x|) :
    |roundR beta fexp rnd x - x| < bpowR beta (-p + 1) * |x| := by
  have hx : x ≠ 0 := by
    intro h; rw [h, abs_zero] at Hx; exact absurd Hx (not_le.mpr (bpowR_pos beta _))
  exact lt_of_lt_of_le (error_lt_ulpR beta fexp rnd x hx)
    (relative_ulpR_le beta fexp emin p Hmin x Hx)

/-- `Relative.relative_error_N` on `ℝ`. -/
theorem relative_error_NR (Hmin : ∀ k, emin < k → p ≤ k - fexp k) (choice : ℤ → Bool)
    (x : ℝ) (Hx : bpowR beta emin ≤ |x|) :
    |roundR beta fexp (ZnearestR choice) x - x| ≤ 1 / 2 * bpowR beta (-p + 1) * |x| := by
  have := relative_ulpR_le beta fexp emin p Hmin x Hx
  have := error_le_half_ulpR beta fexp choice x
  nlinarith

/-- A relative error bound gives the `x * (1 + eps)` form
(`Relative.relative_error_lt_conversion` / `relative_error_le_conversion`). -/
theorem relative_error_conversionR (r x : ℝ) (b : ℝ) (hb : 0 ≤ b)
    (h : x ≠ 0 → |r - x| ≤ b * |x|) (h0 : x = 0 → r = 0) :
    ∃ eps, |eps| ≤ b ∧ r = x * (1 + eps) := by
  by_cases hx : x = 0
  · exact ⟨0, by simpa using hb, by rw [h0 hx, hx]; ring⟩
  · refine ⟨(r - x) / x, ?_, by field_simp; ring⟩
    rw [abs_div, div_le_iff₀ (abs_pos.mpr hx)]
    exact h hx

theorem relative_error_conversionR_lt (r x : ℝ) (b : ℝ) (hb : 0 < b)
    (h : x ≠ 0 → |r - x| < b * |x|) (h0 : x = 0 → r = 0) :
    ∃ eps, |eps| < b ∧ r = x * (1 + eps) := by
  by_cases hx : x = 0
  · exact ⟨0, by simpa using hb, by rw [h0 hx, hx]; ring⟩
  · refine ⟨(r - x) / x, ?_, by field_simp; ring⟩
    rw [abs_div, div_lt_iff₀ (abs_pos.mpr hx)]
    exact h hx

end Fprop_relative_generic

section Fprop_relative_FLX
variable (beta : radix) (prec : ℤ)

theorem relative_error_FLXR_aux (k : ℤ) : prec ≤ k - FLX_exp prec k := by
  unfold FLX_exp; omega

/-- `Relative.relative_error_FLX` on `ℝ`. -/
theorem relative_error_FLXR (rnd : ℝ → ℤ) [Valid_rndR rnd] (x : ℝ) (Hx : x ≠ 0) :
    |roundR beta (FLX_exp prec) rnd x - x| < bpowR beta (-prec + 1) * |x| :=
  relative_errorR beta (FLX_exp prec) (magR beta x - 1) prec
    (fun k _ => relative_error_FLXR_aux prec k) rnd x (magR_spec beta x Hx).1

/-- `Relative.relative_error_FLX_ex` on `ℝ`: the `1 + ε` property in FLX. -/
theorem relative_error_FLXR_ex (rnd : ℝ → ℤ) [Valid_rndR rnd] (x : ℝ) :
    ∃ eps, |eps| < bpowR beta (-prec + 1) ∧ roundR beta (FLX_exp prec) rnd x = x * (1 + eps) :=
  relative_error_conversionR_lt _ x _ (bpowR_pos beta _)
    (relative_error_FLXR beta prec rnd x)
    (fun h => by rw [h, roundR_0])

/-- `Relative.relative_error_N_FLX` on `ℝ`. -/
theorem relative_error_N_FLXR (choice : ℤ → Bool) (x : ℝ) :
    |roundR beta (FLX_exp prec) (ZnearestR choice) x - x| ≤
      1 / 2 * bpowR beta (-prec + 1) * |x| := by
  by_cases Hx : x = 0
  · rw [Hx, roundR_0]; simp
  · exact relative_error_NR beta (FLX_exp prec) (magR beta x - 1) prec
      (fun k _ => relative_error_FLXR_aux prec k) choice x (magR_spec beta x Hx).1

/-- `Relative.relative_error_N_FLX_ex` on `ℝ`. -/
theorem relative_error_N_FLXR_ex (choice : ℤ → Bool) (x : ℝ) :
    ∃ eps, |eps| ≤ 1 / 2 * bpowR beta (-prec + 1) ∧
      roundR beta (FLX_exp prec) (ZnearestR choice) x = x * (1 + eps) :=
  relative_error_conversionR _ x _ (by have := bpowR_pos beta (-prec + 1); positivity)
    (fun _ => relative_error_N_FLXR beta prec choice x)
    (fun h => by rw [h, roundR_0])

end Fprop_relative_FLX

section Fprop_relative_FLT
variable (beta : radix) (emin prec : ℤ)

theorem relative_error_FLTR_aux (k : ℤ) (hk : emin + prec - 1 < k) :
    prec ≤ k - FLT_exp emin prec k := by
  unfold FLT_exp; omega

/-- `Relative.relative_error_FLT` on `ℝ`. -/
theorem relative_error_FLTR (rnd : ℝ → ℤ) [Valid_rndR rnd] (x : ℝ)
    (Hx : bpowR beta (emin + prec - 1) ≤ |x|) :
    |roundR beta (FLT_exp emin prec) rnd x - x| < bpowR beta (-prec + 1) * |x| :=
  relative_errorR beta (FLT_exp emin prec) (emin + prec - 1) prec
    (relative_error_FLTR_aux emin prec) rnd x Hx

/-- `Relative.relative_error_N_FLT` on `ℝ`. -/
theorem relative_error_N_FLTR (choice : ℤ → Bool) (x : ℝ)
    (Hx : bpowR beta (emin + prec - 1) ≤ |x|) :
    |roundR beta (FLT_exp emin prec) (ZnearestR choice) x - x| ≤
      1 / 2 * bpowR beta (-prec + 1) * |x| :=
  relative_error_NR beta (FLT_exp emin prec) (emin + prec - 1) prec
    (relative_error_FLTR_aux emin prec) choice x Hx

end Fprop_relative_FLT

end

end Flocq
end CC
