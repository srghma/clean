/-
  Port of Flocq's `Prop/Div_sqrt_error.v` (Flocq 4, as shipped with CompCert):
  the square-root error bounds with Rocq's statements over the real numbers.

  Copyright (C) 2010-2018 Sylvie Boldo, Guillaume Melquiond (Flocq, LGPL-3.0+).

  `Div_sqrt_errorReal.lean` proves `sqrt_error_N_FLX`, `sqrt_error_N_FLX_ex`,
  `sqrt_error_N_FLX_round_ex`, `sqrt_error_N_FLT_ex` and
  `sqrt_error_N_FLT_round_ex` over any `RatSqrtField`, for a rational `r` with
  `is_round_sqrt … x r`.  Here they are restated over Mathlib's `ℝ` with Rocq's
  `round beta fexp (Znearest choice) (sqrt x)` (`roundR`,
  `Core/Generic_fmtReal.lean`), `Real.sqrt` and `|·|`.  As everywhere in the
  port, the input `x` (a floating-point number) is rational.
-/
import CCLib.flocq.IEEE754.BinarySingleNaNSqrtReal
import CCLib.flocq.Prop.Div_sqrt_errorReal

namespace CC
namespace Flocq

noncomputable section

section Fprop_divsqrt_error_real
variable (beta : radix) (prec : Int) [Prec_gt_0 prec] (choice : Int → Bool)

/-- Rocq's `sqrt_error_N_FLX` over `ℝ`. -/
theorem sqrt_error_N_FLX_real (x : ℚ) (Fx : generic_format beta (FLX_exp prec) x) :
    |roundR beta (FLX_exp prec) (ZnearestR choice) (Real.sqrt x) - Real.sqrt x| ≤
      (1 - 1 / Real.sqrt (1 + 2 * (u_ro beta prec : ℝ))) * |Real.sqrt x| := by
  obtain ⟨r, hr, H⟩ := is_round_sqrt_roundR beta (FLX_exp prec) (Rnd_ext_Znearest choice) x
  rw [← hr]
  have := sqrt_error_N_FLX beta prec choice (R := ℝ) x r Fx H
  simpa using this

/-- Rocq's `sqrt_error_N_FLX_ex` over `ℝ`. -/
theorem sqrt_error_N_FLX_ex_real (x : ℚ) (Fx : generic_format beta (FLX_exp prec) x) :
    ∃ eps : ℝ, |eps| ≤ 1 - 1 / Real.sqrt (1 + 2 * (u_ro beta prec : ℝ)) ∧
      roundR beta (FLX_exp prec) (ZnearestR choice) (Real.sqrt x) = Real.sqrt x * (1 + eps) := by
  obtain ⟨r, hr, H⟩ := is_round_sqrt_roundR beta (FLX_exp prec) (Rnd_ext_Znearest choice) x
  rw [← hr]
  have := sqrt_error_N_FLX_ex beta prec choice (R := ℝ) x r Fx H
  simpa using this

/-- Rocq's `sqrt_error_N_FLX_round_ex` over `ℝ`. -/
theorem sqrt_error_N_FLX_round_ex_real (x : ℚ) (Fx : generic_format beta (FLX_exp prec) x) :
    ∃ eps : ℝ, |eps| ≤ Real.sqrt (1 + 2 * (u_ro beta prec : ℝ)) - 1 ∧
      Real.sqrt x = roundR beta (FLX_exp prec) (ZnearestR choice) (Real.sqrt x) * (1 + eps) := by
  obtain ⟨r, hr, H⟩ := is_round_sqrt_roundR beta (FLX_exp prec) (Rnd_ext_Znearest choice) x
  rw [← hr]
  have := sqrt_error_N_FLX_round_ex beta prec choice (R := ℝ) x r Fx H
  simpa using this

variable (emin : Int)

/-- Rocq's `sqrt_error_N_FLT_ex` over `ℝ`. -/
theorem sqrt_error_N_FLT_ex_real (Hemin : emin ≤ 2 * (1 - prec)) (x : ℚ)
    (Fx : generic_format beta (FLT_exp emin prec) x) :
    ∃ eps : ℝ, |eps| ≤ 1 - 1 / Real.sqrt (1 + 2 * (u_ro beta prec : ℝ)) ∧
      roundR beta (FLT_exp emin prec) (ZnearestR choice) (Real.sqrt x) =
        Real.sqrt x * (1 + eps) := by
  obtain ⟨r, hr, H⟩ :=
    is_round_sqrt_roundR beta (FLT_exp emin prec) (Rnd_ext_Znearest choice) x
  rw [← hr]
  have := sqrt_error_N_FLT_ex beta prec choice (R := ℝ) emin Hemin x r Fx H
  simpa using this

/-- Rocq's `sqrt_error_N_FLT_round_ex` over `ℝ`. -/
theorem sqrt_error_N_FLT_round_ex_real (Hemin : emin ≤ 2 * (1 - prec)) (x : ℚ)
    (Fx : generic_format beta (FLT_exp emin prec) x) :
    ∃ eps : ℝ, |eps| ≤ Real.sqrt (1 + 2 * (u_ro beta prec : ℝ)) - 1 ∧
      Real.sqrt x =
        roundR beta (FLT_exp emin prec) (ZnearestR choice) (Real.sqrt x) * (1 + eps) := by
  obtain ⟨r, hr, H⟩ :=
    is_round_sqrt_roundR beta (FLT_exp emin prec) (Rnd_ext_Znearest choice) x
  rw [← hr]
  have := sqrt_error_N_FLT_round_ex beta prec choice (R := ℝ) emin Hemin x r Fx H
  simpa using this

end Fprop_divsqrt_error_real

end

end Flocq
end CC
