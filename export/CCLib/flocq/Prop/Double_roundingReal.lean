/-
  Port of the real-number statements of Flocq's `Prop/Double_rounding.v`
  (Flocq 4, as shipped with CompCert), over Mathlib's `ℝ`.

  Copyright (C) 2014-2018 Sylvie Boldo, Guillaume Melquiond, Pierre Roux
  (Flocq, LGPL-3.0+).

  The rational port (`Double_rounding*.lean`) states the square-root theorems
  with the relation `is_round_sqrt` instead of `round (sqrt x)`.  Here they get
  Rocq's statements, with `Real.sqrt` and the real rounding `roundR`:
  * `round_round_eqR` is Rocq's `round_round_eq` on `ℝ`;
    `round_round_eqR_cast` relates it to the rational `round_round_eq`;
  * `round_round_sqrtR` (Rocq's `round_round_sqrt`) and its FLX, FLT and FTZ
    instances;
  * `round_round_sqrt_radix_ge_4R` (Rocq's `round_round_sqrt_radix_ge_4`) and
    its FLX, FLT and FTZ instances;
  * for completeness, the real forms of `round_round_plus`,
    `round_round_minus`, `round_round_mult` and `round_round_div` (their
    arguments are format numbers, hence rational, so they follow from the
    rational theorems by `round_round_eqR_cast`).

  As in the rest of the port, the arguments `x`, `y` (float values) are
  rational; the rounded quantity (`Real.sqrt x`) is an arbitrary real.
-/
import CCLib.flocq.Prop.Double_roundingSqrt
import CCLib.flocq.IEEE754.BinarySingleNaNSqrtReal

namespace CC
namespace Flocq

noncomputable section

section Double_round_real

variable (beta : radix)

/-- Rocq's `round_round_eq` on `ℝ`: rounding to nearest in `fexp2`, then in
`fexp1`, is rounding to nearest in `fexp1`. -/
def round_round_eqR (fexp1 fexp2 : ℤ → ℤ) (choice1 choice2 : ℤ → Bool) (x : ℝ) : Prop :=
  roundR beta fexp1 (ZnearestR choice1) (roundR beta fexp2 (ZnearestR choice2) x) =
    roundR beta fexp1 (ZnearestR choice1) x

/-- On rationals, `round_round_eqR` is the rational `round_round_eq`. -/
theorem round_round_eqR_cast (fexp1 fexp2 : ℤ → ℤ) (choice1 choice2 : ℤ → Bool) (q : ℚ) :
    round_round_eqR beta fexp1 fexp2 choice1 choice2 q ↔
      round_round_eq beta fexp1 fexp2 choice1 choice2 q := by
  unfold round_round_eqR round_round_eq
  rw [← round_cast beta fexp2 (Rnd_ext_Znearest choice2),
    ← round_cast beta fexp1 (Rnd_ext_Znearest choice1),
    ← round_cast beta fexp1 (Rnd_ext_Znearest choice1)]
  exact Rat.cast_inj

/-- From the `is_round_sqrt` form of a double-rounding theorem to Rocq's form
`round_round_eq … (sqrt x)`. -/
theorem round_round_eqR_sqrt_of_is_round_sqrt (fexp1 fexp2 : ℤ → ℤ) [Valid_exp fexp1]
    [Valid_exp fexp2] (choice1 choice2 : ℤ → Bool) (x : ℚ)
    (H : ∀ r1 r2 : ℚ, is_round_sqrt beta fexp1 (Znearest choice1) x r1 →
      is_round_sqrt beta fexp2 (Znearest choice2) x r2 →
      round beta fexp1 (Znearest choice1) r2 = r1) :
    round_round_eqR beta fexp1 fexp2 choice1 choice2 (Real.sqrt x) := by
  obtain ⟨r1, hr1, H1⟩ := is_round_sqrt_roundR beta fexp1 (Rnd_ext_Znearest choice1) x
  obtain ⟨r2, hr2, H2⟩ := is_round_sqrt_roundR beta fexp2 (Rnd_ext_Znearest choice2) x
  unfold round_round_eqR
  rw [← hr2, ← hr1, ← round_cast beta fexp1 (Rnd_ext_Znearest choice1), H r1 r2 H1 H2]

/-! ### Square root (Rocq's sections `Double_round_sqrt*`) -/

/-- Rocq's `round_round_sqrt`. -/
theorem round_round_sqrtR (fexp1 fexp2 : ℤ → ℤ) [Valid_exp fexp1] [Valid_exp fexp2]
    (choice1 choice2 : ℤ → Bool) (Hexp : round_round_sqrt_hyp fexp1 fexp2)
    (x : ℚ) (Fx : generic_format beta fexp1 x) :
    round_round_eqR beta fexp1 fexp2 choice1 choice2 (Real.sqrt x) :=
  round_round_eqR_sqrt_of_is_round_sqrt beta fexp1 fexp2 choice1 choice2 x
    (round_round_sqrt beta fexp1 fexp2 choice1 choice2 Hexp x Fx)

/-- Rocq's `round_round_sqrt_FLX`. -/
theorem round_round_sqrtR_FLX (prec prec' : ℤ) [Prec_gt_0 prec] [Prec_gt_0 prec']
    (choice1 choice2 : ℤ → Bool) (Hprec : 2 * prec + 2 ≤ prec')
    (x : ℚ) (Fx : FLX_format beta prec x) :
    round_round_eqR beta (FLX_exp prec) (FLX_exp prec') choice1 choice2 (Real.sqrt x) :=
  round_round_eqR_sqrt_of_is_round_sqrt beta _ _ choice1 choice2 x
    (round_round_sqrt_FLX beta prec prec' choice1 choice2 Hprec x Fx)

/-- Rocq's `round_round_sqrt_FLT`. -/
theorem round_round_sqrtR_FLT (emin prec emin' prec' : ℤ) [Prec_gt_0 prec] [Prec_gt_0 prec']
    (choice1 choice2 : ℤ → Bool) (Hemin : emin ≤ 0)
    (Heminprec : emin' ≤ emin - prec - 2 ∨ 2 * emin' ≤ emin - 4 * prec - 2)
    (Hprec : 2 * prec + 2 ≤ prec') (x : ℚ) (Fx : FLT_format beta emin prec x) :
    round_round_eqR beta (FLT_exp emin prec) (FLT_exp emin' prec') choice1 choice2
      (Real.sqrt x) :=
  round_round_eqR_sqrt_of_is_round_sqrt beta _ _ choice1 choice2 x
    (round_round_sqrt_FLT beta emin prec emin' prec' choice1 choice2 Hemin Heminprec Hprec x Fx)

/-- Rocq's `round_round_sqrt_FTZ` (its unused hypothesis `4 ≤ beta` is
dropped). -/
theorem round_round_sqrtR_FTZ (emin prec emin' prec' : ℤ) [Prec_gt_0 prec] [Prec_gt_0 prec']
    (choice1 choice2 : ℤ → Bool)
    (Hemin : 2 * (emin' + prec') ≤ emin + prec ∧ emin + prec ≤ 1)
    (Hprec : 2 * prec + 2 ≤ prec') (x : ℚ) (Fx : FTZ_format beta emin prec x) :
    round_round_eqR beta (FTZ_exp emin prec) (FTZ_exp emin' prec') choice1 choice2
      (Real.sqrt x) :=
  round_round_eqR_sqrt_of_is_round_sqrt beta _ _ choice1 choice2 x
    (round_round_sqrt beta _ _ choice1 choice2
      (FTZ_round_round_sqrt_hyp emin prec emin' prec' Hemin Hprec) x
      (generic_format_FTZ beta emin prec x Fx))

/-- Rocq's `round_round_sqrt_radix_ge_4`. -/
theorem round_round_sqrt_radix_ge_4R (Hbeta : 4 ≤ beta.radix_val)
    (fexp1 fexp2 : ℤ → ℤ) [Valid_exp fexp1] [Valid_exp fexp2]
    (choice1 choice2 : ℤ → Bool) (Hexp : round_round_sqrt_radix_ge_4_hyp fexp1 fexp2)
    (x : ℚ) (Fx : generic_format beta fexp1 x) :
    round_round_eqR beta fexp1 fexp2 choice1 choice2 (Real.sqrt x) :=
  round_round_eqR_sqrt_of_is_round_sqrt beta fexp1 fexp2 choice1 choice2 x
    (round_round_sqrt_radix_ge_4 beta Hbeta fexp1 fexp2 choice1 choice2 Hexp x Fx)

/-- Rocq's `round_round_sqrt_radix_ge_4_FLX`. -/
theorem round_round_sqrt_radix_ge_4R_FLX (prec prec' : ℤ) [Prec_gt_0 prec] [Prec_gt_0 prec']
    (Hbeta : 4 ≤ beta.radix_val) (choice1 choice2 : ℤ → Bool) (Hprec : 2 * prec + 1 ≤ prec')
    (x : ℚ) (Fx : FLX_format beta prec x) :
    round_round_eqR beta (FLX_exp prec) (FLX_exp prec') choice1 choice2 (Real.sqrt x) :=
  round_round_eqR_sqrt_of_is_round_sqrt beta _ _ choice1 choice2 x
    (round_round_sqrt_radix_ge_4_FLX beta prec prec' Hbeta choice1 choice2 Hprec x Fx)

/-- Rocq's `round_round_sqrt_radix_ge_4_FLT`. -/
theorem round_round_sqrt_radix_ge_4R_FLT (emin prec emin' prec' : ℤ) [Prec_gt_0 prec]
    [Prec_gt_0 prec'] (Hbeta : 4 ≤ beta.radix_val) (choice1 choice2 : ℤ → Bool)
    (Hemin : emin ≤ 0)
    (Heminprec : emin' ≤ emin - prec - 1 ∨ 2 * emin' ≤ emin - 4 * prec)
    (Hprec : 2 * prec + 1 ≤ prec') (x : ℚ) (Fx : FLT_format beta emin prec x) :
    round_round_eqR beta (FLT_exp emin prec) (FLT_exp emin' prec') choice1 choice2
      (Real.sqrt x) :=
  round_round_eqR_sqrt_of_is_round_sqrt beta _ _ choice1 choice2 x
    (round_round_sqrt_radix_ge_4_FLT beta emin prec emin' prec' Hbeta choice1 choice2 Hemin
      Heminprec Hprec x Fx)

/-- Rocq's `round_round_sqrt_radix_ge_4_FTZ`. -/
theorem round_round_sqrt_radix_ge_4R_FTZ (emin prec emin' prec' : ℤ) [Prec_gt_0 prec]
    [Prec_gt_0 prec'] (Hbeta : 4 ≤ beta.radix_val) (choice1 choice2 : ℤ → Bool)
    (Hemin : 2 * (emin' + prec') ≤ emin + prec ∧ emin + prec ≤ 1)
    (Hprec : 2 * prec + 1 ≤ prec') (x : ℚ) (Fx : FTZ_format beta emin prec x) :
    round_round_eqR beta (FTZ_exp emin prec) (FTZ_exp emin' prec') choice1 choice2
      (Real.sqrt x) :=
  round_round_eqR_sqrt_of_is_round_sqrt beta _ _ choice1 choice2 x
    (round_round_sqrt_radix_ge_4_FTZ beta emin prec emin' prec' Hbeta choice1 choice2 Hemin
      Hprec x Fx)

/-! ### Sum, difference, product and quotient of format numbers -/

/-- Rocq's `round_round_plus` on `ℝ`. -/
theorem round_round_plusR (fexp1 fexp2 : ℤ → ℤ) [Valid_exp fexp1] [Valid_exp fexp2]
    (choice1 choice2 : ℤ → Bool) (Hexp : round_round_plus_hyp fexp1 fexp2) (x y : ℚ)
    (Fx : generic_format beta fexp1 x) (Fy : generic_format beta fexp1 y) :
    round_round_eqR beta fexp1 fexp2 choice1 choice2 ((x : ℝ) + y) := by
  rw [← Rat.cast_add, round_round_eqR_cast]
  exact round_round_plus beta fexp1 fexp2 choice1 choice2 Hexp x y Fx Fy

/-- Rocq's `round_round_minus` on `ℝ`. -/
theorem round_round_minusR (fexp1 fexp2 : ℤ → ℤ) [Valid_exp fexp1] [Valid_exp fexp2]
    (choice1 choice2 : ℤ → Bool) (Hexp : round_round_plus_hyp fexp1 fexp2) (x y : ℚ)
    (Fx : generic_format beta fexp1 x) (Fy : generic_format beta fexp1 y) :
    round_round_eqR beta fexp1 fexp2 choice1 choice2 ((x : ℝ) - y) := by
  rw [← Rat.cast_sub, round_round_eqR_cast]
  exact round_round_minus beta fexp1 fexp2 choice1 choice2 Hexp x y Fx Fy

/-- Rocq's `round_round_mult` on `ℝ`, for rounding to nearest. -/
theorem round_round_multR (fexp1 fexp2 : ℤ → ℤ) [Valid_exp fexp2]
    (choice1 choice2 : ℤ → Bool) (Hfexp : round_round_mult_hyp fexp1 fexp2) (x y : ℚ)
    (Fx : generic_format beta fexp1 x) (Fy : generic_format beta fexp1 y) :
    round_round_eqR beta fexp1 fexp2 choice1 choice2 ((x : ℝ) * y) := by
  rw [← Rat.cast_mul, round_round_eqR_cast]
  unfold round_round_eq
  rw [round_generic beta fexp2 (Znearest choice2) _
    (round_round_mult_aux beta fexp1 fexp2 Hfexp x y Fx Fy)]

/-- Rocq's `round_round_div` on `ℝ`. -/
theorem round_round_divR (fexp1 fexp2 : ℤ → ℤ) [Valid_exp fexp1] [Valid_exp fexp2]
    (choice1 choice2 : ℤ → Bool) (Ebeta : ∃ n : ℤ, beta.radix_val = 2 * n)
    (Hexp : round_round_div_hyp fexp1 fexp2) (x y : ℚ) (Nzy : y ≠ 0)
    (Fx : generic_format beta fexp1 x) (Fy : generic_format beta fexp1 y) :
    round_round_eqR beta fexp1 fexp2 choice1 choice2 ((x : ℝ) / y) := by
  rw [← Rat.cast_div, round_round_eqR_cast]
  exact round_round_div beta fexp1 fexp2 choice1 choice2 Ebeta Hexp x y Nzy Fx Fy

end Double_round_real

end

end Flocq
end CC
