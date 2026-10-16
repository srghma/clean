/-
  Port of Flocq's `IEEE754/Binary.v` and `IEEE754/Bits.v` (Flocq 4, as shipped
  with CompCert): the correctness of the square root with Rocq's statement
  over the real numbers.

  Copyright (C) 2010-2018 Sylvie Boldo, Guillaume Melquiond (Flocq, LGPL-3.0+).

  `BinarySqrt.lean` states `Bsqrt_correct` with `is_round_sqrt`; here it is
  restated as `B2R (Bsqrt m x) = round radix2 fexp (round_mode m) (sqrt (B2R x))`
  over Mathlib's `ℝ` (see `BinarySingleNaNSqrtReal.lean`), and specialized to
  `b32_sqrt` and `b64_sqrt`.
-/
import CCLib.flocq.IEEE754.BinarySingleNaNSqrtReal
import CCLib.flocq.IEEE754.BinarySqrt
import CCLib.flocq.IEEE754.Bits

namespace CC
namespace Flocq

noncomputable section

open binary_float BSN.mode

section BinarySqrtReal
variable {prec emax : Int}

/-- `Binary.Bsqrt_correct`, with Rocq's statement over `ℝ`. -/
theorem Bsqrt_correct_real [Prec_gt_0 prec] [Prec_lt_emax prec emax]
    (sqrt_nan : binary_float prec emax → { x : binary_float prec emax // is_nan x = true })
    (m : BSN.mode) (x : binary_float prec emax) :
    ((B2R (Bsqrt sqrt_nan m x) : ℚ) : ℝ) =
      roundR radix2 (BSN.fexp prec emax) (BSN.round_modeR m) (Real.sqrt (B2R x : ℚ)) ∧
    is_finite (Bsqrt sqrt_nan m x) =
      (match x with
       | B754_zero _ => true
       | B754_finite false _ _ _ => true
       | _ => false) ∧
    (is_nan (Bsqrt sqrt_nan m x) = false → Bsign (Bsqrt sqrt_nan m x) = Bsign x) := by
  obtain ⟨H1, H2, H3⟩ := Bsqrt_correct sqrt_nan m x
  exact ⟨is_round_sqrt_real radix2 _ (BSN.Rnd_ext_round_mode m) _ _ H1, H2, H3⟩

end BinarySqrtReal

/-- The value of `b32_sqrt m x` is the binary32 rounding of the real square root
of the value of `x`. -/
theorem b32_sqrt_correct_real (m : BSN.mode) (x : binary32) :
    ((B2R (b32_sqrt m x) : ℚ) : ℝ) =
      roundR radix2 (BSN.fexp 24 128) (BSN.round_modeR m) (Real.sqrt (B2R x : ℚ)) :=
  (Bsqrt_correct_real unop_nan_pl32 m x).1

/-- The value of `b64_sqrt m x` is the binary64 rounding of the real square root
of the value of `x`. -/
theorem b64_sqrt_correct_real (m : BSN.mode) (x : binary64) :
    ((B2R (b64_sqrt m x) : ℚ) : ℝ) =
      roundR radix2 (BSN.fexp 53 1024) (BSN.round_modeR m) (Real.sqrt (B2R x : ℚ)) :=
  (Bsqrt_correct_real unop_nan_pl64 m x).1

end

end Flocq
end CC
