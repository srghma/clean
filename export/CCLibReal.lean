/-
  `CCLibReal` — the parts of the port that use Mathlib's real numbers `ℝ`.

  They are kept out of the `CCLib` root (which depends on Lean core only), so
  that importing `CCLib` does not load Mathlib.

  * `CCLib.flocq.Core.RauxReal` — `bpow`, `mag`, `exp`/`ln` lemmas of Flocq's
    `Core/Raux.v` on `ℝ`; `ℝ` as a `RatSqrtField` and a `RatExpField`.
  * `CCLib.flocq.Core.Generic_fmtReal` — `cexp`, `scaled_mantissa`,
    `generic_format`, `round` and the rounding functions of
    `Core/Generic_fmt.v` on `ℝ`, and their agreement with the rational ones.
  * `CCLib.flocq.IEEE754.BinarySingleNaNSqrtReal`,
    `CCLib.flocq.IEEE754.BinarySqrtReal` — `Bsqrt_correct` (and `b32_sqrt`,
    `b64_sqrt`) with Rocq's statement `B2R (Bsqrt m x) = round … (sqrt (B2R x))`.
  * `CCLib.flocq.Prop.Div_sqrt_errorR` — the square-root error bounds of
    `Prop/Div_sqrt_error.v` with Rocq's statements over `ℝ`.
  * `CCLib.flocq.Core.Generic_fmtRealRound` — the rounding theory of
    `Core/Generic_fmt.v` for arbitrary real arguments (`Valid_rndR`,
    `roundR_generic`, `roundR_le`, `generic_formatR_round`, `roundR_DN_pt`,
    `roundR_UP_pt`, `roundR_N_pt`).
  * `CCLib.flocq.Core.UlpReal` — `ulp` on `ℝ` and the error bounds of
    `Core/Ulp.v` (`error_lt_ulpR`, `error_le_half_ulpR`).
  * `CCLib.flocq.Prop.RelativeReal` — the relative-error bounds of
    `Prop/Relative.v` (generic, FLX, FLT) for arbitrary real arguments.
  * `CCLib.flocq.Core.Generic_fmtRealTransfer` — transfer of rational
    double-rounding identities to every real argument (`roundR_roundR_of_rat`).
  * `CCLib.flocq.Prop.Round_oddReal` — rounding to odd on `ℝ` (`Zrnd_oddR`)
    and `round_N_odd` of `Prop/Round_odd.v` for every real argument.
  * `CCLib.flocq.Prop.Double_roundingReal` — the double-rounding theorems of
    `Prop/Double_rounding.v` with Rocq's statements over `ℝ`, in particular
    `round_round_sqrt` with `Real.sqrt`.
  * `CCLib.lib.MathlibEquiv`, `CCLib.flocq.Core.MathlibEquiv` — definitions of
    the port that duplicate Mathlib / Batteries / core ones, with the proofs
    that they agree (see `MATHLIB_DUPLICATION.md`).
-/
import CCLib.flocq.Core.RauxReal
import CCLib.flocq.Core.Generic_fmtReal
import CCLib.flocq.IEEE754.BinarySingleNaNSqrtReal
import CCLib.flocq.IEEE754.BinarySqrtReal
import CCLib.flocq.Prop.Div_sqrt_errorR
import CCLib.flocq.Core.Generic_fmtRealRound
import CCLib.flocq.Core.UlpReal
import CCLib.flocq.Prop.RelativeReal
import CCLib.lib.MathlibEquiv
import CCLib.flocq.Core.MathlibEquiv
import CCLib.flocq.Core.Generic_fmtRealTransfer
import CCLib.flocq.Prop.Round_oddReal
import CCLib.flocq.Prop.Double_roundingReal
