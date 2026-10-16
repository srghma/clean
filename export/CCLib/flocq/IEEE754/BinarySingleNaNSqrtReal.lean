/-
  Port of Flocq's `IEEE754/BinarySingleNaN.v` (Flocq 4, as shipped with
  CompCert): `Bsqrt_correct` with Rocq's statement over the real numbers.

  Copyright (C) 2010-2018 Sylvie Boldo, Guillaume Melquiond (Flocq, LGPL-3.0+).

  `BinarySingleNaNSqrt.lean` states `Bsqrt_correct` over `Rat` with the
  relation `is_round_sqrt` (a rational characterization of `round (sqrt x)`).
  With Mathlib's real numbers, Rocq's statement
  `B2R (Bsqrt m x) = round radix2 fexp (round_mode m) (sqrt (B2R x))` can be
  written directly:
  * `is_round_sqrt_real`: any `r` with `is_round_sqrt beta fexp rnd x r` is the
    real rounding (`roundR`, `Core/Generic_fmtReal.lean`) of the real square
    root `Real.sqrt x`, for every rounding function with a real version
    (`Rnd_ext`);
  * `round_modeR` is `round_mode` on `ℝ`;
  * `BSN.Bsqrt_correct_real` is Rocq's `Bsqrt_correct`.
-/
import CCLib.flocq.Core.Generic_fmtReal
import CCLib.flocq.IEEE754.BinarySingleNaNSqrt

namespace CC
namespace Flocq

noncomputable section

section RoundSqrtReal
variable (beta : radix) (fexp : ℤ → ℤ)

/-- `is_round_sqrt beta fexp rnd x r` determines `r`: it is Rocq's
`round beta fexp rnd (sqrt x)`, computed on `ℝ`. -/
theorem is_round_sqrt_real {rnd : ℚ → ℤ} {rndR : ℝ → ℤ} [Valid_rnd rnd] (h : Rnd_ext rnd rndR)
    (x r : ℚ) (H : is_round_sqrt beta fexp rnd x r) :
    (r : ℝ) = roundR beta fexp rndR (Real.sqrt x) := by
  rcases le_or_gt x 0 with hx | hx
  · rw [H.nonpos hx, Real.sqrt_eq_zero'.mpr (by exact_mod_cast hx), roundR_zero beta fexp h,
      Rat.cast_zero]
  · have hxR : (0 : ℝ) < x := by exact_mod_cast hx
    have hsq : Real.sqrt (x : ℝ) * Real.sqrt x = x := Real.mul_self_sqrt hxR.le
    by_cases hirr : Irrational (Real.sqrt x)
    · obtain ⟨L, U, hL, hLy, hyU, hq⟩ :=
        roundR_near_irrational beta fexp h _ (Real.sqrt_pos.mpr hxR) hirr
      obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn hLy
      obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn hyU
      have ha0R : (0 : ℝ) ≤ a := (hL.trans ha1).le
      have hb0R : (0 : ℝ) ≤ b := (Real.sqrt_nonneg _).trans hb1.le
      have ha0 : (0 : ℚ) ≤ a := by exact_mod_cast ha0R
      have hb0 : (0 : ℚ) ≤ b := by exact_mod_cast hb0R
      have haa : a * a ≤ x := by
        have : (a : ℝ) * a ≤ x := hsq ▸ mul_self_le_mul_self ha0R ha2.le
        exact_mod_cast this
      have hbb : x ≤ b * b := by
        have : (x : ℝ) ≤ b * b := hsq ▸ mul_self_le_mul_self (Real.sqrt_nonneg _) hb1.le
        exact_mod_cast this
      have l : ((round beta fexp rnd a : ℚ) : ℝ) ≤ r := by exact_mod_cast H.lower a ha0 haa
      have u : (r : ℝ) ≤ ((round beta fexp rnd b : ℚ) : ℝ) := by exact_mod_cast H.upper b hb0 hbb
      rw [hq a ha1 (ha2.trans hyU)] at l
      rw [hq b (hLy.trans hb1) hb2] at u
      exact le_antisymm u l
    · simp only [Irrational, not_not, Set.mem_range] at hirr
      obtain ⟨y, hy⟩ := hirr
      have hy0 : (0 : ℚ) ≤ y := by
        have := Real.sqrt_nonneg (x : ℝ); rw [← hy] at this; exact_mod_cast this
      have hyy : y * y = x := by
        rw [← hy] at hsq; exact_mod_cast hsq
      rw [H.exact y hy0 hyy, round_cast beta fexp h, hy]

/-- Conversely, the real rounding of `Real.sqrt x` is a rational `r` with
`is_round_sqrt beta fexp rnd x r`. -/
theorem is_round_sqrt_roundR {rnd : ℚ → ℤ} {rndR : ℝ → ℤ} [Valid_exp fexp] [Valid_rnd rnd]
    (h : Rnd_ext rnd rndR) (x : ℚ) :
    ∃ r : ℚ, (r : ℝ) = roundR beta fexp rndR (Real.sqrt x) ∧ is_round_sqrt beta fexp rnd x r := by
  rcases le_or_gt x 0 with hx | hx
  · refine ⟨0, ?_, is_round_sqrt_nonpos beta fexp rnd x hx⟩
    rw [Real.sqrt_eq_zero'.mpr (by exact_mod_cast hx), roundR_zero beta fexp h, Rat.cast_zero]
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hsq : Real.sqrt (x : ℝ) * Real.sqrt x = x := Real.mul_self_sqrt hxR.le
  have nonpos : ∀ r : ℚ, x ≤ 0 → r = 0 := fun _ h' => absurd h' (not_le.mpr hx)
  -- `a ≥ 0` with `a * a ≤ x` is at most `√x`, and `b ≥ 0` with `x ≤ b * b` at least `√x`.
  have le_sqrt : ∀ a : ℚ, 0 ≤ a → a * a ≤ x → (a : ℝ) ≤ Real.sqrt x := fun a ha hax => by
    have : ((a * a : ℚ) : ℝ) ≤ x := by exact_mod_cast hax
    rw [Rat.cast_mul] at this
    exact Real.le_sqrt_of_sq_le (by rw [sq]; exact this)
  have sqrt_le : ∀ b : ℚ, 0 ≤ b → x ≤ b * b → Real.sqrt x ≤ (b : ℝ) := fun b hb hxb => by
    have : (x : ℝ) ≤ ((b * b : ℚ) : ℝ) := by exact_mod_cast hxb
    rw [Rat.cast_mul] at this
    exact (Real.sqrt_le_left (by exact_mod_cast hb)).2 (by rw [sq]; exact this)
  by_cases hirr : Irrational (Real.sqrt x)
  · obtain ⟨L, U, hL, hLy, hyU, hq⟩ :=
      roundR_near_irrational beta fexp h _ (Real.sqrt_pos.mpr hxR) hirr
    obtain ⟨q0, hq01, hq02⟩ := exists_rat_btwn hLy
    have hr := hq q0 hq01 (hq02.trans hyU)
    refine ⟨round beta fexp rnd q0, hr, nonpos _, fun y hy hyx => ?_, fun a ha hax => ?_,
      fun b hb hxb => ?_⟩
    · exfalso; apply hirr.ne_rat y
      have := le_antisymm (le_sqrt y hy hyx.le) (sqrt_le y hy hyx.ge)
      exact this.symm
    · have hlt : (a : ℝ) < Real.sqrt x :=
        lt_of_le_of_ne (le_sqrt a ha hax) (fun e => hirr.ne_rat a e.symm)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt hLy hlt)
      have e : round beta fexp rnd q = round beta fexp rnd q0 := by
        have := (hq q (lt_of_le_of_lt (le_max_left _ _) hq1) (hq2.trans hyU)).trans hr.symm
        exact_mod_cast this
      rw [← e]
      exact round_le beta fexp rnd a q (by exact_mod_cast (le_max_right _ _).trans hq1.le)
    · have hlt : Real.sqrt x < (b : ℝ) :=
        lt_of_le_of_ne (sqrt_le b hb hxb) (fun e => hirr.ne_rat b e)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min hyU hlt)
      have e : round beta fexp rnd q = round beta fexp rnd q0 := by
        have := (hq q (hLy.trans hq1) (lt_of_lt_of_le hq2 (min_le_left _ _))).trans hr.symm
        exact_mod_cast this
      rw [← e]
      exact round_le beta fexp rnd q b (by exact_mod_cast hq2.le.trans (min_le_right _ _))
  · simp only [Irrational, not_not, Set.mem_range] at hirr
    obtain ⟨y, hy⟩ := hirr
    have hy0R : (0 : ℝ) ≤ y := hy ▸ Real.sqrt_nonneg _
    refine ⟨round beta fexp rnd y, by rw [round_cast beta fexp h, hy], nonpos _,
      fun y' hy' hyx => ?_, fun a ha hax => ?_, fun b hb hxb => ?_⟩
    · have : (y' : ℝ) = y := by
        rw [hy]; exact le_antisymm (le_sqrt y' hy' hyx.le) (sqrt_le y' hy' hyx.ge)
      rw [show y' = y by exact_mod_cast this]
    · exact round_le beta fexp rnd a y (by exact_mod_cast (hy ▸ le_sqrt a ha hax))
    · exact round_le beta fexp rnd y b (by exact_mod_cast (hy ▸ sqrt_le b hb hxb))

/-- `is_round_sqrt` is exactly Rocq's `r = round beta fexp rnd (sqrt x)`, for
every rounding function with a real version (in particular the five IEEE
rounding modes, `BSN.Rnd_ext_round_mode`). -/
theorem is_round_sqrt_iff_real {rnd : ℚ → ℤ} {rndR : ℝ → ℤ} [Valid_exp fexp] [Valid_rnd rnd]
    (h : Rnd_ext rnd rndR) (x r : ℚ) :
    is_round_sqrt beta fexp rnd x r ↔ (r : ℝ) = roundR beta fexp rndR (Real.sqrt x) := by
  refine ⟨is_round_sqrt_real beta fexp h x r, fun hr => ?_⟩
  obtain ⟨r', hr', H⟩ := is_round_sqrt_roundR beta fexp h x
  rwa [show r = r' by exact_mod_cast hr.trans hr'.symm]

end RoundSqrtReal

namespace BSN

open binary_float mode

/-- `round_mode` on `ℝ`: the real rounding function of each IEEE mode. -/
def round_modeR : mode → ℝ → ℤ
  | mode_NE => ZnearestR (fun x => !(Zeven x))
  | mode_ZR => ZtruncR
  | mode_DN => ZfloorR
  | mode_UP => ZceilR
  | mode_NA => ZnearestR (Zle_bool 0)

/-- `round_modeR m` is the real version of `round_mode m`. -/
theorem Rnd_ext_round_mode (m : mode) : Rnd_ext (round_mode m) (round_modeR m) := by
  cases m
  · exact Rnd_ext_Znearest (fun x => !(Zeven x))
  · exact Rnd_ext_Ztrunc
  · exact Rnd_ext_Zfloor
  · exact Rnd_ext_Zceil
  · exact Rnd_ext_Znearest (Zle_bool 0)

section SqrtReal
variable {prec emax : Int} [Prec_gt_0 prec] [Prec_lt_emax prec emax]

/-- `BinarySingleNaN.Bsqrt_correct`, with Rocq's statement: the square root is
the correctly rounded real square root; it is finite exactly for zeros and
positive finite inputs; and it has the sign of the input unless it is a NaN. -/
theorem Bsqrt_correct_real (md : mode) (x : binary_float prec emax) :
    ((B2R (Bsqrt md x) : ℚ) : ℝ) =
      roundR radix2 (fexp prec emax) (round_modeR md) (Real.sqrt (B2R x : ℚ)) ∧
    is_finite (Bsqrt md x) =
      (match x with
       | B754_zero _ => true
       | B754_finite false _ _ _ => true
       | _ => false) ∧
    (is_nan (Bsqrt md x) = false → Bsign (Bsqrt md x) = Bsign x) := by
  obtain ⟨H1, H2, H3⟩ := Bsqrt_correct md x
  exact ⟨is_round_sqrt_real radix2 _ (Rnd_ext_round_mode md) _ _ H1, H2, H3⟩

end SqrtReal

end BSN

end

end Flocq
end CC
