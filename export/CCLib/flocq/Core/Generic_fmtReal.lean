/-
  Port of the real-number side of Flocq's `Core/Generic_fmt.v` (Flocq 4, as
  shipped with CompCert), over Mathlib's real numbers `ℝ`.

  Copyright (C) 2009-2018 Sylvie Boldo, Guillaume Melquiond (Flocq, LGPL-3.0+).

  The Flocq port states the rounding theory over `Rat` (`Generic_fmt.lean`).
  This file defines Rocq's `cexp`, `scaled_mantissa`, `generic_format` and
  `round` on `R` (here `ℝ`), the rounding functions `Zfloor`, `Zceil`,
  `Ztrunc`, `Zaway` and `Znearest` on `ℝ`, and relates them to the rational
  versions:
  * on rationals the real definitions agree with the rational ones
    (`cexpR_cast`, `scaled_mantissaR_cast`, `generic_formatR_cast`,
    `round_cast`);
  * at an irrational point `y > 0`, the real rounding of `y` is the rounding
    of every rational close enough to `y` (`roundR_near_irrational`).
  The second fact is what turns the rational characterization of a rounded
  square root (`is_round_sqrt`, `IEEE754/BinarySingleNaNSqrt.lean`) into
  Rocq's `round (sqrt x)` (`IEEE754/BinarySingleNaNSqrtReal.lean`).

  The link between a rounding function `rnd : ℚ → ℤ` and its real version
  `rndR : ℝ → ℤ` is the predicate `Rnd_ext rnd rndR`: `rndR` extends `rnd`, and
  `rndR` is constant near every irrational point.  It holds for the five
  rounding functions above (`Rnd_ext_Zfloor`, …, `Rnd_ext_Znearest`).
-/
import CCLib.flocq.Core.RauxReal
import CCLib.flocq.Core.Round_NE

namespace CC
namespace Flocq

noncomputable section

/-! ### `F2R` with values in `ℝ` -/

/-- Rocq's `F2R` with values in `R`. -/
def F2RR {beta : radix} (f : float beta) : ℝ := (f.Fnum : ℝ) * bpowR beta f.Fexp

theorem F2R_cast {beta : radix} (f : float beta) : ((F2R f : ℚ) : ℝ) = F2RR f := by
  unfold F2R F2RR; push_cast; rw [bpow_cast]

/-! ### Rounding functions on `ℝ` -/

/-- `Raux.Zfloor` on `R`. -/
def ZfloorR (x : ℝ) : ℤ := ⌊x⌋

/-- `Raux.Zceil` on `R`. -/
def ZceilR (x : ℝ) : ℤ := ⌈x⌉

/-- `Raux.Ztrunc` on `R`. -/
def ZtruncR (x : ℝ) : ℤ := if x < 0 then ⌈x⌉ else ⌊x⌋

/-- `Raux.Zaway` on `R`. -/
def ZawayR (x : ℝ) : ℤ := if x < 0 then ⌊x⌋ else ⌈x⌉

/-- `Generic_fmt.Znearest` on `R`. -/
def ZnearestR (choice : ℤ → Bool) (x : ℝ) : ℤ :=
  if x - ⌊x⌋ < 1 / 2 then ⌊x⌋
  else if x - ⌊x⌋ = 1 / 2 then (if choice ⌊x⌋ then ⌈x⌉ else ⌊x⌋)
  else ⌈x⌉

theorem Zfloor_eq_floor (q : ℚ) : Zfloor q = ⌊q⌋ := rfl

theorem Zceil_eq_ceil (q : ℚ) : Zceil q = ⌈q⌉ := by
  unfold Zceil; rw [Zfloor_eq_floor, Int.floor_neg, neg_neg]

/-- `rndR : ℝ → ℤ` is a real version of `rnd : ℚ → ℤ`: it agrees with `rnd`
on rationals, and it is constant on a neighbourhood of every irrational. -/
structure Rnd_ext (rnd : ℚ → ℤ) (rndR : ℝ → ℤ) : Prop where
  agree : ∀ q : ℚ, rndR q = rnd q
  stable : ∀ m : ℝ, Irrational m →
    ∃ lo hi : ℝ, lo < m ∧ m < hi ∧ ∀ y : ℝ, lo < y → y < hi → rndR y = rndR m

/-- An irrational lies strictly between two consecutive integers. -/
theorem floor_lt_of_irrational {m : ℝ} (hm : Irrational m) :
    (⌊m⌋ : ℝ) < m ∧ m < (⌊m⌋ : ℝ) + 1 :=
  ⟨lt_of_le_of_ne (Int.floor_le m) (fun h => hm.ne_int ⌊m⌋ h.symm), Int.lt_floor_add_one m⟩

theorem floor_eq_of_between {y : ℝ} {n : ℤ} (h1 : (n : ℝ) < y) (h2 : y < n + 1) : ⌊y⌋ = n :=
  Int.floor_eq_iff.mpr ⟨h1.le, h2⟩

theorem ceil_eq_of_between {y : ℝ} {n : ℤ} (h1 : (n : ℝ) < y) (h2 : y < n + 1) : ⌈y⌉ = n + 1 :=
  Int.ceil_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩

/-- The common shape of the stability proofs: a function determined by
`⌊y⌋`, `⌈y⌉` and the sign of `y` is constant on `(⌊m⌋, ⌊m⌋ + 1)`. -/
theorem stable_of_unit_interval (rndR : ℝ → ℤ)
    (H : ∀ (n : ℤ) (y z : ℝ), (n : ℝ) < y → y < n + 1 → (n : ℝ) < z → z < n + 1 → rndR y = rndR z)
    (m : ℝ) (hm : Irrational m) :
    ∃ lo hi : ℝ, lo < m ∧ m < hi ∧ ∀ y : ℝ, lo < y → y < hi → rndR y = rndR m := by
  obtain ⟨h1, h2⟩ := floor_lt_of_irrational hm
  exact ⟨⌊m⌋, ⌊m⌋ + 1, h1, h2, fun y hy1 hy2 => H _ y m hy1 hy2 h1 h2⟩

theorem Rnd_ext_Zfloor : Rnd_ext Zfloor ZfloorR where
  agree q := by unfold ZfloorR; rw [Rat.floor_cast]; rfl
  stable := stable_of_unit_interval _ fun n y z h1 h2 h3 h4 => by
    unfold ZfloorR; rw [floor_eq_of_between h1 h2, floor_eq_of_between h3 h4]

theorem Rnd_ext_Zceil : Rnd_ext Zceil ZceilR where
  agree q := by unfold ZceilR; rw [Rat.ceil_cast, Zceil_eq_ceil]
  stable := stable_of_unit_interval _ fun n y z h1 h2 h3 h4 => by
    unfold ZceilR; rw [ceil_eq_of_between h1 h2, ceil_eq_of_between h3 h4]

/-- On `(n, n + 1)`, `y < 0` does not depend on `y`. -/
theorem neg_iff_of_unit_interval {n : ℤ} {y z : ℝ} (h1 : (n : ℝ) < y) (h2 : y < n + 1)
    (h3 : (n : ℝ) < z) (h4 : z < n + 1) : (y < 0 ↔ z < 0) := by
  rcases lt_or_ge n 0 with hn | hn
  · have : (n : ℝ) + 1 ≤ 0 := by exact_mod_cast hn
    constructor <;> intro <;> linarith
  · have : (0 : ℝ) ≤ n := by exact_mod_cast hn
    constructor <;> intro <;> linarith

theorem Rnd_ext_Ztrunc : Rnd_ext Ztrunc ZtruncR where
  agree q := by
    unfold ZtruncR Ztrunc Rlt_bool
    by_cases h : q < 0
    · have h' : (q : ℝ) < 0 := by exact_mod_cast h
      rw [if_pos h', decide_eq_true h, if_pos rfl, Rat.ceil_cast, Zceil_eq_ceil]
    · have h' : ¬ (q : ℝ) < 0 := by exact_mod_cast h
      rw [if_neg h', decide_eq_false h, if_neg Bool.false_ne_true, Rat.floor_cast]; rfl
  stable := stable_of_unit_interval _ fun n y z h1 h2 h3 h4 => by
    unfold ZtruncR
    rw [ceil_eq_of_between h1 h2, ceil_eq_of_between h3 h4, floor_eq_of_between h1 h2,
      floor_eq_of_between h3 h4]
    by_cases hy : y < 0
    · rw [if_pos hy, if_pos ((neg_iff_of_unit_interval h1 h2 h3 h4).1 hy)]
    · rw [if_neg hy, if_neg (fun hz => hy ((neg_iff_of_unit_interval h1 h2 h3 h4).2 hz))]

theorem Rnd_ext_Zaway : Rnd_ext Zaway ZawayR where
  agree q := by
    unfold ZawayR Zaway Rlt_bool
    by_cases h : q < 0
    · have h' : (q : ℝ) < 0 := by exact_mod_cast h
      rw [if_pos h', decide_eq_true h, if_pos rfl, Rat.floor_cast]; rfl
    · have h' : ¬ (q : ℝ) < 0 := by exact_mod_cast h
      rw [if_neg h', decide_eq_false h, if_neg Bool.false_ne_true, Rat.ceil_cast, Zceil_eq_ceil]
  stable := stable_of_unit_interval _ fun n y z h1 h2 h3 h4 => by
    unfold ZawayR
    rw [ceil_eq_of_between h1 h2, ceil_eq_of_between h3 h4, floor_eq_of_between h1 h2,
      floor_eq_of_between h3 h4]
    by_cases hy : y < 0
    · rw [if_pos hy, if_pos ((neg_iff_of_unit_interval h1 h2 h3 h4).1 hy)]
    · rw [if_neg hy, if_neg (fun hz => hy ((neg_iff_of_unit_interval h1 h2 h3 h4).2 hz))]

theorem Rnd_ext_Znearest (choice : ℤ → Bool) : Rnd_ext (Znearest choice) (ZnearestR choice) where
  agree q := by
    unfold ZnearestR Znearest Rcompare
    rw [Rat.floor_cast, ← Zfloor_eq_floor, Rat.ceil_cast, ← Zceil_eq_ceil]
    have e : (q : ℝ) - ((Zfloor q : ℤ) : ℝ) = ((q - ((Zfloor q : ℤ) : ℚ) : ℚ) : ℝ) := by
      push_cast; rfl
    have e2 : (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) := by push_cast; rfl
    rw [e, e2]
    by_cases h1 : q - ((Zfloor q : ℤ) : ℚ) < 1 / 2
    · rw [if_pos (by exact_mod_cast h1), if_pos h1]
    · rw [if_neg (by exact_mod_cast h1), if_neg h1]
      by_cases h2 : q - ((Zfloor q : ℤ) : ℚ) = 1 / 2
      · rw [if_pos (by exact_mod_cast h2), if_pos h2]
      · rw [if_neg (by exact_mod_cast h2), if_neg h2]
  stable m hm := by
    obtain ⟨h1, h2⟩ := floor_lt_of_irrational hm
    set n := ⌊m⌋ with hn
    have hmid : m ≠ (n : ℝ) + 1 / 2 := by
      intro h; apply hm.ne_rat ((n : ℚ) + 1 / 2); rw [h]; push_cast; rfl
    rcases lt_or_gt_of_ne hmid with hlt | hgt
    · refine ⟨n, n + 1 / 2, h1, hlt, fun y hy1 hy2 => ?_⟩
      have fy : ⌊y⌋ = n := floor_eq_of_between hy1 (by linarith)
      unfold ZnearestR
      rw [fy, ← hn, if_pos (by linarith), if_pos (by linarith)]
    · refine ⟨n + 1 / 2, n + 1, hgt, h2, fun y hy1 hy2 => ?_⟩
      have fy : ⌊y⌋ = n := floor_eq_of_between (by linarith) hy2
      have cy : ⌈y⌉ = n + 1 := ceil_eq_of_between (by linarith) hy2
      have cm : ⌈m⌉ = n + 1 := ceil_eq_of_between h1 h2
      unfold ZnearestR
      rw [fy, cy, ← hn, cm, if_neg (by linarith), if_neg (by linarith), if_neg (by linarith),
        if_neg (by linarith)]

/-! ### Canonical exponent, scaled mantissa, format and rounding on `ℝ` -/

section Generic
variable (beta : radix) (fexp : ℤ → ℤ)

/-- `Generic_fmt.cexp` on `R`. -/
def cexpR (x : ℝ) : ℤ := fexp (magR beta x)

/-- `Generic_fmt.scaled_mantissa` on `R`. -/
def scaled_mantissaR (x : ℝ) : ℝ := x * bpowR beta (-(cexpR beta fexp x))

/-- `Generic_fmt.generic_format` on `R`. -/
def generic_formatR (x : ℝ) : Prop :=
  x = F2RR (Float beta (ZtruncR (scaled_mantissaR beta fexp x)) (cexpR beta fexp x))

/-- `Generic_fmt.round` on `R`, for a rounding function `rnd : ℝ → ℤ`. -/
def roundR (rnd : ℝ → ℤ) (x : ℝ) : ℝ :=
  F2RR (Float beta (rnd (scaled_mantissaR beta fexp x)) (cexpR beta fexp x))

theorem cexpR_cast (q : ℚ) : cexpR beta fexp q = cexp beta fexp q := by
  unfold cexpR cexp; rw [magR_cast]

theorem scaled_mantissaR_cast (q : ℚ) :
    scaled_mantissaR beta fexp q = ((scaled_mantissa beta fexp q : ℚ) : ℝ) := by
  unfold scaled_mantissaR scaled_mantissa
  rw [Rat.cast_mul, bpow_cast, cexpR_cast]

/-- On rationals, the real `round` is the rational `round`. -/
theorem round_cast {rnd : ℚ → ℤ} {rndR : ℝ → ℤ} (h : Rnd_ext rnd rndR) (q : ℚ) :
    ((round beta fexp rnd q : ℚ) : ℝ) = roundR beta fexp rndR q := by
  unfold round roundR
  rw [F2R_cast, scaled_mantissaR_cast, cexpR_cast, h.agree]

/-- On rationals, the real `generic_format` is the rational `generic_format`. -/
theorem generic_formatR_cast (q : ℚ) :
    generic_formatR beta fexp q ↔ generic_format beta fexp q := by
  unfold generic_formatR generic_format
  rw [scaled_mantissaR_cast, cexpR_cast, Rnd_ext_Ztrunc.agree, ← F2R_cast]
  exact Rat.cast_inj

theorem roundR_zero {rnd : ℚ → ℤ} {rndR : ℝ → ℤ} [Valid_rnd rnd] (h : Rnd_ext rnd rndR) :
    roundR beta fexp rndR 0 = 0 := by
  have := round_cast beta fexp h 0
  simp only [round_0, Rat.cast_zero] at this
  exact this.symm

/-- At an irrational `y > 0`, the real rounding of `y` is the rounding of every
rational in a neighbourhood `(L, H)` of `y`, with `L > 0`. -/
theorem roundR_near_irrational {rnd : ℚ → ℤ} {rndR : ℝ → ℤ} (h : Rnd_ext rnd rndR)
    (y : ℝ) (hy : 0 < y) (hi : Irrational y) :
    ∃ L H : ℝ, 0 < L ∧ L < y ∧ y < H ∧
      ∀ q : ℚ, L < q → (q : ℝ) < H → ((round beta fexp rnd q : ℚ) : ℝ) = roundR beta fexp rndR y := by
  set e := magR beta y with he
  set c := fexp e with hc
  obtain ⟨hy1, hy2⟩ := magR_strict_of_irrational beta y hy hi
  rw [← he] at hy1 hy2
  have hB : 0 < bpowR beta c := bpowR_pos beta c
  have hm : scaled_mantissaR beta fexp y = y * (bpowR beta c)⁻¹ := by
    unfold scaled_mantissaR cexpR; rw [← he, ← hc, bpowR_opp]
  have hmi : Irrational (scaled_mantissaR beta fexp y) := by
    rw [hm, ← bpowR_opp, ← bpow_cast]
    refine hi.mul_ratCast ?_
    intro h0
    have := bpowR_pos beta (-c)
    rw [← bpow_cast, h0, Rat.cast_zero] at this
    exact lt_irrefl _ this
  obtain ⟨lo, hi', hlo, hhi, hst⟩ := h.stable _ hmi
  rw [hm] at hlo hhi
  have hlo' : lo * bpowR beta c < y := by
    have := mul_lt_mul_of_pos_right hlo hB
    rwa [mul_assoc, inv_mul_cancel₀ hB.ne', mul_one] at this
  have hhi' : y < hi' * bpowR beta c := by
    have := mul_lt_mul_of_pos_right hhi hB
    rwa [mul_assoc, inv_mul_cancel₀ hB.ne', mul_one] at this
  refine ⟨max (bpowR beta (e - 1)) (lo * bpowR beta c), min (bpowR beta e) (hi' * bpowR beta c),
    lt_of_lt_of_le (bpowR_pos beta _) (le_max_left _ _), max_lt hy1 hlo', lt_min hy2 hhi', ?_⟩
  intro q hq1 hq2
  have hqe : magR beta q = e :=
    magR_unique_pos beta _ e ⟨(le_max_left _ _).trans hq1.le, lt_of_lt_of_le hq2 (min_le_left _ _)⟩
  rw [round_cast beta fexp h]
  unfold roundR
  have hcq : cexpR beta fexp q = c := by unfold cexpR; rw [hqe]
  have hcy : cexpR beta fexp y = c := rfl
  have hmq : scaled_mantissaR beta fexp q = q * (bpowR beta c)⁻¹ := by
    unfold scaled_mantissaR; rw [hcq, bpowR_opp]
  rw [hcq, hcy]
  suffices key : rndR (scaled_mantissaR beta fexp q) = rndR (scaled_mantissaR beta fexp y) by
    rw [key]
  rw [hmq]
  apply hst
  · have := lt_of_le_of_lt (le_max_right _ _) hq1
    rw [lt_mul_inv_iff₀ hB]; exact this
  · have := lt_of_lt_of_le hq2 (min_le_right _ _)
    rw [mul_inv_lt_iff₀ hB]; exact this

end Generic

end

end Flocq
end CC
