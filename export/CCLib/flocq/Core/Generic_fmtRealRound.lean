/-
  Port of the rounding theory of Flocq's `Core/Generic_fmt.v` (Flocq 4, as
  shipped with CompCert) for arbitrary real arguments, over Mathlib's `ℝ`.

  Copyright (C) 2009-2018 Sylvie Boldo, Guillaume Melquiond (Flocq, LGPL-3.0+).

  `Generic_fmt.lean` proves the rounding theory over `Rat`, and
  `Generic_fmtReal.lean` defines `cexpR`, `scaled_mantissaR`,
  `generic_formatR` and `roundR` on `ℝ` and relates them with the rational
  versions.  This file proves the main results of `Generic_fmt.v` directly
  over `ℝ`, for every real argument (rational or not):
  * `Valid_rndR` is Rocq's `Valid_rnd` for rounding functions `ℝ → ℤ`, with
    instances for `ZfloorR`, `ZceilR`, `ZtruncR`, `ZawayR` and every
    `ZnearestR choice`;
  * `generic_formatR_iff`, `generic_formatR_0`, `generic_formatR_opp`,
    `generic_formatR_F2R`, `generic_formatR_bpow`;
  * `roundR_generic` (`round_generic`), `roundR_le` (`round_le`, monotonicity),
    `roundR_opp`, `roundR_bounded_large_pos`, `roundR_bounded_small_pos`,
    `generic_formatR_round` (`generic_format_round`);
  * `roundR_DN_pt`, `roundR_UP_pt`, `roundR_N_pt` (the rounded value is the
    largest format number below `x`, the smallest above, a nearest one);
  * `generic_formatR_rat`: every real in the format is rational.
-/
import CCLib.flocq.Core.Generic_fmtReal

namespace CC
namespace Flocq

noncomputable section

/-! ### Rounding functions `ℝ → ℤ` -/

/-- `Generic_fmt.Valid_rnd` for rounding functions on `R`. -/
class Valid_rndR (rnd : ℝ → ℤ) : Prop where
  Zrnd_le : ∀ x y : ℝ, x ≤ y → rnd x ≤ rnd y
  Zrnd_IZR : ∀ n : ℤ, rnd (n : ℝ) = n

instance Valid_rndR_floor : Valid_rndR ZfloorR :=
  ⟨fun _ _ h => Int.floor_mono h, fun n => Int.floor_intCast n⟩

instance Valid_rndR_ceil : Valid_rndR ZceilR :=
  ⟨fun _ _ h => Int.ceil_mono h, fun n => Int.ceil_intCast n⟩

instance Valid_rndR_trunc : Valid_rndR ZtruncR where
  Zrnd_le x y h := by
    unfold ZtruncR
    by_cases hx : x < 0 <;> by_cases hy : y < 0 <;> simp only [hx, hy, if_true, if_false]
    · exact Int.ceil_mono h
    · have : ⌈x⌉ ≤ 0 := Int.ceil_le.mpr (by push_cast; linarith)
      have : 0 ≤ ⌊y⌋ := Int.floor_nonneg.mpr (by linarith)
      omega
    · exact absurd (lt_of_le_of_lt h hy) hx
    · exact Int.floor_mono h
  Zrnd_IZR n := by unfold ZtruncR; split <;> simp

instance Valid_rndR_away : Valid_rndR ZawayR where
  Zrnd_le x y h := by
    unfold ZawayR
    by_cases hx : x < 0 <;> by_cases hy : y < 0 <;> simp only [hx, hy, if_true, if_false]
    · exact Int.floor_mono h
    · have : ⌊x⌋ ≤ 0 := Int.floor_le_iff.mpr (by push_cast; linarith)
      have : 0 ≤ ⌈y⌉ := Int.ceil_nonneg (by linarith)
      omega
    · exact absurd (lt_of_le_of_lt h hy) hx
    · exact Int.ceil_mono h
  Zrnd_IZR n := by unfold ZawayR; split <;> simp

/-- If `x` is not an integer, `⌈x⌉ = ⌊x⌋ + 1`. -/
theorem ceil_eq_floor_add_one_of_pos {x : ℝ} (h : 0 < x - ⌊x⌋) : ⌈x⌉ = ⌊x⌋ + 1 := by
  apply Int.ceil_eq_iff.mpr
  push_cast
  constructor <;> linarith [Int.lt_floor_add_one x]

/-- `ZnearestR` without `⌈·⌉`. -/
theorem ZnearestR_eq (choice : ℤ → Bool) (x : ℝ) :
    ZnearestR choice x =
      if x - ⌊x⌋ < 1 / 2 then ⌊x⌋
      else if x - ⌊x⌋ = 1 / 2 then (if choice ⌊x⌋ then ⌊x⌋ + 1 else ⌊x⌋)
      else ⌊x⌋ + 1 := by
  unfold ZnearestR
  by_cases h1 : x - ⌊x⌋ < 1 / 2
  · rw [if_pos h1, if_pos h1]
  · have hc := ceil_eq_floor_add_one_of_pos (x := x) (by linarith)
    simp only [h1, if_false, hc]

theorem ZnearestR_bounds (choice : ℤ → Bool) (x : ℝ) :
    ⌊x⌋ ≤ ZnearestR choice x ∧ ZnearestR choice x ≤ ⌊x⌋ + 1 := by
  rw [ZnearestR_eq]
  split_ifs <;> omega

instance Valid_rndR_nearest (choice : ℤ → Bool) : Valid_rndR (ZnearestR choice) where
  Zrnd_le x y h := by
    have hxb := ZnearestR_bounds choice x
    have hyb := ZnearestR_bounds choice y
    have hf : ⌊x⌋ ≤ ⌊y⌋ := Int.floor_mono h
    rcases lt_or_eq_of_le hf with hlt | heq
    · omega
    · rw [ZnearestR_eq, ZnearestR_eq, ← heq]
      have hfx : (⌊x⌋ : ℝ) = ⌊y⌋ := by rw [heq]
      have : x - ⌊x⌋ ≤ y - ⌊y⌋ := by rw [hfx]; linarith
      rcases lt_trichotomy (x - ⌊x⌋) (1 / 2) with a | a | a <;>
      rcases Bool.eq_false_or_eq_true (choice ⌊x⌋) with hc | hc <;> simp only [hc] <;>
        split_ifs <;> first | omega | (exfalso; linarith)
  Zrnd_IZR n := by
    rw [ZnearestR_eq]; simp

/-- The opposite rounding function `fun x => - rnd (-x)` (`Zrnd_opp`). -/
def Zrnd_oppR (rnd : ℝ → ℤ) (x : ℝ) : ℤ := -rnd (-x)

instance Valid_rndR_opp (rnd : ℝ → ℤ) [Valid_rndR rnd] : Valid_rndR (Zrnd_oppR rnd) where
  Zrnd_le x y h := by
    unfold Zrnd_oppR
    have := Valid_rndR.Zrnd_le (rnd := rnd) (-y) (-x) (by linarith)
    omega
  Zrnd_IZR n := by
    unfold Zrnd_oppR
    have := Valid_rndR.Zrnd_IZR (rnd := rnd) (-n)
    push_cast at this; rw [this]; ring

/-- `Zrnd_DN_or_UP` on `ℝ`. -/
theorem ZrndR_DN_or_UP (rnd : ℝ → ℤ) [Valid_rndR rnd] (x : ℝ) :
    rnd x = ⌊x⌋ ∨ rnd x = ⌈x⌉ := by
  have h1 : (⌊x⌋ : ℤ) ≤ rnd x := by
    have := Valid_rndR.Zrnd_le (rnd := rnd) _ _ (Int.floor_le x)
    rwa [Valid_rndR.Zrnd_IZR (rnd := rnd)] at this
  have h2 : rnd x ≤ ⌈x⌉ := by
    have := Valid_rndR.Zrnd_le (rnd := rnd) _ _ (Int.le_ceil x)
    rwa [Valid_rndR.Zrnd_IZR (rnd := rnd)] at this
  have h3 : ⌈x⌉ ≤ ⌊x⌋ + 1 := Int.ceil_le_floor_add_one x
  omega

/-- A valid rounding moves its argument by less than one. -/
theorem ZrndR_abs_sub_lt (rnd : ℝ → ℤ) [Valid_rndR rnd] (x : ℝ) : |(rnd x : ℝ) - x| < 1 := by
  rw [abs_lt]
  rcases ZrndR_DN_or_UP rnd x with h | h <;> rw [h]
  · constructor <;> linarith [Int.floor_le x, Int.lt_floor_add_one x]
  · constructor <;> linarith [Int.le_ceil x, Int.ceil_lt_add_one x]

/-- `ZnearestR` moves its argument by at most one half. -/
theorem ZnearestR_abs_sub_le (choice : ℤ → Bool) (x : ℝ) :
    |(ZnearestR choice x : ℝ) - x| ≤ 1 / 2 := by
  rw [ZnearestR_eq, abs_le]
  have h0 := Int.floor_le x
  have h1 := Int.lt_floor_add_one x
  split_ifs with ha hb hc
  · constructor <;> linarith
  · push_cast; constructor <;> linarith
  · constructor <;> linarith
  · push_cast
    constructor <;> linarith [lt_of_le_of_ne (not_lt.mp ha) (Ne.symm hb)]

/-- `ZnearestR` picks a nearest integer. -/
theorem ZnearestR_nearest (choice : ℤ → Bool) (x : ℝ) :
    |(ZnearestR choice x : ℝ) - x| ≤ x - ⌊x⌋ ∧ |(ZnearestR choice x : ℝ) - x| ≤ ⌊x⌋ + 1 - x := by
  rw [ZnearestR_eq]
  have h0 := Int.floor_le x
  have h1 := Int.lt_floor_add_one x
  split_ifs with ha hb hc <;> push_cast <;>
    (refine ⟨?_, ?_⟩ <;> rw [abs_le] <;> constructor <;> linarith)

/-! ### Format and rounding on `ℝ` -/

section Generic
variable (beta : radix) (fexp : ℤ → ℤ)

theorem bpowR_add (a b : ℤ) : bpowR beta a * bpowR beta b = bpowR beta (a + b) :=
  (bpowR_plus beta a b).symm

/-- A nonnegative power of the radix is an integer. -/
theorem bpowR_nonneg_int (e : ℤ) (he : 0 ≤ e) :
    bpowR beta e = ((beta.radix_val ^ e.toNat : ℤ) : ℝ) := by
  unfold bpowR
  conv_lhs => rw [← Int.toNat_of_nonneg he]
  rw [zpow_natCast]; push_cast; rfl

theorem bpowR_mono {a b : ℤ} (h : a ≤ b) : bpowR beta a ≤ bpowR beta b :=
  (bpowR_le_iff beta a b).2 h

theorem scaled_mantissaR_mul (x : ℝ) :
    scaled_mantissaR beta fexp x * bpowR beta (cexpR beta fexp x) = x := by
  unfold scaled_mantissaR
  rw [mul_assoc, bpowR_add, neg_add_cancel]
  simp [bpowR]

theorem roundR_eq (rnd : ℝ → ℤ) (x : ℝ) :
    roundR beta fexp rnd x =
      (rnd (scaled_mantissaR beta fexp x) : ℝ) * bpowR beta (cexpR beta fexp x) := rfl

theorem roundR_sub (rnd : ℝ → ℤ) (x : ℝ) :
    roundR beta fexp rnd x - x =
      ((rnd (scaled_mantissaR beta fexp x) : ℝ) - scaled_mantissaR beta fexp x) *
        bpowR beta (cexpR beta fexp x) := by
  rw [roundR_eq, sub_mul, scaled_mantissaR_mul]

theorem magR_opp (x : ℝ) : magR beta (-x) = magR beta x := by
  unfold magR; simp

theorem cexpR_opp (x : ℝ) : cexpR beta fexp (-x) = cexpR beta fexp x := by
  unfold cexpR; rw [magR_opp]

theorem scaled_mantissaR_opp (x : ℝ) :
    scaled_mantissaR beta fexp (-x) = -scaled_mantissaR beta fexp x := by
  unfold scaled_mantissaR; rw [cexpR_opp]; ring

/-- `Generic_fmt.round_opp` on `ℝ`. -/
theorem roundR_opp (rnd : ℝ → ℤ) (x : ℝ) :
    roundR beta fexp rnd (-x) = -roundR beta fexp (Zrnd_oppR rnd) x := by
  rw [roundR_eq, roundR_eq, scaled_mantissaR_opp, cexpR_opp]
  unfold Zrnd_oppR; push_cast; ring

theorem scaled_mantissaR_of_eq (x : ℝ) (m : ℤ)
    (hm : x = (m : ℝ) * bpowR beta (cexpR beta fexp x)) : scaled_mantissaR beta fexp x = m := by
  unfold scaled_mantissaR
  generalize cexpR beta fexp x = c at hm ⊢
  subst hm
  rw [mul_assoc, bpowR_add, add_neg_cancel]; simp [bpowR]

/-- A real is in the format iff it is an integer multiple of `bpow (cexp x)`. -/
theorem generic_formatR_iff (x : ℝ) :
    generic_formatR beta fexp x ↔ ∃ m : ℤ, x = (m : ℝ) * bpowR beta (cexpR beta fexp x) := by
  constructor
  · intro h; exact ⟨_, h⟩
  · rintro ⟨m, hm⟩
    have hs := scaled_mantissaR_of_eq beta fexp x m hm
    unfold generic_formatR F2RR
    simp only
    rw [hs, Valid_rndR.Zrnd_IZR (rnd := ZtruncR)]
    exact hm

/-- `Generic_fmt.generic_format_0` on `ℝ`. -/
theorem generic_formatR_0 : generic_formatR beta fexp 0 :=
  (generic_formatR_iff beta fexp 0).2 ⟨0, by simp⟩

/-- `Generic_fmt.generic_format_opp` on `ℝ`. -/
theorem generic_formatR_opp (x : ℝ) (hx : generic_formatR beta fexp x) :
    generic_formatR beta fexp (-x) := by
  obtain ⟨m, hm⟩ := (generic_formatR_iff beta fexp x).1 hx
  refine (generic_formatR_iff beta fexp (-x)).2 ⟨-m, ?_⟩
  rw [cexpR_opp]; push_cast; rw [neg_mul, ← hm]

/-- `Generic_fmt.generic_format_F2R` on `ℝ`: `m * bpow e` is in the format as
soon as its canonical exponent is at most `e`. -/
theorem generic_formatR_F2R (m e : ℤ)
    (h : cexpR beta fexp ((m : ℝ) * bpowR beta e) ≤ e) :
    generic_formatR beta fexp ((m : ℝ) * bpowR beta e) := by
  set c := cexpR beta fexp ((m : ℝ) * bpowR beta e)
  refine (generic_formatR_iff beta fexp _).2 ⟨m * beta.radix_val ^ (e - c).toNat, ?_⟩
  push_cast
  rw [← Int.cast_pow, ← bpowR_nonneg_int beta _ (by omega), mul_assoc, bpowR_add]
  congr 2; ring

theorem magR_bpowR (e : ℤ) : magR beta (bpowR beta e) = e + 1 := by
  apply magR_unique_pos
  rw [add_sub_cancel_right]
  exact ⟨le_refl _, (bpowR_lt_iff beta _ _).2 (by omega)⟩

/-- `Generic_fmt.generic_format_bpow` on `ℝ`. -/
theorem generic_formatR_bpow (e : ℤ) (h : fexp (e + 1) ≤ e) :
    generic_formatR beta fexp (bpowR beta e) := by
  have := generic_formatR_F2R beta fexp 1 e (by
    rw [Int.cast_one, one_mul]; unfold cexpR; rw [magR_bpowR]; exact h)
  rwa [Int.cast_one, one_mul] at this

/-- Every real in the format is rational, and in the rational format. -/
theorem generic_formatR_rat (x : ℝ) (hx : generic_formatR beta fexp x) :
    ∃ q : ℚ, (q : ℝ) = x ∧ generic_format beta fexp q := by
  obtain ⟨m, hm⟩ := (generic_formatR_iff beta fexp x).1 hx
  have e : (((m : ℚ) * bpow beta (cexpR beta fexp x) : ℚ) : ℝ) = x := by
    rw [Rat.cast_mul, bpow_cast]; push_cast; exact hm.symm
  refine ⟨(m : ℚ) * bpow beta (cexpR beta fexp x), e, ?_⟩
  rw [← generic_formatR_cast, e]; exact hx

section Round
variable (rnd : ℝ → ℤ) [Valid_rndR rnd]

/-- `Generic_fmt.round_generic` on `ℝ`. -/
theorem roundR_generic (x : ℝ) (hx : generic_formatR beta fexp x) :
    roundR beta fexp rnd x = x := by
  obtain ⟨m, hm⟩ := (generic_formatR_iff beta fexp x).1 hx
  have hs := scaled_mantissaR_of_eq beta fexp x m hm
  rw [roundR_eq, hs, Valid_rndR.Zrnd_IZR (rnd := rnd)]; exact hm.symm

/-- `Generic_fmt.round_0` on `ℝ`. -/
theorem roundR_0 : roundR beta fexp rnd 0 = 0 :=
  roundR_generic beta fexp rnd 0 (generic_formatR_0 beta fexp)

theorem scaled_mantissaR_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ scaled_mantissaR beta fexp x :=
  mul_nonneg hx (bpowR_pos beta _).le

theorem roundR_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ roundR beta fexp rnd x := by
  rw [roundR_eq]
  have h := Valid_rndR.Zrnd_le (rnd := rnd) _ _ (scaled_mantissaR_nonneg beta fexp x hx)
  have h0 := Valid_rndR.Zrnd_IZR (rnd := rnd) 0
  push_cast at h0; rw [h0] at h
  exact mul_nonneg (by exact_mod_cast h) (bpowR_pos beta _).le

theorem roundR_nonpos (x : ℝ) (hx : x ≤ 0) : roundR beta fexp rnd x ≤ 0 := by
  have h1 := roundR_nonneg beta fexp (Zrnd_oppR rnd) (-x) (by linarith)
  have h2 := roundR_opp beta fexp rnd (-x)
  rw [neg_neg] at h2
  linarith

/-- For `0 < x` with `bpow (ex - 1) ≤ x < bpow ex`, write `x` with respect to
its magnitude. -/
theorem magR_spec_pos (x : ℝ) (hx : 0 < x) :
    bpowR beta (magR beta x - 1) ≤ x ∧ x < bpowR beta (magR beta x) := by
  have := magR_spec beta x hx.ne'
  rwa [abs_of_pos hx] at this

theorem magR_le_pos (x y : ℝ) (hx : 0 < x) (h : x ≤ y) : magR beta x ≤ magR beta y := by
  have h1 := (magR_spec_pos beta x hx).1
  have h2 := (magR_spec_pos beta y (lt_of_lt_of_le hx h)).2
  have := (bpowR_lt_iff beta _ _).1 (lt_of_le_of_lt (h1.trans h) h2)
  omega

/-- `Generic_fmt.round_bounded_large_pos` on `ℝ`. -/
theorem roundR_bounded_large_pos [Valid_exp fexp] (x : ℝ) (hx : 0 < x)
    (h : fexp (magR beta x) < magR beta x) :
    bpowR beta (magR beta x - 1) ≤ roundR beta fexp rnd x ∧
      roundR beta fexp rnd x ≤ bpowR beta (magR beta x) := by
  set ex := magR beta x with hex
  set c := cexpR beta fexp x with hc
  have hcd : c = fexp ex := rfl
  obtain ⟨h1, h2⟩ := magR_spec_pos beta x hx
  rw [← hex] at h1 h2
  have hB := bpowR_pos beta c
  have hs : scaled_mantissaR beta fexp x = x * bpowR beta (-c) := rfl
  have hBi : bpowR beta (-c) * bpowR beta c = 1 := by rw [bpowR_add, neg_add_cancel]; simp [bpowR]
  rw [roundR_eq, ← hc]
  constructor
  · -- lower bound: `bpow (ex - 1 - c)` is an integer below the scaled mantissa
    have hN := bpowR_nonneg_int beta (ex - 1 - c) (by omega)
    have hle : ((beta.radix_val ^ (ex - 1 - c).toNat : ℤ) : ℝ) ≤ scaled_mantissaR beta fexp x := by
      rw [← hN, hs, show ex - 1 - c = (ex - 1) + -c by ring, ← bpowR_add]
      exact mul_le_mul_of_nonneg_right h1 (bpowR_pos beta _).le
    have := Valid_rndR.Zrnd_le (rnd := rnd) _ _ hle
    rw [Valid_rndR.Zrnd_IZR (rnd := rnd)] at this
    have := mul_le_mul_of_nonneg_right (Int.cast_le (R := ℝ).2 this) hB.le
    rwa [← hN, bpowR_add, show ex - 1 - c + c = ex - 1 by ring] at this
  · have hN := bpowR_nonneg_int beta (ex - c) (by omega)
    have hle : scaled_mantissaR beta fexp x ≤ ((beta.radix_val ^ (ex - c).toNat : ℤ) : ℝ) := by
      rw [← hN, hs, show ex - c = ex + -c by ring, ← bpowR_add]
      exact mul_le_mul_of_nonneg_right h2.le (bpowR_pos beta _).le
    have := Valid_rndR.Zrnd_le (rnd := rnd) _ _ hle
    rw [Valid_rndR.Zrnd_IZR (rnd := rnd)] at this
    have := mul_le_mul_of_nonneg_right (Int.cast_le (R := ℝ).2 this) hB.le
    rwa [← hN, bpowR_add, show ex - c + c = ex by ring] at this

/-- `Generic_fmt.round_bounded_small_pos` on `ℝ`. -/
theorem roundR_bounded_small_pos (x : ℝ) (hx : 0 < x)
    (h : magR beta x ≤ fexp (magR beta x)) :
    roundR beta fexp rnd x = 0 ∨ roundR beta fexp rnd x = bpowR beta (fexp (magR beta x)) := by
  set ex := magR beta x with hex
  have hc : cexpR beta fexp x = fexp ex := rfl
  obtain ⟨_, h2⟩ := magR_spec_pos beta x hx
  rw [← hex] at h2
  have hs0 : 0 ≤ scaled_mantissaR beta fexp x := scaled_mantissaR_nonneg beta fexp x hx.le
  have hs1 : scaled_mantissaR beta fexp x ≤ 1 := by
    unfold scaled_mantissaR; rw [hc]
    have := mul_le_mul_of_nonneg_right (h2.le.trans (bpowR_mono beta h)) (bpowR_pos beta (-fexp ex)).le
    rwa [bpowR_add, add_neg_cancel, show bpowR beta 0 = 1 by simp [bpowR]] at this
  have l0 := Valid_rndR.Zrnd_le (rnd := rnd) _ _ hs0
  have l1 := Valid_rndR.Zrnd_le (rnd := rnd) _ _ hs1
  have e0 := Valid_rndR.Zrnd_IZR (rnd := rnd) 0
  have e1 := Valid_rndR.Zrnd_IZR (rnd := rnd) 1
  push_cast at e0 e1
  rw [e0] at l0; rw [e1] at l1
  rw [roundR_eq, hc]
  rcases (show rnd (scaled_mantissaR beta fexp x) = 0 ∨ rnd (scaled_mantissaR beta fexp x) = 1 by
    omega) with h0 | h0 <;> rw [h0] <;> simp

/-- `Generic_fmt.round_le_pos` on `ℝ`. -/
theorem roundR_le_pos [Valid_exp fexp] (x y : ℝ) (hx : 0 < x) (h : x ≤ y) :
    roundR beta fexp rnd x ≤ roundR beta fexp rnd y := by
  have hy : 0 < y := lt_of_lt_of_le hx h
  have hm := magR_le_pos beta x y hx h
  have same : fexp (magR beta x) = fexp (magR beta y) →
      roundR beta fexp rnd x ≤ roundR beta fexp rnd y := by
    intro he
    have hc : cexpR beta fexp x = cexpR beta fexp y := he
    rw [roundR_eq, roundR_eq, hc]
    apply mul_le_mul_of_nonneg_right _ (bpowR_pos beta _).le
    apply Int.cast_le.2
    apply Valid_rndR.Zrnd_le
    unfold scaled_mantissaR; rw [hc]
    exact mul_le_mul_of_nonneg_right h (bpowR_pos beta _).le
  rcases lt_or_eq_of_le hm with hlt | heq
  · by_cases hfy : fexp (magR beta y) < magR beta y
    · have hly := (roundR_bounded_large_pos beta fexp rnd y hy hfy).1
      have hux : roundR beta fexp rnd x ≤ bpowR beta (magR beta y - 1) := by
        by_cases hfx : fexp (magR beta x) < magR beta x
        · exact (roundR_bounded_large_pos beta fexp rnd x hx hfx).2.trans
            (bpowR_mono beta (by omega))
        · have hfx' : fexp (magR beta x) < magR beta y :=
            valid_exp_large' fexp _ _ hfy hlt.le
          rcases roundR_bounded_small_pos beta fexp rnd x hx (by omega) with h0 | h0
          · rw [h0]; exact (bpowR_pos beta _).le
          · rw [h0]; exact bpowR_mono beta (by omega)
      exact hux.trans hly
    · have := ((Valid_exp.valid_exp (fexp := fexp) (magR beta y)).2 (by omega)).2
        (magR beta x) (by omega)
      exact same this
  · exact same (by rw [heq])

/-- `Generic_fmt.round_le` on `ℝ`: rounding is monotone. -/
theorem roundR_le [Valid_exp fexp] (x y : ℝ) (h : x ≤ y) :
    roundR beta fexp rnd x ≤ roundR beta fexp rnd y := by
  rcases lt_or_ge 0 x with hx | hx
  · exact roundR_le_pos beta fexp rnd x y hx h
  rcases le_or_gt 0 y with hy | hy
  · exact (roundR_nonpos beta fexp rnd x hx).trans (roundR_nonneg beta fexp rnd y hy)
  · have h1 := roundR_opp beta fexp rnd (-x)
    have h2 := roundR_opp beta fexp rnd (-y)
    rw [neg_neg] at h1 h2
    have := roundR_le_pos beta fexp (Zrnd_oppR rnd) (-y) (-x) (by linarith) (by linarith)
    linarith

/-- `Generic_fmt.round_DN_or_UP` on `ℝ`. -/
theorem roundR_DN_or_UP (x : ℝ) :
    roundR beta fexp rnd x = roundR beta fexp ZfloorR x ∨
      roundR beta fexp rnd x = roundR beta fexp ZceilR x := by
  rw [roundR_eq, roundR_eq, roundR_eq]
  rcases ZrndR_DN_or_UP rnd (scaled_mantissaR beta fexp x) with h | h <;> rw [h]
  · left; rfl
  · right; rfl

/-- `Generic_fmt.generic_format_round_pos` on `ℝ`. -/
theorem generic_formatR_round_pos [Valid_exp fexp] (x : ℝ) (hx : 0 < x) :
    generic_formatR beta fexp (roundR beta fexp rnd x) := by
  by_cases hf : fexp (magR beta x) < magR beta x
  · obtain ⟨l, u⟩ := roundR_bounded_large_pos beta fexp rnd x hx hf
    rcases lt_or_eq_of_le u with u | u
    · have hmag : magR beta (roundR beta fexp rnd x) = magR beta x :=
        magR_unique_pos beta _ _ ⟨l, u⟩
      have hcr : cexpR beta fexp (roundR beta fexp rnd x) = cexpR beta fexp x := by
        unfold cexpR; rw [hmag]
      have := generic_formatR_F2R beta fexp (rnd (scaled_mantissaR beta fexp x))
        (cexpR beta fexp x) (by rw [← roundR_eq, hcr])
      rwa [← roundR_eq] at this
    · rw [u]
      exact generic_formatR_bpow beta fexp _ ((Valid_exp.valid_exp (fexp := fexp) _).1 hf)
  · rcases roundR_bounded_small_pos beta fexp rnd x hx (by omega) with h0 | h0
    · rw [h0]; exact generic_formatR_0 beta fexp
    · rw [h0]
      exact generic_formatR_bpow beta fexp _
        ((Valid_exp.valid_exp (fexp := fexp) (magR beta x)).2 (by omega)).1

end Round

/-- `Generic_fmt.generic_format_round` on `ℝ`: the rounded value is in the
format. -/
theorem generic_formatR_round [Valid_exp fexp] (rnd : ℝ → ℤ) [Valid_rndR rnd] (x : ℝ) :
    generic_formatR beta fexp (roundR beta fexp rnd x) := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rw [← neg_neg x, roundR_opp]
    exact generic_formatR_opp beta fexp _
      (generic_formatR_round_pos beta fexp (Zrnd_oppR rnd) (-x) (by linarith))
  · rw [hx, roundR_0]; exact generic_formatR_0 beta fexp
  · exact generic_formatR_round_pos beta fexp rnd x hx

/-- Rounding down never increases. -/
theorem roundR_DN_le (x : ℝ) : roundR beta fexp ZfloorR x ≤ x := by
  rw [roundR_eq]
  conv_rhs => rw [← scaled_mantissaR_mul beta fexp x]
  exact mul_le_mul_of_nonneg_right (Int.floor_le _) (bpowR_pos beta _).le

/-- Rounding up never decreases. -/
theorem roundR_UP_ge (x : ℝ) : x ≤ roundR beta fexp ZceilR x := by
  rw [roundR_eq]
  conv_lhs => rw [← scaled_mantissaR_mul beta fexp x]
  exact mul_le_mul_of_nonneg_right (Int.le_ceil _) (bpowR_pos beta _).le

/-- `Generic_fmt.round_DN_pt` on `ℝ`: rounding down gives the largest format
number below `x` (Rocq's `Rnd_DN_pt`). -/
theorem roundR_DN_pt [Valid_exp fexp] (x : ℝ) :
    generic_formatR beta fexp (roundR beta fexp ZfloorR x) ∧
      roundR beta fexp ZfloorR x ≤ x ∧
      ∀ g, generic_formatR beta fexp g → g ≤ x → g ≤ roundR beta fexp ZfloorR x := by
  refine ⟨generic_formatR_round beta fexp _ x, roundR_DN_le beta fexp x, fun g hg hgx => ?_⟩
  rw [← roundR_generic beta fexp ZfloorR g hg]
  exact roundR_le beta fexp _ g x hgx

/-- `Generic_fmt.round_UP_pt` on `ℝ`: rounding up gives the smallest format
number above `x` (Rocq's `Rnd_UP_pt`). -/
theorem roundR_UP_pt [Valid_exp fexp] (x : ℝ) :
    generic_formatR beta fexp (roundR beta fexp ZceilR x) ∧
      x ≤ roundR beta fexp ZceilR x ∧
      ∀ g, generic_formatR beta fexp g → x ≤ g → roundR beta fexp ZceilR x ≤ g := by
  refine ⟨generic_formatR_round beta fexp _ x, roundR_UP_ge beta fexp x, fun g hg hgx => ?_⟩
  rw [← roundR_generic beta fexp ZceilR g hg]
  exact roundR_le beta fexp _ x g hgx

/-- `Generic_fmt.round_N_pt` on `ℝ`: rounding to nearest gives a format number
nearest to `x` (Rocq's `Rnd_N_pt`). -/
theorem roundR_N_pt [Valid_exp fexp] (choice : ℤ → Bool) (x : ℝ) :
    generic_formatR beta fexp (roundR beta fexp (ZnearestR choice) x) ∧
      ∀ g, generic_formatR beta fexp g →
        |roundR beta fexp (ZnearestR choice) x - x| ≤ |g - x| := by
  refine ⟨generic_formatR_round beta fexp _ x, fun g hg => ?_⟩
  have hdn : g ≤ x → g ≤ (⌊scaled_mantissaR beta fexp x⌋ : ℝ) * bpowR beta (cexpR beta fexp x) :=
    fun h => (roundR_DN_pt beta fexp x).2.2 g hg h
  have hup : x ≤ g → (⌈scaled_mantissaR beta fexp x⌉ : ℝ) * bpowR beta (cexpR beta fexp x) ≤ g :=
    fun h => (roundR_UP_pt beta fexp x).2.2 g hg h
  have hB : 0 < bpowR beta (cexpR beta fexp x) := bpowR_pos beta _
  have hx := scaled_mantissaR_mul beta fexp x
  rw [roundR_eq]
  generalize scaled_mantissaR beta fexp x = s at hx hdn hup ⊢
  generalize bpowR beta (cexpR beta fexp x) = B at hx hB hdn hup ⊢
  subst hx
  obtain ⟨n1, n2⟩ := ZnearestR_nearest choice s
  have hd : (ZnearestR choice s : ℝ) * B - s * B = ((ZnearestR choice s : ℝ) - s) * B := by ring
  rw [hd, abs_mul, abs_of_pos hB]
  rcases le_total g (s * B) with hgx | hgx
  · have h1 := hdn hgx
    rw [abs_of_nonpos (show g - s * B ≤ 0 by linarith)]
    have h2 := mul_le_mul_of_nonneg_right n1 hB.le
    linarith
  · have h1 := hup hgx
    rw [abs_of_nonneg (show 0 ≤ g - s * B by linarith)]
    have n3 : |(ZnearestR choice s : ℝ) - s| ≤ ⌈s⌉ - s := by
      rcases eq_or_lt_of_le (Int.floor_le s) with he | hlt
      · have : ⌈s⌉ = ⌊s⌋ := by rw [← he]; simp
        rw [this]; linarith
      · rw [ceil_eq_floor_add_one_of_pos (by linarith)]; push_cast; linarith
    have h2 := mul_le_mul_of_nonneg_right n3 hB.le
    linarith

end Generic

end

end Flocq
end CC
