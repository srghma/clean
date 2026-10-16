/-
  Port of the real-number side of Flocq's `Core/Raux.v` (Flocq 4, as shipped
  with CompCert), over Mathlib's real numbers `ℝ`.

  Copyright (C) 2009-2018 Sylvie Boldo, Guillaume Melquiond (Flocq, LGPL-3.0+).

  The rest of the Flocq port works over `Rat` (see `Raux.lean`): every
  floating-point number is rational.  This file adds the definitions of
  `Raux.v` on Rocq's `R`, here Mathlib's `ℝ`, and connects them with the
  rational ones:
  * `bpowR r e` is Rocq's `bpow r e : R`; `bpow_cast` says that it is the cast
    of the rational `bpow r e`;
  * `magR r x` is Rocq's `mag r x` on `R` (`mag_val`), with `magR_spec`
    (Rocq's `mag_prop`), `magR_unique` (`mag_unique`) and `magR_cast` (it
    agrees with the rational `mag` on rationals);
  * `exp_le_real` and `bpow_exp_real` are `Raux.exp_le` and `Raux.bpow_exp`
    for Rocq's `exp`/`ln` (Mathlib's `Real.exp`/`Real.log`);
  * `ℝ` is an instance of the classes `RatSqrtField` (`RauxSqrt.lean`) and
    `RatExpField` (`RauxExp.lean`), so every result proved over those classes
    holds for the real square root, exponential and logarithm.
-/
import Mathlib
import CCLib.flocq.Core.RauxSqrt
import CCLib.flocq.Core.RauxExp

namespace CC
namespace Flocq

noncomputable section

/-! ### `ℝ` as a `RatSqrtField` and a `RatExpField` -/

instance : RatSqrtField ℝ where
  ofRat q := (q : ℝ)
  ofRat_add a b := Rat.cast_add a b
  ofRat_mul a b := Rat.cast_mul a b
  ofRat_one := Rat.cast_one
  ofRat_le _ _ := Rat.cast_le
  sqrt := Real.sqrt
  sqrt_nonneg := Real.sqrt_nonneg
  sqrt_sq _ hx := Real.mul_self_sqrt hx
  sqrt_neg _ hx := Real.sqrt_eq_zero'.mpr hx

instance : RatExpField ℝ where
  ofRat q := (q : ℝ)
  ofRat_add a b := Rat.cast_add a b
  ofRat_mul a b := Rat.cast_mul a b
  ofRat_one := Rat.cast_one
  ofRat_lt _ _ := Rat.cast_lt
  exp := Real.exp
  ln := Real.log
  exp_add := Real.exp_add
  exp_ln _ hx := Real.exp_log hx
  exp_increasing _ _ h := Real.exp_lt_exp.mpr h

@[simp] theorem RatSqrtField_ofRat_real (q : ℚ) : RatSqrtField.ofRat (R := ℝ) q = (q : ℝ) := rfl

@[simp] theorem RatSqrtField_sqrt_real (x : ℝ) : RatSqrtField.sqrt x = Real.sqrt x := rfl

@[simp] theorem RatExpField_ofRat_real (q : ℚ) : RatExpField.ofRat (R := ℝ) q = (q : ℝ) := rfl

@[simp] theorem RatExpField_exp_real (x : ℝ) : RatExpField.exp x = Real.exp x := rfl

@[simp] theorem RatExpField_ln_real (x : ℝ) : RatExpField.ln x = Real.log x := rfl

/-- The class's `rabs` on `ℝ` is the absolute value. -/
@[simp] theorem RatSqrtField_rabs_real (x : ℝ) : RatSqrtField.rabs x = |x| := by
  unfold RatSqrtField.rabs
  split
  · next h => exact (abs_of_nonneg h).symm
  · next h => exact (abs_of_neg (lt_of_not_ge h)).symm

/-! ### Powers of the radix on `ℝ` -/

/-- Rocq's `bpow r e` on `R`. -/
def bpowR (r : radix) (e : ℤ) : ℝ := (r.radix_val : ℝ) ^ e

theorem radix_gt_one_real (r : radix) : (1 : ℝ) < r.radix_val := by
  exact_mod_cast radix_gt_1 r

theorem radix_pos_real (r : radix) : (0 : ℝ) < r.radix_val :=
  lt_trans zero_lt_one (radix_gt_one_real r)

/-- The rational `bpow` cast to `ℝ` is `bpowR`. -/
theorem bpow_cast (r : radix) (e : ℤ) : ((bpow r e : ℚ) : ℝ) = bpowR r e := by
  unfold bpow bpowR; push_cast; rfl

theorem bpowR_pos (r : radix) (e : ℤ) : 0 < bpowR r e := zpow_pos (radix_pos_real r) e

theorem bpowR_ne_zero (r : radix) (e : ℤ) : bpowR r e ≠ 0 := (bpowR_pos r e).ne'

/-- `Raux.bpow_plus` on `ℝ`. -/
theorem bpowR_plus (r : radix) (a b : ℤ) : bpowR r (a + b) = bpowR r a * bpowR r b :=
  zpow_add₀ (radix_pos_real r).ne' a b

theorem bpowR_opp (r : radix) (e : ℤ) : bpowR r (-e) = (bpowR r e)⁻¹ := zpow_neg _ e

/-- `Raux.bpow_lt` and `Raux.lt_bpow` on `ℝ`. -/
theorem bpowR_lt_iff (r : radix) (a b : ℤ) : bpowR r a < bpowR r b ↔ a < b :=
  zpow_lt_zpow_iff_right₀ (radix_gt_one_real r)

/-- `Raux.bpow_le` and `Raux.le_bpow` on `ℝ`. -/
theorem bpowR_le_iff (r : radix) (a b : ℤ) : bpowR r a ≤ bpowR r b ↔ a ≤ b :=
  zpow_le_zpow_iff_right₀ (radix_gt_one_real r)

/-- `Raux.bpow_powerRZ` on `ℝ`: `bpow` is the integer power. -/
theorem bpowR_powerRZ (r : radix) (e : ℤ) : bpowR r e = (r.radix_val : ℝ) ^ e := rfl

/-! ### Exponential and logarithm -/

/-- `Raux.exp_le` for Rocq's `exp` (Mathlib's `Real.exp`). -/
theorem exp_le_real (x y : ℝ) (h : x ≤ y) : Real.exp x ≤ Real.exp y := Real.exp_le_exp.mpr h

/-- `Raux.bpow_exp`: `bpow r e = exp (IZR e * ln (IZR r))` on `ℝ`. -/
theorem bpow_exp_real (r : radix) (e : ℤ) :
    bpowR r e = Real.exp ((e : ℝ) * Real.log (r.radix_val : ℝ)) := by
  rw [bpowR, ← Real.rpow_intCast, Real.rpow_def_of_pos (radix_pos_real r), mul_comm]

/-! ### Magnitude on `ℝ` -/

theorem radix_toNat_cast (r : radix) : ((r.radix_val.toNat : ℕ) : ℝ) = (r.radix_val : ℝ) := by
  have h : (0 : ℤ) ≤ r.radix_val := le_of_lt (radix_gt_0 r)
  exact_mod_cast Int.toNat_of_nonneg h

theorem radix_toNat_gt_one (r : radix) : 1 < r.radix_val.toNat := by
  have := radix_gt_1 r; omega

/-- Rocq's `mag r x` on `R` (the exponent `mag_val` of the record `mag_prop`):
the unique `e` with `bpow (e - 1) ≤ |x| < bpow e`, and `0` for `x = 0`. -/
def magR (r : radix) (x : ℝ) : ℤ :=
  if x = 0 then 0 else Int.log r.radix_val.toNat |x| + 1

/-- `Raux.mag_prop`: the specification of `magR`. -/
theorem magR_spec (r : radix) (x : ℝ) (hx : x ≠ 0) :
    bpowR r (magR r x - 1) ≤ |x| ∧ |x| < bpowR r (magR r x) := by
  have hb := radix_toNat_gt_one r
  have hax : 0 < |x| := abs_pos.mpr hx
  unfold magR bpowR
  rw [if_neg hx, add_sub_cancel_right, ← radix_toNat_cast]
  exact ⟨Int.zpow_log_le_self hb hax, Int.lt_zpow_succ_log_self hb _⟩

/-- `Raux.mag_unique` on `ℝ`. -/
theorem magR_unique (r : radix) (x : ℝ) (e : ℤ)
    (h : bpowR r (e - 1) ≤ |x| ∧ |x| < bpowR r e) : magR r x = e := by
  have hx : x ≠ 0 := by
    intro h0; rw [h0, abs_zero] at h
    exact absurd h.1 (not_le.mpr (bpowR_pos r _))
  obtain ⟨h1, h2⟩ := magR_spec r x hx
  have a1 := (bpowR_lt_iff r _ _).1 (lt_of_le_of_lt h.1 h2)
  have a2 := (bpowR_lt_iff r _ _).1 (lt_of_le_of_lt h1 h.2)
  omega

/-- `Raux.mag_unique_pos` on `ℝ`. -/
theorem magR_unique_pos (r : radix) (x : ℝ) (e : ℤ)
    (h : bpowR r (e - 1) ≤ x ∧ x < bpowR r e) : magR r x = e := by
  have hx : 0 ≤ x := le_trans (bpowR_pos r _).le h.1
  exact magR_unique r x e (by rw [abs_of_nonneg hx]; exact h)

theorem magR_zero (r : radix) : magR r 0 = 0 := by simp [magR]

/-- The port's `Rabs` on `Rat` is Mathlib's absolute value. -/
theorem Rabs_eq_abs (q : ℚ) : Rabs q = |q| := by
  rcases le_total 0 q with h | h
  · rw [Rabs, Rat.abs_of_nonneg h, abs_of_nonneg h]
  · rw [Rabs, Rat.abs_of_nonpos h, abs_of_nonpos h]

/-- The real magnitude of a rational is its rational magnitude. -/
theorem magR_cast (r : radix) (q : ℚ) : magR r (q : ℝ) = mag r q := by
  by_cases hq : q = 0
  · subst hq; simp [magR_zero, mag]
  · apply magR_unique
    obtain ⟨h1, h2⟩ := mag_spec r q hq
    have e : |(q : ℝ)| = ((Rabs q : ℚ) : ℝ) := by
      rw [Rabs_eq_abs, Rat.cast_abs]
    rw [e, ← bpow_cast, ← bpow_cast]
    exact ⟨Rat.cast_le.mpr h1, Rat.cast_lt.mpr h2⟩

/-- A positive real that is not a power of the radix lies strictly between
two consecutive powers. -/
theorem magR_strict_of_irrational (r : radix) (x : ℝ) (hx : 0 < x) (hi : Irrational x) :
    bpowR r (magR r x - 1) < x ∧ x < bpowR r (magR r x) := by
  obtain ⟨h1, h2⟩ := magR_spec r x hx.ne'
  rw [abs_of_pos hx] at h1 h2
  refine ⟨lt_of_le_of_ne h1 ?_, h2⟩
  intro heq
  apply hi.ne_rat (bpow r (magR r x - 1))
  rw [bpow_cast]; exact heq.symm

end

end Flocq
end CC
