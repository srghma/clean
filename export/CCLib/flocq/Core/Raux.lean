/-
  Port of Flocq's `Core/Raux.v` (Flocq 4, as shipped with CompCert):
  missing definitions and lemmas about real numbers.

  Copyright (C) 2009-2018 Sylvie Boldo, Guillaume Melquiond (Flocq, LGPL-3.0+).

  **Reals are replaced by rationals.**  The port has no Mathlib and Lean's core
  library has no real numbers, so `R` is Lean's `Rat` throughout the Flocq
  port.  Every floating-point number, and every exact sum, difference,
  product and quotient of floating-point numbers, is rational, so the rounding
  theory of Flocq (`Generic_fmt`, `Ulp`, the IEEE-754 operations other than
  square root) can be stated and proved over `Rat` unchanged.  `IZR n` is the
  cast `(n : Rat)`, `Rabs` is `Rat.abs`, `Rmin`/`Rmax` are `min`/`max`,
  `bpow r e` is `(r : Rat) ^ e` (integer power).

  Rocq's definitions on `R` itself (`bpow`, `mag`, `cexp`, `round`, the
  rounding functions, `Bsqrt_correct`, the square-root error bounds) are
  restated over Mathlib's `ℝ` in `RauxReal.lean`, `Generic_fmtReal.lean`,
  `IEEE754/BinarySingleNaNSqrtReal.lean`, `IEEE754/BinarySqrtReal.lean` and
  `Prop/Div_sqrt_errorR.lean` (library root `CCLibReal`, which needs
  Mathlib); they agree with the rational versions on rationals.

  The square-root lemmas `sqrt_ge_0`, `sqrt_neg`, `sqrt_bpow`, `sqrt_bpow_ge`
  and `mag_sqrt` are in `RauxSqrt.lean`, over any ordered field containing
  `ℚ` with a square root.  `IZR_Zpower_pos`, `bpow_powerRZ` (with Rocq's
  `powerRZ` defined on `Rat`), `exp_le` and `bpow_exp` (over any field
  containing `ℚ` with an exponential and a logarithm, class `RatExpField`)
  are in `RauxExp.lean`.  `Rsqr_le_abs_0_alt` is stated with
  `x * x`.

  Other differences from Rocq:
  * `mag` is a function `Rat → Int` (Rocq: a record `mag_prop x` whose
    projection is the exponent); its specification is `mag_spec`, and
    `mag 0 = 0`.  It is computed exactly from the floor of `|x|` or of
    `1 / |x|` using `Zdigits`;
  * `Rcompare` is `compare` on `Rat` written out with `if`; `Rle_bool`,
    `Rlt_bool`, `Req_bool` are `decide`;
  * `Zfloor`, `Zceil` are `Rat.floor`, `Rat.ceil`;
  * the `LPO` lemmas are stated with `Classical` (they are used in Rocq to
    build `mag`, which is computable here);
  * the `bpow_simplify` tactic is not ported.
-/
import CCLib.flocq.Core.Digits

namespace CC
namespace Flocq

/-! ## Section `Rmissing` -/

/-- `Rabs`. -/
abbrev Rabs (x : Rat) : Rat := x.abs

theorem Rabs_def (x : Rat) : Rabs x = if 0 ≤ x then x else -x := by
  rcases Rat.le_total (a := 0) (b := x) with h | h
  · rw [Rabs, Rat.abs_of_nonneg h, if_pos h]
  · by_cases h0 : 0 ≤ x
    · have : x = 0 := Rat.le_antisymm h h0
      subst this; simp [Rabs, Rat.abs_zero]
    · rw [Rabs, Rat.abs_of_nonpos h, if_neg h0]

theorem rat_lt_of_le_of_lt {a b c : Rat} (h1 : a ≤ b) (h2 : b < c) : a < c := by grind

theorem rat_lt_of_lt_of_le {a b c : Rat} (h1 : a < b) (h2 : b ≤ c) : a < c := by grind

theorem Rabs_nonneg (x : Rat) : 0 ≤ Rabs x := Rat.abs_nonneg

theorem Rabs_pos_eq (x : Rat) (h : 0 ≤ x) : Rabs x = x := Rat.abs_of_nonneg h

theorem Rabs_neg_eq (x : Rat) (h : x ≤ 0) : Rabs x = -x := Rat.abs_of_nonpos h

theorem Rabs_Ropp (x : Rat) : Rabs (-x) = Rabs x := Rat.abs_neg

theorem Rle_0_minus (x y : Rat) (h : x ≤ y) : 0 ≤ y - x := by grind

theorem Rabs_eq_Rabs (x y : Rat) (h : Rabs x = Rabs y) : x = y ∨ x = -y := by
  rw [Rabs_def, Rabs_def] at h
  split at h <;> split at h <;> grind

theorem Rabs_minus_le (x y : Rat) (h0 : 0 ≤ y) (h1 : y ≤ 2 * x) : Rabs (x - y) ≤ x := by
  rw [Rabs_def]; split <;> grind

theorem Rabs_eq_R0 (x : Rat) (h : Rabs x = 0) : x = 0 := by
  rw [Rabs_def] at h; split at h <;> grind

theorem Rmult_neq_reg_r (r1 r2 r3 : Rat) (h : r2 * r1 ≠ r3 * r1) : r2 ≠ r3 := by
  intro e; subst e; exact h rfl

theorem Rmult_neq_compat_r (r1 r2 r3 : Rat) (h1 : r1 ≠ 0) (h2 : r2 ≠ r3) :
    r2 * r1 ≠ r3 * r1 := by
  intro e
  apply h2
  have := congrArg (· / r1) e
  simpa [Rat.mul_div_cancel h1] using this

theorem Rmult_min_distr_r (r r1 r2 : Rat) (h : 0 ≤ r) : min r1 r2 * r = min (r1 * r) (r2 * r) := by
  simp only [Rat.min_def]
  by_cases h1 : r1 ≤ r2
  · rw [if_pos h1, if_pos (Rat.mul_le_mul_of_nonneg_right h1 h)]
  · rw [if_neg h1]
    have h2 : r2 * r ≤ r1 * r := Rat.mul_le_mul_of_nonneg_right (by grind) h
    split
    · exact Rat.le_antisymm h2 (by assumption)
    · rfl

theorem Rmult_min_distr_l (r r1 r2 : Rat) (h : 0 ≤ r) : r * min r1 r2 = min (r * r1) (r * r2) := by
  rw [Rat.mul_comm r, Rat.mul_comm r r1, Rat.mul_comm r r2]
  exact Rmult_min_distr_r r r1 r2 h

theorem Rmin_opp (x y : Rat) : min (-x) (-y) = -(max x y) := by
  simp only [Rat.min_def, Rat.max_def]
  split <;> split <;> grind

theorem Rmax_opp (x y : Rat) : max (-x) (-y) = -(min x y) := by
  simp only [Rat.min_def, Rat.max_def]
  split <;> split <;> grind

theorem Rinv_lt (x y : Rat) (hx : 0 < x) (h : x < y) : y⁻¹ < x⁻¹ := by
  have hy : 0 < y := by grind
  have hxy : 0 < x * y := Rat.mul_pos hx hy
  apply Rat.lt_of_mul_lt_mul_right (c := x * y) _ (Rat.le_of_lt hxy)
  have e1 : y⁻¹ * (x * y) = x := by
    rw [Rat.mul_comm x y, ← Rat.mul_assoc, Rat.inv_mul_cancel y (Rat.ne_of_gt hy), Rat.one_mul]
  have e2 : x⁻¹ * (x * y) = y := by
    rw [← Rat.mul_assoc, Rat.inv_mul_cancel x (Rat.ne_of_gt hx), Rat.one_mul]
  rw [e1, e2]; exact h

theorem Rinv_le (x y : Rat) (hx : 0 < x) (h : x ≤ y) : y⁻¹ ≤ x⁻¹ := by
  rcases Rat.le_iff_lt_or_eq.mp h with h' | h'
  · exact Rat.le_of_lt (Rinv_lt x y hx h')
  · subst h'; exact Rat.le_refl

theorem Rsqr_le_abs_0_alt (x y : Rat) (h : x * x ≤ y * y) : x ≤ Rabs y := by
  apply Classical.byContradiction; intro hn
  have hy0 := Rabs_nonneg y
  have hlt : Rabs y < x := by grind
  have e : y * y = Rabs y * Rabs y := by
    rw [Rabs_def]; split
    · rfl
    · rw [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]
  have : Rabs y * Rabs y < x * x :=
    rat_lt_of_le_of_lt (Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt hlt) hy0)
      (Rat.mul_lt_mul_of_pos_right hlt (by grind))
  grind

theorem Rabs_le_inv (x y : Rat) (h : Rabs x ≤ y) : -y ≤ x ∧ x ≤ y := by
  rw [Rabs_def] at h; split at h <;> grind

theorem Rabs_ge (x y : Rat) (h : y ≤ -x ∨ x ≤ y) : x ≤ Rabs y := by
  rw [Rabs_def]; split <;> grind

theorem Rabs_ge_inv (x y : Rat) (h : x ≤ Rabs y) : y ≤ -x ∨ x ≤ y := by
  rw [Rabs_def] at h; split at h <;> grind

theorem Rabs_lt (x y : Rat) (h : -y < x ∧ x < y) : Rabs x < y := by
  rw [Rabs_def]; split <;> grind

theorem Rabs_lt_inv (x y : Rat) (h : Rabs x < y) : -y < x ∧ x < y := by
  rw [Rabs_def] at h; split at h <;> grind

theorem Rabs_gt (x y : Rat) (h : y < -x ∨ x < y) : x < Rabs y := by
  rw [Rabs_def]; split <;> grind

theorem Rabs_gt_inv (x y : Rat) (h : x < Rabs y) : y < -x ∨ x < y := by
  rw [Rabs_def] at h; split at h <;> grind

theorem rat_inv_neg (a : Rat) : (-a)⁻¹ = -(a⁻¹) := by
  by_cases h : a = 0
  · subst h; simp [Rat.inv_zero]
  · apply Rat.inv_eq_of_mul_eq_one
    rw [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg, Rat.mul_inv_cancel _ h]

theorem rat_inv_nonneg (a : Rat) (h : 0 ≤ a) : 0 ≤ a⁻¹ := by
  by_cases h0 : a = 0
  · subst h0; simp [Rat.inv_zero]
  · exact Rat.le_of_lt (Rat.inv_pos.mpr (by grind))

theorem rat_one_inv : (1 : Rat)⁻¹ = 1 := Rat.inv_eq_of_mul_eq_one (Rat.one_mul 1)

theorem Rabs_mult (a b : Rat) : Rabs (a * b) = Rabs a * Rabs b := by
  rcases Rat.le_total (a := 0) (b := a) with ha | ha <;>
  rcases Rat.le_total (a := 0) (b := b) with hb | hb
  · rw [Rabs_pos_eq _ (Rat.mul_nonneg ha hb), Rabs_pos_eq a ha, Rabs_pos_eq b hb]
  · rw [Rabs_pos_eq a ha, Rabs_neg_eq b hb, ← Rabs_Ropp, ← Rat.mul_neg,
      Rabs_pos_eq _ (Rat.mul_nonneg ha (by grind))]
  · rw [Rabs_neg_eq a ha, Rabs_pos_eq b hb, ← Rabs_Ropp, ← Rat.neg_mul,
      Rabs_pos_eq _ (Rat.mul_nonneg (by grind) hb)]
  · rw [Rabs_neg_eq a ha, Rabs_neg_eq b hb,
      show a * b = (-a) * (-b) by rw [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg],
      Rabs_pos_eq _ (Rat.mul_nonneg (by grind) (by grind))]

theorem Rabs_Rinv (a : Rat) : Rabs a⁻¹ = (Rabs a)⁻¹ := by
  rcases Rat.le_total (a := 0) (b := a) with ha | ha
  · rw [Rabs_pos_eq a ha, Rabs_pos_eq _ (rat_inv_nonneg a ha)]
  · rw [Rabs_neg_eq a ha, ← Rabs_Ropp, ← rat_inv_neg,
      Rabs_pos_eq _ (rat_inv_nonneg _ (by grind))]

theorem Rabs_IZR (m : Int) : Rabs (m : Rat) = ((m.natAbs : Int) : Rat) := by
  rcases Int.le_total 0 m with h | h
  · rw [Rabs_pos_eq _ (Rat.intCast_nonneg.mpr h), Int.natAbs_of_nonneg h]
  · rw [Rabs_neg_eq _ (Rat.intCast_nonpos.mpr h), ← Rat.intCast_neg]
    congr 1; omega

theorem rat_mul_le_mul {a b c d : Rat} (ha : 0 ≤ a) (hc : 0 ≤ c) (h1 : a ≤ b) (h2 : c ≤ d) :
    a * c ≤ b * d :=
  Rat.le_trans (Rat.mul_le_mul_of_nonneg_right h1 hc)
    (Rat.mul_le_mul_of_nonneg_left h2 (Rat.le_trans ha h1))

theorem rat_mul_lt_mul {a b c d : Rat} (ha : 0 ≤ a) (hc : 0 ≤ c) (h1 : a < b) (h2 : c < d) :
    a * c < b * d :=
  rat_lt_of_le_of_lt (Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt h1) hc)
    (Rat.mul_lt_mul_of_pos_left h2 (by grind))

/-! ## Section `IZR` -/

theorem IZR_le_lt (m n p : Int) (h : m ≤ n ∧ n < p) :
    (m : Rat) ≤ n ∧ (n : Rat) < p :=
  ⟨Rat.intCast_le_intCast.mpr h.1, Rat.intCast_lt_intCast.mpr h.2⟩

theorem le_lt_IZR (m n p : Int) (h : (m : Rat) ≤ n ∧ (n : Rat) < p) : m ≤ n ∧ n < p :=
  ⟨Rat.intCast_le_intCast.mp h.1, Rat.intCast_lt_intCast.mp h.2⟩

theorem neq_IZR (m n : Int) (h : (m : Rat) ≠ n) : m ≠ n := by
  intro e; subst e; exact h rfl

/-! ## Section `Rcompare` -/

/-- `Rcompare x y`: the comparison of two numbers. -/
def Rcompare (x y : Rat) : Ordering :=
  if x < y then .lt else if x = y then .eq else .gt

inductive Rcompare_prop (x y : Rat) : Ordering → Prop
  | Rcompare_Lt_ : x < y → Rcompare_prop x y .lt
  | Rcompare_Eq_ : x = y → Rcompare_prop x y .eq
  | Rcompare_Gt_ : y < x → Rcompare_prop x y .gt

theorem Rcompare_spec (x y : Rat) : Rcompare_prop x y (Rcompare x y) := by
  unfold Rcompare
  by_cases h1 : x < y
  · rw [if_pos h1]; exact .Rcompare_Lt_ h1
  · rw [if_neg h1]
    by_cases h2 : x = y
    · rw [if_pos h2]; exact .Rcompare_Eq_ h2
    · rw [if_neg h2]; exact .Rcompare_Gt_ (by grind)

theorem rat_trichotomy (x y : Rat) : x < y ∨ x = y ∨ y < x := by grind

theorem Rcompare_Lt (x y : Rat) (h : x < y) : Rcompare x y = .lt := by
  simp [Rcompare, h]

theorem Rcompare_Lt_inv (x y : Rat) (h : Rcompare x y = .lt) : x < y := by
  unfold Rcompare at h; split at h
  · assumption
  · split at h <;> cases h

theorem Rcompare_not_Lt (x y : Rat) (h : y ≤ x) : Rcompare x y ≠ .lt := by
  intro e; have := Rcompare_Lt_inv x y e; grind

theorem Rcompare_not_Lt_inv (x y : Rat) (h : Rcompare x y ≠ .lt) : y ≤ x := by
  apply Classical.byContradiction; intro hn
  exact h (Rcompare_Lt x y (by grind))

theorem Rcompare_Eq (x y : Rat) (h : x = y) : Rcompare x y = .eq := by
  subst h; simp [Rcompare]

theorem Rcompare_Eq_inv (x y : Rat) (h : Rcompare x y = .eq) : x = y := by
  unfold Rcompare at h; split at h
  · cases h
  · split at h
    · assumption
    · cases h

theorem Rcompare_Gt (x y : Rat) (h : y < x) : Rcompare x y = .gt := by
  unfold Rcompare
  rw [if_neg (by grind), if_neg (by grind)]

theorem Rcompare_Gt_inv (x y : Rat) (h : Rcompare x y = .gt) : y < x := by
  unfold Rcompare at h; split at h
  · cases h
  · split at h
    · cases h
    · grind

theorem Rcompare_not_Gt (x y : Rat) (h : x ≤ y) : Rcompare x y ≠ .gt := by
  intro e; have := Rcompare_Gt_inv x y e; grind

theorem Rcompare_not_Gt_inv (x y : Rat) (h : Rcompare x y ≠ .gt) : x ≤ y := by
  apply Classical.byContradiction; intro hn
  exact h (Rcompare_Gt x y (by grind))

theorem Rcompare_IZR (x y : Int) : Rcompare (x : Rat) (y : Rat) = compare x y := by
  rcases Int.lt_trichotomy x y with h | h | h
  · rw [Rcompare_Lt _ _ (Rat.intCast_lt_intCast.mpr h), Zcompare_Lt _ _ h]
  · rw [Rcompare_Eq _ _ (congrArg _ h), Zcompare_Eq _ _ h]
  · rw [Rcompare_Gt _ _ (Rat.intCast_lt_intCast.mpr h), Zcompare_Gt _ _ h]

theorem Rcompare_sym (x y : Rat) : Rcompare x y = (Rcompare y x).swap := by
  rcases rat_trichotomy y x with h | h | h
  · rw [Rcompare_Gt x y h, Rcompare_Lt y x h]; rfl
  · subst h; rw [Rcompare_Eq y y rfl]; rfl
  · rw [Rcompare_Lt x y h, Rcompare_Gt y x h]; rfl

theorem Rcompare_opp (x y : Rat) : Rcompare (-x) (-y) = Rcompare y x := by
  rcases rat_trichotomy y x with h | h | h
  · rw [Rcompare_Lt (-x) (-y) (by grind), Rcompare_Lt y x h]
  · subst h; rw [Rcompare_Eq _ _ rfl, Rcompare_Eq _ _ rfl]
  · rw [Rcompare_Gt (-x) (-y) (by grind), Rcompare_Gt y x h]

theorem Rcompare_plus_r (z x y : Rat) : Rcompare (x + z) (y + z) = Rcompare x y := by
  rcases rat_trichotomy x y with h | h | h
  · rw [Rcompare_Lt (x + z) (y + z) (by grind), Rcompare_Lt x y h]
  · subst h; rw [Rcompare_Eq _ _ rfl, Rcompare_Eq _ _ rfl]
  · rw [Rcompare_Gt (x + z) (y + z) (by grind), Rcompare_Gt x y h]

theorem Rcompare_plus_l (z x y : Rat) : Rcompare (z + x) (z + y) = Rcompare x y := by
  rcases rat_trichotomy x y with h | h | h
  · rw [Rcompare_Lt (z + x) (z + y) (by grind), Rcompare_Lt x y h]
  · subst h; rw [Rcompare_Eq _ _ rfl, Rcompare_Eq _ _ rfl]
  · rw [Rcompare_Gt (z + x) (z + y) (by grind), Rcompare_Gt x y h]

theorem Rcompare_mult_r (z x y : Rat) (hz : 0 < z) : Rcompare (x * z) (y * z) = Rcompare x y := by
  rcases rat_trichotomy x y with h | h | h
  · rw [Rcompare_Lt (x * z) (y * z) (Rat.mul_lt_mul_of_pos_right h hz), Rcompare_Lt x y h]
  · subst h; rw [Rcompare_Eq _ _ rfl, Rcompare_Eq _ _ rfl]
  · rw [Rcompare_Gt (x * z) (y * z) (Rat.mul_lt_mul_of_pos_right h hz), Rcompare_Gt x y h]

theorem Rcompare_mult_l (z x y : Rat) (hz : 0 < z) : Rcompare (z * x) (z * y) = Rcompare x y := by
  rw [Rat.mul_comm z x, Rat.mul_comm z y]; exact Rcompare_mult_r z x y hz

theorem Rcompare_middle (x d u : Rat) : Rcompare (x - d) (u - x) = Rcompare x ((d + u) / 2) := by
  rcases rat_trichotomy (x - d) (u - x) with h | h | h
  · rw [Rcompare_Lt _ _ h, Rcompare_Lt x ((d + u) / 2) (by grind)]
  · rw [Rcompare_Eq _ _ h, Rcompare_Eq x ((d + u) / 2) (by grind)]
  · rw [Rcompare_Gt _ _ h, Rcompare_Gt x ((d + u) / 2) (by grind)]

theorem Rcompare_half_l (x y : Rat) : Rcompare (x / 2) y = Rcompare x (2 * y) := by
  rcases rat_trichotomy (x / 2) y with h | h | h
  · rw [Rcompare_Lt _ _ h, Rcompare_Lt x (2 * y) (by grind)]
  · rw [Rcompare_Eq _ _ h, Rcompare_Eq x (2 * y) (by grind)]
  · rw [Rcompare_Gt _ _ h, Rcompare_Gt x (2 * y) (by grind)]

theorem Rcompare_half_r (x y : Rat) : Rcompare x (y / 2) = Rcompare (2 * x) y := by
  rcases rat_trichotomy x (y / 2) with h | h | h
  · rw [Rcompare_Lt _ _ h, Rcompare_Lt (2 * x) y (by grind)]
  · rw [Rcompare_Eq _ _ h, Rcompare_Eq (2 * x) y (by grind)]
  · rw [Rcompare_Gt _ _ h, Rcompare_Gt (2 * x) y (by grind)]

theorem Rcompare_sqr (x y : Rat) : Rcompare (x * x) (y * y) = Rcompare (Rabs x) (Rabs y) := by
  have sq : ∀ z : Rat, z * z = Rabs z * Rabs z := by
    intro z; rw [Rabs_def]; split
    · rfl
    · rw [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]
  have mono : ∀ a b : Rat, 0 ≤ a → a < b → a * a < b * b := fun a b ha hab =>
    rat_lt_of_le_of_lt (Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt hab) ha)
      (Rat.mul_lt_mul_of_pos_right hab (by grind))
  rw [sq x, sq y]
  have hx := Rabs_nonneg x
  have hy := Rabs_nonneg y
  rcases rat_trichotomy (Rabs x) (Rabs y) with h | h | h
  · rw [Rcompare_Lt _ _ h, Rcompare_Lt _ _ (mono _ _ hx h)]
  · rw [Rcompare_Eq _ _ h, Rcompare_Eq _ _ (by rw [h])]
  · rw [Rcompare_Gt _ _ h, Rcompare_Gt _ _ (mono _ _ hy h)]

theorem Rmin_compare (x y : Rat) :
    min x y = (match Rcompare x y with | .lt => x | .eq => x | .gt => y) := by
  rcases rat_trichotomy x y with h | h | h
  · rw [Rcompare_Lt _ _ h, Rat.min_def, if_pos (Rat.le_of_lt h)]
  · rw [Rcompare_Eq _ _ h, Rat.min_def, if_pos (by rw [h]; exact Rat.le_refl)]
  · rw [Rcompare_Gt _ _ h, Rat.min_def, if_neg (by grind)]

/-! ## Sections `Rle_bool`, `Rlt_bool`, `Req_bool` -/

def Rle_bool (x y : Rat) : Bool := decide (x ≤ y)
def Rlt_bool (x y : Rat) : Bool := decide (x < y)
def Req_bool (x y : Rat) : Bool := decide (x = y)

inductive Rle_bool_prop (x y : Rat) : Bool → Prop
  | Rle_bool_true_ : x ≤ y → Rle_bool_prop x y true
  | Rle_bool_false_ : y < x → Rle_bool_prop x y false

theorem Rle_bool_spec (x y : Rat) : Rle_bool_prop x y (Rle_bool x y) := by
  unfold Rle_bool
  by_cases h : x ≤ y
  · simp only [h, decide_true]; exact .Rle_bool_true_ h
  · simp only [h, decide_false]; exact .Rle_bool_false_ (by grind)

theorem Rle_bool_true (x y : Rat) (h : x ≤ y) : Rle_bool x y = true := by
  simp [Rle_bool, h]

theorem Rle_bool_false (x y : Rat) (h : y < x) : Rle_bool x y = false := by
  simp [Rle_bool]; grind

inductive Rlt_bool_prop (x y : Rat) : Bool → Prop
  | Rlt_bool_true_ : x < y → Rlt_bool_prop x y true
  | Rlt_bool_false_ : y ≤ x → Rlt_bool_prop x y false

theorem Rlt_bool_spec (x y : Rat) : Rlt_bool_prop x y (Rlt_bool x y) := by
  unfold Rlt_bool
  by_cases h : x < y
  · simp only [h, decide_true]; exact .Rlt_bool_true_ h
  · simp only [h, decide_false]; exact .Rlt_bool_false_ (by grind)

theorem negb_Rlt_bool (x y : Rat) : !(Rle_bool x y) = Rlt_bool y x := by
  simp only [Rle_bool, Rlt_bool]
  by_cases h : x ≤ y
  · simp [h]; grind
  · simp [h]; grind

theorem negb_Rle_bool (x y : Rat) : !(Rlt_bool x y) = Rle_bool y x := by
  simp only [Rle_bool, Rlt_bool]
  by_cases h : x < y
  · simp [h]; grind
  · simp [h]; grind

theorem Rlt_bool_true (x y : Rat) (h : x < y) : Rlt_bool x y = true := by
  simp [Rlt_bool, h]

theorem Rlt_bool_false (x y : Rat) (h : y ≤ x) : Rlt_bool x y = false := by
  simp [Rlt_bool]; grind

theorem Rlt_bool_opp (x y : Rat) : Rlt_bool (-x) (-y) = Rlt_bool y x := by
  simp only [Rlt_bool]; congr 1; apply propext; grind

inductive Req_bool_prop (x y : Rat) : Bool → Prop
  | Req_bool_true_ : x = y → Req_bool_prop x y true
  | Req_bool_false_ : x ≠ y → Req_bool_prop x y false

theorem Req_bool_spec (x y : Rat) : Req_bool_prop x y (Req_bool x y) := by
  unfold Req_bool
  by_cases h : x = y
  · simp only [h, decide_true]; exact .Req_bool_true_ rfl
  · simp only [h, decide_false]; exact .Req_bool_false_ h

theorem Req_bool_true (x y : Rat) (h : x = y) : Req_bool x y = true := by
  simp [Req_bool, h]

theorem Req_bool_false (x y : Rat) (h : x ≠ y) : Req_bool x y = false := by
  simp [Req_bool, h]

/-! ## Section `Floor_Ceil` -/

def Zfloor (x : Rat) : Int := x.floor

theorem Zfloor_lb (x : Rat) : ((Zfloor x : Int) : Rat) ≤ x := Rat.floor_le x

theorem Zfloor_ub (x : Rat) : x < ((Zfloor x : Int) : Rat) + 1 := by
  have := Rat.lt_floor_add_one x
  rw [Rat.intCast_add, Rat.intCast_one] at this
  exact this

theorem Zfloor_lub (n : Int) (x : Rat) (h : (n : Rat) ≤ x) : n ≤ Zfloor x :=
  Rat.le_floor_iff.mpr h

theorem Zfloor_imp (n : Int) (x : Rat) (h : (n : Rat) ≤ x ∧ x < ((n + 1 : Int) : Rat)) :
    Zfloor x = n := by
  have h1 := Zfloor_lub n x h.1
  have h2 : Zfloor x < n + 1 := Rat.floor_lt_iff.mpr h.2
  omega

theorem Zfloor_IZR (n : Int) : Zfloor (n : Rat) = n := Rat.floor_intCast n

theorem Zfloor_le (x y : Rat) (h : x ≤ y) : Zfloor x ≤ Zfloor y := Rat.floor_monotone h

def Zceil (x : Rat) : Int := -(Zfloor (-x))

theorem Zceil_ub (x : Rat) : x ≤ ((Zceil x : Int) : Rat) := by
  have := Zfloor_lb (-x)
  unfold Zceil; rw [Rat.intCast_neg]; grind

theorem Zceil_lb (x : Rat) : ((Zceil x : Int) : Rat) < x + 1 := by
  have := Zfloor_ub (-x)
  unfold Zceil; rw [Rat.intCast_neg]; grind

theorem Zceil_glb (n : Int) (x : Rat) (h : x ≤ (n : Rat)) : Zceil x ≤ n := by
  have := Zfloor_lub (-n) (-x) (by rw [Rat.intCast_neg]; grind)
  unfold Zceil; omega

theorem Zceil_imp (n : Int) (x : Rat) (h : ((n - 1 : Int) : Rat) < x ∧ x ≤ (n : Rat)) :
    Zceil x = n := by
  have := Zfloor_imp (-n) (-x) ⟨by rw [Rat.intCast_neg]; grind,
    by rw [show -n + 1 = -(n - 1) by omega, Rat.intCast_neg]; grind⟩
  unfold Zceil; omega

theorem Zceil_IZR (n : Int) : Zceil (n : Rat) = n := by
  unfold Zceil; rw [← Rat.intCast_neg, Zfloor_IZR]; omega

theorem Zceil_le (x y : Rat) (h : x ≤ y) : Zceil x ≤ Zceil y := by
  have := Zfloor_le (-y) (-x) (by grind)
  unfold Zceil; omega

theorem Zceil_floor_neq (x : Rat) (h : ((Zfloor x : Int) : Rat) ≠ x) :
    Zceil x = Zfloor x + 1 := by
  apply Zceil_imp
  have := Zfloor_lb x
  have := Zfloor_ub x
  rw [Rat.intCast_sub, Rat.intCast_add, Rat.intCast_one]
  constructor <;> grind

def Ztrunc (x : Rat) : Int := if Rlt_bool x 0 then Zceil x else Zfloor x

theorem Ztrunc_IZR (n : Int) : Ztrunc (n : Rat) = n := by
  unfold Ztrunc; split
  · exact Zceil_IZR n
  · exact Zfloor_IZR n

theorem Ztrunc_floor (x : Rat) (h : 0 ≤ x) : Ztrunc x = Zfloor x := by
  unfold Ztrunc; rw [Rlt_bool_false _ _ h]; rfl

theorem Ztrunc_ceil (x : Rat) (h : x ≤ 0) : Ztrunc x = Zceil x := by
  unfold Ztrunc
  by_cases h0 : x < 0
  · rw [Rlt_bool_true _ _ h0]; rfl
  · have : x = 0 := by grind
    subst this
    rw [Rlt_bool_false _ _ (by grind)]
    simp only [Bool.false_eq_true, if_false]
    rw [show (0 : Rat) = ((0 : Int) : Rat) from rfl, Zfloor_IZR, Zceil_IZR]

theorem Ztrunc_le (x y : Rat) (h : x ≤ y) : Ztrunc x ≤ Ztrunc y := by
  by_cases hx : 0 ≤ x
  · rw [Ztrunc_floor x hx, Ztrunc_floor y (by grind)]; exact Zfloor_le x y h
  · rw [Ztrunc_ceil x (by grind)]
    by_cases hy : 0 ≤ y
    · rw [Ztrunc_floor y hy]
      have h1 := Zceil_glb 0 x (by simp; grind)
      have h2 := Zfloor_lub 0 y (by simp; grind)
      omega
    · rw [Ztrunc_ceil y (by grind)]; exact Zceil_le x y h

theorem Ztrunc_opp (x : Rat) : Ztrunc (-x) = -(Ztrunc x) := by
  by_cases hx : 0 ≤ x
  · rw [Ztrunc_floor x hx, Ztrunc_ceil (-x) (by grind)]
    unfold Zceil; rw [Rat.neg_neg]
  · rw [Ztrunc_ceil x (by grind), Ztrunc_floor (-x) (by grind)]
    unfold Zceil; omega

theorem Ztrunc_abs (x : Rat) : Ztrunc (Rabs x) = ((Ztrunc x).natAbs : Int) := by
  by_cases hx : 0 ≤ x
  · rw [Rabs_pos_eq x hx, Ztrunc_floor x hx]
    have := Zfloor_lub 0 x (by simp; exact hx)
    omega
  · rw [Rabs_neg_eq x (by grind), Ztrunc_opp, Ztrunc_ceil x (by grind)]
    have := Zceil_glb 0 x (by simp; grind)
    omega

theorem Ztrunc_lub (n : Int) (x : Rat) (h : (n : Rat) ≤ Rabs x) :
    n ≤ ((Ztrunc x).natAbs : Int) := by
  rw [← Ztrunc_abs, Ztrunc_floor _ (Rabs_nonneg x)]
  exact Zfloor_lub n _ h

def Zaway (x : Rat) : Int := if Rlt_bool x 0 then Zfloor x else Zceil x

theorem Zaway_IZR (n : Int) : Zaway (n : Rat) = n := by
  unfold Zaway; split
  · exact Zfloor_IZR n
  · exact Zceil_IZR n

theorem Zaway_ceil (x : Rat) (h : 0 ≤ x) : Zaway x = Zceil x := by
  unfold Zaway; rw [Rlt_bool_false _ _ h]; rfl

theorem Zaway_floor (x : Rat) (h : x ≤ 0) : Zaway x = Zfloor x := by
  unfold Zaway
  by_cases h0 : x < 0
  · rw [Rlt_bool_true _ _ h0]; rfl
  · have : x = 0 := by grind
    subst this
    rw [Rlt_bool_false _ _ (by grind)]
    simp only [Bool.false_eq_true, if_false]
    rw [show (0 : Rat) = ((0 : Int) : Rat) from rfl, Zfloor_IZR, Zceil_IZR]

theorem Zaway_le (x y : Rat) (h : x ≤ y) : Zaway x ≤ Zaway y := by
  by_cases hy : 0 ≤ y
  · rw [Zaway_ceil y hy]
    by_cases hx : 0 ≤ x
    · rw [Zaway_ceil x hx]; exact Zceil_le x y h
    · rw [Zaway_floor x (by grind)]
      have h1 := Zfloor_lb x
      have h2 := Zceil_ub y
      have : Zfloor x ≤ 0 := Rat.intCast_le_intCast.mp (by simp; grind)
      have : 0 ≤ Zceil y := Rat.intCast_le_intCast.mp (by simp; grind)
      omega
  · rw [Zaway_floor y (by grind), Zaway_floor x (by grind)]; exact Zfloor_le x y h

theorem Zaway_opp (x : Rat) : Zaway (-x) = -(Zaway x) := by
  by_cases hx : 0 ≤ x
  · rw [Zaway_ceil x hx, Zaway_floor (-x) (by grind)]
    unfold Zceil; omega
  · rw [Zaway_floor x (by grind), Zaway_ceil (-x) (by grind)]
    unfold Zceil; rw [Rat.neg_neg]

theorem Zaway_abs (x : Rat) : Zaway (Rabs x) = ((Zaway x).natAbs : Int) := by
  by_cases hx : 0 ≤ x
  · rw [Rabs_pos_eq x hx, Zaway_ceil x hx]
    have h2 := Zceil_ub x
    have : 0 ≤ Zceil x := Rat.intCast_le_intCast.mp (by simp; grind)
    omega
  · rw [Rabs_neg_eq x (by grind), Zaway_opp, Zaway_floor x (by grind)]
    have h1 := Zfloor_lb x
    have : Zfloor x ≤ 0 := Rat.intCast_le_intCast.mp (by simp; grind)
    omega

theorem Rcompare_floor_ceil_middle (x : Rat) (h : ((Zfloor x : Int) : Rat) ≠ x) :
    Rcompare (x - (Zfloor x : Rat)) (1 / 2) =
      Rcompare (x - (Zfloor x : Rat)) ((Zceil x : Rat) - x) := by
  have hc := Zceil_floor_neq x h
  rw [hc, Rat.intCast_add, Rat.intCast_one]
  generalize ((Zfloor x : Int) : Rat) = f
  rcases rat_trichotomy (x - f) (1 / 2) with h | h | h
  · rw [Rcompare_Lt _ _ h, Rcompare_Lt _ _ (by grind)]
  · rw [Rcompare_Eq _ _ h, Rcompare_Eq _ _ (by grind)]
  · rw [Rcompare_Gt _ _ h, Rcompare_Gt _ _ (by grind)]

theorem Rcompare_ceil_floor_middle (x : Rat) (h : ((Zfloor x : Int) : Rat) ≠ x) :
    Rcompare ((Zceil x : Rat) - x) (1 / 2) =
      Rcompare ((Zceil x : Rat) - x) (x - (Zfloor x : Rat)) := by
  have hc := Zceil_floor_neq x h
  rw [hc, Rat.intCast_add, Rat.intCast_one]
  generalize ((Zfloor x : Int) : Rat) = f
  rcases rat_trichotomy (f + 1 - x) (1 / 2) with h | h | h
  · rw [Rcompare_Lt _ _ h, Rcompare_Lt _ _ (by grind)]
  · rw [Rcompare_Eq _ _ h, Rcompare_Eq _ _ (by grind)]
  · rw [Rcompare_Gt _ _ h, Rcompare_Gt _ _ (by grind)]

theorem Zfloor_div (x y : Int) (hy : y ≠ 0) : Zfloor ((x : Rat) / (y : Rat)) = Int.fdiv x y := by
  have pos : ∀ x y : Int, 0 < y → Zfloor ((x : Rat) / (y : Rat)) = x / y := by
    intro x y hy
    have hyq : (0 : Rat) < (y : Rat) := Rat.intCast_pos.mpr hy
    apply Zfloor_imp
    constructor
    · apply Classical.byContradiction; intro hn
      have h1 : (x : Rat) < ((x / y : Int) : Rat) * (y : Rat) :=
        (Rat.div_lt_iff hyq).mp (by grind)
      rw [← Rat.intCast_mul] at h1
      have := Int.ediv_mul_le x (Int.ne_of_gt hy)
      have := Rat.intCast_lt_intCast.mp h1
      omega
    · apply (Rat.div_lt_iff hyq).mpr
      rw [← Rat.intCast_mul, Rat.intCast_lt_intCast]
      exact Int.lt_ediv_add_one_mul_self x hy
  rcases Int.lt_or_gt_of_ne hy with hy' | hy'
  · have e : (x : Rat) / (y : Rat) = ((-x : Int) : Rat) / ((-y : Int) : Rat) := by
      rw [Rat.intCast_neg, Rat.intCast_neg, Rat.div_def, Rat.div_def]
      have : (-(y : Rat))⁻¹ = -((y : Rat)⁻¹) := by
        apply Rat.inv_eq_of_mul_eq_one
        rw [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg,
          Rat.mul_inv_cancel _ (by have := Rat.intCast_lt_intCast.mpr hy'; grind)]
      rw [this, Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]
    rw [e, pos _ _ (by omega)]
    have hy0 : -y ≠ 0 := by omega
    have := @Int.fdiv_neg x (-y) hy0
    rw [Int.neg_neg] at this
    rw [this, Int.fdiv_eq_ediv_of_nonneg _ (by omega), Int.neg_ediv, Int.sign_eq_one_of_pos (by omega)]
    split <;> omega
  · rw [pos x y hy', Int.fdiv_eq_ediv_of_nonneg _ (by omega)]

theorem Ztrunc_div (x y : Int) (hy : y ≠ 0) : Ztrunc ((x : Rat) / (y : Rat)) = Int.tdiv x y := by
  have pos : ∀ x y : Int, 0 ≤ x → 0 < y → Ztrunc ((x : Rat) / (y : Rat)) = Int.tdiv x y := by
    intro x y hx hy
    have hq : 0 ≤ (x : Rat) / (y : Rat) := by
      rw [Rat.div_def]
      exact Rat.mul_nonneg (Rat.intCast_nonneg.mpr hx)
        (rat_inv_nonneg _ (Rat.intCast_nonneg.mpr (by omega)))
    rw [Ztrunc_floor _ hq, Zfloor_div x y (by omega), Int.fdiv_eq_ediv_of_nonneg _ (by omega),
      Int.tdiv_eq_ediv_of_nonneg hx]
  have negx : ∀ x y : Int, (x : Rat) / (y : Rat) = -(((-x : Int) : Rat) / (y : Rat)) := by
    intro x y; rw [Rat.intCast_neg, Rat.div_def, Rat.div_def, Rat.neg_mul, Rat.neg_neg]
  have negy : ∀ x y : Int, (x : Rat) / (y : Rat) = -((x : Rat) / ((-y : Int) : Rat)) := by
    intro x y; rw [Rat.intCast_neg, Rat.div_def, Rat.div_def, rat_inv_neg, Rat.mul_neg, Rat.neg_neg]
  rcases Int.lt_or_gt_of_ne hy with hy' | hy'
  · rw [negy, Ztrunc_opp]
    rcases Int.le_total 0 x with hx | hx
    · rw [pos x (-y) hx (by omega), Int.tdiv_neg, Int.neg_neg]
    · rw [negx, Ztrunc_opp, pos (-x) (-y) (by omega) (by omega), Int.neg_tdiv, Int.tdiv_neg]
      omega
  · rcases Int.le_total 0 x with hx | hx
    · exact pos x y hx hy'
    · rw [negx, Ztrunc_opp, pos (-x) y (by omega) hy', Int.neg_tdiv, Int.neg_neg]

/-! ## Section `pow` -/

section pow
variable (r : radix)

theorem radix_pos : (0 : Rat) < (r.radix_val : Rat) :=
  Rat.intCast_pos.mpr (radix_gt_0 r)

/-- `bpow r e = r ^ e`. -/
def bpow (e : Int) : Rat := (r.radix_val : Rat) ^ e

theorem radix_ne_zero : (r.radix_val : Rat) ≠ 0 := Rat.ne_of_gt (radix_pos r)

theorem bpow_ge_0 (e : Int) : 0 ≤ bpow r e := Rat.zpow_nonneg (Rat.le_of_lt (radix_pos r))

theorem bpow_gt_0 (e : Int) : 0 < bpow r e := Rat.zpow_pos (radix_pos r)

theorem bpow_plus (e1 e2 : Int) : bpow r (e1 + e2) = bpow r e1 * bpow r e2 :=
  Rat.zpow_add (radix_ne_zero r) e1 e2

theorem bpow_1 : bpow r 1 = (r.radix_val : Rat) := Rat.zpow_one _

theorem bpow_plus_1 (e : Int) : bpow r (e + 1) = (r.radix_val : Rat) * bpow r e := by
  rw [bpow_plus, bpow_1, Rat.mul_comm]

theorem bpow_opp (e : Int) : bpow r (-e) = (bpow r e)⁻¹ := Rat.zpow_neg _ _

theorem IZR_Zpower_nat (e : Nat) : ((Zpower_nat r.radix_val e : Int) : Rat) = bpow r (e : Int) := by
  unfold Zpower_nat bpow
  rw [Rat.intCast_pow, Rat.zpow_natCast]

theorem IZR_Zpower (e : Int) (he : 0 ≤ e) : ((Zpower r.radix_val e : Int) : Rat) = bpow r e := by
  rw [Zpower_nonneg _ _ he]
  have := IZR_Zpower_nat r e.toNat
  unfold Zpower_nat at this
  rw [this]; congr 1; omega

theorem bpow_lt (e1 e2 : Int) (h : e1 < e2) : bpow r e1 < bpow r e2 := by
  have e : bpow r e2 = bpow r e1 * bpow r (e2 - e1) := by
    rw [← bpow_plus]; congr 1; omega
  have h1 : (1 : Rat) < bpow r (e2 - e1) := by
    rw [← IZR_Zpower r _ (by omega)]
    have := Zpower_gt_1 r (e2 - e1) (by omega)
    exact Rat.intCast_lt_intCast.mpr this
  rw [e]
  have := Rat.mul_lt_mul_of_pos_left h1 (bpow_gt_0 r e1)
  rwa [Rat.mul_one] at this

theorem lt_bpow (e1 e2 : Int) (h : bpow r e1 < bpow r e2) : e1 < e2 := by
  apply Classical.byContradiction; intro hn
  rcases Int.lt_or_eq_of_le (show e2 ≤ e1 by omega) with h' | h'
  · have := bpow_lt r e2 e1 h'; grind
  · subst h'; grind

theorem bpow_le (e1 e2 : Int) (h : e1 ≤ e2) : bpow r e1 ≤ bpow r e2 := by
  rcases Int.lt_or_eq_of_le h with h' | h'
  · exact Rat.le_of_lt (bpow_lt r e1 e2 h')
  · subst h'; exact Rat.le_refl

theorem le_bpow (e1 e2 : Int) (h : bpow r e1 ≤ bpow r e2) : e1 ≤ e2 := by
  apply Classical.byContradiction; intro hn
  have := bpow_lt r e2 e1 (by omega); grind

theorem bpow_inj (e1 e2 : Int) (h : bpow r e1 = bpow r e2) : e1 = e2 := by
  have := le_bpow r e1 e2 (by rw [h]; exact Rat.le_refl)
  have := le_bpow r e2 e1 (by rw [h]; exact Rat.le_refl)
  omega

/-- The magnitude of `x`: the unique `e` with `bpow (e - 1) ≤ |x| < bpow e` when
`x ≠ 0`; `mag 0 = 0`. -/
def mag (x : Rat) : Int :=
  if x = 0 then 0
  else if 1 ≤ Rabs x then Zdigits r (Zfloor (Rabs x))
  else 1 - Zdigits r (Zceil ((Rabs x)⁻¹) - 1)

theorem mag_spec (x : Rat) (hx : x ≠ 0) :
    bpow r (mag r x - 1) ≤ Rabs x ∧ Rabs x < bpow r (mag r x) := by
  have hax : 0 < Rabs x := by
    have := Rabs_nonneg x
    have : Rabs x ≠ 0 := fun h => hx (Rabs_eq_R0 x h)
    grind
  unfold mag
  rw [if_neg hx]
  by_cases h1 : 1 ≤ Rabs x
  · rw [if_pos h1]
    have hF1 : 1 ≤ Zfloor (Rabs x) := Zfloor_lub 1 _ (by simpa using h1)
    have hFlb := Zfloor_lb (Rabs x)
    have hFub := Zfloor_ub (Rabs x)
    generalize Zfloor (Rabs x) = F at *
    have hc := Zdigits_correct r F
    rw [Int.natAbs_of_nonneg (by omega)] at hc
    have hD := Zdigits_gt_0 r F (by omega)
    generalize Zdigits r F = D at *
    constructor
    · rw [← IZR_Zpower r _ (by omega)]
      exact Rat.le_trans (Rat.intCast_le_intCast.mpr hc.1) hFlb
    · rw [← IZR_Zpower r _ (by omega)]
      have : F + 1 ≤ Zpower r.radix_val D := by omega
      have := Rat.intCast_le_intCast.mpr this
      rw [Rat.intCast_add, Rat.intCast_one] at this
      grind
  · rw [if_neg h1]
    have hy1 : 1 < (Rabs x)⁻¹ := by
      have := Rinv_lt (Rabs x) 1 hax (by grind)
      rwa [rat_one_inv] at this
    have hCub := Zceil_ub ((Rabs x)⁻¹)
    have hClb := Zceil_lb ((Rabs x)⁻¹)
    have hC2 : 2 ≤ Zceil ((Rabs x)⁻¹) := by
      have : ((1 : Int) : Rat) < ((Zceil ((Rabs x)⁻¹) : Int) : Rat) := by
        rw [Rat.intCast_one]; grind
      have := Rat.intCast_lt_intCast.mp this
      omega
    generalize hy : (Rabs x)⁻¹ = y at *
    generalize Zceil y = C at *
    have hc := Zdigits_correct r (C - 1)
    rw [Int.natAbs_of_nonneg (by omega)] at hc
    have hk := Zdigits_gt_0 r (C - 1) (by omega)
    generalize Zdigits r (C - 1) = k at *
    have hx' : Rabs x = y⁻¹ := by rw [← hy, Rat.inv_inv]
    rw [hx']
    have hy0 : 0 < y := by grind
    constructor
    · rw [show 1 - k - 1 = -k by omega, bpow_opp]
      apply Rinv_le _ _ hy0
      rw [← IZR_Zpower r _ (by omega)]
      have : C ≤ Zpower r.radix_val k := by omega
      exact Rat.le_trans hCub (Rat.intCast_le_intCast.mpr this)
    · rw [show 1 - k = -(k - 1) by omega, bpow_opp]
      apply Rinv_lt _ _ (bpow_gt_0 r _)
      rw [← IZR_Zpower r _ (by omega)]
      have h3 := Rat.intCast_le_intCast.mpr hc.1
      rw [Rat.intCast_sub, Rat.intCast_one] at h3
      grind

theorem bpow_lt_bpow (e1 e2 : Int) (h : bpow r (e1 - 1) < bpow r e2) : e1 ≤ e2 := by
  have := lt_bpow r _ _ h; omega

theorem bpow_unique (x : Rat) (e1 e2 : Int)
    (h1 : bpow r (e1 - 1) ≤ x ∧ x < bpow r e1)
    (h2 : bpow r (e2 - 1) ≤ x ∧ x < bpow r e2) : e1 = e2 := by
  have := bpow_lt_bpow r e1 e2 (by grind)
  have := bpow_lt_bpow r e2 e1 (by grind)
  omega

theorem mag_unique (x : Rat) (e : Int) (h : bpow r (e - 1) ≤ Rabs x ∧ Rabs x < bpow r e) :
    mag r x = e := by
  have hx : x ≠ 0 := by
    intro h0; subst h0
    have := bpow_gt_0 r (e - 1)
    simp [Rabs, Rat.abs_zero] at h; grind
  exact bpow_unique r (Rabs x) _ _ (mag_spec r x hx) h

theorem mag_opp (x : Rat) : mag r (-x) = mag r x := by
  unfold mag
  rw [Rabs_Ropp]
  by_cases hx : x = 0
  · subst hx; simp
  · have : -x ≠ 0 := by grind
    rw [if_neg hx, if_neg this]

theorem mag_abs (x : Rat) : mag r (Rabs x) = mag r x := by
  unfold mag
  have e : Rabs (Rabs x) = Rabs x := Rabs_pos_eq _ (Rabs_nonneg x)
  rw [e]
  by_cases hx : x = 0
  · subst hx; simp [Rabs, Rat.abs_zero]
  · have : Rabs x ≠ 0 := fun h => hx (Rabs_eq_R0 x h)
    rw [if_neg hx, if_neg this]

theorem mag_unique_pos (x : Rat) (e : Int) (h : bpow r (e - 1) ≤ x ∧ x < bpow r e) :
    mag r x = e := by
  apply mag_unique
  have := bpow_gt_0 r (e - 1)
  rw [Rabs_pos_eq x (by grind)]; exact h

theorem mag_le_abs (x y : Rat) (hx : x ≠ 0) (h : Rabs x ≤ Rabs y) : mag r x ≤ mag r y := by
  have hy : y ≠ 0 := by
    intro h0; subst h0
    simp [Rabs, Rat.abs_zero] at h
    exact hx (Rabs_eq_R0 x (Rat.le_antisymm h (Rabs_nonneg x)))
  have h1 := mag_spec r x hx
  have h2 := mag_spec r y hy
  exact bpow_lt_bpow r _ _ (by grind)

theorem mag_le (x y : Rat) (hx : 0 < x) (h : x ≤ y) : mag r x ≤ mag r y := by
  apply mag_le_abs r x y (by grind)
  rw [Rabs_pos_eq x (by grind), Rabs_pos_eq y (by grind)]; exact h

theorem lt_mag (x y : Rat) (hy : 0 < y) (h : mag r x < mag r y) : x < y := by
  by_cases hx : x ≤ 0
  · grind
  have hx0 : x ≠ 0 := by grind
  have h1 := mag_spec r x hx0
  have h2 := mag_spec r y (by grind)
  have h3 := bpow_le r (mag r x) (mag r y - 1) (by omega)
  rw [Rabs_pos_eq x (by grind)] at h1
  rw [Rabs_pos_eq y (by grind)] at h2
  grind

theorem mag_bpow (e : Int) : mag r (bpow r e) = e + 1 := by
  apply mag_unique_pos
  rw [Int.add_sub_cancel]
  exact ⟨Rat.le_refl, bpow_lt r _ _ (by omega)⟩

theorem mag_mult_bpow (x : Rat) (e : Int) (hx : x ≠ 0) : mag r (x * bpow r e) = mag r x + e := by
  apply mag_unique
  have h := mag_spec r x hx
  rw [Rabs_mult, Rabs_pos_eq _ (bpow_ge_0 r e), show mag r x + e - 1 = (mag r x - 1) + e by omega,
    bpow_plus, bpow_plus]
  have hb := bpow_gt_0 r e
  exact ⟨Rat.mul_le_mul_of_nonneg_right h.1 (Rat.le_of_lt hb),
    Rat.mul_lt_mul_of_pos_right h.2 hb⟩

theorem mag_le_bpow (x : Rat) (e : Int) (hx : x ≠ 0) (h : Rabs x < bpow r e) : mag r x ≤ e := by
  have := mag_spec r x hx
  exact bpow_lt_bpow r _ _ (by grind)

theorem mag_gt_bpow (x : Rat) (e : Int) (h : bpow r e ≤ Rabs x) : e < mag r x := by
  have hx : x ≠ 0 := by
    intro h0; subst h0
    have := bpow_gt_0 r e
    simp [Rabs, Rat.abs_zero] at h; grind
  have := mag_spec r x hx
  have := lt_bpow r e (mag r x) (by grind)
  exact this

theorem mag_ge_bpow (x : Rat) (e : Int) (h : bpow r (e - 1) ≤ Rabs x) : e ≤ mag r x := by
  have := mag_gt_bpow r x (e - 1) h; omega

theorem bpow_mag_gt (x : Rat) : Rabs x < bpow r (mag r x) := by
  by_cases hx : x = 0
  · subst hx; simp [Rabs, Rat.abs_zero]; exact bpow_gt_0 r _
  · exact (mag_spec r x hx).2

theorem bpow_mag_le (x : Rat) (hx : x ≠ 0) : bpow r (mag r x - 1) ≤ Rabs x :=
  (mag_spec r x hx).1

theorem mag_le_Zpower (m e : Int) (hm : m ≠ 0) (h : (m.natAbs : Int) < Zpower r.radix_val e) :
    mag r (m : Rat) ≤ e := by
  have he : 0 ≤ e := by
    apply Classical.byContradiction; intro hn
    rw [Zpower_neg _ _ (by omega)] at h; omega
  apply mag_le_bpow r _ _ (by simpa using hm)
  rw [Rabs_IZR, ← IZR_Zpower r _ he]
  exact Rat.intCast_lt_intCast.mpr h

theorem mag_gt_Zpower (m e : Int) (hm : m ≠ 0) (h : Zpower r.radix_val e ≤ (m.natAbs : Int)) :
    e < mag r (m : Rat) := by
  rcases Int.lt_or_le e 0 with he | he
  · have := mag_gt_bpow r (m : Rat) 0 (by
      rw [Rabs_IZR, bpow, Rat.zpow_zero]
      have : (1 : Int) ≤ (m.natAbs : Int) := by omega
      have := Rat.intCast_le_intCast.mpr this
      simpa using this)
    omega
  · apply mag_gt_bpow
    rw [Rabs_IZR, ← IZR_Zpower r _ he]
    exact Rat.intCast_le_intCast.mpr h

theorem mag_mult (x y : Rat) (hx : x ≠ 0) (hy : y ≠ 0) :
    mag r x + mag r y - 1 ≤ mag r (x * y) ∧ mag r (x * y) ≤ mag r x + mag r y := by
  have h1 := mag_spec r x hx
  have h2 := mag_spec r y hy
  have hxy : x * y ≠ 0 := by
    intro h; rcases Rat.mul_eq_zero.mp h with h | h <;> contradiction
  constructor
  · apply mag_ge_bpow
    rw [Rabs_mult, show mag r x + mag r y - 1 - 1 = (mag r x - 1) + (mag r y - 1) by omega,
      bpow_plus]
    exact rat_mul_le_mul (bpow_ge_0 r _) (bpow_ge_0 r _) h1.1 h2.1
  · apply mag_le_bpow r _ _ hxy
    rw [Rabs_mult, bpow_plus]
    exact rat_mul_lt_mul (Rabs_nonneg x) (Rabs_nonneg y) h1.2 h2.2

theorem mag_plus (x y : Rat) (hy : 0 < y) (h : y ≤ x) :
    mag r x ≤ mag r (x + y) ∧ mag r (x + y) ≤ mag r x + 1 := by
  constructor
  · exact mag_le r x (x + y) (by grind) (by grind)
  · apply mag_le_bpow r _ _ (by grind)
    have h1 := mag_spec r x (by grind)
    rw [Rabs_pos_eq x (by grind)] at h1
    rw [Rabs_pos_eq _ (by grind), bpow_plus_1]
    have hr : (2 : Rat) ≤ (r.radix_val : Rat) := by
      have := Rat.intCast_le_intCast.mpr (radix_ge_2 r); simpa using this
    have := Rat.mul_le_mul_of_nonneg_right hr (bpow_ge_0 r (mag r x))
    grind

theorem mag_minus (x y : Rat) (hy : 0 < y) (h : y < x) : mag r (x - y) ≤ mag r x := by
  exact mag_le r (x - y) x (by grind) (by grind)

theorem mag_minus_lb (x y : Rat) (hx : 0 < x) (hy : 0 < y) (h : mag r y ≤ mag r x - 2) :
    mag r x - 1 ≤ mag r (x - y) := by
  apply mag_ge_bpow
  have h1 := mag_spec r x (by grind)
  have h2 := bpow_mag_gt r y
  rw [Rabs_pos_eq x (by grind)] at h1
  rw [Rabs_pos_eq y (by grind)] at h2
  have h3 := bpow_le r (mag r y) (mag r x - 2) h
  have e : bpow r (mag r x - 1) = (r.radix_val : Rat) * bpow r (mag r x - 2) := by
    rw [← bpow_plus_1]; congr 1; omega
  have hr : (2 : Rat) ≤ (r.radix_val : Rat) := by
    have := Rat.intCast_le_intCast.mpr (radix_ge_2 r); simpa using this
  have := Rat.mul_le_mul_of_nonneg_right hr (bpow_ge_0 r (mag r x - 2))
  rw [Rabs_pos_eq _ (by grind), show mag r x - 1 - 1 = mag r x - 2 by omega]
  grind

theorem mag_plus_ge (x y : Rat) (hx : x ≠ 0) (h : mag r y ≤ mag r x - 2) :
    mag r x - 1 ≤ mag r (x + y) := by
  apply mag_ge_bpow
  have h1 := mag_spec r x hx
  have h2 := bpow_mag_gt r y
  have h3 := bpow_le r (mag r y) (mag r x - 2) h
  have e : bpow r (mag r x - 1) = (r.radix_val : Rat) * bpow r (mag r x - 2) := by
    rw [← bpow_plus_1]; congr 1; omega
  have hr : (2 : Rat) ≤ (r.radix_val : Rat) := by
    have := Rat.intCast_le_intCast.mpr (radix_ge_2 r); simpa using this
  have := Rat.mul_le_mul_of_nonneg_right hr (bpow_ge_0 r (mag r x - 2))
  rw [show mag r x - 1 - 1 = mag r x - 2 by omega]
  have tri : Rabs x - Rabs y ≤ Rabs (x + y) := by
    rw [Rabs_def x, Rabs_def y, Rabs_def (x + y)]
    split <;> split <;> split <;> grind
  grind

theorem mag_div (x y : Rat) (hx : x ≠ 0) (hy : y ≠ 0) :
    mag r x - mag r y ≤ mag r (x / y) ∧ mag r (x / y) ≤ mag r x - mag r y + 1 := by
  have h1 := mag_spec r x hx
  have h2 := mag_spec r y hy
  have hay : 0 < Rabs y := by
    have := Rabs_nonneg y
    have : Rabs y ≠ 0 := fun h => hy (Rabs_eq_R0 y h)
    grind
  have hxy : x / y ≠ 0 := by
    rw [Rat.div_def]; intro h
    rcases Rat.mul_eq_zero.mp h with h | h
    · exact hx h
    · have := Rat.mul_inv_cancel y hy; rw [h, Rat.mul_zero] at this; exact absurd this (by decide)
  have hinv1 : (Rabs y)⁻¹ ≤ bpow r (1 - mag r y) := by
    rw [show 1 - mag r y = -(mag r y - 1) by omega, bpow_opp]
    exact Rinv_le _ _ (bpow_gt_0 r _) h2.1
  have hinv2 : bpow r (-mag r y) < (Rabs y)⁻¹ := by
    rw [bpow_opp]; exact Rinv_lt _ _ hay h2.2
  have habs : Rabs (x / y) = Rabs x * (Rabs y)⁻¹ := by
    rw [Rat.div_def, Rabs_mult, Rabs_Rinv]
  constructor
  · apply mag_ge_bpow
    rw [habs, show mag r x - mag r y - 1 = (mag r x - 1) + (-mag r y) by omega, bpow_plus]
    exact rat_mul_le_mul (bpow_ge_0 r _) (bpow_ge_0 r _) h1.1 (Rat.le_of_lt hinv2)
  · apply mag_le_bpow r _ _ hxy
    rw [habs, show mag r x - mag r y + 1 = mag r x + (1 - mag r y) by omega, bpow_plus]
    exact rat_lt_of_le_of_lt (Rat.mul_le_mul_of_nonneg_left hinv1 (Rabs_nonneg x))
      (Rat.mul_lt_mul_of_pos_right h1.2 (bpow_gt_0 r _))

theorem mag_1 : mag r 1 = 1 := by
  have := mag_bpow r 0
  rwa [bpow, Rat.zpow_zero] at this

end pow

/-! ## Section `Bool` -/

theorem eqb_sym (x y : Bool) : (x == y) = (y == x) := by cases x <;> cases y <;> rfl

theorem eqb_false (x y : Bool) (h : x = !y) : (x == y) = false := by
  subst h; cases y <;> rfl

theorem eqb_true (x y : Bool) (h : x = y) : (x == y) = true := by
  subst h; cases x <;> rfl

/-! ## Section `cond_Ropp` -/

def cond_Ropp (b : Bool) (m : Rat) : Rat := if b then -m else m

theorem IZR_cond_Zopp (b : Bool) (m : Int) :
    ((cond_Zopp b m : Int) : Rat) = cond_Ropp b (m : Rat) := by
  cases b
  · rfl
  · simp [cond_Zopp, cond_Ropp, Rat.intCast_neg]

theorem abs_cond_Ropp (b : Bool) (m : Rat) : Rabs (cond_Ropp b m) = Rabs m := by
  cases b
  · rfl
  · exact Rabs_Ropp m

theorem cond_Ropp_Rlt_bool (m : Rat) : cond_Ropp (Rlt_bool m 0) m = Rabs m := by
  unfold cond_Ropp Rlt_bool
  by_cases h : m < 0
  · simp only [h, decide_true, if_true]; rw [Rabs_neg_eq m (by grind)]
  · simp only [h, decide_false, Bool.false_eq_true, if_false]; rw [Rabs_pos_eq m (by grind)]

theorem Rlt_bool_cond_Ropp (x : Rat) (sx : Bool) (hx : 0 < x) :
    Rlt_bool (cond_Ropp sx x) 0 = sx := by
  cases sx
  · exact Rlt_bool_false _ _ (Rat.le_of_lt hx)
  · exact Rlt_bool_true _ _ (by simp [cond_Ropp]; grind)

theorem cond_Ropp_involutive (b : Bool) (x : Rat) : cond_Ropp b (cond_Ropp b x) = x := by
  cases b
  · rfl
  · simp [cond_Ropp, Rat.neg_neg]

theorem cond_Ropp_inj (b : Bool) (x y : Rat) (h : cond_Ropp b x = cond_Ropp b y) : x = y := by
  rw [← cond_Ropp_involutive b x, h, cond_Ropp_involutive]

theorem cond_Ropp_mult_l (b : Bool) (x y : Rat) : cond_Ropp b (x * y) = cond_Ropp b x * y := by
  cases b
  · rfl
  · simp [cond_Ropp, Rat.neg_mul]

theorem cond_Ropp_mult_r (b : Bool) (x y : Rat) : cond_Ropp b (x * y) = x * cond_Ropp b y := by
  cases b
  · rfl
  · simp [cond_Ropp, Rat.mul_neg]

theorem cond_Ropp_plus (b : Bool) (x y : Rat) :
    cond_Ropp b (x + y) = cond_Ropp b x + cond_Ropp b y := by
  cases b
  · rfl
  · simp [cond_Ropp, Rat.neg_add]

/-! ## `LPO` -/

theorem LPO_min (P : Nat → Prop) :
    (∃ n, P n ∧ ∀ i, i < n → ¬ P i) ∨ (∀ n, ¬ P n) := by
  by_cases h : ∃ n, P n ∧ ∀ i, i < n → ¬ P i
  · exact Or.inl h
  · right
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih => exact fun hn => h ⟨n, hn, fun i hi hpi => ih i hi hpi⟩

theorem LPO (P : Nat → Prop) : (∃ n, P n) ∨ (∀ n, ¬ P n) := by
  by_cases h : ∃ n, P n
  · exact Or.inl h
  · exact Or.inr fun n hn => h ⟨n, hn⟩

theorem LPO_Z (P : Int → Prop) : (∃ n, P n) ∨ (∀ n, ¬ P n) := by
  by_cases h : ∃ n, P n
  · exact Or.inl h
  · exact Or.inr fun n hn => h ⟨n, hn⟩

end Flocq
end CC
