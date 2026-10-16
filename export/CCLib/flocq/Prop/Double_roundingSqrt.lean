/-
  Port of Flocq's `Prop/Double_rounding.v` (Flocq 4, as shipped with CompCert),
  the lemma `round_round_mid_cases` and the square-root sections
  `Double_round_sqrt`, `Double_round_sqrt_FLX`, `Double_round_sqrt_FLT`,
  `Double_round_sqrt_FTZ`, `Double_round_sqrt_radix_ge_4` and its `FLX`/`FLT`/
  `FTZ` instances.

  Copyright (C) 2014-2018 Sylvie Boldo, Guillaume Melquiond, Pierre Roux
  (Flocq, LGPL-3.0+).

  Conventions as in `Double_rounding.lean`.

  **Square roots without real numbers.**  The Flocq port uses `Rat` for `R`,
  so `sqrt x` is in general not available.  Rocq's conclusion
  `round_round_eq fexp1 fexp2 choice1 choice2 (sqrt x)`, i.e.
  `round1 (round2 (sqrt x)) = round1 (sqrt x)`, is stated here with the
  predicate `is_round_sqrt` of `IEEE754/BinarySingleNaNSqrt.lean` (the same
  device that file uses for `Bsqrt`): for every `r2` with
  `is_round_sqrt beta fexp2 (Znearest choice2) x r2` (`r2` is "the" rounding of
  `√x` in format `fexp2`) and every `r1` with
  `is_round_sqrt beta fexp1 (Znearest choice1) x r1`,
  `round beta fexp1 (Znearest choice1) r2 = r1`.  The proof only uses the
  `nonpos`, `lower` and `upper` fields of `is_round_sqrt` (rounding is
  monotone), so it does not rely on `is_round_sqrt` determining `r`
  uniquely.  When `√x` is rational
  the Rocq statement itself is recovered (`round_round_sqrt_sq`, …): for
  `0 ≤ y`, `round_round_eq … y` holds whenever `y * y` is in format `fexp1`.

  The proof differs from Rocq's in where the rational stand-ins come from.
  Rocq's `round_round_sqrt_aux` shows that `√x` is not within half an ulp
  (of `fexp2`) of the midpoint `a + u1 / 2` between `a = round_DN1 (√x)` and
  its successor; its argument only uses `a * a ≤ x < (a + u1) * (a + u1)` and
  is reproduced in `round_round_sqrt_not_near_mid`, which also covers
  `round_round_sqrt_radix_ge_4_aux` (the two differ only in a constant).  Here `a` is found
  directly as the largest multiple `m * u1` with `(m * u1)² ≤ x`
  (`exists_sqrt_floor`).  Then, instead of applying
  `round_round_lt_mid_further_place`/`round_round_gt_mid_further_place` to
  `√x`, they are applied to a rational point between `√x` and the forbidden
  interval, and the result is transferred to `√x` through the monotonicity
  fields of `is_round_sqrt`.  The exponent `mag (sqrt x)` is
  `(mag x + 1) / 2` (Flocq's `mag_sqrt`).

  `round_round_sqrt_core` and `round_round_sqrt_gen` are the common part of
  `round_round_sqrt` and `round_round_sqrt_radix_ge_4`; they, and
  `exists_sqrt_floor`, `generic_format_of_bmult_le_bpow`, `is_round_sqrt_sq`,
  `round_DN_of_between`, `round_UP_of_between`, `int_lt_of_mul_lt`,
  `mul_le_of_int_le`, `Zpower_mul_bpow` and `round_round_sqrt_not_near_mid`,
  are auxiliary (not in the Rocq file).  The `*_sq` corollaries are not in the
  Rocq file either.
-/
import CCLib.flocq.Prop.Double_roundingDiv
import CCLib.flocq.IEEE754.BinarySingleNaNSqrt

namespace CC
namespace Flocq

section Double_round_sqrt

variable (beta : radix)

/-! ### Auxiliary lemmas (not in the Rocq file) -/

/-- The integer square root, scaled by `u`: the largest `m` with
`(m * u)² ≤ x`. -/
theorem exists_sqrt_floor (u x : Rat) (Px : 0 ≤ x) (N : Int) (PN : 0 ≤ N)
    (hN : x < ((N : Rat) * u) * ((N : Rat) * u)) :
    ∃ m : Int, 0 ≤ m ∧ ((m : Rat) * u) * ((m : Rat) * u) ≤ x ∧
      x < (((m + 1 : Int) : Rat) * u) * (((m + 1 : Int) : Rat) * u) := by
  have key : ∀ n : Nat, x < (((n : Int) : Rat) * u) * (((n : Int) : Rat) * u) →
      ∃ m : Int, 0 ≤ m ∧ ((m : Rat) * u) * ((m : Rat) * u) ≤ x ∧
        x < (((m + 1 : Int) : Rat) * u) * (((m + 1 : Int) : Rat) * u) := by
    intro n
    induction n with
    | zero => intro h; simp at h; grind
    | succ n ih =>
      intro h
      by_cases h' : x < (((n : Int) : Rat) * u) * (((n : Int) : Rat) * u)
      · exact ih h'
      · exact ⟨n, by omega, by grind, by simpa using h⟩
  obtain ⟨n, rfl⟩ : ∃ n : Nat, N = n := ⟨N.toNat, by omega⟩
  exact key n hN

/-- A multiple of `bpow c` between `bpow (e - 1)` and `bpow e` is in a format
whose exponent at `e` is at most `c`. -/
theorem generic_format_of_bmult_le_bpow (fexp : Int → Int) [Valid_exp fexp] (x : Rat) (e c : Int)
    (hx : bpow beta (e - 1) ≤ x ∧ x ≤ bpow beta e) (hm : bmult beta c x) (hc : fexp e ≤ c)
    (he : fexp e < e) : generic_format beta fexp x := by
  rcases (show x < bpow beta e ∨ x = bpow beta e by grind) with h | h
  · have hmag : mag beta x = e := mag_unique_pos beta x e ⟨hx.1, h⟩
    apply generic_format_of_bmult beta fexp hm
    intro _; unfold cexp; rw [hmag]; exact hc
  · rw [h]
    exact generic_format_bpow beta fexp e ((Valid_exp.valid_exp (fexp := fexp) e).1 he)

/-- `round y` is the rounding of the square root of `y * y`. -/
theorem is_round_sqrt_sq (fexp : Int → Int) [Valid_exp fexp] (rnd : Rat → Int) [Valid_rnd rnd]
    (y : Rat) (Py : 0 ≤ y) : is_round_sqrt beta fexp rnd (y * y) (round beta fexp rnd y) where
  nonpos h := by
    rw [mul_self_eq_zero_of_nonpos (y := y) Rat.le_refl h, round_0]
  exact z Pz hz := by
    congr 1
    rcases rat_trichotomy z y with h | h | h
    · have := Rat.mul_lt_mul_of_pos_left h (show 0 < y by grind)
      have := Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt h) Pz
      grind
    · exact h.symm
    · have := Rat.mul_lt_mul_of_pos_left h (show 0 < z by grind)
      have := Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt h) Py
      grind
  lower a Pa h := by
    apply round_le
    apply Classical.byContradiction; intro hn
    have hlt : y < a := by grind
    have := Rat.mul_lt_mul_of_pos_left hlt (show 0 < a by grind)
    have := Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt hlt) Py
    grind
  upper b Pb h := by
    apply round_le
    apply Classical.byContradiction; intro hn
    have hlt : b < y := by grind
    have := Rat.mul_lt_mul_of_pos_left hlt (show 0 < y by grind)
    have := Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt hlt) Pb
    grind

theorem round_DN_of_between (fexp : Int → Int) (y : Rat) (m c : Int) (hc : cexp beta fexp y = c)
    (h : (m : Rat) * bpow beta c ≤ y ∧ y < ((m + 1 : Int) : Rat) * bpow beta c) :
    round beta fexp Zfloor y = (m : Rat) * bpow beta c := by
  rw [round_DN_eq_floor, hc]
  congr 2
  apply Zfloor_imp
  unfold scaled_mantissa; rw [hc]
  have hp := bpow_gt_0 beta (-c)
  have k := bpow_mul_bpow_neg beta c
  have h1 := Rat.mul_le_mul_of_nonneg_right h.1 (Rat.le_of_lt hp)
  have h2 := Rat.mul_lt_mul_of_pos_right h.2 hp
  rw [Rat.mul_assoc, k, Rat.mul_one] at h1 h2
  exact ⟨h1, h2⟩

theorem round_UP_of_between (fexp : Int → Int) (y : Rat) (n c : Int) (hc : cexp beta fexp y = c)
    (h : ((n - 1 : Int) : Rat) * bpow beta c < y ∧ y ≤ (n : Rat) * bpow beta c) :
    round beta fexp Zceil y = (n : Rat) * bpow beta c := by
  rw [round_UP_eq_ceil, hc]
  congr 2
  apply Zceil_imp
  unfold scaled_mantissa; rw [hc]
  have hp := bpow_gt_0 beta (-c)
  have k := bpow_mul_bpow_neg beta c
  have h1 := Rat.mul_lt_mul_of_pos_right h.1 hp
  have h2 := Rat.mul_le_mul_of_nonneg_right h.2 (Rat.le_of_lt hp)
  rw [Rat.mul_assoc, k, Rat.mul_one] at h1 h2
  exact ⟨h1, h2⟩

theorem int_lt_of_mul_lt {p q : Int} {u : Rat} (Pu : 0 < u) (h : (p : Rat) * u < (q : Rat) * u) :
    p < q :=
  Rat.intCast_lt_intCast.mp (Rat.lt_of_mul_lt_mul_right h (Rat.le_of_lt Pu))

theorem mul_le_of_int_le {p q : Int} {u : Rat} (Pu : 0 < u) (h : p ≤ q) :
    (p : Rat) * u ≤ (q : Rat) * u :=
  Rat.mul_le_mul_of_nonneg_right (Rat.intCast_le_intCast.mpr h) (Rat.le_of_lt Pu)

theorem Zpower_mul_bpow (c e : Int) (h : c ≤ e) :
    ((Zpower beta.radix_val (e - c) : Int) : Rat) * bpow beta c = bpow beta e := by
  rw [IZR_Zpower beta _ (by omega), ← bpow_plus, Int.sub_add_cancel]

/-- The heart of Rocq's `round_round_sqrt_aux`: if `x` is in format `fexp1`
and `a = m * u1` is the largest multiple of `u1` below `√x`, then `√x` is not
within `u2 / 2` of the midpoint `a + u1 / 2`. -/
theorem round_round_sqrt_not_near_mid (fexp1 : Int → Int) (x : Rat) (e c1 c2 m : Int)
    (Fx : generic_format beta fexp1 x) (Hf1 : 2 * c1 ≤ fexp1 (mag beta x))
    (H21 : c2 < c1)
    (Ha : ((m + 1 : Int) : Rat) * bpow beta c1 ≤ bpow beta e)
    (Hu : 4 * (bpow beta c2 * bpow beta e) ≤ bpow beta c1 * bpow beta c1) :
    ¬ ((((m : Rat) * bpow beta c1 + 1 / 2 * (bpow beta c1 - bpow beta c2)) *
          ((m : Rat) * bpow beta c1 + 1 / 2 * (bpow beta c1 - bpow beta c2)) ≤ x) ∧
       x ≤ ((m : Rat) * bpow beta c1 + 1 / 2 * (bpow beta c1 + bpow beta c2)) *
          ((m : Rat) * bpow beta c1 + 1 / 2 * (bpow beta c1 + bpow beta c2))) := by
  rintro ⟨hl, hr⟩
  have hu1 := bpow_gt_0 beta c1
  have hu2 := bpow_gt_0 beta c2
  have h21 := bpow_lt beta c2 c1 H21
  obtain ⟨X, hX⟩ := bmult_of_le beta Hf1 (bmult_generic beta fexp1 Fx)
  rw [show 2 * c1 = c1 + c1 by omega, bpow_plus] at hX
  rw [Rat.intCast_add, Rat.intCast_one] at Ha
  have h1 : bpow beta c2 * ((m : Rat) * bpow beta c1 + 1 / 2 * bpow beta c1) <
      bpow beta c2 * bpow beta e := Rat.mul_lt_mul_of_pos_left (by grind) hu2
  have h2a := Rat.mul_lt_mul_of_pos_left h21 hu2
  have h2b := Rat.mul_lt_mul_of_pos_right h21 hu1
  have h22 := Rat.mul_pos hu2 hu2
  have P : (m : Rat) * bpow beta c1 * ((m : Rat) * bpow beta c1) +
      (m : Rat) * bpow beta c1 * bpow beta c1 < x := by grind
  have Q : x < (m : Rat) * bpow beta c1 * ((m : Rat) * bpow beta c1) +
      (m : Rat) * bpow beta c1 * bpow beta c1 + bpow beta c1 * bpow beta c1 := by grind
  have hpos : 0 ≤ bpow beta c1 * bpow beta c1 := Rat.le_of_lt (Rat.mul_pos hu1 hu1)
  have Q' : (X : Rat) < ((m * m + m + 1 : Int) : Rat) := by
    apply Rat.lt_of_mul_lt_mul_right _ hpos
    push_cast
    grind
  have P' : ((m * m + m : Int) : Rat) < (X : Rat) := by
    apply Rat.lt_of_mul_lt_mul_right _ hpos
    push_cast
    grind
  rw [Rat.intCast_lt_intCast] at P' Q'
  omega

/-- Common part of `round_round_sqrt` and `round_round_sqrt_radix_ge_4`:
`e` plays the role of `mag (sqrt x)`. -/
theorem round_round_sqrt_core (fexp1 fexp2 : Int → Int) [Valid_exp fexp1] [Valid_exp fexp2]
    (choice1 choice2 : Int → Bool) (x : Rat) (e : Int)
    (Px : 0 < x) (Fx : generic_format beta fexp1 x)
    (Hx : bpow beta (2 * e - 2) ≤ x ∧ x < bpow beta (2 * e))
    (He1 : fexp1 e < e) (H21 : fexp2 e < fexp1 e) (Hf1 : 2 * fexp1 e ≤ fexp1 (mag beta x))
    (Hu : 4 * (bpow beta (fexp2 e) * bpow beta e) ≤ bpow beta (fexp1 e) * bpow beta (fexp1 e))
    (r1 r2 : Rat)
    (H1 : is_round_sqrt beta fexp1 (Znearest choice1) x r1)
    (H2 : is_round_sqrt beta fexp2 (Znearest choice2) x r2) :
    round beta fexp1 (Znearest choice1) r2 = r1 := by
  -- names for the two ulps
  obtain ⟨c1, hc1⟩ : ∃ c1, fexp1 e = c1 := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ c2, fexp2 e = c2 := ⟨_, rfl⟩
  rw [hc1] at He1 H21 Hf1 Hu
  rw [hc2] at H21 Hu
  have hu1 := bpow_gt_0 beta c1
  have hu2 := bpow_gt_0 beta c2
  have h21 := bpow_lt beta c2 c1 H21
  have hBe := bpow_gt_0 beta (e - 1)
  -- `a = m * u1`, the largest multiple of `u1` below `√x`
  have hK := Zpower_mul_bpow beta c1 e (by omega)
  have hK' := Zpower_mul_bpow beta c1 (e - 1) (by omega)
  have hsq : bpow beta (2 * e) = bpow beta e * bpow beta e := by
    rw [← bpow_plus]; congr 1; omega
  have hsq' : bpow beta (2 * e - 2) = bpow beta (e - 1) * bpow beta (e - 1) := by
    rw [← bpow_plus]; congr 1; omega
  have PK : 0 ≤ Zpower beta.radix_val (e - c1) := by
    apply Classical.byContradiction; intro hn
    have := mul_le_of_int_le hu1 (show Zpower beta.radix_val (e - c1) ≤ 0 by omega)
    have := bpow_gt_0 beta e
    grind
  obtain ⟨m, Pm, hm1, hm2⟩ := exists_sqrt_floor _ x (Rat.le_of_lt Px) _ PK
    (by rw [hK, ← hsq]; exact Hx.2)
  have hlow : bpow beta (e - 1) ≤ (m : Rat) * bpow beta c1 := by
    rw [← hK']
    apply mul_le_of_int_le hu1
    have : Zpower beta.radix_val (e - 1 - c1) < m + 1 := by
      apply int_lt_of_mul_lt hu1
      apply sq_lt_sq_of_nonneg (by rw [hK']; exact Rat.le_of_lt hBe)
        (Rat.le_of_lt (Rat.mul_pos (by exact_mod_cast (show (0 : Int) < m + 1 by omega)) hu1))
      rw [hK', ← hsq']
      grind
    omega
  have hup : ((m + 1 : Int) : Rat) * bpow beta c1 ≤ bpow beta e := by
    rw [← hK]
    apply mul_le_of_int_le hu1
    have : m < Zpower beta.radix_val (e - c1) := by
      apply int_lt_of_mul_lt hu1
      apply sq_lt_sq_of_nonneg (by grind) (by rw [hK]; exact Rat.le_of_lt (bpow_gt_0 beta e))
      rw [hK, ← hsq]
      grind
    omega
  have hm1' : ((m + 1 : Int) : Rat) * bpow beta c1 = (m : Rat) * bpow beta c1 + bpow beta c1 := by
    rw [Rat.intCast_add, Rat.intCast_one, Rat.add_mul, Rat.one_mul]
  have Pa : 0 < (m : Rat) * bpow beta c1 := by grind
  -- `a` and `a + u1` are in both formats
  have hFa : ∀ (fexp : Int → Int) [Valid_exp fexp] (c : Int), fexp e ≤ c → c ≤ c1 → fexp e < e →
      generic_format beta fexp ((m : Rat) * bpow beta c1) ∧
      generic_format beta fexp (((m + 1 : Int) : Rat) * bpow beta c1) := by
    intro fexp _ c hc hcc he
    constructor
    · exact generic_format_of_bmult_le_bpow beta fexp _ e c ⟨hlow, by grind⟩
        (bmult_of_le beta hcc ⟨m, rfl⟩) hc he
    · exact generic_format_of_bmult_le_bpow beta fexp _ e c ⟨by grind, hup⟩
        (bmult_of_le beta hcc ⟨m + 1, rfl⟩) hc he
  obtain ⟨Fa1, Fb1⟩ := hFa fexp1 c1 (by omega) (by omega) (by omega)
  obtain ⟨Fa2, Fb2⟩ := hFa fexp2 c2 (by omega) (by omega) (by omega)
  -- `√x` is not near the midpoint
  have nn := round_round_sqrt_not_near_mid beta fexp1 x e c1 c2 m Fx Hf1 H21 hup Hu
  have hmagc : ∀ c : Rat, (m : Rat) * bpow beta c1 ≤ c → c < ((m + 1 : Int) : Rat) * bpow beta c1 →
      0 < c ∧ mag beta c = e := by
    intro c h1 h2
    exact ⟨by grind, mag_unique_pos beta c e ⟨by grind, by grind⟩⟩
  have hr1a : round beta fexp1 (Znearest choice1) ((m : Rat) * bpow beta c1) =
      (m : Rat) * bpow beta c1 := round_generic beta fexp1 _ _ Fa1
  have hr2a : round beta fexp2 (Znearest choice2) ((m : Rat) * bpow beta c1) =
      (m : Rat) * bpow beta c1 := round_generic beta fexp2 _ _ Fa2
  have hr1b : round beta fexp1 (Znearest choice1) (((m + 1 : Int) : Rat) * bpow beta c1) =
      ((m + 1 : Int) : Rat) * bpow beta c1 := round_generic beta fexp1 _ _ Fb1
  have hr2b : round beta fexp2 (Znearest choice2) (((m + 1 : Int) : Rat) * bpow beta c1) =
      ((m + 1 : Int) : Rat) * bpow beta c1 := round_generic beta fexp2 _ _ Fb2
  rcases (show x < ((m : Rat) * bpow beta c1 + 1 / 2 * (bpow beta c1 - bpow beta c2)) *
          ((m : Rat) * bpow beta c1 + 1 / 2 * (bpow beta c1 - bpow beta c2)) ∨
      ((m : Rat) * bpow beta c1 + 1 / 2 * (bpow beta c1 + bpow beta c2)) *
          ((m : Rat) * bpow beta c1 + 1 / 2 * (bpow beta c1 + bpow beta c2)) < x by
      apply Classical.byContradiction; intro hn
      exact nn ⟨by grind, by grind⟩) with hlt | hgt
  · -- `√x` is below the midpoint: a rational `c` with `√x ≤ c < a + b`
    have hb0 : 0 < 1 / 2 * (bpow beta c1 - bpow beta c2) := by grind
    have hbb := Rat.mul_pos hb0 hb0
    obtain ⟨s, hs⟩ : ∃ s, s = (m : Rat) * bpow beta c1 + 1 / 2 * (bpow beta c1 - bpow beta c2) :=
      ⟨_, rfl⟩
    rw [← hs] at hlt
    have hs0 : 0 < s := by grind
    have hδ : 0 < s * s - x := by grind
    obtain ⟨ε, hε⟩ : ∃ ε, ε = (s * s - x) / (2 * s) := ⟨_, rfl⟩
    have hεm : ε * (2 * s) = s * s - x := by rw [hε]; exact Rat.div_mul_cancel (by grind)
    have hε0 : 0 < ε := by
      apply Classical.byContradiction; intro hn
      have := Rat.mul_le_mul_of_nonneg_right (show ε ≤ 0 by grind) (show 0 ≤ 2 * s by grind)
      grind
    have hεε := Rat.mul_pos hε0 hε0
    have hεb : ε < 1 / 2 * (bpow beta c1 - bpow beta c2) := by
      apply Rat.lt_of_mul_lt_mul_right (c := 2 * s) _ (by grind)
      rw [hεm, hs]
      grind
    have hcx : x ≤ (s - ε) * (s - ε) := by grind
    have hc_lo : (m : Rat) * bpow beta c1 < s - ε := by grind
    have hc_hi : s - ε < ((m + 1 : Int) : Rat) * bpow beta c1 := by grind
    obtain ⟨Pc, hmc⟩ := hmagc (s - ε) (Rat.le_of_lt hc_lo) hc_hi
    have hcexp1 : cexp beta fexp1 (s - ε) = c1 := by unfold cexp; rw [hmc, hc1]
    have hcexp2 : cexp beta fexp2 (s - ε) = c2 := by unfold cexp; rw [hmc, hc2]
    have hr1c : round beta fexp1 (Znearest choice1) (s - ε) = (m : Rat) * bpow beta c1 :=
      round_N_eq_of_near beta fexp1 choice1 _ m c1 hcexp1
        (by rw [Rabs_pos_eq _ (by grind)]; grind)
    have hRR := round_round_lt_mid_further_place beta fexp1 fexp2 choice1 choice2 (s - ε) Pc
      (by rw [hmc, hc1]; omega) (by
        unfold midp
        rw [round_DN_of_between beta fexp1 _ m c1 hcexp1 ⟨Rat.le_of_lt hc_lo, hc_hi⟩,
          ulp_neq_0 beta fexp1 _ (Rat.ne_of_gt Pc), ulp_neq_0 beta fexp2 _ (Rat.ne_of_gt Pc),
          hcexp1, hcexp2]
        grind)
    unfold round_round_eq at hRR
    rw [hr1c] at hRR
    have e1 := H1.lower _ (Rat.le_of_lt Pa) hm1
    have e2 := H1.upper _ (Rat.le_of_lt Pc) hcx
    have e3 := H2.lower _ (Rat.le_of_lt Pa) hm1
    have e4 := H2.upper _ (Rat.le_of_lt Pc) hcx
    rw [hr1a] at e1; rw [hr1c] at e2; rw [hr2a] at e3
    have f1 := round_le beta fexp1 (Znearest choice1) _ _ e3
    have f2 := round_le beta fexp1 (Znearest choice1) _ _ e4
    rw [hr1a] at f1; rw [hRR] at f2
    grind
  · -- `√x` is above the midpoint: a rational `d` with `a + b' < d ≤ √x`
    obtain ⟨s, hs⟩ : ∃ s, s = (m : Rat) * bpow beta c1 + 1 / 2 * (bpow beta c1 + bpow beta c2) :=
      ⟨_, rfl⟩
    rw [← hs] at hgt
    have hs0 : 0 < s := by grind
    have hδ : 0 < x - s * s := by grind
    have hD : 0 < 2 * s + 1 + (x - s * s) := by grind
    obtain ⟨ε, hε⟩ : ∃ ε, ε = (x - s * s) / (2 * s + 1 + (x - s * s)) := ⟨_, rfl⟩
    have hεm : ε * (2 * s + 1 + (x - s * s)) = x - s * s := by
      rw [hε]; exact Rat.div_mul_cancel (Rat.ne_of_gt hD)
    have hε0 : 0 < ε := by
      apply Classical.byContradiction; intro hn
      have := Rat.mul_le_mul_of_nonneg_right (show ε ≤ 0 by grind) (Rat.le_of_lt hD)
      grind
    have hε1 : ε < 1 := by
      apply Rat.lt_of_mul_lt_mul_right (c := 2 * s + 1 + (x - s * s)) _ (Rat.le_of_lt hD)
      rw [hεm]; grind
    have hεε := Rat.mul_lt_mul_of_pos_left hε1 hε0
    have hεδ := Rat.mul_pos hε0 hδ
    have hdx : (s + ε) * (s + ε) ≤ x := by grind
    have hd_lo : (m : Rat) * bpow beta c1 + 1 / 2 * (bpow beta c1 + bpow beta c2) < s + ε := by
      grind
    have hd_hi : s + ε < ((m + 1 : Int) : Rat) * bpow beta c1 := by
      apply sq_lt_sq_of_nonneg (by grind) (by grind)
      grind
    obtain ⟨Pd, hmd⟩ := hmagc (s + ε) (by grind) hd_hi
    have hcexp1 : cexp beta fexp1 (s + ε) = c1 := by unfold cexp; rw [hmd, hc1]
    have hcexp2 : cexp beta fexp2 (s + ε) = c2 := by unfold cexp; rw [hmd, hc2]
    have hr1d : round beta fexp1 (Znearest choice1) (s + ε) = ((m + 1 : Int) : Rat) * bpow beta c1 :=
      round_N_eq_of_near beta fexp1 choice1 _ (m + 1) c1 hcexp1
        (by rw [Rabs_neg_eq _ (by grind)]; grind)
    have hRR := round_round_gt_mid_further_place beta fexp1 fexp2 choice1 choice2 (s + ε) Pd
      (by rw [hmd, hc1, hc2]; omega) (by rw [hmd, hc1]; omega) (by
        unfold midp'
        rw [round_UP_of_between beta fexp1 _ (m + 1) c1 hcexp1
            ⟨by rw [show m + 1 - 1 = m by omega]; grind, Rat.le_of_lt hd_hi⟩,
          ulp_neq_0 beta fexp1 _ (Rat.ne_of_gt Pd), ulp_neq_0 beta fexp2 _ (Rat.ne_of_gt Pd),
          hcexp1, hcexp2]
        grind)
    unfold round_round_eq at hRR
    rw [hr1d] at hRR
    have hb0 : 0 ≤ ((m + 1 : Int) : Rat) * bpow beta c1 := by grind
    have e1 := H1.lower _ (Rat.le_of_lt Pd) hdx
    have e2 := H1.upper _ hb0 (Rat.le_of_lt hm2)
    have e3 := H2.lower _ (Rat.le_of_lt Pd) hdx
    have e4 := H2.upper _ hb0 (Rat.le_of_lt hm2)
    rw [hr1d] at e1; rw [hr1b] at e2; rw [hr2b] at e4
    have f1 := round_le beta fexp1 (Znearest choice1) _ _ e3
    have f2 := round_le beta fexp1 (Znearest choice1) _ _ e4
    rw [hRR] at f1; rw [hr1b] at f2
    grind

/-- `round_round_sqrt` and `round_round_sqrt_radix_ge_4` differ only in the
constant `k` (`2`, resp. `1`) of their third hypothesis. -/
theorem round_round_sqrt_gen (fexp1 fexp2 : Int → Int) [Valid_exp fexp1] [Valid_exp fexp2]
    (choice1 choice2 : Int → Bool) (k : Int) (Hk : 4 ≤ bpow beta k)
    (H1e : ∀ ex, 2 * fexp1 ex ≤ fexp1 (2 * ex))
    (H2e : ∀ ex, 2 * fexp1 ex ≤ fexp1 (2 * ex - 1))
    (H3e : ∀ ex, fexp1 (2 * ex) < 2 * ex → fexp2 ex + ex ≤ 2 * fexp1 ex - k)
    (x : Rat) (Fx : generic_format beta fexp1 x) (r1 r2 : Rat)
    (H1 : is_round_sqrt beta fexp1 (Znearest choice1) x r1)
    (H2 : is_round_sqrt beta fexp2 (Znearest choice2) x r2) :
    round beta fexp1 (Znearest choice1) r2 = r1 := by
  rcases (show x ≤ 0 ∨ 0 < x by grind) with Npx | Px
  · rw [H1.nonpos Npx, H2.nonpos Npx, round_0]
  have Hfx : fexp1 (mag beta x) < mag beta x := mag_generic_gt beta fexp1 x (Rat.ne_of_gt Px) Fx
  obtain ⟨hlo, hhi⟩ := mag_bounds_pos beta x Px
  obtain ⟨e, he⟩ : ∃ e, e = (mag beta x + 1) / 2 := ⟨_, rfl⟩
  have hdisj : mag beta x = 2 * e - 1 ∨ mag beta x = 2 * e := by omega
  have Hlx : fexp1 (2 * e) < 2 * e := by
    rcases hdisj with h | h
    · exact valid_exp_large fexp1 (mag beta x) (2 * e) Hfx (by omega)
    · rw [← h]; exact Hfx
  have Hf1e : 2 * fexp1 e ≤ fexp1 (mag beta x) := by
    rcases hdisj with h | h <;> rw [h]
    · exact H2e e
    · exact H1e e
  have He1 : fexp1 e < e := by have := H1e e; omega
  have H3 := H3e e Hlx
  have hk1 : 0 < k := by
    apply Classical.byContradiction; intro hn
    have := bpow_le beta k 0 (by omega)
    rw [show bpow beta 0 = 1 from Rat.zpow_zero _] at this
    grind
  apply round_round_sqrt_core beta fexp1 fexp2 choice1 choice2 x e Px Fx _ He1 (by omega) Hf1e
    _ r1 r2 H1 H2
  · constructor
    · exact Rat.le_trans (bpow_le beta _ _ (by omega)) hlo
    · have := bpow_le beta (mag beta x) (2 * e) (by omega); grind
  · have e1 : bpow beta (fexp2 e) * bpow beta e = bpow beta (fexp2 e + e) := (bpow_plus _ _ _).symm
    have e2 : bpow beta (fexp1 e) * bpow beta (fexp1 e) = bpow beta (2 * fexp1 e - k) * bpow beta k := by
      rw [← bpow_plus, ← bpow_plus]; congr 1; omega
    rw [e1, e2]
    have h1 := bpow_le beta (fexp2 e + e) (2 * fexp1 e - k) H3
    have h2 := bpow_gt_0 beta (2 * fexp1 e - k)
    have h3 := Rat.mul_le_mul_of_nonneg_left Hk (Rat.le_of_lt h2)
    grind

/-! ### `round_round_mid_cases` -/

theorem round_round_mid_cases (fexp1 fexp2 : Int → Int) [Valid_exp fexp1] [Valid_exp fexp2]
    (choice1 choice2 : Int → Bool) (x : Rat) (Px : 0 < x)
    (Hf2f1 : fexp2 (mag beta x) ≤ fexp1 (mag beta x) - 1)
    (Hf1 : fexp1 (mag beta x) ≤ mag beta x)
    (Hmid : Rabs (x - midp beta fexp1 x) ≤ 1 / 2 * ulp beta fexp2 x →
      round_round_eq beta fexp1 fexp2 choice1 choice2 x) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 x := by
  rcases generic_format_EM beta fexp1 x with Fx | Nfx
  · unfold round_round_eq
    rw [round_generic beta fexp2 _ x
      (generic_inclusion_mag beta fexp1 fexp2 x (fun _ => by omega) Fx)]
  have Hceil := round_UP_DN_ulp beta fexp1 x Nfx
  have hu2 := ulp_ge_0 beta fexp2 x
  rcases (show x - round beta fexp1 Zfloor x < 1 / 2 * (ulp beta fexp1 x - ulp beta fexp2 x) ∨
      1 / 2 * (ulp beta fexp1 x + ulp beta fexp2 x) < x - round beta fexp1 Zfloor x ∨
      (1 / 2 * (ulp beta fexp1 x - ulp beta fexp2 x) ≤ x - round beta fexp1 Zfloor x ∧
       x - round beta fexp1 Zfloor x ≤ 1 / 2 * (ulp beta fexp1 x + ulp beta fexp2 x)) by grind)
    with h | h | h
  · apply round_round_lt_mid_further_place beta fexp1 fexp2 choice1 choice2 x Px Hf1
    unfold midp; grind
  · apply round_round_gt_mid_further_place beta fexp1 fexp2 choice1 choice2 x Px Hf2f1 Hf1
    unfold midp'; grind
  · apply Hmid
    unfold midp
    have := Rabs_cases (x - (round beta fexp1 Zfloor x + 1 / 2 * ulp beta fexp1 x))
    grind

/-! ### Section `Double_round_sqrt` -/

def round_round_sqrt_hyp (fexp1 fexp2 : Int → Int) : Prop :=
  (∀ ex, 2 * fexp1 ex ≤ fexp1 (2 * ex)) ∧
  (∀ ex, 2 * fexp1 ex ≤ fexp1 (2 * ex - 1)) ∧
  (∀ ex, fexp1 (2 * ex) < 2 * ex → fexp2 ex + ex ≤ 2 * fexp1 ex - 2)

/-- Rocq's `mag_sqrt_disj`, for a rational square root `y` of `y * y`. -/
theorem mag_sqrt_disj (y : Rat) (Py : 0 < y) :
    mag beta (y * y) = 2 * mag beta y - 1 ∨ mag beta (y * y) = 2 * mag beta y := by
  have := mag_mult_disj beta y y (Rat.ne_of_gt Py) (Rat.ne_of_gt Py)
  omega

/-- Rocq's `round_round_sqrt`: rounding `√x` first in format `fexp2`, then in
format `fexp1`, gives the rounding of `√x` in format `fexp1`.  Here `r2` and
`r1` are the roundings of `√x` (see the file header). -/
theorem round_round_sqrt (fexp1 fexp2 : Int → Int) [Valid_exp fexp1] [Valid_exp fexp2]
    (choice1 choice2 : Int → Bool) (Hexp : round_round_sqrt_hyp fexp1 fexp2)
    (x : Rat) (Fx : generic_format beta fexp1 x) (r1 r2 : Rat)
    (H1 : is_round_sqrt beta fexp1 (Znearest choice1) x r1)
    (H2 : is_round_sqrt beta fexp2 (Znearest choice2) x r2) :
    round beta fexp1 (Znearest choice1) r2 = r1 := by
  obtain ⟨H1e, H2e, H3e⟩ := Hexp
  refine round_round_sqrt_gen beta fexp1 fexp2 choice1 choice2 2 ?_ H1e H2e H3e x Fx r1 r2 H1 H2
  rw [show (2 : Int) = 1 + 1 from rfl, bpow_plus, bpow_1]
  have : (2 : Rat) ≤ (beta.radix_val : Rat) := by
    have := Rat.intCast_le_intCast.mpr (radix_ge_2 beta); simpa using this
  have := Rat.mul_le_mul_of_nonneg_left this (show (0 : Rat) ≤ beta.radix_val by grind)
  grind

/-- `round_round_sqrt` when `√x` is rational: Rocq's statement. -/
theorem round_round_sqrt_sq (fexp1 fexp2 : Int → Int) [Valid_exp fexp1] [Valid_exp fexp2]
    (choice1 choice2 : Int → Bool) (Hexp : round_round_sqrt_hyp fexp1 fexp2)
    (y : Rat) (Py : 0 ≤ y) (Fx : generic_format beta fexp1 (y * y)) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 y :=
  round_round_sqrt beta fexp1 fexp2 choice1 choice2 Hexp (y * y) Fx _ _
    (is_round_sqrt_sq beta fexp1 _ y Py) (is_round_sqrt_sq beta fexp2 _ y Py)

/-! ### Section `Double_round_sqrt_FLX` -/

theorem FLX_round_round_sqrt_hyp (prec prec' : Int) [Prec_gt_0 prec]
    (Hprec : 2 * prec + 2 ≤ prec') :
    round_round_sqrt_hyp (FLX_exp prec) (FLX_exp prec') := by
  have := Prec_gt_0.prec_gt_0 (prec := prec)
  refine ⟨fun ex => ?_, fun ex => ?_, fun ex _ => ?_⟩ <;> unfold FLX_exp <;> omega

theorem round_round_sqrt_FLX (prec prec' : Int) [Prec_gt_0 prec] [Prec_gt_0 prec']
    (choice1 choice2 : Int → Bool) (Hprec : 2 * prec + 2 ≤ prec')
    (x : Rat) (Fx : FLX_format beta prec x) (r1 r2 : Rat)
    (H1 : is_round_sqrt beta (FLX_exp prec) (Znearest choice1) x r1)
    (H2 : is_round_sqrt beta (FLX_exp prec') (Znearest choice2) x r2) :
    round beta (FLX_exp prec) (Znearest choice1) r2 = r1 :=
  round_round_sqrt beta _ _ choice1 choice2 (FLX_round_round_sqrt_hyp prec prec' Hprec) x
    (generic_format_FLX beta prec x Fx) r1 r2 H1 H2

/-! ### Section `Double_round_sqrt_FLT` -/

theorem FLT_round_round_sqrt_hyp (emin prec emin' prec' : Int) [Prec_gt_0 prec]
    (Hemin : emin ≤ 0)
    (Heminprec : emin' ≤ emin - prec - 2 ∨ 2 * emin' ≤ emin - 4 * prec - 2)
    (Hprec : 2 * prec + 2 ≤ prec') :
    round_round_sqrt_hyp (FLT_exp emin prec) (FLT_exp emin' prec') := by
  have := Prec_gt_0.prec_gt_0 (prec := prec)
  refine ⟨fun ex => ?_, fun ex => ?_, fun ex h => ?_⟩ <;> unfold FLT_exp at * <;> omega

theorem round_round_sqrt_FLT (emin prec emin' prec' : Int) [Prec_gt_0 prec] [Prec_gt_0 prec']
    (choice1 choice2 : Int → Bool) (Hemin : emin ≤ 0)
    (Heminprec : emin' ≤ emin - prec - 2 ∨ 2 * emin' ≤ emin - 4 * prec - 2)
    (Hprec : 2 * prec + 2 ≤ prec')
    (x : Rat) (Fx : FLT_format beta emin prec x) (r1 r2 : Rat)
    (H1 : is_round_sqrt beta (FLT_exp emin prec) (Znearest choice1) x r1)
    (H2 : is_round_sqrt beta (FLT_exp emin' prec') (Znearest choice2) x r2) :
    round beta (FLT_exp emin prec) (Znearest choice1) r2 = r1 :=
  round_round_sqrt beta _ _ choice1 choice2
    (FLT_round_round_sqrt_hyp emin prec emin' prec' Hemin Heminprec Hprec) x
    (generic_format_FLT beta emin prec x Fx) r1 r2 H1 H2

/-! ### Section `Double_round_sqrt_FTZ` -/

theorem FTZ_round_round_sqrt_hyp (emin prec emin' prec' : Int) [Prec_gt_0 prec]
    [Prec_gt_0 prec']
    (Hemin : 2 * (emin' + prec') ≤ emin + prec ∧ emin + prec ≤ 1)
    (Hprec : 2 * prec + 2 ≤ prec') :
    round_round_sqrt_hyp (FTZ_exp emin prec) (FTZ_exp emin' prec') := by
  have := Prec_gt_0.prec_gt_0 (prec := prec)
  have := Prec_gt_0.prec_gt_0 (prec := prec')
  refine ⟨fun ex => ?_, fun ex => ?_, fun ex h => ?_⟩ <;>
    simp only [FTZ_exp_def] at * <;> (repeat' split at *) <;> omega

/-- Rocq's `round_round_sqrt_FTZ` assumes `4 ≤ beta`, which its proof does
not use; it is kept for fidelity. -/
theorem round_round_sqrt_FTZ (emin prec emin' prec' : Int) [Prec_gt_0 prec] [Prec_gt_0 prec']
    (_Hbeta : 4 ≤ beta.radix_val) (choice1 choice2 : Int → Bool)
    (Hemin : 2 * (emin' + prec') ≤ emin + prec ∧ emin + prec ≤ 1)
    (Hprec : 2 * prec + 2 ≤ prec')
    (x : Rat) (Fx : FTZ_format beta emin prec x) (r1 r2 : Rat)
    (H1 : is_round_sqrt beta (FTZ_exp emin prec) (Znearest choice1) x r1)
    (H2 : is_round_sqrt beta (FTZ_exp emin' prec') (Znearest choice2) x r2) :
    round beta (FTZ_exp emin prec) (Znearest choice1) r2 = r1 :=
  round_round_sqrt beta _ _ choice1 choice2
    (FTZ_round_round_sqrt_hyp emin prec emin' prec' Hemin Hprec) x
    (generic_format_FTZ beta emin prec x Fx) r1 r2 H1 H2

/-! ### Section `Double_round_sqrt_radix_ge_4` -/

def round_round_sqrt_radix_ge_4_hyp (fexp1 fexp2 : Int → Int) : Prop :=
  (∀ ex, 2 * fexp1 ex ≤ fexp1 (2 * ex)) ∧
  (∀ ex, 2 * fexp1 ex ≤ fexp1 (2 * ex - 1)) ∧
  (∀ ex, fexp1 (2 * ex) < 2 * ex → fexp2 ex + ex ≤ 2 * fexp1 ex - 1)

theorem round_round_sqrt_radix_ge_4 (Hbeta : 4 ≤ beta.radix_val)
    (fexp1 fexp2 : Int → Int) [Valid_exp fexp1] [Valid_exp fexp2]
    (choice1 choice2 : Int → Bool) (Hexp : round_round_sqrt_radix_ge_4_hyp fexp1 fexp2)
    (x : Rat) (Fx : generic_format beta fexp1 x) (r1 r2 : Rat)
    (H1 : is_round_sqrt beta fexp1 (Znearest choice1) x r1)
    (H2 : is_round_sqrt beta fexp2 (Znearest choice2) x r2) :
    round beta fexp1 (Znearest choice1) r2 = r1 := by
  obtain ⟨H1e, H2e, H3e⟩ := Hexp
  refine round_round_sqrt_gen beta fexp1 fexp2 choice1 choice2 1 ?_ H1e H2e H3e x Fx r1 r2 H1 H2
  rw [bpow_1]
  have := Rat.intCast_le_intCast.mpr Hbeta; simpa using this

/-- `round_round_sqrt_radix_ge_4` when `√x` is rational: Rocq's statement. -/
theorem round_round_sqrt_radix_ge_4_sq (Hbeta : 4 ≤ beta.radix_val)
    (fexp1 fexp2 : Int → Int) [Valid_exp fexp1] [Valid_exp fexp2]
    (choice1 choice2 : Int → Bool) (Hexp : round_round_sqrt_radix_ge_4_hyp fexp1 fexp2)
    (y : Rat) (Py : 0 ≤ y) (Fx : generic_format beta fexp1 (y * y)) :
    round_round_eq beta fexp1 fexp2 choice1 choice2 y :=
  round_round_sqrt_radix_ge_4 beta Hbeta fexp1 fexp2 choice1 choice2 Hexp (y * y) Fx _ _
    (is_round_sqrt_sq beta fexp1 _ y Py) (is_round_sqrt_sq beta fexp2 _ y Py)

/-! ### Section `Double_round_sqrt_radix_ge_4_FLX` -/

theorem FLX_round_round_sqrt_radix_ge_4_hyp (prec prec' : Int) [Prec_gt_0 prec]
    (Hprec : 2 * prec + 1 ≤ prec') :
    round_round_sqrt_radix_ge_4_hyp (FLX_exp prec) (FLX_exp prec') := by
  have := Prec_gt_0.prec_gt_0 (prec := prec)
  refine ⟨fun ex => ?_, fun ex => ?_, fun ex _ => ?_⟩ <;> unfold FLX_exp <;> omega

theorem round_round_sqrt_radix_ge_4_FLX (prec prec' : Int) [Prec_gt_0 prec] [Prec_gt_0 prec']
    (Hbeta : 4 ≤ beta.radix_val) (choice1 choice2 : Int → Bool) (Hprec : 2 * prec + 1 ≤ prec')
    (x : Rat) (Fx : FLX_format beta prec x) (r1 r2 : Rat)
    (H1 : is_round_sqrt beta (FLX_exp prec) (Znearest choice1) x r1)
    (H2 : is_round_sqrt beta (FLX_exp prec') (Znearest choice2) x r2) :
    round beta (FLX_exp prec) (Znearest choice1) r2 = r1 :=
  round_round_sqrt_radix_ge_4 beta Hbeta _ _ choice1 choice2
    (FLX_round_round_sqrt_radix_ge_4_hyp prec prec' Hprec) x
    (generic_format_FLX beta prec x Fx) r1 r2 H1 H2

/-! ### Section `Double_round_sqrt_radix_ge_4_FLT` -/

theorem FLT_round_round_sqrt_radix_ge_4_hyp (emin prec emin' prec' : Int) [Prec_gt_0 prec]
    (Hemin : emin ≤ 0)
    (Heminprec : emin' ≤ emin - prec - 1 ∨ 2 * emin' ≤ emin - 4 * prec)
    (Hprec : 2 * prec + 1 ≤ prec') :
    round_round_sqrt_radix_ge_4_hyp (FLT_exp emin prec) (FLT_exp emin' prec') := by
  have := Prec_gt_0.prec_gt_0 (prec := prec)
  refine ⟨fun ex => ?_, fun ex => ?_, fun ex h => ?_⟩ <;> unfold FLT_exp at * <;> omega

theorem round_round_sqrt_radix_ge_4_FLT (emin prec emin' prec' : Int) [Prec_gt_0 prec]
    [Prec_gt_0 prec'] (Hbeta : 4 ≤ beta.radix_val) (choice1 choice2 : Int → Bool)
    (Hemin : emin ≤ 0)
    (Heminprec : emin' ≤ emin - prec - 1 ∨ 2 * emin' ≤ emin - 4 * prec)
    (Hprec : 2 * prec + 1 ≤ prec')
    (x : Rat) (Fx : FLT_format beta emin prec x) (r1 r2 : Rat)
    (H1 : is_round_sqrt beta (FLT_exp emin prec) (Znearest choice1) x r1)
    (H2 : is_round_sqrt beta (FLT_exp emin' prec') (Znearest choice2) x r2) :
    round beta (FLT_exp emin prec) (Znearest choice1) r2 = r1 :=
  round_round_sqrt_radix_ge_4 beta Hbeta _ _ choice1 choice2
    (FLT_round_round_sqrt_radix_ge_4_hyp emin prec emin' prec' Hemin Heminprec Hprec) x
    (generic_format_FLT beta emin prec x Fx) r1 r2 H1 H2

/-! ### Section `Double_round_sqrt_radix_ge_4_FTZ` -/

theorem FTZ_round_round_sqrt_radix_ge_4_hyp (emin prec emin' prec' : Int) [Prec_gt_0 prec]
    [Prec_gt_0 prec']
    (Hemin : 2 * (emin' + prec') ≤ emin + prec ∧ emin + prec ≤ 1)
    (Hprec : 2 * prec + 1 ≤ prec') :
    round_round_sqrt_radix_ge_4_hyp (FTZ_exp emin prec) (FTZ_exp emin' prec') := by
  have := Prec_gt_0.prec_gt_0 (prec := prec)
  have := Prec_gt_0.prec_gt_0 (prec := prec')
  refine ⟨fun ex => ?_, fun ex => ?_, fun ex h => ?_⟩ <;>
    simp only [FTZ_exp_def] at * <;> (repeat' split at *) <;> omega

theorem round_round_sqrt_radix_ge_4_FTZ (emin prec emin' prec' : Int) [Prec_gt_0 prec]
    [Prec_gt_0 prec'] (Hbeta : 4 ≤ beta.radix_val) (choice1 choice2 : Int → Bool)
    (Hemin : 2 * (emin' + prec') ≤ emin + prec ∧ emin + prec ≤ 1)
    (Hprec : 2 * prec + 1 ≤ prec')
    (x : Rat) (Fx : FTZ_format beta emin prec x) (r1 r2 : Rat)
    (H1 : is_round_sqrt beta (FTZ_exp emin prec) (Znearest choice1) x r1)
    (H2 : is_round_sqrt beta (FTZ_exp emin' prec') (Znearest choice2) x r2) :
    round beta (FTZ_exp emin prec) (Znearest choice1) r2 = r1 :=
  round_round_sqrt_radix_ge_4 beta Hbeta _ _ choice1 choice2
    (FTZ_round_round_sqrt_radix_ge_4_hyp emin prec emin' prec' Hemin Hprec) x
    (generic_format_FTZ beta emin prec x Fx) r1 r2 H1 H2

end Double_round_sqrt

end Flocq
end CC
