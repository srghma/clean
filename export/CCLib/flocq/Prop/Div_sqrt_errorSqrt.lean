/-
  Port of Flocq's `Prop/Div_sqrt_error.v` (Flocq 4, as shipped with CompCert),
  the square-root part of section `Fprop_divsqrt_error` that can be stated
  without real square roots.

  Copyright (C) 2010-2018 Sylvie Boldo, Guillaume Melquiond (Flocq, LGPL-3.0+).

  Conventions as in `Div_sqrt_error.lean`.  As in `Double_roundingSqrt.lean`,
  `round beta fexp (Znearest choice) (sqrt x)` is represented by any `r` with
  `is_round_sqrt beta fexp (Znearest choice) x r`.

  Ported here:
  * `sqrt_error_FLX_N`: `x - r * r` is in the format when `r` is the rounding
    to nearest of `√x` (`FLX`, `1 < prec`);
  * `sqrt_error_N_FLX_aux1`, `sqrt_error_N_FLX_aux2` (their statements do not
    mention `sqrt`).

  Still not ported, because their statements are inequalities between real
  square roots (`√(1 + 2 u_ro)`, `√x`) that have no counterpart over `Rat`:
  `sqrt_error_N_FLX_aux3`, `om1ds1p2u_ro_pos`, `om1ds1p2u_ro_le_u_rod1pu_ro`,
  `s1p2u_rom1_pos`, `sqrt_error_N_FLX`, `sqrt_error_N_FLX_ex`,
  `sqrt_error_N_round_ex_derive`, `sqrt_error_N_FLX_round_ex`,
  `sqrt_error_N_FLT_ex`, `sqrt_error_N_FLT_round_ex`.

  Auxiliary results (not in the Rocq file): for rounding to nearest,
  `is_round_sqrt` determines `r` (`is_round_sqrt_N_unique`), `r` is in the
  format (`is_round_sqrt_N_generic`), and `√x` is within half an ulp of `r`,
  written with squares (`is_round_sqrt_N_le`, `is_round_sqrt_N_ge`).  The
  uniqueness was only argued informally in `IEEE754/BinarySingleNaNSqrt.lean`.
  The proof finds rationals `a ≤ √x ≤ b` in the same open cell of the grid of
  half-ulps (`round_N_cell`), on which rounding to nearest is constant.
-/
import CCLib.flocq.Prop.Double_roundingSqrt
import CCLib.flocq.Prop.Div_sqrt_error
import CCLib.flocq.Prop.Relative
import CCLib.flocq.Prop.Mult_error

namespace CC
namespace Flocq

/-! ### Rational points between `√x` and a bound -/

theorem exists_sq_ge_between (x s : Rat) (Px : 0 ≤ x) (Ps : 0 < s) (h : x < s * s) :
    ∃ c, 0 < c ∧ c < s ∧ x ≤ c * c := by
  have hs2 : (0 : Rat) < 2 * s := by grind
  obtain ⟨ε, hε⟩ : ∃ ε, ε = (s * s - x) / (2 * s) := ⟨_, rfl⟩
  have hεm : ε * (2 * s) = s * s - x := by rw [hε]; exact Rat.div_mul_cancel (Rat.ne_of_gt hs2)
  have hε0 : 0 < ε := by
    apply Classical.byContradiction; intro hn
    have := Rat.mul_le_mul_of_nonneg_right (show ε ≤ 0 by grind) (Rat.le_of_lt hs2)
    grind
  have hεs : ε < s := by
    apply Rat.lt_of_mul_lt_mul_right (c := 2 * s) _ (Rat.le_of_lt hs2)
    rw [hεm]
    have := Rat.mul_pos Ps Ps
    grind
  have hεε := Rat.mul_pos hε0 hε0
  exact ⟨s - ε, by grind, by grind, by grind⟩

theorem exists_sq_le_between (x s : Rat) (Ps : 0 ≤ s) (h : s * s < x) :
    ∃ d, s < d ∧ d * d ≤ x := by
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
  have hεs := Rat.mul_nonneg (Rat.le_of_lt hε0) Ps
  exact ⟨s + ε, by grind, by grind⟩

section RoundSqrtN

variable (beta : radix) (fexp : Int → Int) [Valid_exp fexp] (choice : Int → Bool)

omit [Valid_exp fexp] in
/-- Rounding to nearest is constant on an open cell `(n g, (n + 1) g)` of the
grid of `g = bpow c' / 2`, if `c'` is at most the canonical exponent. -/
theorem round_N_cell (e c' n : Int) (hc' : c' ≤ fexp e) (y : Rat) (hy : mag beta y = e)
    (h1 : (n : Rat) * (1 / 2 * bpow beta c') < y)
    (h2 : y < ((n + 1 : Int) : Rat) * (1 / 2 * bpow beta c')) :
    round beta fexp (Znearest choice) y =
      (((n + Zpower beta.radix_val (fexp e - c')) / (2 * Zpower beta.radix_val (fexp e - c')) :
        Int) : Rat) * bpow beta (fexp e) := by
  have hK := Zpower_mul_bpow beta c' (fexp e) hc'
  generalize Zpower beta.radix_val (fexp e - c') = K at *
  have hB := bpow_gt_0 beta c'
  have PK : 0 < K := by
    apply Classical.byContradiction; intro hn
    have := mul_le_of_int_le hB (show K ≤ 0 by omega)
    have := bpow_gt_0 beta (fexp e)
    grind
  obtain ⟨N0, hN0⟩ : ∃ N0, N0 = (n + K) / (2 * K) := ⟨_, rfl⟩
  have i1 : 2 * K * N0 ≤ n + K := by rw [hN0]; exact Int.mul_ediv_self_le (by omega)
  have i2 : n + K < 2 * K * N0 + 2 * K := by
    rw [hN0]; have := Int.lt_mul_ediv_self_add (x := n + K) (k := 2 * K) (by omega); grind
  rw [← hN0]
  apply round_N_eq_of_near beta fexp choice y N0 (fexp e) (by unfold cexp; rw [hy])
  rw [← hK]
  have j1 := mul_le_of_int_le hB (show 2 * K * N0 - K ≤ n by omega)
  have j2 := mul_le_of_int_le hB (show n + 1 ≤ 2 * K * N0 + K by omega)
  push_cast at j1 j2 h2
  have := Rabs_cases (y - (N0 : Rat) * ((K : Rat) * bpow beta c'))
  grind

omit [Valid_exp fexp] in
/-- For rounding to nearest, `is_round_sqrt` pins `r` down: it is the rounding
of a rational lower bound and of a rational upper bound of `√x`. -/
theorem is_round_sqrt_N_rat (x r : Rat) (Px : 0 < x)
    (H : is_round_sqrt beta fexp (Znearest choice) x r) :
    ∃ a b, 0 ≤ a ∧ a * a ≤ x ∧ 0 ≤ b ∧ x ≤ b * b ∧
      r = round beta fexp (Znearest choice) a ∧ r = round beta fexp (Znearest choice) b := by
  obtain ⟨hlo, hhi⟩ := mag_bounds_pos beta x Px
  obtain ⟨e, he⟩ : ∃ e, e = (mag beta x + 1) / 2 := ⟨_, rfl⟩
  have hx1 : bpow beta (e - 1) * bpow beta (e - 1) ≤ x := by
    rw [← bpow_plus]; exact Rat.le_trans (bpow_le beta _ _ (by omega)) hlo
  have hx2 : x < bpow beta e * bpow beta e := by
    rw [← bpow_plus]; have := bpow_le beta (mag beta x) (e + e) (by omega); grind
  obtain ⟨c', hc'⟩ : ∃ c', c' = min (fexp e) (e - 1) := ⟨_, rfl⟩
  have hc'1 : c' ≤ fexp e := by omega
  have hc'2 : c' ≤ e - 1 := by omega
  have hB := bpow_gt_0 beta c'
  have hBe := bpow_gt_0 beta (e - 1)
  have hKe : ((2 * Zpower beta.radix_val (e - c') : Int) : Rat) * (1 / 2 * bpow beta c') =
      bpow beta e := by
    rw [← Zpower_mul_bpow beta c' e (by omega)]; push_cast; grind
  have hKe1 : ((2 * Zpower beta.radix_val (e - 1 - c') : Int) : Rat) * (1 / 2 * bpow beta c') =
      bpow beta (e - 1) := by
    rw [← Zpower_mul_bpow beta c' (e - 1) (by omega)]; push_cast; grind
  have hg : (0 : Rat) < 1 / 2 * bpow beta c' := by grind
  have PK : 0 ≤ 2 * Zpower beta.radix_val (e - c') := by
    apply Classical.byContradiction; intro hn
    have := mul_le_of_int_le hg (show 2 * Zpower beta.radix_val (e - c') ≤ 0 by omega)
    have := bpow_gt_0 beta e
    grind
  obtain ⟨n, Pn, hn1, hn2⟩ := exists_sqrt_floor _ x (Rat.le_of_lt Px) _ PK
    (by rw [hKe]; exact hx2)
  have hlow : bpow beta (e - 1) ≤ (n : Rat) * (1 / 2 * bpow beta c') := by
    rw [← hKe1]
    apply mul_le_of_int_le hg
    have : 2 * Zpower beta.radix_val (e - 1 - c') < n + 1 := by
      apply int_lt_of_mul_lt hg
      apply sq_lt_sq_of_nonneg (by rw [hKe1]; exact Rat.le_of_lt hBe)
        (Rat.le_of_lt (Rat.mul_pos (by exact_mod_cast (show (0 : Int) < n + 1 by omega)) hg))
      rw [hKe1]; grind
    omega
  have hup : ((n + 1 : Int) : Rat) * (1 / 2 * bpow beta c') ≤ bpow beta e := by
    rw [← hKe]
    apply mul_le_of_int_le hg
    have : n < 2 * Zpower beta.radix_val (e - c') := by
      apply int_lt_of_mul_lt hg
      apply sq_lt_sq_of_nonneg (by grind) (by rw [hKe]; exact Rat.le_of_lt (bpow_gt_0 beta e))
      rw [hKe]; grind
    omega
  have Png : 0 < (n : Rat) * (1 / 2 * bpow beta c') := by grind
  rcases (show (n : Rat) * (1 / 2 * bpow beta c') * ((n : Rat) * (1 / 2 * bpow beta c')) = x ∨
      (n : Rat) * (1 / 2 * bpow beta c') * ((n : Rat) * (1 / 2 * bpow beta c')) < x by grind)
    with hx | hx
  · have := H.exact _ (Rat.le_of_lt Png) hx
    exact ⟨_, _, Rat.le_of_lt Png, by grind, Rat.le_of_lt Png, by grind, this, this⟩
  obtain ⟨a, ha1, ha2⟩ := exists_sq_le_between x _ (Rat.le_of_lt Png) hx
  obtain ⟨b, hb0, hb1, hb2⟩ := exists_sq_ge_between x _ (Rat.le_of_lt Px)
    (Rat.mul_pos (by exact_mod_cast (show (0 : Int) < n + 1 by omega)) hg) hn2
  have hab : a ≤ b := by
    apply Classical.byContradiction; intro hn
    have hlt : b < a := by grind
    have := Rat.mul_lt_mul_of_pos_left hlt hb0
    have := Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt hlt) (show 0 ≤ a by grind)
    grind
  have hma : mag beta a = e := mag_unique_pos beta a e ⟨by grind, by grind⟩
  have hmb : mag beta b = e := mag_unique_pos beta b e ⟨by grind, by grind⟩
  have ra := round_N_cell beta fexp choice e c' n hc'1 a hma ha1 (by grind)
  have rb := round_N_cell beta fexp choice e c' n hc'1 b hmb (by grind) hb1
  have l := H.lower a (by grind) ha2
  have u := H.upper b (Rat.le_of_lt hb0) hb2
  exact ⟨a, b, by grind, ha2, Rat.le_of_lt hb0, hb2, by grind, by grind⟩

theorem is_round_sqrt_N_generic (x r : Rat)
    (H : is_round_sqrt beta fexp (Znearest choice) x r) : generic_format beta fexp r := by
  rcases (show x ≤ 0 ∨ 0 < x by grind) with hx | hx
  · rw [H.nonpos hx]; exact generic_format_0 beta fexp
  · obtain ⟨a, _, _, _, _, _, hra, _⟩ := is_round_sqrt_N_rat beta fexp choice x r hx H
    rw [hra]; exact generic_format_round beta fexp _ a

omit [Valid_exp fexp] in
theorem is_round_sqrt_N_unique (x r r' : Rat)
    (H : is_round_sqrt beta fexp (Znearest choice) x r)
    (H' : is_round_sqrt beta fexp (Znearest choice) x r') : r = r' := by
  rcases (show x ≤ 0 ∨ 0 < x by grind) with hx | hx
  · rw [H.nonpos hx, H'.nonpos hx]
  · obtain ⟨a, b, Pa, ha, Pb, hb, hra, hrb⟩ := is_round_sqrt_N_rat beta fexp choice x r hx H
    have h1 := H'.lower a Pa ha
    have h2 := H'.upper b Pb hb
    grind

omit [Valid_exp fexp] in
theorem is_round_sqrt_nonneg (rnd : Rat → Int) [Valid_rnd rnd] (x r : Rat)
    (H : is_round_sqrt beta fexp rnd x r) : 0 ≤ r := by
  rcases (show x ≤ 0 ∨ 0 < x by grind) with hx | hx
  · rw [H.nonpos hx]; exact Rat.le_refl
  · have := H.lower 0 Rat.le_refl (by grind)
    rwa [round_0] at this

/-- `√x ≤ r + ulp r / 2`, written with squares. -/
theorem is_round_sqrt_N_le (x r : Rat) (Pr : 0 < r)
    (H : is_round_sqrt beta fexp (Znearest choice) x r) :
    x ≤ (r + 1 / 2 * ulp beta fexp r) * (r + 1 / 2 * ulp beta fexp r) := by
  have Fr := is_round_sqrt_N_generic beta fexp choice x r H
  have hu : ulp beta fexp r = bpow beta (cexp beta fexp r) := ulp_neq_0 beta fexp r (Rat.ne_of_gt Pr)
  have hu0 := bpow_gt_0 beta (cexp beta fexp r)
  apply Classical.byContradiction; intro hn
  obtain ⟨a, ha1, ha2⟩ := exists_sq_le_between x (r + 1 / 2 * ulp beta fexp r) (by grind)
    (by grind)
  have l := H.lower a (by grind) ha2
  have hN := (round_N_pt beta fexp choice a).2 _ (generic_format_succ beta fexp r Fr)
  rw [succ_eq_pos beta fexp r (Rat.le_of_lt Pr)] at hN
  have c1 := Rabs_cases (round beta fexp (Znearest choice) a - a)
  have c2 := Rabs_cases (r + ulp beta fexp r - a)
  grind

/-- `r - ulp r / 2 ≤ √x`, written with squares. -/
theorem is_round_sqrt_N_ge [Monotone_exp fexp] (x r : Rat) (Pr : 0 < r)
    (H : is_round_sqrt beta fexp (Znearest choice) x r) :
    (r - 1 / 2 * ulp beta fexp r) * (r - 1 / 2 * ulp beta fexp r) ≤ x := by
  have Fr := is_round_sqrt_N_generic beta fexp choice x r H
  have hu : ulp beta fexp r = bpow beta (cexp beta fexp r) := ulp_neq_0 beta fexp r (Rat.ne_of_gt Pr)
  have hu0 := bpow_gt_0 beta (cexp beta fexp r)
  have hx : 0 < x := by
    apply Classical.byContradiction; intro hn
    have := H.nonpos (by grind); grind
  have hur : ulp beta fexp r ≤ r := by
    rw [hu]
    have h1 := mag_generic_gt beta fexp r (Rat.ne_of_gt Pr) Fr
    have h2 := (mag_bounds_pos beta r Pr).1
    have := bpow_le beta (cexp beta fexp r) (mag beta r - 1) (by omega)
    grind
  apply Classical.byContradiction; intro hn
  obtain ⟨b, hb0, hb1, hb2⟩ := exists_sq_ge_between x (r - 1 / 2 * ulp beta fexp r)
    (Rat.le_of_lt hx) (by grind) (by grind)
  have u := H.upper b (Rat.le_of_lt hb0) hb2
  have Fp := generic_format_pred beta fexp r Fr
  have hp1 := pred_plus_ulp beta fexp r Pr Fr
  have hp2 := pred_lt_id beta fexp r (Rat.ne_of_gt Pr)
  have hp3 := ulp_le_pos beta fexp (pred beta fexp r) r (pred_ge_0 beta fexp r Pr Fr)
    (Rat.le_of_lt hp2)
  have hN := (round_N_pt beta fexp choice b).2 _ Fp
  have c1 := Rabs_cases (round beta fexp (Znearest choice) b - b)
  have c2 := Rabs_cases (pred beta fexp r - b)
  grind

end RoundSqrtN

/-! ### Section `Fprop_divsqrt_error` (square root) -/

section Fprop_divsqrt_error
variable (beta : radix) (prec : Int) [Prec_gt_0 prec] (choice : Int → Bool)

/-- Rocq's `sqrt_error_FLX_N`: the remainder `x - r²` of the square root
rounded to nearest is in the format.  `r` is the rounding of `√x`. -/
theorem sqrt_error_FLX_N (Hp1 : 1 < prec) (x r : Rat)
    (Hx : generic_format beta (FLX_exp prec) x)
    (H : is_round_sqrt beta (FLX_exp prec) (Znearest choice) x r) :
    generic_format beta (FLX_exp prec) (x - r * r) := by
  rcases (show x ≤ 0 ∨ 0 < x by grind) with hx | Px
  · rw [H.nonpos hx, Rat.mul_zero, rat_sub_zero]; exact Hx
  have Pr0 := is_round_sqrt_nonneg beta (FLX_exp prec) _ x r H
  by_cases Hr : r = 0
  · rw [Hr, Rat.mul_zero, rat_sub_zero]; exact Hx
  have Pr : 0 < r := by grind
  have Fr := is_round_sqrt_N_generic beta (FLX_exp prec) choice x r H
  have hle := is_round_sqrt_N_le beta (FLX_exp prec) choice x r Pr H
  have hge := is_round_sqrt_N_ge beta (FLX_exp prec) choice x r Pr H
  obtain ⟨fx, Hx1, Hx2⟩ := canonical_generic_format beta _ x Hx
  obtain ⟨fr, Hr1, Hr2⟩ := canonical_generic_format beta (FLX_exp prec) r Fr
  have hcr : cexp beta (FLX_exp prec) r = mag beta r - prec := rfl
  have hcx : cexp beta (FLX_exp prec) x = mag beta x - prec := rfl
  have hu : ulp beta (FLX_exp prec) r = bpow beta (fr.Fexp) := by
    rw [ulp_neq_0 beta _ r Hr, Hr2, ← Hr1]
  have hfr : fr.Fexp = mag beta r - prec := by rw [Hr2, ← Hr1]; exact hcr
  rw [hu] at hle hge
  obtain ⟨hr1, hr2⟩ := mag_bounds_pos beta r Pr
  obtain ⟨hx1, hx2⟩ := mag_bounds_pos beta x Px
  have hU := bpow_gt_0 beta fr.Fexp
  rw [Rat.sub_eq_add_neg]
  apply generic_format_plus_prec beta prec _ (fun e => Int.le_refl _) x _ fx
    (Fopp (Fmult fr fr)) Hx1 (by rw [F2R_opp, F2R_mult, ← Hr1])
  · -- `|x - r²| ≤ x < bpow (mag x)`, since `r² ≤ 2 x`
    have hfx : prec + fx.Fexp = mag beta x := by rw [Hx2, ← Hx1, hcx]; omega
    rw [hfx]
    -- `ulp r ≤ r / 2`
    have h4 : bpow beta fr.Fexp ≤ 1 / 2 * r := by
      have e1 := bpow_le beta fr.Fexp (mag beta r - 2) (by omega)
      have e2 : bpow beta (mag beta r - 1) = bpow beta (mag beta r - 2) * bpow beta 1 := by
        rw [← bpow_plus]; congr 1; omega
      have e3 : (2 : Rat) ≤ bpow beta 1 := by
        rw [bpow_1]; have := Rat.intCast_le_intCast.mpr (radix_ge_2 beta); simpa using this
      have e4 := Rat.mul_le_mul_of_nonneg_left e3 (Rat.le_of_lt (bpow_gt_0 beta (mag beta r - 2)))
      grind
    have h5 : 3 / 4 * r ≤ r - 1 / 2 * bpow beta fr.Fexp := by grind
    have h6 : 3 / 4 * r * (3 / 4 * r) ≤
        (r - 1 / 2 * bpow beta fr.Fexp) * (r - 1 / 2 * bpow beta fr.Fexp) := by
      have k1 := Rat.mul_le_mul_of_nonneg_left h5 (show (0 : Rat) ≤ 3 / 4 * r by grind)
      have k2 := Rat.mul_le_mul_of_nonneg_right h5 (show (0 : Rat) ≤ r - 1 / 2 * bpow beta fr.Fexp by grind)
      grind
    have hrr := Rat.mul_pos Pr Pr
    have := Rabs_cases (x + -(r * r))
    grind
  · -- `|x - r²| ≤ ulp r (r + ulp r / 4) < ulp r · bpow (mag r)`
    show _ < bpow beta (prec + (fr.Fexp + fr.Fexp))
    rw [show prec + (fr.Fexp + fr.Fexp) = fr.Fexp + mag beta r by omega, bpow_plus]
    have hrU : r + bpow beta fr.Fexp ≤ bpow beta (mag beta r) := by
      have hK := Zpower_mul_bpow beta fr.Fexp (mag beta r) (by omega)
      have hr : r = (fr.Fnum : Rat) * bpow beta fr.Fexp := Hr1
      rw [← hK, hr]
      have : fr.Fnum + 1 ≤ Zpower beta.radix_val (mag beta r - fr.Fexp) := by
        have : fr.Fnum < Zpower beta.radix_val (mag beta r - fr.Fexp) := by
          apply int_lt_of_mul_lt hU; rw [hK, ← hr]; exact hr2
        omega
      have := mul_le_of_int_le hU this
      push_cast at this
      grind
    have k := Rat.mul_lt_mul_of_pos_left
      (show r + 1 / 4 * bpow beta fr.Fexp < bpow beta (mag beta r) by grind) hU
    have := Rabs_cases (x + -(r * r))
    have hUU := Rat.mul_pos hU hU
    grind

omit [Prec_gt_0 prec] in
theorem sqrt_error_N_FLX_aux1 (x : Rat) (Fx : generic_format beta (FLX_exp prec) x)
    (Px : 0 < x) :
    ∃ (mu : Rat) (e : Int), generic_format beta (FLX_exp prec) mu ∧
      x = mu * bpow beta (2 * e) ∧ 1 ≤ mu ∧ mu < bpow beta 2 := by
  obtain ⟨hx1, hx2⟩ := mag_bounds_pos beta x Px
  obtain ⟨e, he⟩ : ∃ e, e = (mag beta x - 1) / 2 := ⟨_, rfl⟩
  have hbe : bpow beta (-2 * e) * bpow beta (2 * e) = 1 := by
    rw [← bpow_plus, show -2 * e + 2 * e = 0 by omega, bpow_zero]
  have hp := bpow_gt_0 beta (-2 * e)
  refine ⟨x * bpow beta (-2 * e), e, mult_bpow_exact_FLX beta prec x _ Fx, ?_, ?_, ?_⟩
  · rw [Rat.mul_assoc, hbe, Rat.mul_one]
  · have := Rat.mul_le_mul_of_nonneg_right hx1 (Rat.le_of_lt hp)
    rw [← bpow_plus] at this
    have := bpow_le beta 0 (mag beta x - 1 + -2 * e) (by omega)
    rw [bpow_zero] at this
    grind
  · have := Rat.mul_lt_mul_of_pos_right hx2 hp
    rw [← bpow_plus] at this
    have := bpow_le beta (mag beta x + -2 * e) 2 (by omega)
    grind

theorem sqrt_error_N_FLX_aux2 (x : Rat) (Fx : generic_format beta (FLX_exp prec) x)
    (HxGe1 : 1 ≤ x) :
    x = 1 ∨ x = 1 + 2 * u_ro beta prec ∨ 1 + 4 * u_ro beta prec ≤ x := by
  have Hp := Prec_gt_0.prec_gt_0 (prec := prec)
  have Px : 0 < x := by grind
  have hmag : 1 ≤ mag beta x := by
    apply mag_ge_bpow; rw [Rabs_pos_eq _ (Rat.le_of_lt Px), show (1 : Int) - 1 = 0 from rfl,
      bpow_zero]; exact HxGe1
  obtain ⟨k, hk⟩ := bmult_of_le beta (show -prec + 1 ≤ FLX_exp prec (mag beta x) by
    unfold FLX_exp; omega) (bmult_generic beta _ Fx)
  have hM := Zpower_mul_bpow beta (-prec + 1) 0 (by omega)
  rw [bpow_zero] at hM
  have hB := bpow_gt_0 beta (-prec + 1)
  have h2u : 2 * u_ro beta prec = bpow beta (-prec + 1) := by unfold u_ro; grind
  have hkM : Zpower beta.radix_val (0 - (-prec + 1)) ≤ k := by
    apply Classical.byContradiction; intro hn
    have := mul_le_of_int_le hB (show k + 1 ≤ Zpower beta.radix_val (0 - (-prec + 1)) by omega)
    push_cast at this
    grind
  rcases (show k = Zpower beta.radix_val (0 - (-prec + 1)) ∨
      k = Zpower beta.radix_val (0 - (-prec + 1)) + 1 ∨
      Zpower beta.radix_val (0 - (-prec + 1)) + 2 ≤ k by omega) with h | h | h
  · left; rw [hk, h, hM]
  · right; left; rw [hk, h]; push_cast; grind
  · right; right
    have := mul_le_of_int_le hB h
    push_cast at this
    grind

end Fprop_divsqrt_error

end Flocq
end CC
