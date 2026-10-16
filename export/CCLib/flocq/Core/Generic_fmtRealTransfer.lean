/-
  Transfer of rational rounding identities to arbitrary real arguments
  (support for the `*Real.lean` ports of Flocq's `Prop/` files).

  Copyright (C) 2009-2018 Sylvie Boldo, Guillaume Melquiond (Flocq, LGPL-3.0+).

  * `Rnd_ext_opp`: `Zrnd_oppR rndR` extends `Zrnd_opp rnd` when `rndR`
    extends `rnd`;
  * `roundR_near_irrational'`: the sign-free version of
    `roundR_near_irrational` (`Core/Generic_fmtReal.lean`): at any irrational
    `y`, the real rounding of `y` is the rational rounding of every rational
    close enough to `y`;
  * `roundR_roundR_of_rat`: a double-rounding identity
    `round f1 r1 (round f2 r2 x) = round f1 r1 x` that holds for every
    rational `x` holds for every real `x`.
-/
import CCLib.flocq.Core.Generic_fmtRealRound

namespace CC
namespace Flocq

noncomputable section

/-- If `rndR` extends `rnd`, the opposite rounding `Zrnd_oppR rndR` extends
`Zrnd_opp rnd`. -/
theorem Rnd_ext_opp {rnd : ℚ → ℤ} {rndR : ℝ → ℤ} (h : Rnd_ext rnd rndR) :
    Rnd_ext (Zrnd_opp rnd) (Zrnd_oppR rndR) where
  agree q := by
    unfold Zrnd_oppR Zrnd_opp
    rw [← h.agree (-q), Rat.cast_neg]
  stable m hm := by
    obtain ⟨lo, hi, h1, h2, hst⟩ := h.stable (-m) hm.neg
    refine ⟨-hi, -lo, by linarith, by linarith, fun y hy1 hy2 => ?_⟩
    unfold Zrnd_oppR
    rw [hst (-y) (by linarith) (by linarith)]

section Generic
variable (beta : radix) (fexp : ℤ → ℤ)

/-- At every irrational `y` (of either sign), the real rounding of `y` is the
rational rounding of every rational in a neighbourhood `(L, H)` of `y`. -/
theorem roundR_near_irrational' {rnd : ℚ → ℤ} {rndR : ℝ → ℤ} (h : Rnd_ext rnd rndR)
    (y : ℝ) (hi : Irrational y) :
    ∃ L H : ℝ, L < y ∧ y < H ∧
      ∀ q : ℚ, L < q → (q : ℝ) < H → ((round beta fexp rnd q : ℚ) : ℝ) = roundR beta fexp rndR y := by
  rcases lt_trichotomy y 0 with hy | hy | hy
  · obtain ⟨L, H, _, h1, h2, hq⟩ :=
      roundR_near_irrational beta fexp (Rnd_ext_opp h) (-y) (by linarith) hi.neg
    refine ⟨-H, -L, by linarith, by linarith, fun q hq1 hq2 => ?_⟩
    have e := hq (-q) (by push_cast; linarith) (by push_cast; linarith)
    have hoo : Zrnd_oppR (Zrnd_oppR rndR) = rndR := by funext t; simp [Zrnd_oppR]
    rw [← neg_neg q, round_opp, Rat.cast_neg, e, ← neg_neg y, roundR_opp, neg_neg, neg_neg, hoo]
  · exact absurd (hy ▸ hi) (by simp)
  · obtain ⟨L, H, _, h1, h2, hq⟩ := roundR_near_irrational beta fexp h y hy hi
    exact ⟨L, H, h1, h2, hq⟩

end Generic

/-- Transfer of a double-rounding identity from `ℚ` to `ℝ`: if rounding first
with `(fexp2, rnd2)` and then with `(fexp1, rnd1)` is the same as rounding
once with `(fexp1, rnd1)` for every rational input, the same holds for the
real extensions of the rounding functions and every real input. -/
theorem roundR_roundR_of_rat (beta : radix) (fexp1 fexp2 : ℤ → ℤ)
    {rnd1 rnd2 : ℚ → ℤ} {rndR1 rndR2 : ℝ → ℤ} (h1 : Rnd_ext rnd1 rndR1) (h2 : Rnd_ext rnd2 rndR2)
    (H : ∀ q : ℚ, round beta fexp1 rnd1 (round beta fexp2 rnd2 q) = round beta fexp1 rnd1 q)
    (x : ℝ) :
    roundR beta fexp1 rndR1 (roundR beta fexp2 rndR2 x) = roundR beta fexp1 rndR1 x := by
  by_cases hx : Irrational x
  · obtain ⟨L1, H1, a1, b1, hq1⟩ := roundR_near_irrational' beta fexp2 h2 x hx
    obtain ⟨L2, H2, a2, b2, hq2⟩ := roundR_near_irrational' beta fexp1 h1 x hx
    obtain ⟨q, hql, hqh⟩ := exists_rat_btwn (max_lt a1 a2 : max L1 L2 < x)
    obtain ⟨q', hql', hqh'⟩ := exists_rat_btwn (lt_min b1 b2 : x < min H1 H2)
    -- one rational in the intersection of both neighbourhoods
    have hq : max L1 L2 < (q : ℝ) := hql
    have hq' : (q : ℝ) < min H1 H2 := lt_trans hqh (lt_trans hql' hqh')
    rw [← hq1 q (lt_of_le_of_lt (le_max_left _ _) hq) (lt_of_lt_of_le hq' (min_le_left _ _)),
      ← hq2 q (lt_of_le_of_lt (le_max_right _ _) hq) (lt_of_lt_of_le hq' (min_le_right _ _)),
      ← round_cast beta fexp1 h1, H]
  · obtain ⟨q, rfl⟩ : x ∈ Set.range ((↑) : ℚ → ℝ) := by
      simpa only [Irrational, not_not] using hx
    rw [← round_cast beta fexp2 h2, ← round_cast beta fexp1 h1, ← round_cast beta fexp1 h1, H]

end

end Flocq
end CC
