/-
  Port of the real-number statements of Flocq's `Prop/Round_odd.v` (Flocq 4,
  as shipped with CompCert), over Mathlib's `ℝ`.

  Copyright (C) 2013-2018 Sylvie Boldo, Guillaume Melquiond (Flocq, LGPL-3.0+).

  `Round_odd.lean` proves the theory of rounding to odd over `Rat`.  Here:
  * `Zrnd_oddR` is Rocq's `Zrnd_odd` on `R`; `Rnd_ext_Zrnd_odd` shows that it
    extends the rational `Zrnd_odd`, and `Valid_rndR_odd` that it is a valid
    rounding (Rocq's `valid_rnd_odd`);
  * `roundR_opp_odd` is Rocq's `round_odd_opp`;
  * `round_N_oddR` is Rocq's `round_N_odd` for every real argument: rounding to
    odd with two extra digits, then rounding to nearest, is rounding to
    nearest (for an even radix);
  * `round_N_oddR_FLX`, `round_N_oddR_FLT` are its instances for the FLX and
    FLT formats.

  The real statements are obtained from the rational ones through the
  transfer lemma `roundR_roundR_of_rat` (`Core/Generic_fmtRealTransfer.lean`).
-/
import CCLib.flocq.Core.Generic_fmtRealTransfer
import CCLib.flocq.Core.Generic_fmtRealRound
import CCLib.flocq.Prop.Round_odd

namespace CC
namespace Flocq

noncomputable section

/-- Rocq's `Zrnd_odd` on `R`: `x` if it is an integer, otherwise the odd one
among `⌊x⌋` and `⌈x⌉`. -/
def Zrnd_oddR (x : ℝ) : ℤ :=
  if x = ((⌊x⌋ : ℤ) : ℝ) then ⌊x⌋
  else if Zeven ⌊x⌋ then ⌈x⌉ else ⌊x⌋

/-- The real `Zrnd_oddR` extends the rational `Zrnd_odd`. -/
theorem Rnd_ext_Zrnd_odd : Rnd_ext Zrnd_odd Zrnd_oddR where
  agree q := by
    unfold Zrnd_oddR Zrnd_odd
    rw [Rat.floor_cast, Rat.ceil_cast, ← Zfloor_eq_floor, ← Zceil_eq_ceil]
    have e : ((q : ℝ) = (((Zfloor q : ℤ) : ℚ) : ℝ)) ↔ q = ((Zfloor q : ℤ) : ℚ) := Rat.cast_inj
    rw [Rat.cast_intCast] at e
    by_cases h : q = ((Zfloor q : ℤ) : ℚ)
    · rw [if_pos (e.2 h), if_pos h]
    · rw [if_neg (fun h' => h (e.1 h')), if_neg h]
  stable := stable_of_unit_interval _ fun n y z h1 h2 h3 h4 => by
    unfold Zrnd_oddR
    have hy : y ≠ ((⌊y⌋ : ℤ) : ℝ) := by rw [floor_eq_of_between h1 h2]; exact ne_of_gt h1
    have hz : z ≠ ((⌊z⌋ : ℤ) : ℝ) := by rw [floor_eq_of_between h3 h4]; exact ne_of_gt h3
    rw [if_neg hy, if_neg hz, floor_eq_of_between h1 h2, floor_eq_of_between h3 h4,
      ceil_eq_of_between h1 h2, ceil_eq_of_between h3 h4]

theorem Zrnd_oddR_DN_or_UP (x : ℝ) : Zrnd_oddR x = ⌊x⌋ ∨ Zrnd_oddR x = ⌈x⌉ := by
  unfold Zrnd_oddR
  split_ifs <;> simp

/-- Rocq's `valid_rnd_odd` on `R`. -/
instance Valid_rndR_odd : Valid_rndR Zrnd_oddR where
  Zrnd_le x y h := by
    rcases lt_or_eq_of_le (Int.floor_mono h) with hlt | heq
    · have h1 : Zrnd_oddR x ≤ ⌈x⌉ := by
        rcases Zrnd_oddR_DN_or_UP x with e | e <;> rw [e]
        exact Int.floor_le_ceil x
      have h2 : ⌈x⌉ ≤ ⌊y⌋ := by
        rw [Int.ceil_le]
        have := Int.floor_le_floor h
        have hx : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
        have : ((⌊x⌋ + 1 : ℤ) : ℝ) ≤ (⌊y⌋ : ℝ) := by exact_mod_cast hlt
        push_cast at this; linarith
      have h3 : ⌊y⌋ ≤ Zrnd_oddR y := by
        rcases Zrnd_oddR_DN_or_UP y with e | e <;> rw [e]
        · exact Int.floor_le_ceil y
      omega
    · by_cases hx : x = ((⌊x⌋ : ℤ) : ℝ)
      · have : Zrnd_oddR x = ⌊x⌋ := by unfold Zrnd_oddR; rw [if_pos hx]
        rw [this, heq]
        rcases Zrnd_oddR_DN_or_UP y with e | e <;> rw [e]
        exact Int.floor_le_ceil y
      · have hx' : (⌊x⌋ : ℝ) < x := lt_of_le_of_ne (Int.floor_le x) (fun e => hx e.symm)
        have hy : y ≠ ((⌊y⌋ : ℤ) : ℝ) := by rw [← heq]; intro e; linarith
        have hcx : ⌈x⌉ = ⌊x⌋ + 1 :=
          ceil_eq_of_between hx' (Int.lt_floor_add_one x)
        have hy' : (⌊y⌋ : ℝ) < y := lt_of_le_of_ne (Int.floor_le y) (fun e => hy e.symm)
        have hcy : ⌈y⌉ = ⌊y⌋ + 1 :=
          ceil_eq_of_between hy' (Int.lt_floor_add_one y)
        unfold Zrnd_oddR
        rw [if_neg hx, if_neg hy, hcx, hcy, heq]
  Zrnd_IZR n := by
    unfold Zrnd_oddR; rw [Int.floor_intCast, if_pos rfl]

/-- Rocq's `Zrnd_odd_opp` on `R`: `Zrnd_odd` is symmetric. -/
theorem Zrnd_oppR_odd : Zrnd_oppR Zrnd_oddR = Zrnd_oddR := by
  funext x
  unfold Zrnd_oppR
  by_cases hx : x = ((⌊x⌋ : ℤ) : ℝ)
  · rw [hx, ← Int.cast_neg, (Valid_rndR_odd).Zrnd_IZR, (Valid_rndR_odd).Zrnd_IZR]; ring
  · have hx' : (⌊x⌋ : ℝ) < x := lt_of_le_of_ne (Int.floor_le x) (fun e => hx e.symm)
    have hcx : ⌈x⌉ = ⌊x⌋ + 1 := ceil_eq_of_between hx' (Int.lt_floor_add_one x)
    have hfn : ⌊-x⌋ = -⌈x⌉ := Int.floor_neg
    have hcn : ⌈-x⌉ = -⌊x⌋ := Int.ceil_neg
    have hnx : -x ≠ ((⌊-x⌋ : ℤ) : ℝ) := by
      rw [hfn, hcx]; push_cast; intro e
      have := Int.lt_floor_add_one x; linarith
    unfold Zrnd_oddR
    rw [if_neg hnx, if_neg hx, hfn, hcn, hcx]
    cases he : Zeven ⌊x⌋
    · have h' : Zeven (-(⌊x⌋ + 1)) = true := by
        rw [Zeven_true_iff]; have := (Zeven_false_iff _).1 he; omega
      rw [h']; simp
    · have h' : Zeven (-(⌊x⌋ + 1)) = false := by
        rw [Zeven_false_iff]; have := (Zeven_true_iff _).1 he; omega
      rw [h']; simp

section Odd_prop
variable (beta : radix) (fexp fexpe : ℤ → ℤ)

/-- Rocq's `round_odd_opp` on `R`. -/
theorem roundR_opp_odd (x : ℝ) :
    roundR beta fexp Zrnd_oddR (-x) = -roundR beta fexp Zrnd_oddR x := by
  rw [roundR_opp, Zrnd_oppR_odd]

variable [Valid_exp fexp] [Exists_NE beta fexp] [Valid_exp fexpe] [Exists_NE beta fexpe]

/-- Rocq's `round_N_odd` for every real `x`: in an even radix, rounding to odd
in a format with (at least) two more digits, then rounding to nearest, is the
same as rounding to nearest directly. -/
theorem round_N_oddR (Even_beta : Zeven beta.radix_val = true)
    (fexpe_fexp : ∀ e, fexpe e ≤ fexp e - 2) (choice : ℤ → Bool) (x : ℝ) :
    roundR beta fexp (ZnearestR choice) (roundR beta fexpe Zrnd_oddR x) =
      roundR beta fexp (ZnearestR choice) x :=
  roundR_roundR_of_rat beta fexp fexpe (Rnd_ext_Znearest choice) Rnd_ext_Zrnd_odd
    (round_N_odd beta fexp fexpe Even_beta fexpe_fexp choice) x

end Odd_prop

section Odd_prop_FLX_FLT

/-- `round_N_oddR` for FLX formats: rounding to odd with precision
`prec + 2` (or more), then to nearest with precision `prec > 1`. -/
theorem round_N_oddR_FLX (beta : radix) (prec prece : ℤ)
    (Even_beta : Zeven beta.radix_val = true) (Hprec1 : 1 < prec) (Hprec : prec + 2 ≤ prece)
    (choice : ℤ → Bool) (x : ℝ) :
    roundR beta (FLX_exp prec) (ZnearestR choice) (roundR beta (FLX_exp prece) Zrnd_oddR x) =
      roundR beta (FLX_exp prec) (ZnearestR choice) x :=
  haveI : Prec_gt_0 prec := ⟨by omega⟩
  haveI : Prec_gt_0 prece := ⟨by omega⟩
  haveI := exists_NE_FLX beta prec (Or.inr Hprec1)
  haveI := exists_NE_FLX beta prece (Or.inr (by omega))
  round_N_oddR beta (FLX_exp prec) (FLX_exp prece) Even_beta
    (fun e => by unfold FLX_exp; omega) choice x

/-- `round_N_oddR` for FLT formats: rounding to odd with precision
`prec + 2` and minimal exponent `emin - 2` (or more), then to nearest with
precision `prec` and minimal exponent `emin`. -/
theorem round_N_oddR_FLT (beta : radix) (emin prec emine prece : ℤ)
    (Even_beta : Zeven beta.radix_val = true) (Hprec1 : 1 < prec)
    (Hprec : prec + 2 ≤ prece) (Hemin : emine ≤ emin - 2) (choice : ℤ → Bool) (x : ℝ) :
    roundR beta (FLT_exp emin prec) (ZnearestR choice)
        (roundR beta (FLT_exp emine prece) Zrnd_oddR x) =
      roundR beta (FLT_exp emin prec) (ZnearestR choice) x :=
  haveI : Prec_gt_0 prec := ⟨by omega⟩
  haveI : Prec_gt_0 prece := ⟨by omega⟩
  haveI := exists_NE_FLT beta emin prec (Or.inr Hprec1)
  haveI := exists_NE_FLT beta emine prece (Or.inr (by omega))
  round_N_oddR beta (FLT_exp emin prec) (FLT_exp emine prece) Even_beta
    (fun e => by unfold FLT_exp; omega) choice x

end Odd_prop_FLX_FLT

end

end Flocq
end CC
