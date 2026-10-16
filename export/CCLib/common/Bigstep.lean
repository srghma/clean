/-
  Big-step semantics and infinite runs — the parts of `common/Smallstep.v`
  (`forever`, `forever_plus`) and `common/Behaviors.v` (`bigstep_semantics`,
  `bigstep_sound`, `behavior_bigstep_terminates`, `behavior_bigstep_diverges`)
  that `cfrontend/ClightBigstep.v` relies on.

  `Forever R s T` is Rocq's coinductive `forever`: an infinite run from `s`
  whose events form (a stream extending) `T`.  It is a genuine `coinductive`
  predicate here, so `Forever.coinduct` is the coinduction principle.

  Rocq proves divergence through `forever_N` with a well-founded order; the
  big-step proofs only ever use the empty order (each coinductive step makes at
  least one transition), so `forever_of_plus` below packages exactly that case.
-/
import CCLib.common.Behaviors

namespace CC
namespace Smallstep

variable {σ : Type} {R : σ → Trace → σ → Prop}

/-- `Smallstep.forever`: an infinite run from `s` with infinite trace `T`. -/
coinductive Forever (R : σ → Trace → σ → Prop) : σ → Traceinf → Prop where
  | intro {s1 t s2 T} : R s1 t s2 → Forever R s2 T → Forever R s1 (Eappinf t T)

/-- Coinduction with `plus` steps (Rocq: `forever_N_forever` instantiated with
    the empty order, together with `forever_N_plus`).  If every state/trace pair
    satisfying `P` can make at least one transition and land in `P` again, then
    `P` implies `Forever`. -/
theorem forever_of_plus (P : σ → Traceinf → Prop)
    (hP : ∀ s T, P s T → ∃ (s' : σ) (t : Trace) (T' : Traceinf),
      Plus R s t s' ∧ P s' T' ∧ T = Eappinf t T') :
    ∀ s T, P s T → Forever R s T := by
  intro s T hsT
  apply Forever.coinduct R
    (fun (s : σ) (T : Traceinf) => ∃ (s' : σ) (t : Trace) (T' : Traceinf),
      Star R s t s' ∧ P s' T' ∧ T = Eappinf t T')
  · intro s T ⟨s', t, T', hst, hP', hT⟩
    cases hst with
    | refl =>
      obtain ⟨s'', t'', T'', hplus, hP'', hT'⟩ := hP _ _ hP'
      cases hplus with
      | intro hr hs heq =>
        refine ⟨_, _, _, hr, ⟨s'', _, T'', hs, hP'', rfl⟩, ?_⟩
        subst heq; rw [hT, Eappinf_E0, hT', Eappinf_assoc]
    | step hr hs heq =>
      refine ⟨_, _, _, hr, ⟨s', _, T', hs, hP', rfl⟩, ?_⟩
      subst heq; rw [hT, Eappinf_assoc]
  · exact ⟨s, E0, T, .refl _, hsT, (Eappinf_E0 T).symm⟩

/-- Rewrite the trace of a run. -/
theorem Star.trace_cast {s1 t s2 t'} (h : Star R s1 t s2) (ht : t = t') : Star R s1 t' s2 :=
  ht ▸ h

/-- Inversion for `forever`. -/
theorem Forever.inv {s T} (h : Forever R s T) :
    ∃ t s' T', R s t s' ∧ Forever R s' T' ∧ T = Eappinf t T' := by
  cases h with
  | intro hr hf => exact ⟨_, _, _, hr, hf, rfl⟩

/-- `Smallstep.star_forever` -/
theorem star_forever {s1 t s2 T} (h1 : Star R s1 t s2) (h2 : Forever R s2 T) :
    Forever R s1 (Eappinf t T) := by
  induction h1 with
  | refl => rw [Eappinf_E0]; exact h2
  | step hr _ heq ih => subst heq; rw [Eappinf_assoc]; exact .intro R hr (ih h2)


/-! ## Silent or reactive (`Behaviors.v`, `forever_silent_or_reactive`) -/

/-- Coinduction principle for `forever_silent`. -/
theorem foreverSilent_coind (P : σ → Prop) (hP : ∀ s, P s → ∃ s', R s E0 s' ∧ P s') :
    ∀ s, P s → ForeverSilent R s := by
  intro s hs
  let next : {x // P x} → {x // P x} := fun x =>
    ⟨Classical.choose (hP x.1 x.2), (Classical.choose_spec (hP x.1 x.2)).2⟩
  let g : Nat → {x // P x} := fun n => Nat.rec ⟨s, hs⟩ (fun _ x => next x) n
  exact ⟨fun n => (g n).1, rfl, fun n => (Classical.choose_spec (hP (g n).1 (g n).2)).1⟩

/-- Coinduction principle for `forever_reactive`. -/
theorem foreverReactive_coind (P : σ → Traceinf → Prop)
    (hP : ∀ s T, P s T → ∃ (s' : σ) (t : Trace) (T' : Traceinf),
      Star R s t s' ∧ t ≠ E0 ∧ P s' T' ∧ T = Eappinf t T') :
    ∀ s T, P s T → ForeverReactive R s T := by
  intro s T hsT
  let X := {p : σ × Traceinf // P p.1 p.2}
  let next : X → X := fun x =>
    ⟨(Classical.choose (hP x.1.1 x.1.2 x.2),
      Classical.choose (Classical.choose_spec (Classical.choose_spec (hP x.1.1 x.1.2 x.2)))),
     (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
        (hP x.1.1 x.1.2 x.2)))).2.2.1⟩
  let tr : X → Trace := fun x => Classical.choose (Classical.choose_spec (hP x.1.1 x.1.2 x.2))
  have hnext : ∀ x : X, Star R x.1.1 (tr x) (next x).1.1 ∧ tr x ≠ E0 ∧
      x.1.2 = Eappinf (tr x) (next x).1.2 := fun x =>
    let h := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (hP x.1.1 x.1.2 x.2)))
    ⟨h.1, h.2.1, h.2.2.2⟩
  let g : Nat → X := fun n => Nat.rec ⟨(s, T), hsT⟩ (fun _ x => next x) n
  let ts : Nat → Trace := fun n => tr (g n)
  have hT : ∀ n, T = Eappinf (prefixTrace ts n) (g n).1.2 := by
    intro n
    induction n with
    | zero => exact (Eappinf_E0 T).symm
    | succ n ih =>
      rw [ih, (hnext (g n)).2.2]
      show _ = Eappinf (Eapp (prefixTrace ts n) (ts n)) _
      rw [Eappinf_assoc]
  refine ⟨fun n => (g n).1.1, ts, rfl, fun n => ⟨(hnext (g n)).1, (hnext (g n)).2.1⟩, ?_⟩
  intro n
  rw [hT n]
  exact isPrefix_Eappinf _ _

/-- `Behaviors.forever_silent_or_reactive` (classical): an infinite run either
    reacts forever, or performs a finite trace and then diverges silently. -/
theorem forever_silent_or_reactive {s T} (h : Forever R s T) :
    ForeverReactive R s T ∨
    ∃ t s' T', Star R s t s' ∧ ForeverSilent R s' ∧ T = Eappinf t T' := by
  let A : σ → Traceinf → Prop := fun s T =>
    ∃ t s' T', Star R s t s' ∧ ForeverSilent R s' ∧ T = Eappinf t T'
  by_cases hA : A s T
  · exact Or.inr hA
  · left
    apply foreverReactive_coind (fun s T => Forever R s T ∧ ¬ A s T) _ s T ⟨h, hA⟩
    intro s T ⟨hf, hnA⟩
    apply Classical.byContradiction
    intro hno
    apply hnA
    refine ⟨E0, s, T, .refl _, ?_, (Eappinf_E0 T).symm⟩
    apply foreverSilent_coind (fun x => Star R s E0 x ∧ Forever R x T) _ s ⟨.refl _, hf⟩
    intro x ⟨hsx, hfx⟩
    obtain ⟨t, x', T', hr, hf', hT⟩ := hfx.inv
    by_cases ht : t = E0
    · subst ht
      rw [Eappinf_E0] at hT; subst hT
      exact ⟨x', hr, star_right hsx hr rfl, hf'⟩
    · exfalso
      apply hno
      refine ⟨x', t, T', star_right hsx hr rfl, ht, ⟨hf', ?_⟩, hT⟩
      intro ⟨t2, s2, T2, h2, hs2, hT2⟩
      apply hnA
      refine ⟨Eapp t t2, s2, T2, star_trans (star_right hsx hr rfl) h2 rfl, hs2, ?_⟩
      rw [hT, hT2, Eappinf_assoc]

/-! ## Big-step semantics (`Behaviors.v`) -/

/-- `Behaviors.bigstep_semantics`: a big-step semantics is given by its
    terminating and its diverging executions. -/
structure BigstepSemantics where
  bigstep_terminates : Trace → Integers.Int → Prop
  bigstep_diverges : Traceinf → Prop

/-- `Behaviors.bigstep_sound`: every big-step execution is matched by a run of
    the transition semantics `L`. -/
structure BigstepSound (B : BigstepSemantics) (L : Semantics) : Prop where
  bigstep_terminates_sound : ∀ t r, B.bigstep_terminates t r →
    ∃ s1 s2, L.initial_state s1 ∧ Star L.step s1 t s2 ∧ L.final_state s2 r
  bigstep_diverges_sound : ∀ T, B.bigstep_diverges T →
    ∃ s1, L.initial_state s1 ∧ Forever L.step s1 T

open ProgramBehavior

/-- `Behaviors.behavior_bigstep_terminates` -/
theorem behavior_bigstep_terminates {B : BigstepSemantics} {L : Semantics}
    (hsound : BigstepSound B L) {t r} (h : B.bigstep_terminates t r) :
    ProgramBehaves L (Terminates t r) := by
  obtain ⟨s1, s2, hi, hs, hf⟩ := hsound.bigstep_terminates_sound t r h
  exact .runs hi (.terminates hs hf)

/-- `Behaviors.behavior_bigstep_diverges`: a diverging big-step execution is
    either a reactive behaviour of `L`, or a silent divergence after a finite
    prefix `t` of its trace (`traceinf_prefix t T`). -/
theorem behavior_bigstep_diverges {B : BigstepSemantics} {L : Semantics}
    (hsound : BigstepSound B L) {T} (h : B.bigstep_diverges T) :
    ProgramBehaves L (Reacts T) ∨
    ∃ t, ProgramBehaves L (Diverges t) ∧ ∃ T', T = Eappinf t T' := by
  obtain ⟨s1, hi, hf⟩ := hsound.bigstep_diverges_sound T h
  rcases forever_silent_or_reactive hf with hr | ⟨t, s', T', hs, hsil, hT⟩
  · exact Or.inl (.runs hi (.reacts hr))
  · exact Or.inr ⟨t, .runs hi (.diverges hs hsil), T', hT⟩

end Smallstep
end CC
