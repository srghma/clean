/-
  Whole-program behaviours — port of the first half of `common/Behaviors.v`.

  A program terminates (with a finite trace and an exit code), diverges
  silently after a finite trace, reacts forever (infinite trace), or goes
  wrong after a finite trace.  `state_behaves_exists` / `program_behaves_exists`
  show, classically, that every state and every program has at least one
  behaviour; for Clight they are instantiated in `ClightBehaviors.lean`.

  Not ported: forward/backward simulations and their preservation theorems
  (the second half of `Behaviors.v`), which only matter for compiler passes.
-/
import CCLib.common.Smallstep

namespace CC
namespace Smallstep

/-! ## Behaviours -/

/-- `Behaviors.program_behavior` -/
inductive ProgramBehavior where
  | Terminates (t : Trace) (r : Integers.Int)
  | Diverges (t : Trace)
  | Reacts (T : Traceinf)
  | Goes_wrong (t : Trace)

namespace ProgramBehavior

/-- `Behaviors.not_wrong` -/
def not_wrong : ProgramBehavior → Prop
  | Goes_wrong _ => False
  | _ => True

/-- `Behaviors.behavior_app`: prefix a behaviour with a finite trace. -/
def behavior_app (t : Trace) : ProgramBehavior → ProgramBehavior
  | Terminates t1 r => Terminates (Eapp t t1) r
  | Diverges t1 => Diverges (Eapp t t1)
  | Reacts T => Reacts (Eappinf t T)
  | Goes_wrong t1 => Goes_wrong (Eapp t t1)

theorem behavior_app_assoc (t1 t2 : Trace) (beh : ProgramBehavior) :
    behavior_app (Eapp t1 t2) beh = behavior_app t1 (behavior_app t2 beh) := by
  cases beh <;> simp [behavior_app, Eapp_assoc, Eappinf_assoc]

theorem behavior_app_E0 (beh : ProgramBehavior) : behavior_app E0 beh = beh := by
  cases beh <;> simp [behavior_app, E0_left, Eappinf_E0]

/-- `Behaviors.behavior_prefix` -/
def behavior_prefix (t : Trace) (beh : ProgramBehavior) : Prop :=
  ∃ beh', beh = behavior_app t beh'

/-- `Behaviors.behavior_improves beh1 beh2`: `beh1` is `beh2`, or goes wrong
    after a prefix of `beh2`. -/
def behavior_improves (beh1 beh2 : ProgramBehavior) : Prop :=
  beh1 = beh2 ∨ ∃ t, beh1 = Goes_wrong t ∧ behavior_prefix t beh2

theorem behavior_improves_refl (beh : ProgramBehavior) : behavior_improves beh beh :=
  Or.inl rfl

theorem behavior_improves_trans {beh1 beh2 beh3 : ProgramBehavior}
    (h1 : behavior_improves beh1 beh2) (h2 : behavior_improves beh2 beh3) :
    behavior_improves beh1 beh3 := by
  rcases h1 with rfl | ⟨t1, rfl, beh2', rfl⟩
  · exact h2
  · rcases h2 with h2 | ⟨t2, h2, beh3', rfl⟩
    · exact Or.inr ⟨t1, rfl, beh2', h2.symm⟩
    · cases beh2' with
      | Goes_wrong t =>
        simp only [behavior_app, Goes_wrong.injEq] at h2
        subst h2
        exact Or.inr ⟨t1, rfl, behavior_app t beh3', behavior_app_assoc _ _ _⟩
      | _ => simp [behavior_app] at h2

theorem behavior_improves_bot (beh : ProgramBehavior) : behavior_improves (Goes_wrong E0) beh :=
  Or.inr ⟨E0, rfl, beh, (behavior_app_E0 beh).symm⟩

theorem behavior_improves_app (t : Trace) {beh1 beh2 : ProgramBehavior}
    (h : behavior_improves beh1 beh2) :
    behavior_improves (behavior_app t beh1) (behavior_app t beh2) := by
  rcases h with rfl | ⟨t', rfl, beh', rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨Eapp t t', rfl, beh', (behavior_app_assoc _ _ _).symm⟩

end ProgramBehavior

open ProgramBehavior

/-! ## Behaviours of states and programs -/

section
variable (L : Semantics)

/-- `Behaviors.state_behaves` -/
inductive StateBehaves (s : L.state) : ProgramBehavior → Prop where
  | terminates {t s' r} : Star L.step s t s' → L.final_state s' r → StateBehaves s (Terminates t r)
  | diverges {t s'} : Star L.step s t s' → ForeverSilent L.step s' → StateBehaves s (Diverges t)
  | reacts {T} : ForeverReactive L.step s T → StateBehaves s (Reacts T)
  | goes_wrong {t s'} : Star L.step s t s' → Nostep L.step s' →
      (∀ r, ¬ L.final_state s' r) → StateBehaves s (Goes_wrong t)

/-- `Behaviors.program_behaves` -/
inductive ProgramBehaves : ProgramBehavior → Prop where
  | runs {s beh} : L.initial_state s → StateBehaves L s beh → ProgramBehaves beh
  | goes_initially_wrong : (∀ s, ¬ L.initial_state s) → ProgramBehaves (Goes_wrong E0)

end

theorem state_behaves_app {L : Semantics} {s1 t s2 beh} (h1 : Star L.step s1 t s2)
    (h2 : StateBehaves L s2 beh) : StateBehaves L s1 (behavior_app t beh) := by
  cases h2 with
  | terminates h hf => exact .terminates (star_trans h1 h rfl) hf
  | diverges h hf => exact .diverges (star_trans h1 h rfl) hf
  | reacts h => exact .reacts (star_forever_reactive h1 h)
  | goes_wrong h hn hf => exact .goes_wrong (star_trans h1 h rfl) hn hf

/-! ## Every state has a behaviour -/

section Exists
variable {σ : Type} {R : σ → Trace → σ → Prop}

/-- Building an infinite silent run by repeatedly choosing a successor. -/
theorem forever_silent_of {s1 : σ}
    (hstep : ∀ s', Star R s1 E0 s' → ∃ t s'', R s' t s'')
    (hsil : ∀ t s', Star R s1 t s' → t = E0) : ForeverSilent R s1 := by
  have next : ∀ x : {x // Star R s1 E0 x}, ∃ y : {y // Star R s1 E0 y}, R x.1 E0 y.1 := by
    intro ⟨x, hx⟩
    obtain ⟨t, s'', hr⟩ := hstep x hx
    have hs : Star R s1 (Eapp E0 t) s'' := star_right hx hr rfl
    have ht : t = E0 := hsil _ _ hs
    subst ht
    exact ⟨⟨s'', hs⟩, hr⟩
  let g : Nat → {x // Star R s1 E0 x} := fun n =>
    Nat.rec ⟨s1, .refl _⟩ (fun _ x => Classical.choose (next x)) n
  exact ⟨fun n => (g n).1, rfl, fun n => Classical.choose_spec (next (g n))⟩

/-- `List` lookup with a default, used to read off an infinite trace. -/
def nthD {α : Type} : List α → Nat → α → α
  | [], _, d => d
  | a :: _, 0, _ => a
  | _ :: l, n + 1, d => nthD l n d

theorem nthD_eq_getElem {α : Type} (l : List α) (i : Nat) (d : α) (h : i < l.length) :
    nthD l i d = l[i] := by
  induction l generalizing i with
  | nil => simp at h
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i (by simp at h; omega)

theorem prefixTrace_append (ts : Nat → Trace) (m k : Nat) :
    ∃ rest, prefixTrace ts (m + k) = prefixTrace ts m ++ rest := by
  induction k with
  | zero => exact ⟨[], by simp⟩
  | succ k ih =>
    obtain ⟨rest, h⟩ := ih
    exact ⟨rest ++ ts (m + k), by
      rw [← Nat.add_assoc, prefixTrace, h]; simp [Eapp, List.append_assoc]⟩

theorem getElem_of_prefix {α : Type} (l1 rest : List α) (i : Nat) (h1 : i < l1.length)
    (h2 : i < (l1 ++ rest).length) : (l1 ++ rest)[i] = l1[i] :=
  List.getElem_append_left h1

/-- Building an infinite reactive run by repeatedly choosing a non-silent
    continuation. -/
theorem forever_reactive_of {s : σ}
    (h : ∀ t1 s1, Star R s t1 s1 → ∃ t2 s2, Star R s1 t2 s2 ∧ t2 ≠ E0) :
    ∃ T, ForeverReactive R s T := by
  have next : ∀ p : {p : Trace × σ // Star R s p.1 p.2},
      ∃ q : Trace × σ, Star R p.1.2 q.1 q.2 ∧ q.1 ≠ E0 := by
    intro ⟨⟨t1, s1⟩, hp⟩
    obtain ⟨t2, s2, h2, hne⟩ := h t1 s1 hp
    exact ⟨(t2, s2), h2, hne⟩
  let step : {p : Trace × σ // Star R s p.1 p.2} → {p : Trace × σ // Star R s p.1 p.2} :=
    fun p => ⟨(Eapp p.1.1 (Classical.choose (next p)).1, (Classical.choose (next p)).2),
      star_trans p.2 (Classical.choose_spec (next p)).1 rfl⟩
  let g : Nat → {p : Trace × σ // Star R s p.1 p.2} := fun n =>
    Nat.rec ⟨(E0, s), .refl _⟩ (fun _ p => step p) n
  let ts : Nat → Trace := fun n => (Classical.choose (next (g n))).1
  have hts : ∀ n, Star R (g n).1.2 (ts n) (g (n + 1)).1.2 ∧ ts n ≠ E0 :=
    fun n => Classical.choose_spec (next (g n))
  have hpre : ∀ n, (g n).1.1 = prefixTrace ts n := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => show Eapp (g n).1.1 (ts n) = _; rw [ih]; rfl
  have hne : ∀ n, ts n ≠ E0 := fun n => (hts n).2
  let T : Traceinf := fun i => nthD (prefixTrace ts (i + 1)) i default
  refine ⟨T, fun n => (g n).1.2, ts, rfl, hts, ?_⟩
  intro n i hi
  show nthD (prefixTrace ts (i + 1)) i default = _
  have hlen := prefixTrace_length_ge ts hne (i + 1)
  rw [nthD_eq_getElem _ _ _ (by omega)]
  by_cases hle : i + 1 ≤ n
  · obtain ⟨rest, hr⟩ := prefixTrace_append ts (i + 1) (n - (i + 1))
    rw [Nat.add_sub_cancel' hle] at hr
    simp only [hr]
    rw [getElem_of_prefix _ _ _ (by omega)]
  · obtain ⟨rest, hr⟩ := prefixTrace_append ts n (i + 1 - n)
    rw [Nat.add_sub_cancel' (by omega)] at hr
    simp only [hr]
    rw [getElem_of_prefix _ _ _ hi]

end Exists

/-- `Behaviors.state_behaves_exists` (classical). -/
theorem state_behaves_exists (L : Semantics) (s : L.state) : ∃ beh, StateBehaves L s beh := by
  by_cases hA : ∃ t s', Star L.step s t s' ∧ Nostep L.step s'
  · obtain ⟨t, s', hs, hn⟩ := hA
    by_cases hf : ∃ r, L.final_state s' r
    · obtain ⟨r, hr⟩ := hf; exact ⟨_, .terminates hs hr⟩
    · exact ⟨_, .goes_wrong hs hn (fun r h => hf ⟨r, h⟩)⟩
  · have hB : ∀ t s', Star L.step s t s' → ∃ t' s'', L.step s' t' s'' := by
      intro t s' h
      apply Classical.byContradiction
      intro hc
      exact hA ⟨t, s', h, fun t' s'' hst => hc ⟨t', s'', hst⟩⟩
    by_cases hB1 : ∃ t1 s1, Star L.step s t1 s1 ∧ ∀ t2 s2, Star L.step s1 t2 s2 → t2 = E0
    · obtain ⟨t1, s1, h1, hsil⟩ := hB1
      refine ⟨_, .diverges h1 (forever_silent_of ?_ hsil)⟩
      intro s' hs'
      exact hB _ _ (star_trans h1 hs' rfl)
    · have hB2 : ∀ t1 s1, Star L.step s t1 s1 → ∃ t2 s2, Star L.step s1 t2 s2 ∧ t2 ≠ E0 := by
        intro t1 s1 h1
        apply Classical.byContradiction
        intro hc
        exact hB1 ⟨t1, s1, h1, fun t2 s2 h2 =>
          Classical.byContradiction fun hne => hc ⟨t2, s2, h2, hne⟩⟩
      obtain ⟨T, hT⟩ := forever_reactive_of hB2
      exact ⟨_, .reacts hT⟩

/-- `Behaviors.program_behaves_exists` (classical): every program has at least
    one behaviour. -/
theorem program_behaves_exists (L : Semantics) : ∃ beh, ProgramBehaves L beh := by
  by_cases h : ∃ s, L.initial_state s
  · obtain ⟨s, hs⟩ := h
    obtain ⟨beh, hb⟩ := state_behaves_exists L s
    exact ⟨beh, .runs hs hb⟩
  · exact ⟨_, .goes_initially_wrong (fun s hs => h ⟨s, hs⟩)⟩

/-- A safe state does not go wrong. -/
theorem safe_not_goes_wrong {L : Semantics} {s beh} (hs : SafeAlways L s)
    (hb : StateBehaves L s beh) : beh.not_wrong := by
  cases hb with
  | goes_wrong h hn hf =>
    rcases hs _ _ h with ⟨r, hr⟩ | ⟨t', s'', hst⟩
    · exact hf r hr
    · exact hn t' s'' hst
  | _ => trivial

end Smallstep
end CC
