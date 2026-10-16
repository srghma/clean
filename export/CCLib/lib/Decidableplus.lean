/-
  Port of `lib/Decidableplus.v`: deciding propositions by evaluation.

  Rocq's `DecidableClass.Decidable` (a Boolean witness plus a specification)
  is Lean's built-in `Decidable` class, and the `decide_goal` tactic is Lean's
  `decide`.  Most instances of `Decidableplus.v` are already in Lean core:

  | Rocq instance | Lean |
  |---|---|
  | `Decidable_not`, `Decidable_and`, `Decidable_or`, `Decidable_implies`, `Decidable_equiv` | `instDecidableNot`, `instDecidableAnd`, `instDecidableOr`, `forall_prop_decidable`, `instDecidableIff` |
  | `Decidable_eq` (from a `{x=y}+{x<>y}` function) | `DecidableEq` |
  | `Decidable_eq_bool`, `Decidable_eq_nat`, `Decidable_eq_Z` | `instDecidableEqBool`, `instDecidableEqNat`, `Int.instDecidableEq` |
  | `Decidable_le_Z`, `Decidable_lt_Z` (and `ge`/`gt`) | `Int.decLe`, `Int.decLt` |
  | `Decidable_forall_in_list`, `Decidable_exists_in_list` | `List.decidableBAll`, `List.decidableBEx` |

  This file adds the remaining ones: `Decidable_eq_positive` (a name for the
  derived `DecidableEq Positive`),
  `Decidable_divides`, the class `Finite` of types with finitely many
  elements, its instances `Finite_bool`, `Finite_pair`, `Finite_option`, and
  `Decidable_forall` / `Decidable_exists` over finite types.
-/
import CCLib.lib.Positive

namespace CC
namespace Decidableplus

/-- `Decidable_eq_positive`: the derived `DecidableEq Positive` instance. -/
instance Decidable_eq_positive (x y : Positive) : Decidable (x = y) := inferInstance

/-- `Decidable_divides`: divisibility on integers, decided by `y = (y / x) * x`. -/
instance Decidable_divides (x y : Int) : Decidable (x ∣ y) :=
  decidable_of_iff (y = (y / x) * x) (by
    constructor
    · intro h; exact ⟨y / x, by rw [Int.mul_comm]; exact h⟩
    · rintro ⟨k, rfl⟩
      by_cases hx : x = 0
      · subst hx; simp
      · rw [Int.mul_ediv_cancel_left _ hx, Int.mul_comm])

/-- Types with finitely many elements (`Decidableplus.Finite`). -/
class Finite (T : Type _) where
  Finite_elements : List T
  Finite_elements_spec : ∀ x : T, x ∈ Finite_elements

export Finite (Finite_elements Finite_elements_spec)

/-- `Decidable_forall`: universal quantification over a finite type. -/
instance Decidable_forall {T : Type _} [Finite T] (P : T → Prop) [∀ x, Decidable (P x)] :
    Decidable (∀ x, P x) :=
  decidable_of_iff (∀ x, x ∈ (Finite_elements : List T) → P x)
    ⟨fun h x => h x (Finite_elements_spec x), fun h x _ => h x⟩

/-- `Decidable_exists`: existential quantification over a finite type. -/
instance Decidable_exists {T : Type _} [Finite T] (P : T → Prop) [∀ x, Decidable (P x)] :
    Decidable (∃ x, P x) :=
  decidable_of_iff (∃ x, x ∈ (Finite_elements : List T) ∧ P x)
    ⟨fun ⟨x, _, h⟩ => ⟨x, h⟩, fun ⟨x, h⟩ => ⟨x, Finite_elements_spec x, h⟩⟩

/-- `Finite_bool` -/
instance Finite_bool : Finite Bool where
  Finite_elements := [false, true]
  Finite_elements_spec x := by cases x <;> simp

/-- `Finite_pair` -/
instance Finite_pair {A B : Type _} [Finite A] [Finite B] : Finite (A × B) where
  Finite_elements :=
    (Finite_elements : List A).flatMap fun a => (Finite_elements : List B).map fun b => (a, b)
  Finite_elements_spec x := by
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨x.1, Finite_elements_spec _, x.2, Finite_elements_spec _, rfl⟩

/-- `Finite_option` -/
instance Finite_option {A : Type _} [Finite A] : Finite (Option A) where
  Finite_elements := none :: (Finite_elements : List A).map some
  Finite_elements_spec x := by
    cases x with
    | none => simp
    | some a => simp [Finite_elements_spec a]

example : ∀ b : Bool, b || !b = true := by decide
example : ∃ p : Bool × Option Bool, p.2 = some p.1 ∧ p.1 = true := by decide
example : (3 : Int) ∣ 12 ∧ ¬ (5 : Int) ∣ 12 := by decide

end Decidableplus
end CC
