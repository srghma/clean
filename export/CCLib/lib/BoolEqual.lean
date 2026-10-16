/-
  Port of `lib/BoolEqual.v`: Boolean-valued equalities.

  In Rocq this file defines Ltac tactics (`boolean_equality`,
  `decidable_equality_from`) that generate a Boolean equality `A → A → bool`
  for an inductive type `A`, prove it reflexive and sound, and wrap it as a
  decidable equality `{x = y} + {x <> y}`.  Their purpose is to avoid the
  large transparent terms produced by `decide equality`.

  In Lean the same job is done by the `deriving DecidableEq` and
  `deriving BEq` handlers, which the port uses for all its inductive types
  (registers, operators, conditions, instructions, …).  What remains to port
  are the generic lemmas, stated here for an arbitrary Boolean equality:

  * `proj_sumbool_is_true`, `proj_sumbool_true`, `false_not_true`;
  * `dec_eq_from_bool_eq`: a reflexive and sound Boolean equality yields a
    `DecidableEq` instance (the core of `decidable_equality_from`);
  * `bool_eq_iff`: such a Boolean equality is exactly `decide (x = y)`.
-/

namespace CC
namespace BoolEqual

/-- `BE.proj_sumbool_is_true` -/
theorem proj_sumbool_is_true {A : Type _} [DecidableEq A] (x : A) : decide (x = x) = true := by
  simp

/-- `BE.proj_sumbool_true` -/
theorem proj_sumbool_true {A : Type _} {x y : A} [Decidable (x = y)]
    (h : decide (x = y) = true) : x = y := of_decide_eq_true h

/-- `BE.false_not_true` -/
theorem false_not_true (P : Prop) (h : false = true) : P := nomatch h

/-- `BE.dec_eq_from_bool_eq`: a reflexive and sound Boolean equality gives a
decidable equality. -/
def dec_eq_from_bool_eq {A : Type _} (f : A → A → Bool)
    (f_refl : ∀ x, f x x = true) (f_sound : ∀ x y, f x y = true → x = y) : DecidableEq A :=
  fun x y =>
    if h : f x y = true then isTrue (f_sound x y h)
    else isFalse (fun e => h (e ▸ f_refl x))

/-- A reflexive and sound Boolean equality decides equality. -/
theorem bool_eq_iff {A : Type _} (f : A → A → Bool)
    (f_refl : ∀ x, f x x = true) (f_sound : ∀ x y, f x y = true → x = y) (x y : A) :
    f x y = true ↔ x = y :=
  ⟨f_sound x y, fun e => e ▸ f_refl x⟩

/-- Example: the derived equality of an enumeration agrees with `dec_eq_from_bool_eq`. -/
example : (dec_eq_from_bool_eq (fun a b : Bool => a == b) (by decide) (by decide) true false).decide
    = false := rfl

end BoolEqual
end CC
