/-
  Port of `lib/Wfsimpl.v`: defining recursive functions by Noetherian
  induction, with a non-dependent result type.

  Ported: `Fix` / `unroll_Fix` (well-founded relation) and `Fixm` /
  `unroll_Fixm` (natural-number measure).

  Differences from Rocq: Lean's `WellFounded.fix` plays the role of
  `Wf.Fix`, and its unrolling equation `WellFounded.fix_eq` holds without
  appealing to functional extensionality (which is a theorem in Lean anyway).
  In practice the port defines recursive functions with `termination_by`, so
  these combinators are provided for completeness and for literal ports.
-/

namespace CC
namespace Wfsimpl

section FIX

variable {A B : Sort _} {R : A → A → Prop}

/-- `Wfsimpl.Fix` -/
def Fix (Rwf : WellFounded R) (F : (x : A) → ((y : A) → R y x → B) → B) (x : A) : B :=
  Rwf.fix (C := fun _ => B) F x

/-- `Wfsimpl.unroll_Fix` -/
theorem unroll_Fix (Rwf : WellFounded R) (F : (x : A) → ((y : A) → R y x → B) → B) (x : A) :
    Fix Rwf F x = F x (fun y _ => Fix Rwf F y) :=
  WellFounded.fix_eq Rwf _ x

end FIX

section FIXM

variable {A B : Sort _}

/-- `Wfsimpl.Fixm`: recursion on a natural-number measure. -/
def Fixm (measure : A → Nat)
    (F : (x : A) → ((y : A) → measure y < measure x → B) → B) (x : A) : B :=
  Fix (InvImage.wf measure Nat.lt_wfRel.wf) F x

/-- `Wfsimpl.unroll_Fixm` -/
theorem unroll_Fixm (measure : A → Nat)
    (F : (x : A) → ((y : A) → measure y < measure x → B) → B) (x : A) :
    Fixm measure F x = F x (fun y _ => Fixm measure F y) :=
  unroll_Fix _ F x

end FIXM

end Wfsimpl
end CC
