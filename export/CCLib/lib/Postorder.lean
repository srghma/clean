/-
  Postorder numbering of a directed graph — port of the algorithm of
  `lib/Postorder.v` (`state`, `init_state`, `transition`, `postorder`).

  Differences from Rocq:
  * Rocq iterates `transition` with `WfIter.iterate`, using the
    lexicographic order on (number of unvisited nodes, worklist size).  Here
    `postorder` is a Lean function defined by well-founded recursion on the
    same measure (`PTree.cardinal` is defined structurally).
  * The successor lists are sorted with an insertion sort rather than
    Rocq's merge sort; both return the sorted list.
  * The correctness theorem `postorder_correct` is not ported yet.
-/
import CCLib.lib.MapsTheory

namespace CC

namespace PTree
variable {A : Type}

/-- Number of bound keys of a tree (`PTree_Properties.cardinal`, computed
    structurally). -/
def cardinal : PTree A → Nat
  | .Leaf => 0
  | .Node l o r => cardinal l + (if o.isSome then 1 else 0) + cardinal r

theorem cardinal_remove_lt : ∀ (i : Positive) (m : PTree A) {v : A}, get i m = some v →
    cardinal (remove i m) < cardinal m
  | _, .Leaf, _, h => by simp at h
  | .xH, .Node l o r, _, h => by
    simp only [get] at h; subst h; simp [remove, cardinal]
  | .xO ii, .Node l o r, _, h => by
    simp only [get] at h
    have := cardinal_remove_lt ii l h
    simp only [remove, cardinal]; omega
  | .xI ii, .Node l o r, _, h => by
    simp only [get] at h
    have := cardinal_remove_lt ii r h
    simp only [remove, cardinal]; omega

end PTree

namespace Postorder

/-- `Postorder.node` -/
abbrev Node := Positive
/-- `Postorder.graph` -/
abbrev Graph := PTree (List Node)

/-- Insertion of a positive into a sorted list. -/
def insertSorted (x : Positive) : List Positive → List Positive
  | [] => [x]
  | y :: l => if y.toNat < x.toNat then y :: insertSorted x l else x :: y :: l

/-- `Postorder.Sort.sort`: sort a list of positives in increasing order. -/
def sort : List Positive → List Positive
  | [] => []
  | x :: l => insertSorted x (sort l)

/-- `Postorder.state` -/
structure State where
  gr : Graph
  wrk : List (Node × List Node)
  map : PTree Positive
  next : Positive

/-- `Postorder.init_state` -/
def initState (g : Graph) (root : Node) : State :=
  match g.get root with
  | some succs => ⟨g.remove root, [(root, sort succs)], PTree.empty, .xH⟩
  | none => ⟨g, [], PTree.empty, .xH⟩

/-- `Postorder.size_worklist` -/
def sizeWorklist : List (Positive × List Positive) → Nat
  | [] => 0
  | (_, succs) :: w' => succs.length + 1 + sizeWorklist w'

/-- `Postorder.transition` -/
def transition (s : State) : Sum (PTree Positive) State :=
  match s.wrk with
  | [] => .inl s.map
  | (x, []) :: l => .inr ⟨s.gr, l, s.map.set x s.next, s.next.succ⟩
  | (x, y :: succsX) :: l =>
      match s.gr.get y with
      | none => .inr ⟨s.gr, (x, succsX) :: l, s.map, s.next⟩
      | some succsY => .inr ⟨s.gr.remove y, (y, sort succsY) :: (x, succsX) :: l, s.map, s.next⟩

/-- The measure decreased by `transition` (Rocq's `lt_state`). -/
def measure (s : State) : Nat × Nat := (s.gr.cardinal, sizeWorklist s.wrk)

/-- `Postorder.transition_decreases` -/
theorem transition_decreases {s s' : State} (h : transition s = .inr s') :
    Prod.Lex (· < ·) (· < ·) (measure s') (measure s) := by
  unfold transition at h
  split at h
  · cases h
  · rename_i x l hw
    cases h
    apply Prod.Lex.right; simp [hw, sizeWorklist]
  · rename_i x y succsX l hw
    split at h
    · cases h
      apply Prod.Lex.right; simp [hw, sizeWorklist]
    · rename_i succsY hg
      cases h
      exact Prod.Lex.left _ _ (PTree.cardinal_remove_lt _ _ hg)

/-- Iterate `transition` until it returns a final numbering (Rocq's
    `WfIter.iterate transition`). -/
def iterate (s : State) : PTree Positive :=
  match h : transition s with
  | .inl m => m
  | .inr s' =>
    have := transition_decreases h
    iterate s'
termination_by measure s
decreasing_by exact this

/-- `Postorder.postorder` -/
def postorder (g : Graph) (root : Node) : PTree Positive := iterate (initState g root)

end Postorder
end CC
