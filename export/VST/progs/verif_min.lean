/-
  Port of VST's `progs/verif_min.v`: `minimum` (`vst/progs/min.c`) meets its
  specification.

  VST's specification:

      DECLARE _minimum
       WITH a: val, n: Z, al: list Z
       PRE [ tptr tint , tint ]
         PROP  (1 <= n <= Int.max_signed; Forall repable_signed al)
         PARAMS (a; Vint (Int.repr n))
         SEP   (data_at Ews (tarray tint n) (map Vint (map Int.repr al)) a)
       POST [ tint ]
         PROP ()
         RETURN (Vint (Int.repr (fold_right Z.min (hd 0 al) al)))
         SEP   (data_at Ews (tarray tint n) (map Vint (map Int.repr al)) a).

  Here the separation logic is the one of `CCLib.logic`; the array of `n`
  `int`s at `a` is `arrayU32 p b ofs n f` (an `int` and an `unsigned int`
  have the same 32-bit representation), the share `Ews` is a readable
  permission `p`, and `al` is the list of the elements as 32-bit integers
  (`Integers.Int`), so `Forall repable_signed al` is built in.  The returned
  value is `listMin al`, the minimum of the elements for the signed order;
  `listMin_signed` shows that it is VST's `fold_right Z.min (hd 0 al) al`.
  `data_at` also implies that the array fits in the address space
  (`field_compatible`); that is the hypothesis `hno`.

  The proof follows `body_min` of `verif_min.v`: after `min = a[0]`, the
  loop invariant says that `min` is the minimum of the first `i` elements
  (and of `a[0]`), and `0 ≤ i ≤ n`.
-/
import VST.progs.min
import CCLib
open CC CC.Sep CC.HProp
open Min

namespace VST.Verif.Min

/-! ## The minimum of the first elements -/

/-- One step of the loop: `if (j < min) min = j;`. -/
def imin (acc x : Integers.Int) : Integers.Int := if Integers.Int.lt x acc then x else acc

/-- The minimum of `f 0` and the first `n` elements. -/
def minTo (f : Nat → Integers.Int) : Nat → Integers.Int
  | 0 => f 0
  | n + 1 => imin (minTo f n) (f n)

/-- The minimum of a list for the signed order (the first element if the list
    is empty-free; `0` for the empty list, as VST's `hd 0 al`). -/
def listMin (contents : List Integers.Int) : Integers.Int :=
  contents.foldl imin (contents.headD (Integers.Int.repr 0))

/-- The elements of a list, as a function (`Znth`). -/
def elems (contents : List Integers.Int) (j : Nat) : Integers.Int :=
  contents.getD j (Integers.Int.repr 0)

theorem minTo_elems (contents : List Integers.Int) :
    ∀ n, n ≤ contents.length →
      minTo (elems contents) n = (contents.take n).foldl imin (elems contents 0) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    have hlt : n < contents.length := by omega
    rw [minTo, ih (by omega), List.take_succ_eq_append_getElem hlt, List.foldl_append]
    simp [elems, hlt]

theorem minTo_elems_length (contents : List Integers.Int) :
    minTo (elems contents) contents.length = listMin contents := by
  rw [minTo_elems contents _ (Nat.le_refl _), List.take_length, listMin]
  cases contents <;> rfl

/-! ### Agreement with VST's `fold_right Z.min (hd 0 al) al` -/

theorem signed_imin (acc x : Integers.Int) :
    Integers.Int.signed (imin acc x) = min (Integers.Int.signed acc) (Integers.Int.signed x) := by
  have hlt : Integers.Int.lt x acc = decide (Integers.Int.signed x < Integers.Int.signed acc) := by
    simp [Integers.Int.lt, Integers.MI.lt, Integers.Int.signed, Integers.MI.signed, BitVec.slt]
  unfold imin
  rw [hlt, Int.min_def]
  by_cases h : Integers.Int.signed x < Integers.Int.signed acc
  · rw [if_pos (by simpa using h), if_neg (by exact Int.not_le.mpr h)]
  · rw [if_neg (by simpa using h), if_pos (by exact Int.not_lt.mp h)]

private theorem foldl_min_eq_foldr (l : List _root_.Int) (x : _root_.Int) :
    l.foldl min x = l.foldr min x := by
  induction l generalizing x with
  | nil => rfl
  | cons y l ih =>
    rw [List.foldl_cons, ih, List.foldr_cons]
    clear ih
    induction l generalizing x with
    | nil => exact Int.min_comm _ _
    | cons z l ih' => rw [List.foldr_cons, List.foldr_cons, ih']; omega

/-- `listMin` is VST's `fold_right Z.min (hd 0 al) al`, on the signed
    values of the elements. -/
theorem listMin_signed (contents : List Integers.Int) :
    Integers.Int.signed (listMin contents)
      = (contents.map Integers.Int.signed).foldr min
          ((contents.map Integers.Int.signed).headD 0) := by
  have key : ∀ (l : List Integers.Int) (x : Integers.Int),
      Integers.Int.signed (l.foldl imin x) = (l.map Integers.Int.signed).foldl min
        (Integers.Int.signed x) := by
    intro l
    induction l with
    | nil => intro x; rfl
    | cons y l ih => intro x; rw [List.foldl_cons, ih, signed_imin]; rfl
  rw [listMin, key, foldl_min_eq_foldr]
  cases contents <;> rfl

/-! ## Facts about the generated program -/

/-- The temporaries `minimum` writes are distinct from the ones it reads. -/
structure Distinct : Prop where
  i_a : _i ≠ _a
  i_n : _i ≠ _n
  i_min : _i ≠ _min
  min_a : _min ≠ _a
  min_n : _min ≠ _n
  min_i : _min ≠ _i
  j_a : _j ≠ _a
  j_n : _j ≠ _n
  j_i : _j ≠ _i
  j_min : _j ≠ _min

theorem idents_distinct : Distinct := by constructor <;> decide

/-- The side conditions of `function_entry2` for `minimum`. -/
theorem entry_wf :
    listNorepet (varNames f_minimum.fn_vars)
    ∧ listNorepet (varNames f_minimum.fn_params)
    ∧ listDisjoint (varNames f_minimum.fn_params) (varNames f_minimum.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem n_ne_a : _n ≠ _a := by decide

/-- The parts of the body. -/
def elemExpr (idx : Expr) : Expr :=
  .Ederef (.Ebinop .Oadd (.Etempvar _a (tptr tint)) idx (tptr tint)) tint
def setMin0 : Stmt := .Sset _min (elemExpr (.Econst_int (Integers.Int.repr 0) tint))
def setI0 : Stmt := .Sset _i (.Econst_int (Integers.Int.repr 0) tint)
def guardExpr : Expr := .Ebinop .Olt (.Etempvar _i tint) (.Etempvar _n tint) tint
def ifStmt : Stmt := .Sifthenelse guardExpr .Sskip .Sbreak
def setJ : Stmt := .Sset _j (elemExpr (.Etempvar _i tint))
def minGuard : Expr := .Ebinop .Olt (.Etempvar _j tint) (.Etempvar _min tint) tint
def ifMin : Stmt := .Sifthenelse minGuard (.Sset _min (.Etempvar _j tint)) .Sskip
def bodyStmt : Stmt := .Ssequence setJ ifMin
def incrStmt : Stmt :=
  .Sset _i (.Ebinop .Oadd (.Etempvar _i tint) (.Econst_int (Integers.Int.repr 1) tint) tint)
def loopStmt : Stmt := .Sloop (.Ssequence ifStmt bodyStmt) incrStmt
def retStmt : Stmt := .Sreturn (some (.Etempvar _min tint))
def fullBody : Stmt := .Ssequence setMin0 (.Ssequence (.Ssequence setI0 loopStmt) retStmt)

theorem body_eq : f_minimum.fn_body = fullBody := rfl

/-! ## Assertions -/

section
variable (p : Permission) (b : Block) (ofs0 : Integers.Ptrofs) (L : Nat)
variable (f : Nat → Integers.Int)

/-- The local state: `a` and `n` as passed, `i = iv`, `min = mv`, `j` as far
    as set, and the array owned. -/
def St (iv : Nat) (mv : Integers.Int) (j : Option Integers.Int) : Sep.Assn := fun e le hp =>
  e = emptyEnv
  ∧ le.get _a = some (.Vptr b ofs0)
  ∧ le.get _n = some (.Vint (Integers.Int.repr L))
  ∧ le.get _i = some (.Vint (Integers.Int.repr iv))
  ∧ le.get _min = some (.Vint mv)
  ∧ (match j with | none => True | some x => le.get _j = some (.Vint x))
  ∧ arrayU32 p b (Integers.Ptrofs.unsigned ofs0) L f hp

/-- The loop invariant, `k` iterations left: `min` is the minimum of the first
    `i` elements, and `0 ≤ i ≤ n`. -/
def LInv (k : Nat) : Sep.Assn := fun e le hp =>
  ∃ iv, St p b ofs0 L f iv (minTo f iv) none e le hp ∧ iv ≤ L ∧ L - iv = k

/-- After the guard: `i < n`. -/
def LMid (k : Nat) : Sep.Assn := fun e le hp =>
  ∃ iv, St p b ofs0 L f iv (minTo f iv) none e le hp ∧ iv < L ∧ L - iv = k

/-- After the body, before `i++`: `min` accounts for element `i`. -/
def LAfter (k : Nat) : Sep.Assn := fun e le hp =>
  ∃ iv, St p b ofs0 L f iv (minTo f (iv + 1)) none e le hp ∧ iv < L ∧ L - iv = k

/-- After the loop: `min` is the minimum of all the elements. -/
def Done : Sep.Assn := fun e le hp =>
  e = emptyEnv ∧ le.get _min = some (.Vint (minTo f L))
  ∧ arrayU32 p b (Integers.Ptrofs.unsigned ofs0) L f hp

/-- The postcondition: the minimum is returned, and the array handed back. -/
def Ret : Val → HProp := fun v hp =>
  v = .Vint (minTo f L) ∧ arrayU32 p b (Integers.Ptrofs.unsigned ofs0) L f hp

/-- The exits of the loop body (before `i++`). -/
def IterR (k : Nat) : Sep.ExitConds :=
  { normal := LAfter p b ofs0 L f k, brk := Done p b ofs0 L f,
    cont := LAfter p b ofs0 L f k, ret := Ret p b ofs0 L f }

def LoopR : Sep.ExitConds :=
  { normal := Done p b ofs0 L f, brk := Sep.Assn.no, cont := Sep.Assn.no,
    ret := Ret p b ofs0 L f }

end

/-! ## The proof -/

private theorem no_ovf_mono (A : _root_.Int) (i l : Nat) (hil : i ≤ l)
    (h : A + 4 * (l : _root_.Int) < 18446744073709551616) :
    A + 4 * (i : _root_.Int) < 18446744073709551616 := by omega

section
variable (ge : CGenv) (fe : EntryRel) (p : Permission) (b : Block)
variable (ofs0 : Integers.Ptrofs) (L : Nat) (f : Nat → Integers.Int)

/-- The guard `i < n`, evaluated. -/
theorem eval_guard (e : Env) (le : TempEnv) (m : Mem) (iv : Nat) (mv : Integers.Int)
    (j : Option Integers.Int) (hp : Heap) (hL : (L : _root_.Int) < 2147483648) (hiv : iv ≤ L)
    (hSt : St p b ofs0 L f iv mv j e le hp) :
    EvalExpr ge e le m guardExpr (Val.ofBool (decide (iv < L))) := by
  obtain ⟨_, _, hn, hi, _⟩ := hSt
  have h : EvalExpr ge e le m guardExpr
      (Val.ofBool (Integers.Int.lt (Integers.Int.repr iv) (Integers.Int.repr L))) :=
    EvalExpr.Ebinop .Olt _ _ _ _ _ _ (EvalExpr.Etempvar _i tint _ hi)
      (EvalExpr.Etempvar _n tint _ hn) (semBinop_lt_int _ _ _ _)
  rw [lt_repr (iv : _root_.Int) (L : _root_.Int) (by omega) (by omega) (by omega) hL] at h
  simpa using h

/-- The `if` at the top of the loop body: continue while `i < n`, break
    out with the minimum of all the elements otherwise. -/
theorem if_triple (k : Nat) (hL : (L : _root_.Int) < 2147483648) :
    Sep.Triple ge fe f_minimum (LInv p b ofs0 L f k) ifStmt
      { IterR p b ofs0 L f k with normal := LMid p b ofs0 L f k } := by
  cases k with
  | zero =>
    refine Sep.triple_if_false ge fe f_minimum _ _ _ _ _ (fun e le hp m hP _ => ?_) ?_
    · obtain ⟨iv, hSt, hiv, hk⟩ := hP
      refine ⟨_, eval_guard ge p b ofs0 L f e le m iv _ none hp hL hiv hSt, ?_⟩
      have : ¬ iv < L := by omega
      simpa [this, guardExpr, typeof] using boolVal_ofBool_int m false
    · refine Sep.triple_conseq ge fe f_minimum (Sep.triple_break ge fe f_minimum _)
        (fun _ _ _ x => x) (fun _ _ _ x => False.elim x) (fun e le hp h => ?_)
        (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)
      obtain ⟨iv, ⟨he, _, _, _, hmin, _, harr⟩, hiv, hk⟩ := h
      have : iv = L := by omega
      subst this
      exact ⟨he, hmin, harr⟩
  | succ j =>
    refine Sep.triple_if_true ge fe f_minimum _ _ _ _ _ (fun e le hp m hP _ => ?_) ?_
    · obtain ⟨iv, hSt, hiv, hk⟩ := hP
      refine ⟨_, eval_guard ge p b ofs0 L f e le m iv _ none hp hL hiv hSt, ?_⟩
      have : iv < L := by omega
      simpa [this, guardExpr, typeof] using boolVal_ofBool_int m true
    · refine Sep.triple_fallthrough ge fe f_minimum _ _ _ _
        (Sep.triple_skip ge fe f_minimum _) (fun e le hp h => ?_)
      obtain ⟨iv, hSt, hiv, hk⟩ := h
      exact ⟨iv, hSt, by omega, hk⟩

/-- The body: `j = a[i]; if (j < min) min = j;`. -/
theorem body_triple (k : Nat) (hd : Distinct) (hpr : permOrder p .Readable = true)
    (hL : (L : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned ofs0 + 4 * (L : _root_.Int) < 18446744073709551616) :
    Sep.Triple ge fe f_minimum (LMid p b ofs0 L f k) bodyStmt (IterR p b ofs0 L f k) := by
  refine Sep.triple_exists ge fe f_minimum _ _ _ (fun iv => ?_)
  show Sep.Triple ge fe f_minimum
    (fun e le hp => St p b ofs0 L f iv (minTo f iv) none e le hp ∧ iv < L ∧ L - iv = k)
    bodyStmt _
  refine Sep.triple_seq_only ge fe f_minimum (Q := fun e le hp =>
      St p b ofs0 L f iv (minTo f iv) (some (f iv)) e le hp ∧ iv < L ∧ L - iv = k) ?_ ?_
  · -- j = a[i]
    refine Sep.triple_set ge fe f_minimum _ _ _ _ (fun e le hp m hP hag => ?_)
    obtain ⟨⟨he, ha, hn, hi, hmin, _, harr⟩, hlt, hk⟩ := hP
    refine ⟨.Vint (f iv), ?_, ?_⟩
    · exact eval_index_array_int hpr harr hag hlt (EvalExpr.Etempvar _a (tptr tint) _ ha)
        (EvalExpr.Etempvar _i tint _ hi) rfl rfl
        (elemOfs_unsigned ge.genv_cenv ofs0 iv (by omega) (no_ovf_mono _ iv L (by omega) hno))
    · exact ⟨⟨he, (PTree.gso _ _ _ _ hd.j_a).trans ha, (PTree.gso _ _ _ _ hd.j_n).trans hn,
        (PTree.gso _ _ _ _ hd.j_i).trans hi, (PTree.gso _ _ _ _ hd.j_min).trans hmin,
        PTree.gss _ _ _, harr⟩, hlt, hk⟩
  · -- if (j < min) min = j;
    refine Sep.triple_if ge fe f_minimum _
      (fun e le hp => (St p b ofs0 L f iv (minTo f iv) (some (f iv)) e le hp ∧ iv < L
        ∧ L - iv = k) ∧ Integers.Int.lt (f iv) (minTo f iv) = true)
      (fun e le hp => (St p b ofs0 L f iv (minTo f iv) (some (f iv)) e le hp ∧ iv < L
        ∧ L - iv = k) ∧ Integers.Int.lt (f iv) (minTo f iv) = false)
      _ _ _ _ (fun e le hp m hP _ => ?_) ?_ ?_
    · have hP' := hP
      obtain ⟨⟨_, _, _, _, hmin, hj, _⟩, _⟩ := hP
      refine ⟨Val.ofBool (Integers.Int.lt (f iv) (minTo f iv)),
        Integers.Int.lt (f iv) (minTo f iv), ?_, ?_, ?_⟩
      · exact EvalExpr.Ebinop .Olt _ _ _ _ _ _ (EvalExpr.Etempvar _j tint _ hj)
          (EvalExpr.Etempvar _min tint _ hmin) (semBinop_lt_int _ _ _ _)
      · simpa [minGuard, typeof] using boolVal_ofBool_int m _
      · cases h : Integers.Int.lt (f iv) (minTo f iv) <;> exact ⟨hP', rfl⟩
    · -- min = j
      refine Sep.triple_fallthrough ge fe f_minimum _ _ _ _
        (Sep.triple_set ge fe f_minimum _ _ _ _ (fun e le hp m hP _ => ?_)) (fun _ _ _ x => x)
      obtain ⟨⟨⟨he, ha, hn, hi, _, hj, harr⟩, hlt, hk⟩, hcmp⟩ := hP
      refine ⟨.Vint (f iv), EvalExpr.Etempvar _j tint _ hj, iv, ⟨he,
        (PTree.gso _ _ _ _ hd.min_a).trans ha, (PTree.gso _ _ _ _ hd.min_n).trans hn,
        (PTree.gso _ _ _ _ hd.min_i).trans hi, ?_, trivial, harr⟩, hlt, hk⟩
      rw [PTree.gss, minTo, imin, hcmp]; rfl
    · -- skip
      refine Sep.triple_fallthrough ge fe f_minimum _ _ _ _
        (Sep.triple_skip ge fe f_minimum _) (fun e le hp hP => ?_)
      obtain ⟨⟨⟨he, ha, hn, hi, hmin, _, harr⟩, hlt, hk⟩, hcmp⟩ := hP
      refine ⟨iv, ⟨he, ha, hn, hi, ?_, trivial, harr⟩, hlt, hk⟩
      rw [minTo, imin, hcmp]; exact hmin

/-- `i++`: one iteration fewer is left. -/
theorem incr_triple (k : Nat) (hd : Distinct) :
    Sep.Triple ge fe f_minimum (LAfter p b ofs0 L f k) incrStmt
      { normal := fun e le hp => ∃ n', n' < k ∧ LInv p b ofs0 L f n' e le hp,
        brk := Done p b ofs0 L f, cont := Sep.Assn.no, ret := Ret p b ofs0 L f } := by
  refine Sep.triple_fallthrough ge fe f_minimum _ _ _ _
    (Sep.triple_set ge fe f_minimum _ _ _ _ (fun e le hp m hP _ => ?_)) (fun _ _ _ x => x)
  obtain ⟨iv, ⟨he, ha, hn, hi, hmin, _, harr⟩, hlt, hk⟩ := hP
  refine ⟨.Vint (Integers.Int.repr ((iv : _root_.Int) + 1)), ?_, ?_⟩
  · refine EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (EvalExpr.Etempvar _i tint _ hi)
      (EvalExpr.Econst_int _ tint) ?_
    simp only [typeof]
    rw [semBinop_add_int, repr_add]
  · refine ⟨L - (iv + 1), by omega, iv + 1, ⟨he, (PTree.gso _ _ _ _ hd.i_a).trans ha,
      (PTree.gso _ _ _ _ hd.i_n).trans hn, ?_, (PTree.gso _ _ _ _ hd.i_min).trans hmin,
      trivial, harr⟩, by omega, rfl⟩
    rw [PTree.gss]
    simp

/-- The loop: it terminates, and leaves with the minimum of all the
    elements. -/
theorem loop_triple (hd : Distinct) (hpr : permOrder p .Readable = true)
    (hL : (L : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned ofs0 + 4 * (L : _root_.Int) < 18446744073709551616)
    (k : Nat) :
    Sep.Triple ge fe f_minimum (LInv p b ofs0 L f k) loopStmt (LoopR p b ofs0 L f) := by
  refine Sep.triple_loop ge fe f_minimum (LoopR p b ofs0 L f) (LInv p b ofs0 L f)
    (LAfter p b ofs0 L f) _ _ (fun k => ?_) (fun k => ?_) k
  · exact Sep.triple_seq ge fe f_minimum _ (LMid p b ofs0 L f k) _ _ _
      (if_triple ge fe p b ofs0 L f k hL) (body_triple ge fe p b ofs0 L f k hd hpr hL hno)
  · exact Sep.triple_conseq ge fe f_minimum (incr_triple ge fe p b ofs0 L f k hd)
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
      (fun _ _ x => x)

/-- The precondition of the body: the parameters as passed, the array owned. -/
def Pre : Sep.Assn := fun e le hp =>
  e = emptyEnv
  ∧ le.get _a = some (.Vptr b ofs0)
  ∧ le.get _n = some (.Vint (Integers.Int.repr L))
  ∧ arrayU32 p b (Integers.Ptrofs.unsigned ofs0) L f hp

/-- **The body of `minimum`**: for a non-empty array, it returns the minimum
    of the elements and hands the array back. -/
theorem minimum_body (hd : Distinct) (hpr : permOrder p .Readable = true) (hL1 : 1 ≤ L)
    (hL : (L : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned ofs0 + 4 * (L : _root_.Int) < 18446744073709551616) :
    Sep.Triple ge fe f_minimum (Pre p b ofs0 L f) fullBody
      { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no,
        ret := Ret p b ofs0 L f } := by
  -- min = a[0]
  refine Sep.triple_seq_only ge fe f_minimum (Q := fun e le hp =>
      Pre p b ofs0 L f e le hp ∧ le.get _min = some (.Vint (f 0))) ?_ ?_
  · refine Sep.triple_set ge fe f_minimum _ _ _ _ (fun e le hp m hP hag => ?_)
    obtain ⟨he, ha, hn, harr⟩ := hP
    refine ⟨.Vint (f 0), ?_, ⟨he, (PTree.gso _ _ _ _ hd.min_a).trans ha,
      (PTree.gso _ _ _ _ hd.min_n).trans hn, harr⟩, PTree.gss _ _ _⟩
    exact eval_index_array_int (i := 0) hpr harr hag (by omega)
      (EvalExpr.Etempvar _a (tptr tint) _ ha) (EvalExpr.Econst_int _ tint) rfl rfl
      (elemOfs_unsigned ge.genv_cenv ofs0 0 (by omega) (no_ovf_mono _ 0 L (by omega) hno))
  -- i = 0; the loop
  refine Sep.triple_seq ge fe f_minimum _ (Done p b ofs0 L f) _ _ _ ?_ ?_
  · refine Sep.triple_seq_only ge fe f_minimum (Q := LInv p b ofs0 L f L) ?_ ?_
    · refine Sep.triple_set ge fe f_minimum _ _ _ _ (fun e le hp m hP _ => ?_)
      obtain ⟨⟨he, ha, hn, harr⟩, hmin⟩ := hP
      exact ⟨_, EvalExpr.Econst_int _ tint, 0, ⟨he, (PTree.gso _ _ _ _ hd.i_a).trans ha,
        (PTree.gso _ _ _ _ hd.i_n).trans hn, PTree.gss _ _ _,
        (PTree.gso _ _ _ _ hd.i_min).trans hmin, trivial, harr⟩, by omega, by omega⟩
    · exact Sep.triple_conseq ge fe f_minimum (loop_triple ge fe p b ofs0 L f hd hpr hL hno L)
        (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
        (fun _ _ x => x)
  -- return min
  · refine Sep.triple_return ge fe f_minimum _ _ _ (fun e le hp m h _ => ?_)
    obtain ⟨he, hmin, harr⟩ := h
    refine ⟨.Vint (minTo f L), .Vint (minTo f L), m, hp, EvalExpr.Etempvar _min tint _ hmin,
      semCast_int m _, ?_, ⟨rfl, harr⟩, fun _ hdj hag => ⟨hdj, hag⟩⟩
    rw [he]; exact freeList_emptyEnv _ _

/-! ## As a function specification (VST's `minimum_spec`) -/

/-- `minimum_spec`: called with a pointer to an array of `contents.length`
    `int`s, readable with permission `p`, it returns the minimum of `contents`
    and hands the array back. -/
def minimumSpec (p : Permission) (b : Block) (ofs0 : Integers.Ptrofs)
    (contents : List Integers.Int) : Sep.FunSpec where
  tyargs := [tptr tint, tint]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp =>
    vargs = [.Vptr b ofs0, .Vint (Integers.Int.repr contents.length)]
    ∧ arrayU32 p b (Integers.Ptrofs.unsigned ofs0) contents.length (elems contents) hp
  post := fun v hp =>
    v = .Vint (listMin contents)
    ∧ arrayU32 p b (Integers.Ptrofs.unsigned ofs0) contents.length (elems contents) hp
  measure := fun _ => 0

/-- **`minimum` satisfies `minimum_spec`** (VST's `body_min`): the array is
    readable, has between `1` and `Int.max_signed` elements, and fits in the
    address space. -/
theorem minimum_satisfies (contents : List Integers.Int)
    (hpr : permOrder p .Readable = true)
    (hL1 : 1 ≤ contents.length)
    (hL : (contents.length : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned ofs0 + 4 * (contents.length : _root_.Int)
      < 18446744073709551616) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_minimum)
      (minimumSpec p b ofs0 contents)
      [.Vptr b ofs0, .Vint (Integers.Int.repr contents.length)] := by
  obtain ⟨hv, hpar, hdisj⟩ := entry_wf
  refine Sep.satisfies_internal_noVars ge (FunctionEntry2 ge) f_minimum _ _
    (Pre p b ofs0 contents.length (elems contents)) (fun m => ?_) ?_
  · refine ⟨PTree.set _n (.Vint (Integers.Int.repr contents.length))
              (PTree.set _a (.Vptr b ofs0) (createUndefTemps f_minimum.fn_temps)),
            FunctionEntry2.intro hv hpar hdisj (AllocVariables.nil _ _) rfl,
            fun hp hpre => ?_⟩
    obtain ⟨_, harr⟩ := hpre
    exact ⟨rfl, (PTree.gso _ _ _ _ n_ne_a).trans (PTree.gss _ _ _), PTree.gss _ _ _, harr⟩
  · have h := body_eq ▸ minimum_body ge (FunctionEntry2 ge) p b ofs0 contents.length
      (elems contents) idents_distinct hpr hL1 hL hno
    refine Sep.triple_conseq ge (FunctionEntry2 ge) f_minimum h (fun _ _ _ x => x)
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun v hp hr => ?_)
    obtain ⟨hv, harr⟩ := hr
    exact ⟨by rw [hv, minTo_elems_length], harr⟩

end
end VST.Verif.Min
