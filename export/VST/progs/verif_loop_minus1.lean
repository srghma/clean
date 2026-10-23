/-
  Port of VST's `progs/verif_loop_minus1.v`: the `sumarray` of
  `vst/progs/loop_minus1.c`, whose loop counter starts at `-1`
  (`for (i=-1; i< n - 1; i++) s += a[i + 1];`), meets the same specification
  as the `sumarray` of `sumarray.c`.

  VST's specification (identical to the one of `verif_sumarray.v`):

      DECLARE _sumarray
       WITH a: val, sh : share, contents : list Z, size: Z
       PRE [ tptr tuint, tint ]
         PROP  (readable_share sh; 0 <= size <= Int.max_signed)
         PARAMS (a; Vint (Int.repr size))
         SEP   (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a)
       POST [ tuint ]
         PROP () RETURN (Vint (Int.repr (sum_Z contents)))
         SEP (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a).

  The specification, the sum `sumTo`/`listSum` and the element function
  `elems` are those of the port of `verif_sumarray.v`
  (`VST.Verif.Sumarray.sumarraySpec`), so the theorem below states that the
  two C functions satisfy the same specification.

  The proof follows `verif_loop_minus1.v`: the loop invariant says that `s`
  is the sum of the first `i + 1` elements, with `-1 ≤ i ≤ size - 1`; here
  `iv = i + 1` is the number of elements summed.
-/
import VST.progs.loop_minus1
import VST.progs.verif_sumarray
open CC CC.Sep CC.HProp
open Loop_minus1
open VST.Verif.Sumarray (sumTo listSum elems sumTo_elems_length semBinop_add_uint semCast_uint
  sumarraySpec)

namespace VST.Verif.LoopMinus1

/-! ## Facts about the generated program -/

/-- The temporaries `sumarray` writes are distinct from the ones it reads. -/
structure Distinct : Prop where
  i_a : _i ≠ _a
  i_n : _i ≠ _n
  s_a : _s ≠ _a
  s_n : _s ≠ _n
  s_i : _s ≠ _i
  t1_a : _t'1 ≠ _a
  t1_n : _t'1 ≠ _n
  t1_i : _t'1 ≠ _i
  t1_s : _t'1 ≠ _s

theorem idents_distinct : Distinct := by constructor <;> decide

/-- The side conditions of `function_entry2` for `sumarray`. -/
theorem entry_wf :
    listNorepet (varNames f_sumarray.fn_vars)
    ∧ listNorepet (varNames f_sumarray.fn_params)
    ∧ listDisjoint (varNames f_sumarray.fn_params) (varNames f_sumarray.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem n_ne_a : _n ≠ _a := by decide

/-- The parts of the body. -/
def one : Expr := .Econst_int (Integers.Int.repr 1) tint
def setS0 : Stmt := .Sset _s (.Econst_int (Integers.Int.repr 0) tint)
def setIm1 : Stmt := .Sset _i (.Eunop .Oneg one tint)
def guardExpr : Expr :=
  .Ebinop .Olt (.Etempvar _i tint) (.Ebinop .Osub (.Etempvar _n tint) one tint) tint
def ifStmt : Stmt := .Sifthenelse guardExpr .Sskip .Sbreak
def idxExpr : Expr := .Ebinop .Oadd (.Etempvar _i tint) one tint
def setT1 : Stmt :=
  .Sset _t'1 (.Ederef (.Ebinop .Oadd (.Etempvar _a (tptr tuint)) idxExpr (tptr tuint)) tuint)
def setS : Stmt := .Sset _s (.Ebinop .Oadd (.Etempvar _s tuint) (.Etempvar _t'1 tuint) tuint)
def bodyStmt : Stmt := .Ssequence setT1 setS
def incrStmt : Stmt := .Sset _i (.Ebinop .Oadd (.Etempvar _i tint) one tint)
def loopStmt : Stmt := .Sloop (.Ssequence ifStmt bodyStmt) incrStmt
def retStmt : Stmt := .Sreturn (some (.Etempvar _s tuint))
def fullBody : Stmt := .Ssequence setS0 (.Ssequence (.Ssequence setIm1 loopStmt) retStmt)

theorem body_eq : f_sumarray.fn_body = fullBody := rfl

/-! ## Assertions -/

section
variable (p : Permission) (b : Block) (ofs0 : Integers.Ptrofs) (L : Nat)
variable (f : Nat → Integers.Int)

/-- The local state: `a` and `n` as passed, `i = iv - 1`, `s = sv`, `t'1` as
    far as set, and the array owned. -/
def St (iv : Nat) (sv : Integers.Int) (t1 : Option Integers.Int) : Sep.Assn := fun e le hp =>
  e = emptyEnv
  ∧ le.get _a = some (.Vptr b ofs0)
  ∧ le.get _n = some (.Vint (Integers.Int.repr L))
  ∧ le.get _i = some (.Vint (Integers.Int.repr ((iv : _root_.Int) - 1)))
  ∧ le.get _s = some (.Vint sv)
  ∧ (match t1 with | none => True | some x => le.get _t'1 = some (.Vint x))
  ∧ arrayU32 p b (Integers.Ptrofs.unsigned ofs0) L f hp

/-- The loop invariant, `k` iterations left: `s` is the sum of the first
    `i + 1` elements, and `-1 ≤ i ≤ size - 1`. -/
def LInv (k : Nat) : Sep.Assn := fun e le hp =>
  ∃ iv, St p b ofs0 L f iv (sumTo f iv) none e le hp ∧ iv ≤ L ∧ L - iv = k

/-- After the guard: `i < size - 1`. -/
def LMid (k : Nat) : Sep.Assn := fun e le hp =>
  ∃ iv, St p b ofs0 L f iv (sumTo f iv) none e le hp ∧ iv < L ∧ L - iv = k

/-- After the body, before `i++`. -/
def LAfter (k : Nat) : Sep.Assn := fun e le hp =>
  ∃ iv, St p b ofs0 L f iv (sumTo f (iv + 1)) none e le hp ∧ iv < L ∧ L - iv = k

/-- After the loop: `s` is the sum of all the elements. -/
def Done : Sep.Assn := fun e le hp =>
  e = emptyEnv ∧ le.get _s = some (.Vint (sumTo f L))
  ∧ arrayU32 p b (Integers.Ptrofs.unsigned ofs0) L f hp

/-- The postcondition: the sum is returned, and the array handed back. -/
def Ret : Val → HProp := fun v hp =>
  v = .Vint (sumTo f L) ∧ arrayU32 p b (Integers.Ptrofs.unsigned ofs0) L f hp

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

/-- `i + 1`, evaluated: the number of elements already summed. -/
theorem eval_idx (e : Env) (le : TempEnv) (m : Mem) (iv : Nat)
    (hi : le.get _i = some (.Vint (Integers.Int.repr ((iv : _root_.Int) - 1)))) :
    EvalExpr ge e le m idxExpr (.Vint (Integers.Int.repr (iv : _root_.Int))) := by
  have h := EvalExpr.Ebinop (ge := ge) (e := e) (le := le) (m := m) .Oadd _ _ tint _ _ _
    (EvalExpr.Etempvar _i tint _ hi) (EvalExpr.Econst_int (Integers.Int.repr 1) tint)
    (semBinop_add_int _ _ _ _)
  rw [repr_add, show (iv : _root_.Int) - 1 + 1 = (iv : _root_.Int) by omega] at h
  exact h

/-- The guard `i < n - 1`, evaluated. -/
theorem eval_guard (e : Env) (le : TempEnv) (m : Mem) (iv : Nat) (sv : Integers.Int)
    (t1 : Option Integers.Int) (hp : Heap) (hL : (L : _root_.Int) < 2147483648) (hiv : iv ≤ L)
    (hSt : St p b ofs0 L f iv sv t1 e le hp) :
    EvalExpr ge e le m guardExpr (Val.ofBool (decide (iv < L))) := by
  obtain ⟨_, _, hn, hi, _⟩ := hSt
  have hsub := EvalExpr.Ebinop (ge := ge) (e := e) (le := le) (m := m) .Osub _ _ tint _ _ _
    (EvalExpr.Etempvar _n tint _ hn) (EvalExpr.Econst_int (Integers.Int.repr 1) tint)
    (semBinop_sub_int _ _ _ _)
  rw [repr_sub] at hsub
  have h : EvalExpr ge e le m guardExpr
      (Val.ofBool (Integers.Int.lt (Integers.Int.repr ((iv : _root_.Int) - 1))
        (Integers.Int.repr ((L : _root_.Int) - 1)))) :=
    EvalExpr.Ebinop .Olt _ _ _ _ _ _ (EvalExpr.Etempvar _i tint _ hi) hsub
      (semBinop_lt_int _ _ _ _)
  rw [lt_repr_signed _ _ (by omega) (by omega) (by omega) (by omega)] at h
  have hdec : decide ((iv : _root_.Int) - 1 < (L : _root_.Int) - 1) = decide (iv < L) := by
    by_cases hlt : iv < L <;> simp [hlt]
  rw [hdec] at h
  exact h

/-- The `if` at the top of the loop body: continue while `i < n - 1`, break
    out with the sum of all the elements otherwise. -/
theorem if_triple (k : Nat) (hL : (L : _root_.Int) < 2147483648) :
    Sep.Triple ge fe f_sumarray (LInv p b ofs0 L f k) ifStmt
      { IterR p b ofs0 L f k with normal := LMid p b ofs0 L f k } := by
  cases k with
  | zero =>
    refine Sep.triple_if_false ge fe f_sumarray _ _ _ _ _ (fun e le hp m hP _ => ?_) ?_
    · obtain ⟨iv, hSt, hiv, hk⟩ := hP
      refine ⟨_, eval_guard ge p b ofs0 L f e le m iv _ none hp hL hiv hSt, ?_⟩
      have : ¬ iv < L := by omega
      simpa [this, guardExpr, typeof] using boolVal_ofBool_int m false
    · refine Sep.triple_conseq ge fe f_sumarray (Sep.triple_break ge fe f_sumarray _)
        (fun _ _ _ x => x) (fun _ _ _ x => False.elim x) (fun e le hp h => ?_)
        (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)
      obtain ⟨iv, ⟨he, _, _, _, hs, _, harr⟩, hiv, hk⟩ := h
      have : iv = L := by omega
      subst this
      exact ⟨he, hs, harr⟩
  | succ j =>
    refine Sep.triple_if_true ge fe f_sumarray _ _ _ _ _ (fun e le hp m hP _ => ?_) ?_
    · obtain ⟨iv, hSt, hiv, hk⟩ := hP
      refine ⟨_, eval_guard ge p b ofs0 L f e le m iv _ none hp hL hiv hSt, ?_⟩
      have : iv < L := by omega
      simpa [this, guardExpr, typeof] using boolVal_ofBool_int m true
    · refine Sep.triple_fallthrough ge fe f_sumarray _ _ _ _
        (Sep.triple_skip ge fe f_sumarray _) (fun e le hp h => ?_)
      obtain ⟨iv, hSt, hiv, hk⟩ := h
      exact ⟨iv, hSt, by omega, hk⟩

/-- The body: `s += a[i + 1]`. -/
theorem body_triple (k : Nat) (hd : Distinct) (hpr : permOrder p .Readable = true)
    (hL : (L : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned ofs0 + 4 * (L : _root_.Int) < 18446744073709551616) :
    Sep.Triple ge fe f_sumarray (LMid p b ofs0 L f k) bodyStmt (IterR p b ofs0 L f k) := by
  refine Sep.triple_exists ge fe f_sumarray _ _ _ (fun iv => ?_)
  show Sep.Triple ge fe f_sumarray
    (fun e le hp => St p b ofs0 L f iv (sumTo f iv) none e le hp ∧ iv < L ∧ L - iv = k)
    bodyStmt _
  refine Sep.triple_seq_only ge fe f_sumarray (Q := fun e le hp =>
      St p b ofs0 L f iv (sumTo f iv) (some (f iv)) e le hp ∧ iv < L ∧ L - iv = k) ?_ ?_
  · -- t'1 = a[i + 1]
    refine Sep.triple_set ge fe f_sumarray _ _ _ _ (fun e le hp m hP hag => ?_)
    obtain ⟨⟨he, ha, hn, hi, hs, _, harr⟩, hlt, hk⟩ := hP
    refine ⟨.Vint (f iv), ?_, ?_⟩
    · exact eval_index_array hpr harr hag hlt (EvalExpr.Etempvar _a (tptr tuint) _ ha)
        (eval_idx ge e le m iv hi) rfl rfl
        (elemOfs_unsigned ge.genv_cenv ofs0 iv (by omega) (no_ovf_mono _ iv L (by omega) hno))
    · exact ⟨⟨he, (PTree.gso _ _ _ _ hd.t1_a).trans ha, (PTree.gso _ _ _ _ hd.t1_n).trans hn,
        (PTree.gso _ _ _ _ hd.t1_i).trans hi, (PTree.gso _ _ _ _ hd.t1_s).trans hs,
        PTree.gss _ _ _, harr⟩, hlt, hk⟩
  · -- s = s + t'1
    refine Sep.triple_fallthrough ge fe f_sumarray _ _ _ _
      (Sep.triple_set ge fe f_sumarray _ _ _ _ (fun e le hp m hP _ => ?_)) (fun _ _ _ x => x)
    obtain ⟨⟨he, ha, hn, hi, hs, ht1, harr⟩, hlt, hk⟩ := hP
    refine ⟨.Vint (sumTo f (iv + 1)), ?_, ?_⟩
    · exact EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (EvalExpr.Etempvar _s tuint _ hs)
        (EvalExpr.Etempvar _t'1 tuint _ ht1) (semBinop_add_uint _ _ _ _)
    · exact ⟨iv, ⟨he, (PTree.gso _ _ _ _ hd.s_a).trans ha, (PTree.gso _ _ _ _ hd.s_n).trans hn,
        (PTree.gso _ _ _ _ hd.s_i).trans hi, PTree.gss _ _ _, trivial, harr⟩, hlt, hk⟩

/-- `i++`: one iteration fewer is left. -/
theorem incr_triple (k : Nat) (hd : Distinct) :
    Sep.Triple ge fe f_sumarray (LAfter p b ofs0 L f k) incrStmt
      { normal := fun e le hp => ∃ n', n' < k ∧ LInv p b ofs0 L f n' e le hp,
        brk := Done p b ofs0 L f, cont := Sep.Assn.no, ret := Ret p b ofs0 L f } := by
  refine Sep.triple_fallthrough ge fe f_sumarray _ _ _ _
    (Sep.triple_set ge fe f_sumarray _ _ _ _ (fun e le hp m hP _ => ?_)) (fun _ _ _ x => x)
  obtain ⟨iv, ⟨he, ha, hn, hi, hs, _, harr⟩, hlt, hk⟩ := hP
  refine ⟨.Vint (Integers.Int.repr (iv : _root_.Int)), eval_idx ge e le m iv hi, ?_⟩
  refine ⟨L - (iv + 1), by omega, iv + 1, ⟨he, (PTree.gso _ _ _ _ hd.i_a).trans ha,
    (PTree.gso _ _ _ _ hd.i_n).trans hn, ?_, (PTree.gso _ _ _ _ hd.s_i.symm).trans hs,
    trivial, harr⟩, by omega, rfl⟩
  rw [PTree.gss, show (((iv + 1 : Nat) : _root_.Int) - 1) = (iv : _root_.Int) by omega]

/-- The loop: it terminates, and leaves with the sum of all the elements. -/
theorem loop_triple (hd : Distinct) (hpr : permOrder p .Readable = true)
    (hL : (L : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned ofs0 + 4 * (L : _root_.Int) < 18446744073709551616)
    (k : Nat) :
    Sep.Triple ge fe f_sumarray (LInv p b ofs0 L f k) loopStmt (LoopR p b ofs0 L f) := by
  refine Sep.triple_loop ge fe f_sumarray (LoopR p b ofs0 L f) (LInv p b ofs0 L f)
    (LAfter p b ofs0 L f) _ _ (fun k => ?_) (fun k => ?_) k
  · exact Sep.triple_seq ge fe f_sumarray _ (LMid p b ofs0 L f k) _ _ _
      (if_triple ge fe p b ofs0 L f k hL) (body_triple ge fe p b ofs0 L f k hd hpr hL hno)
  · exact Sep.triple_conseq ge fe f_sumarray (incr_triple ge fe p b ofs0 L f k hd)
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
      (fun _ _ x => x)

/-- The precondition of the body: the parameters as passed, the array owned. -/
def Pre : Sep.Assn := fun e le hp =>
  e = emptyEnv
  ∧ le.get _a = some (.Vptr b ofs0)
  ∧ le.get _n = some (.Vint (Integers.Int.repr L))
  ∧ arrayU32 p b (Integers.Ptrofs.unsigned ofs0) L f hp

/-- **The body of `sumarray`** (`loop_minus1.c`): it returns the sum of the
    elements and hands the array back. -/
theorem sumarray_body (hd : Distinct) (hpr : permOrder p .Readable = true)
    (hL : (L : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned ofs0 + 4 * (L : _root_.Int) < 18446744073709551616) :
    Sep.Triple ge fe f_sumarray (Pre p b ofs0 L f) fullBody
      { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no,
        ret := Ret p b ofs0 L f } := by
  -- s = 0
  refine Sep.triple_seq_only ge fe f_sumarray (Q := fun e le hp =>
      Pre p b ofs0 L f e le hp ∧ le.get _s = some (.Vint (Integers.Int.repr 0))) ?_ ?_
  · refine Sep.triple_set ge fe f_sumarray _ _ _ _ (fun e le hp m hP _ => ?_)
    obtain ⟨he, ha, hn, harr⟩ := hP
    exact ⟨_, EvalExpr.Econst_int _ tint, ⟨he, (PTree.gso _ _ _ _ hd.s_a).trans ha,
      (PTree.gso _ _ _ _ hd.s_n).trans hn, harr⟩, PTree.gss _ _ _⟩
  refine Sep.triple_seq ge fe f_sumarray _ (Done p b ofs0 L f) _ _ _ ?_ ?_
  · -- i = -1; the loop
    refine Sep.triple_seq_only ge fe f_sumarray (Q := LInv p b ofs0 L f L) ?_ ?_
    · refine Sep.triple_set ge fe f_sumarray _ _ _ _ (fun e le hp m hP _ => ?_)
      obtain ⟨⟨he, ha, hn, harr⟩, hs⟩ := hP
      refine ⟨.Vint (Integers.Int.repr (((0 : Nat) : _root_.Int) - 1)), ?_, 0,
        ⟨he, (PTree.gso _ _ _ _ hd.i_a).trans ha, (PTree.gso _ _ _ _ hd.i_n).trans hn,
        PTree.gss _ _ _, (PTree.gso _ _ _ _ hd.s_i.symm).trans hs, trivial, harr⟩,
        by omega, by omega⟩
      refine EvalExpr.Eunop .Oneg _ _ _ _ (EvalExpr.Econst_int (Integers.Int.repr 1) tint) ?_
      rw [show typeof one = tint from rfl, semUnop_neg_int, neg_repr_one]
      rfl
    · exact Sep.triple_conseq ge fe f_sumarray
        (loop_triple ge fe p b ofs0 L f hd hpr hL hno L)
        (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
        (fun _ _ x => x)
  · -- return s
    refine Sep.triple_return ge fe f_sumarray _ _ _ (fun e le hp m h _ => ?_)
    obtain ⟨he, hs, harr⟩ := h
    refine ⟨.Vint (sumTo f L), .Vint (sumTo f L), m, hp, EvalExpr.Etempvar _s tuint _ hs,
      semCast_uint m _, ?_, ⟨rfl, harr⟩, fun _ hdj hag => ⟨hdj, hag⟩⟩
    rw [he]; exact freeList_emptyEnv _ _

/-- **The `sumarray` of `loop_minus1.c` satisfies `sumarray_spec`** (VST's
    `body_sumarray` of `verif_loop_minus1.v`), the specification of the
    `sumarray` of `sumarray.c`: the array is readable, its size is at most
    `Int.max_signed`, and it fits in the address space. -/
theorem sumarray_satisfies (contents : List Integers.Int)
    (hpr : permOrder p .Readable = true)
    (hL : (contents.length : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned ofs0 + 4 * (contents.length : _root_.Int)
      < 18446744073709551616) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_sumarray)
      (sumarraySpec p b ofs0 contents)
      [.Vptr b ofs0, .Vint (Integers.Int.repr contents.length)] := by
  obtain ⟨hv, hpar, hdisj⟩ := entry_wf
  refine Sep.satisfies_internal_noVars ge (FunctionEntry2 ge) f_sumarray _ _
    (Pre p b ofs0 contents.length (elems contents)) (fun m => ?_) ?_
  · refine ⟨PTree.set _n (.Vint (Integers.Int.repr contents.length))
              (PTree.set _a (.Vptr b ofs0) (createUndefTemps f_sumarray.fn_temps)),
            FunctionEntry2.intro hv hpar hdisj (AllocVariables.nil _ _) rfl,
            fun hp hpre => ?_⟩
    obtain ⟨_, harr⟩ := hpre
    exact ⟨rfl, (PTree.gso _ _ _ _ n_ne_a).trans (PTree.gss _ _ _), PTree.gss _ _ _, harr⟩
  · have h := body_eq ▸ sumarray_body ge (FunctionEntry2 ge) p b ofs0 contents.length
      (elems contents) idents_distinct hpr hL hno
    refine Sep.triple_conseq ge (FunctionEntry2 ge) f_sumarray h (fun _ _ _ x => x)
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun v hp hr => ?_)
    obtain ⟨hv, harr⟩ := hr
    exact ⟨by rw [hv, sumTo_elems_length], harr⟩

end
end VST.Verif.LoopMinus1
