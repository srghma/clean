/-
  Writing an element of an array of `int`s through a heap fragment:
  `base[idx] = rhs;` at type `int` (the store counterpart of
  `CCLib.logic.HoareArrayInt.eval_index_array_int`).

  The precondition is "a pure fact `Rl` about the local environment and the
  temporaries, and the whole fragment is the array"; the array is split at
  the written index (`arrayU32_split`), the cell is written with
  `triple_assign`, and the array is joined back (`arrayU32_update`).
-/
import CCLib.logic.Aggregate
import CCLib.logic.HoareArrayInt

namespace CC
namespace Sep

open HProp

/-- `arrayU32` only depends on the elements below its length. -/
theorem arrayU32_congr (p : Permission) (b : Block) :
    ∀ (n : Nat) (f g : Nat → Integers.Int) (ofs : _root_.Int),
      (∀ i, i < n → f i = g i) → arrayU32 p b ofs n f = arrayU32 p b ofs n g := by
  intro n
  induction n with
  | zero => intro _ _ _ _; rfl
  | succ n ih =>
    intro f g ofs h
    show mapsto .Mint32 p b ofs (.Vint (f 0)) ∗ arrayU32 p b (ofs + 4) n (fun i => f (i + 1))
      = mapsto .Mint32 p b ofs (.Vint (g 0)) ∗ arrayU32 p b (ofs + 4) n (fun i => g (i + 1))
    rw [h 0 (by omega), ih (fun i => f (i + 1)) (fun i => g (i + 1)) (ofs + 4)
      (fun i hi => h (i + 1) (by omega))]

private theorem no_ovf_le (A : _root_.Int) (i n : Nat) (hin : i ≤ n)
    (h : A + 4 * (n : _root_.Int) < 18446744073709551616) :
    A + 4 * (i : _root_.Int) < 18446744073709551616 := by omega

/-- **Store into an `int` array**: `base[idx] = rhs;` replaces element `i`
of the array by the value of `rhs`.  `base`, `idx` and `rhs` must not read
the array (they are evaluated from the locals described by `Rl`). -/
theorem triple_store_index_int (ge : CGenv) (fe : EntryRel) (f : Function)
    (Rl : Env → TempEnv → Prop) (base idx rhs : Expr)
    (p : Permission) (b : Block) (ofs0 : Integers.Ptrofs) (n i : Nat)
    (g : Nat → Integers.Int) (v : Integers.Int)
    (hpw : permOrder p .Writable = true) (hi : i < n)
    (hn : (n : _root_.Int) < 2147483648)
    (hno : Integers.Ptrofs.unsigned ofs0 + 4 * (n : _root_.Int) < 18446744073709551616)
    (hbase : ∀ e le m, Rl e le → EvalExpr ge e le m base (.Vptr b ofs0))
    (hidx : ∀ e le m, Rl e le → EvalExpr ge e le m idx (.Vint (Integers.Int.repr i)))
    (hrhs : ∀ e le m, Rl e le → EvalExpr ge e le m rhs (.Vint v))
    (htyb : typeof base = tptr tint) (hty : typeof idx = tint) (htyr : typeof rhs = tint) :
    Triple ge fe f
      (fun e le hp => Rl e le ∧ arrayU32 p b (Integers.Ptrofs.unsigned ofs0) n g hp)
      (.Sassign (.Ederef (.Ebinop .Oadd base idx (tptr tint)) tint) rhs)
      (.only (fun e le hp => Rl e le
        ∧ arrayU32 p b (Integers.Ptrofs.unsigned ofs0) n (fun j => if j = i then v else g j) hp)) := by
  have haddr : Integers.Ptrofs.unsigned (elemOfs ge.genv_cenv ofs0 (Integers.Int.repr i))
      = Integers.Ptrofs.unsigned ofs0 + 4 * (i : _root_.Int) :=
    elemOfs_unsigned ge.genv_cenv ofs0 i (by omega) (no_ovf_le _ i n (by omega) hno)
  refine triple_assign ge fe f _ _ _ _ .Mint32 p b
    (elemOfs ge.genv_cenv ofs0 (Integers.Int.repr i)) hpw rfl ?_
  intro e le hp m hP _
  obtain ⟨hR, harr⟩ := hP
  rw [arrayU32_split p b _ n g i hi] at harr
  obtain ⟨h1, h2, hd12, heq, hm1, hrest⟩ := harr
  refine ⟨.Vint (g i), .Vint v, h1, h2, hd12, heq, by rw [haddr]; exact hm1, ?_, ?_, ?_⟩
  · have hadd : Cop.semBinaryOperation ge.genv_cenv .Oadd (.Vptr b ofs0) (typeof base)
        (.Vint (Integers.Int.repr i)) (typeof idx) m
        = some (.Vptr b (elemOfs ge.genv_cenv ofs0 (Integers.Int.repr i))) := by
      rw [hty, htyb]; exact semAdd_elem_int _ _ _ _ _
    exact EvalLvalue.Ederef _ _ _ _
      (EvalExpr.Ebinop .Oadd _ _ _ _ _ _ (hbase e le m hR) (hidx e le m hR) hadd)
  · refine ⟨.Vint v, hrhs e le m hR, ?_⟩
    rw [htyr]; exact semCast_int m v
  · intro h1' hm1' hd1'
    refine ⟨hR, ?_⟩
    rw [arrayU32_update p b _ n g i v hi]
    exact ⟨h1', h2, hd1', rfl, by rw [haddr] at hm1'; exact hm1', hrest⟩

end Sep
end CC
