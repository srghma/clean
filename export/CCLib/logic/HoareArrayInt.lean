/-
  Reading an element of an array of signed `int`s through a heap fragment
  (`base[idx]` at type `int`).

  `arrayU32` describes `n` 32-bit words, whatever their C signedness: an
  `int` array and an `unsigned int` array have the same bytes and are both
  read with the chunk `Mint32`.  `CCLib.logic.SepHoareCore.eval_index_array`
  is the `unsigned int` case; this module gives the `int` case, and the
  signed-`int` arithmetic facts (negative values included) that loops over
  such arrays need.
-/
import CCLib.logic.SepHoareCore

namespace CC
namespace Sep

/-- `Cop.sem_add` of a pointer to `int` and an `int` index: the element
address `elemOfs`. -/
theorem semAdd_elem_int (cenv : CompositeEnv) (m : Mem) (b : Block)
    (ofs0 : Integers.Ptrofs) (iv : Integers.Int) :
    Cop.semBinaryOperation cenv .Oadd (.Vptr b ofs0) (tptr tint) (.Vint iv) tint m
      = some (.Vptr b (elemOfs cenv ofs0 iv)) := by
  simp [Cop.semBinaryOperation, Cop.semAdd, Cop.classifyAdd, typeconv,
        removeAttributes, tattr, tptr, tuint, tint, Cop.semAddPtrInt, elemOfs, sizeof]

/-- Evaluating `base[idx]` for an `int` array the fragment owns. -/
theorem eval_index_array_int {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem}
    {p : Permission} {b : Block} {ofs0 : Integers.Ptrofs} {n : Nat}
    {f : Nat → Integers.Int} {h : Heap} {base idx : Expr} {i : Nat}
    (hpr : permOrder p .Readable = true)
    (harr : arrayU32 p b (Integers.Ptrofs.unsigned ofs0) n f h)
    (hag : Heap.Agrees h m) (hi : i < n)
    (hptr : EvalExpr ge e le m base (.Vptr b ofs0))
    (hidx : EvalExpr ge e le m idx (.Vint (Integers.Int.repr i)))
    (htyb : typeof base = tptr tint) (hty : typeof idx = tint)
    (haddr : Integers.Ptrofs.unsigned
               (elemOfs ge.genv_cenv ofs0 (Integers.Int.repr i))
             = Integers.Ptrofs.unsigned ofs0 + 4 * (i : _root_.Int)) :
    EvalExpr ge e le m
      (.Ederef (.Ebinop .Oadd base idx (tptr tint)) tint) (.Vint (f i)) := by
  have hadd : Cop.semBinaryOperation ge.genv_cenv .Oadd (.Vptr b ofs0) (typeof base)
                (.Vint (Integers.Int.repr i)) (typeof idx) m
              = some (.Vptr b (elemOfs ge.genv_cenv ofs0 (Integers.Int.repr i))) := by
    rw [hty, htyb]; exact semAdd_elem_int _ _ _ _ _
  refine EvalExpr.Elvalue _ b (elemOfs ge.genv_cenv ofs0 (Integers.Int.repr i)) .Full _
    (EvalLvalue.Ederef _ _ _ _
      (EvalExpr.Ebinop .Oadd _ _ _ (.Vptr b ofs0) (.Vint (Integers.Int.repr i)) _
        hptr hidx hadd)) ?_
  refine DerefLoc.value .Mint32 _ rfl ?_
  rw [Mem.loadv_ptr _ _ _ _ (Or.inl rfl), haddr]
  exact arrayU32_load p b hpr n f i hi (Integers.Ptrofs.unsigned ofs0) h m harr hag

/-- `Cop.sem_cast` from `int` to `int` is the identity. -/
theorem semCast_int (m : Mem) (v : Integers.Int) :
    Cop.semCast (.Vint v) tint tint m = some (.Vint v) := by
  simp [Cop.semCast, Cop.classifyCast, tint, Archi.ptr64]

/-! ## Signed `int` arithmetic on `repr` -/

/-- `repr` is injective on the signed range, negative values included
(`toInt_repr` is the non-negative case). -/
theorem toInt_repr_signed (i : _root_.Int) (h1 : -2147483648 ≤ i) (h2 : i < 2147483648) :
    (Integers.Int.repr i).toInt = i := by
  show (BitVec.ofInt 32 i).toInt = i
  rw [BitVec.toInt_ofInt]
  exact Int.bmod_eq_of_le (by simp; omega) (by simp; omega)

/-- Signed `<` on `repr` of two values of the signed range is `<` on `Z`. -/
theorem lt_repr_signed (i j : _root_.Int) (hi1 : -2147483648 ≤ i) (hi2 : i < 2147483648)
    (hj1 : -2147483648 ≤ j) (hj2 : j < 2147483648) :
    Integers.Int.lt (Integers.Int.repr i) (Integers.Int.repr j) = decide (i < j) := by
  show BitVec.slt _ _ = _
  rw [BitVec.slt_eq_decide, toInt_repr_signed i hi1 hi2, toInt_repr_signed j hj1 hj2]

theorem neg_repr_one : Integers.Int.neg (Integers.Int.repr 1) = Integers.Int.repr (-1) := by
  decide

/-- `Cop.sem_unary_operation Oneg` at `int`. -/
theorem semUnop_neg_int (m : Mem) (x : Integers.Int) :
    Cop.semUnaryOperation .Oneg (.Vint x) tint m = some (.Vint (Integers.Int.neg x)) := by
  simp [Cop.semUnaryOperation, Cop.semNeg, Cop.classifyNeg, tint]

end Sep
end CC
