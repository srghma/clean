/-
  Why the ARM and PowerPC proofs after instruction selection
  (`RTLtyping` subject reduction, `Allocproof`, `Stackingproof`,
  `Selectionproof`, `Asmgenproof`) are not ported: the value layer of the port
  is 64-bit (`Archi.ptr64 = true`), while these targets are 32-bit.  Two
  facts that CompCert's proofs rely on are false over this value layer; they
  are refuted below.

  1. `Op.type_of_operation_sound` (used by `RTLtyping.subject_reduction`,
     hence by `Allocproof`): on ARM and PowerPC `Oaddrstack` has result type
     `Tint`, but it computes a pointer, and a pointer has type `Tlong` (not
     `Tint`) when `Archi.ptr64 = true`.
  2. `SelectOpproof.eval_addressing` / `Selectionproof.eval_load`: the
     fall-back addressing mode `Aindexed 0` computes `Val.add v (Vint 0)`,
     which is `Vundef` for a pointer `v` when `Archi.ptr64 = true`, so a load
     through a computed pointer gets stuck after instruction selection.
  3. `Stackingproof`: storing a pointer in a stack slot of type `Tint`
     (`Locmap.set`) normalizes it with `Val.load_result Mint32`, which drops
     pointers when `Archi.ptr64 = true`.
-/
import CCLib.arm.Op
import CCLib.powerpc.Op
import CCLib.arm.Locations

open CC

namespace ArmPpcPtr64Gap

/-- A pointer has type `Tint` only on 32-bit configurations; the port's value
    layer is 64-bit. -/
theorem vptr_not_tint (b : Block) (o : Integers.Ptrofs) : ¬ Val.HasType (.Vptr b o) .Tint := by
  simp [Val.HasType, Val.hasType, Archi.ptr64]

/-- ARM: `type_of_operation_sound` is false for `Oaddrstack` over the 64-bit
    value layer. -/
theorem arm_type_of_operation_sound_fails (ge : Genv Unit Unit) (b : Block) :
    ¬ ∀ (sp : Val) (op : Arm.Op.Operation) (vl : List Val) (m : Mem)
        (v : Val), op ≠ .Omove → Arm.Op.evalOperation ge sp op vl m = some v →
        Val.HasType v (Arm.Op.typeOfOperation op).2 := by
  intro h
  have := h (.Vptr b 0) (.Oaddrstack 0) [] Mem.empty
    (Val.offsetPtr (.Vptr b 0) 0) (by simp) rfl
  simp [Val.offsetPtr, Arm.Op.typeOfOperation] at this
  exact vptr_not_tint _ _ this

/-- PowerPC: the same for `Oaddrstack`. -/
theorem powerpc_type_of_operation_sound_fails (ge : Genv Unit Unit) (b : Block) :
    ¬ ∀ (sp : Val) (op : PowerPC.Op.Operation) (vl : List Val) (m : Mem)
        (v : Val), op ≠ .Omove → PowerPC.Op.evalOperation ge sp op vl m = some v →
        Val.HasType v (PowerPC.Op.typeOfOperation op).2 := by
  intro h
  have := h (.Vptr b 0) (.Oaddrstack 0) [] Mem.empty
    (Val.offsetPtr (.Vptr b 0) 0) (by simp) rfl
  simp [Val.offsetPtr, PowerPC.Op.typeOfOperation] at this
  exact vptr_not_tint _ _ this

/-- ARM: the fall-back addressing mode `Aindexed 0` turns a pointer into
    `Vundef`. -/
theorem arm_aindexed_zero_ptr (ge : Genv Unit Unit) (sp : Val) (b : Block) (o : Integers.Ptrofs) :
    Arm.Op.evalAddressing ge sp (.Aindexed Integers.Int.zero) [.Vptr b o] = some .Vundef := by
  simp [Arm.Op.evalAddressing, Val.add, Archi.ptr64]

/-- PowerPC: the same. -/
theorem powerpc_aindexed_zero_ptr (ge : Genv Unit Unit) (sp : Val) (b : Block)
    (o : Integers.Ptrofs) :
    PowerPC.Op.evalAddressing ge sp (.Aindexed Integers.Int.zero) [.Vptr b o] = some .Vundef := by
  simp [PowerPC.Op.evalAddressing, Val.add, Archi.ptr64]

/-- ARM: a pointer spilled to a stack slot of type `Tint` is lost. -/
theorem arm_locmap_set_tint_ptr (ls : Arm.Locmap) (b : Block) (o : Integers.Ptrofs) :
    Arm.Locmap.set (.S .Local 0 .Tint) (.Vptr b o) ls (.S .Local 0 .Tint) = .Vundef := by
  simp [Arm.Locmap.set, Val.loadResult, Chunk.ofTyp, Archi.ptr64]

end ArmPpcPtr64Gap
