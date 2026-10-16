/-
  [ARM instance of `CCLib/driver/Compiler.lean`.]

  The whole compiler for the ARM target — port of the definitions of
  `driver/Compiler.v` (`transf_rtl_program`, `transf_cminor_program`,
  `transf_clight_program`, `transf_c_program`) with the ARM back end
  (`CCLib/arm/…`).  The front end (CompCert C → Cminor) is the shared one of
  `CCLib/cfrontend/`, and the composition operators `@@`, `@@@`, `totalIf`,
  `partialIf`, `time` are those of `CCLib/driver/Compiler.lean`.

  Differences from Rocq: as in `CCLib/driver/Compiler.lean`, the compiler
  options of `Compopts.v`, the Rocq `Parameter`s of `arm/Archi.v`
  (`big_endian`, `abi`, `thumb2_support`, `hardware_idiv`) and the untrusted
  OCaml components are fields of a `Config` record.  The ARM calling
  convention never needs normalization of small-integer arguments or results
  (`Conventions1.parameter_needs_normalization = false`); the shared front
  end, which is parameterized by an aarch64 `AbiKind`, is therefore run with
  `.Apple`, the ABI kind for which these functions are also constantly
  `false`.

  Caveat: the shared front end and the value layer of the port are 64-bit
  (`Archi.ptr64 = true`), so `transfClightProgram` and `transfCProgram` lay
  out C types with 8-byte pointers, unlike CompCert's ARM configuration.
  `transfRtlProgram` and `transfCminorProgram` are the ARM back end as in
  Rocq.  No correctness theorem is stated for this compiler.
-/
import CCLib.driver.Compiler
import CCLib.arm.Selection
import CCLib.arm.RTLgen
import CCLib.arm.Tailcall
import CCLib.arm.Inlining
import CCLib.arm.Renumber
import CCLib.arm.Constprop
import CCLib.arm.CSE
import CCLib.arm.Deadcode
import CCLib.arm.Unusedglob
import CCLib.arm.Allocation
import CCLib.arm.Tunneling
import CCLib.arm.Linearize
import CCLib.arm.CleanupLabels
import CCLib.arm.Debugvar
import CCLib.arm.Stacking
import CCLib.arm.Asmgen

namespace CC
namespace Arm
namespace Compiler

open CC.Compiler (applyTotal applyPartial time totalIf partialIf)
open CC.Compiler

/-- The ABI kind given to the shared front end: no normalization of
    small-integer arguments and results, as on ARM. -/
def frontendAbi : CC.Conventions1.AbiKind := .Apple

theorem frontendAbi_no_normalization (t : XType) :
    CC.Conventions1.returnValueNeedsNormalization frontendAbi t = false ∧
    CC.Conventions1.parameterNeedsNormalization frontendAbi t = false := ⟨rfl, rfl⟩

/-- Compiler options (`Compopts.v`), target parameters, and the untrusted
    components that CompCert implements outside Rocq (ARM back end). -/
structure Config where
  /-- `Archi.big_endian` -/
  bigEndian : Bool := false
  /-- `Archi.abi`, `Archi.thumb2_support`, `Archi.hardware_idiv` -/
  params : Archi.Arm.Params
  /-- `Compopts.thumb` -/
  thumb : Unit → Bool := fun _ => false
  /-- `Compopts.optim_tailcalls` -/
  optimTailcalls : Bool := true
  /-- `Compopts.optim_constprop` -/
  optimConstprop : Bool := true
  /-- `Compopts.optim_CSE` -/
  optimCSE : Bool := true
  /-- `Compopts.optim_redundancy` -/
  optimRedundancy : Bool := true
  /-- `Compopts.debug` -/
  debug : Bool := false
  /-- `Compopts.optim_for_size` -/
  optimForSize : Bool := false
  /-- `Compopts.va_strict` -/
  vaStrict : Bool := false
  /-- `Compopts.propagate_float_constants` -/
  propagateFloatConstants : Bool := true
  /-- `Compopts.generate_float_constants` -/
  generateFloatConstants : Bool := true
  /-- `SelectOp.symbol_is_relocatable` -/
  symbolIsRelocatable : Ident → Bool := fun _ => false
  /-- `SimplExpr.first_unused_ident` -/
  firstUnusedIdent : Csyntax.Program → Ident
  /-- `Selection.compile_switch` (its result is validated) -/
  compileSwitch : Z → Nat → Switch.Table → Switch.Comptree
  /-- `Selection.if_conversion_heuristic` -/
  ifConversionHeuristic :
    Ident → Cminor.Expr → Cminor.Expr → Cminor.Expr → ATyp → CminorSel.Stmt → Bool :=
    fun _ _ _ _ _ _ => true
  /-- `RTLgen.more_likely` -/
  moreLikely : CminorSel.Condexpr → CminorSel.Stmt → CminorSel.Stmt → Bool :=
    fun _ _ _ => false
  /-- `Inlining.should_inline (inlining_analysis p)` -/
  shouldInline : RTL.Program → Ident → RTL.Function → Bool := fun _ _ _ => false
  /-- `Allocation.regalloc` (its result is validated) -/
  regalloc : RTL.Function → Res LTL.Function
  /-- `Linearize.enumerate_aux` (its result is validated) -/
  enumerateAux : LTL.Function → PMap Bool → List LTL.Node

namespace Config
variable (c : Config)

def vaOptions : CC.ValueAOp.Options :=
  { strict := c.vaStrict, propagateFloatConstants := c.propagateFloatConstants }

def constpropOptions : CC.ConstpropOp.Options :=
  { strict := c.vaStrict, propagateFloatConstants := c.propagateFloatConstants,
    generateFloatConstants := c.generateFloatConstants,
    symbolIsRelocatable := c.symbolIsRelocatable }

def selectionOptions : Selection.Options :=
  { thumb := c.thumb, optimForSize := c.optimForSize,
    compileSwitch := c.compileSwitch, ifConversionHeuristic := c.ifConversionHeuristic }

def simplLocalsOptions : SimplLocals.Options := { debug := c.debug, abi := frontendAbi }

def asmgenOptions : Asmgen.Options := { thumb := c.thumb, params := c.params }
end Config

open Config

variable (c : Config)

/-- `transf_rtl_program`: the back end, from RTL to ARM assembly. -/
def transfRtlProgram (f : RTL.Program) : Res Asm.Program :=
  Res.OK f
   @@ totalIf (fun _ => c.optimTailcalls)
        (time "Tail calls" (Tailcall.transfProgram c.bigEndian c.params.abi))
  @@@ time "Inlining" (Inlining.transfProgram id c.shouldInline)
   @@ time "Renumbering" Renumber.transfProgram
   @@ totalIf (fun _ => c.optimConstprop)
        (time "Constant propagation" (Constprop.transfProgram c.constpropOptions))
   @@ totalIf (fun _ => c.optimConstprop) (time "Renumbering" Renumber.transfProgram)
  @@@ partialIf (fun _ => c.optimCSE) (time "CSE" (CSE.transfProgram c.vaOptions))
  @@@ partialIf (fun _ => c.optimRedundancy)
        (time "Redundancy elimination" (Deadcode.transfProgram c.vaOptions))
  @@@ time "Unused globals" Unusedglob.transformProgram
  @@@ time "Register allocation" (Allocation.transfProgram c.bigEndian c.params c.regalloc)
   @@ time "Branch tunneling" Tunneling.tunnelProgram
  @@@ time "CFG linearization" (Linearize.transfProgram c.enumerateAux)
   @@ time "Label cleanup" CleanupLabels.transfProgram
  @@@ partialIf (fun _ => c.debug)
        (time "Debugging info for local variables" Debugvar.transfProgram)
  @@@ time "Mach generation" (Stacking.transfProgram c.bigEndian c.params.abi)
  @@@ time "Asm generation" (Asmgen.transfProgram c.asmgenOptions)

/-- `transf_cminor_program` -/
def transfCminorProgram (p : Cminor.Program) : Res Asm.Program :=
  Res.OK p
  @@@ time "Instruction selection" (Selection.selProgram c.selectionOptions)
  @@@ time "RTL generation" (RTLgen.translProgram c.moreLikely)
  @@@ transfRtlProgram c

/-- `transf_clight_program` -/
def transfClightProgram (p : Program) : Res Asm.Program :=
  Res.OK p
  @@@ time "Simplification of locals" (SimplLocals.transfProgram c.simplLocalsOptions)
  @@@ time "C#minor generation" (Cshmgen.translProgram (CC.Conventions1.returnValueNeedsNormalization frontendAbi))
  @@@ time "Cminor generation" Cminorgen.translProgram
  @@@ transfCminorProgram c

/-- `transf_c_program`: the whole compiler, from CompCert C to ARM
    assembly. -/
def transfCProgram (p : Csyntax.Program) : Res Asm.Program :=
  Res.OK p
  @@@ time "Clight generation" (SimplExpr.translProgram (c.firstUnusedIdent p))
  @@@ transfClightProgram c

end Compiler
end Arm
end CC
