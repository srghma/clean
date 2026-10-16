/-
  [PowerPC instance of `CCLib/driver/Compiler.lean`.]

  The whole compiler for the PowerPC target — port of the definitions of
  `driver/Compiler.v` (`transf_rtl_program`, `transf_cminor_program`,
  `transf_clight_program`, `transf_c_program`) with the PowerPC back end
  (`CCLib/powerpc/…`).  The front end (CompCert C → Cminor) is the shared one of
  `CCLib/cfrontend/`, and the composition operators `@@`, `@@@`, `totalIf`,
  `partialIf`, `time` are those of `CCLib/driver/Compiler.lean`.

  Differences from Rocq: as in `CCLib/driver/Compiler.lean`, the compiler
  options of `Compopts.v`, the Rocq `Parameter` `Archi.ppc64`, the
  single-precision-argument flag of `Conventions1`, the linker parameters of
  `powerpc/Asm.v` (`low_half`, `high_half`, `symbol_is_small_data`, ...) and the untrusted
  OCaml components are fields of a `Config` record.  The PowerPC calling
  convention never needs normalization of small-integer arguments or results
  (`Conventions1.parameter_needs_normalization = false`); the shared front
  end, which is parameterized by an aarch64 `AbiKind`, is therefore run with
  `.Apple`, the ABI kind for which these functions are also constantly
  `false`.

  Caveat: the shared front end and the value layer of the port are 64-bit
  (`Archi.ptr64 = true`), so `transfClightProgram` and `transfCProgram` lay
  out C types with 8-byte pointers, unlike CompCert's 32-bit PowerPC configuration.
  `transfRtlProgram` and `transfCminorProgram` are the PowerPC back end as in
  Rocq.  No correctness theorem is stated for this compiler.
-/
import CCLib.driver.Compiler
import CCLib.powerpc.Selection
import CCLib.powerpc.RTLgen
import CCLib.powerpc.Tailcall
import CCLib.powerpc.Inlining
import CCLib.powerpc.Renumber
import CCLib.powerpc.Constprop
import CCLib.powerpc.CSE
import CCLib.powerpc.Deadcode
import CCLib.powerpc.Unusedglob
import CCLib.powerpc.Allocation
import CCLib.powerpc.Tunneling
import CCLib.powerpc.Linearize
import CCLib.powerpc.CleanupLabels
import CCLib.powerpc.Debugvar
import CCLib.powerpc.Stacking
import CCLib.powerpc.Asmgen

namespace CC
namespace PowerPC
namespace Compiler

open CC.Compiler (applyTotal applyPartial time totalIf partialIf)
open CC.Compiler

/-- The ABI kind given to the shared front end: no normalization of
    small-integer arguments and results, as on PowerPC. -/
def frontendAbi : CC.Conventions1.AbiKind := .Apple

theorem frontendAbi_no_normalization (t : XType) :
    CC.Conventions1.returnValueNeedsNormalization frontendAbi t = false ∧
    CC.Conventions1.parameterNeedsNormalization frontendAbi t = false := ⟨rfl, rfl⟩

/-- Compiler options (`Compopts.v`), target parameters, and the untrusted
    components that CompCert implements outside Rocq (PowerPC back end). -/
structure Config where
  /-- `Archi.ppc64` -/
  ppc64 : Bool := false
  /-- the single-precision-argument flag of `Conventions1` -/
  sps : Bool := false
  /-- the linker parameters of `powerpc/Asm.v` (`low_half`, `high_half`,
      `symbol_is_small_data`, `small_data_area_offset`, `symbol_is_rel_data`,
      `symbol_is_aligned`) -/
  linker : Asm.LinkerParams
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
  { ppc64 := c.ppc64, optimForSize := c.optimForSize,
    compileSwitch := c.compileSwitch, ifConversionHeuristic := c.ifConversionHeuristic }

def simplLocalsOptions : SimplLocals.Options := { debug := c.debug, abi := frontendAbi }

end Config

open Config

variable (c : Config)

/-- `transf_rtl_program`: the back end, from RTL to PowerPC assembly. -/
def transfRtlProgram (f : RTL.Program) : Res Asm.Program :=
  Res.OK f
   @@ totalIf (fun _ => c.optimTailcalls)
        (time "Tail calls" (Tailcall.transfProgram c.ppc64 c.sps))
  @@@ time "Inlining" (Inlining.transfProgram id c.shouldInline)
   @@ time "Renumbering" Renumber.transfProgram
   @@ totalIf (fun _ => c.optimConstprop)
        (time "Constant propagation" (Constprop.transfProgram c.ppc64 c.constpropOptions))
   @@ totalIf (fun _ => c.optimConstprop) (time "Renumbering" Renumber.transfProgram)
  @@@ partialIf (fun _ => c.optimCSE) (time "CSE" (CSE.transfProgram c.ppc64 c.vaOptions))
  @@@ partialIf (fun _ => c.optimRedundancy)
        (time "Redundancy elimination" (Deadcode.transfProgram c.vaOptions))
  @@@ time "Unused globals" Unusedglob.transformProgram
  @@@ time "Register allocation" (Allocation.transfProgram c.ppc64 c.sps c.regalloc)
   @@ time "Branch tunneling" Tunneling.tunnelProgram
  @@@ time "CFG linearization" (Linearize.transfProgram c.enumerateAux)
   @@ time "Label cleanup" CleanupLabels.transfProgram
  @@@ partialIf (fun _ => c.debug)
        (time "Debugging info for local variables" Debugvar.transfProgram)
  @@@ time "Mach generation" (Stacking.transfProgram c.ppc64 c.sps)
  @@@ time "Asm generation" (Asmgen.transfProgram c.linker)

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

/-- `transf_c_program`: the whole compiler, from CompCert C to PowerPC
    assembly. -/
def transfCProgram (p : Csyntax.Program) : Res Asm.Program :=
  Res.OK p
  @@@ time "Clight generation" (SimplExpr.translProgram (c.firstUnusedIdent p))
  @@@ transfClightProgram c

end Compiler
end PowerPC
end CC
