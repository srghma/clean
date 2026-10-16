/-
  [RISC-V instance of `CCLib/backend/Inlining.lean`: the same development, in
  namespace `CC.RiscV`, over the RISC-V operators, registers and conventions.]

  RTL function inlining — port of `backend/Inlining.v`.

  Ported: `funenv`, `size_fenv`, `add_globdef`, `funenv_program`, the state
  monad and its operations (`initstate`, `set_instr`, `add_instr`,
  `reserve_nodes`, `reserve_regs`, `request_stack`, `ptree_mfold`), contexts
  and the shifting functions (`shiftpos`, `spc`, `sreg`, `sregs`, `sros`,
  `sop`, `saddr`, `sbuiltinarg`, `sbuiltinres`, `initcontext`,
  `callcontext`, `tailcontext`), `add_moves`, `can_inline`,
  `inline_function`, `inline_tail_function`, `inline_return`,
  `expand_instr`, `expand_cfg_rec`, `expand_cfg`, `expand_function`,
  `transf_function`, `transf_fundef`, `transf_program`.

  Differences from Rocq:
  * The OCaml parameters `inlining_info`, `inlining_analysis` and
    `should_inline` are explicit arguments.
  * The state monad is a plain state monad: Rocq's monad also carries the
    proof `sincr s s'` that the state only grows, which is only used in
    proofs.
  * `size_fenv` (`PTree_Properties.cardinal`) is `PTree.card`, the number
    of bound keys, computed structurally; `card_remove_lt` is
    `PTree_Properties.cardinal_remove`.
  * `expand_cfg` is `Fixm size_fenv expand_cfg_rec` in Rocq: well-founded
    recursion on the size of the environment, each inlining removing the
    inlined function from the environment.  Here `expandCfgFuel` recurses
    structurally on a counter `fuel`, and `expandCfg fenv` starts it at
    `PTree.card fenv`.  Each nested inlining removes a bound key, so the
    environment `fenv'` seen with fuel `n` always satisfies
    `PTree.card fenv' ≤ n` (by `card_remove_lt`); in particular when the fuel
    is `0` the environment is empty and no call can be inlined anyway, so
    the fuel never cuts the expansion short.  This keeps the pass reducible
    by `decide`.
  * The proofs (`Inliningspec.v`, `Inliningproof.v`) are not ported.
-/
import CCLib.riscV.RTL
import CCLib.common.MemoryInject
import CCLib.backend.Inlining

namespace CC
namespace RiscV



namespace Inlining

open Op RTL

/-! ## Environment of inlinable functions -/

/-- `Inlining.funenv` -/
abbrev Funenv := PTree RTL.Function

/-- `Inlining.size_fenv` -/
def sizeFenv (fenv : Funenv) : Nat := PTree.card fenv

section FUNENV
variable {Info : Type} (inliningAnalysis : RTL.Program → Info)
  (shouldInline : Info → Ident → RTL.Function → Bool)

/-- `Inlining.add_globdef` -/
def addGlobdef (io : Info) (fenv : Funenv) (idg : Ident × GlobDef RTL.Fundef Unit) : Funenv :=
  match idg with
  | (id, .Gfun (.Internal f)) =>
      if shouldInline io id f then fenv.set id f else fenv.remove id
  | (id, _) => fenv.remove id

/-- `Inlining.funenv_program` -/
def funenvProgram (p : RTL.Program) : Funenv :=
  let io := inliningAnalysis p
  p.prog_defs.foldl (addGlobdef shouldInline io) PTree.empty

end FUNENV

/-! ## State monad -/

/-- `Inlining.state` -/
structure State where
  st_nextreg : Positive
  st_nextnode : Positive
  st_code : RTL.Code
  st_stksize : Z

/-- `Inlining.mon` (without the monotonicity proof). -/
abbrev Mon (A : Type) := StateM State A

/-- `Inlining.initstate` -/
def initstate : State := ⟨.xH, .xH, PTree.empty, 0⟩

/-- `Inlining.set_instr` -/
def setInstr (pc : Node) (i : Instruction) : Mon Unit :=
  modify fun s => { s with st_code := s.st_code.set pc i }

/-- `Inlining.add_instr` -/
def addInstr (i : Instruction) : Mon Node :=
  modifyGet fun s =>
    let pc := s.st_nextnode
    (pc, { s with st_nextnode := pc.succ, st_code := s.st_code.set pc i })

/-- `Inlining.reserve_nodes` -/
def reserveNodes (numnodes : Positive) : Mon Positive :=
  modifyGet fun s => (s.st_nextnode, { s with st_nextnode := s.st_nextnode.add numnodes })

/-- `Inlining.reserve_regs` -/
def reserveRegs (numregs : Positive) : Mon Positive :=
  modifyGet fun s => (s.st_nextreg, { s with st_nextreg := s.st_nextreg.add numregs })

/-- `Inlining.request_stack` -/
def requestStack (sz : Z) : Mon Unit :=
  modify fun s => { s with st_stksize := Max.max s.st_stksize sz }

/-- `Inlining.ptree_mfold` -/
def ptreeMfold {A : Type} (f : Positive → A → Mon Unit) (t : PTree A) : Mon Unit :=
  modify fun s => PTree.fold (fun s1 k v => ((f k v).run s1).2) t s

/-! ## Inlining contexts -/

/-- `Inlining.context` -/
structure Context where
  dpc : Positive
  dreg : Positive
  dstk : Z
  mreg : Positive
  mstk : Z
  retinfo : Option (Node × Reg)

/-- `Inlining.shiftpos` -/
def shiftpos (p amount : Positive) : Positive := Positive.ofNat (p.toNat + amount.toNat - 1)

/-- `Inlining.spc` -/
def spc (ctx : Context) (pc : Node) : Node := shiftpos pc ctx.dpc
/-- `Inlining.sreg` -/
def sreg (ctx : Context) (r : Reg) : Reg := shiftpos r ctx.dreg
/-- `Inlining.sregs` -/
def sregs (ctx : Context) (rl : List Reg) : List Reg := rl.map (sreg ctx)
/-- `Inlining.sros` -/
def sros (ctx : Context) (ros : Sum Reg Ident) : Sum Reg Ident :=
  match ros with
  | .inl r => .inl (sreg ctx r)
  | .inr id => .inr id
/-- `Inlining.sop` -/
def sop (ctx : Context) (op : Operation) : Operation := shiftStackOperation ctx.dstk op
/-- `Inlining.saddr` -/
def saddr (ctx : Context) (addr : Addressing) : Addressing := shiftStackAddressing ctx.dstk addr

/-- `Inlining.sbuiltinarg` -/
def sbuiltinarg (ctx : Context) : BuiltinArg Reg → BuiltinArg Reg
  | .BA x => .BA (sreg ctx x)
  | .BA_loadstack chunk ofs =>
      .BA_loadstack chunk (Integers.Ptrofs.add ofs (Integers.Ptrofs.repr ctx.dstk))
  | .BA_addrstack ofs => .BA_addrstack (Integers.Ptrofs.add ofs (Integers.Ptrofs.repr ctx.dstk))
  | .BA_splitlong hi lo => .BA_splitlong (sbuiltinarg ctx hi) (sbuiltinarg ctx lo)
  | .BA_addptr a1 a2 => .BA_addptr (sbuiltinarg ctx a1) (sbuiltinarg ctx a2)
  | a => a

/-- `Inlining.sbuiltinres` -/
def sbuiltinres (ctx : Context) (a : BuiltinRes Reg) : BuiltinRes Reg :=
  match a with
  | .BR x => .BR (sreg ctx x)
  | _ => .BR_none

/-- `Inlining.initcontext` -/
def initcontext (dpc dreg nreg : Positive) (sz : Z) : Context :=
  { dpc, dreg, dstk := 0, mreg := nreg, mstk := Max.max sz 0, retinfo := none }

/-- `Inlining.callcontext` -/
def callcontext (ctx : Context) (dpc dreg nreg : Positive) (sz : Z) (retpc : Node)
    (retreg : Reg) : Context :=
  { dpc, dreg, dstk := align (ctx.dstk + ctx.mstk) (minSafeAlignment sz), mreg := nreg,
    mstk := Max.max sz 0, retinfo := some (spc ctx retpc, sreg ctx retreg) }

/-- `Inlining.tailcontext` -/
def tailcontext (ctx : Context) (dpc dreg nreg : Positive) (sz : Z) : Context :=
  { dpc, dreg, dstk := align ctx.dstk (minSafeAlignment sz), mreg := nreg,
    mstk := Max.max sz 0, retinfo := ctx.retinfo }

/-! ## Recursive expansion and copying of a CFG -/

/-- `Inlining.add_moves` -/
def addMoves : List Reg → List Reg → Node → Mon Node
  | s1 :: sl, d1 :: dl, succ => do
      let n ← addInstr (.Iop .Omove [s1] d1 succ)
      addMoves sl dl n
  | _, _, succ => pure succ

/-- The recursor of `expand_cfg_rec`: copies a function body in a context,
    under a smaller environment.  `none` when the fuel is exhausted. -/
abbrev Recursor := Option (Funenv → Context → RTL.Function → Mon Unit)

section EXPAND_CFG
variable (fenv : Funenv) (rec : Recursor)

/-- `Inlining.can_inline`: `some (id, f, rec)` if `ros` names a function
    `id ↦ f` of the environment (`Can_inline`), `none` otherwise
    (`Cannot_inline`). -/
def canInline (ros : Sum Reg Ident) :
    Option (Ident × RTL.Function × (Funenv → Context → RTL.Function → Mon Unit)) :=
  match ros, rec with
  | .inr id, some r => (fenv.get id).map fun f => (id, f, r)
  | _, _ => none

/-- `Inlining.inline_function` -/
def inlineFunction (r : Funenv → Context → RTL.Function → Mon Unit) (ctx : Context) (id : Ident)
    (f : RTL.Function) (args : List Reg) (retpc : Node) (retreg : Reg) : Mon Node := do
  let npc := maxPcFunction f
  let nreg := maxRegFunction f
  let dpc ← reserveNodes npc
  let dreg ← reserveRegs nreg
  let ctx' := callcontext ctx dpc dreg nreg f.fn_stacksize retpc retreg
  r (fenv.remove id) ctx' f
  addMoves (sregs ctx args) (sregs ctx' f.fn_params) (spc ctx' f.fn_entrypoint)

/-- `Inlining.inline_tail_function` -/
def inlineTailFunction (r : Funenv → Context → RTL.Function → Mon Unit) (ctx : Context)
    (id : Ident) (f : RTL.Function) (args : List Reg) : Mon Node := do
  let npc := maxPcFunction f
  let nreg := maxRegFunction f
  let dpc ← reserveNodes npc
  let dreg ← reserveRegs nreg
  let ctx' := tailcontext ctx dpc dreg nreg f.fn_stacksize
  r (fenv.remove id) ctx' f
  addMoves (sregs ctx args) (sregs ctx' f.fn_params) (spc ctx' f.fn_entrypoint)

/-- `Inlining.inline_return` -/
def inlineReturn (ctx : Context) (or : Option Reg) (retinfo : Node × Reg) : Instruction :=
  match retinfo, or with
  | (retpc, retreg), some r => .Iop .Omove [sreg ctx r] retreg retpc
  | (retpc, _), none => .Inop retpc

/-- `Inlining.expand_instr` -/
def expandInstr (ctx : Context) (pc : Node) (i : Instruction) : Mon Unit :=
  match i with
  | .Inop s => setInstr (spc ctx pc) (.Inop (spc ctx s))
  | .Iop op args res s =>
      setInstr (spc ctx pc) (.Iop (sop ctx op) (sregs ctx args) (sreg ctx res) (spc ctx s))
  | .Iload chunk addr args dst s =>
      setInstr (spc ctx pc)
        (.Iload chunk (saddr ctx addr) (sregs ctx args) (sreg ctx dst) (spc ctx s))
  | .Istore chunk addr args src s =>
      setInstr (spc ctx pc)
        (.Istore chunk (saddr ctx addr) (sregs ctx args) (sreg ctx src) (spc ctx s))
  | .Icall sg ros args res s =>
      match canInline fenv rec ros with
      | none =>
          setInstr (spc ctx pc)
            (.Icall sg (sros ctx ros) (sregs ctx args) (sreg ctx res) (spc ctx s))
      | some (id, f, r) => do
          let n ← inlineFunction fenv r ctx id f args s res
          setInstr (spc ctx pc) (.Inop n)
  | .Itailcall sg ros args =>
      match canInline fenv rec ros with
      | none =>
          match ctx.retinfo with
          | none => setInstr (spc ctx pc) (.Itailcall sg (sros ctx ros) (sregs ctx args))
          | some (rpc, rreg) =>
              setInstr (spc ctx pc) (.Icall sg (sros ctx ros) (sregs ctx args) rreg rpc)
      | some (id, f, r) => do
          let n ← inlineTailFunction fenv r ctx id f args
          setInstr (spc ctx pc) (.Inop n)
  | .Ibuiltin ef args res s =>
      setInstr (spc ctx pc)
        (.Ibuiltin ef (args.map (sbuiltinarg ctx)) (sbuiltinres ctx res) (spc ctx s))
  | .Icond cond args s1 s2 =>
      setInstr (spc ctx pc) (.Icond cond (sregs ctx args) (spc ctx s1) (spc ctx s2))
  | .Ijumptable r tbl =>
      setInstr (spc ctx pc) (.Ijumptable (sreg ctx r) (tbl.map (spc ctx)))
  | .Ireturn or =>
      match ctx.retinfo with
      | none => setInstr (spc ctx pc) (.Ireturn (or.map (sreg ctx)))
      | some rinfo => setInstr (spc ctx pc) (inlineReturn ctx or rinfo)

/-- `Inlining.expand_cfg_rec` -/
def expandCfgRec (ctx : Context) (f : RTL.Function) : Mon Unit := do
  requestStack (ctx.dstk + ctx.mstk)
  ptreeMfold (expandInstr fenv rec ctx) f.fn_code

end EXPAND_CFG

/-- `expand_cfg` with an explicit recursion counter (see the header). -/
def expandCfgFuel : Nat → Funenv → Context → RTL.Function → Mon Unit
  | 0, fenv => expandCfgRec fenv none
  | n + 1, fenv => expandCfgRec fenv (some (expandCfgFuel n))

/-- `Inlining.expand_cfg` -/
def expandCfg (fenv : Funenv) : Context → RTL.Function → Mon Unit :=
  expandCfgFuel (sizeFenv fenv) fenv

/-- `Inlining.expand_function` -/
def expandFunction (fenv : Funenv) (f : RTL.Function) : Mon Context := do
  let npc := maxPcFunction f
  let nreg := maxRegFunction f
  let dpc ← reserveNodes npc
  let dreg ← reserveRegs nreg
  let ctx := initcontext dpc dreg nreg f.fn_stacksize
  expandCfg fenv ctx f
  pure ctx

/-! ## Inlining in functions and whole programs -/

/-- `Inlining.transf_function` -/
def transfFunction (fenv : Funenv) (f : RTL.Function) : Res RTL.Function :=
  let (ctx, s) := (expandFunction fenv f).run initstate
  if s.st_stksize < Integers.Ptrofs.max_unsigned then
    .OK { fn_sig := f.fn_sig, fn_params := sregs ctx f.fn_params, fn_stacksize := s.st_stksize,
          fn_code := s.st_code, fn_entrypoint := spc ctx f.fn_entrypoint }
  else .Error "Inlining: stack too big"

/-- `Inlining.transf_fundef` -/
def transfFundef (fenv : Funenv) (fd : RTL.Fundef) : Res RTL.Fundef :=
  ASTFundef.transfPartial (transfFunction fenv) fd

section TRANSF
variable {Info : Type} (inliningAnalysis : RTL.Program → Info)
  (shouldInline : Info → Ident → RTL.Function → Bool)

/-- `Inlining.transf_program` -/
def transfProgram (p : RTL.Program) : Res RTL.Program :=
  let fenv := funenvProgram inliningAnalysis shouldInline p
  transformPartialProgram (transfFundef fenv) p

end TRANSF

end Inlining
end RiscV
end CC
