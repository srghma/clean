/-
  Translation from Clight to Csharpminor: semantic preservation — port of
  `cfrontend/Cshmgenproof.v`, part 3: the relational specification of the
  translation of function definitions (`match_fundef`), properties of the
  translation functions (`transl_fundef_sig1/2`, `transl_lbl_stmt_1/2`), the
  global-environment lemmas of section `CORRECTNESS` (`symbols_preserved`,
  `functions_translated`, …), and the matching between Clight and
  Csharpminor local environments (`match_env` and its lemmas).

  Differences from Rocq:
  * whole-program statement: the "compilation unit" of every function is the
    program itself, so the composite environment used by the translation is
    `prog.prog_comp_env` throughout and `linkorder` hypotheses disappear;
  * the port's `PTree` is not canonical, so `match_env_same_blocks` is proved
    from a new lemma `elements_rel` (two trees with related bindings list them
    in the same order) instead of `PTree.elements_canonical_order`.
-/
import CCLib.cfrontend.CshmgenproofOps2
import CCLib.common.GlobalenvsTransf
import CCLib.cfrontend.ClightBehaviors

namespace CC
namespace Cshmgen

open Conventions1 (AbiKind)

/-! ## Relational specification of the translation of function definitions -/

/-- `Cshmgenproof.match_fundef` (for the whole program: `ce` is its composite
    environment). -/
inductive MatchFundef (rvNorm : XType → Bool) (ce : CompositeEnv) : FunDef → Csharpminor.Fundef → Prop where
  | internal (f tf) : translFunction rvNorm ce f = .OK tf → MatchFundef rvNorm ce (.Internal f) (.Internal tf)
  | external (ef args res cc) : ef.sig = signatureOfType args res cc →
      MatchFundef rvNorm ce (.External ef args res cc) (.External ef)

theorem translFundef_match {rvNorm : XType → Bool} {ce : CompositeEnv} {id : Ident} {f : FunDef}
    {tf : Csharpminor.Fundef} (h : translFundef rvNorm ce id f = .OK tf) : MatchFundef rvNorm ce f tf := by
  cases f with
  | Internal g =>
    simp only [translFundef, res_bind_eq_OK] at h
    obtain ⟨tg, htg, h⟩ := h
    cases h; exact .internal _ _ htg
  | External ef args res cc =>
    simp only [translFundef] at h
    split at h
    · cases h; exact .external _ _ _ _ ‹_›
    · cases h

/-- `Cshmgenproof.transf_program_match` -/
theorem transf_program_match {rvNorm : XType → Bool} {prog : Program} {tprog : Csharpminor.Program}
    (h : translProgram rvNorm prog = .OK tprog) :
    MatchProgram (MatchFundef rvNorm prog.prog_comp_env) (fun _ _ => True) prog.toAST tprog := by
  have hm := match_transform_partial_program2 h
  exact ⟨hm.defs.imp (fun f tf ⟨_, hf⟩ => translFundef_match hf) (fun _ _ _ => trivial),
    hm.main_eq, hm.public_eq⟩

/-! ## Properties of operations over types -/

/-- `Cshmgenproof.transl_fundef_sig1` -/
theorem transl_fundef_sig1 {rvNorm : XType → Bool} {ce : CompositeEnv} {f : FunDef}
    {tf : Csharpminor.Fundef} {args : List Ty} {res : Ty} {cc : CallConv}
    (h : MatchFundef rvNorm ce f tf) (hc : Cop.classifyFun (typeOfFundef f) = .f args res cc) :
    Csharpminor.funsig tf = signatureOfType args res cc := by
  cases h with
  | internal f tf htr =>
    simp only [translFunction, res_bind_eq_OK] at htr
    obtain ⟨_, _, _, _, htr⟩ := htr
    cases htr
    simp only [typeOfFundef, typeOfFunction, Cop.classifyFun] at hc
    cases hc
    rfl
  | external ef args' res' cc' hsig =>
    simp only [typeOfFundef, Cop.classifyFun] at hc
    cases hc
    exact hsig

/-- `Cshmgenproof.transl_fundef_sig2` -/
theorem transl_fundef_sig2 {rvNorm : XType → Bool} {ce : CompositeEnv} {f : FunDef}
    {tf : Csharpminor.Fundef} {args : List Ty} {res : Ty} {cc : CallConv}
    (h : MatchFundef rvNorm ce f tf) (ht : typeOfFundef f = .Tfunction args res cc) :
    Csharpminor.funsig tf = signatureOfType args res cc :=
  transl_fundef_sig1 h (by rw [ht]; rfl)

/-- `Cshmgenproof.transl_alignof` (whole-program version). -/
theorem transl_alignof {ce : CompositeEnv} {t : Ty} {al : Z} (h : alignof ce t = .OK al) :
    al = CC.alignof ce t := by
  unfold alignof at h; split at h <;> cases h; rfl

/-! ## Properties of labeled statements -/

section LBL
variable {rvNorm : XType → Bool} {ce : CompositeEnv} {tyret : Ty} {nbrk ncnt : Nat}

theorem transl_lbl_stmt_default :
    ∀ {sl : LStmts} {tsl : Csharpminor.LblStmt},
    translLblStmt rvNorm ce tyret nbrk ncnt sl = .OK tsl →
    translLblStmt rvNorm ce tyret nbrk ncnt (selectSwitchDefault sl) =
      .OK (Csharpminor.selectSwitchDefault tsl)
  | .LSnil, _, h => by simp only [translLblStmt] at h; cases h; rfl
  | .LScons o s sl, _, h => by
    simp only [translLblStmt, res_bind_eq_OK] at h
    obtain ⟨ts, hts, tsl', htsl', h⟩ := h
    cases h
    cases o with
    | none => simp only [selectSwitchDefault, Csharpminor.selectSwitchDefault, translLblStmt, hts,
        htsl']; rfl
    | some c =>
      simp only [selectSwitchDefault, Csharpminor.selectSwitchDefault]
      exact transl_lbl_stmt_default htsl'

theorem transl_lbl_stmt_case (n : Z) :
    ∀ {sl : LStmts} {tsl : Csharpminor.LblStmt},
    translLblStmt rvNorm ce tyret nbrk ncnt sl = .OK tsl →
    match selectSwitchCase n sl with
    | none => Csharpminor.selectSwitchCase n tsl = none
    | some sl' => ∃ tsl', Csharpminor.selectSwitchCase n tsl = some tsl' ∧
        translLblStmt rvNorm ce tyret nbrk ncnt sl' = .OK tsl'
  | .LSnil, _, h => by simp only [translLblStmt] at h; cases h; rfl
  | .LScons o s sl, _, h => by
    simp only [translLblStmt, res_bind_eq_OK] at h
    obtain ⟨ts, hts, tsl', htsl', h⟩ := h
    cases h
    cases o with
    | none =>
      simp only [selectSwitchCase, Csharpminor.selectSwitchCase]
      exact transl_lbl_stmt_case n htsl'
    | some c =>
      simp only [selectSwitchCase, Csharpminor.selectSwitchCase]
      by_cases hc : c = n
      · simp only [hc, if_true]
        exact ⟨_, rfl, by simp only [translLblStmt, hts, htsl']; rfl⟩
      · simp only [hc, if_false]; exact transl_lbl_stmt_case n htsl'

/-- `Cshmgenproof.transl_lbl_stmt_1` -/
theorem transl_lbl_stmt_1 (n : Z) {sl : LStmts} {tsl : Csharpminor.LblStmt}
    (h : translLblStmt rvNorm ce tyret nbrk ncnt sl = .OK tsl) :
    translLblStmt rvNorm ce tyret nbrk ncnt (selectSwitch n sl) =
      .OK (Csharpminor.selectSwitch n tsl) := by
  have hc := transl_lbl_stmt_case n h
  unfold selectSwitch Csharpminor.selectSwitch
  revert hc
  cases selectSwitchCase n sl with
  | none => intro hc; simp only at hc; rw [hc]; exact transl_lbl_stmt_default h
  | some sl' =>
    intro hc
    obtain ⟨tsl', h1, h2⟩ := hc
    rw [h1]; exact h2

/-- `Cshmgenproof.transl_lbl_stmt_2` -/
theorem transl_lbl_stmt_2 :
    ∀ {sl : LStmts} {tsl : Csharpminor.LblStmt},
    translLblStmt rvNorm ce tyret nbrk ncnt sl = .OK tsl →
    translStatement rvNorm ce tyret nbrk ncnt (seqOfLabeledStatement sl) =
      .OK (Csharpminor.seqOfLblStmt tsl)
  | .LSnil, _, h => by simp only [translLblStmt] at h; cases h; rfl
  | .LScons o s sl, _, h => by
    simp only [translLblStmt, res_bind_eq_OK] at h
    obtain ⟨ts, hts, tsl', htsl', h⟩ := h
    cases h
    simp only [seqOfLabeledStatement, Csharpminor.seqOfLblStmt, translStatement, hts,
      transl_lbl_stmt_2 htsl']
    rfl

end LBL

/-! ## Trees with related bindings list them in the same order -/

namespace PTree
variable {A B : Type}

theorem elemsAux_empty {t : PTree A} (h : ∀ i, PTree.get i t = none) (rp : List Bool)
    (acc : List (Positive × A)) : PTree.elemsAux t rp acc = acc := by
  induction t generalizing rp acc with
  | Leaf => rfl
  | Node l o r ihl ihr =>
    have ho : o = none := h .xH
    subst ho
    simp only [PTree.elemsAux]
    rw [ihr (fun i => h (.xI i)), ihl (fun i => h (.xO i))]

/-- Two trees whose bindings are related by `R`, key by key, list them in the
    same order (replaces `PTree.elements_canonical_order`): stated through any
    pair of maps that agree on related bindings. -/
theorem elemsAux_rel {C : Type} {R : A → B → Prop} (g1 : Positive × A → C) (g2 : Positive × B → C)
    (hg : ∀ k x y, R x y → g1 (k, x) = g2 (k, y)) :
    ∀ (t1 : PTree A) (t2 : PTree B),
    (∀ i x, PTree.get i t1 = some x → ∃ y, PTree.get i t2 = some y ∧ R x y) →
    (∀ i y, PTree.get i t2 = some y → ∃ x, PTree.get i t1 = some x ∧ R x y) →
    ∀ (rp : List Bool) (acc1 : List (Positive × A)) (acc2 : List (Positive × B)),
    acc1.map g1 = acc2.map g2 →
    (PTree.elemsAux t1 rp acc1).map g1 = (PTree.elemsAux t2 rp acc2).map g2
  | .Leaf, t2, _, h21, rp, acc1, acc2, hacc => by
    rw [elemsAux_empty (t := t2) (fun i => by
      cases h : PTree.get i t2 with
      | none => rfl
      | some y => obtain ⟨x, hx, _⟩ := h21 i y h; simp at hx)]
    exact hacc
  | .Node l1 o1 r1, .Leaf, h12, _, rp, acc1, acc2, hacc => by
    rw [elemsAux_empty (t := .Node l1 o1 r1) (fun i => by
      cases h : PTree.get i (.Node l1 o1 r1) with
      | none => rfl
      | some x => obtain ⟨y, hy, _⟩ := h12 i x h; simp at hy)]
    exact hacc
  | .Node l1 o1 r1, .Node l2 o2 r2, h12, h21, rp, acc1, acc2, hacc => by
    simp only [PTree.elemsAux]
    apply elemsAux_rel g1 g2 hg l1 l2 (fun i x h => h12 (.xO i) x h) (fun i y h => h21 (.xO i) y h)
    have hr := elemsAux_rel g1 g2 hg r1 r2 (fun i x h => h12 (.xI i) x h)
      (fun i y h => h21 (.xI i) y h) (true :: rp) acc1 acc2 hacc
    cases o1 with
    | none =>
      cases o2 with
      | none => exact hr
      | some y => obtain ⟨x, hx, _⟩ := h21 .xH y rfl; cases hx
    | some x =>
      obtain ⟨y, hy, hxy⟩ := h12 .xH x rfl
      cases hy
      simp only [List.map_cons, hr, hg _ _ _ hxy]

theorem elements_rel {C : Type} {R : A → B → Prop} (g1 : Positive × A → C) (g2 : Positive × B → C)
    (hg : ∀ k x y, R x y → g1 (k, x) = g2 (k, y)) (t1 : PTree A) (t2 : PTree B)
    (h12 : ∀ i x, PTree.get i t1 = some x → ∃ y, PTree.get i t2 = some y ∧ R x y)
    (h21 : ∀ i y, PTree.get i t2 = some y → ∃ x, PTree.get i t1 = some x ∧ R x y) :
    (PTree.elements t1).map g1 = (PTree.elements t2).map g2 :=
  elemsAux_rel g1 g2 hg t1 t2 h12 h21 [] [] [] rfl

end PTree

/-! ## Matching between environments -/

/-- `Cshmgenproof.match_env` -/
structure MatchEnv (ce : CompositeEnv) (e : Env) (te : Csharpminor.Env) : Prop where
  me_local : ∀ id b ty, e.get id = some (b, ty) → te.get id = some (b, CC.sizeof ce ty)
  me_local_inv : ∀ id b sz, te.get id = some (b, sz) → ∃ ty, e.get id = some (b, ty)

section MATCH_ENV
variable {ce : CompositeEnv}

/-- `Cshmgenproof.match_env_globals` -/
theorem match_env_globals {e : Env} {te : Csharpminor.Env} {id : Ident} (h : MatchEnv ce e te)
    (he : e.get id = none) : te.get id = none := by
  cases ht : te.get id with
  | none => rfl
  | some p =>
    obtain ⟨b, sz⟩ := p
    obtain ⟨ty, hty⟩ := h.me_local_inv id b sz ht
    rw [he] at hty; cases hty

/-- `Cshmgenproof.match_env_same_blocks` -/
theorem match_env_same_blocks {e : Env} {te : Csharpminor.Env} (h : MatchEnv ce e te) :
    Csharpminor.blocksOfEnv te = blocksOfEnv ce e := by
  unfold Csharpminor.blocksOfEnv blocksOfEnv
  symm
  refine PTree.elements_rel (R := fun (x : Block × Ty) (y : Block × Z) =>
      y.1 = x.1 ∧ y.2 = CC.sizeof ce x.2) (blockOfBinding ce) Csharpminor.blockOfBinding
    ?_ e te (fun i x hx => ⟨_, h.me_local i x.1 x.2 hx, rfl, rfl⟩) ?_
  · intro k x y ⟨h1, h2⟩
    simp only [blockOfBinding, Csharpminor.blockOfBinding, h1, h2]
  · intro i y hy
    obtain ⟨ty, hty⟩ := h.me_local_inv i y.1 y.2 hy
    have := h.me_local i y.1 ty hty
    rw [hy] at this
    have h2 := congrArg Prod.snd (Option.some.inj this)
    exact ⟨_, hty, rfl, h2⟩

/-- `Cshmgenproof.match_env_free_blocks` -/
theorem match_env_free_blocks {e : Env} {te : Csharpminor.Env} {m m' : Mem}
    (h : MatchEnv ce e te) (hf : Mem.freeList m (blocksOfEnv ce e) = some m') :
    Mem.freeList m (Csharpminor.blocksOfEnv te) = some m' := by
  rw [match_env_same_blocks h]; exact hf

/-- `Cshmgenproof.match_env_empty` -/
theorem match_env_empty : MatchEnv ce emptyEnv Csharpminor.emptyEnv :=
  ⟨fun id b ty h => by simp [emptyEnv] at h, fun id b sz h => by simp [Csharpminor.emptyEnv] at h⟩

/-- `Cshmgenproof.match_env_alloc_variables` -/
theorem match_env_alloc_variables {e1 : Env} {m1 : Mem} {vars : List (Ident × Ty)} {e2 : Env}
    {m2 : Mem} (h : AllocVariables ce e1 m1 vars e2 m2) :
    ∀ {tvars : List (Ident × Z)} {te1 : Csharpminor.Env}, mmap (translVar ce) vars = .OK tvars →
    MatchEnv ce e1 te1 →
    ∃ te2, Csharpminor.AllocVariables te1 m1 tvars te2 m2 ∧ MatchEnv ce e2 te2 := by
  induction h with
  | nil e m =>
    intro tvars te1 htr hme
    simp only [mmap] at htr; cases htr
    exact ⟨te1, .nil _ _, hme⟩
  | cons e m id ty vars m1 b1 m2 e2 halloc _ ih =>
    intro tvars te1 htr hme
    simp only [mmap, res_bind_eq_OK] at htr
    obtain ⟨y, hy, ys, hys, htr⟩ := htr
    cases htr
    simp only [translVar, res_bind_eq_OK] at hy
    obtain ⟨sz, hsz, hy⟩ := hy
    cases hy
    rw [transl_sizeof hsz]
    obtain ⟨te2, A, B⟩ := ih (te1 := PTree.set id (b1, CC.sizeof ce ty) te1) hys
      ⟨fun id0 b ty0 h0 => by
        rw [PTree.gsspec] at h0 ⊢
        split
        · next hid => rw [if_pos hid] at h0; cases h0; rfl
        · next hid => rw [if_neg hid] at h0; exact hme.me_local _ _ _ h0,
       fun id0 b sz h0 => by
        rw [PTree.gsspec] at h0 ⊢
        split
        · next hid => rw [if_pos hid] at h0; cases h0; exact ⟨ty, rfl⟩
        · next hid => rw [if_neg hid] at h0; exact hme.me_local_inv _ _ _ h0⟩
    exact ⟨te2, .cons _ _ _ _ _ _ _ _ _ halloc A, B⟩

/-- `Cshmgenproof.create_undef_temps_match` -/
theorem create_undef_temps_match :
    ∀ temps : List (Ident × Ty),
    Csharpminor.createUndefTemps (temps.map (·.1)) = createUndefTemps temps
  | [] => rfl
  | (id, ty) :: temps => by
    simp only [List.map_cons, Csharpminor.createUndefTemps, createUndefTemps,
      create_undef_temps_match temps]

/-- `Cshmgenproof.bind_parameter_temps_match` -/
theorem bind_parameter_temps_match :
    ∀ (vars : List (Ident × Ty)) (vals : List Val) (le1 le2 : TempEnv),
    bindParameterTemps vars vals le1 = some le2 →
    Csharpminor.bindParameters (vars.map (·.1)) vals le1 = some le2
  | [], [], _, _, h => h
  | [], _ :: _, _, _, h => by simp [bindParameterTemps] at h
  | (_, _) :: _, [], _, _, h => by simp [bindParameterTemps] at h
  | (id, ty) :: vars, v :: vals, le1, le2, h => by
    simp only [bindParameterTemps] at h
    exact bind_parameter_temps_match vars vals _ _ h

/-- `Cshmgenproof.transl_vars_names` -/
theorem transl_vars_names :
    ∀ {vars : List (Ident × Ty)} {tvars : List (Ident × Z)},
    mmap (translVar ce) vars = .OK tvars → tvars.map Prod.fst = varNames vars
  | [], _, h => by simp only [mmap] at h; cases h; rfl
  | (id, ty) :: vars, _, h => by
    simp only [mmap, res_bind_eq_OK] at h
    obtain ⟨y, hy, ys, hys, h⟩ := h
    cases h
    simp only [translVar, res_bind_eq_OK] at hy
    obtain ⟨sz, _, hy⟩ := hy
    cases hy
    simp only [List.map_cons]
    rw [transl_vars_names hys]; rfl

end MATCH_ENV

/-! ## Global environments -/

section GENV
variable {rvNorm : XType → Bool} {prog : Program} {tprog : Csharpminor.Program}
  (TRANSL : MatchProgram (MatchFundef rvNorm prog.prog_comp_env) (fun _ _ => True) prog.toAST tprog)
include TRANSL

/-- `Cshmgenproof.symbols_preserved` -/
theorem symbols_preserved (s : Ident) :
    Genv.findSymbol tprog.globalenv s = Genv.findSymbol prog.globalenv.genv_genv s :=
  TRANSL.find_symbol s

/-- `Cshmgenproof.senv_preserved` (an equality of symbol environments). -/
theorem senv_preserved : Genv.toSenv tprog.globalenv = Genv.toSenv prog.globalenv.genv_genv :=
  TRANSL.senv

/-- `Cshmgenproof.function_ptr_translated` -/
theorem function_ptr_translated {b : Block} {f : FunDef}
    (h : Genv.findFunctPtr prog.globalenv.genv_genv b = some f) :
    ∃ tf, Genv.findFunctPtr tprog.globalenv b = some tf ∧ MatchFundef rvNorm prog.prog_comp_env f tf :=
  TRANSL.find_funct_ptr h

/-- `Cshmgenproof.functions_translated` -/
theorem functions_translated {v : Val} {f : FunDef}
    (h : Genv.findFunct prog.globalenv.genv_genv v = some f) :
    ∃ tf, Genv.findFunct tprog.globalenv v = some tf ∧ MatchFundef rvNorm prog.prog_comp_env f tf :=
  TRANSL.find_funct h

end GENV

end Cshmgen
end CC
