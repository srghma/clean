/-
  `common/Linking.v`, second half: matching between programs with a linking
  context, commutation of linking with program transformations, the
  `TransfLink` class, linking of lists of compilation units, and composition of
  compilation passes.

  `CCLib/common/GlobalenvsTransf.lean` has a context-free `MatchProgram`, which is what
  the `Globalenvs` preservation theorems (`init_mem_match`, …) are stated for.
  `MatchProgramGen.toMatchProgram` shows that CompCert's contextual
  `match_program_gen` implies it, so those theorems apply to programs related
  by the relation defined here.
-/
import CCLib.common.LinkingTheory

namespace CC
namespace Linking
open Linker

/-! ## `match_program_gen` -/

section MatchGen
variable {C F1 V1 F2 V2 : Type} [Linker C]

/-- `Linking.match_globdef`: a function definition may be matched in any
    compilation unit `ctx'` below the context `ctx`. -/
inductive MatchGlobdefGen (Rf : C → F1 → F2 → Prop) (Rv : V1 → V2 → Prop) (ctx : C) :
    GlobDef F1 V1 → GlobDef F2 V2 → Prop where
  | gfun {ctx' : C} {f1 : F1} {f2 : F2} :
      linkorder ctx' ctx → Rf ctx' f1 f2 → MatchGlobdefGen Rf Rv ctx (.Gfun f1) (.Gfun f2)
  | gvar {v1 : GlobVar V1} {v2 : GlobVar V2} :
      Genv.MatchGlobvar Rv v1 v2 → MatchGlobdefGen Rf Rv ctx (.Gvar v1) (.Gvar v2)

/-- `Linking.match_ident_globdef` -/
def MatchIdentGlobdef (Rf : C → F1 → F2 → Prop) (Rv : V1 → V2 → Prop) (ctx : C)
    (ig1 : Ident × GlobDef F1 V1) (ig2 : Ident × GlobDef F2 V2) : Prop :=
  ig1.1 = ig2.1 ∧ MatchGlobdefGen Rf Rv ctx ig1.2 ig2.2

/-- `Linking.match_program_gen` -/
structure MatchProgramGen (Rf : C → F1 → F2 → Prop) (Rv : V1 → V2 → Prop) (ctx : C)
    (p1 : ASTProgram F1 V1) (p2 : ASTProgram F2 V2) : Prop where
  defs : ListForall2 (MatchIdentGlobdef Rf Rv ctx) p1.prog_defs p2.prog_defs
  main_eq : p2.prog_main = p1.prog_main
  public_eq : p2.prog_public = p1.prog_public

variable {Rf : C → F1 → F2 → Prop} {Rv : V1 → V2 → Prop}

/-- `Linking.match_program_defmap` -/
theorem match_program_defmap {ctx : C} {p1 : ASTProgram F1 V1} {p2 : ASTProgram F2 V2}
    (h : MatchProgramGen Rf Rv ctx p1 p2) (id : Ident) :
    OptionRel (MatchGlobdefGen Rf Rv ctx) (p1.defmap.get id) (p2.defmap.get id) :=
  PTree.ofList_related h.defs id

/-- `Linking.match_program_gen_main` -/
theorem match_program_gen_main {ctx : C} {p1 : ASTProgram F1 V1} {p2 : ASTProgram F2 V2}
    (h : MatchProgramGen Rf Rv ctx p1 p2) : p2.prog_main = p1.prog_main := h.main_eq

/-- `Linking.match_program_public` -/
theorem match_program_public {ctx : C} {p1 : ASTProgram F1 V1} {p2 : ASTProgram F2 V2}
    (h : MatchProgramGen Rf Rv ctx p1 p2) : p2.prog_public = p1.prog_public := h.public_eq

theorem matchDefs_of_forall2 {ctx : C} :
    ∀ {l1 : List (Ident × GlobDef F1 V1)} {l2 : List (Ident × GlobDef F2 V2)},
    ListForall2 (MatchIdentGlobdef Rf Rv ctx) l1 l2 →
    Genv.MatchDefs (fun f1 f2 => ∃ ctx', linkorder ctx' ctx ∧ Rf ctx' f1 f2) Rv l1 l2
  | _, _, .nil => .nil
  | (id, g1) :: _, (id', g2) :: _, .cons ⟨he, hm⟩ t => by
    simp only at he; subst he
    refine .cons ?_ (matchDefs_of_forall2 t)
    cases hm with
    | gfun hl hr => exact .gfun ⟨_, hl, hr⟩
    | gvar hv => exact .gvar hv

theorem forall2_of_matchDefs {ctx : C} {Rf' : F1 → F2 → Prop} {Rv' : V1 → V2 → Prop}
    (hf : ∀ f1 f2, Rf' f1 f2 → Rf ctx f1 f2) (hv : ∀ v1 v2, Rv' v1 v2 → Rv v1 v2) :
    ∀ {l1 : List (Ident × GlobDef F1 V1)} {l2 : List (Ident × GlobDef F2 V2)},
    Genv.MatchDefs Rf' Rv' l1 l2 → ListForall2 (MatchIdentGlobdef Rf Rv ctx) l1 l2
  | _, _, .nil => .nil
  | _, _, .cons hm t => by
    refine .cons ⟨rfl, ?_⟩ (forall2_of_matchDefs hf hv t)
    cases hm with
    | gfun hr => exact .gfun (linkorder_refl ctx) (hf _ _ hr)
    | gvar hr => exact .gvar ⟨hv _ _ hr.info, hr.init, hr.readonly, hr.volatile⟩

/-- The contextual relation implies the context-free `MatchProgram` of
    `GlobalenvsTransf`, so the `Globalenvs` preservation theorems
    (`MatchProgram.init_mem`, `find_funct_ptr`, `senv`, …) apply. -/
theorem MatchProgramGen.toMatchProgram {ctx : C} {p1 : ASTProgram F1 V1} {p2 : ASTProgram F2 V2}
    (h : MatchProgramGen Rf Rv ctx p1 p2) :
    MatchProgram (fun f1 f2 => ∃ ctx', linkorder ctx' ctx ∧ Rf ctx' f1 f2) Rv p1 p2 :=
  ⟨matchDefs_of_forall2 h.defs, h.main_eq, h.public_eq⟩

end MatchGen

/-- `Linking.match_program`: `match_program_gen` with the source program as
    the context. -/
def MatchProgramCtx {F1 V1 F2 V2 : Type} [Linker F1] [Linker V1]
    (Rf : ASTProgram F1 V1 → F1 → F2 → Prop) (Rv : V1 → V2 → Prop)
    (p1 : ASTProgram F1 V1) (p2 : ASTProgram F2 V2) : Prop :=
  MatchProgramGen Rf Rv p1 p1 p2

/-- `Linking.match_program_main` -/
theorem match_program_main {F1 V1 F2 V2 : Type} [Linker F1] [Linker V1]
    {Rf : ASTProgram F1 V1 → F1 → F2 → Prop} {Rv : V1 → V2 → Prop}
    {p1 : ASTProgram F1 V1} {p2 : ASTProgram F2 V2} (h : MatchProgramCtx Rf Rv p1 p2) :
    p2.prog_main = p1.prog_main := h.main_eq

/-! ## Program transformations produce matching programs -/

/-- `Linking.match_transform_partial_program2` -/
theorem match_transform_partial_program2 {C F1 V1 F2 V2 : Type} [Linker C]
    {Rf : C → F1 → F2 → Prop} {Rv : V1 → V2 → Prop}
    {transfFun : Ident → F1 → Res F2} {transfVar : Ident → V1 → Res V2}
    (ctx : C) {p : ASTProgram F1 V1} {tp : ASTProgram F2 V2}
    (htr : transformPartialProgram2 transfFun transfVar p = .OK tp)
    (hf : ∀ i f tf, transfFun i f = .OK tf → Rf ctx f tf)
    (hv : ∀ i v tv, transfVar i v = .OK tv → Rv v tv) :
    MatchProgramGen Rf Rv ctx p tp := by
  have h := CC.match_transform_partial_program2 htr
  exact ⟨forall2_of_matchDefs (fun f1 f2 ⟨i, e⟩ => hf i f1 f2 e)
    (fun v1 v2 ⟨i, e⟩ => hv i v1 v2 e) h.defs, h.main_eq, h.public_eq⟩

section Contextual
variable {A B V : Type} [Linker A] [Linker V]

/-- `Linking.match_transform_partial_program_contextual` -/
theorem match_transform_partial_program_contextual (Rf : ASTProgram A V → A → B → Prop)
    {transf : A → Res B} {p : ASTProgram A V} {tp : ASTProgram B V}
    (htr : transformPartialProgram transf p = .OK tp)
    (h : ∀ f tf, transf f = .OK tf → Rf p f tf) : MatchProgramCtx Rf Eq p tp :=
  match_transform_partial_program2 p htr (fun _ f tf e => h f tf e)
    (fun _ v tv e => by cases e; rfl)

/-- `Linking.match_transform_program_contextual` -/
theorem match_transform_program_contextual (Rf : ASTProgram A V → A → B → Prop)
    (transf : A → B) (p : ASTProgram A V) (h : ∀ f, Rf p f (transf f)) :
    MatchProgramCtx Rf Eq p (transformProgram transf p) :=
  match_transform_partial_program_contextual Rf (transform_program_partial_program transf p)
    (fun f tf e => by cases e; exact h f)

/-- `Linking.match_transform_partial_program` -/
theorem match_transform_partial_program {transf : A → Res B} {p : ASTProgram A V}
    {tp : ASTProgram B V} (htr : transformPartialProgram transf p = .OK tp) :
    MatchProgramCtx (fun _ f tf => transf f = .OK tf) Eq p tp :=
  match_transform_partial_program_contextual _ htr (fun _ _ e => e)

/-- `Linking.match_transform_program` -/
theorem match_transform_program (transf : A → B) (p : ASTProgram A V) :
    MatchProgramCtx (fun _ f tf => tf = transf f) Eq p (transformProgram transf p) :=
  match_transform_program_contextual _ transf p (fun _ => rfl)

end Contextual

/-! ## Commutation between linking and program transformations -/

section LinkMatch
variable {C F1 V1 F2 V2 : Type} [Linker C]
variable {Rf : C → F1 → F2 → Prop} {Rv : V1 → V2 → Prop}

/-- `Linking.match_globdef_linkorder` -/
theorem match_globdef_linkorder {ctx ctx' : C} {g : GlobDef F1 V1} {tg : GlobDef F2 V2}
    (h : MatchGlobdefGen Rf Rv ctx g tg) (hl : linkorder ctx ctx') :
    MatchGlobdefGen Rf Rv ctx' g tg := by
  cases h with
  | gfun lo r => exact .gfun (linkorder_trans lo hl) r
  | gvar hv => exact .gvar hv

variable [Linker F1] [Linker F2] [Linker V1] [Linker V2]

/-- Hypothesis `link_match_fundef` of `Linking.LINK_MATCH_PROGRAM`. -/
def LinkMatchFundef (Rf : C → F1 → F2 → Prop) : Prop :=
  ∀ (ctx1 ctx2 : C) (f1 : F1) (tf1 : F2) (f2 : F1) (tf2 : F2) (f : F1),
    link f1 f2 = some f → Rf ctx1 f1 tf1 → Rf ctx2 f2 tf2 →
    ∃ tf, link tf1 tf2 = some tf ∧ (Rf ctx1 f tf ∨ Rf ctx2 f tf)

/-- Hypothesis `link_match_varinfo` of `Linking.LINK_MATCH_PROGRAM`. -/
def LinkMatchVarinfo (Rv : V1 → V2 → Prop) : Prop :=
  ∀ (v1 : V1) (tv1 : V2) (v2 : V1) (tv2 : V2) (v : V1),
    link v1 v2 = some v → Rv v1 tv1 → Rv v2 tv2 → ∃ tv, link tv1 tv2 = some tv ∧ Rv v tv

/-- `Linking.link_match_globvar` -/
theorem link_match_globvar (hlv : LinkMatchVarinfo Rv) {v1 v2 v : GlobVar V1}
    {tv1 tv2 : GlobVar V2} (h : link v1 v2 = some v)
    (h1 : Genv.MatchGlobvar Rv v1 tv1) (h2 : Genv.MatchGlobvar Rv v2 tv2) :
    ∃ tv, link tv1 tv2 = some tv ∧ Genv.MatchGlobvar Rv v tv := by
  obtain ⟨i1, in1, r1, vo1⟩ := v1
  obtain ⟨ti1, tin1, tr1, tvo1⟩ := tv1
  obtain ⟨i2, in2, r2, vo2⟩ := v2
  obtain ⟨ti2, tin2, tr2, tvo2⟩ := tv2
  obtain ⟨hi1, e1, e2, e3⟩ := h1
  obtain ⟨hi2, e4, e5, e6⟩ := h2
  simp only at hi1 e1 e2 e3 hi2 e4 e5 e6
  subst e1 e2 e3 e4 e5 e6
  change linkVardef _ _ = some v at h
  unfold linkVardef at h
  simp only at h
  split at h
  · cases h
  · rename_i info hinfo
    split at h
    · cases h
    · rename_i init hinit
      split at h
      · rename_i hc
        cases h
        obtain ⟨tinfo, P, Q⟩ := hlv _ _ _ _ _ hinfo hi1 hi2
        refine ⟨⟨tinfo, init, r1, vo1⟩, ?_, ⟨Q, rfl, rfl, rfl⟩⟩
        change linkVardef _ _ = _
        unfold linkVardef
        simp only [P, hinit, hc, if_true]
      · cases h

/-- `Linking.link_match_globdef` -/
theorem link_match_globdef (hlf : LinkMatchFundef Rf) (hlv : LinkMatchVarinfo Rv)
    {ctx1 ctx2 ctx : C} {g1 g2 g : GlobDef F1 V1} {tg1 tg2 : GlobDef F2 V2}
    (l1 : linkorder ctx1 ctx) (l2 : linkorder ctx2 ctx) (h : link g1 g2 = some g)
    (m1 : MatchGlobdefGen Rf Rv ctx1 g1 tg1) (m2 : MatchGlobdefGen Rf Rv ctx2 g2 tg2) :
    ∃ tg, link tg1 tg2 = some tg ∧ MatchGlobdefGen Rf Rv ctx g tg := by
  change linkDef _ _ = some g at h
  cases m1 with
  | gfun lo1 r1 =>
    cases m2 with
    | gfun lo2 r2 =>
      simp only [linkDef, Option.map_eq_some_iff] at h
      obtain ⟨f, hf, rfl⟩ := h
      obtain ⟨tf, P, Q⟩ := hlf _ _ _ _ _ _ _ hf r1 r2
      refine ⟨.Gfun tf, ?_, ?_⟩
      · change linkDef _ _ = _
        simp only [linkDef, P, Option.map_some]
      · rcases Q with Q | Q
        · exact .gfun (linkorder_trans lo1 l1) Q
        · exact .gfun (linkorder_trans lo2 l2) Q
    | gvar => cases h
  | gvar hv1 =>
    cases m2 with
    | gfun => cases h
    | gvar hv2 =>
      simp only [linkDef, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, rfl⟩ := h
      obtain ⟨tv, P, Q⟩ := link_match_globvar hlv hv hv1 hv2
      refine ⟨.Gvar tv, ?_, .gvar Q⟩
      change linkDef _ _ = _
      simp only [linkDef, P, Option.map_some]

/-- `Linking.link_match_program`: linking commutes with matching. -/
theorem link_match_program (hlf : LinkMatchFundef Rf) (hlv : LinkMatchVarinfo Rv)
    {ctx1 ctx2 ctx : C} {p1 p2 p : ASTProgram F1 V1} {tp1 tp2 : ASTProgram F2 V2}
    (h : link p1 p2 = some p)
    (m1 : MatchProgramGen Rf Rv ctx1 p1 tp1) (m2 : MatchProgramGen Rf Rv ctx2 p2 tp2)
    (l1 : linkorder ctx1 ctx) (l2 : linkorder ctx2 ctx) :
    ∃ tp, link tp1 tp2 = some tp ∧ MatchProgramGen Rf Rv ctx p tp := by
  obtain ⟨hm, hq, rfl⟩ := link_prog_inv h
  refine ⟨linkProgResult tp1 tp2, link_prog_succeeds ?_ ?_, ?_, ?_, ?_⟩
  · rw [m1.main_eq, m2.main_eq]; exact hm
  · intro id tg1 tg2 e1 e2
    have r1 := match_program_defmap m1 id
    have r2 := match_program_defmap m2 id
    rw [e1] at r1; rw [e2] at r2
    generalize hg1 : p1.defmap.get id = o1 at r1
    generalize hg2 : p2.defmap.get id = o2 at r2
    cases r1 with
    | some mg1 =>
      cases r2 with
      | some mg2 =>
        obtain ⟨pub1, pub2, gd, hl⟩ := hq id _ _ hg1 hg2
        obtain ⟨tg, htl, _⟩ := link_match_globdef hlf hlv l1 l2 hl mg1 mg2
        rw [m1.public_eq, m2.public_eq]
        exact ⟨pub1, pub2, by rw [htl]; exact Option.some_ne_none _⟩
  · show ListForall2 _ (PTree.elements _) (PTree.elements _)
    apply PTree.elements_canonical_order'
    intro id
    rw [PTree.gcombine _ rfl, PTree.gcombine _ rfl]
    have r1 := match_program_defmap m1 id
    have r2 := match_program_defmap m2 id
    generalize tp1.defmap.get id = to1 at r1 ⊢
    generalize tp2.defmap.get id = to2 at r2 ⊢
    generalize hg1 : p1.defmap.get id = o1 at r1 ⊢
    generalize hg2 : p2.defmap.get id = o2 at r2 ⊢
    cases r1 with
    | none =>
      cases r2 with
      | none => exact .none
      | some mg2 => exact .some (match_globdef_linkorder mg2 l2)
    | some mg1 =>
      cases r2 with
      | none => exact .some (match_globdef_linkorder mg1 l1)
      | some mg2 =>
        obtain ⟨_, _, gd, hl⟩ := hq id _ _ hg1 hg2
        obtain ⟨tg, htl, mg⟩ := link_match_globdef hlf hlv l1 l2 hl mg1 mg2
        simp only [linkProgMerge]
        rw [hl, htl]
        exact .some mg
  · exact m1.main_eq
  · show tp1.prog_public ++ tp2.prog_public = p1.prog_public ++ p2.prog_public
    rw [m1.public_eq, m2.public_eq]

end LinkMatch

/-! ## The `TransfLink` class -/

/-- `Linking.TransfLink`: a program relation commutes with linking. -/
class TransfLink {A B : Type} [Linker A] [Linker B] (transf : A → B → Prop) : Prop where
  transf_link : ∀ {p1 p2 : A} {tp1 tp2 : B} {p : A}, link p1 p2 = some p →
    transf p1 tp1 → transf p2 tp2 → ∃ tp, link tp1 tp2 = some tp ∧ transf p tp

section TransfFundef
variable {A B : Type}

/-- `Linking.link_transf_partial_fundef` -/
theorem link_transf_partial_fundef (tr1 tr2 : A → Res B) {f1 f2 f : FunDefGen A}
    {tf1 tf2 : FunDefGen B} (h : link f1 f2 = some f)
    (h1 : transfPartialFundef tr1 f1 = .OK tf1) (h2 : transfPartialFundef tr2 f2 = .OK tf2) :
    ∃ tf, link tf1 tf2 = some tf ∧
      (transfPartialFundef tr1 f = .OK tf ∨ transfPartialFundef tr2 f = .OK tf) := by
  change linkFundef f1 f2 = some f at h
  cases f1 with
  | Internal a1 =>
    cases e1 : tr1 a1 with
    | Error => simp [transfPartialFundef, e1] at h1
    | OK b1 =>
      simp only [transfPartialFundef, e1, Res.OK.injEq] at h1
      subst h1
      cases f2 with
      | Internal => simp [linkFundef] at h
      | External ef targs tres cc =>
        simp only [transfPartialFundef, Res.OK.injEq] at h2
        subst h2
        cases ef <;> simp [linkFundef] at h
        subst h
        exact ⟨.Internal b1, rfl, .inl (by simp [transfPartialFundef, e1])⟩
  | External ef targs tres cc =>
    simp only [transfPartialFundef, Res.OK.injEq] at h1
    subst h1
    cases f2 with
    | Internal a2 =>
      cases e2 : tr2 a2 with
      | Error => simp [transfPartialFundef, e2] at h2
      | OK b2 =>
        simp only [transfPartialFundef, e2, Res.OK.injEq] at h2
        subst h2
        cases ef <;> simp [linkFundef] at h
        subst h
        exact ⟨.Internal b2, rfl, .inr (by simp [transfPartialFundef, e2])⟩
    | External ef2 targs2 tres2 cc2 =>
      simp only [transfPartialFundef, Res.OK.injEq] at h2
      subst h2
      simp only [linkFundef] at h
      split at h
      · rename_i hc
        cases h
        refine ⟨.External ef targs tres cc, ?_, .inl rfl⟩
        change linkFundef _ _ = _
        simp only [linkFundef, if_pos hc]
      · cases h

/-- The total-transformation analogue of `link_transf_partial_fundef`. -/
theorem link_transf_fundef (tr1 tr2 : A → B) {f1 f2 f : FunDefGen A}
    (h : link f1 f2 = some f) :
    ∃ tf, link (transfFundef tr1 f1) (transfFundef tr2 f2) = some tf ∧
      (tf = transfFundef tr1 f ∨ tf = transfFundef tr2 f) := by
  obtain ⟨tf, P, Q⟩ := link_transf_partial_fundef (fun f => .OK (tr1 f)) (fun f => .OK (tr2 f)) h
    (transfPartialFundef_OK tr1 f1) (transfPartialFundef_OK tr2 f2)
  rw [transfPartialFundef_OK, transfPartialFundef_OK] at Q
  refine ⟨tf, P, ?_⟩
  rcases Q with Q | Q
  · cases Q; exact .inl rfl
  · cases Q; exact .inr rfl

end TransfFundef

section TransfInstances
variable {A B V : Type} [Linker V]

theorem linkMatchVarinfo_eq : LinkMatchVarinfo (V1 := V) (V2 := V) Eq := by
  intro v1 tv1 v2 tv2 v h e1 e2
  subst e1 e2
  exact ⟨v, h, rfl⟩

/-- `Linking.TransfPartialContextualLink` -/
instance transfPartialContextualLink {Cx : Type} (trFun : Cx → A → Res B)
    (ctxFor : ASTProgram (FunDefGen A) V → Cx) :
    TransfLink (fun (p1 : ASTProgram (FunDefGen A) V) (p2 : ASTProgram (FunDefGen B) V) =>
      MatchProgramCtx (fun cu f tf => transfPartialFundef (trFun (ctxFor cu)) f = .OK tf) Eq
        p1 p2) where
  transf_link := by
    intro p1 p2 tp1 tp2 p h m1 m2
    obtain ⟨lo1, lo2⟩ := link_linkorder h
    refine link_match_program ?_ linkMatchVarinfo_eq h m1 m2 lo1 lo2
    intro _ _ _ _ _ _ _ hl e1 e2
    exact link_transf_partial_fundef _ _ hl e1 e2

/-- `Linking.TransfPartialContextualLink2` -/
instance transfPartialContextualLink2 {Cx D : Type} (trFun : Cx → D → A → Res B)
    (ctx1For : ASTProgram (FunDefGen A) V → Cx) (ctx2For : ASTProgram (FunDefGen A) V → D) :
    TransfLink (fun (p1 : ASTProgram (FunDefGen A) V) (p2 : ASTProgram (FunDefGen B) V) =>
      MatchProgramCtx
        (fun cu f tf => transfPartialFundef (trFun (ctx1For cu) (ctx2For cu)) f = .OK tf) Eq
        p1 p2) where
  transf_link := by
    intro p1 p2 tp1 tp2 p h m1 m2
    obtain ⟨lo1, lo2⟩ := link_linkorder h
    refine link_match_program ?_ linkMatchVarinfo_eq h m1 m2 lo1 lo2
    intro _ _ _ _ _ _ _ hl e1 e2
    exact link_transf_partial_fundef _ _ hl e1 e2

/-- `Linking.TransfPartialLink` -/
instance transfPartialLink (trFun : A → Res B) :
    TransfLink (fun (p1 : ASTProgram (FunDefGen A) V) (p2 : ASTProgram (FunDefGen B) V) =>
      MatchProgramCtx (fun _ f tf => transfPartialFundef trFun f = .OK tf) Eq p1 p2) where
  transf_link := by
    intro p1 p2 tp1 tp2 p h m1 m2
    obtain ⟨lo1, lo2⟩ := link_linkorder h
    refine link_match_program ?_ linkMatchVarinfo_eq h m1 m2 lo1 lo2
    intro _ _ _ _ _ _ _ hl e1 e2
    exact link_transf_partial_fundef _ _ hl e1 e2

/-- `Linking.TransfTotallContextualLink` -/
instance transfTotalContextualLink {Cx : Type} (trFun : Cx → A → B)
    (ctxFor : ASTProgram (FunDefGen A) V → Cx) :
    TransfLink (fun (p1 : ASTProgram (FunDefGen A) V) (p2 : ASTProgram (FunDefGen B) V) =>
      MatchProgramCtx (fun cu f tf => tf = transfFundef (trFun (ctxFor cu)) f) Eq p1 p2) where
  transf_link := by
    intro p1 p2 tp1 tp2 p h m1 m2
    obtain ⟨lo1, lo2⟩ := link_linkorder h
    refine link_match_program ?_ linkMatchVarinfo_eq h m1 m2 lo1 lo2
    intro _ _ _ _ _ _ _ hl e1 e2
    subst e1 e2
    exact link_transf_fundef _ _ hl

/-- `Linking.TransfTotalLink` -/
instance transfTotalLink (trFun : A → B) :
    TransfLink (fun (p1 : ASTProgram (FunDefGen A) V) (p2 : ASTProgram (FunDefGen B) V) =>
      MatchProgramCtx (fun _ f tf => tf = transfFundef trFun f) Eq p1 p2) where
  transf_link := by
    intro p1 p2 tp1 tp2 p h m1 m2
    obtain ⟨lo1, lo2⟩ := link_linkorder h
    refine link_match_program ?_ linkMatchVarinfo_eq h m1 m2 lo1 lo2
    intro _ _ _ _ _ _ _ hl e1 e2
    subst e1 e2
    exact link_transf_fundef _ _ hl

end TransfInstances

/-! ## Linking a non-empty list of compilation units -/

/-- `Coqlib.nlist`: non-empty lists. -/
inductive NList (A : Type) where
  | nbase (a : A)
  | ncons (a : A) (l : NList A)

/-- `Coqlib.nIn` -/
def NList.In {A : Type} (a : A) : NList A → Prop
  | .nbase b => b = a
  | .ncons b l => b = a ∨ NList.In a l

/-- `Coqlib.nlist_forall2` -/
inductive NListForall2 {A B : Type} (R : A → B → Prop) : NList A → NList B → Prop where
  | nbase {a b} : R a b → NListForall2 R (.nbase a) (.nbase b)
  | ncons {a l b m} : R a b → NListForall2 R l m → NListForall2 R (.ncons a l) (.ncons b m)

section LinkList
variable {A : Type} [Linker A]

/-- `Linking.link_list` -/
def linkList : NList A → Option A
  | .nbase a => some a
  | .ncons a l =>
    match linkList l with
    | none => none
    | some b => link a b

/-- `Linking.link_list_linkorder` -/
theorem link_list_linkorder {a : A} : ∀ {l : NList A} {b : A},
    linkList l = some b → NList.In a l → linkorder a b
  | .nbase c, b, h, hin => by
    simp only [linkList, Option.some.injEq] at h
    simp only [NList.In] at hin
    subst h hin; exact linkorder_refl _
  | .ncons c l, b, h, hin => by
    simp only [linkList] at h
    split at h
    · cases h
    · rename_i b' hb'
      have hl := link_linkorder h
      rcases hin with rfl | hin
      · exact hl.1
      · exact linkorder_trans (link_list_linkorder hb' hin) hl.2

end LinkList

/-- `Linking.link_list_match`: list linking commutes with any relation that
    commutes with binary linking. -/
theorem link_list_match {A B : Type} [Linker A] [Linker B] (R : A → B → Prop) [TL : TransfLink R] :
    ∀ {al : NList A} {bl : NList B}, NListForall2 R al bl →
    ∀ {a : A}, linkList al = some a → ∃ b, linkList bl = some b ∧ R a b
  | _, _, .nbase hr, a', h => by
    simp only [linkList, Option.some.injEq] at h
    subst h; exact ⟨_, rfl, hr⟩
  | _, _, .ncons (l := l) hr t, a', h => by
    simp only [linkList] at h
    split at h
    · cases h
    · rename_i a1 ha1
      obtain ⟨b', P, Q⟩ := link_list_match R t ha1
      obtain ⟨b'', U, W⟩ := TL.transf_link h hr Q
      refine ⟨b'', ?_, W⟩
      simp only [linkList, P, U]

/-! ## Linking and composition of compilation passes -/

/-- `Linking.Language`: a type of programs with a linker. -/
structure Language where
  prog : Type
  linker : Linker prog

instance instLinkerLanguage (L : Language) : Linker L.prog := L.linker

/-- `Linking.Language_gen` -/
def Language.gen (A : Type) [L : Linker A] : Language := ⟨A, L⟩

/-- `Linking.Pass`: a matching relation between source and target programs
    that commutes with linking. -/
structure Pass (S T : Language) where
  pass_match : S.prog → T.prog → Prop
  pass_match_link : TransfLink pass_match

/-- `Linking.pass_identity` -/
def passIdentity (l : Language) : Pass l l where
  pass_match p1 p2 := p1 = p2
  pass_match_link := ⟨fun h e1 e2 => by subst e1 e2; exact ⟨_, h, rfl⟩⟩

/-- `Linking.pass_compose` -/
def passCompose {l1 l2 l3 : Language} (pass : Pass l1 l2) (pass' : Pass l2 l3) : Pass l1 l3 where
  pass_match p1 p3 := ∃ p2, pass.pass_match p1 p2 ∧ pass'.pass_match p2 p3
  pass_match_link := ⟨fun h ⟨_, a1, b1⟩ ⟨_, a2, b2⟩ => by
    obtain ⟨p', hp', m'⟩ := pass.pass_match_link.transf_link h a1 a2
    obtain ⟨tp, htp, m''⟩ := pass'.pass_match_link.transf_link hp' b1 b2
    exact ⟨tp, htp, p', m', m''⟩⟩

/-- `Linking.Passes`: a list of composable passes. -/
inductive Passes : Language → Language → Type 1 where
  | nil (l : Language) : Passes l l
  | cons {l1 l2 l3 : Language} : Pass l1 l2 → Passes l2 l3 → Passes l1 l3

/-- `Linking.compose_passes` -/
def composePasses : {l l' : Language} → Passes l l' → Pass l l'
  | _, _, .nil l => passIdentity l
  | _, _, .cons pass1 passes => passCompose pass1 (composePasses passes)

/-- `Linking.nlist_forall2_identity` -/
theorem nlist_forall2_identity {A : Type} : ∀ {la lb : NList A},
    NListForall2 (fun a b => a = b) la lb → la = lb
  | _, _, .nbase h => by subst h; rfl
  | _, _, .ncons h t => by subst h; rw [nlist_forall2_identity t]

/-- `Linking.nlist_forall2_compose_inv` -/
theorem nlist_forall2_compose_inv {A B C : Type} {R1 : A → B → Prop} {R2 : B → C → Prop} :
    ∀ {la : NList A} {lc : NList C},
    NListForall2 (fun a c => ∃ b, R1 a b ∧ R2 b c) la lc →
    ∃ lb : NList B, NListForall2 R1 la lb ∧ NListForall2 R2 lb lc
  | _, _, .nbase ⟨b, P, Q⟩ => ⟨.nbase b, .nbase P, .nbase Q⟩
  | _, _, .ncons ⟨b, P, Q⟩ t =>
    let ⟨lb, U, W⟩ := nlist_forall2_compose_inv t
    ⟨.ncons b lb, .ncons P U, .ncons Q W⟩

/-- `Linking.link_list_compose_passes`: linking the target units of a
    composition of passes succeeds whenever linking the source units does, and
    the results are related by the composed pass. -/
theorem link_list_compose_passes : ∀ {src tgt : Language} (passes : Passes src tgt)
    {srcUnits : NList src.prog} {tgtUnits : NList tgt.prog},
    NListForall2 (composePasses passes).pass_match srcUnits tgtUnits →
    ∀ {srcProg : src.prog}, linkList srcUnits = some srcProg →
    ∃ tgtProg, linkList tgtUnits = some tgtProg ∧ (composePasses passes).pass_match srcProg tgtProg
  | _, _, .nil _, _, _, F2, srcProg, hl => by
    have := nlist_forall2_identity F2
    subst this
    exact ⟨srcProg, hl, rfl⟩
  | _, _, .cons p passes, _, _, F2, srcProg, hl => by
    obtain ⟨interm, P, Q⟩ := nlist_forall2_compose_inv F2
    have := p.pass_match_link
    obtain ⟨intermProg, U, W⟩ := link_list_match p.pass_match P hl
    obtain ⟨tgtProg, X, Y⟩ := link_list_compose_passes passes Q U
    exact ⟨tgtProg, X, intermProg, W, Y⟩

end Linking
end CC
