/-
  The generic theory of `common/Linking.v` (and the linking part of
  `cfrontend/Ctypes.v` that does not involve composite environments).

  `CCLib/common/Linking.lean` provides a *computational*, Clight-specific linker used
  to merge `clightgen` outputs; it deliberately deviates from CompCert (array
  completion, signature checks against the definition).  This file is the
  faithful port of CompCert's linking **theory**:

  * the `Linker` class (`link`, `linkorder`, `link_linkorder`, …);
  * the instances for function definitions (`Ctypes.Linker_fundef`, since the
    port's only `fundef` is `Ctypes.fundef`), types (`Ctypes.Linker_types`),
    variable initialisers, variables, `unit`, global definitions and generic
    programs (`link_prog`, `link_prog_inv`, `link_prog_succeeds`,
    `prog_defmap_linkorder`);
  * `match_program_gen` with its linking context, `match_program_defmap`, the
    `match_transform_*` theorems, and the commutation of linking with
    matching (`link_match_globvar`, `link_match_globdef`, `link_match_program`);
  * the `TransfLink` class and its five standard instances;
  * linking of non-empty lists of units (`link_list`, `link_list_linkorder`,
    `link_list_match`) and composition of passes (`Language`, `Pass`,
    `pass_identity`, `pass_compose`, `Passes`, `compose_passes`,
    `link_list_compose_passes`).

  Rocq's `PTree_Properties.for_all` is expressed with `List.all` over
  `PTree.elements`.
-/
import CCLib.common.GlobalenvsTransf
import CCLib.lib.MapsTheory

namespace CC

/-! ## The `Linker` class -/

/-- `Linking.Linker`: a partial binary `link` operator and a preorder
    `linkorder` such that linking produces an upper bound. -/
class Linker (A : Type) where
  link : A → A → Option A
  linkorder : A → A → Prop
  linkorder_refl : ∀ x, linkorder x x
  linkorder_trans : ∀ {x y z}, linkorder x y → linkorder y z → linkorder x z
  link_linkorder : ∀ {x y z}, link x y = some z → linkorder x z ∧ linkorder y z

namespace Linking

open Linker

/-! ## Function definitions (`Ctypes.Linker_fundef`) -/

section Fundef
variable {F : Type}

/-- `Ctypes.link_fundef`: an `EF_external` declaration links with an internal
    definition; two external declarations link if identical. -/
def linkFundef : FunDefGen F → FunDefGen F → Option (FunDefGen F)
  | .Internal _, .Internal _ => none
  | .External ef1 targs1 tres1 cc1, .External ef2 targs2 tres2 cc2 =>
    if ef1 = ef2 ∧ targs1 = targs2 ∧ tres1 = tres2 ∧ cc1 = cc2 then
      some (.External ef1 targs1 tres1 cc1)
    else none
  | .Internal f, .External ef _ _ _ =>
    match ef with
    | .EF_external _ _ => some (.Internal f)
    | _ => none
  | .External ef _ _ _, .Internal f =>
    match ef with
    | .EF_external _ _ => some (.Internal f)
    | _ => none

/-- `Ctypes.linkorder_fundef` -/
inductive LinkorderFundef : FunDefGen F → FunDefGen F → Prop where
  | refl (fd : FunDefGen F) : LinkorderFundef fd fd
  | ext_int (f : F) (id : String) (sg : Signature) (targs : List Ty) (tres : Ty)
      (cc : CallConv) : LinkorderFundef (.External (.EF_external id sg) targs tres cc) (.Internal f)

theorem linkFundef_linkorder {x y z : FunDefGen F} (h : linkFundef x y = some z) :
    LinkorderFundef x z ∧ LinkorderFundef y z := by
  cases x with
  | Internal f1 =>
    cases y with
    | Internal f2 => simp [linkFundef] at h
    | External ef targs tres cc =>
      cases ef <;> simp [linkFundef] at h
      subst h; exact ⟨.refl _, .ext_int _ _ _ _ _ _⟩
  | External ef targs tres cc =>
    cases y with
    | Internal f2 =>
      cases ef <;> simp [linkFundef] at h
      subst h; exact ⟨.ext_int _ _ _ _ _ _, .refl _⟩
    | External ef2 targs2 tres2 cc2 =>
      simp only [linkFundef] at h
      split at h
      · rename_i hc
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hc
        cases h; exact ⟨.refl _, .refl _⟩
      · cases h

instance instLinkerFundef : Linker (FunDefGen F) where
  link := linkFundef
  linkorder := LinkorderFundef
  linkorder_refl := .refl
  linkorder_trans := by
    intro x y z h1 h2
    cases h1 with
    | refl => exact h2
    | ext_int => cases h2 with
      | refl => exact .ext_int _ _ _ _ _ _
  link_linkorder := linkFundef_linkorder

/-- `Ctypes.link_fundef_either` -/
theorem link_fundef_either {f1 f2 f : FunDefGen F} (h : link f1 f2 = some f) :
    f = f1 ∨ f = f2 := by
  change linkFundef f1 f2 = some f at h
  cases f1 with
  | Internal f1 =>
    cases f2 with
    | Internal => simp [linkFundef] at h
    | External ef => cases ef <;> simp [linkFundef] at h; exact .inl h.symm
  | External ef targs tres cc =>
    cases f2 with
    | Internal => cases ef <;> simp [linkFundef] at h; exact .inr h.symm
    | External =>
      simp only [linkFundef] at h
      split at h
      · cases h; exact .inl rfl
      · cases h

end Fundef

/-! ## Types (`Ctypes.Linker_types`) -/

instance instLinkerTy : Linker Ty where
  link t1 t2 := if t1 = t2 then some t1 else none
  linkorder t1 t2 := t1 = t2
  linkorder_refl _ := rfl
  linkorder_trans h1 h2 := h1.trans h2
  link_linkorder := by
    intro x y z h
    split at h
    · cases h; rename_i he; exact ⟨rfl, he.symm⟩
    · cases h

/-! ## Variable initialisers (`Linking.Linker_varinit`) -/

/-- `Linking.link_varinit`.  Rocq's `classify_init` distinguishes an `extern`
    initialiser (`nil`), a `common` one (`[Init_space sz]`) and a definitive
    one; the match below follows the same case order. -/
def linkVarinit : List InitData → List InitData → Option (List InitData)
  | [], i2 => some i2
  | i1, [] => some i1
  | [.Init_space sz1], i2 => if sz1 = InitData.listSize i2 then some i2 else none
  | i1, [.Init_space sz2] => if sz2 = InitData.listSize i1 then some i1 else none
  | _, _ => none

/-- `Linking.linkorder_varinit` -/
inductive LinkorderVarinit : List InitData → List InitData → Prop where
  | refl (il : List InitData) : LinkorderVarinit il il
  | extern (il : List InitData) : LinkorderVarinit [] il
  | common (sz : Z) (il : List InitData) :
      il ≠ [] → InitData.listSize il = sz → LinkorderVarinit [.Init_space sz] il

theorem listSize_space (sz : Z) : InitData.listSize [.Init_space sz] = max sz 0 := by
  simp [InitData.listSize, InitData.size]

theorem linkVarinit_linkorder {x y z : List InitData} (h : linkVarinit x y = some z) :
    LinkorderVarinit x z ∧ LinkorderVarinit y z := by
  unfold linkVarinit at h
  split at h
  · cases h; exact ⟨.extern _, .refl _⟩
  · cases h; exact ⟨.refl _, .extern _⟩
  · rename_i sz1 i2 hne
    split at h
    · rename_i hs; cases h
      refine ⟨.common _ _ ?_ hs.symm, .refl _⟩
      intro hn; subst hn; exact hne rfl
    · cases h
  · rename_i i1 sz2 hne _
    split at h
    · rename_i hs; cases h
      refine ⟨.refl _, .common _ _ ?_ hs.symm⟩
      intro hn; subst hn; simp at hne
    · cases h
  · cases h

instance instLinkerVarinit : Linker (List InitData) where
  link := linkVarinit
  linkorder := LinkorderVarinit
  linkorder_refl := .refl
  linkorder_trans := by
    intro x y z h1 h2
    cases h1 with
    | refl => exact h2
    | extern => exact .extern _
    | common sz il hne hsz =>
      cases h2 with
      | refl => exact .common _ _ hne hsz
      | extern => exact absurd rfl hne
      | common sz' _ hne' hsz' =>
        refine .common _ _ hne' ?_
        have := InitData.listSize_nonneg z
        rw [← hsz, listSize_space, hsz']
        rw [hsz'] at this
        exact (Int.max_eq_left this).symm
  link_linkorder := linkVarinit_linkorder

/-! ## Variables (`Linking.Linker_vardef`) -/

section Vardef
variable {V : Type} [Linker V]

/-- `Linking.link_vardef` -/
def linkVardef (v1 v2 : GlobVar V) : Option (GlobVar V) :=
  match link v1.gvar_info v2.gvar_info with
  | none => none
  | some info =>
    match link v1.gvar_init v2.gvar_init with
    | none => none
    | some init =>
      if v1.gvar_readonly == v2.gvar_readonly && v1.gvar_volatile == v2.gvar_volatile then
        some ⟨info, init, v1.gvar_readonly, v1.gvar_volatile⟩
      else none

/-- `Linking.linkorder_vardef` -/
inductive LinkorderVardef : GlobVar V → GlobVar V → Prop where
  | intro {info1 info2 : V} {i1 i2 : List InitData} (ro vo : Bool) :
      linkorder info1 info2 → linkorder i1 i2 → LinkorderVardef ⟨info1, i1, ro, vo⟩ ⟨info2, i2, ro, vo⟩

theorem linkVardef_linkorder {x y z : GlobVar V} (h : linkVardef x y = some z) :
    LinkorderVardef x z ∧ LinkorderVardef y z := by
  obtain ⟨f1, i1, r1, v1⟩ := x
  obtain ⟨f2, i2, r2, v2⟩ := y
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
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        cases h
        have h1 := link_linkorder hinfo
        have h2 := link_linkorder hinit
        exact ⟨.intro _ _ h1.1 h2.1, .intro _ _ h1.2 h2.2⟩
      · cases h

instance instLinkerVardef : Linker (GlobVar V) where
  link := linkVardef
  linkorder := LinkorderVardef
  linkorder_refl := fun ⟨_, _, _, _⟩ => .intro _ _ (linkorder_refl _) (linkorder_refl _)
  linkorder_trans := by
    intro x y z h1 h2
    cases h1 with
    | intro ro vo a b =>
      cases h2 with
      | intro _ _ c d => exact .intro _ _ (linkorder_trans a c) (linkorder_trans b d)
  link_linkorder := linkVardef_linkorder

end Vardef

/-! ## `unit` (`Linking.Linker_unit`) -/

instance instLinkerUnit : Linker Unit where
  link _ _ := some ()
  linkorder _ _ := True
  linkorder_refl _ := trivial
  linkorder_trans _ _ := trivial
  link_linkorder _ := ⟨trivial, trivial⟩

/-! ## Global definitions (`Linking.Linker_def`) -/

section Def
variable {F V : Type} [Linker F] [Linker V]

/-- `Linking.link_def` -/
def linkDef : GlobDef F V → GlobDef F V → Option (GlobDef F V)
  | .Gfun f1, .Gfun f2 => (link f1 f2).map .Gfun
  | .Gvar v1, .Gvar v2 => (link v1 v2).map .Gvar
  | _, _ => none

/-- `Linking.linkorder_def` -/
inductive LinkorderDef : GlobDef F V → GlobDef F V → Prop where
  | gfun {fd1 fd2 : F} : linkorder fd1 fd2 → LinkorderDef (.Gfun fd1) (.Gfun fd2)
  | gvar {v1 v2 : GlobVar V} : linkorder v1 v2 → LinkorderDef (.Gvar v1) (.Gvar v2)

theorem linkDef_linkorder {x y z : GlobDef F V} (h : linkDef x y = some z) :
    LinkorderDef x z ∧ LinkorderDef y z := by
  cases x <;> cases y <;> simp only [linkDef, Option.map_eq_some_iff] at h
  · obtain ⟨f, hf, rfl⟩ := h
    have := link_linkorder hf; exact ⟨.gfun this.1, .gfun this.2⟩
  · cases h
  · cases h
  · obtain ⟨v, hv, rfl⟩ := h
    have := link_linkorder hv; exact ⟨.gvar this.1, .gvar this.2⟩

instance instLinkerDef : Linker (GlobDef F V) where
  link := linkDef
  linkorder := LinkorderDef
  linkorder_refl
    | .Gfun _ => .gfun (linkorder_refl _)
    | .Gvar _ => .gvar (linkorder_refl _)
  linkorder_trans := by
    intro x y z h1 h2
    cases h1 with
    | gfun a => cases h2 with | gfun b => exact .gfun (linkorder_trans a b)
    | gvar a => cases h2 with | gvar b => exact .gvar (linkorder_trans a b)
  link_linkorder := linkDef_linkorder

end Def

end Linking

/-! ## Relations on lists and options (`Coqlib.list_forall2`, `option_rel`) -/

/-- `Coqlib.list_forall2` -/
inductive ListForall2 {A B : Type} (R : A → B → Prop) : List A → List B → Prop where
  | nil : ListForall2 R [] []
  | cons {a b l1 l2} : R a b → ListForall2 R l1 l2 → ListForall2 R (a :: l1) (b :: l2)

/-- `Coqlib.option_rel` -/
inductive OptionRel {A B : Type} (R : A → B → Prop) : Option A → Option B → Prop where
  | none : OptionRel R none none
  | some {a b} : R a b → OptionRel R (some a) (some b)

/-! ## More `PTree` properties -/

namespace PTree
variable {A B : Type}

/-- `PTree_Properties.for_all` -/
def forAll (m : PTree A) (f : Positive → A → Bool) : Bool :=
  (elements m).all (fun p => f p.1 p.2)

/-- `PTree_Properties.for_all_correct` -/
theorem forAll_correct (m : PTree A) (f : Positive → A → Bool) :
    forAll m f = true ↔ ∀ x a, get x m = some a → f x a = true := by
  unfold forAll
  rw [List.all_eq_true]
  constructor
  · intro h x a hx
    exact h (x, a) (elements_correct m x a hx)
  · intro h ⟨x, a⟩ hx
    exact h x a (elements_complete m x a hx)

theorem get_ofList_none {l : List (Positive × A)} {k : Positive} (h : k ∉ l.map Prod.fst) :
    get k (ofList l) = none := by
  unfold ofList; rw [get_foldl_set_not_mem _ _ _ h]; exact gempty k

/-- `PTree_Properties.of_list_elements` -/
theorem ofList_elements (m : PTree A) (k : Positive) : get k (ofList (elements m)) = get k m := by
  cases hm : get k m with
  | some v => exact ofList_norepet (elements_keys_norepet m) (elements_correct m k v hm)
  | none =>
    cases hg : get k (ofList (elements m)) with
    | none => rfl
    | some g =>
      have := elements_complete m k g (in_ofList hg)
      rw [hm] at this; cases this

/-- `PTree_Properties.of_list_related` -/
theorem ofList_related {R : A → B → Prop} {l1 : List (Positive × A)} {l2 : List (Positive × B)}
    (h : ListForall2 (fun a b => a.1 = b.1 ∧ R a.2 b.2) l1 l2) (k : Positive) :
    OptionRel R (get k (ofList l1)) (get k (ofList l2)) := by
  unfold ofList
  suffices ∀ (m1 : PTree A) (m2 : PTree B), (∀ k, OptionRel R (get k m1) (get k m2)) →
      ∀ k, OptionRel R (get k (l1.foldl (fun m kv => m.set kv.1 kv.2) m1))
        (get k (l2.foldl (fun m kv => m.set kv.1 kv.2) m2)) by
    apply this
    intro k; simp only [gempty]; exact .none
  induction h with
  | nil => intro m1 m2 hm; exact hm
  | cons hab _ ih =>
    intro m1 m2 hm
    apply ih
    intro k
    obtain ⟨he, hr⟩ := hab
    simp only
    rw [he, gsspec, gsspec]
    split
    · exact .some hr
    · exact hm k

theorem elemsAux_empty (m : PTree A) (h : ∀ i, get i m = none) (rp : List Bool)
    (acc : List (Positive × A)) : elemsAux m rp acc = acc := by
  induction m generalizing rp acc with
  | Leaf => rfl
  | Node l o r ihl ihr =>
    have ho : o = none := h .xH
    subst ho
    simp only [elemsAux]
    rw [ihr (fun i => h (.xI i)), ihl (fun i => h (.xO i))]

theorem optionRel_none_left {R : A → B → Prop} {o : Option B} (h : OptionRel R none o) :
    o = none := by cases h; rfl

theorem optionRel_none_right {R : A → B → Prop} {o : Option A} (h : OptionRel R o none) :
    o = none := by cases h; rfl

theorem elemsAux_related {R : A → B → Prop} (m1 : PTree A) (m2 : PTree B)
    (h : ∀ i, OptionRel R (get i m1) (get i m2)) (rp : List Bool)
    {acc1 : List (Positive × A)} {acc2 : List (Positive × B)}
    (hacc : ListForall2 (fun a b => a.1 = b.1 ∧ R a.2 b.2) acc1 acc2) :
    ListForall2 (fun a b => a.1 = b.1 ∧ R a.2 b.2) (elemsAux m1 rp acc1) (elemsAux m2 rp acc2) := by
  induction m1 generalizing m2 rp acc1 acc2 with
  | Leaf =>
    rw [elemsAux_empty m2 (fun i => optionRel_none_left (by simpa using h i))]
    exact hacc
  | Node l1 o1 r1 ihl ihr =>
    cases m2 with
    | Leaf =>
      rw [elemsAux_empty (.Node l1 o1 r1) (fun i => optionRel_none_right (by simpa using h i))]
      exact hacc
    | Node l2 o2 r2 =>
      simp only [elemsAux]
      apply ihl l2 (fun i => h (.xO i))
      have hr := ihr r2 (fun i => h (.xI i)) (true :: rp) hacc
      have ho : OptionRel R o1 o2 := h .xH
      cases ho with
      | none => exact hr
      | some hab => exact .cons ⟨rfl, hab⟩ hr

/-- `PTree.elements_canonical_order'` (the port's trees are not canonical, but
    two trees with related contents still list their bindings in the same
    order). -/
theorem elements_canonical_order' {R : A → B → Prop} (m1 : PTree A) (m2 : PTree B)
    (h : ∀ i, OptionRel R (get i m1) (get i m2)) :
    ListForall2 (fun a b => a.1 = b.1 ∧ R a.2 b.2) (elements m1) (elements m2) :=
  elemsAux_related m1 m2 h [] .nil

end PTree

namespace Linking
open Linker

/-! ## Programs (`Linking.Linker_prog`) -/

section LinkerProg
variable {F V : Type} [Linker F] [Linker V]

/-- `Linking.link_prog_check` -/
def linkProgCheck (p1 p2 : ASTProgram F V) (x : Ident) (gd1 : GlobDef F V) : Bool :=
  match p2.defmap.get x with
  | none => true
  | some gd2 =>
    decide (x ∈ p1.prog_public) && decide (x ∈ p2.prog_public) && (link gd1 gd2).isSome

/-- `Linking.link_prog_merge` -/
def linkProgMerge (o1 o2 : Option (GlobDef F V)) : Option (GlobDef F V) :=
  match o1, o2 with
  | none, _ => o2
  | _, none => o1
  | some gd1, some gd2 => link gd1 gd2

/-- The program that `link_prog` returns when linking succeeds. -/
def linkProgResult (p1 p2 : ASTProgram F V) : ASTProgram F V :=
  ⟨PTree.elements (PTree.combine linkProgMerge p1.defmap p2.defmap),
   p1.prog_public ++ p2.prog_public, p1.prog_main⟩

/-- `Linking.link_prog` -/
def linkProg (p1 p2 : ASTProgram F V) : Option (ASTProgram F V) :=
  if p1.prog_main = p2.prog_main ∧ PTree.forAll p1.defmap (linkProgCheck p1 p2) = true then
    some (linkProgResult p1 p2)
  else none

/-- `Linking.link_prog_inv` -/
theorem link_prog_inv {p1 p2 p : ASTProgram F V} (h : linkProg p1 p2 = some p) :
    p1.prog_main = p2.prog_main ∧
    (∀ id gd1 gd2, p1.defmap.get id = some gd1 → p2.defmap.get id = some gd2 →
      id ∈ p1.prog_public ∧ id ∈ p2.prog_public ∧ ∃ gd, link gd1 gd2 = some gd) ∧
    p = linkProgResult p1 p2 := by
  unfold linkProg at h
  split at h
  · rename_i hc
    cases h
    refine ⟨hc.1, ?_, rfl⟩
    intro id gd1 gd2 h1 h2
    have := (PTree.forAll_correct _ _).mp hc.2 id gd1 h1
    simp only [linkProgCheck, h2, Bool.and_eq_true, decide_eq_true_eq, Option.isSome_iff_exists]
      at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  · cases h

/-- `Linking.link_prog_succeeds` -/
theorem link_prog_succeeds {p1 p2 : ASTProgram F V} (hm : p1.prog_main = p2.prog_main)
    (h : ∀ id gd1 gd2, p1.defmap.get id = some gd1 → p2.defmap.get id = some gd2 →
      id ∈ p1.prog_public ∧ id ∈ p2.prog_public ∧ link gd1 gd2 ≠ none) :
    linkProg p1 p2 = some (linkProgResult p1 p2) := by
  unfold linkProg
  rw [if_pos]
  refine ⟨hm, (PTree.forAll_correct _ _).mpr ?_⟩
  intro x gd1 hx
  unfold linkProgCheck
  split
  · rfl
  · rename_i gd2 h2
    obtain ⟨a, b, c⟩ := h x gd1 gd2 hx h2
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨a, b⟩, Option.isSome_iff_ne_none.mpr c⟩

omit [Linker F] [Linker V] in
/-- `Linking.prog_defmap_elements` -/
theorem prog_defmap_elements (m : PTree (GlobDef F V)) (pub : List Ident) (mn : Ident) (x : Ident) :
    (ASTProgram.mk (PTree.elements m) pub mn).defmap.get x = m.get x :=
  PTree.ofList_elements m x

theorem linkProgResult_defmap (p1 p2 : ASTProgram F V) (x : Ident) :
    (linkProgResult p1 p2).defmap.get x = linkProgMerge (p1.defmap.get x) (p2.defmap.get x) := by
  unfold linkProgResult
  rw [prog_defmap_elements, PTree.gcombine _ rfl]

/-- The `linkorder` of `Linking.Linker_prog`. -/
def ProgLinkorder (p1 p2 : ASTProgram F V) : Prop :=
  p1.prog_main = p2.prog_main ∧
  (∀ x, x ∈ p1.prog_public → x ∈ p2.prog_public) ∧
  ∀ id gd1, p1.defmap.get id = some gd1 →
    ∃ gd2, p2.defmap.get id = some gd2 ∧ linkorder gd1 gd2 ∧ (id ∉ p2.prog_public → gd2 = gd1)

theorem linkProg_linkorder {x y z : ASTProgram F V} (h : linkProg x y = some z) :
    ProgLinkorder x z ∧ ProgLinkorder y z := by
  obtain ⟨hm, hq, rfl⟩ := link_prog_inv h
  refine ⟨⟨rfl, fun a ha => List.mem_append_left _ ha, ?_⟩,
    ⟨hm.symm, fun a ha => List.mem_append_right _ ha, ?_⟩⟩
  · intro id gd1 h1
    rw [linkProgResult_defmap, h1]
    cases h2 : y.defmap.get id with
    | none => exact ⟨gd1, rfl, linkorder_refl _, fun _ => rfl⟩
    | some gd2 =>
      obtain ⟨p, q, gd, r⟩ := hq id gd1 gd2 h1 h2
      refine ⟨gd, r, (link_linkorder r).1, fun hn => ?_⟩
      exact absurd (List.mem_append_left _ p) hn
  · intro id gd2 h2
    rw [linkProgResult_defmap, h2]
    cases h1 : x.defmap.get id with
    | none => exact ⟨gd2, rfl, linkorder_refl _, fun _ => rfl⟩
    | some gd1 =>
      obtain ⟨p, q, gd, r⟩ := hq id gd1 gd2 h1 h2
      refine ⟨gd, r, (link_linkorder r).2, fun hn => ?_⟩
      exact absurd (List.mem_append_left _ p) hn

instance instLinkerProg : Linker (ASTProgram F V) where
  link := linkProg
  linkorder := ProgLinkorder
  linkorder_refl p := ⟨rfl, fun _ h => h, fun _ gd1 h => ⟨gd1, h, linkorder_refl _, fun _ => rfl⟩⟩
  linkorder_trans := by
    intro x y z ⟨m1, p1, d1⟩ ⟨m2, p2, d2⟩
    refine ⟨m1.trans m2, fun a h => p2 a (p1 a h), ?_⟩
    intro id gd1 h1
    obtain ⟨gd2, h2, l12, e12⟩ := d1 id gd1 h1
    obtain ⟨gd3, h3, l23, e23⟩ := d2 id gd2 h2
    refine ⟨gd3, h3, linkorder_trans l12 l23, fun hn => ?_⟩
    rw [e23 hn, e12 (fun hy => hn (p2 _ hy))]
  link_linkorder := linkProg_linkorder

/-- `Linking.prog_defmap_linkorder` -/
theorem prog_defmap_linkorder {p1 p2 : ASTProgram F V} {id : Ident} {gd1 : GlobDef F V}
    (hl : linkorder p1 p2) (h : p1.defmap.get id = some gd1) :
    ∃ gd2, p2.defmap.get id = some gd2 ∧ linkorder gd1 gd2 := by
  obtain ⟨gd2, a, b, _⟩ := hl.2.2 id gd1 h
  exact ⟨gd2, a, b⟩

end LinkerProg

end Linking
end CC
