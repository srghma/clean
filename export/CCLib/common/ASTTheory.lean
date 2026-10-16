/-
  The rest of `common/AST.v`: the lemmas about types, chunks and initialisers,
  generic programs (`AST.program`) with their definition map (`prog_defmap`,
  backed by `PTree_Properties.of_list` from `lib/Maps.v`), the generic program
  transformations (`transform_program`, `transform_partial_program(2)`,
  `transf_fundef`, `transf_partial_fundef`), `rpair` and builtin arguments.

  The Clight `Program` record of `CCLib/cfrontend/Clight.lean` predates this file and is
  kept as it is; `ASTProgram F V` is CompCert's generic `AST.program F V`, which
  the transformation theorems (`CCLib/common/GlobalenvsTransf.lean`) are stated over.

  Error messages: CompCert's `transf_globdefs` prefixes the error with the name
  of the offending global; the port's `Res.Error` carries a `String`, so the
  message is passed through unchanged.
-/
import CCLib.lib.MapsTheory
import CCLib.cfrontend.Ctypes

namespace CC

/-! ## Types, chunks and initialisers -/

/-- `AST.typesize_pos` -/
theorem ATyp.size_pos (ty : ATyp) : ty.size > 0 := by cases ty <;> decide

/-- `AST.typesize_Tptr` -/
theorem ATyp.size_Tptr : Tptr.size = if Archi.ptr64 then 8 else 4 := by
  simp [Tptr, Archi.ptr64, ATyp.size]

/-- `AST.subtype` -/
def ATyp.subtype : ATyp → ATyp → Bool
  | .Tint, .Tint | .Tlong, .Tlong | .Tfloat, .Tfloat | .Tsingle, .Tsingle => true
  | .Tint, .Tany32 | .Tsingle, .Tany32 | .Tany32, .Tany32 => true
  | _, .Tany64 => true
  | _, _ => false

/-- `AST.subtype_list` -/
def ATyp.subtypeList : List ATyp → List ATyp → Bool
  | [], [] => true
  | t1 :: l1, t2 :: l2 => ATyp.subtype t1 t2 && ATyp.subtypeList l1 l2
  | _, _ => false

/-- `AST.proj_inj_type` -/
theorem XType.proj_inj (t : ATyp) : t.inj.proj = t := by
  cases t <;> rfl

/-- `AST.proj_sig_args` -/
def Signature.projArgs (s : Signature) : List ATyp := s.sig_args.map XType.proj
/-- `AST.proj_sig_res` -/
def Signature.projRes (s : Signature) : ATyp := s.sig_res.proj

/-- `AST.signature_main` -/
def signature_main : Signature := mksignature [] .Xint cc_default

/-- `AST.type_of_Mptr` -/
theorem Chunk.typ_Mptr : Mptr.typ = Tptr := by
  simp [Mptr, Tptr, Archi.ptr64, Chunk.typ]

/-- `AST.chunk_of_Tptr` -/
theorem Chunk.ofTyp_Tptr : Chunk.ofTyp Tptr = Mptr := by
  simp [Mptr, Tptr, Archi.ptr64, Chunk.ofTyp]

/-- `AST.proj_xtype_of_chunk` -/
theorem Chunk.proj_xtype (c : Chunk) : c.xtype.proj = c.typ := by
  cases c <;> rfl

/-- `AST.ef_inline`: should the compiler inline this external function? -/
def ExtFun.inline : ExtFun → Bool
  | .EF_external .. | .EF_runtime .. | .EF_malloc | .EF_free => false
  | _ => true

/-- `AST.ef_reloads`: must this external function reload its arguments? -/
def ExtFun.reloads : ExtFun → Bool
  | .EF_annot .. | .EF_debug .. => false
  | _ => true

/-- `AST.init_data_size_pos` -/
theorem InitData.size_nonneg (i : InitData) : i.size ≥ 0 := by
  cases i <;> simp only [InitData.size, Archi.ptr64, if_true] <;>
    first | decide | exact Int.le_max_right _ _

/-- `AST.init_data_list_size_pos` -/
theorem InitData.listSize_nonneg (il : List InitData) : InitData.listSize il ≥ 0 := by
  induction il with
  | nil => decide
  | cons i il ih =>
    show i.size + InitData.listSize il ≥ 0
    exact Int.add_nonneg i.size_nonneg ih

theorem InitData.listSize_cons (i : InitData) (il : List InitData) :
    InitData.listSize (i :: il) = i.size + InitData.listSize il := rfl

/-! ## `PTree_Properties.of_list` -/

namespace PTree
variable {A : Type}

/-- `PTree_Properties.of_list`: the tree built by inserting the pairs of `l`
    in order (later bindings win). -/
def ofList (l : List (Positive × A)) : PTree A :=
  l.foldl (fun m kv => m.set kv.1 kv.2) empty

theorem get_foldl_set_not_mem (l : List (Positive × A)) (m : PTree A) (k : Positive)
    (h : k ∉ l.map Prod.fst) :
    get k (l.foldl (fun m kv => m.set kv.1 kv.2) m) = get k m := by
  induction l generalizing m with
  | nil => rfl
  | cons kv l ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [List.foldl_cons]
    rw [ih _ h.2, gso _ _ _ _ (Ne.symm h.1)]

theorem get_foldl_set_mem (l : List (Positive × A)) (m : PTree A) (k : Positive) (g : A)
    (h : get k (l.foldl (fun m kv => m.set kv.1 kv.2) m) = some g) :
    (k, g) ∈ l ∨ get k m = some g := by
  induction l generalizing m with
  | nil => exact .inr h
  | cons kv l ih =>
    rcases ih _ h with h1 | h1
    · exact .inl (List.mem_cons_of_mem _ h1)
    · by_cases hk : kv.1 = k
      · subst hk; rw [gss] at h1; cases h1; exact .inl (by simp)
      · rw [gso _ _ _ _ hk] at h1; exact .inr h1

/-- `PTree_Properties.in_of_list` -/
theorem in_ofList {l : List (Positive × A)} {k : Positive} {g : A}
    (h : get k (ofList l) = some g) : (k, g) ∈ l := by
  rcases get_foldl_set_mem l empty k g h with h | h
  · exact h
  · simp at h

/-- `PTree_Properties.of_list_dom` -/
theorem ofList_dom {l : List (Positive × A)} {k : Positive} (h : k ∈ l.map Prod.fst) :
    ∃ g, get k (ofList l) = some g := by
  unfold ofList
  generalize (empty : PTree A) = m
  induction l generalizing m with
  | nil => simp at h
  | cons kv l ih =>
    simp only [List.foldl_cons]
    by_cases hk : k ∈ l.map Prod.fst
    · exact ih hk _
    · simp only [List.map_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨kv.2, by rw [get_foldl_set_not_mem _ _ _ hk, gss]⟩
      · exact absurd h hk

/-- `PTree_Properties.of_list_unique` -/
theorem ofList_unique {l1 l2 : List (Positive × A)} {k : Positive} {g : A}
    (h : k ∉ l2.map Prod.fst) : get k (ofList (l1 ++ (k, g) :: l2)) = some g := by
  unfold ofList
  rw [List.foldl_append, List.foldl_cons, get_foldl_set_not_mem _ _ _ h, gss]

/-- `PTree_Properties.of_list_norepet` -/
theorem ofList_norepet {l : List (Positive × A)} {k : Positive} {g : A}
    (hnd : (l.map Prod.fst).Nodup) (h : (k, g) ∈ l) : get k (ofList l) = some g := by
  obtain ⟨l1, l2, rfl⟩ := List.append_of_mem h
  apply ofList_unique
  simp only [List.map_append, List.map_cons] at hnd
  have := (List.nodup_append.mp hnd).2.1
  exact (List.nodup_cons.mp this).1

end PTree

/-! ## Generic programs -/

/-- `AST.program F V` -/
structure ASTProgram (F V : Type) where
  prog_defs : List (Ident × GlobDef F V)
  prog_public : List Ident
  prog_main : Ident

namespace ASTProgram
variable {F V : Type}

/-- `AST.prog_defs_names` -/
def defsNames (p : ASTProgram F V) : List Ident := p.prog_defs.map Prod.fst

/-- `AST.prog_defmap`: if several definitions have the same name, the last one
    wins. -/
def defmap (p : ASTProgram F V) : PTree (GlobDef F V) := PTree.ofList p.prog_defs

/-- `AST.in_prog_defmap` -/
theorem in_defmap {p : ASTProgram F V} {id g} (h : p.defmap.get id = some g) :
    (id, g) ∈ p.prog_defs := PTree.in_ofList h

/-- `AST.prog_defmap_dom` -/
theorem defmap_dom {p : ASTProgram F V} {id} (h : id ∈ p.defsNames) :
    ∃ g, p.defmap.get id = some g := PTree.ofList_dom h

/-- `AST.prog_defmap_unique` -/
theorem defmap_unique {p : ASTProgram F V} {defs1 id g defs2}
    (h : p.prog_defs = defs1 ++ (id, g) :: defs2) (hn : id ∉ defs2.map Prod.fst) :
    p.defmap.get id = some g := by
  unfold defmap; rw [h]; exact PTree.ofList_unique hn

/-- `AST.prog_defmap_norepet` -/
theorem defmap_norepet {p : ASTProgram F V} {id g} (hnd : p.defsNames.Nodup)
    (h : (id, g) ∈ p.prog_defs) : p.defmap.get id = some g :=
  PTree.ofList_norepet hnd h

end ASTProgram

/-! ## Generic transformations over programs -/

section TRANSF_PROGRAM
variable {A B V W : Type}

/-- `AST.transform_program_globdef` -/
def transformProgramGlobdef (transf : A → B) : Ident × GlobDef A V → Ident × GlobDef B V
  | (id, .Gfun f) => (id, .Gfun (transf f))
  | (id, .Gvar v) => (id, .Gvar v)

/-- `AST.transform_program` -/
def transformProgram (transf : A → B) (p : ASTProgram A V) : ASTProgram B V :=
  ⟨p.prog_defs.map (transformProgramGlobdef transf), p.prog_public, p.prog_main⟩

/-- `AST.transf_globvar` -/
def transfGlobvar (transfVar : Ident → V → Res W) (i : Ident) (g : GlobVar V) :
    Res (GlobVar W) :=
  match transfVar i g.gvar_info with
  | .OK info' => .OK ⟨info', g.gvar_init, g.gvar_readonly, g.gvar_volatile⟩
  | .Error msg => .Error msg

/-- `AST.transf_globdefs` -/
def transfGlobdefs (transfFun : Ident → A → Res B) (transfVar : Ident → V → Res W) :
    List (Ident × GlobDef A V) → Res (List (Ident × GlobDef B W))
  | [] => .OK []
  | (id, .Gfun f) :: l' =>
    match transfFun id f with
    | .Error msg => .Error ("In function: " ++ msg)
    | .OK tf =>
      match transfGlobdefs transfFun transfVar l' with
      | .OK tl' => .OK ((id, .Gfun tf) :: tl')
      | .Error msg => .Error msg
  | (id, .Gvar v) :: l' =>
    match transfGlobvar transfVar id v with
    | .Error msg => .Error ("In variable: " ++ msg)
    | .OK tv =>
      match transfGlobdefs transfFun transfVar l' with
      | .OK tl' => .OK ((id, .Gvar tv) :: tl')
      | .Error msg => .Error msg

/-- `AST.transform_partial_program2` -/
def transformPartialProgram2 (transfFun : Ident → A → Res B) (transfVar : Ident → V → Res W)
    (p : ASTProgram A V) : Res (ASTProgram B W) :=
  match transfGlobdefs transfFun transfVar p.prog_defs with
  | .OK gl' => .OK ⟨gl', p.prog_public, p.prog_main⟩
  | .Error msg => .Error msg

/-- `AST.transform_partial_program` -/
def transformPartialProgram (transfFun : A → Res B) (p : ASTProgram A V) :
    Res (ASTProgram B V) :=
  transformPartialProgram2 (fun _ f => transfFun f) (fun _ v => .OK v) p

/-- `AST.transform_program_partial_program` -/
theorem transform_program_partial_program (transfFun : A → B) (p : ASTProgram A V) :
    transformPartialProgram (fun f => .OK (transfFun f)) p = .OK (transformProgram transfFun p) := by
  have key : ∀ l : List (Ident × GlobDef A V),
      transfGlobdefs (fun _ f => .OK (transfFun f)) (fun _ (v : V) => .OK v) l =
      .OK (l.map (transformProgramGlobdef transfFun)) := by
    intro l
    induction l with
    | nil => rfl
    | cons idg l ih =>
      obtain ⟨id, g⟩ := idg
      cases g <;> simp [transfGlobdefs, transfGlobvar, ih, transformProgramGlobdef]
  simp [transformPartialProgram, transformPartialProgram2, key, transformProgram]

end TRANSF_PROGRAM

/-! ## Transformations of function definitions -/

section TRANSF_FUNDEF
variable {A B : Type}

/-- `AST.transf_fundef` (for `Ctypes.fundef`) -/
def transfFundef (transf : A → B) : FunDefGen A → FunDefGen B
  | .Internal f => .Internal (transf f)
  | .External ef targs tres cc => .External ef targs tres cc

/-- `AST.transf_partial_fundef` (for `Ctypes.fundef`) -/
def transfPartialFundef (transfPartial : A → Res B) : FunDefGen A → Res (FunDefGen B)
  | .Internal f =>
    match transfPartial f with
    | .OK f' => .OK (.Internal f')
    | .Error msg => .Error msg
  | .External ef targs tres cc => .OK (.External ef targs tres cc)

theorem transfPartialFundef_OK (transf : A → B) (fd : FunDefGen A) :
    transfPartialFundef (fun f => .OK (transf f)) fd = .OK (transfFundef transf fd) := by
  cases fd <;> rfl

end TRANSF_FUNDEF

/-! ## Register pairs (`rpair`) -/

/-- `AST.rpair` -/
inductive RPair (A : Type) where
  | One (r : A)
  | Twolong (rhi rlo : A)
  deriving DecidableEq, Repr

namespace RPair
variable {A B : Type}

/-- `AST.typ_rpair` -/
def typ (typOf : A → ATyp) : RPair A → ATyp
  | .One r => typOf r
  | .Twolong _ _ => .Tlong

/-- `AST.map_rpair` -/
def map (f : A → B) : RPair A → RPair B
  | .One r => .One (f r)
  | .Twolong rhi rlo => .Twolong (f rhi) (f rlo)

/-- `AST.regs_of_rpair` -/
def regs : RPair A → List A
  | .One r => [r]
  | .Twolong rhi rlo => [rhi, rlo]

/-- `AST.regs_of_rpairs` -/
def regsList : List (RPair A) → List A
  | [] => []
  | p :: l => regs p ++ regsList l

/-- `AST.in_regs_of_rpairs` -/
theorem in_regsList {x : A} {p : RPair A} {l : List (RPair A)} (hx : x ∈ regs p)
    (hp : p ∈ l) : x ∈ regsList l := by
  induction l with
  | nil => simp at hp
  | cons q l ih =>
    simp only [regsList, List.mem_append]
    rcases List.mem_cons.mp hp with rfl | hp
    · exact .inl hx
    · exact .inr (ih hp)

/-- `AST.in_regs_of_rpairs_inv` -/
theorem in_regsList_inv {x : A} {l : List (RPair A)} (h : x ∈ regsList l) :
    ∃ p, p ∈ l ∧ x ∈ regs p := by
  induction l with
  | nil => simp [regsList] at h
  | cons q l ih =>
    simp only [regsList, List.mem_append] at h
    rcases h with h | h
    · exact ⟨q, List.mem_cons_self, h⟩
    · obtain ⟨p, hp, hx⟩ := ih h; exact ⟨p, List.mem_cons_of_mem _ hp, hx⟩

/-- `AST.forall_rpair` -/
def Forall (P : A → Prop) : RPair A → Prop
  | .One r => P r
  | .Twolong rhi rlo => P rhi ∧ P rlo

end RPair

/-! ## Arguments and results of builtins -/

/-- `AST.builtin_arg` -/
inductive BuiltinArg (A : Type) where
  | BA (x : A)
  | BA_int (n : Integers.Int)
  | BA_long (n : Integers.Int64)
  | BA_float (f : Floats.Float)
  | BA_single (f : Floats.Float32)
  | BA_loadstack (chunk : Chunk) (ofs : Integers.Ptrofs)
  | BA_addrstack (ofs : Integers.Ptrofs)
  | BA_loadglobal (chunk : Chunk) (id : Ident) (ofs : Integers.Ptrofs)
  | BA_addrglobal (id : Ident) (ofs : Integers.Ptrofs)
  | BA_splitlong (hi lo : BuiltinArg A)
  | BA_addptr (a1 a2 : BuiltinArg A)
  deriving DecidableEq

/-- `AST.builtin_res` -/
inductive BuiltinRes (A : Type) where
  | BR (x : A)
  | BR_none
  | BR_splitlong (hi lo : BuiltinRes A)

namespace BuiltinArg
variable {A B : Type}

/-- `AST.globals_of_builtin_arg` -/
def globals : BuiltinArg A → List Ident
  | .BA_loadglobal _ id _ => [id]
  | .BA_addrglobal id _ => [id]
  | .BA_splitlong hi lo => globals hi ++ globals lo
  | .BA_addptr a1 a2 => globals a1 ++ globals a2
  | _ => []

/-- `AST.globals_of_builtin_args` -/
def globalsList (al : List (BuiltinArg A)) : List Ident := al.flatMap globals

/-- `AST.params_of_builtin_arg` -/
def params : BuiltinArg A → List A
  | .BA x => [x]
  | .BA_splitlong hi lo => params hi ++ params lo
  | .BA_addptr a1 a2 => params a1 ++ params a2
  | _ => []

/-- `AST.params_of_builtin_args` -/
def paramsList (al : List (BuiltinArg A)) : List A := al.flatMap params

/-- `AST.map_builtin_arg` -/
def map (f : A → B) : BuiltinArg A → BuiltinArg B
  | .BA x => .BA (f x)
  | .BA_int n => .BA_int n
  | .BA_long n => .BA_long n
  | .BA_float n => .BA_float n
  | .BA_single n => .BA_single n
  | .BA_loadstack chunk ofs => .BA_loadstack chunk ofs
  | .BA_addrstack ofs => .BA_addrstack ofs
  | .BA_loadglobal chunk id ofs => .BA_loadglobal chunk id ofs
  | .BA_addrglobal id ofs => .BA_addrglobal id ofs
  | .BA_splitlong hi lo => .BA_splitlong (map f hi) (map f lo)
  | .BA_addptr a1 a2 => .BA_addptr (map f a1) (map f a2)

end BuiltinArg

namespace BuiltinRes
variable {A B : Type}

/-- `AST.params_of_builtin_res` -/
def params : BuiltinRes A → List A
  | .BR x => [x]
  | .BR_none => []
  | .BR_splitlong hi lo => params hi ++ params lo

/-- `AST.map_builtin_res` -/
def map (f : A → B) : BuiltinRes A → BuiltinRes B
  | .BR x => .BR (f x)
  | .BR_none => .BR_none
  | .BR_splitlong hi lo => .BR_splitlong (map f hi) (map f lo)

end BuiltinRes

/-- `AST.builtin_arg_constraint` -/
inductive BuiltinArgConstraint where
  | OK_default | OK_const | OK_addrstack | OK_addressing | OK_all

end CC
