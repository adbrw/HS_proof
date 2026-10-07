import HSFormal.Compression
import HSFormal.GraphCorner
import Mathlib.Algebra.Homology.HomotopyCategory

/-!
# The graph corner for chain complexes up to homotopy

Instantiates the abstract interface of `HSFormal.GraphCorner` with the paper's data: `𝒦` is the
homotopy category of `ℤ`-graded chain complexes over a preadditive category with a strict
involution, the duality is Ranicki's `C ↦ C^{N-*}` of `HSFormal.Compression`, and the bidual
map is `ε_r = (-1)^{r(N-r)}` (manuscript §5). The abstract transposition then coincides with
`transposeFamily`. A homotopy action by homotopy isometries with *specified* homotopies (the
hypotheses (5.1)) yields the data `A : G →* End C` and `IsIsometryAction` used by
`GraphCorner.lemma_5_2`.
-/

namespace HSFormal.GraphCorner

open CategoryTheory Category Limits Preadditive Opposite HomologicalComplex HSFormal.Compression

noncomputable section

variable {V : Type*} [Category V] [Preadditive V] (J : StrictInvolution V) (N : ℤ)

/-- The homotopy category `K(V)` of `ℤ`-graded chain complexes. -/
abbrev ChainHomotopyCategory (V : Type*) [Category V] [Preadditive V] :=
  HomotopyCategory V (ComplexShape.down ℤ)

/-- Ranicki's duality `C ↦ C^{N-*}` as a functor on chain complexes. -/
@[simps, reducible]
def chainDual : (ChainComplex V ℤ)ᵒᵖ ⥤ ChainComplex V ℤ where
  obj D := dualComplex J N D.unop
  map f := dualHom J N f.unop

instance : (chainDual J N).Additive where
  map_add := by
    intros
    ext
    simp [J.star_add]

/-- The duality on `K(V)`: homotopic maps have homotopic duals. -/
def homotopyDualAux : ChainHomotopyCategory V ⥤ (ChainHomotopyCategory V)ᵒᵖ :=
  CategoryTheory.Quotient.lift _
    ((chainDual J N).rightOp ⋙ (HomotopyCategory.quotient V (ComplexShape.down ℤ)).op)
    fun _ _ _ _ ⟨h⟩ ↦ Quiver.Hom.unop_inj
      (HomotopyCategory.eq_of_homotopy _ _ (dualHomotopy J N h))

instance : (homotopyDualAux J N).Additive := by
  have : (HomotopyCategory.quotient V (ComplexShape.down ℤ) ⋙ homotopyDualAux J N).Additive :=
    inferInstanceAs ((chainDual J N).rightOp ⋙
      (HomotopyCategory.quotient V (ComplexShape.down ℤ)).op).Additive
  exact Functor.additive_of_full_essSurj_comp (HomotopyCategory.quotient V _) _

/-- Ranicki's duality on the homotopy category. -/
def homotopyDual : (ChainHomotopyCategory V)ᵒᵖ ⥤ ChainHomotopyCategory V :=
  (homotopyDualAux J N).leftOp

instance : (homotopyDual J N).Additive := by
  dsimp [homotopyDual]
  infer_instance

@[simp]
lemma dualMap_homotopyDual_quotient_map {C D : ChainComplex V ℤ} (f : C ⟶ D) :
    dualMap (homotopyDual J N) ((HomotopyCategory.quotient V _).map f) =
      (HomotopyCategory.quotient V _).map (dualHom J N f) := rfl

lemma eqToHom_comp_d (D : ChainComplex V ℤ) {a b a' b' : ℤ} (ha : a = a') (hb : b = b') :
    eqToHom (congrArg D.X ha) ≫ D.d a' b' = D.d a b ≫ eqToHom (congrArg D.X hb) := by
  subst ha hb
  simp

lemma f_comp_eqToHom {D D' : ChainComplex V ℤ} (f : D ⟶ D') {a a' : ℤ} (h : a = a') :
    f.f a ≫ eqToHom (congrArg D'.X h) = eqToHom (congrArg D.X h) ≫ f.f a' := by
  subst h
  simp

/-- The canonical bidual chain isomorphism, multiplication by `ε_r = (-1)^{r(N-r)}`. -/
@[simps]
def bidual (D : ChainComplex V ℤ) : dualComplex J N (dualComplex J N D) ⟶ D where
  f r := (r * (N - r)).negOnePow • eqToHom (congrArg D.X (sub_sub_cancel N r))
  comm' r r' h := by
    simp only [ComplexShape.down_Rel] at h
    subst h
    simp only [dualComplex_d, J.star_units_smul, J.star_star, Linear.units_smul_comp,
      Linear.comp_units_smul, smul_smul]
    rw [eqToHom_comp_d D (sub_sub_cancel N (r' + 1)) (sub_sub_cancel N r')]
    congr 1
    rw [← Int.negOnePow_add, ← Int.negOnePow_add, Int.negOnePow_eq_iff]
    exact ⟨-r' - 1, by ring⟩

@[reassoc]
lemma bidual_naturality {D D' : ChainComplex V ℤ} (f : D ⟶ D') :
    dualHom J N (dualHom J N f) ≫ bidual J N D' = bidual J N D ≫ f := by
  ext r
  simp only [comp_f, dualHom_f, J.star_star, bidual_f, Linear.comp_units_smul,
    Linear.units_smul_comp]
  rw [f_comp_eqToHom f (sub_sub_cancel N r)]

/-- The bidual map `ε : C^{N-*N-*} ⟶ C` on the homotopy category. -/
def homotopyBidual : (homotopyDual J N).rightOp ⋙ homotopyDual J N ⟶ 𝟭 _ where
  app X := (HomotopyCategory.quotient V _).map (bidual J N X.as)
  naturality X Y f := by
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient V _).map_surjective f
    change (HomotopyCategory.quotient V _).map (dualHom J N (dualHom J N f)) ≫ _ = _
    exact ((HomotopyCategory.quotient V _).map_comp _ _).symm.trans
      ((congrArg (HomotopyCategory.quotient V _).map (bidual_naturality J N f)).trans
        ((HomotopyCategory.quotient V _).map_comp _ _))

/-- With `ε_r = (-1)^{r(N-r)}`, the abstract transposition is Ranicki's
`(Tφ)_r = (-1)^{r(N-r)} φ_{N-r}^*` of `HSFormal.Compression.transposeFamily`. -/
theorem transpose_quotient_map {D : ChainComplex V ℤ} (φ : dualComplex J N D ⟶ D) :
    transpose (homotopyDual J N) (homotopyBidual J N) ((HomotopyCategory.quotient V _).map φ) =
      (HomotopyCategory.quotient V _).map (dualHom J N φ ≫ bidual J N D) := by
  rfl

theorem dualHom_comp_bidual_f {D : ChainComplex V ℤ} (φ : dualComplex J N D ⟶ D) (r : ℤ) :
    (dualHom J N φ ≫ bidual J N D).f r = transposeFamily J N D.X (fun s ↦ φ.f s) r := by
  simp [transposeFamily, Linear.comp_units_smul]

/-- A homotopy action of `G` on `(C, φ)` by homotopy isometries with specified homotopies
(manuscript (5.1)): `A_1 = 1`, `A_gA_h ≃ A_{gh}`, `A_gφ ≃ φA_{g⁻¹}^*`. -/
structure HomotopyIsometryAction (G : Type) [Group G] (C : ChainComplex V ℤ)
    (φ : dualComplex J N C ⟶ C) where
  /-- The chain maps `A_g`. -/
  act : G → (C ⟶ C)
  act_one : act 1 = 𝟙 C
  /-- `A_g A_h ≃ A_{gh}`. -/
  mul : ∀ g h, Homotopy (act h ≫ act g) (act (g * h))
  /-- `A_g φ ≃ φ A_{g⁻¹}^*`. -/
  isometry : ∀ g, Homotopy (φ ≫ act g) (dualHom J N (act g⁻¹) ≫ φ)

namespace HomotopyIsometryAction

variable {J N} {G : Type} [Group G] {C : ChainComplex V ℤ} {φ : dualComplex J N C ⟶ C}
  (a : HomotopyIsometryAction J N G C φ)

/-- The action in the homotopy category. -/
def toEnd : G →* End ((HomotopyCategory.quotient V (ComplexShape.down ℤ)).obj C) where
  toFun g := (HomotopyCategory.quotient V _).map (a.act g)
  map_one' := by
    rw [a.act_one, CategoryTheory.Functor.map_id]
    rfl
  map_mul' g h := by
    rw [End.mul_def, ← CategoryTheory.Functor.map_comp]
    exact (HomotopyCategory.eq_of_homotopy _ _ (a.mul g h)).symm

theorem isIsometryAction :
    IsIsometryAction (homotopyDual J N) a.toEnd ((HomotopyCategory.quotient V _).map φ) := by
  intro g
  change (HomotopyCategory.quotient V _).map φ ≫ (HomotopyCategory.quotient V _).map (a.act g) =
    (HomotopyCategory.quotient V _).map (dualHom J N (a.act g⁻¹)) ≫
      (HomotopyCategory.quotient V _).map φ
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact HomotopyCategory.eq_of_homotopy _ _ (a.isometry g)

end HomotopyIsometryAction

section Graph

variable {J N} [Linear ℚ V] {G : Type} [Group G] [Fintype G] {C : ChainComplex V ℤ}
  {φ : dualComplex J N C ⟶ C} (a : HomotopyIsometryAction J N G C φ) [HasBiproduct fun _ : G ↦ C]

/-- The quotient functor carries the chain-level graph idempotent `q⁻¹ Σ_g A_g ⊗ R_{g⁻¹}` to the
graph idempotent of the induced action on `K(V)`. -/
theorem quotient_map_graphIdem :
    (HomotopyCategory.quotient V _).map (graphIdem a.act) =
      (graphMapIso (HomotopyCategory.quotient V _)).hom ≫ graphIdem a.toEnd ≫
        (graphMapIso (HomotopyCategory.quotient V _)).inv :=
  map_graphIdem _ _

omit [Linear ℚ V] [Group G] in
theorem quotient_map_graphForm :
    (HomotopyCategory.quotient V _).map (graphForm (G := G) (chainDual J N) φ) =
      dualMap (homotopyDual J N) (graphMapIso (HomotopyCategory.quotient V _)).inv ≫
        graphForm (homotopyDual J N) ((HomotopyCategory.quotient V _).map φ) ≫
        (graphMapIso (HomotopyCategory.quotient V _)).inv := by
  simp only [graphForm, Functor.map_sum, sum_comp, comp_sum, CategoryTheory.Functor.map_comp,
    assoc]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  have hι : (HomotopyCategory.quotient V _).map (biproduct.ι (fun _ : G ↦ C) g) =
      biproduct.ι _ g ≫ (graphMapIso (HomotopyCategory.quotient V _)).inv := by
    simp
  rw [← dualMap_comp_assoc, ← hι]
  erw [Category.assoc, ← hι]
  rfl

/-- Lemma 5.1's hypothesis `E² ≃ E`, with a specified homotopy, for the chain-level graph
idempotent of a homotopy action. -/
def graphIdemHomotopy : Homotopy (graphIdem a.act ≫ graphIdem a.act) (graphIdem a.act) :=
  HomotopyCategory.homotopyOfEq _ _ (by
    rw [CategoryTheory.Functor.map_comp, quotient_map_graphIdem]
    simp only [assoc, Iso.inv_hom_id_assoc, graphIdem_comp_graphIdem_assoc])

/-- Lemma 5.1's hypothesis `EΦ ≃ ΦE^*`, with a specified homotopy, for the chain-level graph
idempotent and graph form `Φ = φ ⊗ 1`. -/
def graphFormHomotopy :
    Homotopy (graphForm (chainDual J N) φ ≫ graphIdem a.act)
      (dualHom J N (graphIdem a.act) ≫ graphForm (chainDual J N) φ) :=
  HomotopyCategory.homotopyOfEq _ _ (by
    have h := graphForm_comp_graphIdem a.toEnd a.isIsometryAction
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      ← dualMap_homotopyDual_quotient_map, quotient_map_graphIdem, quotient_map_graphForm]
    simp only [dualMap_comp, assoc]
    repeat erw [Category.assoc]
    erw [Iso.inv_hom_id_assoc]
    erw [← dualMap_comp_assoc (homotopyDual J N) (graphMapIso _).inv (graphMapIso _).hom]
    rw [Iso.inv_hom_id, dualMap_id, id_comp]
    erw [reassoc_of% h])

/-- Manuscript Lemma 5.2 for a homotopy action on a chain complex: every splitting, in the
homotopy category, of the graph idempotent of the homotopy action is homotopy equivalent to `C`
by `w = uι`, and `w φ_D w^* ≃ φ`. -/
theorem lemma_5_2_chain {D : ChainHomotopyCategory V} (R : Retract D (graph G _))
    (hR : R.r ≫ R.i = graphIdem a.toEnd) :
    dualMap (homotopyDual J N) (cornerToSheet a.toEnd R) ≫
        cornerForm (homotopyDual J N) (order G)
          (graphForm (homotopyDual J N) ((HomotopyCategory.quotient V _).map φ)) R ≫
        cornerToSheet a.toEnd R = (HomotopyCategory.quotient V _).map φ ∧
      IsIso (cornerToSheet a.toEnd R) :=
  ⟨lemma_5_2 hR a.isIsometryAction, (cornerIso hR).isIso_hom⟩

end Graph

end

end HSFormal.GraphCorner
