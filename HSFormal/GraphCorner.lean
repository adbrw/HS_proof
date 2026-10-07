import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Idempotents.Basic
import Mathlib.CategoryTheory.Retract
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Field.Rat

/-!
# The support-correct graph corner (manuscript §5)

The homotopy-coherent algebra of manuscript §5, in a `ℚ`-linear category `𝒦` in which the
relations hold on the nose; in the application `𝒦` is a homotopy category of bounded complexes,
so equalities below are chain homotopies. The duality is an additive functor `𝔻 : 𝒦ᵒᵖ ⥤ 𝒦`,
`X ↦ X^∨`, `f ↦ f^* = dualMap 𝔻 f`, with Ranicki's transposition `Tφ = ε ∘ φ^*` for a bidual
map `ε : X^∨∨ ⟶ X`. Composition is diagrammatic: the paper's `A_g φ` is `φ ≫ A g`.

A homotopy action of a finite group `G` (order `q`) on `X` by isometries of `φ : X^∨ ⟶ X`
(manuscript (5.1)) is `A : G →* End X` with `IsIsometryAction 𝔻 A φ`. On the graph object
`𝒞 = ⨁_{g ∈ G} X` we define `E = q⁻¹ Σ_g A_g ⊗ R_{g⁻¹}` (5.2), the graph form `Φ = φ ⊗ 1`, the
row `u` (`u_b = A_b`) and column `v` (`v_a = q⁻¹A_{a⁻¹}`), and prove

* (5.3) `E_ab = q⁻¹A_{a⁻¹b}`, `E² = E`, `EΦ = ΦE^*`; `E` commutes with the strict left action;
* (5.6) `uv = 1`, `vu = E`, `uE = u`, `Ev = v`, `v = Ej`, `u = qπ_1E`; (5.7) `uΦu^* = qφ`;
* Lemma 5.1 (algebraic content): in an idempotent-complete `𝒦` an idempotent `E` with
  `EΦ = ΦE^*` splits, and the corner form `φ_D = q⁻¹ rΦr^*` is Poincaré with inverse
  `b_D = q ι^*Φ⁻¹ι`, symmetric if `Φ` is, and independent of the splitting up to isometry;
* Lemma 5.2 / (5.8): for every splitting `D` of the graph idempotent, `w = uι` and `z = rv` are
  inverse and `w φ_D w^* = φ`.

`graphIdem` is defined for any family `A : G → End X`, and additive `ℚ`-linear functors carry it
to the graph idempotent of the image family (`map_graphIdem`); this transports the identities
from a homotopy category back to chain homotopies (`HSFormal.GraphCornerChain`).

In `𝒦` itself `E` is split by `(v, u)` (`graphRetract`); the content of Lemma 5.1 is the
splitting in the equivariant category, where `u, v` are unavailable, and Lemma 5.2 applies to
its image under any duality-preserving forgetful functor.
-/

namespace HSFormal.GraphCorner

open CategoryTheory Category Limits Preadditive Opposite

noncomputable section

variable {𝒦 : Type*} [Category 𝒦]

section Duality

variable (𝔻 : 𝒦ᵒᵖ ⥤ 𝒦)

/-- The dual `f^* : Y^∨ ⟶ X^∨` of `f : X ⟶ Y`. -/
def dualMap {X Y : 𝒦} (f : X ⟶ Y) : 𝔻.obj (op Y) ⟶ 𝔻.obj (op X) := 𝔻.map f.op

@[reassoc (attr := simp)]
lemma dualMap_comp {X Y Z : 𝒦} (f : X ⟶ Y) (g : Y ⟶ Z) :
    dualMap 𝔻 (f ≫ g) = dualMap 𝔻 g ≫ dualMap 𝔻 f := by
  simp [dualMap]

@[simp]
lemma dualMap_id (X : 𝒦) : dualMap 𝔻 (𝟙 X) = 𝟙 _ := by simp [dualMap]

variable (ε : 𝔻.rightOp ⋙ 𝔻 ⟶ 𝟭 𝒦)

/-- Ranicki's transposition `Tφ = ε ∘ φ^*` of a form `φ : X^∨ ⟶ X`, for a bidual
identification `ε : X^∨∨ ⟶ X`; `φ` is symmetric when `Tφ = φ`. -/
def transpose {X : 𝒦} (φ : 𝔻.obj (op X) ⟶ X) : 𝔻.obj (op X) ⟶ X := dualMap 𝔻 φ ≫ ε.app X

variable {𝔻}

/-- `T(f Φ f^*) = f (TΦ) f^*`. -/
lemma transpose_conj {X Y : 𝒦} (φ : 𝔻.obj (op X) ⟶ X) (f : X ⟶ Y) :
    transpose 𝔻 ε (dualMap 𝔻 f ≫ φ ≫ f) = dualMap 𝔻 f ≫ transpose 𝔻 ε φ ≫ f := by
  have h : dualMap 𝔻 (dualMap 𝔻 f) ≫ ε.app Y = ε.app X ≫ f := ε.naturality f
  simp only [transpose, dualMap_comp, assoc, h]

variable (𝔻) [Preadditive 𝒦] [𝔻.Additive]

/-- `f ↦ f^*` as an additive map. -/
def dualMapHom (X Y : 𝒦) : (X ⟶ Y) →+ (𝔻.obj (op Y) ⟶ 𝔻.obj (op X)) :=
  AddMonoidHom.mk' (dualMap 𝔻) fun f g ↦ by simp [dualMap]

@[simp]
lemma dualMap_add {X Y : 𝒦} (f g : X ⟶ Y) : dualMap 𝔻 (f + g) = dualMap 𝔻 f + dualMap 𝔻 g :=
  map_add (dualMapHom 𝔻 X Y) f g

@[simp]
lemma dualMap_zero {X Y : 𝒦} : dualMap 𝔻 (0 : X ⟶ Y) = 0 := map_zero (dualMapHom 𝔻 X Y)

@[simp]
lemma dualMap_sum {X Y : 𝒦} {ι : Type*} (s : Finset ι) (f : ι → (X ⟶ Y)) :
    dualMap 𝔻 (∑ i ∈ s, f i) = ∑ i ∈ s, dualMap 𝔻 (f i) :=
  map_sum (dualMapHom 𝔻 X Y) f s

variable {𝔻}

lemma transpose_sum {X : 𝒦} {ι : Type*} (s : Finset ι) (φ : ι → (𝔻.obj (op X) ⟶ X)) :
    transpose 𝔻 ε (∑ i ∈ s, φ i) = ∑ i ∈ s, transpose 𝔻 ε (φ i) := by
  simp [transpose, sum_comp]

variable [Linear ℚ 𝒦]

@[simp]
lemma dualMap_smul {X Y : 𝒦} (c : ℚ) (f : X ⟶ Y) : dualMap 𝔻 (c • f) = c • dualMap 𝔻 f :=
  map_rat_smul (dualMapHom 𝔻 X Y) c f

@[simp]
lemma transpose_smul {X : 𝒦} (c : ℚ) (φ : 𝔻.obj (op X) ⟶ X) :
    transpose 𝔻 ε (c • φ) = c • transpose 𝔻 ε φ := by
  simp [transpose]

end Duality

section Action

variable {G : Type} [Group G] {X : 𝒦} (A : G →* End X)

/-- A homotopy action in diagrammatic order: `A_g A_h = A_{gh}` reads `A h ≫ A g = A (g * h)`. -/
lemma act_comp (g h : G) : A g ≫ A h = A (h * g) := by
  rw [map_mul, End.mul_def]

lemma act_one : A 1 = 𝟙 X := by rw [map_one, End.one_def]

@[reassoc (attr := simp)]
lemma act_inv_comp (g : G) : A g⁻¹ ≫ A g = 𝟙 X := by
  rw [act_comp, mul_inv_cancel, act_one]

@[reassoc (attr := simp)]
lemma act_comp_inv (g : G) : A g ≫ A g⁻¹ = 𝟙 X := by
  rw [act_comp, inv_mul_cancel, act_one]

/-- Manuscript (5.1), isometry part: `A_g φ = φ A_{g⁻¹}^*`. -/
def IsIsometryAction (𝔻 : 𝒦ᵒᵖ ⥤ 𝒦) (A : G →* End X) (φ : 𝔻.obj (op X) ⟶ X) : Prop :=
  ∀ g, φ ≫ A g = dualMap 𝔻 (A g⁻¹) ≫ φ

end Action

/-- The group order `q = |G|` as a rational scalar. -/
abbrev order (G : Type) [Fintype G] : ℚ := Fintype.card G

lemma order_ne_zero {G : Type} [Fintype G] [Nonempty G] : order G ≠ 0 :=
  Nat.cast_ne_zero.mpr Fintype.card_ne_zero

section Graph

variable [Preadditive 𝒦] {G : Type} {X : 𝒦} [HasBiproduct fun _ : G ↦ X]

variable (G X) in
/-- The graph object `𝒞 = X ⊗ ℚ[G] = ⨁_{g ∈ G} X`, one sheet for each group element. -/
abbrev graph : 𝒦 := ⨁ fun _ : G ↦ X

@[reassoc]
lemma ι_π_graph [DecidableEq G] (a b : G) :
    biproduct.ι (fun _ : G ↦ X) b ≫ biproduct.π _ a = if b = a then 𝟙 X else 0 := by
  rw [biproduct.ι_π]
  split_ifs <;> simp

/-- The sheetwise endomorphism `f ⊗ 1`. -/
def sheetwise (f : X ⟶ X) : graph G X ⟶ graph G X := biproduct.map fun _ ↦ f

section GraphForm

variable (𝔻 : 𝒦ᵒᵖ ⥤ 𝒦) (φ : 𝔻.obj (op X) ⟶ X) [Fintype G]

/-- Manuscript (5.2): the graph form `Φ = φ ⊗ 1 : 𝒞^∨ ⟶ 𝒞`. -/
def graphForm : 𝔻.obj (op (graph G X)) ⟶ graph G X :=
  ∑ g, dualMap 𝔻 (biproduct.ι (fun _ : G ↦ X) g) ≫ φ ≫ biproduct.ι (fun _ : G ↦ X) g

@[reassoc (attr := simp)]
lemma graphForm_π (a : G) :
    graphForm 𝔻 φ ≫ biproduct.π (fun _ : G ↦ X) a =
      dualMap 𝔻 (biproduct.ι (fun _ : G ↦ X) a) ≫ φ := by
  classical
  simp only [graphForm, sum_comp, assoc, ι_π_graph, comp_ite, comp_id, comp_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

variable [𝔻.Additive]

/-- The duals of the sheet projections and inclusions exhibit `𝒞^∨` as `⨁_g X^∨`. -/
lemma dual_graph_hom_ext {Z : 𝒦} {f f' : 𝔻.obj (op (graph G X)) ⟶ Z}
    (h : ∀ b, dualMap 𝔻 (biproduct.π (fun _ : G ↦ X) b) ≫ f =
      dualMap 𝔻 (biproduct.π (fun _ : G ↦ X) b) ≫ f') : f = f' := by
  have hid : ∑ b, dualMap 𝔻 (biproduct.ι (fun _ : G ↦ X) b) ≫
      dualMap 𝔻 (biproduct.π (fun _ : G ↦ X) b) = 𝟙 _ := by
    simp_rw [← dualMap_comp]
    rw [← dualMap_sum, biproduct.total, dualMap_id]
  rw [← id_comp f, ← id_comp f', ← hid]
  simp only [sum_comp, assoc, h]

omit [Fintype G] in
@[reassoc]
lemma dualMap_π_comp_dualMap_ι [DecidableEq G] (a b : G) :
    dualMap 𝔻 (biproduct.π (fun _ : G ↦ X) b) ≫ dualMap 𝔻 (biproduct.ι (fun _ : G ↦ X) a) =
      if a = b then 𝟙 _ else 0 := by
  rw [← dualMap_comp, ι_π_graph]
  split_ifs <;> simp

@[reassoc (attr := simp)]
lemma dualMap_π_graphForm (b : G) :
    dualMap 𝔻 (biproduct.π (fun _ : G ↦ X) b) ≫ graphForm 𝔻 φ =
      φ ≫ biproduct.ι (fun _ : G ↦ X) b := by
  classical
  simp only [graphForm, comp_sum, dualMap_π_comp_dualMap_ι_assoc, ite_comp, id_comp, zero_comp,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- `Φ` is an isomorphism (Poincaré) when `φ` is. -/
instance [IsIso φ] : IsIso (graphForm (G := G) 𝔻 φ) := by
  classical
  refine ⟨∑ g, biproduct.π (fun _ : G ↦ X) g ≫ inv φ ≫ dualMap 𝔻 (biproduct.π _ g), ?_, ?_⟩
  · apply dual_graph_hom_ext 𝔻
    intro b
    simp only [dualMap_π_graphForm_assoc, comp_sum, ι_π_graph_assoc, ite_comp, id_comp, zero_comp,
      comp_ite, comp_zero, IsIso.hom_inv_id_assoc, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      comp_id]
  · ext a b
    simp only [sum_comp, assoc, graphForm_π, comp_sum, dualMap_π_comp_dualMap_ι_assoc, ite_comp,
      id_comp, zero_comp, comp_ite, comp_zero, IsIso.inv_hom_id, comp_id, ι_π_graph]
    simp [Finset.sum_ite_eq, eq_comm]

/-- `Φ = φ ⊗ 1` is symmetric when `φ` is. -/
theorem transpose_graphForm (ε : 𝔻.rightOp ⋙ 𝔻 ⟶ 𝟭 𝒦) :
    transpose 𝔻 ε (graphForm (G := G) 𝔻 φ) = graphForm 𝔻 (transpose 𝔻 ε φ) := by
  simp only [graphForm, transpose_sum, transpose_conj]

end GraphForm

variable [Group G]

/-- The right translation `R_g`, sending sheet `b` to sheet `b g`. -/
def rightTranslation (g : G) : graph G X ⟶ graph G X :=
  biproduct.desc fun b ↦ biproduct.ι (fun _ : G ↦ X) (b * g)

/-- The strict left action `L_g`, sending sheet `b` to sheet `g b`. -/
def leftTranslation (g : G) : graph G X ⟶ graph G X :=
  biproduct.desc fun b ↦ biproduct.ι (fun _ : G ↦ X) (g * b)

section Families

variable (A : G → End X)

/-- The graph row `u = q π_1 E`, with components `u_b = A_b`. -/
def graphRow : graph G X ⟶ X := biproduct.desc fun b ↦ A b

omit [Group G] in
@[reassoc (attr := simp)]
lemma ι_graphRow (b : G) : biproduct.ι _ b ≫ graphRow A = A b := by
  simp [graphRow]

variable [Fintype G] [Linear ℚ 𝒦]

/-- Manuscript (5.2): the graph idempotent `E = q⁻¹ Σ_g A_g ⊗ R_{g⁻¹}`. -/
def graphIdem : graph G X ⟶ graph G X :=
  (order G)⁻¹ • ∑ g, sheetwise (A g) ≫ rightTranslation g⁻¹

/-- The graph column `v = E j`, with components `v_a = q⁻¹ A_{a⁻¹}`. -/
def graphCol : X ⟶ graph G X := (order G)⁻¹ • biproduct.lift fun a ↦ A a⁻¹

@[reassoc (attr := simp)]
lemma graphCol_π (a : G) : graphCol A ≫ biproduct.π _ a = (order G)⁻¹ • A a⁻¹ := by
  simp [graphCol]

/-- Manuscript (5.3): the entry of `E` from sheet `b` to sheet `a` is `q⁻¹ A_{a⁻¹b}`. -/
theorem ι_graphIdem_π (a b : G) :
    biproduct.ι _ b ≫ graphIdem A ≫ biproduct.π _ a = (order G)⁻¹ • A (a⁻¹ * b) := by
  classical
  simp only [graphIdem, sheetwise, rightTranslation, Linear.comp_smul, Linear.smul_comp,
    sum_comp, comp_sum, assoc, biproduct.ι_map_assoc, biproduct.ι_desc_assoc, ι_π_graph]
  rw [Finset.sum_eq_single (a⁻¹ * b)]
  · simp
  · intro g _ hg
    rw [ite_eq_right, comp_zero]
    rintro rfl
    exact hg (by simp [mul_assoc])
  · simp

section Map

variable {𝒦' : Type*} [Category 𝒦'] [Preadditive 𝒦'] [Linear ℚ 𝒦'] (F : 𝒦 ⥤ 𝒦') [F.Additive]
  [HasBiproduct fun _ : G ↦ F.obj X]

/-- The comparison `F(⨁_g X) ≅ ⨁_g F X` for an additive functor. -/
@[simps]
def graphMapIso : F.obj (graph G X) ≅ graph G (F.obj X) where
  hom := biproduct.lift fun g ↦ F.map (biproduct.π (fun _ : G ↦ X) g)
  inv := biproduct.desc fun g ↦ F.map (biproduct.ι (fun _ : G ↦ X) g)
  hom_inv_id := by
    rw [biproduct.lift_desc]
    simp_rw [← F.map_comp]
    rw [← F.map_sum, biproduct.total, F.map_id]
  inv_hom_id := by
    classical
    ext a b
    simp only [biproduct.ι_desc_assoc, assoc, biproduct.lift_π, ← F.map_comp, ι_π_graph, id_comp]
    split_ifs <;> simp

/-- An additive `ℚ`-linear functor carries the graph idempotent of `A` to that of `F ∘ A`. -/
theorem map_graphIdem [F.Linear ℚ] :
    F.map (graphIdem A) =
      (graphMapIso F).hom ≫ graphIdem (fun g ↦ F.map (A g)) ≫ (graphMapIso F).inv := by
  rw [← cancel_epi (graphMapIso F).inv, ← cancel_mono (graphMapIso F).hom]
  simp only [Iso.inv_hom_id_assoc, assoc, Iso.inv_hom_id, comp_id]
  ext b a
  simp only [graphMapIso_inv, graphMapIso_hom, biproduct.ι_desc_assoc, assoc, biproduct.lift_π,
    ← F.map_comp, ι_graphIdem_π, F.map_smul]

end Map

end Families

variable (A : G →* End X) [Fintype G] [Linear ℚ 𝒦]

/-- Manuscript (5.6): `vu = E`. -/
@[reassoc]
theorem graphRow_comp_graphCol : graphRow A ≫ graphCol A = graphIdem A := by
  ext b a
  rw [ι_graphIdem_π, assoc, ι_graphRow_assoc, graphCol_π, Linear.comp_smul, act_comp]

/-- Manuscript (5.6): `uv = 1`. -/
@[reassoc (attr := simp)]
theorem graphCol_comp_graphRow : graphCol A ≫ graphRow A = 𝟙 X := by
  rw [graphCol, graphRow, Linear.smul_comp, biproduct.lift_desc]
  simp only [act_inv_comp, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℚ,
    smul_smul]
  rw [inv_mul_cancel₀ order_ne_zero, one_smul]

/-- Manuscript (5.3): `E² = E`. -/
@[reassoc (attr := simp)]
theorem graphIdem_comp_graphIdem : graphIdem A ≫ graphIdem A = graphIdem A := by
  rw [← graphRow_comp_graphCol, assoc, graphCol_comp_graphRow_assoc]

/-- Manuscript (5.6): `uE = u`. -/
@[reassoc (attr := simp)]
theorem graphIdem_comp_graphRow : graphIdem A ≫ graphRow A = graphRow A := by
  rw [← graphRow_comp_graphCol, assoc, graphCol_comp_graphRow, comp_id]

/-- Manuscript (5.6): `Ev = v`. -/
@[reassoc (attr := simp)]
theorem graphCol_comp_graphIdem : graphCol A ≫ graphIdem A = graphCol A := by
  rw [← graphRow_comp_graphCol, graphCol_comp_graphRow_assoc]

/-- `v = E j` with `j` the inclusion of the identity sheet. -/
theorem ι_one_comp_graphIdem : biproduct.ι _ 1 ≫ graphIdem A = graphCol A := by
  rw [← graphRow_comp_graphCol, ι_graphRow_assoc, act_one, id_comp]

/-- `u = q π_1 E` with `π_1` the projection to the identity sheet. -/
theorem order_smul_graphIdem_comp_π_one :
    order G • (graphIdem A ≫ biproduct.π _ 1) = graphRow A := by
  rw [← graphRow_comp_graphCol, assoc, graphCol_π, inv_one, act_one, Linear.comp_smul, comp_id,
    smul_smul, mul_inv_cancel₀ order_ne_zero, one_smul]

/-- The tautological splitting `X → 𝒞 → X` of `E` by the graph column and row. -/
@[simps]
def graphRetract : Retract X (graph G X) where
  i := graphCol A
  r := graphRow A

omit [Fintype G] [Linear ℚ 𝒦] in
/-- The left action is strict and the graph row intertwines it with `A`. -/
@[reassoc]
theorem leftTranslation_comp_graphRow (g : G) :
    leftTranslation g ≫ graphRow A = graphRow A ≫ A g := by
  ext b
  simp only [leftTranslation, biproduct.ι_desc_assoc, ι_graphRow, ι_graphRow_assoc, act_comp]

@[reassoc]
theorem graphCol_comp_leftTranslation (g : G) :
    graphCol A ≫ leftTranslation g = A g ≫ graphCol A := by
  classical
  ext a
  simp only [graphCol, leftTranslation, Linear.smul_comp, assoc, Linear.comp_smul,
    biproduct.lift_desc_assoc, sum_comp, biproduct.lift_π, ι_π_graph]
  rw [Finset.sum_eq_single (g⁻¹ * a), ite_eq_left (by simp), comp_id, act_comp]
  · simp
  · intro b _ hb
    rw [ite_eq_right, comp_zero]
    rintro rfl
    exact hb (by simp)
  · simp

/-- `E` commutes with the strict left action, so it is an equivariant idempotent. -/
theorem leftTranslation_comp_graphIdem (g : G) :
    leftTranslation g ≫ graphIdem A = graphIdem A ≫ leftTranslation g := by
  rw [← graphRow_comp_graphCol, leftTranslation_comp_graphRow_assoc, assoc,
    graphCol_comp_leftTranslation]

section Isometry

variable {𝔻 : 𝒦ᵒᵖ ⥤ 𝒦} {φ : 𝔻.obj (op X) ⟶ X} (hφ : IsIsometryAction 𝔻 A φ)
include hφ

/-- `uΦ = q φ v^*`. -/
theorem graphForm_comp_graphRow [𝔻.Additive] :
    graphForm 𝔻 φ ≫ graphRow A = order G • (dualMap 𝔻 (graphCol A) ≫ φ) := by
  apply dual_graph_hom_ext 𝔻
  intro b
  rw [dualMap_π_graphForm_assoc, ι_graphRow, Linear.comp_smul, ← dualMap_comp_assoc, graphCol_π,
    dualMap_smul, Linear.smul_comp, smul_smul, mul_inv_cancel₀ order_ne_zero, one_smul, hφ]

/-- `Φ u^* = q v φ`. -/
theorem dualMap_graphRow_comp_graphForm :
    dualMap 𝔻 (graphRow A) ≫ graphForm 𝔻 φ = order G • (φ ≫ graphCol A) := by
  ext a
  rw [assoc, graphForm_π, ← dualMap_comp_assoc, ι_graphRow, Linear.smul_comp, assoc, graphCol_π,
    Linear.comp_smul, smul_smul, mul_inv_cancel₀ order_ne_zero, one_smul, hφ, inv_inv]

/-- Manuscript (5.3): `EΦ = ΦE^*`. -/
theorem graphForm_comp_graphIdem [𝔻.Additive] :
    graphForm 𝔻 φ ≫ graphIdem A = dualMap 𝔻 (graphIdem A) ≫ graphForm 𝔻 φ := by
  rw [← graphRow_comp_graphCol, dualMap_comp, assoc, dualMap_graphRow_comp_graphForm A hφ,
    ← assoc, graphForm_comp_graphRow A hφ, Linear.smul_comp, Linear.comp_smul, assoc]

/-- Manuscript (5.7): `uΦu^* = Σ_b A_b φ A_b^* = q φ`. -/
theorem graphRow_isometry :
    dualMap 𝔻 (graphRow A) ≫ graphForm 𝔻 φ ≫ graphRow A = order G • φ := by
  rw [← assoc, dualMap_graphRow_comp_graphForm A hφ, Linear.smul_comp, assoc,
    graphCol_comp_graphRow, comp_id]

end Isometry

end Graph

/-- Two splittings of the same idempotent have isomorphic objects, via `r₂ ι₁`. -/
@[reassoc]
theorem retract_comp_retract {C D D' : 𝒦} (R : Retract D C) (R' : Retract D' C)
    (h : R.r ≫ R.i = R'.r ≫ R'.i) : (R.i ≫ R'.r) ≫ (R'.i ≫ R.r) = 𝟙 D := by
  rw [assoc, ← assoc R'.r, ← h, assoc, R.retract_assoc, R.retract]

section Corner

variable [Preadditive 𝒦] [Linear ℚ 𝒦] (𝔻 : 𝒦ᵒᵖ ⥤ 𝒦) (q : ℚ) {C D : 𝒦}
  (Φ : 𝔻.obj (op C) ⟶ C) (R : Retract D C)

/-- Manuscript (5.5): the normalized corner form `φ_D = q⁻¹ rΦr^*`. -/
def cornerForm : 𝔻.obj (op D) ⟶ D := q⁻¹ • (dualMap 𝔻 R.r ≫ Φ ≫ R.r)

/-- Manuscript (5.5): the inverse duality `b_D = q ι^*Φ⁻¹ι`. -/
def cornerInv [IsIso Φ] : D ⟶ 𝔻.obj (op D) := q • (R.i ≫ inv Φ ≫ dualMap 𝔻 R.i)

variable {𝔻 q Φ R}

section Poincare

variable [IsIso Φ] (hq : q ≠ 0) (hΦ : Φ ≫ (R.r ≫ R.i) = dualMap 𝔻 (R.r ≫ R.i) ≫ Φ)
include hq hΦ

/-- Lemma 5.1: `φ_D b_D = 1`. -/
@[reassoc]
theorem cornerInv_comp_cornerForm : cornerInv 𝔻 q Φ R ≫ cornerForm 𝔻 q Φ R = 𝟙 D := by
  have h : dualMap 𝔻 R.i ≫ dualMap 𝔻 R.r ≫ Φ ≫ R.r = Φ ≫ R.r := by
    rw [← dualMap_comp_assoc, ← reassoc_of% hΦ, R.retract, comp_id]
  simp only [cornerInv, cornerForm, Linear.smul_comp, Linear.comp_smul, smul_smul,
    inv_mul_cancel₀ hq, one_smul, assoc, h, IsIso.inv_hom_id_assoc, R.retract]

/-- Lemma 5.1: `b_D φ_D = 1`. -/
@[reassoc]
theorem cornerForm_comp_cornerInv : cornerForm 𝔻 q Φ R ≫ cornerInv 𝔻 q Φ R = 𝟙 _ := by
  have h : Φ ≫ R.r ≫ R.i ≫ inv Φ = dualMap 𝔻 (R.r ≫ R.i) := by
    rw [reassoc_of% hΦ, IsIso.hom_inv_id, comp_id]
  simp only [cornerInv, cornerForm, Linear.smul_comp, Linear.comp_smul, smul_smul,
    mul_inv_cancel₀ hq, one_smul, assoc, reassoc_of% h, ← dualMap_comp, R.retract_assoc,
    R.retract, dualMap_id]

/-- Lemma 5.1: the normalized corner is Poincaré. -/
theorem isIso_cornerForm : IsIso (cornerForm 𝔻 q Φ R) :=
  ⟨cornerInv 𝔻 q Φ R, cornerForm_comp_cornerInv hq hΦ, cornerInv_comp_cornerForm hq hΦ⟩

end Poincare

/-- Lemma 5.1, independence of the splitting: `r₂ι₁` is an isometry of normalized corners. -/
theorem cornerForm_isometry {D' : 𝒦} (R' : Retract D' C) (h : R.r ≫ R.i = R'.r ≫ R'.i)
    (hΦ : Φ ≫ (R'.r ≫ R'.i) = dualMap 𝔻 (R'.r ≫ R'.i) ≫ Φ) :
    dualMap 𝔻 (R.i ≫ R'.r) ≫ cornerForm 𝔻 q Φ R ≫ (R.i ≫ R'.r) = cornerForm 𝔻 q Φ R' := by
  have hr : R.r ≫ R.i ≫ R'.r = R'.r := by
    rw [← assoc, h, assoc, R'.retract, comp_id]
  have hd : dualMap 𝔻 R'.r ≫ dualMap 𝔻 R.i ≫ dualMap 𝔻 R.r ≫ Φ =
      dualMap 𝔻 R'.r ≫ Φ ≫ R.r ≫ R.i := by
    rw [← dualMap_comp_assoc 𝔻 R.r R.i, h, ← hΦ]
  simp only [cornerForm, Linear.smul_comp, Linear.comp_smul, assoc, dualMap_comp]
  rw [reassoc_of% hd, hr, hr]

variable [𝔻.Additive] (ε : 𝔻.rightOp ⋙ 𝔻 ⟶ 𝟭 𝒦)

/-- Conjugation by `r` commutes with transposition, so `φ_D` is symmetric when `Φ` is. -/
theorem transpose_cornerForm :
    transpose 𝔻 ε (cornerForm 𝔻 q Φ R) = cornerForm 𝔻 q (transpose 𝔻 ε Φ) R := by
  rw [cornerForm, transpose_smul, transpose_conj, cornerForm]

/-- Manuscript Lemma 5.1 (algebraic content). In an idempotent-complete `ℚ`-linear category with
duality (in the application `K^b(Kar 𝒬)`, idempotent complete by [BS01, Thm 2.8]), an idempotent
`E` with `EΦ = ΦE^*` on a Poincaré object `(C, Φ)` splits as `D → C → D`; the normalized corner
`(D, q⁻¹ rΦr^*)` is Poincaré with inverse `q ι^*Φ⁻¹ι`, and symmetric when `Φ` is. -/
theorem lemma_5_1 [IsIdempotentComplete 𝒦] {E : C ⟶ C} (hE : E ≫ E = E)
    (Φ : 𝔻.obj (op C) ⟶ C) [IsIso Φ] (hΦ : Φ ≫ E = dualMap 𝔻 E ≫ Φ) (hq : q ≠ 0) :
    ∃ (D : 𝒦) (R : Retract D C), R.r ≫ R.i = E ∧
      cornerInv 𝔻 q Φ R ≫ cornerForm 𝔻 q Φ R = 𝟙 D ∧
      cornerForm 𝔻 q Φ R ≫ cornerInv 𝔻 q Φ R = 𝟙 _ ∧
      (transpose 𝔻 ε Φ = Φ → transpose 𝔻 ε (cornerForm 𝔻 q Φ R) = cornerForm 𝔻 q Φ R) := by
  obtain ⟨D, i, r, hir, hri⟩ := IsIdempotentComplete.idempotents_split C E hE
  let R : Retract D C := ⟨i, r, hir⟩
  have hΦ' : Φ ≫ (R.r ≫ R.i) = dualMap 𝔻 (R.r ≫ R.i) ≫ Φ := hri ▸ hΦ
  exact ⟨D, R, hri, cornerInv_comp_cornerForm hq hΦ', cornerForm_comp_cornerInv hq hΦ',
    fun hsym ↦ by rw [transpose_cornerForm, hsym]⟩

end Corner

section Normalization

variable [Preadditive 𝒦] [Linear ℚ 𝒦] {G : Type} [Group G] [Fintype G] {X : 𝒦}
  [HasBiproduct fun _ : G ↦ X] (A : G →* End X) {D : 𝒦} (R : Retract D (graph G X))

/-- Manuscript Lemma 5.2: `w = uι : D ⟶ X`. -/
def cornerToSheet : D ⟶ X := R.i ≫ graphRow A

/-- Manuscript Lemma 5.2: `z = rv : X ⟶ D`. -/
def sheetToCorner : X ⟶ D := graphCol A ≫ R.r

variable {A R} (hR : R.r ≫ R.i = graphIdem A)
include hR

/-- `wz = uEv = 1`. -/
@[reassoc]
theorem sheetToCorner_comp_cornerToSheet : sheetToCorner A R ≫ cornerToSheet A R = 𝟙 X := by
  rw [sheetToCorner, cornerToSheet, assoc, reassoc_of% hR, graphCol_comp_graphIdem_assoc,
    graphCol_comp_graphRow]

/-- `zw = rEι = 1`. -/
@[reassoc]
theorem cornerToSheet_comp_sheetToCorner : cornerToSheet A R ≫ sheetToCorner A R = 𝟙 D := by
  rw [sheetToCorner, cornerToSheet, assoc, graphRow_comp_graphCol_assoc, ← hR, assoc,
    R.retract_assoc, R.retract]

/-- Any splitting of the graph idempotent is isomorphic to the sheet `X`. -/
@[simps]
def cornerIso : D ≅ X where
  hom := cornerToSheet A R
  inv := sheetToCorner A R
  hom_inv_id := cornerToSheet_comp_sheetToCorner hR
  inv_hom_id := sheetToCorner_comp_cornerToSheet hR

/-- Crux review C1: `w` intertwines the strict action `r L_g ι` on the corner with `A_g`. -/
theorem cornerToSheet_equivariant (g : G) :
    (R.i ≫ leftTranslation g ≫ R.r) ≫ cornerToSheet A R = cornerToSheet A R ≫ A g := by
  rw [cornerToSheet, assoc, assoc, reassoc_of% hR, graphIdem_comp_graphRow,
    leftTranslation_comp_graphRow, assoc]

/-- Manuscript Lemma 5.2 and (5.8): for any splitting `D` of the graph idempotent, the
normalized corner `(D, q⁻¹ rΦr^*)` with `q = |G|` is isometric to `(X, φ)` via `w = uι`:
`w φ_D w^* = q⁻¹ uEΦE^*u^* = q⁻¹ uΦu^* = φ`. -/
theorem lemma_5_2 {𝔻 : 𝒦ᵒᵖ ⥤ 𝒦} {φ : 𝔻.obj (op X) ⟶ X}
    (hφ : IsIsometryAction 𝔻 A φ) :
    dualMap 𝔻 (cornerToSheet A R) ≫ cornerForm 𝔻 (order G) (graphForm 𝔻 φ) R ≫
      cornerToSheet A R = φ := by
  have hu : R.r ≫ R.i ≫ graphRow A = graphRow A := by
    rw [reassoc_of% hR, graphIdem_comp_graphRow]
  have hu' : dualMap 𝔻 (graphRow A) ≫ dualMap 𝔻 R.i ≫ dualMap 𝔻 R.r =
      dualMap 𝔻 (graphRow A) := by
    rw [← dualMap_comp, ← dualMap_comp, assoc, hu]
  simp only [cornerToSheet, cornerForm, dualMap_comp, Linear.smul_comp, Linear.comp_smul, assoc,
    hu, reassoc_of% hu', graphRow_isometry A hφ, smul_smul, inv_mul_cancel₀ order_ne_zero,
    one_smul]

omit hR in
/-- The tautological splitting realizes the normalized corner exactly: `q⁻¹ uΦu^* = φ`. -/
theorem cornerForm_graphRetract {𝔻 : 𝒦ᵒᵖ ⥤ 𝒦} {φ : 𝔻.obj (op X) ⟶ X}
    (hφ : IsIsometryAction 𝔻 A φ) :
    cornerForm 𝔻 (order G) (graphForm 𝔻 φ) (graphRetract A) = φ := by
  rw [cornerForm, graphRetract_r, graphRow_isometry A hφ, smul_smul,
    inv_mul_cancel₀ order_ne_zero, one_smul]

end Normalization

end

end HSFormal.GraphCorner
