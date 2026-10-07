import HSFormal.Assembly
import HSFormal.Cubical.SeqDual
import HSFormal.Cubical.CylinderInvariance
import HSFormal.InducedClassUniform
import HSFormal.Bridges
import HSFormal.Cubical.ChainModel

/-!
# Proposition 9.2 (realization) from the chain-model data of §8

Manuscript Prop. 9.2 (l.746–825) applied to the chain models of §8, and the step
`ClassConstruction manifoldGerm` (hence `ClassConstruction'`).

* `bx`: a single sheet-shifted degree block `u_{r → r'} ⊗ R_{g⁻¹}` of a sequence of honest graph
  type `g` (`IsSeq`), as a morphism of `ℬ_{G,Z}(X)` between the complexes of controlled sequences;
  composition, sums, transpose (`star_bx`), the differentials of the complexes and of their shifted
  duals (`extComplex_d`, `dualComplex_extComplex_d`), and **exterior vanishing** `bx_eq_zero`:
  a block whose entries have endpoints approaching `Z` (`ExtTendsto`) is `0` in `ℬ_{G,Z}`.
* **Lemma 9.1, endpoint form** (`dist_ge_of_word`, `extTendsto_word`): a word `π v P u σ` through
  the far projection, with `f`-small factors, has both endpoints at distance `≥ R` from `y`, hence
  in the exterior `Z = T × Z₀`. The band factorization of Lemma 9.1 is not needed: `I_Z` is
  characterized by endpoint estimates (`inIdeal_map_iff`).
* `ExtInverse.toSymPoincare`: a controlled based complex with a strictly symmetric duality and an
  inverse with homotopies **modulo `Z`** is an honest Poincaré complex of `ℬ_{G,Z}(X)`.
* `ChainModelInput`: exactly the conclusions of Lemmas 8.1–8.2 consumed here (field layout shared
  with `FixedData.ChainModelData`, converted by `FixedData.chainModelInput`).
* Prop. 9.2: `compressed` (the compressed `C = D/F`, `φ̂ = πφπ^*`, Poincaré in `ℬ_{1,Z}(T × Sⁿ)`
  through `extInverse`: the defects of (9.7) and l.787–801 are words), `sheetData` (`A_g = πa_gσ`
  with `A_1 = 1`, `B̂_{g,h}`, `V̂_g`; the residuals (9.5), (9.6) and l.804–815 are words:
  `comm_res`, `mul_res`, `adj_res`), and `isometry`/`push_cls_compressed`: `π` is a homotopy
  isometry `proj D ≃ push C` in `ℬ_{1,Z₀}(Sⁿ)` (`πσ = 1`, `σπ = 1 - P` with `P` supported in
  `Z₀`, `πφπ^* = φ̂` exactly).
* `classConstruction_manifoldGerm : ClassConstruction manifoldGerm` and
  `classConstruction'_manifoldGerm`, from `FixedData.chainModelData` (`D_i` is the germ complex of
  `f̂`, `cls_chainModelInput_uncompressed`).
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace HSFormal.Prop92

open Filter Matrix CategoryTheory CategoryTheory.Limits Metric HSFormal.LTheory
  HSFormal.Compression HSFormal.AsymptoticObject HSFormal.Cubical HSFormal.Cubical.BasedComplex
open scoped ENNReal Topology Pointwise

/-! ### Single shifted sequences of degree blocks in `ℬ_{G,Z}(X)` -/

section Bx

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  (π : ∀ i, G i →* H) {X : Type} [MulAction H X] [PseudoEMetricSpace X]
  {A B B' : ControlledSeq X}

/-- A sequence of matrices of honest graph type `g` (manuscript §8, l.544–548). -/
def IsSeq (A B : ControlledSeq X) (g : ∀ i, G i) (u : ∀ i, Matrix (B.C i).X (A.C i).X ℚ) :
    Prop :=
  Tendsto (fun i ↦ graphProp (π i (g i)) (u i) (A.label i) (B.label i)) atTop (𝓝 0)

variable {π}

namespace IsSeq

variable {g g' : ∀ i, G i} {u u' : ∀ i, Matrix (B.C i).X (A.C i).X ℚ}

theorem block (hu : IsSeq π A B g u) (r r' : ℤ) :
    IsGraphType (M := A.obj π r) (N := B.obj π r') g (fun i ↦ Cubical.BasedComplex.blockMat (u i) r r') :=
  tendsto_zero_of_le hu fun _ ↦ graphProp_submatrix_le _ _ _

theorem add (hu : IsSeq π A B g u) (hu' : IsSeq π A B g u') :
    IsSeq π A B g (fun i ↦ u i + u' i) :=
  tendsto_zero_of_le (by simpa using hu.max hu') fun _ ↦ graphProp_add_le _

theorem neg (hu : IsSeq π A B g u) : IsSeq π A B g (fun i ↦ -u i) := by
  simpa [IsSeq] using hu

theorem sub (hu : IsSeq π A B g u) (hu' : IsSeq π A B g u') :
    IsSeq π A B g (fun i ↦ u i - u' i) := by
  simpa [sub_eq_add_neg] using hu.add hu'.neg

theorem smul (c : ℚ) (hu : IsSeq π A B g u) : IsSeq π A B g (fun i ↦ c • u i) :=
  tendsto_zero_of_le hu fun _ ↦ graphProp_smul_le _ c

theorem congr (hu : IsSeq π A B g u) (hg : ∀ i, g i = g' i) (hu' : ∀ i, u i = u' i) :
    IsSeq π A B g' u' := by
  rwa [← funext hg, ← funext hu']

variable [IsIsometricSMul H X]

theorem mul {v : ∀ i, Matrix (B'.C i).X (B.C i).X ℚ} (hu : IsSeq π A B g u)
    (hv : IsSeq π B B' g' v) : IsSeq π A B' (fun i ↦ g' i * g i) (fun i ↦ v i * u i) :=
  tendsto_zero_of_le (by simpa using Filter.Tendsto.add hu hv) fun i ↦ by
    rw [map_mul]; exact graphProp_mul_le _ _ _ _ _ _ _

theorem transpose (hu : IsSeq π A B g u) :
    IsSeq π B A (fun i ↦ (g i)⁻¹) (fun i ↦ (u i)ᵀ) := by
  simpa [IsSeq] using hu

end IsSeq

theorem isSeq_one {u : ∀ i, Matrix (B.C i).X (A.C i).X ℚ} (hu : PropTendsto u A.label B.label) :
    IsSeq π A B 1 u := by
  simpa [IsSeq, PropTendsto] using hu

theorem IsSeq.toProp {u : ∀ i, Matrix (B.C i).X (A.C i).X ℚ} (hu : IsSeq π A B 1 u) :
    PropTendsto u A.label B.label := by
  simpa [IsSeq, PropTendsto] using hu

/-- A sequence `j i ∈ J i` of a uniform graph family. -/
theorem isSeq_of_graphTendsto {J : ℕ → Type*} {τ : ∀ i, J i → G i}
    {u : ∀ i, J i → Matrix (B.C i).X (A.C i).X ℚ}
    (hu : GraphTendsto (fun _ _ ↦ True) (fun i j ↦ π i (τ i j)) u A.label B.label) (j : ∀ i, J i) :
    IsSeq π A B (fun i ↦ τ i (j i)) (fun i ↦ u i (j i)) :=
  tendsto_zero_of_le hu fun i ↦ (graphPropOn_true _).symm.le.trans
    (graphPropOn_le_graphErr (buf := fun _ _ ↦ True) (θ := fun i j ↦ π i (τ i j)) (u := u)
      (a := A.label) (b := B.label) i (j i))

variable [IsIsometricSMul H X] (Z : Set X)

variable (π) in
/-- The shifted degree block `u_{r → r'} ⊗ R_{g⁻¹}` of a sequence of honest graph type `g`, as a
morphism of `ℬ_{G,Z}(X)` between the complexes of `A` and `B`. -/
def bx (g : ∀ i, G i) (u : ∀ i, Matrix (B.C i).X (A.C i).X ℚ) (hu : IsSeq π A B g u)
    (r r' : ℤ) : (A.extComplex π Z).X r ⟶ (B.extComplex π Z).X r' :=
  (extFunctor π Z).map (sheetHom g _ (hu.block r r'))

variable {Z}
variable {g g' k : ∀ i, G i} {u u' : ∀ i, Matrix (B.C i).X (A.C i).X ℚ}

theorem bx_congr (hu : IsSeq π A B g u) (hu' : IsSeq π A B g' u') (hg : ∀ i, g i = g' i)
    (huu : ∀ i, u i = u' i) (r r' : ℤ) : bx π Z g u hu r r' = bx π Z g' u' hu' r r' := by
  obtain rfl := funext hg
  obtain rfl := funext huu
  rfl

theorem bx_comp {v : ∀ i, Matrix (B'.C i).X (B.C i).X ℚ} (hu : IsSeq π A B g u)
    (hv : IsSeq π B B' g' v) (hk : ∀ i, g' i * g i = k i) (hvu : IsSeq π A B' k fun i ↦ v i * u i)
    {r r' r'' : ℤ} (h : ∀ i κ σ, u i κ σ ≠ 0 → ((A.C i).deg σ : ℤ) = r → ((B.C i).deg κ : ℤ) = r') :
    bx π Z g u hu r r' ≫ bx π Z g' v hv r' r'' = bx π Z k (fun i ↦ v i * u i) hvu r r'' := by
  obtain rfl := funext hk
  rw [bx, bx, bx, ← Functor.map_comp, sheetHom_comp]
  congr 1
  exact AsymptoticObject.hom_ext fun i ↦ by
    simp only [sheetHom_val]
    rw [Cubical.BasedComplex.blockMat_mul _ _ (h i)]

theorem bx_comp' {v : ∀ i, Matrix (B'.C i).X (B.C i).X ℚ} (hu : IsSeq π A B g u)
    (hv : IsSeq π B B' g' v) {r r' r'' : ℤ}
    (h : ∀ i κ σ, u i κ σ ≠ 0 → ((A.C i).deg σ : ℤ) = r → ((B.C i).deg κ : ℤ) = r') :
    bx π Z g u hu r r' ≫ bx π Z g' v hv r' r'' =
      bx π Z (fun i ↦ g' i * g i) (fun i ↦ v i * u i) (hu.mul hv) r r'' :=
  bx_comp hu hv (fun _ ↦ rfl) _ h

theorem bx_comp1 {v : ∀ i, Matrix (B'.C i).X (B.C i).X ℚ} (hu : IsSeq π A B 1 u)
    (hv : IsSeq π B B' 1 v) {r r' r'' : ℤ}
    (h : ∀ i κ σ, u i κ σ ≠ 0 → ((A.C i).deg σ : ℤ) = r → ((B.C i).deg κ : ℤ) = r') :
    bx π Z 1 u hu r r' ≫ bx π Z 1 v hv r' r'' =
      bx π Z 1 (fun i ↦ v i * u i) ((hu.mul hv).congr (fun _ ↦ one_mul _) fun _ ↦ rfl) r r'' :=
  bx_comp hu hv (fun _ ↦ one_mul _) _ h

theorem bx_comp_left {v : ∀ i, Matrix (B'.C i).X (B.C i).X ℚ} (hu : IsSeq π A B 1 u)
    (hv : IsSeq π B B' g' v) {r r' r'' : ℤ}
    (h : ∀ i κ σ, u i κ σ ≠ 0 → ((A.C i).deg σ : ℤ) = r → ((B.C i).deg κ : ℤ) = r') :
    bx π Z 1 u hu r r' ≫ bx π Z g' v hv r' r'' =
      bx π Z g' (fun i ↦ v i * u i) ((hu.mul hv).congr (fun _ ↦ mul_one _) fun _ ↦ rfl) r r'' :=
  bx_comp hu hv (fun _ ↦ mul_one _) _ h

theorem bx_comp_right {v : ∀ i, Matrix (B'.C i).X (B.C i).X ℚ} (hu : IsSeq π A B g u)
    (hv : IsSeq π B B' 1 v) {r r' r'' : ℤ}
    (h : ∀ i κ σ, u i κ σ ≠ 0 → ((A.C i).deg σ : ℤ) = r → ((B.C i).deg κ : ℤ) = r') :
    bx π Z g u hu r r' ≫ bx π Z 1 v hv r' r'' =
      bx π Z g (fun i ↦ v i * u i) ((hu.mul hv).congr (fun _ ↦ one_mul _) fun _ ↦ rfl) r r'' :=
  bx_comp hu hv (fun _ ↦ one_mul _) _ h

theorem bx_add (hu : IsSeq π A B g u) (hu' : IsSeq π A B g u') (r r' : ℤ) :
    bx π Z g u hu r r' + bx π Z g u' hu' r r' = bx π Z g _ (hu.add hu') r r' := by
  rw [bx, bx, bx, ← Functor.map_add, sheetHom_add]
  rfl

theorem bx_sub (hu : IsSeq π A B g u) (hu' : IsSeq π A B g u') (r r' : ℤ) :
    bx π Z g u hu r r' - bx π Z g u' hu' r r' = bx π Z g _ (hu.sub hu') r r' := by
  rw [bx, bx, bx, ← Functor.map_sub, sheetHom_sub]
  rfl

theorem bx_neg (hu : IsSeq π A B g u) (r r' : ℤ) :
    -bx π Z g u hu r r' = bx π Z g _ hu.neg r r' := by
  rw [bx, bx, ← Functor.map_neg]
  congr 1
  exact AsymptoticObject.hom_ext fun i ↦ by
    rw [AsymptoticObject.neg_val, sheetHom_val, sheetHom_val, ← sheet_neg]
    rfl

theorem bx_smul (c : ℚ) (hu : IsSeq π A B g u) (r r' : ℤ) :
    c • bx π Z g u hu r r' = bx π Z g _ (hu.smul c) r r' := by
  rw [bx, bx, ← Functor.map_smul, sheetHom_smul]
  rfl

theorem bx_eq_zero_of_deg (hu : IsSeq π A B g u) {r r' : ℤ}
    (h : ∀ i κ σ, ((A.C i).deg σ : ℤ) = r → ((B.C i).deg κ : ℤ) = r' → u i κ σ = 0) :
    bx π Z g u hu r r' = 0 := by
  rw [bx, ← (extFunctor π Z).map_zero]
  congr 1
  exact AsymptoticObject.hom_ext fun i ↦ by
    rw [sheetHom_val, Cubical.BasedComplex.blockMat_eq_zero (h i), sheet_zero, AsymptoticObject.zero_val]

theorem bx_one (r : ℤ) :
    bx π Z 1 (fun i ↦ (1 : Matrix (A.C i).X (A.C i).X ℚ)) (isSeq_one PropTendsto.one) r r =
      𝟙 _ := by
  rw [bx]
  refine Eq.trans ?_ ((extFunctor π Z).map_id _)
  congr 1
  exact AsymptoticObject.hom_ext fun i ↦ by
    rw [sheetHom_val, Cubical.BasedComplex.blockMat_one, Pi.one_apply, sheet_one_one]
    rfl

theorem bx_congr_block (hu : IsSeq π A B g u) (hu' : IsSeq π A B g' u') (hg : ∀ i, g i = g' i)
    {r r' : ℤ}
    (h : ∀ i κ σ, ((A.C i).deg σ : ℤ) = r → ((B.C i).deg κ : ℤ) = r' → u i κ σ = u' i κ σ) :
    bx π Z g u hu r r' = bx π Z g' u' hu' r r' := by
  obtain rfl := funext hg
  rw [bx, bx]
  congr 1
  exact AsymptoticObject.hom_ext fun i ↦ by
    rw [sheetHom_val, sheetHom_val]
    congr 1
    ext k' k
    exact h i _ _ ((cellEquiv (A.C i) r).symm k).2 ((cellEquiv (B.C i) r').symm k').2

theorem bx_units_smul (n : ℤˣ) (hu : IsSeq π A B g u) (r r' : ℤ) :
    n • bx π Z g u hu r r' = bx π Z g _ (hu.smul ((n : ℤ) : ℚ)) r r' := by
  rw [← bx_smul, Units.smul_def, Int.cast_smul_eq_zsmul]

theorem star_bx (hu : IsSeq π A B g u) (r r' : ℤ) :
    (exteriorInvCat π Z).inv.star (bx π Z g u hu r r') =
      bx π Z (fun i ↦ (g i)⁻¹) (fun i ↦ (u i)ᵀ) hu.transpose r' r := by
  change (extFunctor π Z).map (AsymptoticObject.transpose _) = _
  rw [transpose_sheetHom]
  rfl

variable (Z) in
theorem extComplex_d (A : ControlledSeq X) (r r' : ℤ) :
    (A.extComplex π Z).d r r' = bx π Z 1 (fun i ↦ (A.C i).d) (isSeq_one A.tendsto_d) r r' :=
  rfl

variable (π Z) in
theorem extComplex_id (A : ControlledSeq X) (r : ℤ) :
    𝟙 ((A.extComplex π Z).X r) =
      bx π Z 1 (fun i ↦ (1 : Matrix (A.C i).X (A.C i).X ℚ)) (isSeq_one PropTendsto.one) r r :=
  (bx_one r).symm

/-- The shifted dual differential `δ_r = (-1)^r d^*_{N-r+1}` of `ℬ_{G,Z}(X)` is the block of the
based dual differential `(-1)^N dᵀ sgn`. -/
theorem dualComplex_extComplex_d {N : ℕ} (hN : A.DimLE N) (r r' : ℤ) :
    (dualComplex (exteriorInvCat π Z).inv N (A.extComplex π Z)).d r r' =
      bx π Z 1 (fun i ↦ ((A.C i).dual N (hN i)).d)
        (isSeq_one (A := A) (B := A) (A.dual N hN).tendsto_d) (N - r) (N - r') := by
  erw [dualComplex_d, extComplex_d, star_bx, bx_units_smul]
  refine bx_congr_block _ _ (fun i ↦ by simp) fun i κ σ hσ hκ ↦ ?_
  have hle := hN i σ
  rw [dual_d_apply, Matrix.smul_apply, transpose_apply,
    MatRealization.negOnePow_cast_eq (k := (A.C i).deg σ) (by omega), smul_eq_mul, mul_assoc]

end Bx

/-! ### Exterior witnesses: endpoint estimates -/

section MatEd

variable {X α β : Type*} [PseudoEMetricSpace X] {Z : Set X} {u v : Matrix β α ℚ}
  {source : α → X} {target : β → X}

theorem matEd_add_le :
    matEd Z (u + v) source target ≤ max (matEd Z u source target) (matEd Z v source target) :=
  matEd_le_iff.mpr fun b a h ↦ by
    by_cases hu : u b a = 0
    · have hv : v b a ≠ 0 := by simpa [hu] using h
      exact (infEDist_le_matEd hv).imp (le_max_of_le_right ·) (le_max_of_le_right ·)
    · exact (infEDist_le_matEd hu).imp (le_max_of_le_left ·) (le_max_of_le_left ·)

theorem matEd_submatrix_le {α' β' : Type*} (f : α' → α) (g : β' → β) :
    matEd Z (u.submatrix g f) (source ∘ f) (target ∘ g) ≤ matEd Z u source target :=
  matEd_le_iff.mpr fun _ _ h ↦ infEDist_le_matEd (u := u) (source := source) (target := target) h

variable {α β : ℕ → Type*} {u v : ∀ i, Matrix (β i) (α i) ℚ} {source : ∀ i, α i → X}
  {target : ∀ i, β i → X}

/-- Uniformly vanishing endpoint distances to `Z`: the family has exterior witnesses. -/
def ExtTendsto (Z : Set X) (u : ∀ i, Matrix (β i) (α i) ℚ) (source : ∀ i, α i → X)
    (target : ∀ i, β i → X) : Prop :=
  Tendsto (fun i ↦ matEd Z (u i) (source i) (target i)) atTop (𝓝 0)

namespace ExtTendsto

theorem add (hu : ExtTendsto Z u source target) (hv : ExtTendsto Z v source target) :
    ExtTendsto Z (fun i ↦ u i + v i) source target :=
  tendsto_zero_of_le (by simpa using hu.max hv) fun _ ↦ matEd_add_le

theorem neg (hu : ExtTendsto Z u source target) : ExtTendsto Z (fun i ↦ -u i) source target := by
  simpa [ExtTendsto, matEd_neg] using hu

theorem sub (hu : ExtTendsto Z u source target) (hv : ExtTendsto Z v source target) :
    ExtTendsto Z (fun i ↦ u i - v i) source target := by
  simpa [sub_eq_add_neg] using hu.add hv.neg

theorem zero : ExtTendsto Z (fun i ↦ (0 : Matrix (β i) (α i) ℚ)) source target :=
  tendsto_zero_of_forall_eq_zero fun _ ↦ le_antisymm (matEd_le_iff.mpr fun _ _ h ↦ (h rfl).elim)
    bot_le

theorem congr (hu : ExtTendsto Z u source target) (h : ∀ i, u i = v i) :
    ExtTendsto Z v source target := by
  rwa [← funext h]

end ExtTendsto

end MatEd

section BxExt

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  {π : ∀ i, G i →* H} {X : Type} [MulAction H X] [PseudoEMetricSpace X] [IsIsometricSMul H X]
  {Z : Set X} {A B : ControlledSeq X} {g g' : ∀ i, G i} {u u' : ∀ i, Matrix (B.C i).X (A.C i).X ℚ}

/-- **Exterior witnesses** (Lemma 9.1, §2): a shifted block whose entries have endpoints
approaching the invariant exterior `Z` vanishes in `ℬ_{G,Z}(X)`. -/
theorem bx_eq_zero (hZ : ∀ h : H, h • Z = Z) (hu : IsSeq π A B g u)
    (h : ExtTendsto Z u A.label B.label) (r r' : ℤ) : bx π Z g u hu r r' = 0 := by
  rw [bx, extFunctor_map_eq_zero_iff]
  exact inIdeal_sheetHom hZ _ h fun i _ _ hcb ↦
    infEDist_le_matEd (u := u i) (source := A.label i) (target := B.label i) hcb

theorem bx_eq_bx (hZ : ∀ h : H, h • Z = Z) (hu : IsSeq π A B g u) (hu' : IsSeq π A B g u')
    (h : ExtTendsto Z (fun i ↦ u i - u' i) A.label B.label) (r r' : ℤ) :
    bx π Z g u hu r r' = bx π Z g u' hu' r r' := by
  rw [← sub_eq_zero, bx_sub]
  exact bx_eq_zero hZ _ h r r'

end BxExt

/-! ### Words through the far projection (Lemma 9.1) -/

section Words

/-- Compression of products (9.4): `(v u)^ = v̂ û + π v P u σ` on the retained cells. -/
theorem restrict_mul {α : Type*} [Fintype α] [DecidableEq α] (far : α → Prop)
    [DecidablePred far] (u v : Matrix α α ℚ) :
    (v * u).submatrix (Subtype.val : {a // ¬far a} → α) (Subtype.val : {a // ¬far a} → α) =
      v.submatrix (Subtype.val : {a // ¬far a} → α) (Subtype.val : {a // ¬far a} → α) *
          u.submatrix (Subtype.val : {a // ¬far a} → α) (Subtype.val : {a // ¬far a} → α) +
        (v * (farProj far * u)).submatrix (Subtype.val : {a // ¬far a} → α)
          (Subtype.val : {a // ¬far a} → α) := by
  have h := one_sub_nearIncl_mul_nearProj (α := α) far
  simp only [← nearProj_mul_mul_nearIncl (P := fun a ↦ ¬far a) (Q := fun a ↦ ¬far a), ← h]
  simp only [Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul]
  abel

theorem restrict_one {α : Type*} [Fintype α] [DecidableEq α] (P : α → Prop) :
    (1 : Matrix α α ℚ).submatrix (Subtype.val : {a // P a} → α) (Subtype.val : {a // P a} → α) =
      1 :=
  submatrix_one _ Subtype.val_injective

variable {T Y : Type*} [PseudoEMetricSpace T] [PseudoMetricSpace Y] {y : Y} {R t : ℝ}

/-- The exterior `T × {z : d(y, z) ≥ R}` of (7.8). -/
abbrev extSet (T : Type*) (y : Y) (R : ℝ) : Set (T × Y) := Set.univ ×ˢ {z | R ≤ dist y z}

/-- **Lemma 9.1, endpoint form.** If the far cells lie beyond `t` and both factors of a word
`v P u` move the `f`-coordinate by less than `t - R`, both endpoints of every nonzero entry of the
word lie at distance `≥ R` from `y`, i.e. in the exterior. -/
theorem dist_ge_of_word {α β γ : Type*} [Fintype β] {u : Matrix β α ℚ} {v : Matrix γ β ℚ}
    {far : β → Prop} {fa : α → Y} {fb : β → Y} {fc : γ → Y}
    (hfar : ∀ b, far b → t < dist y (fb b))
    (hu : prop u fa fb < ENNReal.ofReal (t - R)) (hv : prop v fb fc < ENNReal.ofReal (t - R))
    {c : γ} {a : α} (h : (v * (farProj far * u)) c a ≠ 0) :
    R ≤ dist y (fa a) ∧ R ≤ dist y (fc c) := by
  classical
  obtain ⟨b, hvb, hb⟩ := exists_mul_apply_ne_zero h
  have hfb : far b ∧ u b a ≠ 0 := by
    by_contra hn
    refine hb ?_
    rw [farProj, diagonal_mul]
    by_cases hf : far b
    · have : u b a = 0 := by by_contra h'; exact hn ⟨hf, h'⟩
      simp [this]
    · simp [hf]
  have h₁ := hfar b hfb.1
  have h₂ : dist (fb b) (fa a) < t - R :=
    edist_lt_ofReal.mp ((edist_le_prop hfb.2).trans_lt hu)
  have h₃ : dist (fc c) (fb b) < t - R := edist_lt_ofReal.mp ((edist_le_prop hvb).trans_lt hv)
  constructor
  · have := dist_triangle y (fa a) (fb b)
    rw [dist_comm (fa a)] at this
    linarith
  · have := dist_triangle y (fc c) (fb b)
    linarith

/-- **Lemma 9.1 for sequences**: words `v P u` through the far cells, restricted to the retained
cells and labelled in `T × Y` with `Y`-coordinate the `f`-label, have exterior witnesses as soon
as `u`, `v` have `f`-propagation tending to zero. -/
theorem extTendsto_word {α : ℕ → Type*} [∀ i, Fintype (α i)] {u v : ∀ i, Matrix (α i) (α i) ℚ}
    {far : ∀ i, α i → Prop} {f : ∀ i, α i → Y} {ρ : ∀ i, α i → T} (hRt : R < t)
    (hfar : ∀ i b, far i b → t < dist y (f i b))
    (hu : Tendsto (fun i ↦ prop (u i) (f i) (f i)) atTop (𝓝 0))
    (hv : Tendsto (fun i ↦ prop (v i) (f i) (f i)) atTop (𝓝 0)) :
    ExtTendsto (extSet T y R)
      (fun i ↦ (v i * (farProj (far i) * u i)).submatrix (Subtype.val : {a // ¬far i a} → α i)
        (Subtype.val : {a // ¬far i a} → α i))
      (fun i (σ : {a // ¬far i a}) ↦ (ρ i σ.1, f i σ.1))
      (fun i (σ : {a // ¬far i a}) ↦ (ρ i σ.1, f i σ.1)) := by
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (t - R) := ENNReal.ofReal_pos.mpr (by linarith)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [(tendsto_order.1 hu).2 _ hpos, (tendsto_order.1 hv).2 _ hpos] with i hui hvi
  refine (le_antisymm (matEd_le_iff.mpr fun c a h ↦ ?_) bot_le).symm
  obtain ⟨ha, hc⟩ := dist_ge_of_word (hfar i) hui hvi h
  exact ⟨(infEDist_zero_of_mem (show (ρ i c.1, f i c.1) ∈ extSet T y R from ⟨trivial, hc⟩)).le,
    (infEDist_zero_of_mem (show (ρ i a.1, f i a.1) ∈ extSet T y R from ⟨trivial, ha⟩)).le⟩

/-- One-sided words `P u`: the far end lies in `Z₀`, the other within the propagation of `u`. -/
theorem matEd_farProj_mul_le {α β : Type*} [Fintype α] {far : α → Prop} {u : Matrix α β ℚ}
    {fa : α → Y} {fb : β → Y} {Z₀ : Set Y} (hfar : ∀ a, far a → fa a ∈ Z₀) :
    matEd Z₀ (farProj far * u) fb fa ≤ prop u fb fa := by
  classical
  refine matEd_le_iff.mpr fun κ b h ↦ ?_
  have hκ : far κ ∧ u κ b ≠ 0 := by
    rw [farProj, diagonal_mul] at h
    by_cases hf : far κ
    · exact ⟨hf, by simpa [hf] using h⟩
    · simp [hf] at h
  have h0 : infEDist (fa κ) Z₀ = 0 := infEDist_zero_of_mem (hfar κ hκ.1)
  refine ⟨by rw [h0]; exact zero_le, ?_⟩
  calc infEDist (fb b) Z₀ ≤ infEDist (fa κ) Z₀ + edist (fb b) (fa κ) :=
        infEDist_le_infEDist_add_edist
    _ = edist (fa κ) (fb b) := by rw [h0, zero_add, edist_comm]
    _ ≤ prop u fb fa := edist_le_prop hκ.2

end Words

/-! ### Poincaré duality modulo the exterior -/

section ExtPoincare

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  (π : ∀ i, G i →* H) {X : Type} [MulAction H X] [PseudoEMetricSpace X] [IsIsometricSMul H X]
  (Z : Set X)

/-- The quotient `𝒜_G(X)` (prequotient) `→ ℬ_{G,Z}(X)` as a duality-preserving functor. -/
abbrev extInv : InvFunctor (asymptoticObjInvolution π X) (exteriorInvCat π Z).inv :=
  (asymptoticQuotInv π X).comp ((supportKaroubiFiltration π Z).proj : InvFunctor _ _)

variable {π Z} {A : ControlledSeq X} {N : ℕ}

/-- The matrices of a controlled map `A^{N-*} → A`, on the cells of `A`. -/
abbrev dmat (hN : A.DimLE N) (φ : ControlledSeq.Hom (A.dual N hN) A) (i : ℕ) :
    Matrix (A.C i).X (A.C i).X ℚ :=
  (φ.f i).f

theorem extInv_mapDual_dualityMap_f (hN : A.DimLE N) (φ : ControlledSeq.Hom (A.dual N hN) A)
    (r : ℤ) :
    ((extInv π Z).mapDual (ControlledSeq.dualityMap π hN φ)).f r =
      bx π Z (A := A) (B := A) 1 (dmat hN φ) (isSeq_one φ.tendsto) (N - r) r := by
  rw [InvFunctor.mapDual_f, ControlledSeq.dualityMap_f]
  rfl

theorem extInv_mapC_d (r r' : ℤ) :
    ((extInv π Z).mapC (A.toComplex π)).d r r' =
      bx π Z 1 (fun i ↦ (A.C i).d) (isSeq_one A.tendsto_d) r r' :=
  rfl

theorem extInv_mapC_id (r : ℤ) :
    𝟙 (((extInv π Z).mapC (A.toComplex π)).X r) =
      bx π Z 1 (fun i ↦ (1 : Matrix (A.C i).X (A.C i).X ℚ)) (isSeq_one PropTendsto.one) r r :=
  (bx_one r).symm

theorem dualComplex_extInv_mapC_d (hN : A.DimLE N) (r r' : ℤ) :
    (dualComplex (exteriorInvCat π Z).inv N ((extInv π Z).mapC (A.toComplex π))).d r r' =
      bx π Z 1 (fun i ↦ ((A.C i).dual N (hN i)).d)
        (isSeq_one (A := A) (B := A) (A.dual N hN).tendsto_d) (N - r) (N - r') :=
  dualComplex_extComplex_d hN r r'

theorem dualComplex_extInv_mapC_id (r : ℤ) :
    𝟙 ((dualComplex (exteriorInvCat π Z).inv N ((extInv π Z).mapC (A.toComplex π))).X r) =
      bx π Z 1 (fun i ↦ (1 : Matrix (A.C i).X (A.C i).X ℚ)) (isSeq_one PropTendsto.one)
        (N - r) (N - r) :=
  (bx_one _).symm

theorem deg_dmat (hN : A.DimLE N) (φ : ControlledSeq.Hom (A.dual N hN) A) {i : ℕ}
    {κ σ : (A.C i).X} (h : dmat hN φ i κ σ ≠ 0) :
    ((A.C i).deg κ : ℤ) = N - (A.C i).deg σ := by
  have h₁ := (φ.f i).deg0 κ σ h
  have := hN i σ
  change ((A.C i).deg κ : ℤ) = ((N - (A.C i).deg σ : ℕ) : ℤ) + 0 at h₁
  omega

theorem deg_dual_d (hN : A.DimLE N) {i : ℕ} {κ σ : (A.C i).X}
    (h : ((A.C i).dual N (hN i)).d κ σ ≠ 0) : ((A.C i).deg κ : ℤ) = (A.C i).deg σ + 1 := by
  have h₁ := ((A.C i).dual N (hN i)).d_deg κ σ h
  have := hN i σ
  have := hN i κ
  change N - (A.C i).deg σ = N - (A.C i).deg κ + 1 at h₁
  omega

/-- The data of a chain duality inverse modulo the exterior `Z`: a based inverse `b` of the
strictly symmetric duality `φ` and homotopies `bφ ≃ 1`, `φb ≃ 1` whose defects (the chain defect
of `b` and the two homotopy residuals) have exterior witnesses; e.g. the compressed `b̂ = σ^*bσ`
and `π H σ`, `σ^* H' π^*` of Proposition 9.2, with defects the words of (9.7). -/
structure ExtInverse (A : ControlledSeq X) (N : ℕ) (hN : A.DimLE N) (Z : Set X)
    (φ : ControlledSeq.Hom (A.dual N hN) A) where
  b : ∀ i, Matrix (A.C i).X (A.C i).X ℚ
  b_deg : ∀ i, HasDeg (A.C i) ((A.C i).dual N (hN i)) 0 (b i)
  b_tendsto : PropTendsto b A.label A.label
  b_comm : ExtTendsto Z (fun i ↦ ((A.C i).dual N (hN i)).d * b i - b i * (A.C i).d)
    A.label A.label
  h₁ : ∀ i, Matrix (A.C i).X (A.C i).X ℚ
  h₁_deg : ∀ i, HasDeg ((A.C i).dual N (hN i)) ((A.C i).dual N (hN i)) 1 (h₁ i)
  h₁_tendsto : PropTendsto h₁ A.label A.label
  h₁_res : ExtTendsto Z (fun i ↦ b i * dmat hN φ i - 1 -
    (((A.C i).dual N (hN i)).d * h₁ i + h₁ i * ((A.C i).dual N (hN i)).d)) A.label A.label
  h₂ : ∀ i, Matrix (A.C i).X (A.C i).X ℚ
  h₂_deg : ∀ i, HasDeg (A.C i) (A.C i) 1 (h₂ i)
  h₂_tendsto : PropTendsto h₂ A.label A.label
  h₂_res : ExtTendsto Z (fun i ↦ dmat hN φ i * b i - 1 - ((A.C i).d * h₂ i + h₂ i * (A.C i).d))
    A.label A.label

namespace ExtInverse

variable {hN : A.DimLE N} {φ : ControlledSeq.Hom (A.dual N hN) A} (E : ExtInverse A N hN Z φ)

include E in
theorem deg_h₁ {i : ℕ} {κ σ : (A.C i).X} (h : E.h₁ i κ σ ≠ 0) :
    ((A.C i).deg κ : ℤ) + 1 = (A.C i).deg σ := by
  have h₁ := E.h₁_deg i κ σ h
  have := hN i κ
  have := hN i σ
  change ((N - (A.C i).deg κ : ℕ) : ℤ) = ((N - (A.C i).deg σ : ℕ) : ℤ) + 1 at h₁
  omega

include E in
theorem deg_b {i : ℕ} {κ σ : (A.C i).X} (h : E.b i κ σ ≠ 0) :
    ((A.C i).deg κ : ℤ) = N - (A.C i).deg σ := by
  have h₁ := E.b_deg i κ σ h
  have := hN i κ
  change ((N - (A.C i).deg κ : ℕ) : ℤ) = (A.C i).deg σ + 0 at h₁
  omega

variable (hZ : ∀ h : H, h • Z = Z)

include hZ in
/-- The inverse `ψ = b̂` of the duality, a chain map of `ℬ_{G,Z}(X)`. -/
def ψ : A.extComplex π Z ⟶ dualComplex (exteriorInvCat π Z).inv N (A.extComplex π Z) where
  f r := bx π Z 1 E.b (isSeq_one E.b_tendsto) r (N - r)
  comm' r r' (h : r' + 1 = r) := by
    erw [dualComplex_extComplex_d hN, extComplex_d, bx_comp1, bx_comp1]
    · exact bx_eq_bx hZ _ _ E.b_comm _ _
    · intro i κ σ hne hσ; have := (A.C i).d_deg κ σ hne; omega
    · intro i κ σ hne hσ; rw [E.deg_b hne, hσ]

theorem ψ_f (r : ℤ) : (E.ψ hZ).f r = bx π Z 1 E.b (isSeq_one E.b_tendsto) r (N - r) := rfl

include hZ in
/-- `φ̂b̂ ≃ 1` in `ℬ_{G,Z}(X)`, with the homotopy `π H σ`. -/
def homotopy₂ :
    Homotopy (E.ψ hZ ≫ (extInv π Z).mapDual (ControlledSeq.dualityMap π hN φ)) (𝟙 _) where
  hom r r' := bx π Z 1 E.h₂ (isSeq_one E.h₂_tendsto) r r'
  zero r r' hrr' := bx_eq_zero_of_deg _ fun i κ σ hσ hκ ↦ by
    by_contra hne
    have := E.h₂_deg i κ σ hne
    exact hrr' (by change r + 1 = r'; omega)
  comm r := by
    erw [dNext_eq _ (show (ComplexShape.down ℤ).Rel r (r - 1) by simp),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (r + 1) r by simp), HomologicalComplex.comp_f,
      HomologicalComplex.id_f, ψ_f, extInv_mapDual_dualityMap_f]
    simp only [extComplex_d, extInv_mapC_d, extComplex_id]
    erw [bx_comp1, bx_comp1, bx_comp1, bx_add, bx_add]
    · refine bx_eq_bx hZ _ _ (E.h₂_res.congr fun i ↦ ?_) _ _
      abel
    · intro i κ σ hne hσ; have := E.h₂_deg i κ σ hne; omega
    · intro i κ σ hne hσ; have := (A.C i).d_deg κ σ hne; omega
    · intro i κ σ hne hσ; rw [E.deg_b hne, hσ]

include hZ in
/-- `b̂φ̂ ≃ 1` in `ℬ_{G,Z}(X)`, with the homotopy `σ^* H' π^*`. -/
def homotopy₁ :
    Homotopy ((extInv π Z).mapDual (ControlledSeq.dualityMap π hN φ) ≫ E.ψ hZ) (𝟙 _) where
  hom r r' := bx π Z 1 E.h₁ (isSeq_one E.h₁_tendsto) (N - r) (N - r')
  zero r r' hrr' := bx_eq_zero_of_deg _ fun i κ σ hσ hκ ↦ by
    by_contra hne
    have h₁ := E.h₁_deg i κ σ hne
    have := hN i κ
    have := hN i σ
    change ((N - (A.C i).deg κ : ℕ) : ℤ) = ((N - (A.C i).deg σ : ℕ) : ℤ) + 1 at h₁
    exact hrr' (by change r + 1 = r'; omega)
  comm r := by
    erw [dNext_eq _ (show (ComplexShape.down ℤ).Rel r (r - 1) by simp),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (r + 1) r by simp), HomologicalComplex.comp_f,
      HomologicalComplex.id_f, ψ_f, extInv_mapDual_dualityMap_f]
    simp (config := { dsimp := false, proj := false }) only [dualComplex_extComplex_d hN,
      dualComplex_extInv_mapC_d hN, dualComplex_extInv_mapC_id]
    (try erw [dualComplex_extComplex_d hN])
    erw [bx_comp1, bx_comp1, bx_comp1, bx_add, bx_add]
    · refine bx_eq_bx hZ _ _ (E.h₁_res.congr fun i ↦ ?_) _ _
      abel
    · intro i κ σ hne hσ; have := E.deg_h₁ hne; omega
    · intro i κ σ hne hσ; have := deg_dual_d hN hne; omega
    · intro i κ σ hne hσ; rw [deg_dmat hN φ hne, hσ]; ring

include E in
/-- **Poincaré duality modulo the exterior**: a controlled based complex with a strictly
symmetric duality `φ` and an inverse modulo `Z` is a Poincaré complex of `ℬ_{G,Z}(X)`. -/
def toSymPoincare (π : ∀ i, G i →* H) (hZ : ∀ h : H, h • Z = Z) (hφ : ControlledSeq.IsSymm hN φ) :
    SymPoincare (exteriorInvCat π Z).inv N where
  C := (extInv π Z).mapC (A.toComplex π)
  p := 𝟙 _
  p_idem := Category.id_comp _
  support r hr := by
    rw [HomologicalComplex.id_f, extInv_mapC_id]
    exact bx_eq_zero_of_deg _ fun i κ σ hσ _ ↦ by exfalso; have := hN i σ; omega
  φ := (extInv π Z).mapDual (ControlledSeq.dualityMap π hN φ)
  φ_kar := by simp
  symm := by
    rw [IsStrictSymm, InvFunctor.transposeHom_mapDual]
    exact congrArg _ (ControlledSeq.isStrictSymm_dualityMap hφ)
  poincare := ⟨E.ψ hZ, by
      rw [dualHom_id, Category.id_comp]; exact Category.comp_id _,
      ⟨E.homotopy₂ hZ⟩,
    ⟨(E.homotopy₁ hZ).trans (Homotopy.ofEq (dualHom_id (exteriorInvCat π Z).inv N _).symm)⟩⟩

theorem toSymPoincare_C (hφ : ControlledSeq.IsSymm hN φ) :
    (E.toSymPoincare π hZ hφ).C = A.extComplex π Z := rfl

theorem toSymPoincare_p (hφ : ControlledSeq.IsSymm hN φ) :
    (E.toSymPoincare π hZ hφ).p = 𝟙 (E.toSymPoincare π hZ hφ).C :=
  rfl

theorem toSymPoincare_φ_f (hφ : ControlledSeq.IsSymm hN φ) (r : ℤ) :
    (E.toSymPoincare π hZ hφ).φ.f r =
      bx π Z (A := A) (B := A) 1 (dmat hN φ) (isSeq_one φ.tendsto) (N - r) r :=
  extInv_mapDual_dualityMap_f hN φ r

end ExtInverse

end ExtPoincare

/-! ### Free sheets `Ind : ℬ_{1,Z} → ℬ_{G,Z}` on shifted blocks -/

section Ind

variable {p : ℕ} (cd : ControlData p) {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  (π : ∀ i, G i →* cd.Cp) {A B : ControlledSeq cd.X}

theorem ind_map_bx {u : ∀ i, Matrix (B.C i).X (A.C i).X ℚ} (hu : IsSeq (scalarHom cd.Cp) A B 1 u)
    (r r' : ℤ) :
    (cd.ind π).F.map (bx (scalarHom cd.Cp) cd.Z 1 u hu r r') =
      bx π cd.Z 1 u (isSeq_one hu.toProp) r r' := by
  change (extFunctor π cd.Z).map ((AsymptoticObject.freeSheet π).map
    (ControlledSeq.hom (scalarHom cd.Cp) u hu.toProp r r')) = _
  rw [ControlledSeq.freeSheet_map_hom]
  rfl

end Ind

theorem smul_Z₀ {p : ℕ} (cd : ControlData p) (h : cd.Cp) : h • cd.Z₀ = cd.Z₀ := by
  ext z; simp [Set.mem_smul_set]

/-! ### The chain-model input of §8 -/

/-- The pair `(ρ̃, f)` of control labels in `T × Sⁿ` (§9, l.721). -/
def pairLabel {α : ℕ → Type*} {T Y : Type*} (ρ : ∀ i, α i → T) (f : ∀ i, α i → Y) (i : ℕ)
    (σ : α i) : T × Y :=
  (ρ i σ, f i σ)

/-- Uniform `f`-propagation of a family of matrix sequences. -/
def UnifPropTendsto {X : Type*} [PseudoEMetricSpace X] {α : ℕ → Type*} {J : ℕ → Type*}
    (u : ∀ i, J i → Matrix (α i) (α i) ℚ) (f : ∀ i, α i → X) : Prop :=
  Tendsto (fun i ↦ ⨆ j, prop (u i j) (f i) (f i)) atTop (𝓝 0)

theorem UnifPropTendsto.apply {X : Type*} [PseudoEMetricSpace X] {α : ℕ → Type*}
    {J : ℕ → Type*} {u : ∀ i, J i → Matrix (α i) (α i) ℚ} {f : ∀ i, α i → X}
    (hu : UnifPropTendsto u f) (j : ∀ i, J i) :
    Tendsto (fun i ↦ prop (u i (j i)) (f i) (f i)) atTop (𝓝 0) :=
  tendsto_zero_of_le hu fun i ↦ le_iSup (fun j ↦ prop (u i j) (f i) (f i)) (j i)

/-- **The conclusions of Lemmas 8.1–8.2 consumed by Proposition 9.2** (§8, l.540–706), for control
data `cd` and tail groups `π_i : G_i → C_p`:

* the closed chain models `D_i` of `W = Sⁿ × ℂP²` (cubically `Tⁿ_{m_i} ⊗ CPcell`), a controlled
  sequence over `Sⁿ` with the `f`-labels of the cells, of dimension `≤ N = n + 4`;
* Lemma 8.1: the strictly symmetric duality `φ_i`, its local inverse `b_i` and the inverse
  homotopies (`duality`, all `f`-controlled);
* the auxiliary `T`-coordinate `ρ̃` of the cells, honest only on the buffered region `buf`
  (l.544–548): there `d, φ, b, H, H'` are `(ρ̃, f)`-controlled, and `a_g`, `B_{g,h}`, `V_g` have
  graph type `g`, `gh`, `g` uniformly (`GraphTendsto` on `buf`);
* the far subcomplexes `F_i` (l.710), with far cells beyond the cut radius `t > R` and retained
  cells eventually inside the buffer (l.721);
* the chain maps `a_g` (`a_1 = 1`), the homotopies `B_{g,h}` of (8.5) and the adjoint homotopies
  `V_g` of (8.6)–(8.7) (`a_g φ - φ a_{g⁻¹}^* = dV + Vδ`, l.697–705), all with uniformly vanishing
  `f`-propagation.

Neither (8.4) `a_g z = z` nor the slant homotopies `U_g` are consumed: only their output `V_g`. -/
structure ChainModelInput {p : ℕ} (cd : ControlData p) {G : ℕ → Type} [∀ i, Group (G i)]
    [∀ i, Fintype (G i)] (π : ∀ i, G i →* cd.Cp) where
  /-- The chain models `D_i`, labelled by `f`. -/
  D : ControlledSeq (RoundSphere cd.n)
  dimLE : D.DimLE (cd.n + 4)
  /-- Lemma 8.1: `φ`, `b`, `H : bφ ≃ 1`, `H' : φb ≃ 1`. -/
  duality : D.SymDuality (cd.n + 4) dimLE
  /-- The `T`-coordinate `ρ̃` of the cells. -/
  ρ : ∀ i, (D.C i).X → sphere (0 : EuclideanSpace ℂ (Fin cd.m)) 1
  /-- The buffered region. -/
  buf : ∀ i, (D.C i).X → Prop
  /-- The far subcomplexes `F_i`. -/
  far : ∀ i, (D.C i).X → Prop
  [decFar : ∀ i, DecidablePred (far i)]
  isSub_far : ∀ i, (D.C i).IsSub (far i)
  /-- The radius `t` of (7.8). -/
  t : ℝ
  R_lt_t : cd.R < t
  far_dist : ∀ i σ, far i σ → t < dist cd.y (D.label i σ)
  near_buf : ∀ᶠ i in atTop, ∀ σ, ¬far i σ → buf i σ
  d_buf : PropTendstoOn buf (fun i ↦ (D.C i).d) (pairLabel ρ D.label) (pairLabel ρ D.label)
  φ_buf : PropTendstoOn buf (fun i ↦ (duality.hom.f i).f) (pairLabel ρ D.label)
    (pairLabel ρ D.label)
  b_buf : PropTendstoOn buf (fun i ↦ (duality.inv.f i).f) (pairLabel ρ D.label)
    (pairLabel ρ D.label)
  homInv_buf : PropTendstoOn buf (fun i ↦ (duality.homInv.h i).h) (pairLabel ρ D.label)
    (pairLabel ρ D.label)
  invHom_buf : PropTendstoOn buf (fun i ↦ (duality.invHom.h i).h) (pairLabel ρ D.label)
    (pairLabel ρ D.label)
  /-- The chain approximations `a_g` of `ĥ_g × 1`, (8.1)–(8.4). -/
  a : ∀ i, G i → BasedComplex.Hom (D.C i) (D.C i)
  a_one : ∀ i, a i 1 = BasedComplex.Hom.id (D.C i)
  a_f : UnifPropTendsto (fun i g ↦ (a i g).f) D.label
  a_buf : GraphTendsto buf (fun i g ↦ (π i g : cd.Cp)) (fun i g ↦ (a i g).f) (pairLabel ρ D.label)
    (pairLabel ρ D.label)
  /-- Lemma 8.2, (8.5): `a_g a_h - a_{gh} = dB_{g,h} + B_{g,h}d`. -/
  B : ∀ i (gh : G i × G i), BasedComplex.Htpy ((a i gh.1).comp (a i gh.2)) (a i (gh.1 * gh.2))
  B_f : UnifPropTendsto (fun i gh ↦ (B i gh).h) D.label
  B_buf : GraphTendsto buf (fun i gh ↦ (π i (gh.1 * gh.2) : cd.Cp)) (fun i gh ↦ (B i gh).h)
    (pairLabel ρ D.label) (pairLabel ρ D.label)
  /-- (8.6)–(8.7): `a_g φ - φ a_{g⁻¹}^* = dV_g + V_gδ`. -/
  V : ∀ i (g : G i), BasedComplex.Htpy ((a i g).comp (duality.hom.f i))
    ((duality.hom.f i).comp ((a i g⁻¹).dual (cd.n + 4) (dimLE i) (dimLE i)))
  V_f : UnifPropTendsto (fun i g ↦ (V i g).h) D.label
  V_buf : GraphTendsto buf (fun i g ↦ (π i g : cd.Cp)) (fun i g ↦ (V i g).h)
    (pairLabel ρ D.label) (pairLabel ρ D.label)

theorem restrict_dual_d {C : BasedComplex} {Q : C.X → Prop} [DecidablePred Q]
    {hQ : C.IsLocallyClosed Q} {N : ℕ} (hN : (C.restrict Q hQ).DimLE N) (hN' : C.DimLE N) :
    ((C.restrict Q hQ).dual N hN).d =
      (C.dual N hN').d.submatrix (Subtype.val : {σ // Q σ} → C.X) Subtype.val := by
  ext σ τ
  rw [dual_d_apply, submatrix_apply, dual_d_apply]
  rfl

namespace ChainModelInput

variable {p : ℕ} {cd : ControlData p} {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  {π : ∀ i, G i →* cd.Cp} (I : ChainModelInput cd π)

attribute [instance] decFar

/-- The dimension `N = n + 4` of `W`, as a natural number. -/
abbrev Nn (_ : ChainModelInput cd π) : ℕ := cd.n + 4

/-- The `(ρ̃, f)`-labels of the cells. -/
abbrev lab : ∀ i, (I.D.C i).X → cd.X := pairLabel I.ρ I.D.label

theorem near_buf' : ∀ᶠ i in atTop, ∀ σ : {σ // ¬I.far i σ}, I.buf i σ.1 :=
  I.near_buf.mono fun _ h σ ↦ h σ.1 σ.2

/-- **The compressed complexes** `C_i = D_i/F_i` of (9.1), with the retained `(ρ̃, f)`-labels. -/
def Cq : ControlledSeq cd.X :=
  ControlledSeq.quotOfBuffer I.D.C I.lab I.buf I.far I.isSub_far I.d_buf I.near_buf

/-- The same compressed complexes `D/F` with the `f`-labels, over `Sⁿ`. -/
abbrev Dq : ControlledSeq (RoundSphere cd.n) := I.D.quot I.far I.isSub_far

theorem dimLE_Cq : I.Cq.DimLE I.Nn := fun i σ ↦ I.dimLE i σ.1

/-- Restriction `u ↦ π u σ` of a matrix to the retained cells (9.3). -/
abbrev hat (i : ℕ) (u : Matrix (I.D.C i).X (I.D.C i).X ℚ) : Matrix (I.Cq.C i).X (I.Cq.C i).X ℚ :=
  u.submatrix Subtype.val Subtype.val

/-- The residual word `π v P u σ` of Lemma 9.1. -/
abbrev W (i : ℕ) (u v : Matrix (I.D.C i).X (I.D.C i).X ℚ) : Matrix (I.Cq.C i).X (I.Cq.C i).X ℚ :=
  (v * (farProj (I.far i) * u)).submatrix Subtype.val Subtype.val

theorem hat_mul (i : ℕ) (u v : Matrix (I.D.C i).X (I.D.C i).X ℚ) :
    I.hat i v * I.hat i u = I.hat i (v * u) - I.W i u v := by
  rw [eq_sub_iff_add_eq]
  exact (restrict_mul (I.far i) u v).symm

theorem hat_add (i : ℕ) (u v : Matrix (I.D.C i).X (I.D.C i).X ℚ) :
    I.hat i (u + v) = I.hat i u + I.hat i v := rfl

theorem hat_sub (i : ℕ) (u v : Matrix (I.D.C i).X (I.D.C i).X ℚ) :
    I.hat i (u - v) = I.hat i u - I.hat i v := rfl

theorem hat_one (i : ℕ) : I.hat i 1 = 1 := restrict_one _

theorem hat_transpose (i : ℕ) (u : Matrix (I.D.C i).X (I.D.C i).X ℚ) :
    I.hat i uᵀ = (I.hat i u)ᵀ := rfl

theorem Cq_d (i : ℕ) : (I.Cq.C i).d = I.hat i (I.D.C i).d := rfl

theorem Cq_dual_d (i : ℕ) :
    ((I.Cq.C i).dual I.Nn (I.dimLE_Cq i)).d = I.hat i ((I.D.C i).dual I.Nn (I.dimLE i)).d :=
  restrict_dual_d (hQ := (I.isSub_far i).isLocallyClosed_compl) _ _

theorem Cq_label : I.Cq.label = fun i σ ↦ I.lab i σ.1 := rfl

theorem Z_eq : cd.Z = extSet _ cd.y cd.R := rfl

/-- **Lemma 9.1**: residual words have exterior witnesses. -/
theorem extTendsto_W {u v : ∀ i, Matrix (I.D.C i).X (I.D.C i).X ℚ}
    (hu : Tendsto (fun i ↦ prop (u i) (I.D.label i) (I.D.label i)) atTop (𝓝 0))
    (hv : Tendsto (fun i ↦ prop (v i) (I.D.label i) (I.D.label i)) atTop (𝓝 0)) :
    ExtTendsto cd.Z (fun i ↦ I.W i (u i) (v i)) I.Cq.label I.Cq.label :=
  extTendsto_word (ρ := I.ρ) I.R_lt_t I.far_dist hu hv

/-! #### The primitive matrices of `D_i` and their identities -/

/-- `d`. -/
abbrev mD (i : ℕ) : Matrix (I.D.C i).X (I.D.C i).X ℚ := (I.D.C i).d
/-- The dual differential `δ = (-1)^N dᵀ sgn`. -/
abbrev mδ (i : ℕ) : Matrix (I.D.C i).X (I.D.C i).X ℚ := ((I.D.C i).dual I.Nn (I.dimLE i)).d
/-- `φ`. -/
abbrev mφ (i : ℕ) : Matrix (I.D.C i).X (I.D.C i).X ℚ := (I.duality.hom.f i).f
/-- `b`. -/
abbrev mb (i : ℕ) : Matrix (I.D.C i).X (I.D.C i).X ℚ := (I.duality.inv.f i).f
/-- `H : bφ ≃ 1`. -/
abbrev mH (i : ℕ) : Matrix (I.D.C i).X (I.D.C i).X ℚ := (I.duality.homInv.h i).h
/-- `H' : φb ≃ 1`. -/
abbrev mH' (i : ℕ) : Matrix (I.D.C i).X (I.D.C i).X ℚ := (I.duality.invHom.h i).h

theorem mδ_mb (i : ℕ) : I.mδ i * I.mb i = I.mb i * I.mD i := (I.duality.inv.f i).comm

theorem mb_mφ (i : ℕ) : I.mb i * I.mφ i - 1 = I.mδ i * I.mH i + I.mH i * I.mδ i :=
  (I.duality.homInv.h i).eq

theorem mφ_mb (i : ℕ) : I.mφ i * I.mb i - 1 = I.mD i * I.mH' i + I.mH' i * I.mD i :=
  (I.duality.invHom.h i).eq

theorem fprop_d : Tendsto (fun i ↦ prop (I.mD i) (I.D.label i) (I.D.label i)) atTop (𝓝 0) :=
  I.D.tendsto_d

theorem fprop_δ : Tendsto (fun i ↦ prop (I.mδ i) (I.D.label i) (I.D.label i)) atTop (𝓝 0) :=
  (I.D.dual I.Nn I.dimLE).tendsto_d

theorem fprop_φ : Tendsto (fun i ↦ prop (I.mφ i) (I.D.label i) (I.D.label i)) atTop (𝓝 0) :=
  I.duality.hom.tendsto

theorem fprop_b : Tendsto (fun i ↦ prop (I.mb i) (I.D.label i) (I.D.label i)) atTop (𝓝 0) :=
  I.duality.inv.tendsto

theorem fprop_H : Tendsto (fun i ↦ prop (I.mH i) (I.D.label i) (I.D.label i)) atTop (𝓝 0) :=
  I.duality.homInv.tendsto

theorem fprop_H' : Tendsto (fun i ↦ prop (I.mH' i) (I.D.label i) (I.D.label i)) atTop (𝓝 0) :=
  I.duality.invHom.tendsto

/-! #### The compressed duality and its inverse modulo the exterior -/

/-- `φ̂ = π φ π^*` (9.3), an exact chain map since `π` and `π^*` are (l.769). -/
@[implicit_reducible] def φhatB (i : ℕ) : BasedComplex.Hom ((I.Cq.C i).dual I.Nn (I.dimLE_Cq i)) (I.Cq.C i) where
  f := I.hat i (I.mφ i)
  deg0 κ σ h := (I.duality.hom.f i).deg0 κ.1 σ.1 h
  comm := by
    have := ((ControlledSeq.compressDuality (far := I.far) (far' := I.far) (hfar := I.isSub_far)
      (hfar' := I.isSub_far) I.dimLE I.duality.hom).f i).comm
    rwa [ControlledSeq.compressDuality_f] at this

/-- The compressed duality as a controlled chain map over `T × Sⁿ`. -/
@[implicit_reducible] def φhat : ControlledSeq.Hom (I.Cq.dual I.Nn I.dimLE_Cq) I.Cq :=
  ⟨I.φhatB, I.φ_buf.restrict _ _ I.near_buf'⟩

theorem dmat_φhat (i : ℕ) : dmat I.dimLE_Cq I.φhat i = I.hat i (I.mφ i) := rfl

theorem φhat_symm : ControlledSeq.IsSymm I.dimLE_Cq I.φhat := fun i ↦
  (isSymm_iff _).mpr fun σ τ ↦ (isSymm_iff _).mp (I.duality.symm i) σ.1 τ.1

theorem Cq_d' (i : ℕ) : (I.Cq.C i).d = I.hat i (I.mD i) := rfl

theorem Cq_dual_d' (i : ℕ) : ((I.Cq.C i).dual I.Nn (I.dimLE_Cq i)).d = I.hat i (I.mδ i) :=
  I.Cq_dual_d i

/-- **The inverse data of Proposition 9.2**: `b̂ = σ^* b σ`, `π H σ`, `σ^* H' π^*`, with the
defects of (9.7) and l.787–801, all words through the far projection. -/
def extInverse : ExtInverse I.Cq I.Nn I.dimLE_Cq cd.Z I.φhat where
  b i := I.hat i (I.mb i)
  b_deg i κ σ h := (I.duality.inv.f i).deg0 κ.1 σ.1 h
  b_tendsto := I.b_buf.restrict _ _ I.near_buf'
  b_comm := ((I.extTendsto_W I.fprop_d I.fprop_b).sub (I.extTendsto_W I.fprop_b I.fprop_δ)).congr
    fun i ↦ by
      rw [Cq_dual_d', Cq_d', hat_mul, hat_mul, mδ_mb]
      abel
  h₁ i := I.hat i (I.mH i)
  h₁_deg i κ σ h := (I.duality.homInv.h i).deg1 κ.1 σ.1 h
  h₁_tendsto := I.homInv_buf.restrict _ _ I.near_buf'
  h₁_res := (((I.extTendsto_W I.fprop_H I.fprop_δ).add
      (I.extTendsto_W I.fprop_δ I.fprop_H)).sub (I.extTendsto_W I.fprop_φ I.fprop_b)).congr
    fun i ↦ by
      have e := congrArg (I.hat i) (I.mb_mφ i)
      rw [hat_sub, hat_one, hat_add] at e
      rw [Cq_dual_d', dmat_φhat, hat_mul, hat_mul, hat_mul, eq_add_of_sub_eq e]
      abel
  h₂ i := I.hat i (I.mH' i)
  h₂_deg i κ σ h := (I.duality.invHom.h i).deg1 κ.1 σ.1 h
  h₂_tendsto := I.invHom_buf.restrict _ _ I.near_buf'
  h₂_res := (((I.extTendsto_W I.fprop_H' I.fprop_d).add
      (I.extTendsto_W I.fprop_d I.fprop_H')).sub (I.extTendsto_W I.fprop_b I.fprop_φ)).congr
    fun i ↦ by
      have e := congrArg (I.hat i) (I.mφ_mb i)
      rw [hat_sub, hat_one, hat_add] at e
      rw [Cq_d', dmat_φhat, hat_mul, hat_mul, hat_mul, eq_add_of_sub_eq e]
      abel

/-- **Proposition 9.2, Poincaré part** (l.769–801): the compressed complex `(C_i, d̂_i, φ̂_i)` with
the retained `(ρ̃, f)`-labels is a Poincaré complex of `ℬ_{1,Z}(T × Sⁿ)`, with `p = 1`. -/
def compressed : SymPoincare cd.B1.inv cd.N :=
  I.extInverse.toSymPoincare (scalarHom cd.Cp) cd.smul_Z I.φhat_symm

theorem compressed_C : I.compressed.C = I.Cq.extComplex (scalarHom cd.Cp) cd.Z := rfl

theorem compressed_p : I.compressed.p = 𝟙 I.compressed.C := rfl

/-! #### The compressed families `A_g = π a_g σ`, `B̂_{g,h} = π B_{g,h} σ`, `V̂_g = π V_g π^*` -/

/-- `a_g`. -/
abbrev ma (i : ℕ) (g : G i) : Matrix (I.D.C i).X (I.D.C i).X ℚ := (I.a i g).f
/-- `B_{g,h}`. -/
abbrev mB (i : ℕ) (gh : G i × G i) : Matrix (I.D.C i).X (I.D.C i).X ℚ := (I.B i gh).h
/-- `V_g`. -/
abbrev mV (i : ℕ) (g : G i) : Matrix (I.D.C i).X (I.D.C i).X ℚ := (I.V i g).h

theorem graph_a : GraphTendsto (fun _ _ ↦ True) (fun i g ↦ (π i g : cd.Cp))
    (fun i g ↦ I.hat i (I.ma i g)) I.Cq.label I.Cq.label :=
  I.a_buf.restrict _ _ I.near_buf'

theorem graph_B : GraphTendsto (fun _ _ ↦ True) (fun i gh ↦ (π i (gh.1 * gh.2) : cd.Cp))
    (fun i gh ↦ I.hat i (I.mB i gh)) I.Cq.label I.Cq.label :=
  I.B_buf.restrict _ _ I.near_buf'

theorem graph_V : GraphTendsto (fun _ _ ↦ True) (fun i g ↦ (π i g : cd.Cp))
    (fun i g ↦ I.hat i (I.mV i g)) I.Cq.label I.Cq.label :=
  I.V_buf.restrict _ _ I.near_buf'

theorem isSeq_a (g : ∀ i, G i) : IsSeq π I.Cq I.Cq g (fun i ↦ I.hat i (I.ma i (g i))) :=
  isSeq_of_graphTendsto (τ := fun _ ↦ id) I.graph_a g

theorem isSeq_B (g h : ∀ i, G i) :
    IsSeq π I.Cq I.Cq (fun i ↦ g i * h i) (fun i ↦ I.hat i (I.mB i (g i, h i))) := by
  have := isSeq_of_graphTendsto (J := fun i ↦ G i × G i) (τ := fun _ gh ↦ gh.1 * gh.2)
    (π := π) (A := I.Cq) (B := I.Cq) (u := fun i gh ↦ I.hat i (I.mB i gh)) I.graph_B
    fun i ↦ (g i, h i)
  exact this

theorem isSeq_V (g : ∀ i, G i) : IsSeq π I.Cq I.Cq g (fun i ↦ I.hat i (I.mV i (g i))) :=
  isSeq_of_graphTendsto (τ := fun _ ↦ id) I.graph_V g

theorem fprop_a (g : ∀ i, G i) :
    Tendsto (fun i ↦ prop (I.ma i (g i)) (I.D.label i) (I.D.label i)) atTop (𝓝 0) :=
  I.a_f.apply g

theorem fprop_aT (g : ∀ i, G i) :
    Tendsto (fun i ↦ prop (I.ma i (g i))ᵀ (I.D.label i) (I.D.label i)) atTop (𝓝 0) :=
  PropTendsto.transpose (I.a_f.apply g)

theorem fprop_B (g h : ∀ i, G i) :
    Tendsto (fun i ↦ prop (I.mB i (g i, h i)) (I.D.label i) (I.D.label i)) atTop (𝓝 0) :=
  I.B_f.apply fun i ↦ (g i, h i)

theorem fprop_V (g : ∀ i, G i) :
    Tendsto (fun i ↦ prop (I.mV i (g i)) (I.D.label i) (I.D.label i)) atTop (𝓝 0) :=
  I.V_f.apply g

/-- `A_g` in degree `r` on the orbit representatives. -/
def Ablk (r : ℤ) : GraphFamily G (I.Cq.obj π r) (I.Cq.obj π r) :=
  ControlledSeq.gblock π (A := I.Cq) (B := I.Cq) (fun i g ↦ I.hat i (I.ma i g)) r r

theorem hasGraphType_Ablk (r : ℤ) : HasGraphType (fun _ ↦ id) (I.Ablk r) :=
  ControlledSeq.hasGraphType_gblock π (τ := fun _ ↦ id) I.graph_a r r

theorem shift_Ablk (g : ∀ i, G i) (r : ℤ) :
    cd.shift π (A := I.compressed.C.X r) (A' := I.compressed.C.X r) g (fun i ↦ I.Ablk r i (g i))
        ((I.hasGraphType_Ablk r).apply g) =
      bx π cd.Z g (fun i ↦ I.hat i (I.ma i (g i))) (I.isSeq_a g) r r :=
  rfl

theorem CG_d (r r' : ℤ) :
    ((cd.ind π).mapC I.compressed.C).d r r' =
      bx π cd.Z 1 (fun i ↦ (I.Cq.C i).d) (isSeq_one I.Cq.tendsto_d) r r' :=
  ind_map_bx cd π (isSeq_one I.Cq.tendsto_d) r r'

theorem deg_hat_ma {i : ℕ} {g : G i} {κ σ : (I.Cq.C i).X} (h : I.hat i (I.ma i g) κ σ ≠ 0) :
    ((I.Cq.C i).deg κ : ℤ) = (I.Cq.C i).deg σ := by
  have : ((I.Cq.C i).deg κ : ℤ) = (I.Cq.C i).deg σ + 0 := (I.a i g).deg0 κ.1 σ.1 h
  omega

theorem deg_Cq_d {i : ℕ} {κ σ : (I.Cq.C i).X} (h : (I.Cq.C i).d κ σ ≠ 0) :
    ((I.Cq.C i).deg σ : ℤ) = (I.Cq.C i).deg κ + 1 := by
  have := (I.Cq.C i).d_deg κ σ h
  omega

/-- (9.5): `d̂ A_g - A_g d̂ = π a P d σ - π d P a σ`, words through the far projection. -/
theorem comm_res (g : ∀ i, G i) :
    ExtTendsto cd.Z (fun i ↦ (I.Cq.C i).d * I.hat i (I.ma i (g i)) -
      I.hat i (I.ma i (g i)) * (I.Cq.C i).d) I.Cq.label I.Cq.label :=
  ((I.extTendsto_W I.fprop_d (I.fprop_a g)).sub (I.extTendsto_W (I.fprop_a g) I.fprop_d)).congr
    fun i ↦ by
      rw [Cq_d', hat_mul, hat_mul,
        show I.mD i * I.ma i (g i) = I.ma i (g i) * I.mD i from (I.a i (g i)).comm]
      abel

/-- **The scalar complex with its sheet action** (`SheetAction`): `C = D/F` with `φ̂`, and the
compressed chain maps `A_g = π a_g σ` of (9.3), which commute with `d̂` in `ℬ_{G,Z}(T × Sⁿ)` after
the sheet shift by (9.5) and Lemma 9.1; `A_1 = πσ = 1`. -/
def sheetAction : cd.SheetAction π where
  C := I.compressed
  p_eq := rfl
  A := I.Ablk
  hA := I.hasGraphType_Ablk
  A_one r i := by
    change Cubical.BasedComplex.blockMat (I.hat i (I.a i 1).f) r r = 1
    rw [I.a_one, BasedComplex.Hom.id, hat_one]
    exact Cubical.BasedComplex.blockMat_one r
  comm g r r' := by
    by_cases h : r' + 1 = r
    · erw [shift_Ablk, shift_Ablk, CG_d, bx_comp_right, bx_comp_left]
      · exact bx_eq_bx cd.smul_Z _ _ (I.comm_res g) r r'
      · intro i κ σ hne hσ; have := I.deg_Cq_d hne; omega
      · intro i κ σ hne hσ; rw [I.deg_hat_ma hne, hσ]
    · rw [((cd.ind π).mapC I.compressed.C).shape r r' h, comp_zero, zero_comp]

/-! #### The coset-product and adjoint equations in `ℬ_{G,Z}(T × Sⁿ)` -/

theorem Nn_eq : (I.Nn : ℤ) = cd.N := rfl

theorem dual_CG_d (r r' : ℤ) :
    (dualComplex (cd.BG π).inv cd.N ((cd.ind π).mapC I.compressed.C)).d r r' =
      bx π cd.Z 1 (fun i ↦ ((I.Cq.C i).dual I.Nn (I.dimLE_Cq i)).d)
        (isSeq_one (A := I.Cq) (B := I.Cq) (I.Cq.dual I.Nn I.dimLE_Cq).tendsto_d)
        (cd.N - r) (cd.N - r') := by
  erw [dualComplex_d, CG_d, star_bx, bx_units_smul]
  refine bx_congr_block _ _ (fun i ↦ by simp) fun i κ σ hσ hκ ↦ ?_
  have hle := I.dimLE_Cq i σ
  rw [dual_d_apply, Matrix.smul_apply, transpose_apply,
    MatRealization.negOnePow_cast_eq (k := (I.Cq.C i).deg σ) (by rw [I.Nn_eq]; omega),
    smul_eq_mul, mul_assoc]

theorem φG_f (r : ℤ) :
    (cd.ind π).F.map (I.compressed.φ.f r) =
      bx π cd.Z 1 (fun i ↦ I.hat i (I.mφ i)) (isSeq_one I.φhat.tendsto) (cd.N - r) r := by
  rw [show I.compressed.φ.f r = _ from ExtInverse.toSymPoincare_φ_f _ _ _ r]
  exact ind_map_bx cd π _ _ _

theorem deg_hat_mφ {i : ℕ} {κ σ : (I.Cq.C i).X} (h : I.hat i (I.mφ i) κ σ ≠ 0) :
    ((I.Cq.C i).deg κ : ℤ) = cd.N - (I.Cq.C i).deg σ :=
  deg_dmat I.dimLE_Cq I.φhat h

theorem deg_hat_mB {i : ℕ} {gh : G i × G i} {κ σ : (I.Cq.C i).X}
    (h : I.hat i (I.mB i gh) κ σ ≠ 0) : ((I.Cq.C i).deg κ : ℤ) = (I.Cq.C i).deg σ + 1 := by
  exact (I.B i gh).deg1 κ.1 σ.1 h

theorem deg_hat_mV {i : ℕ} {g : G i} {κ σ : (I.Cq.C i).X} (h : I.hat i (I.mV i g) κ σ ≠ 0) :
    ((I.Cq.C i).deg κ : ℤ) = cd.N - (I.Cq.C i).deg σ + 1 := by
  have h₁ := (I.V i g).deg1 κ.1 σ.1 h
  have := I.dimLE i σ.1
  change ((I.D.C i).deg κ.1 : ℤ) = ((cd.n + 4 - (I.D.C i).deg σ.1 : ℕ) : ℤ) + 1 at h₁
  change ((I.D.C i).deg κ.1 : ℤ) = (cd.n : ℤ) + 4 - (I.D.C i).deg σ.1 + 1
  omega

theorem deg_dual_Cq_d {i : ℕ} {κ σ : (I.Cq.C i).X}
    (h : ((I.Cq.C i).dual I.Nn (I.dimLE_Cq i)).d κ σ ≠ 0) :
    ((I.Cq.C i).deg κ : ℤ) = (I.Cq.C i).deg σ + 1 :=
  deg_dual_d I.dimLE_Cq h

/-- (9.6): `A_gA_h - A_{gh} - d̂B̂ - B̂d̂ = -π a_g P a_h σ + π B P d σ + π d P B σ`. -/
theorem mul_res (g h : ∀ i, G i) :
    ExtTendsto cd.Z (fun i ↦ I.hat i (I.ma i (g i)) * I.hat i (I.ma i (h i)) -
      (I.hat i (I.mB i (g i, h i)) * (I.Cq.C i).d + (I.Cq.C i).d * I.hat i (I.mB i (g i, h i)) +
        I.hat i (I.ma i (g i * h i)))) I.Cq.label I.Cq.label :=
  (((I.extTendsto_W I.fprop_d (I.fprop_B g h)).add (I.extTendsto_W (I.fprop_B g h) I.fprop_d)).sub
      (I.extTendsto_W (I.fprop_a h) (I.fprop_a g))).congr fun i ↦ by
    have e := congrArg (I.hat i) (I.B i (g i, h i)).eq
    change I.hat i (I.ma i (g i) * I.ma i (h i) - I.ma i (g i * h i)) =
      I.hat i (I.mD i * I.mB i (g i, h i) + I.mB i (g i, h i) * I.mD i) at e
    rw [hat_sub, hat_add] at e
    rw [Cq_d', hat_mul, hat_mul, hat_mul, sub_eq_iff_eq_add.mp e]
    abel

/-- The adjoint residual of l.804–815:
`A_gφ̂ - φ̂A_{g⁻¹}^* - d̂V̂ - V̂δ̂ = -π a_g P φ π^* + π φ P^* a_{g⁻¹}^* π^* + …`. -/
theorem adj_res (g : ∀ i, G i) :
    ExtTendsto cd.Z (fun i ↦ I.hat i (I.ma i (g i)) * I.hat i (I.mφ i) -
      (I.hat i (I.mV i (g i)) * ((I.Cq.C i).dual I.Nn (I.dimLE_Cq i)).d +
        (I.Cq.C i).d * I.hat i (I.mV i (g i)) +
          I.hat i (I.mφ i) * (I.hat i (I.ma i (g i)⁻¹))ᵀ)) I.Cq.label I.Cq.label :=
  ((((I.extTendsto_W I.fprop_δ (I.fprop_V g)).add (I.extTendsto_W (I.fprop_V g) I.fprop_d)).add
      (I.extTendsto_W (I.fprop_aT fun i ↦ (g i)⁻¹) I.fprop_φ)).sub
        (I.extTendsto_W I.fprop_φ (I.fprop_a g))).congr fun i ↦ by
    have e := congrArg (I.hat i) (I.V i (g i)).eq
    change I.hat i (I.ma i (g i) * I.mφ i - I.mφ i * (I.ma i (g i)⁻¹)ᵀ) =
      I.hat i (I.mD i * I.mV i (g i) + I.mV i (g i) * I.mδ i) at e
    rw [hat_sub, hat_add] at e
    rw [Cq_d', Cq_dual_d', ← hat_transpose, hat_mul, hat_mul, hat_mul, hat_mul,
      sub_eq_iff_eq_add.mp e]
    abel

theorem act_f (g : ∀ i, G i) (r : ℤ) :
    (I.sheetAction.act g).f r = bx π cd.Z g (fun i ↦ I.hat i (I.ma i (g i))) (I.isSeq_a g) r r :=
  rfl

theorem CG_d' (r r' : ℤ) :
    I.sheetAction.CG.d r r' = bx π cd.Z 1 (fun i ↦ (I.Cq.C i).d) (isSeq_one I.Cq.tendsto_d) r r' :=
  I.CG_d r r'

theorem φG_f' (r : ℤ) :
    I.sheetAction.φG.f r =
      bx π cd.Z 1 (fun i ↦ I.hat i (I.mφ i)) (isSeq_one I.φhat.tendsto) (cd.N - r) r :=
  I.φG_f r

theorem dual_CG_d' (r r' : ℤ) :
    (dualComplex (cd.BG π).inv cd.N I.sheetAction.CG).d r r' =
      bx π cd.Z 1 (fun i ↦ ((I.Cq.C i).dual I.Nn (I.dimLE_Cq i)).d)
        (isSeq_one (A := I.Cq) (B := I.Cq) (I.Cq.dual I.Nn I.dimLE_Cq).tendsto_d)
        (cd.N - r) (cd.N - r') :=
  I.dual_CG_d r r'

/-- `B̂_{g,h}` in degree `r → r + 1` on the orbit representatives. -/
def Bblk (r : ℤ) : GraphFamily (fun i ↦ G i × G i) (I.Cq.obj π r) (I.Cq.obj π (r + 1)) :=
  ControlledSeq.gblock π (A := I.Cq) (B := I.Cq) (fun i gh ↦ I.hat i (I.mB i gh)) r (r + 1)

theorem hasGraphType_Bblk (r : ℤ) : HasGraphType (fun _ gh ↦ gh.1 * gh.2) (I.Bblk r) := by
  have := ControlledSeq.hasGraphType_gblock π (J := fun i ↦ G i × G i)
    (τ := fun _ gh ↦ gh.1 * gh.2) (A := I.Cq) (B := I.Cq)
    (u := fun i gh ↦ I.hat i (I.mB i gh)) I.graph_B r (r + 1)
  exact this

/-- `V̂_g` in degree `N - r → r + 1` on the orbit representatives. -/
def Vblk (r : ℤ) : GraphFamily G (I.Cq.obj π (cd.N - r)) (I.Cq.obj π (r + 1)) :=
  ControlledSeq.gblock π (A := I.Cq) (B := I.Cq) (fun i g ↦ I.hat i (I.mV i g)) (cd.N - r) (r + 1)

theorem hasGraphType_Vblk (r : ℤ) : HasGraphType (fun _ ↦ id) (I.Vblk r) :=
  ControlledSeq.hasGraphType_gblock π (τ := fun _ ↦ id) I.graph_V (cd.N - r) (r + 1)

/-- The chain-homotopy identity behind `mulHomotopy`, stated in `ℬ_{G,Z}(T × Sⁿ)` itself. -/
theorem mulHomotopy_comm_aux (g h : ∀ i, G i) (r : ℤ) :
    bx π cd.Z h (fun i ↦ I.hat i (I.ma i (h i))) (I.isSeq_a h) r r ≫
        bx π cd.Z g (fun i ↦ I.hat i (I.ma i (g i))) (I.isSeq_a g) r r =
      bx π cd.Z 1 (fun i ↦ (I.Cq.C i).d) (isSeq_one I.Cq.tendsto_d) r (r - 1) ≫
          bx π cd.Z (fun i ↦ g i * h i) (fun i ↦ I.hat i (I.mB i (g i, h i))) (I.isSeq_B g h)
            (r - 1) r +
        bx π cd.Z (fun i ↦ g i * h i) (fun i ↦ I.hat i (I.mB i (g i, h i))) (I.isSeq_B g h)
            r (r + 1) ≫
          bx π cd.Z 1 (fun i ↦ (I.Cq.C i).d) (isSeq_one I.Cq.tendsto_d) (r + 1) r +
      bx π cd.Z (g * h) (fun i ↦ I.hat i (I.ma i ((g * h) i))) (I.isSeq_a (g * h)) r r := by
  rw [bx_comp', bx_comp_left, bx_comp_right,
    bx_congr (I.isSeq_a (g * h)) (g' := fun i ↦ g i * h i)
      (u' := fun i ↦ I.hat i (I.ma i (g i * h i))) (I.isSeq_a (g * h)) (fun _ ↦ rfl)
      (fun _ ↦ rfl), bx_add, bx_add]
  · exact bx_eq_bx cd.smul_Z _ _ (I.mul_res g h) r r
  · intro i κ σ hne hσ; have := I.deg_hat_mB hne; omega
  · intro i κ σ hne hσ; have := I.deg_Cq_d hne; omega
  · intro i κ σ hne hσ; rw [I.deg_hat_ma hne, hσ]

/-- The coset-product homotopy `A_g A_h ≃ A_{gh}` with components `B̂_{g,h}`, (9.6). -/
def mulHomotopy (g h : ∀ i, G i) :
    Homotopy (I.sheetAction.act h ≫ I.sheetAction.act g) (I.sheetAction.act (g * h)) where
  hom r r' :=
    bx π cd.Z (fun i ↦ g i * h i) (fun i ↦ I.hat i (I.mB i (g i, h i))) (I.isSeq_B g h) r r'
  zero r r' hrr' := bx_eq_zero_of_deg _ fun i κ σ hσ hκ ↦ by
    by_contra hne
    have := I.deg_hat_mB hne
    exact hrr' (by change r + 1 = r'; omega)
  comm r := by
    erw [dNext_eq _ (show (ComplexShape.down ℤ).Rel r (r - 1) by simp),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (r + 1) r by simp)]
    rw [HomologicalComplex.comp_f, act_f, act_f, act_f, CG_d', CG_d']
    exact I.mulHomotopy_comm_aux g h r

theorem deg_hat_maT {i : ℕ} {g : G i} {κ σ : (I.Cq.C i).X}
    (h : (I.hat i (I.ma i g))ᵀ κ σ ≠ 0) : ((I.Cq.C i).deg κ : ℤ) = (I.Cq.C i).deg σ :=
  (I.deg_hat_ma h).symm

theorem dualAct_comp_φG (g : ∀ i, G i) (r : ℤ) :
    (dualHom (cd.BG π).inv cd.N (I.sheetAction.act g⁻¹)).f r ≫ I.sheetAction.φG.f r =
      bx π cd.Z g (fun i ↦ I.hat i (I.mφ i) * (I.hat i (I.ma i (g i)⁻¹))ᵀ)
        (((I.isSeq_a g⁻¹).transpose.mul (isSeq_one I.φhat.tendsto)).congr (fun i ↦ by simp)
          fun _ ↦ rfl) (cd.N - r) r := by
  erw [dualHom_f, act_f, star_bx, φG_f', bx_comp_right]
  · exact bx_congr _ _ (fun i ↦ by simp) (fun _ ↦ rfl) _ _
  · intro i κ σ hne hσ
    have := I.deg_hat_maT hne
    omega

theorem φG_comp_act (g : ∀ i, G i) (r : ℤ) :
    I.sheetAction.φG.f r ≫ (I.sheetAction.act g).f r =
      bx π cd.Z g (fun i ↦ I.hat i (I.ma i (g i)) * I.hat i (I.mφ i))
        ((isSeq_one I.φhat.tendsto).mul (I.isSeq_a g) |>.congr (fun _ ↦ mul_one _) fun _ ↦ rfl)
        (cd.N - r) r := by
  rw [φG_f', act_f]
  exact bx_comp_left _ _ fun i κ σ hne hσ ↦ by have := I.deg_hat_mφ hne; omega

theorem dualCG_d_comp_V (g : ∀ i, G i) (r : ℤ) :
    (dualComplex (cd.BG π).inv cd.N I.sheetAction.CG).d r (r - 1) ≫
        bx π cd.Z g (fun i ↦ I.hat i (I.mV i (g i))) (I.isSeq_V g) (cd.N - (r - 1)) r =
      bx π cd.Z g (fun i ↦ I.hat i (I.mV i (g i)) * ((I.Cq.C i).dual I.Nn (I.dimLE_Cq i)).d)
        (((isSeq_one (A := I.Cq) (B := I.Cq) (I.Cq.dual I.Nn I.dimLE_Cq).tendsto_d).mul
          (I.isSeq_V g)).congr (fun _ ↦ mul_one _) fun _ ↦ rfl) (cd.N - r) r := by
  rw [dual_CG_d']
  exact bx_comp_left _ _ fun i κ σ hne hσ ↦ by have := I.deg_dual_Cq_d hne; omega

theorem V_comp_CG_d (g : ∀ i, G i) (r : ℤ) :
    bx π cd.Z g (fun i ↦ I.hat i (I.mV i (g i))) (I.isSeq_V g) (cd.N - r) (r + 1) ≫
        I.sheetAction.CG.d (r + 1) r =
      bx π cd.Z g (fun i ↦ (I.Cq.C i).d * I.hat i (I.mV i (g i)))
        (((I.isSeq_V g).mul (isSeq_one I.Cq.tendsto_d)).congr (fun _ ↦ one_mul _) fun _ ↦ rfl)
        (cd.N - r) r := by
  rw [CG_d']
  exact bx_comp_right _ _ fun i κ σ hne hσ ↦ by have := I.deg_hat_mV hne; omega

/-- The adjoint homotopy `A_g φ̂ ≃ φ̂ A_{g⁻¹}^*` with components `V̂_g = π V_g π^*` (l.804–815). -/
def adjHomotopy (g : ∀ i, G i) :
    Homotopy (I.sheetAction.φG ≫ I.sheetAction.act g)
      (dualHom (cd.BG π).inv cd.N (I.sheetAction.act g⁻¹) ≫ I.sheetAction.φG) where
  hom r r' := bx π cd.Z g (fun i ↦ I.hat i (I.mV i (g i))) (I.isSeq_V g) (cd.N - r) r'
  zero r r' hrr' := bx_eq_zero_of_deg _ fun i κ σ hσ hκ ↦ by
    by_contra hne
    have := I.deg_hat_mV hne
    exact hrr' (by change r + 1 = r'; omega)
  comm r := by
    erw [dNext_eq _ (show (ComplexShape.down ℤ).Rel r (r - 1) by simp),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (r + 1) r by simp)]
    rw [HomologicalComplex.comp_f,
      HomologicalComplex.comp_f, I.dualAct_comp_φG, I.φG_comp_act]
    erw [I.dualCG_d_comp_V, I.V_comp_CG_d]
    exact (bx_eq_bx cd.smul_Z _ _ (I.adj_res g) _ r).trans
      ((congrArg (· + _) (bx_add _ _ _ _)).trans (bx_add _ _ _ _)).symm

/-- **Proposition 9.2, sheet part** (l.746–825): the compressed complex with `φ̂`, the compressed
chain maps `A_g = π a_g σ` (`A_1 = 1`), the coset-product homotopies `B̂_{g,h} = π B_{g,h} σ` and
the adjoint homotopies `V̂_g = π V_g π^*`, all of uniform graph type, satisfy the equations of
`SheetData` in `ℬ_{G,Z}(T × Sⁿ)` after the sheet shift: each residual is a sum of words through
the far projection, which have exterior witnesses by Lemma 9.1. -/
def sheetData : cd.SheetData π where
  toAction := I.sheetAction
  B := I.Bblk
  hB := I.hasGraphType_Bblk
  mul g h := ⟨I.mulHomotopy g h, fun _ ↦ rfl⟩
  V := I.Vblk
  hV := I.hasGraphType_Vblk
  adj g := ⟨I.adjHomotopy g, fun _ ↦ rfl⟩

theorem sheetData_C : I.sheetData.toAction.C = I.compressed := rfl

/-! #### `π`, `σ` are inverse isometries in `ℬ_{1,Z₀}(Sⁿ)` (last paragraph of Prop. 9.2) -/

/-- The uncompressed chain model `(D, φ)`, a Poincaré complex of `𝒜_1(Sⁿ)` (Lemma 8.1). -/
def uncompressed : SymPoincare cd.A1S.inv cd.N := I.duality.symPoincare (scalarHom cd.Cp)

theorem far_mem_Z₀ {i : ℕ} {σ : (I.D.C i).X} (h : I.far i σ) : I.D.label i σ ∈ cd.Z₀ :=
  (I.R_lt_t.trans (I.far_dist i σ h)).le

theorem isSeq_nearProj :
    IsSeq (scalarHom cd.Cp) I.D I.Dq 1 (fun i ↦ nearProj fun σ ↦ ¬I.far i σ) :=
  isSeq_one (I.D.toQuot I.far I.isSub_far).tendsto

theorem isSeq_nearIncl :
    IsSeq (scalarHom cd.Cp) I.Dq I.D 1 (fun i ↦ nearIncl fun σ ↦ ¬I.far i σ) :=
  isSeq_one (ControlledSeq.tendsto_nearIncl I.D I.far I.isSub_far)

theorem compressed_push_C :
    (I.compressed.map cd.push).C = I.Dq.extComplex (scalarHom cd.Cp) cd.Z₀ := rfl

theorem uncompressed_proj_C :
    (I.uncompressed.map cd.proj).C = I.D.extComplex (scalarHom cd.Cp) cd.Z₀ := rfl

theorem compressed_push_p : (I.compressed.map cd.push).p = 𝟙 _ := by
  simp [SymPoincare.map, compressed_p]

theorem uncompressed_proj_p : (I.uncompressed.map cd.proj).p = 𝟙 _ := by
  simp [SymPoincare.map, uncompressed, ControlledSeq.SymDuality.symPoincare,
    ControlledSeq.SymDuality.symPoincareObj]

theorem compressed_push_φ_f (r : ℤ) :
    (I.compressed.map cd.push).φ.f r =
      bx (scalarHom cd.Cp) cd.Z₀ (A := I.Dq) (B := I.Dq) 1 (fun i ↦ I.hat i (I.mφ i))
        (isSeq_one (ControlledSeq.PropTendsto.quot (D := I.D) (D' := I.D) (hfar := I.isSub_far)
            (hfar' := I.isSub_far) I.duality.hom.tendsto)) (cd.N - r) r := by
  rw [SymPoincare.map_φ, InvFunctor.mapDual_f,
    show I.compressed.φ.f r = _ from ExtInverse.toSymPoincare_φ_f _ _ _ r]
  rfl

theorem uncompressed_proj_φ_f (r : ℤ) :
    (I.uncompressed.map cd.proj).φ.f r =
      bx (scalarHom cd.Cp) cd.Z₀ (A := I.D) (B := I.D) 1 (fun i ↦ I.mφ i)
        (isSeq_one I.duality.hom.tendsto) (cd.N - r) r :=
  extInv_mapDual_dualityMap_f I.dimLE I.duality.hom r

/-- The section `σ` of (9.1). -/
abbrev mσ (i : ℕ) : Matrix (I.D.C i).X (I.Dq.C i).X ℚ := nearIncl fun σ ↦ ¬I.far i σ
/-- The projection `π` of (9.1). -/
abbrev mπ (i : ℕ) : Matrix (I.Dq.C i).X (I.D.C i).X ℚ := nearProj fun σ ↦ ¬I.far i σ

theorem nearProj_deg {i : ℕ} {κ : (I.Dq.C i).X} {σ : (I.D.C i).X} (h : I.mπ i κ σ ≠ 0) :
    ((I.Dq.C i).deg κ : ℤ) = (I.D.C i).deg σ := by
  obtain rfl := nearProj_ne_zero h; rfl

theorem nearIncl_deg {i : ℕ} {κ : (I.D.C i).X} {σ : (I.Dq.C i).X} (h : I.mσ i κ σ ≠ 0) :
    ((I.D.C i).deg κ : ℤ) = (I.Dq.C i).deg σ := by
  obtain rfl := nearIncl_ne_zero h; rfl

/-- `π : D → D/F`, an exact chain map. -/
def quotMap : (I.uncompressed.map cd.proj).C ⟶ (I.compressed.map cd.push).C :=
  (extInv (scalarHom cd.Cp) cd.Z₀).mapH ((I.D.toQuot I.far I.isSub_far).toComplex _)

theorem quotMap_f (r : ℤ) :
    I.quotMap.f r = bx (scalarHom cd.Cp) cd.Z₀ 1 I.mπ I.isSeq_nearProj r r := rfl

theorem mσ_res (i : ℕ) : (I.D.C i).d * I.mσ i - I.mσ i * (I.Dq.C i).d =
    (farProj (I.far i) * (I.D.C i).d).submatrix id Subtype.val := by
  have h1 : (I.Dq.C i).d = I.mπ i * (I.D.C i).d * I.mσ i := (nearProj_mul_mul_nearIncl _).symm
  have h2 := one_sub_nearIncl_mul_nearProj (α := (I.D.C i).X) (I.far i)
  rw [h1, ← mul_nearIncl, ← h2]
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc] <;> rfl

/-- The chain defect `dσ - σd̂ = P d σ` of the section is `Z₀`-supported. -/
theorem sect_res :
    ExtTendsto cd.Z₀ (fun i ↦ (I.D.C i).d * I.mσ i - I.mσ i * (I.Dq.C i).d) I.Dq.label
      I.D.label := by
  refine tendsto_zero_of_le I.D.tendsto_d fun i ↦ ?_
  dsimp only
  rw [mσ_res]
  exact (matEd_submatrix_le (Z := cd.Z₀) (source := I.D.label i) (target := I.D.label i)
    Subtype.val id).trans (matEd_farProj_mul_le fun _ h ↦ I.far_mem_Z₀ h)

theorem sect_comm (r r' : ℤ) (h : r' + 1 = r) :
    bx (scalarHom cd.Cp) cd.Z₀ 1 I.mσ I.isSeq_nearIncl r r ≫
        bx (scalarHom cd.Cp) cd.Z₀ 1 (fun i ↦ (I.D.C i).d) (isSeq_one I.D.tendsto_d) r r' =
      bx (scalarHom cd.Cp) cd.Z₀ 1 (fun i ↦ (I.Dq.C i).d) (isSeq_one I.Dq.tendsto_d) r r' ≫
        bx (scalarHom cd.Cp) cd.Z₀ 1 I.mσ I.isSeq_nearIncl r' r' := by
  rw [bx_comp1, bx_comp1]
  · exact bx_eq_bx (smul_Z₀ cd) _ _ I.sect_res r r'
  · intro i κ σ hne hσ; have := (I.Dq.C i).d_deg κ σ hne; omega
  · intro i κ σ hne hσ; rw [I.nearIncl_deg hne, hσ]

/-- `σ : D/F → D`, a chain map of `ℬ_{1,Z₀}(Sⁿ)` (its defect `P d σ` is `Z₀`-supported). -/
def sectMap : (I.compressed.map cd.push).C ⟶ (I.uncompressed.map cd.proj).C where
  f r := bx (scalarHom cd.Cp) cd.Z₀ 1 I.mσ I.isSeq_nearIncl r r
  comm' r r' h := I.sect_comm r r' h

theorem sectMap_f (r : ℤ) :
    I.sectMap.f r = bx (scalarHom cd.Cp) cd.Z₀ 1 I.mσ I.isSeq_nearIncl r r := rfl

theorem quot_sect_f (r : ℤ) :
    bx (scalarHom cd.Cp) cd.Z₀ 1 I.mπ I.isSeq_nearProj r r ≫
        bx (scalarHom cd.Cp) cd.Z₀ 1 I.mσ I.isSeq_nearIncl r r =
      bx (scalarHom cd.Cp) cd.Z₀ 1 (fun i ↦ (1 : Matrix (I.D.C i).X (I.D.C i).X ℚ))
        (isSeq_one PropTendsto.one) r r := by
  rw [bx_comp1]
  · refine bx_eq_bx (smul_Z₀ cd) _ _ ?_ r r
    refine tendsto_zero_of_le (tendsto_const_nhds (x := (0 : ℝ≥0∞))) fun i ↦ ?_
    have h2 := one_sub_nearIncl_mul_nearProj (α := (I.D.C i).X) (I.far i)
    have h3 : I.mσ i * I.mπ i - 1 = -(farProj (I.far i) * 1) := by
      (rw [Matrix.mul_one, ← h2, neg_sub]) <;> rfl
    dsimp only
    rw [h3, matEd_neg]
    refine (matEd_farProj_mul_le fun _ h ↦ I.far_mem_Z₀ h).trans ?_
    rw [prop_one]
  · intro i κ σ hne hσ; rw [I.nearProj_deg hne, hσ]

theorem quot_sect : I.quotMap ≫ I.sectMap = 𝟙 _ := by
  ext r
  erw [HomologicalComplex.comp_f, quotMap_f, sectMap_f, quot_sect_f, HomologicalComplex.id_f]
  exact bx_one r

theorem sect_quot_f (r : ℤ) :
    bx (scalarHom cd.Cp) cd.Z₀ 1 I.mσ I.isSeq_nearIncl r r ≫
        bx (scalarHom cd.Cp) cd.Z₀ 1 I.mπ I.isSeq_nearProj r r =
      bx (scalarHom cd.Cp) cd.Z₀ 1 (fun i ↦ (1 : Matrix (I.Dq.C i).X (I.Dq.C i).X ℚ))
        (isSeq_one PropTendsto.one) r r := by
  rw [bx_comp1]
  · exact bx_congr _ _ (fun _ ↦ rfl) (fun i ↦ nearProj_mul_nearIncl) r r
  · intro i κ σ hne hσ; rw [I.nearIncl_deg hne, hσ]

theorem sect_quot : I.sectMap ≫ I.quotMap = 𝟙 _ := by
  ext r
  erw [HomologicalComplex.comp_f, quotMap_f, sectMap_f, sect_quot_f, HomologicalComplex.id_f]
  exact bx_one r

theorem deg_mφ {i : ℕ} {κ σ : (I.D.C i).X} (h : I.mφ i κ σ ≠ 0) :
    ((I.D.C i).deg κ : ℤ) = cd.N - (I.D.C i).deg σ :=
  deg_dmat I.dimLE I.duality.hom h

theorem conj_f (r : ℤ) :
    bx (scalarHom cd.Cp) cd.Z₀ (fun i ↦ ((1 : ∀ _ : ℕ, Unit) i)⁻¹) (fun i ↦ (I.mπ i)ᵀ)
        I.isSeq_nearProj.transpose (cd.N - r) (cd.N - r) ≫
      bx (scalarHom cd.Cp) cd.Z₀ 1 I.mφ (isSeq_one I.duality.hom.tendsto) (cd.N - r) r ≫
        bx (scalarHom cd.Cp) cd.Z₀ 1 I.mπ I.isSeq_nearProj r r =
      bx (scalarHom cd.Cp) cd.Z₀ (A := I.Dq) (B := I.Dq) 1 (fun i ↦ I.hat i (I.mφ i))
        (isSeq_one (ControlledSeq.PropTendsto.quot (D := I.D) (D' := I.D) (hfar := I.isSub_far)
            (hfar' := I.isSub_far) I.duality.hom.tendsto)) (cd.N - r) r := by
  rw [bx_comp1, bx_comp_right]
  · refine bx_congr _ _ (fun _ ↦ rfl) (fun i ↦ ?_) _ _
    erw [ControlledSeq.nearProj_transpose, nearProj_mul_mul_nearIncl] <;> rfl
  · intro i κ σ hne hσ
    rw [transpose_apply] at hne
    obtain rfl := nearProj_ne_zero hne
    exact hσ
  · intro i κ σ hne hσ; rw [I.deg_mφ hne, hσ]; ring

theorem conj_eq : dualHom cd.B1S.inv cd.N I.quotMap ≫ (I.uncompressed.map cd.proj).φ ≫
    I.quotMap = (I.compressed.map cd.push).φ := by
  ext r
  erw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, dualHom_f, quotMap_f, quotMap_f,
    star_bx, uncompressed_proj_φ_f, compressed_push_φ_f]
  exact I.conj_f r

/-- **`π : D → C` is a homotopy isometry in `ℬ_{1,Z₀}(Sⁿ)`** (last paragraph of the proof of
Proposition 9.2, l.817–824): `πσ = 1`, `σπ = 1 - P` with `P` supported in `Z₀`, and the
transported cap map is exactly `πφπ^* = φ̂`. -/
def isometry : (I.uncompressed.map cd.proj).HomotopyIsometry (I.compressed.map cd.push) where
  f := I.quotMap
  g := I.sectMap
  f_kar := by rw [uncompressed_proj_p, compressed_push_p, Category.id_comp, Category.comp_id]
  g_kar := by rw [uncompressed_proj_p, compressed_push_p, Category.id_comp, Category.comp_id]
  fg := Homotopy.ofEq (by rw [quot_sect, uncompressed_proj_p])
  gf := Homotopy.ofEq (by rw [sect_quot, compressed_push_p])
  conj := Homotopy.ofEq I.conj_eq

/-- **Proposition 9.2, class part**: after forgetting `T`, the compressed class is the class of
the uncompressed chain model, `push [C] = proj [D]` in `Lconc_N(ℬ_{1,Z₀}(Sⁿ))`. -/
theorem push_cls_compressed :
    Lconc.map cd.push (Lconc.cls I.compressed) = Lconc.map cd.proj (Lconc.cls I.uncompressed) := by
  rw [Lconc.map_cls, Lconc.map_cls]
  exact (Lconc.cls_eq_of_isometry I.isometry).symm

end ChainModelInput

/-! ### Assembly: `ClassConstruction` from chain-model inputs -/

/-- **`ClassConstruction` from chain-model inputs**: if for the fixed data of every action there
are tail groups and a chain-model input over `d.control` whose uncompressed class is the germ of
`f̂` after `proj`, then Proposition 9.2 gives `ClassConstruction germ`. -/
theorem classConstruction_of_chainModel {germ : ManifoldGerm}
    (h : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
      [SecondCountableTopology M] [LocallyCompactSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ConnectedSpace M] [AddAction ℤ_[p] M]
      [ContinuousVAdd ℤ_[p] M] (d : FixedData p n M),
      ∃ (Γ : TailGroups p d.Cp) (I : ChainModelInput d.control Γ.π),
        Lconc.map d.control.proj (Lconc.cls I.uncompressed) =
          Lconc.map d.control.proj (germ d.control d.fhatS)) :
    ClassConstruction germ := by
  intro p _ n M _ _ _ _ _ _ _ _ d
  obtain ⟨Γ, I, hI⟩ := h p n M d
  exact ⟨Γ, I.sheetData, I.push_cls_compressed.trans hI⟩

/-- The existential form `ClassConstruction'` from chain-model inputs. -/
theorem classConstruction'_of_chainModel {germ : ManifoldGerm}
    (h : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
      [SecondCountableTopology M] [LocallyCompactSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ConnectedSpace M] [AddAction ℤ_[p] M]
      [ContinuousVAdd ℤ_[p] M] (d : FixedData p n M),
      ∃ (Γ : TailGroups p d.Cp) (I : ChainModelInput d.control Γ.π),
        Lconc.map d.control.proj (Lconc.cls I.uncompressed) =
          Lconc.map d.control.proj (germ d.control d.fhatS)) :
    ClassConstruction' germ :=
  classConstruction'_of (classConstruction_of_chainModel h)

end HSFormal.Prop92

/-! ### The cubical chain model of §8 as a `ChainModelInput` -/

namespace HSFormal.FixedData

open HSFormal.Prop92 HSFormal.LTheory

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {M : Type*} [TopologicalSpace M] [AddAction ℤ_[p] M]
  [ContinuousVAdd ℤ_[p] M] [LocallyCompactSpace M] [FirstCountableTopology M] [T2Space M]
  (d : FixedData p n M)

/-- The chain-model data of Lemmas 8.1–8.2 on the germ grid (`chainModelData`), as the input of
Proposition 9.2 for `cd = d.control` and the tail groups `G_i = H/K_i → C_p`. -/
def chainModelInput : ChainModelInput d.control d.toTailGroups.π where
  D := d.seqW
  dimLE := d.seqW_dimLE
  duality := d.seqWDuality
  ρ := d.chainModelData.ρ
  buf := d.chainModelData.buf
  far := d.chainModelData.far
  decFar := d.chainModelData.decFar
  isSub_far := d.chainModelData.isSub_far
  t := d.chainModelData.t
  R_lt_t := d.chainModelData.R_lt_t
  far_dist := d.chainModelData.far_dist
  near_buf := d.chainModelData.near_buf
  d_buf := d.chainModelData.d_buf
  φ_buf := d.chainModelData.φ_buf
  b_buf := d.chainModelData.b_buf
  homInv_buf := d.chainModelData.homInv_buf
  invHom_buf := d.chainModelData.invHom_buf
  a := d.chainModelData.a
  a_one := d.chainModelData.a_one
  a_f := d.chainModelData.a_f
  a_buf := d.chainModelData.a_buf
  B := d.chainModelData.B
  B_f := d.chainModelData.B_f
  B_buf := d.chainModelData.B_buf
  V := d.chainModelData.V
  V_f := d.chainModelData.V_f
  V_buf := d.chainModelData.V_buf

/-- The uncompressed chain model is the manifold germ of `f̂` (`D_i` is the germ complex). -/
theorem cls_chainModelInput_uncompressed :
    Lconc.cls d.chainModelInput.uncompressed = manifoldGerm d.control d.fhatS := by
  rw [d.manifoldGerm_fhatS]
  rfl

end HSFormal.FixedData

namespace HSFormal.Prop92

/-- **S1–S3 (Proposition 9.2 applied to the chain models of §8)**: `ClassConstruction` for the
cubical manifold germ, with `Γ = d.toTailGroups`, `S` the compressed sheet data and `c = f̂`. -/
theorem classConstruction_manifoldGerm : ClassConstruction manifoldGerm :=
  classConstruction_of_chainModel fun _ _ _ _ _ _ _ _ _ _ _ _ d ↦
    ⟨d.toTailGroups, d.chainModelInput, by rw [d.cls_chainModelInput_uncompressed]⟩

/-- **`ClassConstruction' manifoldGerm`**, the hypothesis of `hilbertSmith_of_remaining`. -/
theorem classConstruction'_manifoldGerm : ClassConstruction' manifoldGerm :=
  classConstruction'_of classConstruction_manifoldGerm

end HSFormal.Prop92
