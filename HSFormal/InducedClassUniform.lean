import HSFormal.Assembly
import HSFormal.CornerClass

/-!
# Uniform sheet sums from sequencewise equations (manuscript §10, (10.1)–(10.4))

The hypotheses `SheetData` of (★) impose the equations of (5.1) after the sheet shift for every
*sequence* `g ∈ ∏ G_i` of a fixed uniform graph family.  The averaged projector (10.2) and its
homotopies are sums over *all* `g ∈ G_i` at index `i`.  This file supplies the passage:

* `tendsto_iSup_of_forall_seq` (**worst sequences**): if `f i (j i) → 0` along every sequence
  `j ∈ ∏ J_i` of finite nonempty sets, then `sup_{j ∈ J_i} f i j → 0`.
* `matEd`: the largest distance from `Z` of the endpoints of the nonzero entries of a labelled
  matrix; for an invariant `Z` it is unchanged by the sheet shift (`matEd_sheet`).
* `extM`: a controlled family as a morphism of `ℬ_Z(X)`, and `extM_eq_iff`: equations in
  `ℬ_Z(X)` are endpoint estimates of the defect (manuscript §2).
* `tendsto_iSup_matEd_of_seq`, `extM_eq_of_sum`: sequencewise equations of shifted matrices give
  uniform endpoint estimates, hence equations between the shifted sums.
* `seqScalar`, `seqUnit`: multiplication by a nonvanishing rational sequence, a central
  self-adjoint automorphism (the normalizing scalar `q = (|G_i|)_i` of (10.2)).
* `sheetIncl`, `sheetProj`: the inclusion and projection of the sheet `1` of `Res Ind M`; they are
  natural, adjoint, and cut out the `(1, 1)` block of a shifted sum.
-/

noncomputable section

namespace HSFormal

open Filter Matrix CategoryTheory CategoryTheory.Limits Metric
open scoped ENNReal Topology Pointwise

/-! ### Worst sequences -/

/-- **Worst sequences.** Uniform bounds over finite nonempty index sets follow from bounds along
every sequence: choose at each index a worst element. -/
theorem tendsto_iSup_of_forall_seq {J : ℕ → Type*} [∀ i, Finite (J i)] [∀ i, Nonempty (J i)]
    {f : ∀ i, J i → ℝ≥0∞} (h : ∀ j : ∀ i, J i, Tendsto (fun i ↦ f i (j i)) atTop (𝓝 0)) :
    Tendsto (fun i ↦ ⨆ j, f i j) atTop (𝓝 0) := by
  choose j hj using fun i ↦ exists_eq_ciSup_of_finite (f := f i)
  exact (h j).congr fun i ↦ hj i

/-! ### Endpoint distances of labelled matrices -/

section MatEd

variable {H X A B : Type*} [Group H] [MulAction H X] [PseudoEMetricSpace X] (Z : Set X)

/-- The largest distance from `Z` of the endpoints of the nonzero entries of `u`. -/
def matEd (u : Matrix B A ℚ) (source : A → X) (target : B → X) : ℝ≥0∞ :=
  ⨆ (b) (a) (_ : u b a ≠ 0), max (infEDist (target b) Z) (infEDist (source a) Z)

variable {Z} {u v : Matrix B A ℚ} {source : A → X} {target : B → X}

theorem matEd_le_iff {r : ℝ≥0∞} :
    matEd Z u source target ≤ r ↔
      ∀ b a, u b a ≠ 0 → infEDist (target b) Z ≤ r ∧ infEDist (source a) Z ≤ r := by
  simp only [matEd, iSup_le_iff, max_le_iff]

theorem infEDist_le_matEd {b : B} {a : A} (h : u b a ≠ 0) :
    infEDist (target b) Z ≤ matEd Z u source target ∧
      infEDist (source a) Z ≤ matEd Z u source target :=
  matEd_le_iff.mp le_rfl b a h

theorem matEd_smul_le (c : ℚ) : matEd Z (c • u) source target ≤ matEd Z u source target :=
  matEd_le_iff.mpr fun b a h ↦ infEDist_le_matEd (by
    rw [Matrix.smul_apply, smul_eq_mul] at h
    exact right_ne_zero_of_mul h)

theorem matEd_neg : matEd Z (-u) source target = matEd Z u source target := by
  simp [matEd]

theorem matEd_sum_le {ι : Type*} (s : Finset ι) (w : ι → Matrix B A ℚ) :
    matEd Z (∑ j ∈ s, w j) source target ≤ ⨆ j ∈ s, matEd Z (w j) source target := by
  refine matEd_le_iff.mpr fun b a hba ↦ ?_
  erw [Finset.sum_apply, Finset.sum_apply] at hba
  obtain ⟨j, hj, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hba
  have := infEDist_le_matEd (Z := Z) (source := source) (target := target) hne
  exact ⟨this.1.trans (le_iSup₂_of_le j hj le_rfl), this.2.trans (le_iSup₂_of_le j hj le_rfl)⟩

/-- For an invariant `Z`, the sheet shift does not change endpoint distances. -/
theorem matEd_sheet [IsIsometricSMul H X] {Γ : Type*} [Group Γ] (hZ : ∀ h : H, h • Z = Z) (ρ : Γ →* H) (g : Γ)
    (u : Matrix B A ℚ) :
    matEd Z (sheet g u) (sheetLabel ρ source) (sheetLabel ρ target) =
      matEd Z u source target := by
  refine le_antisymm (matEd_le_iff.mpr fun p q hpq ↦ ?_) (matEd_le_iff.mpr fun b a hba ↦ ?_)
  · obtain ⟨-, hu⟩ := sheet_apply_ne_zero hpq
    simpa [sheetLabel, infEDist_smul_of_invariant hZ] using infEDist_le_matEd (Z := Z)
      (source := source) (target := target) hu
  · have h : sheet g u (b, 1) (a, g) ≠ 0 := by simpa using hba
    simpa [sheetLabel, infEDist_smul_of_invariant hZ] using
      infEDist_le_matEd (Z := Z) (source := sheetLabel ρ source) (target := sheetLabel ρ target) h

end MatEd

/-! ### Controlled families as morphisms of `ℬ_Z(X)` -/

open LTheory AsymptoticObject AsymptoticCategory Compression

section Ext

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  {π : ∀ i, G i →* H} {X : Type} [MulAction H X] [PseudoEMetricSpace X] (Z : Set X)

/-- The object of `ℬ_Z(X)` of a based module. -/
abbrev extO (M : AsymptoticObject π X) : exteriorInvCat π Z :=
  ExteriorCategory.functor.obj (AsymptoticCategory.functor.obj M)

/-- A controlled family as a morphism of `ℬ_Z(X)`. -/
abbrev extM {M N : AsymptoticObject π X} (f : M ⟶ N) : extO Z M ⟶ extO Z N :=
  ExteriorCategory.functor.map (AsymptoticCategory.functor.map f)

variable {Z} {M N P : AsymptoticObject π X}

theorem extM_comp (f : M ⟶ N) (g : N ⟶ P) : extM Z f ≫ extM Z g = extM Z (f ≫ g) := by
  simp only [extM, Functor.map_comp]
  rfl

theorem extM_add (f g : M ⟶ N) : extM Z f + extM Z g = extM Z (f + g) := by
  simp only [extM, Functor.map_add]
  rfl

theorem extM_sub (f g : M ⟶ N) : extM Z f - extM Z g = extM Z (f - g) := by
  simp only [extM, Functor.map_sub]
  rfl

theorem extM_zsmul (n : ℤ) (f : M ⟶ N) : n • extM Z f = extM Z (n • f) := by
  simp only [extM, Functor.map_zsmul]
  rfl

theorem extM_units_smul (u : ℤˣ) (f : M ⟶ N) : u • extM Z f = extM Z ((u : ℤ) • f) := by
  rw [Units.smul_def, extM_zsmul]

theorem extM_units_smul_rat (u : ℤˣ) (f : M ⟶ N) :
    u • extM Z f = extM Z (((u : ℤ) : ℚ) • f) := by
  rw [extM_units_smul, Int.cast_smul_eq_zsmul]

theorem extM_id (M : AsymptoticObject π X) : extM Z (𝟙 M) = 𝟙 _ := by
  rw [extM, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rfl

theorem extM_star (f : M ⟶ N) :
    (exteriorInvCat π Z).inv.star (extM Z f) = extM Z (AsymptoticObject.transpose f) :=
  rfl

/-- Manuscript §2: an equation in `ℬ_Z(X)` between controlled families is the vanishing of the
endpoint distances of the defect. -/
theorem extM_eq_iff (f g : M ⟶ N) :
    extM Z f = extM Z g ↔ Tendsto (endpointDist Z (f - g).1) atTop (𝓝 0) := by
  erw [extM, extM, ExteriorCategory.functor_map_eq_iff, ← Functor.map_sub, inIdeal_map_iff]

/-- Every morphism of `ℬ_Z(X)` has a controlled representative. -/
theorem exists_extM {A B : exteriorInvCat π Z} (φ : A ⟶ B) :
    ∃ f : A.as.as ⟶ B.as.as, extM Z f = φ := by
  obtain ⟨φ', rfl⟩ := (ExteriorCategory.functor (Z := Z)).map_surjective φ
  obtain ⟨f, rfl⟩ := AsymptoticCategory.exists_rep φ'
  exact ⟨f, rfl⟩

/-- A chosen controlled representative. -/
def repM {A B : exteriorInvCat π Z} (φ : A ⟶ B) : A.as.as ⟶ B.as.as :=
  (exists_extM φ).choose

@[simp]
theorem extM_repM {A B : exteriorInvCat π Z} (φ : A ⟶ B) : extM Z (repM φ) = φ :=
  (exists_extM φ).choose_spec

end Ext

/-! ### Uniformization -/

section Uniform

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  {π : ∀ i, G i →* H} {X : Type} [MulAction H X] [PseudoEMetricSpace X] [IsIsometricSMul H X]
  {Z : Set X} (hZ : ∀ h : H, h • Z = Z) {M N : AsymptoticObject π X}

omit [IsIsometricSMul H X] [∀ i, Fintype (G i)] in
theorem endpointDist_eq_matEd (f : Family M N) (i : ℕ) :
    endpointDist Z f i = matEd Z (f i) (M.fullLabel i) (N.fullLabel i) :=
  rfl

include hZ in
/-- **A single shifted sequence**: an equation in `ℬ_Z(X)` whose defect is the shift of `R` gives
endpoint estimates for `R` on the orbit representatives. -/
theorem tendsto_matEd_of_extM_eq {f g : M ⟶ N} (h : extM Z f = extM Z g) (τ : ∀ i, G i)
    (R : ScalarFamily M N) (hR : ∀ i, f.1 i - g.1 i = sheet (τ i) (R i)) :
    Tendsto (fun i ↦ matEd Z (R i) (M.label i) (N.label i)) atTop (𝓝 0) := by
  refine ((extM_eq_iff f g).mp h).congr fun i ↦ ?_
  rw [endpointDist_eq_matEd, sub_val, hR, fullLabel_eq_sheetLabel, fullLabel_eq_sheetLabel,
    matEd_sheet hZ]

include hZ in
/-- **Uniform shifted sums**: if the defect of an equation is a sum of shifts of matrices with
uniformly small endpoint distances, the equation holds in `ℬ_Z(X)`, however many terms. -/
theorem extM_eq_of_sum {J : ℕ → Type*} [∀ i, Fintype (J i)] (τ : ∀ i, J i → G i)
    (R : GraphFamily J M N) {r : ℕ → ℝ≥0∞} (hr : Tendsto r atTop (𝓝 0))
    (hR : ∀ i p, matEd Z (R i p) (M.label i) (N.label i) ≤ r i) {f g : M ⟶ N}
    (hfg : ∀ i, f.1 i - g.1 i = ∑ p, sheet (τ i p) (R i p)) : extM Z f = extM Z g := by
  rw [extM_eq_iff]
  refine tendsto_zero_of_le hr fun i ↦ ?_
  rw [endpointDist_eq_matEd, sub_val, hfg]
  refine (matEd_sum_le _ _).trans (iSup₂_le fun p _ ↦ ?_)
  rw [fullLabel_eq_sheetLabel, fullLabel_eq_sheetLabel, matEd_sheet hZ]
  exact hR i p

include hZ in
/-- `extM_eq_of_sum` for rescaled families with a uniform endpoint estimate. -/
theorem extM_eq_of_sum_unif {J : ℕ → Type*} [∀ i, Fintype (J i)] (τ : ∀ i, J i → G i)
    (R : GraphFamily J M N) (c : ∀ i, J i → ℚ)
    (hR : Tendsto (fun i ↦ ⨆ p, matEd Z (R i p) (M.label i) (N.label i)) atTop (𝓝 0))
    {f g : M ⟶ N} (hfg : ∀ i, f.1 i - g.1 i = ∑ p, sheet (τ i p) (c i p • R i p)) :
    extM Z f = extM Z g :=
  extM_eq_of_sum hZ τ (fun i p ↦ c i p • R i p) hR
    (fun _ p ↦ (matEd_smul_le _).trans (le_iSup_of_le p le_rfl)) hfg

omit [IsIsometricSMul H X] in
/-- Equations between morphisms of forgotten objects, entrywise. -/
theorem extM_eq_of_forget_entries {f g : forgetObj M ⟶ forgetObj N} {r : ℕ → ℝ≥0∞}
    (hr : Tendsto r atTop (𝓝 0))
    (h : ∀ i x y, (f.1 i - g.1 i) x y ≠ 0 →
      infEDist (N.fullLabel i (forgetCoord N i x)) Z ≤ r i ∧
        infEDist (M.fullLabel i (forgetCoord M i y)) Z ≤ r i) :
    extM Z f = extM Z g := by
  rw [extM_eq_iff]
  refine tendsto_zero_of_le hr fun i ↦ endpointDist_le_iff.mpr fun x y hxy ↦ ?_
  rw [fullLabel_forgetObj, fullLabel_forgetObj]
  exact h i x y hxy

end Uniform

/-! ### Multiplication by a rational sequence -/

section Scalar

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  {π : ∀ i, G i →* H} {X : Type} [MulAction H X] [PseudoEMetricSpace X] (Z : Set X)

/-- Multiplication by the rational sequence `c`. -/
def seqScalar (c : ℕ → ℚ) (M : AsymptoticObject π X) : M ⟶ M :=
  ⟨fun i ↦ c i • (𝟙 M : M ⟶ M).1 i,
    ⟨fun i ↦ ((𝟙 M : M ⟶ M).2.equivariant i).smul _,
      tendsto_zero_of_le (tendsto_propSeq (𝟙 M)) fun _ ↦ prop_smul_le _⟩⟩

@[simp]
theorem seqScalar_val (c : ℕ → ℚ) (M : AsymptoticObject π X) (i : ℕ) :
    (seqScalar c M).1 i = c i • (𝟙 M : M ⟶ M).1 i :=
  rfl

variable {M N : AsymptoticObject π X}

theorem comp_seqScalar_val (c : ℕ → ℚ) (f : M ⟶ N) (i : ℕ) :
    (f ≫ seqScalar c N).1 i = c i • f.1 i := by
  rw [comp_val, seqScalar_val, Matrix.smul_mul, ← comp_val, Category.comp_id]

theorem seqScalar_comm (c : ℕ → ℚ) (f : M ⟶ N) : seqScalar c M ≫ f = f ≫ seqScalar c N :=
  hom_ext fun i ↦ by simp

theorem seqScalar_comp (c c' : ℕ → ℚ) (M : AsymptoticObject π X) :
    seqScalar c M ≫ seqScalar c' M = seqScalar (c * c') M :=
  hom_ext fun i ↦ by simp [smul_smul]

theorem seqScalar_one (M : AsymptoticObject π X) : seqScalar 1 M = 𝟙 M :=
  hom_ext fun i ↦ by simp

theorem transpose_seqScalar (c : ℕ → ℚ) (M : AsymptoticObject π X) :
    AsymptoticObject.transpose (seqScalar c M) = seqScalar c M :=
  hom_ext fun i ↦ by simp

theorem forgetHom_seqScalar (c : ℕ → ℚ) (M : AsymptoticObject π X) :
    forgetHom (seqScalar c M) = seqScalar c (forgetObj M) :=
  hom_ext fun i ↦ by
    have h : (𝟙 (forgetObj M) : forgetObj M ⟶ forgetObj M).1 i = (forgetHom (𝟙 M)).1 i :=
      congrArg (fun f ↦ f.1 i) ((forgetFunctor π X).map_id M).symm
    rw [forgetHom_val, seqScalar_val, seqScalar_val, h, forgetHom_val]
    rfl

/-- Multiplication by a nonvanishing rational sequence as a central self-adjoint automorphism
of `ℬ_Z(X)` (for `c = (|G_i|)_i`, the normalizing scalar `q` of (10.2)). -/
@[simps]
def seqUnit (c : ℕ → ℚ) (hc : ∀ i, c i ≠ 0) : CentralUnit (exteriorInvCat π Z).inv where
  hom A := extM Z (seqScalar c A.as.as)
  inv A := extM Z (seqScalar c⁻¹ A.as.as)
  hom_inv A := by
    erw [extM_comp, seqScalar_comp, show c * c⁻¹ = 1 from funext fun i ↦ mul_inv_cancel₀ (hc i),
      seqScalar_one, extM_id]
    rfl
  inv_hom A := by
    erw [extM_comp, seqScalar_comp, show c⁻¹ * c = 1 from funext fun i ↦ inv_mul_cancel₀ (hc i),
      seqScalar_one, extM_id]
    rfl
  comm φ := by
    obtain ⟨f, rfl⟩ := exists_extM φ
    erw [extM_comp, extM_comp, seqScalar_comm]
  star_hom A := by erw [extM_star, transpose_seqScalar]

end Scalar

/-! ### The sheet `1` of `Res Ind M` -/

section SheetOne

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  {π : ∀ i, G i →* H} {X : Type} [MulAction H X] [PseudoEMetricSpace X]

theorem isEquivariant_unit {m n : ℕ} (u : Matrix (Fin n × Unit) (Fin m × Unit) ℚ) :
    IsEquivariant u := by
  intro x b' b
  rfl

omit [∀ i, Fintype (G i)] in
theorem id_val_scalar_apply (M : AsymptoticObject (scalarHom H) X) (i : ℕ)
    (c b : Fin (M.rank i) × Unit) :
    (𝟙 M : M ⟶ M).1 i c b = (1 : Matrix (Fin (M.rank i)) (Fin (M.rank i)) ℚ) c.1 b.1 := by
  rw [id_val]
  rcases c with ⟨c, ⟨⟩⟩
  rcases b with ⟨b, ⟨⟩⟩
  by_cases h : c = b
  · subst h; simp
  · simp [h]

omit [PseudoEMetricSpace X] in
theorem sum_forgetCoord (M : AsymptoticObject π X) (i : ℕ) {β : Type*} [AddCommMonoid β]
    (F : Fin ((forgetObj M).rank i) × Unit → β) :
    ∑ x, F x = ∑ p, F ((forgetCoord M i).symm p) :=
  Fintype.sum_equiv (forgetCoord M i) _ _ fun x ↦ by simp

variable (π) in
open scoped Classical in
/-- The matrix of the inclusion of the sheet `1` of `Res Ind M`. -/
def sheetInclMat (M : AsymptoticObject (scalarHom H) X) (i : ℕ) :
    Matrix (Fin ((forgetObj (freeSheetObj π M)).rank i) × Unit) (Fin (M.rank i) × Unit) ℚ :=
  Matrix.of fun x a ↦ if forgetCoord (freeSheetObj π M) i x = (a.1, 1) then 1 else 0

omit [PseudoEMetricSpace X] in
theorem mul_sheetInclMat (M : AsymptoticObject (scalarHom H) X) (i : ℕ) {β : Type*} [Fintype β]
    (B : Matrix β (Fin ((forgetObj (freeSheetObj π M)).rank i) × Unit) ℚ) (y : β)
    (a : Fin (M.rank i) × Unit) :
    (B * sheetInclMat π M i) y a = B y ((forgetCoord (freeSheetObj π M) i).symm (a.1, 1)) := by
  classical
  rw [Matrix.mul_apply, sum_forgetCoord]
  simp [sheetInclMat]

omit [PseudoEMetricSpace X] in
theorem sheetInclMat_transpose_mul (M : AsymptoticObject (scalarHom H) X) (i : ℕ) {β : Type*}
    [Fintype β] (B : Matrix (Fin ((forgetObj (freeSheetObj π M)).rank i) × Unit) β ℚ) (y : β)
    (a : Fin (M.rank i) × Unit) :
    ((sheetInclMat π M i)ᵀ * B) a y = B ((forgetCoord (freeSheetObj π M) i).symm (a.1, 1)) y := by
  classical
  rw [Matrix.mul_apply, sum_forgetCoord]
  simp [sheetInclMat]

variable (π) in
/-- The inclusion of the sheet `1`, `M → Res Ind M`: the unit of `Ind ⊣ Res`. -/
def sheetIncl (M : AsymptoticObject (scalarHom H) X) : M ⟶ forgetObj (freeSheetObj π M) :=
  ⟨sheetInclMat π M, ⟨fun _ ↦ isEquivariant_unit _, tendsto_zero_of_forall_eq_zero fun i ↦
    le_antisymm (prop_le_iff.mpr fun x a hxa ↦ by
      have hx : forgetCoord (freeSheetObj π M) i x = (a.1, 1) := by
        by_contra h
        simp [sheetInclMat, h] at hxa
      rw [fullLabel_forgetObj, hx]
      simp [fullLabel, freeSheetObj]) bot_le⟩⟩

variable (π) in
/-- The projection onto the sheet `1`, `Res Ind M → M`. -/
def sheetProj (M : AsymptoticObject (scalarHom H) X) : forgetObj (freeSheetObj π M) ⟶ M :=
  AsymptoticObject.transpose (sheetIncl π M)

@[simp]
theorem sheetIncl_val (M : AsymptoticObject (scalarHom H) X) (i : ℕ) :
    (sheetIncl π M).1 i = sheetInclMat π M i :=
  rfl

@[simp]
theorem sheetProj_val (M : AsymptoticObject (scalarHom H) X) (i : ℕ) :
    (sheetProj π M).1 i = (sheetInclMat π M i)ᵀ :=
  rfl

theorem sheetIncl_comp_sheetProj (M : AsymptoticObject (scalarHom H) X) :
    sheetIncl π M ≫ sheetProj π M = 𝟙 M :=
  hom_ext fun i ↦ by
    classical
    ext a' a
    rw [comp_val, sheetIncl_val, sheetProj_val, sheetInclMat_transpose_mul]
    simp only [sheetInclMat, Matrix.of_apply, Equiv.apply_symm_apply, Prod.mk.injEq, and_true,
      id_val, Matrix.one_apply]
    rcases a' with ⟨a', ⟨⟩⟩
    rcases a with ⟨a, ⟨⟩⟩
    by_cases h : a' = a <;> simp [h]

theorem transpose_sheetProj (M : AsymptoticObject (scalarHom H) X) :
    AsymptoticObject.transpose (sheetProj π M) = sheetIncl π M :=
  AsymptoticObject.transpose_transpose _

variable [IsIsometricSMul H X]

/-- Naturality of the inclusion of the sheet `1`. -/
theorem sheetIncl_naturality {M N : AsymptoticObject (scalarHom H) X} (f : M ⟶ N) :
    sheetIncl π M ≫ forgetHom ((AsymptoticObject.freeSheet π).map f) = f ≫ sheetIncl π N :=
  hom_ext fun i ↦ by
    classical
    ext y ⟨a, ⟨⟩⟩
    erw [comp_val, comp_val, sheetIncl_val, sheetIncl_val, mul_sheetInclMat, forgetHom_val,
      Matrix.submatrix_apply, Equiv.apply_symm_apply, freeSheet_map, sheetHom_val,
      Matrix.mul_apply]
    obtain ⟨⟨k, s⟩, hy⟩ : ∃ p, forgetCoord (freeSheetObj π N) i y = p := ⟨_, rfl⟩
    have hy' : forgetCoord ((AsymptoticObject.freeSheet π).obj N) i y = (k, s) := hy
    rw [hy', Fintype.sum_prod_type]
    simp only [sheetInclMat, Matrix.of_apply, hy, sheet_apply, Pi.one_apply, mul_one,
      scalarMatrix, Prod.mk.injEq]
    by_cases hs : s = 1
    · subst hs; simp
    · simp [hs, Ne.symm hs]

/-- Naturality of the projection onto the sheet `1`. -/
theorem sheetProj_naturality {M N : AsymptoticObject (scalarHom H) X} (f : M ⟶ N) :
    forgetHom ((AsymptoticObject.freeSheet π).map f) ≫ sheetProj π N = sheetProj π M ≫ f := by
  have h := congrArg AsymptoticObject.transpose (sheetIncl_naturality (π := π)
    (AsymptoticObject.transpose f))
  erw [AsymptoticObject.transpose_comp, AsymptoticObject.transpose_comp,
    AsymptoticObject.transpose_transpose, ← forgetHom_transpose,
    ← AsymptoticObject.freeSheet_map_transpose, AsymptoticObject.transpose_transpose] at h
  exact h

/-- The `(1, 1)` block of a shifted sum of type `id` is the family at `1` (manuscript (5.3)). -/
theorem sheetIncl_graphSum_sheetProj {M N : AsymptoticObject (scalarHom H) X}
    (a : GraphFamily G (freeSheetObj π M) (freeSheetObj π N))
    (ha : HasGraphType (fun _ ↦ id) a) (i : ℕ) :
    (sheetIncl π M ≫ forgetHom (graphSum _ a ha) ≫ sheetProj π N).1 i =
      Matrix.of fun c b ↦ a i 1 c.1 b.1 := by
  ext c b
  rw [comp_val, comp_val, sheetProj_val, sheetIncl_val, mul_sheetInclMat,
    sheetInclMat_transpose_mul, forgetHom_val, Matrix.submatrix_apply, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply, graphSum_id_apply]
  simp

end SheetOne

/-! ### Block matrices on `Res Ind M` -/

section Blocks

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  {π : ∀ i, G i →* H} {X : Type} [MulAction H X] [PseudoEMetricSpace X]

/-- The matrix of `Res` with the block `b s' s` from the sheet `s` to the sheet `s'`. -/
def blockMat {M N : AsymptoticObject π X} (b : ∀ i, G i → G i → Matrix (Fin (N.rank i)) (Fin (M.rank i)) ℚ)
    (i : ℕ) : Matrix (Fin ((forgetObj N).rank i) × Unit) (Fin ((forgetObj M).rank i) × Unit) ℚ :=
  Matrix.of fun x y ↦ b i (forgetCoord N i x).2 (forgetCoord M i y).2 (forgetCoord N i x).1
    (forgetCoord M i y).1

variable {M N P : AsymptoticObject π X}

omit [PseudoEMetricSpace X] in
@[simp]
theorem blockMat_apply (b : ∀ i, G i → G i → Matrix (Fin (N.rank i)) (Fin (M.rank i)) ℚ) (i : ℕ)
    (x y) : blockMat b i x y = b i (forgetCoord N i x).2 (forgetCoord M i y).2
      (forgetCoord N i x).1 (forgetCoord M i y).1 :=
  rfl

omit [PseudoEMetricSpace X] in
theorem blockMat_add (b b' : ∀ i, G i → G i → Matrix (Fin (N.rank i)) (Fin (M.rank i)) ℚ)
    (i : ℕ) : blockMat b i + blockMat b' i = blockMat (fun i s' s ↦ b i s' s + b' i s' s) i := by
  ext; simp

omit [PseudoEMetricSpace X] in
theorem blockMat_sub (b b' : ∀ i, G i → G i → Matrix (Fin (N.rank i)) (Fin (M.rank i)) ℚ)
    (i : ℕ) : blockMat b i - blockMat b' i = blockMat (fun i s' s ↦ b i s' s - b' i s' s) i := by
  ext; simp

/-- `Res` of a shifted sum of type `id` is the block matrix `(s', s) ↦ a_{s'⁻¹ s}` (5.3). -/
theorem forgetHom_graphSum [IsIsometricSMul H X] (a : GraphFamily G M N)
    (ha : HasGraphType (fun _ ↦ id) a) (i : ℕ) :
    (forgetHom (graphSum _ a ha)).1 i = blockMat (fun i s' s ↦ a i (s'⁻¹ * s)) i := by
  ext x y
  rw [forgetHom_val, Matrix.submatrix_apply, graphSum_id_apply, blockMat_apply]

omit [∀ i, Fintype (G i)] in
theorem edist_fullLabel_le [IsIsometricSMul H X] {M N : AsymptoticObject π X} (i : ℕ)
    (x : Fin (N.rank i) × G i) (y : Fin (M.rank i) × G i) (u : Matrix (Fin (N.rank i)) (Fin (M.rank i)) ℚ)
    (h : u x.1 y.1 ≠ 0) :
    edist (N.fullLabel i x) (M.fullLabel i y) ≤
      graphProp (π i (x.2⁻¹ * y.2)) u (M.label i) (N.label i) := by
  have e : M.fullLabel i y = π i x.2 • (π i (x.2⁻¹ * y.2) • M.label i y.1) := by
    rw [smul_smul, ← map_mul, mul_inv_cancel_left]; rfl
  rw [e, fullLabel, edist_smul_left]
  exact edist_le_graphProp h

/-- A uniform family of types `(g, h) ↦ gh`, placed in the block `(g⁻¹, h)`, is controlled after
forgetting the action (the homotopy of (5.6), `vu ≃ E`). -/
theorem isControlled_blockMat [IsIsometricSMul H X] (b : GraphFamily (fun i ↦ G i × G i) M N)
    (hb : HasGraphType (fun _ p ↦ p.1 * p.2) b) (c : ℕ → ℚ) :
    IsControlled (forgetObj M) (forgetObj N)
      (blockMat (M := M) (N := N) fun i s' s ↦ c i • b i (s'⁻¹, s)) := by
  refine ⟨fun _ ↦ isEquivariant_unit _, tendsto_zero_of_le hb fun i ↦ prop_le_iff.mpr ?_⟩
  intro x y hxy
  have hb' : b i ((forgetCoord N i x).2⁻¹, (forgetCoord M i y).2) (forgetCoord N i x).1
      (forgetCoord M i y).1 ≠ 0 := by
    rw [blockMat_apply, Matrix.smul_apply, smul_eq_mul] at hxy
    exact right_ne_zero_of_mul hxy
  rw [fullLabel_forgetObj, fullLabel_forgetObj]
  exact (edist_fullLabel_le i _ _ _ hb').trans
    (graphProp_le_graphPropSeq (fun _ p ↦ p.1 * p.2) b i
      ((forgetCoord N i x).2⁻¹, (forgetCoord M i y).2))

/-- The block morphism of `isControlled_blockMat`. -/
def blockHom [IsIsometricSMul H X] (b : GraphFamily (fun i ↦ G i × G i) M N)
    (hb : HasGraphType (fun _ p ↦ p.1 * p.2) b) (c : ℕ → ℚ) : forgetObj M ⟶ forgetObj N :=
  ⟨blockMat (M := M) (N := N) fun i s' s ↦ c i • b i (s'⁻¹, s), isControlled_blockMat b hb c⟩

variable {M₀ N₀ P₀ : AsymptoticObject (scalarHom H) X} [IsIsometricSMul H X]

theorem blockMat_mul_freeSheet
    (b : ∀ i, G i → G i →
      Matrix (Fin ((freeSheetObj π P₀).rank i)) (Fin ((freeSheetObj π N₀).rank i)) ℚ)
    (f : M₀ ⟶ N₀) (i : ℕ) :
    blockMat (M := freeSheetObj π N₀) (N := freeSheetObj π P₀) b i *
        (forgetHom (sheetHom 1 (scalarMatrix π f.1) (isGraphType_scalarMatrix f))).1 i =
      blockMat (M := freeSheetObj π M₀) (N := freeSheetObj π P₀)
        (fun i s' s ↦ b i s' s * scalarMatrix π f.1 i) i := by
  classical
  ext x y
  rw [Matrix.mul_apply, sum_forgetCoord, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [blockMat_apply, Equiv.apply_symm_apply, forgetHom_val, Matrix.submatrix_apply,
    sheetHom_val, Pi.one_apply, sheet_apply, mul_one, mul_ite, mul_zero]
  rw [Finset.sum_eq_single (forgetCoord (freeSheetObj π M₀) i y).2]
  · simp [Matrix.mul_apply]
  · intro t _ ht
    exact Finset.sum_eq_zero fun k _ ↦ ite_eq_right (Ne.symm ht)
  · simp

theorem freeSheet_mul_blockMat
    (b : ∀ i, G i → G i →
      Matrix (Fin ((freeSheetObj π N₀).rank i)) (Fin ((freeSheetObj π M₀).rank i)) ℚ)
    (f : N₀ ⟶ P₀) (i : ℕ) :
    (forgetHom (sheetHom 1 (scalarMatrix π f.1) (isGraphType_scalarMatrix f))).1 i *
        blockMat (M := freeSheetObj π M₀) (N := freeSheetObj π N₀) b i =
      blockMat (M := freeSheetObj π M₀) (N := freeSheetObj π P₀)
        (fun i s' s ↦ scalarMatrix π f.1 i * b i s' s) i := by
  classical
  ext x y
  rw [Matrix.mul_apply, sum_forgetCoord, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [blockMat_apply, Equiv.apply_symm_apply, forgetHom_val, Matrix.submatrix_apply,
    sheetHom_val, Pi.one_apply, sheet_apply, mul_one, ite_mul, zero_mul]
  rw [Finset.sum_eq_single (forgetCoord (freeSheetObj π P₀) i x).2]
  · simp [Matrix.mul_apply]
  · intro t _ ht
    exact Finset.sum_eq_zero fun k _ ↦ ite_eq_right ht
  · simp

/-- The composite `Res(b) ε c η Res(a)` through the sheet `1`: block `(s', s)` is
`c b_{s'⁻¹} a_s` (manuscript (5.6), `vu`). -/
theorem forgetHom_sheetOne_comp
    (a : GraphFamily G (freeSheetObj π M₀) (freeSheetObj π N₀))
    (ha : HasGraphType (fun _ ↦ id) a)
    (b : GraphFamily G (freeSheetObj π N₀) (freeSheetObj π P₀))
    (hb : HasGraphType (fun _ ↦ id) b) (c : ℕ → ℚ) (i : ℕ) :
    (forgetHom (graphSum _ a ha) ≫ sheetProj π N₀ ≫ seqScalar c N₀ ≫ sheetIncl π N₀ ≫
        forgetHom (graphSum _ b hb)).1 i =
      blockMat (fun i s' s ↦ c i • (b i s'⁻¹ * a i s)) i := by
  ext x y
  simp only [← Category.assoc]
  rw [comp_val, comp_val, comp_seqScalar_val, comp_val, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.smul_apply, sheetProj_val, sheetIncl_val, ← Matrix.mul_assoc, Matrix.mul_apply,
    Fintype.sum_prod_type]
  have key : ∀ (p : Fin (N₀.rank i) × Unit),
      ((forgetHom (graphSum _ b hb)).1 i * sheetInclMat π N₀ i) x p =
        (forgetHom (graphSum _ b hb)).1 i x ((forgetCoord (freeSheetObj π N₀) i).symm (p.1, 1)) :=
    fun p ↦ mul_sheetInclMat N₀ i _ x p
  have key' : ∀ (p : Fin (N₀.rank i) × Unit),
      ((sheetInclMat π N₀ i)ᵀ * (forgetHom (graphSum _ a ha)).1 i) p y =
        (forgetHom (graphSum _ a ha)).1 i ((forgetCoord (freeSheetObj π N₀) i).symm (p.1, 1)) y :=
    fun p ↦ sheetInclMat_transpose_mul N₀ i _ y p
  simp only [key, key']
  simp only [forgetHom_graphSum, blockMat_apply,
    Equiv.apply_symm_apply, Finset.univ_unique, Finset.sum_singleton, mul_one, inv_one, one_mul,
    smul_eq_mul, Matrix.mul_apply, Matrix.smul_apply]
  rfl

end Blocks

/-! ### The sheet `1` in the exterior categories -/

section SheetOneExterior

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  (π : ∀ i, G i →* H) {X : Type} [MulAction H X] [PseudoEMetricSpace X] [IsIsometricSMul H X]
  {Z : Set X} (hZ : ∀ h : H, h • Z = Z)

/-- Free sheets `Ind : ℬ_{1,Z}(X) → ℬ_{G,Z}(X)`. -/
abbrev indQ : exteriorInvCat (scalarHom H) Z ⟶ exteriorInvCat π Z :=
  (freeSheetFiltrationHom (π := π) hZ).quot

/-- Forgetting the action `Res : ℬ_{G,Z}(X) → ℬ_{1,Z}(X)`. -/
abbrev resQ : exteriorInvCat π Z ⟶ exteriorInvCat (scalarHom H) Z :=
  (forgetFiltrationHom π Z).quot

/-- The inclusion of the sheet `1`, `A → Res Ind A`, in `ℬ_{1,Z}(X)`. -/
def sheetInclE (A : exteriorInvCat (scalarHom H) Z) :
    A ⟶ (resQ π).F.obj ((indQ π hZ).F.obj A) :=
  extM Z (sheetIncl π A.as.as)

/-- The projection onto the sheet `1`, `Res Ind A → A`, in `ℬ_{1,Z}(X)`. -/
def sheetProjE (A : exteriorInvCat (scalarHom H) Z) :
    (resQ π).F.obj ((indQ π hZ).F.obj A) ⟶ A :=
  extM Z (sheetProj π A.as.as)

variable {π hZ}

@[reassoc]
theorem sheetInclE_naturality {A B : exteriorInvCat (scalarHom H) Z} (φ : A ⟶ B) :
    sheetInclE π hZ A ≫ (resQ π).F.map ((indQ π hZ).F.map φ) = φ ≫ sheetInclE π hZ B := by
  obtain ⟨f, rfl⟩ := exists_extM φ
  exact (extM_comp _ _).trans ((congrArg (extM Z) (sheetIncl_naturality f)).trans
    (extM_comp _ _).symm)

@[reassoc]
theorem sheetProjE_naturality {A B : exteriorInvCat (scalarHom H) Z} (φ : A ⟶ B) :
    (resQ π).F.map ((indQ π hZ).F.map φ) ≫ sheetProjE π hZ B = sheetProjE π hZ A ≫ φ := by
  obtain ⟨f, rfl⟩ := exists_extM φ
  exact (extM_comp _ _).trans ((congrArg (extM Z) (sheetProj_naturality f)).trans
    (extM_comp _ _).symm)

@[reassoc (attr := simp)]
theorem sheetInclE_comp_sheetProjE (A : exteriorInvCat (scalarHom H) Z) :
    sheetInclE π hZ A ≫ sheetProjE π hZ A = 𝟙 A := by
  erw [sheetInclE, sheetProjE, extM_comp, sheetIncl_comp_sheetProj, extM_id]
  rfl

theorem star_sheetProjE (A : exteriorInvCat (scalarHom H) Z) :
    (exteriorInvCat (scalarHom H) Z).inv.star (sheetProjE π hZ A) = sheetInclE π hZ A := by
  erw [sheetProjE, extM_star, transpose_sheetProj]
  rfl

variable (π hZ)

/-- The inclusion of the sheet `1` of a chain complex, `C → Res Ind C`. -/
@[simps]
def sheetInclC (C : ChainComplex (exteriorInvCat (scalarHom H) Z) ℤ) :
    C ⟶ (resQ π).mapC ((indQ π hZ).mapC C) where
  f r := sheetInclE π hZ (C.X r)
  comm' r r' _ := sheetInclE_naturality (C.d r r')

/-- The projection onto the sheet `1` of a chain complex, `Res Ind C → C`. -/
@[simps]
def sheetProjC (C : ChainComplex (exteriorInvCat (scalarHom H) Z) ℤ) :
    (resQ π).mapC ((indQ π hZ).mapC C) ⟶ C where
  f r := sheetProjE π hZ (C.X r)
  comm' r r' _ := (sheetProjE_naturality (C.d r r')).symm

variable {π hZ}

@[reassoc (attr := simp)]
theorem sheetInclC_comp_sheetProjC (C : ChainComplex (exteriorInvCat (scalarHom H) Z) ℤ) :
    sheetInclC π hZ C ≫ sheetProjC π hZ C = 𝟙 C := by
  ext r
  simp

/-- The form of `Res Ind C` restricted to the sheet `1`: `ε^* Φ = φ η`. -/
theorem dualHom_sheetProjC_comp {C : ChainComplex (exteriorInvCat (scalarHom H) Z) ℤ} {N : ℤ}
    (φ : dualComplex (exteriorInvCat (scalarHom H) Z).inv N C ⟶ C) :
    dualHom _ N (sheetProjC π hZ C) ≫ (resQ π).mapDual ((indQ π hZ).mapDual φ) =
      φ ≫ sheetInclC π hZ C := by
  ext r
  simp only [HomologicalComplex.comp_f, dualHom_f, sheetProjC_f, InvFunctor.mapDual_f,
    sheetInclC_f]
  exact sheetInclE_naturality (φ.f r)

end SheetOneExterior

end HSFormal
