import HSFormal.AsymptoticRelabel
import HSFormal.LTheory.Isometry
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# The functor `τ ⊗ −` and local tensor triviality (manuscript §6, Lemma 6.1)

For a finite set `Q` with an action `ρ : H →* Equiv.Perm Q`, `tensor ρ` is `ℚ[Q] ⊗ −` on
`𝒜_G(X)`: the basis `Q × B_i` with diagonal action (`G i` acting on `Q` through `π i`), each
basis vector keeping the label of its `B_i`-factor, and the orthonormal form on `ℚ[Q]`
(l.400–413).  Free orbits of the diagonal action are indexed by `Fin (rank i) × Q`.  The
manuscript's `τ_i = ℚ[G_i/P_i] = ℚ[C_p]` is `ρ = MulAction.toPermHom H H` (`H = C_p`, `π i`
with kernel `P_i`); the `|H|`-fold sum of the identity is the trivial action `ρ = 1`.

These are strictly duality-preserving `ℚ`-linear functors on `𝒜_G(X)`, on the support
categories `𝒜_S(X)`, on the exterior quotients `ℬ_Z(X)` and on `𝒜_A/𝒜_Y`; they commute with
the quotient, inclusion, excision (Lemma 2.2) and relabeling (Lemma 2.4) functors.  The
summand inclusions `A → ℚ[Q]^{triv} ⊗ A` are natural, unitary, and form a biproduct.

**Lemma 6.1** (`localTriv`, `exists_unitary_localTriv`): if `S` lies in a compact subset of
the lift `W` of a trivializing open set of `X/H` (a sheet function `c`, locally constant on
`W` with `c (h • x) = h * c x`), then on `𝒜_S(X)` the map (6.2) `e_b ⊗ m_x ↦ m_x` in copy
`c(x)⁻¹ b` is a natural isomorphism `τ ⊗ − ≅ ⨁_H 𝟭` whose inverse is its transpose.
-/

noncomputable section

namespace HSFormal

open Filter Matrix CategoryTheory CategoryTheory.Limits Metric
open scoped Classical ENNReal Topology Kronecker Pointwise

universe u

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)]
  {π : ∀ i, G i →* H} {X : Type u} [MulAction H X] [PseudoEMetricSpace X]

variable (Q : Type*) [Fintype Q]

/-- Orbit representatives of the tensor basis: `Fin n × Q ≃ Fin (n * |Q|)`. -/
def tensorIdx (n : ℕ) : Fin n × Q ≃ Fin (n * Fintype.card Q) :=
  (Equiv.prodCongr (Equiv.refl _) (Fintype.equivFin Q)).trans finProdFinEquiv

namespace AsymptoticObject

/-- `ℚ[Q] ⊗ M`: the orbit `(k, q)` carries the label of `k` (l.406, l.413). -/
@[reducible]
def tensorObj (M : AsymptoticObject π X) : AsymptoticObject π X where
  rank i := M.rank i * Fintype.card Q
  label i r := M.label i ((tensorIdx Q (M.rank i)).symm r).1

variable {Q} (ρ : H →* Equiv.Perm Q)

/-- The basis vector `(r, g)`, `r = (k, q)`, of `ℚ[Q] ⊗ M` is
`g • (e_q ⊗ m_k) = e_{ρ(π g) q} ⊗ m_{(k, g)}`. -/
def tensorCoord (M : AsymptoticObject π X) (i : ℕ) :
    Fin ((M.tensorObj Q).rank i) × G i ≃ Q × (Fin (M.rank i) × G i) where
  toFun b := (ρ (π i b.2) ((tensorIdx Q (M.rank i)).symm b.1).2,
    ((tensorIdx Q (M.rank i)).symm b.1).1, b.2)
  invFun a := (tensorIdx Q (M.rank i) (a.2.1, (ρ (π i a.2.2)).symm a.1), a.2.2)
  left_inv b := by simp
  right_inv a := by simp

omit [PseudoEMetricSpace X] in
theorem fullLabel_tensorObj (M : AsymptoticObject π X) (i : ℕ)
    (b : Fin ((M.tensorObj Q).rank i) × G i) :
    (M.tensorObj Q).fullLabel i b = M.fullLabel i (tensorCoord ρ M i b).2 := rfl

variable {M N P : AsymptoticObject π X}

/-- `1_{ℚ[Q]} ⊗ u` in the tensor basis. -/
def tensorMatrix (u : Family M N) : Family (M.tensorObj Q) (N.tensorObj Q) :=
  fun i ↦ ((1 : Matrix Q Q ℚ) ⊗ₖ u i).submatrix (tensorCoord ρ N i) (tensorCoord ρ M i)

omit [MulAction H X] [PseudoEMetricSpace X] in
theorem tensorMatrix_apply (u : Family M N) (i : ℕ) (b' b) :
    tensorMatrix ρ u i b' b = if (tensorCoord ρ N i b').1 = (tensorCoord ρ M i b).1 then
      u i (tensorCoord ρ N i b').2 (tensorCoord ρ M i b).2 else 0 := by
  simp [tensorMatrix, one_apply]

omit [MulAction H X] [PseudoEMetricSpace X] in
theorem isEquivariant_tensorMatrix {u : Family M N} (hu : ∀ i, IsEquivariant (u i)) (i : ℕ) :
    IsEquivariant (tensorMatrix ρ u i) := by
  intro g b' b
  simp only [tensorMatrix_apply, tensorCoord, Equiv.coe_fn_mk, map_mul, Equiv.Perm.coe_mul,
    Function.comp_apply, (ρ (π i g)).injective.eq_iff]
  rw [hu i g (((tensorIdx Q (N.rank i)).symm b'.1).1, b'.2)
    (((tensorIdx Q (M.rank i)).symm b.1).1, b.2)]
  exact if_congr Iff.rfl rfl rfl

theorem propSeq_tensorMatrix_le (u : Family M N) (i : ℕ) :
    propSeq (M.tensorObj Q) (N.tensorObj Q) (tensorMatrix ρ u) i ≤ propSeq M N u i := by
  refine prop_le_iff.mpr fun b' b h ↦ ?_
  rw [tensorMatrix_apply] at h
  split_ifs at h with h'
  · rw [fullLabel_tensorObj ρ, fullLabel_tensorObj ρ]
    exact edist_le_prop h
  · exact (h rfl).elim

variable [∀ i, Fintype (G i)]

omit [MulAction H X] [PseudoEMetricSpace X] in
theorem tensorMatrix_mul (u : Family M N) (w : Family N P) (i : ℕ) :
    tensorMatrix ρ (fun i ↦ w i * u i) i = tensorMatrix ρ w i * tensorMatrix ρ u i := by
  simp only [tensorMatrix, submatrix_mul_equiv, ← mul_kronecker_mul, one_mul]

omit [MulAction H X] [PseudoEMetricSpace X] [∀ i, Fintype (G i)] in
theorem tensorMatrix_one (i : ℕ) : tensorMatrix ρ (fun _ ↦ 1 : Family M M) i = 1 := by
  simp only [tensorMatrix, one_kronecker_one, submatrix_one_equiv]

omit [MulAction H X] [PseudoEMetricSpace X] [∀ i, Fintype (G i)] in
theorem tensorMatrix_transpose (u : Family M N) (i : ℕ) :
    (tensorMatrix ρ u i)ᵀ = tensorMatrix ρ (fun i ↦ (u i)ᵀ) i := by
  simp only [tensorMatrix, transpose_submatrix, ← kroneckerMap_transpose, transpose_one]

omit [MulAction H X] [PseudoEMetricSpace X] [∀ i, Fintype (G i)] in
theorem tensorMatrix_add (u v : Family M N) (i : ℕ) :
    tensorMatrix ρ (u + v) i = tensorMatrix ρ u i + tensorMatrix ρ v i := by
  ext b' b
  simp only [tensorMatrix_apply, Pi.add_apply, Matrix.add_apply]
  split_ifs <;> simp

omit [MulAction H X] [PseudoEMetricSpace X] [∀ i, Fintype (G i)] in
theorem tensorMatrix_smul (c : ℚ) (u : Family M N) (i : ℕ) :
    tensorMatrix ρ (c • u) i = c • tensorMatrix ρ u i := by
  ext b' b
  simp only [tensorMatrix_apply, Pi.smul_apply, Matrix.smul_apply]
  split_ifs <;> simp

/-- `1 ⊗ f`; its propagation is at most that of `f`. -/
def tensorHom (f : M ⟶ N) : M.tensorObj Q ⟶ N.tensorObj Q :=
  ⟨tensorMatrix ρ f.1, (⟨isEquivariant_tensorMatrix ρ (equivariant f),
    tendsto_zero_of_le (tendsto_propSeq f) (propSeq_tensorMatrix_le ρ f.1)⟩ :
      IsControlled (M.tensorObj Q) (N.tensorObj Q) (tensorMatrix ρ f.1))⟩

@[simp]
theorem tensorHom_val (f : M ⟶ N) (i : ℕ) : (tensorHom ρ f).1 i = tensorMatrix ρ f.1 i := rfl

variable (Q) in
/-- `ℚ[Q] ⊗ −` on controlled families. -/
@[simps obj]
def tensorFunctor : AsymptoticObject π X ⥤ AsymptoticObject π X where
  obj := tensorObj Q
  map := tensorHom ρ
  map_id _ := hom_ext fun i ↦ tensorMatrix_one ρ i
  map_comp f g := hom_ext fun i ↦ tensorMatrix_mul ρ f.1 g.1 i

theorem tensorFunctor_map (f : M ⟶ N) : (tensorFunctor Q ρ).map f = tensorHom ρ f := rfl

theorem tensorHom_transpose (f : M ⟶ N) :
    tensorHom ρ (transpose f) = transpose (tensorHom ρ f) :=
  hom_ext fun i ↦ (tensorMatrix_transpose ρ f.1 i).symm

theorem tensorHom_add (f g : M ⟶ N) : tensorHom ρ (f + g) = tensorHom ρ f + tensorHom ρ g :=
  hom_ext fun i ↦ tensorMatrix_add ρ f.1 g.1 i

theorem tensorHom_smul (c : ℚ) (f : M ⟶ N) : tensorHom ρ (c • f) = c • tensorHom ρ f :=
  hom_ext fun i ↦ tensorMatrix_smul ρ c f.1 i

omit [∀ i, Fintype (G i)] in
theorem supportDist_tensorObj_le (S : Set X) (M : AsymptoticObject π X) (i : ℕ) :
    (M.tensorObj Q).supportDist S i ≤ M.supportDist S i :=
  iSup_le fun b ↦ by
    rw [fullLabel_tensorObj (1 : H →* Equiv.Perm Q)]
    exact infEDist_le_supportDist i _

omit [∀ i, Fintype (G i)] in
theorem IsSupported.tensorObj {S : Set X} (hM : M.IsSupported S) :
    (M.tensorObj Q).IsSupported S :=
  tendsto_zero_of_le hM (supportDist_tensorObj_le S M)

end AsymptoticObject

open AsymptoticObject Compression LTheory

variable [∀ i, Fintype (G i)] {Q} (ρ : H →* Equiv.Perm Q)

namespace AsymptoticCategory

variable (π X) in
/-- The transpose duality of `𝒜_G(X)` (§2: same labelled basis, transpose matrix). -/
@[implicit_reducible] def involution : StrictInvolution (AsymptoticCategory π X) where
  star := transpose
  star_comp := transpose_comp
  star_id := transpose_id
  star_add := transpose_add
  star_star := transpose_transpose

@[simp] theorem involution_star {A B : AsymptoticCategory π X} (φ : A ⟶ B) :
    (involution π X).star φ = transpose φ := rfl

/-- `ℚ[Q] ⊗ −` on `𝒜_G(X)`. -/
def tensor : AsymptoticCategory π X ⥤ AsymptoticCategory π X :=
  CategoryTheory.Quotient.lift _ (tensorFunctor Q ρ ⋙ functor) fun _ _ f g h ↦
    (functor_map_eq_iff _ _).mpr <| h.mono fun i hi ↦ by
      change tensorMatrix ρ f.1 i = tensorMatrix ρ g.1 i
      simp only [tensorMatrix, hi]

theorem tensor_obj (A : AsymptoticCategory π X) :
    (tensor ρ).obj A = functor.obj (A.as.tensorObj Q) := rfl

theorem tensor_map_functor_map {M N : AsymptoticObject π X} (f : M ⟶ N) :
    (tensor ρ).map (functor.map f) = functor.map (tensorHom ρ f) := rfl

theorem functor_comp_tensor :
    functor ⋙ tensor ρ = tensorFunctor Q ρ ⋙ functor (π := π) (X := X) :=
  CategoryTheory.Quotient.lift_spec _ _ _

instance tensor_additive : (tensor (π := π) (X := X) ρ).Additive where
  map_add {A B φ ψ} := by
    obtain ⟨f, rfl⟩ := exists_rep φ
    obtain ⟨g, rfl⟩ := exists_rep ψ
    rw [← Functor.map_add, tensor_map_functor_map, tensor_map_functor_map,
      tensor_map_functor_map, tensorHom_add, Functor.map_add]
    rfl

instance tensor_linear : (tensor (π := π) (X := X) ρ).Linear ℚ where
  map_smul {A B} φ c := by
    obtain ⟨f, rfl⟩ := exists_rep φ
    rw [← Functor.map_smul, tensor_map_functor_map, tensor_map_functor_map, tensorHom_smul,
      Functor.map_smul]
    rfl

/-- `τ ⊗ −` is strictly duality-preserving (orthonormal form on `ℚ[Q]`, l.413). -/
theorem tensor_map_transpose {A B : AsymptoticCategory π X} (φ : A ⟶ B) :
    (tensor ρ).map (transpose φ) = transpose ((tensor ρ).map φ) := by
  obtain ⟨f, rfl⟩ := exists_rep φ
  rw [transpose_map, tensor_map_functor_map, tensor_map_functor_map]
  erw [transpose_map]
  rw [tensorHom_transpose]

/-- `ℚ[Q] ⊗ −` as a duality-preserving functor. -/
def tensorInv : InvFunctor (involution π X) (involution π X) where
  F := tensor ρ
  map_star := tensor_map_transpose ρ

/-! ### Support categories `𝒜_S(X)` -/

variable (S : Set X)

variable (π) in
/-- The transpose duality of `𝒜_S(X)`. -/
def supportInvolution : StrictInvolution (SupportCategory π S) where
  star f := ObjectProperty.homMk (transpose f.hom)
  star_comp _ _ := by ext1; exact transpose_comp _ _
  star_id _ := by ext1; exact transpose_id _
  star_add _ _ := by ext1; exact transpose_add _ _
  star_star _ := by ext1; exact transpose_transpose _

@[simp] theorem supportInvolution_star_hom {A B : SupportCategory π S} (f : A ⟶ B) :
    ((supportInvolution π S).star f).hom = transpose f.hom := rfl

/-- `ℚ[Q] ⊗ −` on `𝒜_S(X)`: labels are unchanged, so supports are preserved. -/
def supportTensor : SupportCategory π S ⥤ SupportCategory π S :=
  (supportProperty S).lift ((supportProperty S).ι ⋙ tensor ρ) fun A ↦
    IsSupported.tensorObj A.property

@[simp] theorem supportTensor_map_hom {A B : SupportCategory π S} (f : A ⟶ B) :
    ((supportTensor ρ S).map f).hom = (tensor ρ).map f.hom := rfl

instance supportTensor_additive : (supportTensor (π := π) ρ S).Additive where
  map_add := by intros; ext1; exact (tensor ρ).map_add

instance supportTensor_linear : (supportTensor (π := π) ρ S).Linear ℚ where
  map_smul _ _ := by ext1; exact (tensor ρ).map_smul _ _

/-- `ℚ[Q] ⊗ −` on `𝒜_S(X)` as a duality-preserving functor. -/
def supportTensorInv : InvFunctor (supportInvolution π S) (supportInvolution π S) where
  F := supportTensor ρ S
  map_star f := by ext1; exact tensor_map_transpose ρ f.hom

/-- `τ ⊗ −` commutes with the inclusion `𝒜_S(X) ⊂ 𝒜(X)`. -/
theorem supportTensor_comp_ι :
    supportTensor ρ S ⋙ (supportProperty (π := π) S).ι =
      (supportProperty S).ι ⋙ tensor ρ :=
  CategoryTheory.Functor.ext (fun _ ↦ rfl) fun _ _ _ ↦ by
    erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]; rfl

/-! ### Exterior quotients `ℬ_Z(X)` and `𝒜_A/𝒜_Y` -/

theorem transpose_sub {A B : AsymptoticCategory π X} (φ ψ : A ⟶ B) :
    transpose (φ - ψ) = transpose φ - transpose ψ :=
  (involution π X).star_sub φ ψ

variable {S}

theorem inIdeal_transpose {A B : AsymptoticCategory π X} {φ : A ⟶ B} (h : InIdeal S φ) :
    InIdeal S (transpose φ) := by
  obtain ⟨W, hW, u, v, rfl⟩ := h
  exact ⟨W, hW, transpose v, transpose u, transpose_comp u v⟩

theorem inIdeal_tensor_map {A B : AsymptoticCategory π X} {φ : A ⟶ B} (h : InIdeal S φ) :
    InIdeal S ((tensor ρ).map φ) := by
  obtain ⟨W, hW, u, v, rfl⟩ := h
  exact ⟨(tensor ρ).obj W, IsSupported.tensorObj hW, (tensor ρ).map u, (tensor ρ).map v,
    (tensor ρ).map_comp u v⟩

end AsymptoticCategory

namespace ExteriorCategory

variable {Z : Set X}

/-- The transpose duality of `ℬ_Z(X)`: `I_Z` is closed under transpose. -/
def transpose {A B : ExteriorCategory π Z} (φ : A ⟶ B) : B ⟶ A :=
  Quot.liftOn φ (fun f ↦ functor.map (AsymptoticCategory.transpose f)) fun f g h ↦ by
    rw [HomRel.compClosure_eq_self] at h
    exact (functor_map_eq_iff _ _).mpr (by
      simpa [AsymptoticCategory.transpose_sub] using AsymptoticCategory.inIdeal_transpose h)

@[simp]
theorem transpose_functor_map {A B : AsymptoticCategory π X} (φ : A ⟶ B) :
    transpose ((functor (Z := Z)).map φ) = functor.map (AsymptoticCategory.transpose φ) :=
  rfl

variable (π Z) in
/-- The transpose duality of `ℬ_Z(X)` as a strict involution. -/
def involution : StrictInvolution (ExteriorCategory π Z) where
  star := transpose
  star_comp φ ψ := by
    obtain ⟨f, rfl⟩ := functor.map_surjective φ
    obtain ⟨g, rfl⟩ := functor.map_surjective ψ
    rw [← Functor.map_comp, transpose_functor_map, transpose_functor_map,
      transpose_functor_map, AsymptoticCategory.transpose_comp, Functor.map_comp]
  star_id A := by
    change transpose ((functor (Z := Z)).map (𝟙 A.as)) = functor.map (𝟙 A.as)
    rw [transpose_functor_map, AsymptoticCategory.transpose_id]
  star_add φ ψ := by
    obtain ⟨f, rfl⟩ := functor.map_surjective φ
    obtain ⟨g, rfl⟩ := functor.map_surjective ψ
    rw [← Functor.map_add, transpose_functor_map, transpose_functor_map,
      transpose_functor_map, AsymptoticCategory.transpose_add, Functor.map_add]
  star_star φ := by
    obtain ⟨f, rfl⟩ := functor.map_surjective φ
    rw [transpose_functor_map, transpose_functor_map,
      AsymptoticCategory.transpose_transpose]

variable (Z) in
/-- `ℚ[Q] ⊗ −` on `ℬ_Z(X)`: it preserves `I_Z`. -/
def tensor : ExteriorCategory π Z ⥤ ExteriorCategory π Z :=
  CategoryTheory.Quotient.lift _ (AsymptoticCategory.tensor ρ ⋙ functor) fun _ _ _ _ h ↦
    (functor_map_eq_iff _ _).mpr (by
      rw [← Functor.map_sub]; exact AsymptoticCategory.inIdeal_tensor_map ρ h)

theorem tensor_map_functor_map {A B : AsymptoticCategory π X} (φ : A ⟶ B) :
    (tensor ρ Z).map (functor.map φ) = functor.map ((AsymptoticCategory.tensor ρ).map φ) := rfl

/-- `τ ⊗ −` commutes with `𝒜(X) → ℬ_Z(X)`. -/
theorem functor_comp_tensor :
    functor ⋙ tensor ρ Z = AsymptoticCategory.tensor (π := π) ρ ⋙ functor :=
  CategoryTheory.Quotient.lift_spec _ _ _

instance tensor_additive : (tensor (π := π) ρ Z).Additive where
  map_add {_ _ φ ψ} := by
    obtain ⟨f, rfl⟩ := functor.map_surjective φ
    obtain ⟨g, rfl⟩ := functor.map_surjective ψ
    rw [← Functor.map_add, tensor_map_functor_map, tensor_map_functor_map,
      tensor_map_functor_map, Functor.map_add, Functor.map_add]
    rfl

instance tensor_linear : (tensor (π := π) ρ Z).Linear ℚ where
  map_smul φ c := by
    obtain ⟨f, rfl⟩ := functor.map_surjective φ
    rw [← Functor.map_smul, tensor_map_functor_map, tensor_map_functor_map, Functor.map_smul,
      Functor.map_smul]
    rfl

theorem tensor_map_transpose {A B : ExteriorCategory π Z} (φ : A ⟶ B) :
    (tensor ρ Z).map (transpose φ) = transpose ((tensor ρ Z).map φ) := by
  obtain ⟨f, rfl⟩ := functor.map_surjective φ
  rw [transpose_functor_map, tensor_map_functor_map, tensor_map_functor_map]
  erw [transpose_functor_map]
  rw [AsymptoticCategory.tensor_map_transpose]

/-- `ℚ[Q] ⊗ −` on `ℬ_Z(X)` as a duality-preserving functor. -/
def tensorInv : InvFunctor (involution π Z) (involution π Z) where
  F := tensor ρ Z
  map_star := tensor_map_transpose ρ

end ExteriorCategory

namespace AsymptoticCategory

variable {A Y : Set X}

theorem subIdealRel_add ⦃P R : SupportCategory π A⦄ (f₁ f₂ g₁ g₂ : P ⟶ R)
    (h : subIdealRel π A Y f₁ f₂) (h' : subIdealRel π A Y g₁ g₂) :
    subIdealRel π A Y (f₁ + g₁) (f₂ + g₂) := by
  change InIdeal Y ((f₁.hom + g₁.hom) - (f₂.hom + g₂.hom))
  rw [add_sub_add_comm]
  exact h.add h'

theorem subIdealRel_smul (c : ℚ) ⦃P R : SupportCategory π A⦄ (f₁ f₂ : P ⟶ R)
    (h : subIdealRel π A Y f₁ f₂) : subIdealRel π A Y (c • f₁) (c • f₂) := by
  change InIdeal Y (c • f₁.hom - c • f₂.hom)
  rw [← smul_sub]
  exact h.smul c

instance SupportQuotient.preadditive : Preadditive (SupportQuotient π A Y) :=
  Quotient.preadditive _ subIdealRel_add

/-- The quotient functor `𝒜_A(X) → 𝒜_A/𝒜_Y`. -/
abbrev SupportQuotient.functor : SupportCategory π A ⥤ SupportQuotient π A Y :=
  CategoryTheory.Quotient.functor _

instance SupportQuotient.functor_additive :
    (SupportQuotient.functor (π := π) (A := A) (Y := Y)).Additive :=
  Quotient.functor_additive _ subIdealRel_add

instance SupportQuotient.linear : Linear ℚ (SupportQuotient π A Y) :=
  Quotient.linear ℚ _ subIdealRel_smul

instance SupportQuotient.functor_linear :
    (SupportQuotient.functor (π := π) (A := A) (Y := Y)).Linear ℚ :=
  Quotient.linear_functor ℚ _ subIdealRel_smul

/-- The transpose duality of `𝒜_A/𝒜_Y`. -/
def SupportQuotient.transpose {P R : SupportQuotient π A Y} (φ : P ⟶ R) : R ⟶ P :=
  Quot.liftOn φ (fun f ↦ functor.map ((supportInvolution π A).star f)) fun f g h ↦ by
    rw [HomRel.compClosure_eq_self] at h
    refine CategoryTheory.Quotient.sound _ ?_
    change InIdeal Y (AsymptoticCategory.transpose f.hom - AsymptoticCategory.transpose g.hom)
    rw [← transpose_sub]
    exact inIdeal_transpose h

@[simp]
theorem SupportQuotient.transpose_functor_map {P R : SupportCategory π A} (f : P ⟶ R) :
    SupportQuotient.transpose ((SupportQuotient.functor (Y := Y)).map f) =
      SupportQuotient.functor.map ((supportInvolution π A).star f) := rfl

variable (π A Y) in
/-- The transpose duality of `𝒜_A/𝒜_Y` as a strict involution. -/
def SupportQuotient.involution : StrictInvolution (SupportQuotient π A Y) where
  star := SupportQuotient.transpose
  star_comp φ ψ := by
    obtain ⟨f, rfl⟩ := SupportQuotient.functor.map_surjective φ
    obtain ⟨g, rfl⟩ := SupportQuotient.functor.map_surjective ψ
    rw [← Functor.map_comp, SupportQuotient.transpose_functor_map,
      SupportQuotient.transpose_functor_map, SupportQuotient.transpose_functor_map,
      StrictInvolution.star_comp, Functor.map_comp]
  star_id P := by
    change SupportQuotient.transpose ((SupportQuotient.functor (Y := Y)).map (𝟙 P.as)) =
      SupportQuotient.functor.map (𝟙 P.as)
    rw [SupportQuotient.transpose_functor_map, StrictInvolution.star_id]
  star_add φ ψ := by
    obtain ⟨f, rfl⟩ := SupportQuotient.functor.map_surjective φ
    obtain ⟨g, rfl⟩ := SupportQuotient.functor.map_surjective ψ
    rw [← Functor.map_add, SupportQuotient.transpose_functor_map,
      SupportQuotient.transpose_functor_map, SupportQuotient.transpose_functor_map,
      StrictInvolution.star_add, Functor.map_add]
  star_star φ := by
    obtain ⟨f, rfl⟩ := SupportQuotient.functor.map_surjective φ
    rw [SupportQuotient.transpose_functor_map, SupportQuotient.transpose_functor_map,
      StrictInvolution.star_star]

variable (A Y) in
/-- `ℚ[Q] ⊗ −` on `𝒜_A/𝒜_Y`. -/
def SupportQuotient.tensor : SupportQuotient π A Y ⥤ SupportQuotient π A Y :=
  CategoryTheory.Quotient.lift _ (supportTensor ρ A ⋙ SupportQuotient.functor) fun _ _ f g h ↦
    CategoryTheory.Quotient.sound _ <| by
      change InIdeal Y ((AsymptoticCategory.tensor ρ).map f.hom -
        (AsymptoticCategory.tensor ρ).map g.hom)
      rw [← Functor.map_sub]
      exact inIdeal_tensor_map ρ h

theorem SupportQuotient.tensor_map_functor_map {P R : SupportCategory π A} (f : P ⟶ R) :
    (SupportQuotient.tensor ρ A Y).map (SupportQuotient.functor.map f) =
      SupportQuotient.functor.map ((supportTensor ρ A).map f) := rfl

/-- `τ ⊗ −` commutes with `𝒜_A(X) → 𝒜_A/𝒜_Y`. -/
theorem SupportQuotient.functor_comp_tensor :
    SupportQuotient.functor ⋙ SupportQuotient.tensor ρ A Y =
      supportTensor (π := π) ρ A ⋙ SupportQuotient.functor :=
  CategoryTheory.Quotient.lift_spec _ _ _

instance SupportQuotient.tensor_additive :
    (SupportQuotient.tensor (π := π) ρ A Y).Additive where
  map_add {_ _ φ ψ} := by
    obtain ⟨f, rfl⟩ := SupportQuotient.functor.map_surjective φ
    obtain ⟨g, rfl⟩ := SupportQuotient.functor.map_surjective ψ
    rw [← Functor.map_add, SupportQuotient.tensor_map_functor_map,
      SupportQuotient.tensor_map_functor_map, SupportQuotient.tensor_map_functor_map,
      Functor.map_add, Functor.map_add]
    rfl

instance SupportQuotient.tensor_linear :
    (SupportQuotient.tensor (π := π) ρ A Y).Linear ℚ where
  map_smul φ c := by
    obtain ⟨f, rfl⟩ := SupportQuotient.functor.map_surjective φ
    rw [← Functor.map_smul, SupportQuotient.tensor_map_functor_map,
      SupportQuotient.tensor_map_functor_map, Functor.map_smul, Functor.map_smul]
    rfl

/-- `ℚ[Q] ⊗ −` on `𝒜_A/𝒜_Y` as a duality-preserving functor. -/
def SupportQuotient.tensorInv :
    InvFunctor (SupportQuotient.involution π A Y) (SupportQuotient.involution π A Y) where
  F := SupportQuotient.tensor ρ A Y
  map_star φ := by
    obtain ⟨f, rfl⟩ := SupportQuotient.functor.map_surjective φ
    change (SupportQuotient.tensor ρ A Y).map (SupportQuotient.transpose
      (SupportQuotient.functor.map f)) = SupportQuotient.transpose
        ((SupportQuotient.tensor ρ A Y).map (SupportQuotient.functor.map f))
    rw [SupportQuotient.transpose_functor_map, SupportQuotient.tensor_map_functor_map,
      SupportQuotient.tensor_map_functor_map]
    erw [SupportQuotient.transpose_functor_map]
    exact congrArg _ ((supportTensorInv ρ A).map_star f)

variable (A) {B : Set X}

theorem functor_comp_excisionFunctor :
    SupportQuotient.functor ⋙ excisionFunctor A B =
      (supportProperty (π := π) A).ι ⋙ ExteriorCategory.functor :=
  CategoryTheory.Quotient.lift_spec _ _ _

/-- `τ ⊗ −` commutes with the excision functor `𝒜_A/𝒜_{A ∩ B} → 𝒜(X)/𝒜_B` of
Lemma 2.2. -/
theorem excisionFunctor_comp_tensor :
    excisionFunctor A B ⋙ ExteriorCategory.tensor ρ B =
      SupportQuotient.tensor (π := π) ρ A (A ∩ B) ⋙ excisionFunctor A B := by
  refine CategoryTheory.Quotient.lift_unique' _ _ _ ?_
  rw [← Functor.assoc, ← Functor.assoc, functor_comp_excisionFunctor,
    SupportQuotient.functor_comp_tensor, Functor.assoc, Functor.assoc,
    ExteriorCategory.functor_comp_tensor, functor_comp_excisionFunctor, ← Functor.assoc,
    ← Functor.assoc, supportTensor_comp_ι]

end AsymptoticCategory

/-! ### Relabeling, Lemma 2.4 -/

section Relabel

variable {Y : Type*} [MulAction H Y] [PseudoEMetricSpace Y] {j : Y → X}
  (hjeq : ∀ (h : H) (y : Y), j (h • y) = h • j y)

theorem AsymptoticObject.pushFunctor_comp_tensorFunctor (hj : UniformContinuous j) :
    pushFunctor (π := π) hjeq hj ⋙ tensorFunctor Q ρ =
      tensorFunctor Q ρ ⋙ pushFunctor hjeq hj :=
  CategoryTheory.Functor.ext (fun _ ↦ rfl) fun _ _ _ ↦ by
    erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]; rfl

namespace AsymptoticCategory

/-- `τ ⊗ −` commutes with push-forward of labels. -/
theorem pushTail_comp_tensor (hj : UniformContinuous j) :
    pushTail (π := π) hjeq hj ⋙ tensor ρ = tensor ρ ⋙ pushTail hjeq hj := by
  have h1 : functor ⋙ pushTail (π := π) hjeq hj = pushFunctor hjeq hj ⋙ functor :=
    CategoryTheory.Quotient.lift_spec _ _ _
  refine CategoryTheory.Quotient.lift_unique' _ _ _ ?_
  rw [← Functor.assoc, h1, Functor.assoc, functor_comp_tensor, ← Functor.assoc,
    pushFunctor_comp_tensorFunctor, Functor.assoc, ← h1, ← Functor.assoc, ← Functor.assoc,
    functor_comp_tensor]

/-- `τ ⊗ −` commutes with the relabeling equivalence `𝒜_G(Y) ≌ 𝒜_{j(Y)}(X)` of
Lemma 2.4. -/
theorem relabelFunctor_comp_supportTensor (hj : Isometry j) {T : Set X}
    (hT : Set.range j = T) :
    relabelFunctor hjeq hj hT ⋙ supportTensor ρ T =
      tensor ρ ⋙ relabelFunctor (π := π) hjeq hj hT :=
  CategoryTheory.Functor.ext (fun _ ↦ rfl) fun _ _ _ ↦ by
    erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
    ext1
    exact Functor.congr_hom (pushTail_comp_tensor ρ hjeq hj.uniformContinuous) _ |>.trans
      (by simp [relabelFunctor]; erw [eqToHom_refl, eqToHom_refl, Category.id_comp,
        Category.comp_id])

end AsymptoticCategory

end Relabel

/-! ### `ℚ[Q]^{triv} ⊗ −` is the `|Q|`-fold sum of the identity -/

namespace AsymptoticObject

variable {M N : AsymptoticObject π X}

/-- The summand `q` of `ℚ[Q]^{triv} ⊗ M = ⨁_{q ∈ Q} M`. -/
def sumEmb (M : AsymptoticObject π X) (q : Q) : OrbitEmbedding M (M.tensorObj Q) where
  toFun i k := tensorIdx Q (M.rank i) (k, q)
  injective _ _ _ h := congrArg Prod.fst ((tensorIdx Q _).injective h)
  label_toFun _ _ := by simp [tensorObj]

omit [MulAction H X] [PseudoEMetricSpace X] [∀ i, Fintype (G i)] in
theorem mem_range_sumEmb (M : AsymptoticObject π X) (q : Q) (i : ℕ)
    (r : Fin ((M.tensorObj Q).rank i)) :
    r ∈ Set.range ((M.sumEmb q).toFun i) ↔ ((tensorIdx Q (M.rank i)).symm r).2 = q := by
  constructor
  · rintro ⟨k, rfl⟩
    simp [sumEmb]
  · intro h
    exact ⟨((tensorIdx Q (M.rank i)).symm r).1, by simp [sumEmb, ← h]⟩

omit [MulAction H X] [PseudoEMetricSpace X] [∀ i, Fintype (G i)] in
theorem exists_sumEmb_eq_iff (M : AsymptoticObject π X) (q : Q) (i : ℕ)
    (r : Fin ((M.tensorObj Q).rank i)) :
    (∃ k, (M.sumEmb q).toFun i k = r) ↔ ((tensorIdx Q (M.rank i)).symm r).2 = q :=
  mem_range_sumEmb M q i r

theorem sumEmb_incl_proj (M : AsymptoticObject π X) (q q' : Q) :
    (M.sumEmb q).incl ≫ (M.sumEmb q').proj = if q = q' then 𝟙 M else 0 := by
  split_ifs with h
  · subst h
    exact OrbitEmbedding.incl_proj _
  · refine OrbitEmbedding.incl_proj_eq_zero _ _ fun i k k' hkk' ↦ h ?_
    simpa [sumEmb] using congrArg Prod.snd ((tensorIdx Q _).injective hkk')

theorem sum_val {ι : Type*} (s : Finset ι) (f : ι → (M ⟶ N)) (i : ℕ) :
    (∑ q ∈ s, f q).1 i = ∑ q ∈ s, (f q).1 i :=
  map_sum (AddMonoidHom.mk' (fun f : M ⟶ N ↦ f.1 i) fun f g ↦ add_val f g i) _ _

theorem sum_sumEmb_proj_incl (M : AsymptoticObject π X) :
    ∑ q : Q, (M.sumEmb q).proj ≫ (M.sumEmb q).incl = 𝟙 (M.tensorObj Q) := by
  refine hom_ext fun i ↦ ?_
  simp only [OrbitEmbedding.proj_incl, sum_val]
  ext b' b
  simp [Matrix.sum_apply, diagonal_apply, one_apply, exists_sumEmb_eq_iff]

theorem sumEmb_incl_tensorHom_proj (f : M ⟶ N) (q q' : Q) :
    (M.sumEmb q).incl ≫ tensorHom 1 f ≫ (N.sumEmb q').proj = if q = q' then f else 0 := by
  refine hom_ext fun i ↦ ?_
  rw [OrbitEmbedding.incl_comp, OrbitEmbedding.comp_proj, tensorHom_val, submatrix_submatrix,
    Function.comp_id, Function.id_comp]
  ext b' b
  split_ifs with h
  · subst h
    simp [tensorMatrix_apply, tensorCoord, OrbitEmbedding.basisMap, sumEmb]
  · simp [tensorMatrix_apply, tensorCoord, OrbitEmbedding.basisMap, sumEmb, Ne.symm h]

theorem tensorHom_comp_sumEmb_proj (f : M ⟶ N) (q : Q) :
    tensorHom 1 f ≫ (N.sumEmb q).proj = (M.sumEmb q).proj ≫ f := by
  calc tensorHom 1 f ≫ (N.sumEmb q).proj
      = (∑ q', (M.sumEmb q').proj ≫ (M.sumEmb q').incl) ≫ tensorHom 1 f ≫
          (N.sumEmb q).proj := by
        rw [sum_sumEmb_proj_incl, Category.id_comp]
    _ = ∑ q', (M.sumEmb q').proj ≫
          ((M.sumEmb q').incl ≫ tensorHom 1 f ≫ (N.sumEmb q).proj) := by
        simp only [Preadditive.sum_comp, Category.assoc]
    _ = (M.sumEmb q).proj ≫ f := by
        rw [Finset.sum_eq_single q (fun q' _ h ↦ by simp [sumEmb_incl_tensorHom_proj, h])
          (by simp)]
        simp [sumEmb_incl_tensorHom_proj]

theorem sumEmb_incl_comp_tensorHom (f : M ⟶ N) (q : Q) :
    (M.sumEmb q).incl ≫ tensorHom 1 f = f ≫ (N.sumEmb q).incl := by
  calc (M.sumEmb q).incl ≫ tensorHom 1 f
      = (M.sumEmb q).incl ≫ tensorHom 1 f ≫
          ∑ q', (N.sumEmb q').proj ≫ (N.sumEmb q').incl := by
        rw [sum_sumEmb_proj_incl, Category.comp_id]
    _ = ∑ q', ((M.sumEmb q).incl ≫ tensorHom 1 f ≫ (N.sumEmb q').proj) ≫
          (N.sumEmb q').incl := by
        simp only [Preadditive.comp_sum, Category.assoc]
    _ = f ≫ (N.sumEmb q).incl := by
        rw [Finset.sum_eq_single q (fun q' _ h ↦ by simp [sumEmb_incl_tensorHom_proj, Ne.symm h])
          (by simp)]
        simp [sumEmb_incl_tensorHom_proj]

end AsymptoticObject

namespace AsymptoticCategory

variable (S : Set X)

/-- The inclusion `A ⟶ ⨁_Q A` of the summand `q`, natural on `𝒜_S(X)`. -/
def sumIncl (q : Q) :
    𝟭 (SupportCategory π S) ⟶ supportTensor (1 : H →* Equiv.Perm Q) S where
  app A := ObjectProperty.homMk (functor.map (A.obj.as.sumEmb q).incl)
  naturality A B f := by
    ext1
    obtain ⟨u, hu⟩ := exists_rep f.hom
    change f.hom ≫ functor.map (B.obj.as.sumEmb q).incl =
      functor.map (A.obj.as.sumEmb q).incl ≫ (tensor _).map f.hom
    rw [← hu, tensor_map_functor_map]
    erw [← Functor.map_comp, ← Functor.map_comp]
    rw [sumEmb_incl_comp_tensorHom]

/-- The projection `⨁_Q A ⟶ A` onto the summand `q`, natural on `𝒜_S(X)`. -/
def sumProj (q : Q) :
    supportTensor (1 : H →* Equiv.Perm Q) S ⟶ 𝟭 (SupportCategory π S) where
  app A := ObjectProperty.homMk (functor.map (A.obj.as.sumEmb q).proj)
  naturality A B f := by
    ext1
    obtain ⟨u, hu⟩ := exists_rep f.hom
    change (tensor _).map f.hom ≫ functor.map (B.obj.as.sumEmb q).proj =
      functor.map (A.obj.as.sumEmb q).proj ≫ f.hom
    rw [← hu, tensor_map_functor_map]
    erw [← Functor.map_comp, ← Functor.map_comp]
    rw [tensorHom_comp_sumEmb_proj]

/-- The summand inclusions are unitary: their transposes are the projections. -/
theorem sumIncl_unitary (q : Q) (A : SupportCategory π S) :
    (supportInvolution π S).star ((sumIncl S q).app A) = (sumProj S q).app A := rfl

theorem sumIncl_sumProj (q q' : Q) (A : SupportCategory π S) :
    (sumIncl S q).app A ≫ (sumProj S q').app A = if q = q' then 𝟙 A else 0 := by
  ext1
  change functor.map ((A.obj.as.sumEmb q).incl ≫ (A.obj.as.sumEmb q').proj) = _
  rw [sumEmb_incl_proj]
  split_ifs <;> rfl

theorem sum_sumProj_sumIncl (A : SupportCategory π S) :
    ∑ q : Q, (sumProj S q).app A ≫ (sumIncl S q).app A = 𝟙 _ := by
  ext1
  rw [← (supportProperty S).ι_map, Functor.map_sum]
  change ∑ q : Q, functor.map (A.obj.as.sumEmb q).proj ≫ functor.map (A.obj.as.sumEmb q).incl =
    functor.map (𝟙 _)
  simp only [← Functor.map_comp, ← Functor.map_sum]
  exact congrArg _ (sum_sumEmb_proj_incl _)

/-- `ℚ[Q]^{triv} ⊗ A` is the biproduct `⨁_{q ∈ Q} A`, with unitary structure maps. -/
def sumBicone (A : SupportCategory π S) : Bicone fun _ : Q ↦ A where
  pt := (supportTensor (1 : H →* Equiv.Perm Q) S).obj A
  π q := (sumProj S q).app A
  ι q := (sumIncl S q).app A
  ι_π q q' := by
    rw [sumIncl_sumProj]
    split_ifs with h
    · subst h; rfl
    · rfl

def sumBicone_isBilimit (A : SupportCategory π S) : (sumBicone (Q := Q) S A).IsBilimit :=
  isBilimitOfTotal _ (sum_sumProj_sumIncl S A)

end AsymptoticCategory

/-! ### Sheet functions (l.417) -/

section Sheet

variable {S W K : Set X} {c : X → H}

/-- `c` is a sheet function near `S`: on a uniform neighbourhood of `S` it is equivariant,
`c (h • x) = h * c x`, and constant on balls of a fixed radius. -/
def IsUniformSheet (S : Set X) (c : X → H) : Prop :=
  ∃ δ > 0, ∀ x, infEDist x S < δ →
    (∀ y, edist x y < δ → c y = c x) ∧ ∀ h : H, c (h • x) = h * c x

theorem IsUniformSheet.mono {S' : Set X} (hSS' : S ⊆ S') (hc : IsUniformSheet S' c) :
    IsUniformSheet S c := by
  obtain ⟨δ, hδ, h⟩ := hc
  exact ⟨δ, hδ, fun x hx ↦ h x ((infEDist_anti hSS').trans_lt hx)⟩

/-- A sheet function on an open set `W`, the lift of a trivializing open set `V ⊆ X/H`: `c`
is locally constant on `W` with `c (h • x) = h * c x` (l.417). -/
structure IsSheetFunction (W : Set X) (c : X → H) : Prop where
  isOpen : IsOpen W
  eventually_eq : ∀ x ∈ W, ∀ᶠ y in 𝓝 x, c y = c x
  map_smul : ∀ (h : H), ∀ x ∈ W, c (h • x) = h * c x

/-- A sheet function on `W` is uniform near every compact `K ⊆ W` (Lebesgue number; this is
the positive separation of the sheet pieces over a compact set, l.417–425). -/
theorem IsSheetFunction.isUniformSheet (hc : IsSheetFunction W c) (hK : IsCompact K)
    (hKW : K ⊆ W) : IsUniformSheet K c := by
  obtain ⟨δ, hδ, hball⟩ : ∃ δ > 0, ∀ x ∈ K, ∃ y, eball x δ ⊆ {z | z ∈ W ∧ c z = c y} := by
    simpa only [eball, UniformSpace.ball, Set.preimage_ofPred_eq, edist_comm] using
      uniformity_basis_edist.lebesgue_number_lemma_nhds (U := fun x ↦ {y | y ∈ W ∧ c y = c x})
        hK fun x hx ↦
          Filter.Eventually.and (hc.isOpen.eventually_mem (hKW hx)) (hc.eventually_eq x (hKW hx))
  refine ⟨δ / 2, ENNReal.half_pos hδ.ne', fun x hx ↦ ?_⟩
  obtain ⟨s, hs, hxs⟩ := infEDist_lt_iff.mp hx
  obtain ⟨z, hz⟩ := hball s hs
  have hxz := hz (Metric.mem_eball.mpr (hxs.trans_le ENNReal.half_le_self))
  refine ⟨fun y hy ↦ ?_, fun h ↦ hc.map_smul h x hxz.1⟩
  have hys : edist y s < δ := by
    calc edist y s ≤ edist y x + edist x s := edist_triangle _ _ _
      _ < δ / 2 + δ / 2 := ENNReal.add_lt_add ((edist_comm x y) ▸ hy) hxs
      _ = δ := ENNReal.add_halves δ
  have hyz := hz (Metric.mem_eball.mpr hys)
  exact hyz.2.trans hxz.2.symm

omit [PseudoEMetricSpace X] in
theorem eq_of_mem_smul_of_disjoint {W₀ : Set X}
    (hdisj : ∀ h : H, h ≠ 1 → Disjoint (h • W₀) W₀) {x : X} {g g' : H} (hg : x ∈ g • W₀)
    (hg' : x ∈ g' • W₀) : g = g' := by
  by_contra hne
  have h1 : g'⁻¹ • x ∈ W₀ := Set.mem_smul_set_iff_inv_smul_mem.mp hg'
  have h2 : g'⁻¹ • x ∈ (g'⁻¹ * g) • W₀ := by
    rw [← smul_smul]
    exact Set.smul_mem_smul_set hg
  refine Set.disjoint_left.mp (hdisj (g'⁻¹ * g) ?_) h2 h1
  rw [Ne, inv_mul_eq_one]
  exact Ne.symm hne

/-- **Trivializing open sets.** If the translates `h • W₀` of an open sheet are pairwise
disjoint (`W₀` maps homeomorphically onto an evenly covered open `V ⊆ X/H`), then
`x ↦ h` for `x ∈ h • W₀` is a sheet function on the lift `⋃ h, h • W₀` of `V`. -/
theorem exists_isSheetFunction [ContinuousConstSMul H X] {W₀ : Set X} (hW₀ : IsOpen W₀)
    (hdisj : ∀ h : H, h ≠ 1 → Disjoint (h • W₀) W₀) :
    ∃ c : X → H, IsSheetFunction (⋃ h : H, h • W₀) c := by
  let c : X → H := fun x ↦ if hx : ∃ h : H, x ∈ h • W₀ then hx.choose else 1
  have hc : ∀ x g, x ∈ g • W₀ → c x = g := fun x g hx ↦ by
    have hex : ∃ h : H, x ∈ h • W₀ := ⟨g, hx⟩
    simp only [c, dite_eq_left hex]
    exact eq_of_mem_smul_of_disjoint hdisj hex.choose_spec hx
  refine ⟨c, isOpen_iUnion fun h ↦ hW₀.smul h, fun x hx ↦ ?_, fun h x hx ↦ ?_⟩
  · obtain ⟨g, hg⟩ := Set.mem_iUnion.mp hx
    filter_upwards [(hW₀.smul g).mem_nhds hg] with y hy
    rw [hc y g hy, hc x g hg]
  · obtain ⟨g, hg⟩ := Set.mem_iUnion.mp hx
    rw [hc x g hg, hc (h • x) (h * g) (by rw [← smul_smul]; exact Set.smul_mem_smul_set hg)]

/-- Sheet functions restrict along isometric equivariant maps, e.g. to the subspaces of the
induction in Lemma 6.2. -/
theorem IsUniformSheet.comp {Y : Type*} [MulAction H Y] [PseudoEMetricSpace Y] {j : Y → X}
    (hj : Isometry j) (hjeq : ∀ (h : H) (y : Y), j (h • y) = h • j y)
    (hc : IsUniformSheet S c) : IsUniformSheet (j ⁻¹' S) (c ∘ j) := by
  obtain ⟨δ, hδ, h⟩ := hc
  refine ⟨δ, hδ, fun y hy ↦ ?_⟩
  have hle : infEDist (j y) S ≤ infEDist y (j ⁻¹' S) := le_infEDist.mpr fun s' hs' ↦
    (infEDist_le_edist_of_mem (show j s' ∈ S from hs')).trans_eq (hj.edist_eq y s')
  have hjy : infEDist (j y) S < δ := hle.trans_lt hy
  refine ⟨fun y' hy' ↦ (h _ hjy).1 _ (by rwa [hj.edist_eq]), fun g ↦ ?_⟩
  simp only [Function.comp_apply, hjeq]
  exact (h _ hjy).2 g

theorem IsUniformSheet.eventually_sheet (hc : IsUniformSheet S c)
    {M N : AsymptoticObject π X} (hM : M.IsSupported S) (hN : N.IsSupported S) (f : M ⟶ N) :
    ∀ᶠ i in atTop, ∀ b' b, f.1 i b' b ≠ 0 →
      π i b'.2 * c (N.label i b'.1) = π i b.2 * c (M.label i b.1) := by
  obtain ⟨δ, hδ, h⟩ := hc
  filter_upwards [(tendsto_order.1 hM).2 δ hδ, (tendsto_order.1 hN).2 δ hδ,
    (tendsto_order.1 (tendsto_propSeq f)).2 δ hδ] with i hMi hNi hfi b' b hb
  have hx := (infEDist_le_supportDist (S := S) i b).trans_lt hMi
  have hxy : edist (M.fullLabel i b) (N.fullLabel i b') < δ := by
    rw [edist_comm]
    exact (edist_le_prop hb).trans_lt hfi
  have hM1 := (infEDist_le_supportDist (S := S) i (b.1, 1)).trans_lt hMi
  have hN1 := (infEDist_le_supportDist (S := S) i (b'.1, 1)).trans_lt hNi
  rw [fullLabel_one] at hM1 hN1
  rw [← (h _ hN1).2, ← (h _ hM1).2]
  exact ((h _ hx).1 _ hxy)

end Sheet

/-! ### Lemma 6.1: local tensor triviality -/

section LocalTriviality

variable [Fintype H]

variable (H) in
/-- `τ = ℚ[H]`, `H = C_p = G_i/P_i` acting by left multiplication (l.403). -/
abbrev tauAction : H →* Equiv.Perm H := MulAction.toPermHom H H

omit [Fintype H] in
theorem sheet_iff {a a' c c' q q' : H} (h : a' * c' = a * c) :
    a' * q' = a * q ↔ c'⁻¹ * q' = c⁻¹ * q := by
  have h2 : a'⁻¹ * a = c' * c⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, h, mul_inv_cancel_right]
  rw [← eq_inv_mul_iff_mul_eq, inv_mul_eq_iff_eq_mul, ← mul_assoc, h2, mul_assoc]

namespace AsymptoticObject

variable (c : X → H) (M : AsymptoticObject π X)

/-- The sheet permutation (6.2) of the orbits of `τ ⊗ M`: `(k, q) ↦ (k, c(ℓ k)⁻¹ q)`. -/
def sheetPerm (i : ℕ) : Equiv.Perm (Fin ((M.tensorObj H).rank i)) where
  toFun r := tensorIdx H (M.rank i) (((tensorIdx H (M.rank i)).symm r).1,
    (c (M.label i ((tensorIdx H (M.rank i)).symm r).1))⁻¹ * ((tensorIdx H (M.rank i)).symm r).2)
  invFun r := tensorIdx H (M.rank i) (((tensorIdx H (M.rank i)).symm r).1,
    c (M.label i ((tensorIdx H (M.rank i)).symm r).1) * ((tensorIdx H (M.rank i)).symm r).2)
  left_inv r := by simp
  right_inv r := by simp

/-- (6.2) as a label-preserving permutation of the orbits of `τ ⊗ M`. -/
def sheetEmb : OrbitEmbedding (M.tensorObj H) (M.tensorObj H) where
  toFun i := M.sheetPerm c i
  injective i := (M.sheetPerm c i).injective
  label_toFun i r := by simp [tensorObj, sheetPerm]

theorem sheetEmb_proj_incl : (M.sheetEmb c).proj ≫ (M.sheetEmb c).incl = 𝟙 _ := by
  rw [OrbitEmbedding.proj_incl, ← diagProj_true]
  congr 1
  funext i r
  exact propext (iff_true_intro ((M.sheetPerm c i).surjective r))

/-- The isometry (6.2) of `τ ⊗ M` with `⨁_H M`; its inverse is its transpose. -/
def sheetIso : M.tensorObj H ≅ M.tensorObj H where
  hom := (M.sheetEmb c).incl
  inv := (M.sheetEmb c).proj
  hom_inv_id := OrbitEmbedding.incl_proj _
  inv_hom_id := M.sheetEmb_proj_incl c

variable {M} {N : AsymptoticObject π X}

omit [∀ i, Fintype (G i)] [MulAction H X] [PseudoEMetricSpace X] in
theorem tensorMatrix_tau_eq (f : Family M N) (i : ℕ) (hf : ∀ b' b, f i b' b ≠ 0 →
    π i b'.2 * c (N.label i b'.1) = π i b.2 * c (M.label i b.1)) :
    tensorMatrix (tauAction H) f i = (tensorMatrix 1 f i).submatrix ((N.sheetEmb c).basisMap i)
      ((M.sheetEmb c).basisMap i) := by
  ext b' b
  simp only [submatrix_apply, tensorMatrix_apply, tensorCoord, OrbitEmbedding.basisMap, sheetEmb,
    sheetPerm]
  simp only [Equiv.coe_fn_mk, MulAction.toPermHom_apply, MulAction.toPerm_apply, smul_eq_mul,
    MonoidHom.one_apply, Equiv.Perm.coe_one, id_eq, Equiv.symm_apply_apply]
  by_cases h0 : f i (((tensorIdx H (N.rank i)).symm b'.1).1, b'.2)
    (((tensorIdx H (M.rank i)).symm b.1).1, b.2) = 0
  · simp only [h0, ite_self]
  · rw [sheet_iff (hf _ _ h0)]

/-- Over a uniform sheet function, `τ ⊗ f` is conjugate by (6.2) to `⨁_H f` in the tail. -/
theorem functor_map_tensorHom_tau {S : Set X} (hc : IsUniformSheet S c) (hM : M.IsSupported S)
    (hN : N.IsSupported S) (f : M ⟶ N) :
    AsymptoticCategory.functor.map (tensorHom (tauAction H) f) =
      AsymptoticCategory.functor.map
        ((M.sheetEmb c).incl ≫ tensorHom 1 f ≫ (N.sheetEmb c).proj) := by
  rw [AsymptoticCategory.functor_map_eq_iff]
  filter_upwards [hc.eventually_sheet hM hN f] with i hi
  rw [tensorHom_val, OrbitEmbedding.incl_comp, OrbitEmbedding.comp_proj, tensorHom_val,
    submatrix_submatrix, Function.comp_id, Function.id_comp]
  exact tensorMatrix_tau_eq c f.1 i hi

end AsymptoticObject

namespace AsymptoticCategory

variable {S : Set X} {c : X → H}

/-- **Lemma 6.1 (local triviality).** If `c` is a sheet function near `S` (e.g. `S` is
contained in a compact subset of the lift of a trivializing open set of `X/H`,
`IsSheetFunction.isUniformSheet`), the map (6.2) `e_b ⊗ m_x ↦ m_x` in copy `c(x)⁻¹ b` is a
natural isomorphism `τ ⊗ − ≅ ⨁_H 𝟭` of endofunctors of `𝒜_S(X)`. -/
def localTriv (hc : IsUniformSheet S c) :
    supportTensor (π := π) (tauAction H) S ≅ supportTensor (1 : H →* Equiv.Perm H) S :=
  NatIso.ofComponents (fun A ↦ ObjectProperty.isoMk _ (functor.mapIso (A.obj.as.sheetIso c)))
    fun {A B} f ↦ by
      ext1
      obtain ⟨u, hu⟩ := exists_rep f.hom
      change (tensor _).map f.hom ≫ functor.map (B.obj.as.sheetEmb c).incl =
        functor.map (A.obj.as.sheetEmb c).incl ≫ (tensor _).map f.hom
      rw [← hu, tensor_map_functor_map, tensor_map_functor_map,
        functor_map_tensorHom_tau c hc A.property B.property u]
      erw [← Functor.map_comp, ← Functor.map_comp]
      simp only [Category.assoc, sheetEmb_proj_incl, Category.comp_id]
      rfl

@[simp]
theorem localTriv_hom_app_hom (hc : IsUniformSheet S c) (A : SupportCategory π S) :
    ((localTriv hc).hom.app A).hom = functor.map (A.obj.as.sheetEmb c).incl := rfl

@[simp]
theorem localTriv_inv_app_hom (hc : IsUniformSheet S c) (A : SupportCategory π S) :
    ((localTriv hc).inv.app A).hom = functor.map (A.obj.as.sheetEmb c).proj := rfl

/-- **Lemma 6.1, unitarity:** the inverse of (6.2) is its transpose, so (6.2) is an isometry
for the forms `τ ⊗ φ` and `⨁_H φ`. -/
theorem localTriv_unitary (hc : IsUniformSheet S c) (A : SupportCategory π S) :
    (supportInvolution π S).star ((localTriv hc).hom.app A) = (localTriv hc).inv.app A := rfl

/-- **Lemma 6.1** as stated in the manuscript (l.415): let `W₀` be an open sheet whose
translates are pairwise disjoint, so that `⋃ h, h • W₀` is the lift of a trivializing open set
`V ⊆ X/H`, and let `S` lie in a compact subset of this lift (e.g. `S = T_U`, `U ⊆ V` compact).
Then on `𝒜_S(X)` there is a unitary natural isomorphism `τ ⊗ − ≅ ⨁_H 𝟭`. -/
theorem exists_unitary_localTriv [ContinuousConstSMul H X] {W₀ K : Set X} (hW₀ : IsOpen W₀)
    (hdisj : ∀ h : H, h ≠ 1 → Disjoint (h • W₀) W₀) (hK : IsCompact K)
    (hKW : K ⊆ ⋃ h : H, h • W₀) (hSK : S ⊆ K) :
    ∃ e : supportTensor (π := π) (tauAction H) S ≅ supportTensor (1 : H →* Equiv.Perm H) S,
      ∀ A, (supportInvolution π S).star (e.hom.app A) = e.inv.app A := by
  obtain ⟨c, hc⟩ := exists_isSheetFunction hW₀ hdisj
  have hcS := (hc.isUniformSheet hK hKW).mono hSK
  exact ⟨localTriv hcS, localTriv_unitary hcS⟩

end AsymptoticCategory

end LocalTriviality

end HSFormal
