import HSFormal.LTheory.Model.NegK.High.RegLocal

/-!
# Theorem R, part 4: matrices and the concrete rings (NegKHigh module N12, `RegMatrix`)

`blueprint/negK-high.md` §4 ("Kar form (dictionary)") and §7 (N12).

* **Ring isomorphisms.** `laurentGroupEquiv : (A[G])[T;T⁻¹] ≃+* (A[T;T⁻¹])[G]`,
  `polynomialGroupEquiv : (A[G])[X] ≃+* (A[X])[G]`, `lpRingEquiv` (functoriality of `lpRing` in
  ring isomorphisms), `lpRingGroupEquiv : lpRing n (A[G]) ≃+* (lpComm n A)[G]`, and
  `faceRingEquiv : lpRing n (K[G][X]) ≃+* C[G]` with `C = lpComm n (K[X])`.
* **The concrete rings.** `FullRing K G n = lpRing (n + 1) (K[G])` and
  `FaceRing K G n = lpRing n (K[G][X])` with `faceMap n : FaceRing → FullRing` the localization at
  the central innermost variable (`isCentralLoc_faceMap`); `FaceRing` is noetherian of global
  dimension `≤ n + 1` (transported along `faceRingEquiv` from `RegPd`/`RegNoeth`).
  **`theoremR_module`** is Theorem R in the blueprint's module form.
* **Dictionary** for a (noncommutative) ring `R`, with maps acting by `x ↦ x ᵥ* A` (the
  convention of `FreeQGMat.linOf`, composition `A ≫ B = A * B`): `imMod e` (image of an
  idempotent matrix: finitely generated projective), `exists_idempotent_of_projective` (every
  finitely generated projective is some `imMod e`), `matKarIso_of_linearEquiv` (a module
  isomorphism `imMod e ≃ imMod f` gives a Karoubi isomorphism `MatKarIso e f`),
  `imModFromBlocksEquiv` (block sums), `isLocMap_imModLoc` (`imMod (e.map ι)` is the localization
  of `imMod e`); `MatKarIso.refl/symm/trans/map/fromBlocks` for assembling fibres in N13.
* **`theoremR_matrix`** (the interface for N13): for an idempotent matrix `e` over
  `FullRing K G n` there are idempotent matrices `e₀, e₁` over `FaceRing K G n` with
  `MatKarIso (fromBlocks e 0 0 (e₁.map faceMap)) (e₀.map faceMap)`, i.e.
  `E ⊞ ι⁺Q₁ ≅ ι⁺Q₀` (an isomorphism, not just a stable one).
-/

open CategoryTheory

namespace HSFormal.LTheory.Reg

universe u

section RingIso

open LaurentPolynomial

variable {A : Type u} [CommRing A] {G : Type u} [Group G]

/-- `(A[G])[Γ] ≃ (A[Γ])[G]` for an additive monoid `Γ` (exponents of the Laurent/polynomial
variable). -/
noncomputable def swapEquiv (Γ : Type*) [AddMonoid Γ] :
    AddMonoidAlgebra (MonoidAlgebra A G) Γ ≃+* MonoidAlgebra (AddMonoidAlgebra A Γ) G :=
  (AddMonoidAlgebra.toMultiplicative (MonoidAlgebra A G) Γ).trans <|
    MonoidAlgebra.commRingEquiv.trans <|
      MonoidAlgebra.mapRingEquiv G (AddMonoidAlgebra.toMultiplicative A Γ).symm

variable (A G) in
/-- `(A[G])[T;T⁻¹] ≃ (A[T;T⁻¹])[G]`. -/
noncomputable def laurentGroupEquiv :
    LaurentPolynomial (MonoidAlgebra A G) ≃+* MonoidAlgebra (LaurentPolynomial A) G :=
  swapEquiv ℤ

variable (A G) in
/-- `(A[G])[X] ≃ (A[X])[G]`. -/
noncomputable def polynomialGroupEquiv :
    Polynomial (MonoidAlgebra A G) ≃+* MonoidAlgebra (Polynomial A) G :=
  (Polynomial.toFinsuppIso _).trans <| (swapEquiv ℕ).trans <|
    MonoidAlgebra.mapRingEquiv G (Polynomial.toFinsuppIso A).symm

/-- `lpRing n` respects ring isomorphisms. -/
noncomputable def lpRingEquiv : ∀ (n : ℕ) {R R' : RingCat.{u}}, (R ≃+* R') →
    (lpRing n R ≃+* lpRing n R')
  | 0, _, _, e => e
  | n + 1, _, _, e => lpRingEquiv n (R := RingCat.of (LaurentPolynomial _))
      (R' := RingCat.of (LaurentPolynomial _)) (AddMonoidAlgebra.mapRingEquiv ℤ e)

variable (G) in
/-- `lpRing n (A[G]) ≃ (lpComm n A)[G]`. -/
noncomputable def lpRingGroupEquiv : ∀ (n : ℕ) (A : CommRingCat.{u}),
    lpRing n (RingCat.of (MonoidAlgebra A G)) ≃+* MonoidAlgebra (lpComm n A) G
  | 0, _ => RingEquiv.refl _
  | n + 1, A => (lpRingEquiv n (R := RingCat.of (LaurentPolynomial (MonoidAlgebra A G)))
      (R' := RingCat.of (MonoidAlgebra (LaurentPolynomial A) G)) (laurentGroupEquiv A G)).trans
      (lpRingGroupEquiv n (CommRingCat.of (LaurentPolynomial A)))

variable (G) in
/-- The faces ring `lpRing n (K[G][X])` is the group ring `C[G]` of `C = lpComm n (K[X])`. -/
noncomputable def faceRingEquiv (K : Type u) [Field K] (n : ℕ) :
    lpRing n (RingCat.of (Polynomial (MonoidAlgebra K G))) ≃+*
      MonoidAlgebra (lpComm n (CommRingCat.of (Polynomial K))) G :=
  (lpRingEquiv n (R := RingCat.of (Polynomial (MonoidAlgebra K G)))
    (R' := RingCat.of (MonoidAlgebra (Polynomial K) G)) (polynomialGroupEquiv K G)).trans
    (lpRingGroupEquiv G n (CommRingCat.of (Polynomial K)))

end RingIso


section Faces

variable (K : Type u) [Field K] (G : Type u) [Group G] [Fintype G]

/-- The faces ring `S = lpRing n (K[G][X])` (Laurent in `n` outer variables, polynomial in the
innermost one). -/
noncomputable abbrev FaceRing (n : ℕ) : RingCat.{u} := lpRing n (RingCat.of (Polynomial (MonoidAlgebra K G)))

/-- The full ring `S' = lpRing (n + 1) (K[G])`. -/
noncomputable abbrev FullRing (n : ℕ) : RingCat.{u} := lpRing (n + 1) (RingCat.of (MonoidAlgebra K G))

/-- **(R3)** for the faces ring. -/
instance isNoetherianRing_faceRing (n : ℕ) : IsNoetherianRing (FaceRing K G n) := by
  have := isNoetherianRing_lpComm_polynomial_monoidAlgebra K G n
  exact isNoetherianRing_of_ringEquiv _ (faceRingEquiv G K n).symm

/-- **(R1) + (R2)** for the faces ring: global dimension `≤ n + 1`. -/
lemma globalDimLE_faceRing [NeZero (Nat.card G : K)] (n : ℕ) :
    GlobalDimLE (FaceRing K G n) (n + 1) :=
  (globalDimLE_lpComm_polynomial_monoidAlgebra K G n).of_ringEquiv (faceRingEquiv G K n).symm

/-- **Theorem R (module form).** For every finitely generated projective module `P` over
`S' = lpRing (n + 1) (K[G])` there are finitely generated projective modules `Q₀, Q₁` over the
faces ring `S = lpRing n (K[G][X])` with `P ⊕ Q₁[w⁻¹] ≅ Q₀[w⁻¹]`, `w` the innermost
variable (`Q_j[w⁻¹]` is `E_j.Q'`, the localization along `faceMap`). -/
theorem theoremR_module [NeZero (Nat.card G : K)] (n : ℕ) (P : Type u) [AddCommGroup P]
    [Module (FullRing K G n) P] [Module.Finite (FullRing K G n) P]
    [Module.Projective (FullRing K G n) P] :
    ∃ E₀ E₁ : LocProj (faceMap n (RingCat.of (MonoidAlgebra K G)))
        (faceVar n (RingCat.of (MonoidAlgebra K G))),
      Nonempty ((P × E₁.Q') ≃ₗ[FullRing K G n] E₀.Q') :=
  theoremR_abstract (isCentralLoc_faceMap n _) (globalDimLE_faceRing K G n) P

end Faces


/-! ### Idempotent matrices and finitely generated projective modules -/

section Dictionary

open Matrix

variable {R : Type u} [Ring R] {α β : Type*} [Fintype α]

/-- `x ↦ x ᵥ* A`, a left `R`-linear map `R^α → R^β` (the convention of `FreeQGMat.linOf`:
morphisms compose as `A ≫ B = A * B`). -/
def vecMulLin (A : Matrix α β R) : (α → R) →ₗ[R] (β → R) where
  toFun x := x ᵥ* A
  map_add' x y := add_vecMul A x y
  map_smul' c x := smul_vecMul c x A

@[simp] lemma vecMulLin_apply (A : Matrix α β R) (x : α → R) : vecMulLin A x = x ᵥ* A := rfl

/-- The matrix of a left `R`-linear map `R^α → R^β` in the `vecMul` convention. -/
def repMat [DecidableEq α] (L : (α → R) →ₗ[R] (β → R)) : Matrix α β R :=
  fun i j ↦ L (Pi.single i 1) j

lemma linearMap_eq_vecMul [DecidableEq α] (L : (α → R) →ₗ[R] (β → R)) (x : α → R) :
    L x = x ᵥ* repMat L := by
  have hx : x = ∑ i, x i • (Pi.single i (1 : R) : α → R) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  funext k
  simp [map_sum, map_smul, vecMul, dotProduct, Finset.sum_apply, repMat]

lemma eq_of_vecMul_eq [DecidableEq α] {A B : Matrix α β R} (h : ∀ x, x ᵥ* A = x ᵥ* B) :
    A = B := by
  ext i j
  simpa [single_one_vecMul] using congrFun (h (Pi.single i 1)) j

variable [Fintype β]

/-- The image `{x ᵥ* e}` of a square matrix: for idempotent `e`, the finitely generated
projective module of the Karoubi object `(R^α, e)`. -/
abbrev imMod (e : Matrix α α R) : Submodule R (α → R) := LinearMap.range (vecMulLin e)

lemma mem_imMod {e : Matrix α α R} {y : α → R} : y ∈ imMod e ↔ ∃ x, x ᵥ* e = y := Iff.rfl

lemma vecMul_eq_self_of_mem {e : Matrix α α R} (he : e * e = e) {y : α → R}
    (hy : y ∈ imMod e) : y ᵥ* e = y := by
  obtain ⟨x, rfl⟩ := hy
  simp [vecMul_vecMul, he]

instance (e : Matrix α α R) : Module.Finite R (imMod e) := Module.Finite.range _

lemma projective_imMod {e : Matrix α α R} (he : e * e = e) : Module.Projective R (imMod e) :=
  Module.Projective.of_split (imMod e).subtype (vecMulLin e).rangeRestrict
    (LinearMap.ext fun y ↦ Subtype.ext (vecMul_eq_self_of_mem he y.2))

/-- Isomorphism of Karoubi objects `(R^α, e) ≅ (R^β, f)` in the matrix category
(composition `A ≫ B = A * B`). -/
def MatKarIso (e : Matrix α α R) (f : Matrix β β R) : Prop :=
  ∃ (u : Matrix α β R) (v : Matrix β α R), e * u * f = u ∧ f * v * e = v ∧ u * v = e ∧ v * u = f

namespace MatKarIso

variable {γ : Type*} [Fintype γ] {e : Matrix α α R} {f : Matrix β β R} {g : Matrix γ γ R}

lemma refl (he : e * e = e) : MatKarIso e e := ⟨e, e, by simp [he], by simp [he], he, he⟩

lemma symm (h : MatKarIso e f) : MatKarIso f e :=
  let ⟨u, v, h1, h2, h3, h4⟩ := h; ⟨v, u, h2, h1, h4, h3⟩

/-- Transitivity (for idempotent `e`, `f`). -/
lemma trans (he : e * e = e) (hf : f * f = f) (h : MatKarIso e f) (h' : MatKarIso f g) :
    MatKarIso e g := by
  obtain ⟨u, v, h1, h2, h3, h4⟩ := h
  obtain ⟨u', v', h1', h2', h3', h4'⟩ := h'
  have heu : e * u = u := by
    conv_lhs => rw [← h1]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, he, h1]
  have hvu' : f * u' = u' := by
    conv_lhs => rw [← h1']
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hf, h1']
  have huf : u * f = u := by
    conv_lhs => rw [← h1]
    rw [Matrix.mul_assoc, hf, h1]
  have hve : v * e = v := by
    conv_lhs => rw [← h2]
    rw [Matrix.mul_assoc, he, h2]
  have hg : g * g = g := by
    rw [← h4', Matrix.mul_assoc, ← Matrix.mul_assoc u' v' u', h3', hvu']
  have hu'g : u' * g = u' := by
    conv_lhs => rw [← h1']
    rw [Matrix.mul_assoc, hg, h1']
  have hgv' : g * v' = v' := by
    conv_lhs => rw [← h2']
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hg, h2']
  refine ⟨u * u', v' * v, ?_, ?_, ?_, ?_⟩
  · rw [← Matrix.mul_assoc, heu, Matrix.mul_assoc, hu'g]
  · rw [← Matrix.mul_assoc, hgv', Matrix.mul_assoc, hve]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc u' v' v, h3', ← Matrix.mul_assoc, huf, h3]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc v u u', h4, ← Matrix.mul_assoc, ← h4', Matrix.mul_assoc, hvu']

/-- Ring homomorphisms preserve Karoubi isomorphisms. -/
lemma map {R' : Type*} [Ring R'] (φ : R →+* R') (h : MatKarIso e f) :
    MatKarIso (e.map φ) (f.map φ) := by
  obtain ⟨u, v, h1, h2, h3, h4⟩ := h
  refine ⟨u.map φ, v.map φ, ?_, ?_, ?_, ?_⟩ <;>
    simp only [← Matrix.map_mul, h1, h2, h3, h4]

/-- Block sums of Karoubi isomorphisms. -/
lemma fromBlocks {δ : Type*} [Fintype δ] {e' : Matrix γ γ R} {f' : Matrix δ δ R}
    (h : MatKarIso e f) (h' : MatKarIso e' f') :
    MatKarIso (Matrix.fromBlocks e 0 0 e') (Matrix.fromBlocks f 0 0 f') := by
  obtain ⟨u, v, h1, h2, h3, h4⟩ := h
  obtain ⟨u', v', h1', h2', h3', h4'⟩ := h'
  refine ⟨Matrix.fromBlocks u 0 0 u', Matrix.fromBlocks v 0 0 v', ?_, ?_, ?_, ?_⟩ <;>
    simp [Matrix.fromBlocks_multiply, h1, h2, h3, h4, h1', h2', h3', h4']

end MatKarIso

/-- The matrix of a linear map `imMod e → imMod f`, extended by `x ↦ x ᵥ* e`. -/
def matOf [DecidableEq α] {e : Matrix α α R} {f : Matrix β β R} (φ : imMod e →ₗ[R] imMod f) :
    Matrix α β R :=
  repMat ((imMod f).subtype ∘ₗ φ ∘ₗ (vecMulLin e).rangeRestrict)

lemma vecMul_matOf [DecidableEq α] {e : Matrix α α R} {f : Matrix β β R}
    (φ : imMod e →ₗ[R] imMod f) (x : α → R) :
    x ᵥ* matOf φ = φ ((vecMulLin e).rangeRestrict x) := by
  rw [matOf, ← linearMap_eq_vecMul]
  rfl

lemma vecMul_matOf_of_mem [DecidableEq α] {e : Matrix α α R} {f : Matrix β β R} (he : e * e = e)
    (φ : imMod e →ₗ[R] imMod f) {y : α → R} (hy : y ∈ imMod e) :
    y ᵥ* matOf φ = φ ⟨y, hy⟩ := by
  have : (vecMulLin e).rangeRestrict y = ⟨y, hy⟩ := Subtype.ext (vecMul_eq_self_of_mem he hy)
  rw [vecMul_matOf, this]

lemma vecMul_mem_imMod (e : Matrix α α R) (x : α → R) : x ᵥ* e ∈ imMod e := ⟨x, rfl⟩

lemma rangeRestrict_vecMulLin (e : Matrix α α R) (x : α → R) :
    (vecMulLin e).rangeRestrict x = ⟨x ᵥ* e, vecMul_mem_imMod e x⟩ := rfl

lemma vecMul_matOf_mem [DecidableEq α] {e : Matrix α α R} {f : Matrix β β R}
    (φ : imMod e →ₗ[R] imMod f) (x : α → R) : x ᵥ* matOf φ ∈ imMod f := by
  rw [vecMul_matOf]
  exact Subtype.prop _

/-- One half of `matKarIso_of_linearEquiv`. -/
lemma matKarIso_aux [DecidableEq α] [DecidableEq β] {e : Matrix α α R}
    {f : Matrix β β R} (he : e * e = e) (hf : f * f = f) (φ : imMod e ≃ₗ[R] imMod f) :
    e * matOf φ.toLinearMap * f = matOf φ.toLinearMap ∧
      matOf φ.toLinearMap * matOf φ.symm.toLinearMap = e := by
  refine ⟨eq_of_vecMul_eq fun x ↦ ?_, eq_of_vecMul_eq fun x ↦ ?_⟩
  · rw [← vecMul_vecMul, ← vecMul_vecMul, vecMul_eq_self_of_mem hf (vecMul_matOf_mem _ _),
      vecMul_matOf_of_mem he _ (vecMul_mem_imMod e x), vecMul_matOf, rangeRestrict_vecMulLin]
  · have h1 : (⟨x ᵥ* matOf φ.toLinearMap, vecMul_matOf_mem _ x⟩ : imMod f) =
        φ ((vecMulLin e).rangeRestrict x) := Subtype.ext (vecMul_matOf _ x)
    rw [← vecMul_vecMul, vecMul_matOf_of_mem hf _ (vecMul_matOf_mem _ x), h1]
    simp [rangeRestrict_vecMulLin]

/-- **Module isomorphism ⇒ Karoubi isomorphism.** -/
theorem matKarIso_of_linearEquiv [DecidableEq α] [DecidableEq β] {e : Matrix α α R}
    {f : Matrix β β R} (he : e * e = e) (hf : f * f = f) (φ : imMod e ≃ₗ[R] imMod f) :
    MatKarIso e f := by
  obtain ⟨h1, h3⟩ := matKarIso_aux he hf φ
  obtain ⟨h2, h4⟩ := matKarIso_aux hf he φ.symm
  exact ⟨_, _, h1, h2, h3, h4⟩

/-- The image of a block-diagonal matrix is the product of the images. -/
def imModFromBlocksEquiv (e : Matrix α α R) (f : Matrix β β R) :
    imMod (fromBlocks e 0 0 f) ≃ₗ[R] imMod e × imMod f where
  toFun y := (⟨y.1 ∘ Sum.inl, by
      obtain ⟨x, hx⟩ := y.2
      exact ⟨x ∘ Sum.inl, by rw [← hx]; simp [vecMul_fromBlocks]⟩⟩,
    ⟨y.1 ∘ Sum.inr, by
      obtain ⟨x, hx⟩ := y.2
      exact ⟨x ∘ Sum.inr, by rw [← hx]; simp [vecMul_fromBlocks]⟩⟩)
  invFun p := ⟨Sum.elim p.1.1 p.2.1, by
      obtain ⟨x₁, hx₁⟩ := p.1.2
      obtain ⟨x₂, hx₂⟩ := p.2.2
      rw [vecMulLin_apply] at hx₁ hx₂
      exact ⟨Sum.elim x₁ x₂, by simp [vecMul_fromBlocks, hx₁, hx₂]⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv y := Subtype.ext (by simp)
  right_inv p := by simp

/-- Every finitely generated projective module is the image of an idempotent matrix. -/
theorem exists_idempotent_of_projective (Q : Type*) [AddCommGroup Q] [Module R Q]
    [Module.Finite R Q] [Module.Projective R Q] :
    ∃ (r : ℕ) (e : Matrix (Fin r) (Fin r) R), e * e = e ∧ Nonempty (Q ≃ₗ[R] imMod e) := by
  obtain ⟨r, π, hπ⟩ := Module.Finite.exists_fin' R Q
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π LinearMap.id hπ
  have hσ' : ∀ q, π (σ q) = q := fun q ↦ congrArg (fun g : Q →ₗ[R] Q ↦ g q) hσ
  have hσinj : Function.Injective σ := fun a b h ↦ by rw [← hσ' a, ← hσ' b, h]
  have hP : ∀ x, x ᵥ* repMat (σ ∘ₗ π) = σ (π x) := fun x ↦
    (linearMap_eq_vecMul (σ ∘ₗ π) x).symm
  refine ⟨r, repMat (σ ∘ₗ π), eq_of_vecMul_eq fun x ↦ ?_, ⟨?_⟩⟩
  · rw [← vecMul_vecMul, hP, hP, hσ']
  · refine (LinearEquiv.ofInjective σ hσinj).trans (LinearEquiv.ofEq _ _ ?_)
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨x, rfl⟩ := hπ q
      exact ⟨x, hP x⟩
    · rintro ⟨x, rfl⟩
      exact ⟨π x, (hP x).symm⟩

end Dictionary


/-! ### Localization of images and Theorem R in matrix form -/

section MatrixForm

open Matrix

variable {S S' : Type u} [Ring S] [Ring S'] {ι : S →+* S'} {w : S}

lemma piMap_vecMul {α β : Type*} [Fintype α] (e : Matrix α β S) (x : α → S) :
    piMap ι β (x ᵥ* e) = piMap ι α x ᵥ* e.map ι :=
  funext fun j ↦ RingHom.map_vecMul ι e x j

variable (ι) in
/-- The localization `imMod e → imMod (e.map ι)`, coefficientwise `ι`. -/
def imModLoc {α : Type*} [Fintype α] (e : Matrix α α S) : imMod e →ₛₗ[ι] imMod (e.map ι) :=
  LinearMap.codRestrict _ ((piMap ι α).comp (imMod e).subtype) fun y ↦ by
    obtain ⟨x, hx⟩ := y.2
    exact ⟨piMap ι α x, by
      simp only [vecMulLin_apply, LinearMap.coe_comp, Function.comp_apply,
        Submodule.coe_subtype, ← hx, piMap_vecMul]⟩

lemma isLocMap_imModLoc (hι : IsCentralLoc ι w) {α : Type*} [Fintype α] (e : Matrix α α S) :
    IsLocMap ι w (imModLoc ι e) := by
  refine ⟨fun y' ↦ ?_, fun y hy ↦ ?_⟩
  · obtain ⟨x', hx'⟩ := y'.2
    obtain ⟨x, n, hx⟩ := (isLocMap_piMap hι α).surj x'
    refine ⟨⟨x ᵥ* e, vecMul_mem_imMod e x⟩, n, Subtype.ext ?_⟩
    change ι w ^ n • (y' : α → S') = piMap ι α (x ᵥ* e)
    rw [piMap_vecMul, ← hx, ← hx', vecMulLin_apply, smul_vecMul]
  · obtain ⟨n, hn⟩ := (isLocMap_piMap hι α).ker y (congrArg Subtype.val hy)
    exact ⟨n, Subtype.ext hn⟩

lemma map_idempotent {α : Type*} [Fintype α] {e : Matrix α α S} (he : e * e = e) :
    e.map ι * e.map ι = e.map ι := by
  rw [← Matrix.map_mul, he]

lemma fromBlocks_idempotent {α β : Type*} [Fintype α] [Fintype β] {e : Matrix α α S'}
    {f : Matrix β β S'} (he : e * e = e) (hf : f * f = f) :
    fromBlocks e 0 0 f * fromBlocks e 0 0 f = fromBlocks e 0 0 f := by
  rw [fromBlocks_multiply]
  simp [he, hf]

/-- An abstract localized projective is the localization of an idempotent matrix. -/
lemma LocProj.exists_idempotent (hι : IsCentralLoc ι w) (E : LocProj ι w) :
    ∃ (r : ℕ) (e : Matrix (Fin r) (Fin r) S), e * e = e ∧
      Nonempty (E.Q' ≃ₗ[S'] imMod (e.map ι)) := by
  obtain ⟨r, e, he, ⟨ψ⟩⟩ := exists_idempotent_of_projective (R := S) E.Q
  exact ⟨r, e, he, ⟨locEquiv hι (E.isLocMap.comp_equiv ψ.symm) (isLocMap_imModLoc hι e)⟩⟩

/-- **Theorem R (abstract matrix form).** Under the hypotheses of `theoremR_abstract`, for every
idempotent matrix `e` over `S'` there are idempotent matrices `e₀, e₁` over `S` with
`(S'^α, e) ⊕ ι(S^{r₁}, e₁) ≅ ι(S^{r₀}, e₀)` as Karoubi objects. -/
theorem theoremR_matrix_abstract [IsNoetherianRing S] (hι : IsCentralLoc ι w) {d : ℕ}
    (hgl : GlobalDimLE S d) {α : Type u} [Fintype α] [DecidableEq α] (e : Matrix α α S')
    (he : e * e = e) :
    ∃ (r₀ r₁ : ℕ) (e₀ : Matrix (Fin r₀) (Fin r₀) S) (e₁ : Matrix (Fin r₁) (Fin r₁) S),
      e₀ * e₀ = e₀ ∧ e₁ * e₁ = e₁ ∧
        MatKarIso (fromBlocks e 0 0 (e₁.map ι)) (e₀.map ι) := by
  have := projective_imMod he
  obtain ⟨E₀, E₁, ⟨φ⟩⟩ := theoremR_abstract hι hgl (imMod e)
  obtain ⟨r₀, e₀, he₀, ⟨ψ₀⟩⟩ := E₀.exists_idempotent hι
  obtain ⟨r₁, e₁, he₁, ⟨ψ₁⟩⟩ := E₁.exists_idempotent hι
  refine ⟨r₀, r₁, e₀, e₁, he₀, he₁, matKarIso_of_linearEquiv
    (fromBlocks_idempotent he (map_idempotent he₁)) (map_idempotent he₀) ?_⟩
  exact (imModFromBlocksEquiv e (e₁.map ι)).trans
    ((((LinearEquiv.refl S' _).prodCongr ψ₁.symm).trans φ).trans ψ₀)

end MatrixForm

/-- `|G| ≠ 0` in a field of characteristic zero. -/
instance instNeZeroNatCard (K : Type*) [Field K] [CharZero K] (G : Type*) [Finite G]
    [Nonempty G] :
    NeZero (Nat.card G : K) :=
  ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩

section Final

variable (K : Type u) [Field K] (G : Type u) [Group G] [Fintype G] [NeZero (Nat.card G : K)]

open Matrix in
/-- **Theorem R (matrix form)**, the interface for the Karoubi-level form (N13).

Let `S' = lpRing (n + 1) (K[G])` (`K[G][t₁^±,…,t_{n+1}^±]`, innermost variable `w = t_{n+1}`),
`S = lpRing n (K[G][X])` its faces ring and `faceMap n : S → S'` (`X ↦ w`).  For every idempotent
matrix `e` over `S'` there are idempotent matrices `e₀, e₁` over `S` with
`(S'^α, e) ⊕ (S'^{r₁}, faceMap e₁) ≅ (S'^{r₀}, faceMap e₀)` as Karoubi objects of the matrix
category over `S'` (composition `A ≫ B = A * B`, i.e. maps act by `x ↦ x ᵥ* A`). -/
theorem theoremR_matrix (n : ℕ) {α : Type u} [Fintype α] [DecidableEq α]
    (e : Matrix α α (FullRing K G n)) (he : e * e = e) :
    ∃ (r₀ r₁ : ℕ) (e₀ : Matrix (Fin r₀) (Fin r₀) (FaceRing K G n))
      (e₁ : Matrix (Fin r₁) (Fin r₁) (FaceRing K G n)),
      e₀ * e₀ = e₀ ∧ e₁ * e₁ = e₁ ∧
        MatKarIso (fromBlocks e 0 0 (e₁.map (faceMap n (RingCat.of (MonoidAlgebra K G)))))
          (e₀.map (faceMap n (RingCat.of (MonoidAlgebra K G)))) :=
  theoremR_matrix_abstract (isCentralLoc_faceMap n _) (globalDimLE_faceRing K G n) e he

end Final


/-- Usage at a fibre of `finSuppFreeQG G T` (`K = ℚ`, `Λᵢ = ℚ[G i]`). -/
example (G : ℕ → Type) [∀ i, Group (G i)] [∀ i, Fintype (G i)] (i n m : ℕ)
    (e : Matrix (Fin m) (Fin m) (FullRing ℚ (G i) n)) (he : e * e = e) :
    ∃ (r₀ r₁ : ℕ) (e₀ : Matrix (Fin r₀) (Fin r₀) (FaceRing ℚ (G i) n))
      (e₁ : Matrix (Fin r₁) (Fin r₁) (FaceRing ℚ (G i) n)),
      e₀ * e₀ = e₀ ∧ e₁ * e₁ = e₁ ∧
        MatKarIso (Matrix.fromBlocks e 0 0 (e₁.map (faceMap n (RingCat.of (MonoidAlgebra ℚ (G i))))))
          (e₀.map (faceMap n (RingCat.of (MonoidAlgebra ℚ (G i))))) :=
  theoremR_matrix ℚ (G i) n e he

end HSFormal.LTheory.Reg
