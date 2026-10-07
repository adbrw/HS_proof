import HSFormal.LTheory.Isometry
import HSFormal.SignatureRing

/-!
# The middle form and `Sign_G` of a symmetric Poincaré complex (L-theory module M9a)

`PermRep G S`: the based permutation modules `ℚ^{Fin n × S}` of a group `G` acting on `S`, with
`G`-equivariant matrices as morphisms and transpose as strict involution `PermRep.inv G S`.  For
`S = G` this is `Free(ℚ[G])` with the duality of manuscript (3.2): in the free basis, rational
transpose is the group-ring adjoint (`regMatrix_transpose`), with no factor `1 / |G|`.

For `P = (C, p, φ) : SymPoincare (PermRep.inv G S) N` and `m = N - m`, the middle form lives on the
Kar cohomology `H^m(C, p) = H_m(C^{N-*}, p^*)` (`SymPoincare.middle`, cycles modulo boundaries and
`ker p^*`): `b([x], [y]) = ⟨x, φ y⟩` (`pairing`).  It is `G`-invariant, `(-1)^m`-symmetric
(`pairing_swap`) and nondegenerate by Poincaré duality (`mem_karBoundaries_of_pairing`).
`SymPoincare.sign` is `Sign_G` of this form (manuscript (3.1)); it is invariant under homotopy
isometries (`sign_eq_of_isometry`), additive (`sign_sum`), odd (`sign_neg`), and its value at `1`
is the ordinary signature (`sign_one`).  Isometry invariance and additivity use that an isometric
map out of a nondegenerate space is injective, so isometric maps both ways are isomorphisms
(`ratEquivariantSignature_eq_of_isometries`); no inverse on homology has to be constructed.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression
open LinearMap (BilinForm)
open scoped Matrix

noncomputable section

section RatSign

variable {G V₁ V₂ : Type*} [Group G] [AddCommGroup V₁] [Module ℚ V₁] [FiniteDimensional ℚ V₁]
  [AddCommGroup V₂] [Module ℚ V₂] [FiniteDimensional ℚ V₂] {ρ₁ : Representation ℚ G V₁}
  {ρ₂ : Representation ℚ G V₂} {b₁ : BilinForm ℚ V₁} {b₂ : BilinForm ℚ V₂}

/-- The rational `Sign_G` is an isometry invariant. -/
theorem ratEquivariantSignature_congr [Finite G] (hb₁ : IsInvariantForm ρ₁ b₁) (e : V₁ ≃ₗ[ℚ] V₂)
    (he : ∀ g v, e (ρ₁ g v) = ρ₂ g (e v)) (hbe : ∀ v w, b₂ (e v) (e w) = b₁ v w) :
    ratEquivariantSignature ρ₂ b₂ = ratEquivariantSignature ρ₁ b₁ := by
  refine equivariantSignature_congr hb₁.baseChange (e.baseChange ℚ ℝ V₁ V₂) (fun g x ↦ ?_)
    fun x y ↦ ?_
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, hx, hx']
    | tmul a v => simp [LinearEquiv.baseChange_tmul, he]
  · have h : (BilinForm.baseChange ℝ b₂).compl₁₂ (e.baseChange ℚ ℝ V₁ V₂).toLinearMap
        (e.baseChange ℚ ℝ V₁ V₂).toLinearMap = BilinForm.baseChange ℝ b₁ :=
      bilin_baseChange_ext fun v w ↦ by simp [hbe]
    exact LinearMap.congr_fun₂ h x y

omit [FiniteDimensional ℚ V₁] [FiniteDimensional ℚ V₂] in
/-- An isometric map out of a nondegenerate space is injective. -/
lemma injective_of_isometry {f : V₁ →ₗ[ℚ] V₂} (hb₁ : LinearMap.SeparatingLeft b₁)
    (hf : ∀ x y, b₂ (f x) (f y) = b₁ x y) : Function.Injective f :=
  (injective_iff_map_eq_zero f).mpr fun x hx ↦ hb₁ x fun y ↦ by rw [← hf, hx, map_zero,
    LinearMap.zero_apply]

/-- Isometric maps in both directions between nondegenerate invariant forms, one of them
equivariant, force equal signatures. -/
theorem ratEquivariantSignature_eq_of_isometries [Finite G] (hb₁ : IsInvariantForm ρ₁ b₁)
    (hb₂ : IsInvariantForm ρ₂ b₂) (f : V₁ →ₗ[ℚ] V₂) (g : V₂ →ₗ[ℚ] V₁)
    (hf : ∀ x y, b₂ (f x) (f y) = b₁ x y) (hg : ∀ x y, b₁ (g x) (g y) = b₂ x y)
    (hfρ : ∀ σ v, f (ρ₁ σ v) = ρ₂ σ (f v)) :
    ratEquivariantSignature ρ₂ b₂ = ratEquivariantSignature ρ₁ b₁ := by
  have hfi := injective_of_isometry hb₁.nondegenerate.1 hf
  have hd := le_antisymm (LinearMap.finrank_le_finrank_of_injective hfi)
    (LinearMap.finrank_le_finrank_of_injective (injective_of_isometry hb₂.nondegenerate.1 hg))
  exact ratEquivariantSignature_congr hb₁ (.ofBijective f
    ⟨hfi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hfi⟩) hfρ hf

end RatSign

/-- A bilinear form vanishing on `W` in each argument descends to `V ⧸ W`. -/
def liftQ₂ {V : Type*} [AddCommGroup V] [Module ℚ V] (B : BilinForm ℚ V) (W : Submodule ℚ V)
    (h₁ : ∀ x ∈ W, ∀ y, B x y = 0) (h₂ : ∀ x, ∀ y ∈ W, B x y = 0) : BilinForm ℚ (V ⧸ W) :=
  W.liftQ (W.liftQ B.flip fun y hy ↦ LinearMap.ext fun x ↦ h₂ x y hy).flip fun x hx ↦
    Submodule.linearMap_qext _ (LinearMap.ext fun y ↦ h₁ x hx y)

@[simp]
lemma liftQ₂_mk {V : Type*} [AddCommGroup V] [Module ℚ V] (B : BilinForm ℚ V) (W : Submodule ℚ V)
    (h₁ h₂) (x y : V) :
    liftQ₂ B W h₁ h₂ (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = B x y := rfl

/-- `(ker M)^⊥ = range Mᵀ` for the dot product. -/
lemma exists_transpose_mulVec_eq {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] (M : Matrix κ ι ℚ) {v : ι → ℚ} (h : ∀ u, M *ᵥ u = 0 → v ⬝ᵥ u = 0) :
    ∃ w, Mᵀ *ᵥ w = v := by
  have hv : dotProductEquiv ℚ ι v ∈ (LinearMap.ker M.mulVecLin).dualAnnihilator :=
    (Submodule.mem_dualAnnihilator _).mpr fun u hu ↦ h u hu
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hv
  obtain ⟨χ, hχ⟩ := hv
  obtain ⟨w, rfl⟩ := (dotProductEquiv ℚ κ).surjective χ
  refine ⟨w, (dotProductEquiv ℚ ι).injective (LinearMap.ext fun u ↦ ?_)⟩
  rw [← hχ]
  simp [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]

lemma units_smul_mem {V : Type*} [AddCommGroup V] [Module ℚ V] {W : Submodule ℚ V} (u : ℤˣ)
    {x : V} (hx : x ∈ W) : u • x ∈ W := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp [hx]

/-- The based permutation modules `ℚ^{Fin n × S}` of a group `G` acting on `S`; for `S = G` these
are the free modules `ℚ[G]^n`. -/
@[ext]
structure PermRep (G S : Type) where
  /-- The number of copies of `ℚ^S`. -/
  rank : ℕ

namespace PermRep

variable {G S : Type} [Group G] [MulAction G S]

/-- The basis `Fin n × S`. -/
abbrev Idx (X : PermRep G S) : Type := Fin X.rank × S

/-- The underlying rational vector space. -/
abbrev Sp (X : PermRep G S) : Type := X.Idx → ℚ

/-- `G` permutes the basis. -/
def act (X : PermRep G S) : Representation ℚ G X.Sp where
  toFun g := LinearMap.funLeft ℚ ℚ fun x : X.Idx ↦ (x.1, g⁻¹ • x.2)
  map_one' := LinearMap.ext fun _ ↦ funext fun _ ↦ by simp
  map_mul' g h := LinearMap.ext fun _ ↦ funext fun _ ↦ by simp [mul_smul]

@[simp]
lemma act_apply (X : PermRep G S) (g : G) (v : X.Sp) (x : X.Idx) :
    X.act g v x = v (x.1, g⁻¹ • x.2) := rfl

variable [Fintype S]

lemma dotProduct_act (X : PermRep G S) (g : G) (v w : X.Sp) :
    X.act g v ⬝ᵥ X.act g w = v ⬝ᵥ w :=
  Fintype.sum_equiv ((Equiv.refl _).prodCongr (MulAction.toPerm g⁻¹)) _ _ fun _ ↦ rfl

/-- The `G`-equivariant matrices `ℚ^X → ℚ^Y`. -/
def homSubmodule (X Y : PermRep G S) : Submodule ℚ (Matrix Y.Idx X.Idx ℚ) where
  carrier := {M | ∀ (g : G) i s j t, M (i, g • s) (j, g • t) = M (i, s) (j, t)}
  add_mem' ha hb g i s j t := by simp [ha g i s j t, hb g i s j t]
  zero_mem' := by simp
  smul_mem' c M h g i s j t := by simp [h g i s j t]

lemma mul_mem_homSubmodule {X Y Z : PermRep G S} {A : Matrix Z.Idx Y.Idx ℚ}
    {B : Matrix Y.Idx X.Idx ℚ} (hA : A ∈ homSubmodule Y Z) (hB : B ∈ homSubmodule X Y) :
    A * B ∈ homSubmodule X Z := fun g i s k u ↦
  (Fintype.sum_equiv ((Equiv.refl _).prodCongr (MulAction.toPerm g)) _ _ fun ⟨j, t⟩ ↦ by
    simp [hA g i s j t, hB g j t k u]).symm

variable [DecidableEq S]

instance : Category (PermRep G S) where
  Hom X Y := homSubmodule X Y
  id X := ⟨1, fun g i s j t ↦ by simp [Matrix.one_apply, Prod.ext_iff]⟩
  comp f g := ⟨g.1 * f.1, mul_mem_homSubmodule g.2 f.2⟩
  id_comp f := Subtype.ext (Matrix.mul_one _)
  comp_id f := Subtype.ext (Matrix.one_mul _)
  assoc f g h := Subtype.ext (Matrix.mul_assoc _ _ _).symm

variable {X Y Z : PermRep G S}

@[ext]
lemma hom_ext {f g : X ⟶ Y} (h : f.1 = g.1) : f = g := Subtype.ext h

@[simp] lemma comp_val (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).1 = g.1 * f.1 := rfl

@[simp] lemma id_val (X : PermRep G S) : (𝟙 X : X ⟶ X).1 = 1 := rfl

instance : Preadditive (PermRep G S) where
  homGroup X Y := inferInstanceAs (AddCommGroup (homSubmodule X Y))
  add_comp _ _ _ _ _ _ := Subtype.ext (Matrix.mul_add _ _ _)
  comp_add _ _ _ _ _ _ := Subtype.ext (Matrix.add_mul _ _ _)

instance : Linear ℚ (PermRep G S) where
  homModule X Y := inferInstanceAs (Module ℚ (homSubmodule X Y))
  smul_comp _ _ _ _ _ _ := Subtype.ext (Matrix.mul_smul _ _ _)
  comp_smul _ _ _ _ _ _ := Subtype.ext (Matrix.smul_mul _ _ _)

variable (G S) in
/-- Transpose: the duality of `Free(ℚ[G])` in a free basis (manuscript (3.2)). -/
def inv : StrictInvolution (PermRep G S) where
  star f := ⟨f.1ᵀ, fun g i s j t ↦ f.2 g j t i s⟩
  star_comp _ _ := Subtype.ext (Matrix.transpose_mul _ _)
  star_id _ := Subtype.ext Matrix.transpose_one
  star_add _ _ := Subtype.ext (Matrix.transpose_add _ _)
  star_star _ := Subtype.ext (Matrix.transpose_transpose _)

@[simp] lemma star_val (f : X ⟶ Y) : ((inv G S).star f).1 = f.1ᵀ := rfl

/-- The `ℚ[G]`-matrix `A_ij = ∑_g f_{(i,1),(j,g)} g` of an endomorphism of `ℚ[G]^n`. -/
def groupMatrix [Fintype G] [DecidableEq G] {X : PermRep G G} (f : X ⟶ X) :
    Matrix (Fin X.rank) (Fin X.rank) (MonoidAlgebra ℚ G) :=
  Matrix.of fun i j ↦ MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun g ↦ f.1 (i, 1) (j, g))

/-- Manuscript (3.2): in the free basis `(i, g)` of `ℚ[G]^n` a morphism is the regular matrix of
its `ℚ[G]`-matrix, and the involution (transpose) is the group-ring adjoint `g ↦ g⁻¹`. -/
lemma val_eq_regMatrix [Fintype G] [DecidableEq G] {X : PermRep G G} (f : X ⟶ X) :
    f.1 = (regMatrix (groupMatrix f)).submatrix Prod.swap Prod.swap ∧
      ((inv G G).star f).1 = (regMatrix (groupAdjoint (groupMatrix f))).submatrix Prod.swap
        Prod.swap := by
  have h : f.1 = (regMatrix (groupMatrix f)).submatrix Prod.swap Prod.swap := by
    ext ⟨i, s⟩ ⟨j, t⟩
    simpa [regMatrix, groupMatrix] using (f.2 s⁻¹ i s j t).symm
  refine ⟨h, ?_⟩
  rw [star_val, h, Matrix.transpose_submatrix, regMatrix_transpose]

/-- The underlying linear map. -/
def toLin (f : X ⟶ Y) : X.Sp →ₗ[ℚ] Y.Sp := Matrix.mulVecLin f.1

lemma toLin_apply (f : X ⟶ Y) (v : X.Sp) : toLin f v = f.1 *ᵥ v := rfl

@[simp]
lemma toLin_comp (f : X ⟶ Y) (g : Y ⟶ Z) (v : X.Sp) : toLin (f ≫ g) v = toLin g (toLin f v) :=
  (Matrix.mulVec_mulVec _ _ _).symm

@[simp] lemma toLin_id (v : X.Sp) : toLin (𝟙 X) v = v := Matrix.one_mulVec v

@[simp]
lemma toLin_add (f g : X ⟶ Y) (v : X.Sp) : toLin (f + g) v = toLin f v + toLin g v :=
  Matrix.add_mulVec _ _ _

@[simp] lemma toLin_zero (v : X.Sp) : toLin (0 : X ⟶ Y) v = 0 := Matrix.zero_mulVec v

@[simp]
lemma toLin_neg (f : X ⟶ Y) (v : X.Sp) : toLin (-f) v = -toLin f v := Matrix.neg_mulVec _ _

@[simp]
lemma toLin_units_smul (u : ℤˣ) (f : X ⟶ Y) (v : X.Sp) : toLin (u • f) v = u • toLin f v := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp

lemma toLin_eqToHom_trans {X' : PermRep G S} (h : X = Y) (h' : Y = X') (v : X.Sp) :
    toLin (eqToHom h') (toLin (eqToHom h) v) = toLin (eqToHom (h.trans h')) v := by
  rw [← toLin_comp, eqToHom_trans]

lemma toLin_comp_eq {Y' : PermRep G S} {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X ⟶ Y'} {g' : Y' ⟶ Z}
    (h : f ≫ g = f' ≫ g') (v : X.Sp) : toLin g (toLin f v) = toLin g' (toLin f' v) := by
  rw [← toLin_comp, h, toLin_comp]

/-- `⟨f^* x, y⟩ = ⟨x, f y⟩`. -/
lemma toLin_star_dotProduct (f : X ⟶ Y) (x : Y.Sp) (y : X.Sp) :
    toLin ((inv G S).star f) x ⬝ᵥ y = x ⬝ᵥ toLin f y := by
  simp [toLin_apply, Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]

lemma dotProduct_toLin_star (f : X ⟶ Y) (x : X.Sp) (y : Y.Sp) :
    x ⬝ᵥ toLin ((inv G S).star f) y = toLin f x ⬝ᵥ y := by
  rw [dotProduct_comm, toLin_star_dotProduct, dotProduct_comm]

/-- Morphisms are equivariant. -/
lemma toLin_act (f : X ⟶ Y) (g : G) (v : X.Sp) : toLin f (X.act g v) = Y.act g (toLin f v) := by
  funext ⟨i, s⟩
  simp only [toLin_apply, act_apply, Matrix.mulVec, dotProduct]
  exact Fintype.sum_equiv ((Equiv.refl _).prodCongr (MulAction.toPerm g⁻¹)) _ _ fun ⟨j, t⟩ ↦ by
    simp [f.2 g⁻¹ i s j t]

section KarHomology

variable (E : ChainComplex (PermRep G S) ℤ) (e : E ⟶ E) (r : ℤ)

/-- The cycles `ker d_r`. -/
def cycles : Submodule ℚ (E.X r).Sp :=
  LinearMap.ker (toLin (E.d r (r - 1)))

/-- Boundaries plus `ker e`: the cycles vanishing in the homology of the Kar complex `(E, e)`. -/
def karBoundaries : Submodule ℚ (E.X r).Sp :=
  LinearMap.range (toLin (E.d (r + 1) r)) ⊔ LinearMap.ker (toLin (e.f r))

/-- The homology `H_r(E, e)` of the Kar complex `(E, e)`: cycles modulo `karBoundaries`.  For a
chain idempotent `e` this is the homology of the subcomplex `im e` (`z ↦ e z`). -/
abbrev karHomology : Type :=
  cycles E r ⧸ (karBoundaries E e r).comap (cycles E r).subtype

lemma act_mem_cycles (g : G) {x : (E.X r).Sp} (hx : x ∈ cycles E r) :
    (E.X r).act g x ∈ cycles E r := by
  rw [cycles, LinearMap.mem_ker] at hx ⊢
  rw [toLin_act, hx, map_zero]

lemma act_mem_karBoundaries (g : G) {x : (E.X r).Sp} (hx : x ∈ karBoundaries E e r) :
    (E.X r).act g x ∈ karBoundaries E e r := by
  obtain ⟨_, ⟨w, rfl⟩, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add, ← toLin_act]
  refine Submodule.add_mem_sup ⟨_, rfl⟩ ?_
  rw [LinearMap.mem_ker] at hz ⊢
  rw [toLin_act, hz, map_zero]

/-- The representation of `G` on `H_r(E, e)`. -/
def karRep : Representation ℚ G (karHomology E e r) :=
  ((E.X r).act.subrepresentation _ fun g _ ↦ act_mem_cycles E r g).quotient _
    fun g _ hx ↦ act_mem_karBoundaries E e r g hx

variable {E e} {E' : ChainComplex (PermRep G S) ℤ} {e' : E' ⟶ E'}

lemma toLin_mem_cycles (h : E ⟶ E') {x : (E.X r).Sp} (hx : x ∈ cycles E r) :
    toLin (h.f r) x ∈ cycles E' r := by
  rw [cycles, LinearMap.mem_ker] at hx ⊢
  rw [← toLin_comp, h.comm, toLin_comp, hx, map_zero]

lemma toLin_mem_karBoundaries (h : E ⟶ E') (hh : e ≫ h = h ≫ e') {x : (E.X r).Sp}
    (hx : x ∈ karBoundaries E e r) : toLin (h.f r) x ∈ karBoundaries E' e' r := by
  obtain ⟨_, ⟨w, rfl⟩, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add, ← toLin_comp, ← h.comm, toLin_comp]
  refine Submodule.add_mem_sup ⟨_, rfl⟩ ?_
  rw [LinearMap.mem_ker] at hz ⊢
  rw [← toLin_comp, ← comp_f, ← hh, comp_f, toLin_comp, hz, map_zero]

/-- The map on Kar homology induced by a chain map `h` with `e h = h e'`. -/
def karMap (h : E ⟶ E') (hh : e ≫ h = h ≫ e') : karHomology E e r →ₗ[ℚ] karHomology E' e' r :=
  Submodule.mapQ _ _ ((toLin (h.f r)).restrict fun _ ↦ toLin_mem_cycles r h)
    fun _ hx ↦ toLin_mem_karBoundaries r h hh hx

@[simp]
lemma karMap_mk (h : E ⟶ E') (hh : e ≫ h = h ≫ e') (x : cycles E r) :
    karMap r h hh (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨toLin (h.f r) x, toLin_mem_cycles r h x.2⟩ := rfl

lemma karMap_karRep (h : E ⟶ E') (hh : e ≫ h = h ≫ e') (g : G) (x : karHomology E e r) :
    karMap r h hh (karRep E e r g x) = karRep E' e' r g (karMap r h hh x) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk (Subtype.ext (toLin_act (h.f r) g x.1))

end KarHomology

section Pairing

variable {N : ℤ} {C C' : ChainComplex (PermRep G S) ℤ} (m : ℤ) (hm : m = N - m)

/-- `d^*` is the dual differential up to the sign `(-1)^r`. -/
lemma star_d (r r' : ℤ) :
    (inv G S).star (C.d (N - r') (N - r)) = r.negOnePow • (dualComplex (inv G S) N C).d r r' := by
  rw [dualComplex_d, smul_smul, Int.units_mul_self, one_smul]

/-- The Kronecker pairing of a middle cocycle with a boundary vanishes. -/
lemma dotProduct_d_eq_zero {x : (C.X (N - m)).Sp} (hx : x ∈ cycles (dualComplex (inv G S) N C) m)
    (z : (C.X (N - (m - 1))).Sp) : x ⬝ᵥ toLin (C.d (N - (m - 1)) (N - m)) z = 0 := by
  have h : toLin ((inv G S).star (C.d (N - (m - 1)) (N - m))) x = 0 := by
    have h := LinearMap.mem_ker.mp hx
    rw [dualComplex_d] at h
    erw [toLin_units_smul, smul_eq_zero_iff_eq] at h
    exact h
  rw [← toLin_star_dotProduct, h, zero_dotProduct]

/-- The middle pairing `⟨x, φ y⟩` on `C^{N-*}_m = C_{N-m}`, using `m = N - m`. -/
def pairing (φ : dualComplex (inv G S) N C ⟶ C) : BilinForm ℚ (C.X (N - m)).Sp :=
  LinearMap.mk₂ ℚ
    (fun x y ↦ x ⬝ᵥ
      toLin (φ.f (N - m)) (toLin (eqToHom (congrArg (dualComplex (inv G S) N C).X hm)) y))
    (fun _ _ _ ↦ add_dotProduct _ _ _) (fun _ _ _ ↦ smul_dotProduct _ _ _)
    (fun _ _ _ ↦ by simp [dotProduct_add]) (fun _ _ _ ↦ by simp [dotProduct_smul])

lemma pairing_apply (φ : dualComplex (inv G S) N C ⟶ C) (x y : (C.X (N - m)).Sp) :
    pairing m hm φ x y =
      x ⬝ᵥ toLin (φ.f (N - m)) (toLin (eqToHom (congrArg (dualComplex (inv G S) N C).X hm)) y) :=
  rfl

lemma pairing_add (φ φ' : dualComplex (inv G S) N C ⟶ C) :
    pairing m hm (φ + φ') = pairing m hm φ + pairing m hm φ' :=
  LinearMap.ext₂ fun x y ↦ by
    rw [LinearMap.add_apply, LinearMap.add_apply, pairing_apply, pairing_apply, pairing_apply,
      add_f_apply, toLin_add, dotProduct_add]

lemma pairing_neg (φ : dualComplex (inv G S) N C ⟶ C) : pairing m hm (-φ) = -pairing m hm φ :=
  LinearMap.ext₂ fun x y ↦ by
    rw [LinearMap.neg_apply, LinearMap.neg_apply, pairing_apply, pairing_apply, neg_f_apply,
      toLin_neg, dotProduct_neg]

lemma pairing_act (φ : dualComplex (inv G S) N C ⟶ C) (g : G) (x y : (C.X (N - m)).Sp) :
    pairing m hm φ ((C.X (N - m)).act g x) ((C.X (N - m)).act g y) = pairing m hm φ x y := by
  rw [pairing_apply, pairing_apply]
  erw [toLin_act, toLin_act]
  exact dotProduct_act _ g _ _

lemma pairing_d (φ : dualComplex (inv G S) N C ⟶ C) {x}
    (hx : x ∈ cycles (dualComplex (inv G S) N C) m) (z) :
    pairing m hm φ x (toLin ((dualComplex (inv G S) N C).d (m + 1) m) z) = 0 := by
  rw [pairing_apply, toLin_comp_eq (eqToHom_naturality₂ (dualComplex (inv G S) N C).d
    (show m + 1 = N - (m - 1) by omega) hm), toLin_comp_eq (φ.comm _ _).symm]
  exact dotProduct_d_eq_zero m hx _

lemma pairing_kar {p : C ⟶ C} (φ : dualComplex (inv G S) N C ⟶ C)
    (hφ : dualHom (inv G S) N p ≫ φ = φ) (x) {y}
    (hy : y ∈ LinearMap.ker (toLin ((dualHom (inv G S) N p).f m))) : pairing m hm φ x y = 0 := by
  have h : ∀ w, toLin (φ.f (N - m)) w =
      toLin (φ.f (N - m)) (toLin ((dualHom (inv G S) N p).f (N - m)) w) := fun w ↦ by
    rw [← toLin_comp, ← comp_f, hφ]
  rw [pairing_apply, h, ← toLin_comp_eq (f_comp_eqToHom (dualHom (inv G S) N p) hm),
    LinearMap.mem_ker.mp hy, map_zero, map_zero, dotProduct_zero]

/-- `T φ = φ` makes the middle pairing `(-1)^{m(N-m)}`-symmetric. -/
lemma pairing_swap (φ : dualComplex (inv G S) N C ⟶ C) (hφ : IsStrictSymm (inv G S) N φ)
    (x y : (C.X (N - m)).Sp) :
    pairing m hm φ x y = (m * (N - m)).negOnePow • pairing m hm φ y x := by
  have hT : φ.f m = (m * (N - m)).negOnePow • ((inv G S).star (φ.f (N - m)) ≫
      eqToHom (congrArg C.X (sub_sub_cancel N m))) := by
    conv_lhs => rw [← hφ]
    exact transposeHom_f φ m
  rw [pairing_apply, ← toLin_comp_eq (f_comp_eqToHom φ hm), ← toLin_star_dotProduct,
    star_eqToHom, hT, toLin_units_smul, dotProduct_smul, toLin_comp, ← toLin_star_dotProduct]
  erw [star_eqToHom, toLin_eqToHom_trans, dotProduct_toLin_star, dotProduct_comm]
  rfl

/-- `⟨x, f φ f^* y⟩ = ⟨f^* x, φ f^* y⟩`. -/
lemma pairing_conj (f : C' ⟶ C) (φ : dualComplex (inv G S) N C' ⟶ C') (x y : (C.X (N - m)).Sp) :
    pairing m hm (dualHom (inv G S) N f ≫ φ ≫ f) x y =
      pairing m hm φ (toLin ((dualHom (inv G S) N f).f m) x)
        (toLin ((dualHom (inv G S) N f).f m) y) := by
  rw [pairing_apply, comp_f, comp_f, toLin_comp, toLin_comp,
    ← toLin_comp_eq (f_comp_eqToHom (dualHom (inv G S) N f) hm), ← toLin_star_dotProduct]
  rfl

/-- Homotopic structures give the same pairing on middle cocycles. -/
lemma pairing_homotopy {φ φ' : dualComplex (inv G S) N C ⟶ C} (H : Homotopy φ φ') {x y}
    (hx : x ∈ cycles (dualComplex (inv G S) N C) m)
    (hy : y ∈ cycles (dualComplex (inv G S) N C) m) :
    pairing m hm φ x y = pairing m hm φ' x y := by
  have hc := H.comm (N - m)
  rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel (N - m) (N - (m + 1)) by simp; omega),
    prevD_eq _ (show (ComplexShape.down ℤ).Rel (N - (m - 1)) (N - m) by simp; omega)] at hc
  rw [pairing_apply, pairing_apply, hc, toLin_add, toLin_add, dotProduct_add, dotProduct_add,
    toLin_comp, toLin_comp, ← toLin_comp_eq (eqToHom_naturality₂ (dualComplex (inv G S) N C).d hm
      (show m - 1 = N - (m + 1) by omega)), LinearMap.mem_ker.mp hy, map_zero, map_zero,
    dotProduct_zero, zero_add, dotProduct_d_eq_zero m hx, zero_add]

end Pairing

end PermRep

open PermRep

namespace SymPoincare

variable {G S : Type} [Group G] [MulAction G S] [Fintype S] [DecidableEq S] {N : ℤ}
  (P Q : SymPoincare (inv G S) N) (m : ℤ) (hm : m = N - m)

/-- Poincaré duality: a middle cocycle orthogonal to all middle cocycles vanishes in
`H^m(C, p)`.  With `ψ φ ≃ p`, `⟨p^* x, z⟩ = ⟨x, φ ψ z⟩ = 0` for every cycle `z` of `C_{N-m}`,
so `p^* x ∈ (ker d)^⊥ = im d^*`. -/
theorem mem_karBoundaries_of_pairing {x : ((dualComplex (inv G S) N P.C).X m).Sp}
    (hx : x ∈ PermRep.cycles (dualComplex (inv G S) N P.C) m)
    (h : ∀ y ∈ PermRep.cycles (dualComplex (inv G S) N P.C) m, pairing m hm P.φ x y = 0) :
    x ∈ karBoundaries (dualComplex (inv G S) N P.C) (dualHom (inv G S) N P.p) m := by
  obtain ⟨ψ, -, ⟨H⟩, -⟩ := P.poincare
  have hc := H.comm (N - m)
  rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel (N - m) (N - (m + 1)) by simp; omega),
    prevD_eq _ (show (ComplexShape.down ℤ).Rel (N - (m - 1)) (N - m) by simp; omega)] at hc
  have key : ∀ z, (P.C.d (N - m) (N - (m + 1))).1 *ᵥ z = 0 →
      toLin ((dualHom (inv G S) N P.p).f m) x ⬝ᵥ z = 0 := by
    intro z hz
    replace hz : toLin (P.C.d (N - m) (N - (m + 1))) z = 0 := hz
    have hy : toLin (eqToHom (congrArg (dualComplex (inv G S) N P.C).X hm.symm))
        (toLin (ψ.f (N - m)) z) ∈ PermRep.cycles (dualComplex (inv G S) N P.C) m := by
      rw [PermRep.cycles, LinearMap.mem_ker, toLin_comp_eq (eqToHom_naturality₂
        (dualComplex (inv G S) N P.C).d hm.symm (show N - (m + 1) = m - 1 by omega)).symm,
        toLin_comp_eq (ψ.comm _ _), hz, map_zero, map_zero]
    have := h _ hy
    rw [pairing_apply, toLin_eqToHom_trans, eqToHom_refl, toLin_id, ← toLin_comp, ← comp_f, hc,
      toLin_add, toLin_add, dotProduct_add, dotProduct_add, toLin_comp, hz, map_zero,
      dotProduct_zero, zero_add, toLin_comp, dotProduct_d_eq_zero m hx, zero_add] at this
    rw [dualHom_f]
    erw [toLin_star_dotProduct]
    exact this
  obtain ⟨w, hw⟩ := exists_transpose_mulVec_eq _ key
  have hq : toLin ((dualHom (inv G S) N P.p).f m) x ∈
      LinearMap.range (toLin ((dualComplex (inv G S) N P.C).d (m + 1) m)) := by
    rw [← hw, ← star_val, ← toLin_apply, star_d]
    erw [toLin_units_smul]
    exact units_smul_mem _ ⟨w, rfl⟩
  have hqq : toLin ((dualHom (inv G S) N P.p).f m) (toLin ((dualHom (inv G S) N P.p).f m) x) =
      toLin ((dualHom (inv G S) N P.p).f m) x := by
    rw [← toLin_comp, ← comp_f, ← dualHom_comp, P.p_idem]
  have := Submodule.add_mem_sup hq (show x - toLin ((dualHom (inv G S) N P.p).f m) x ∈
    LinearMap.ker (toLin ((dualHom (inv G S) N P.p).f m)) by
      rw [LinearMap.mem_ker, map_sub, hqq, sub_self])
  rwa [add_sub_cancel] at this

/-- The Kar cohomology `H^m(C, p) = H_m(C^{N-*}, p^*)`, which carries the middle form. -/
abbrev middle : Type :=
  karHomology (dualComplex (inv G S) N P.C) (dualHom (inv G S) N P.p) m

/-- The `G`-action on `H^m(C, p)`. -/
abbrev middleRep : Representation ℚ G (P.middle m) :=
  karRep _ _ m

lemma pairing_karBoundaries {x y : (P.C.X (N - m)).Sp}
    (hx : x ∈ PermRep.cycles (dualComplex (inv G S) N P.C) m)
    (hy : y ∈ karBoundaries (dualComplex (inv G S) N P.C) (dualHom (inv G S) N P.p) m) :
    pairing m hm P.φ x y = 0 := by
  obtain ⟨_, ⟨w, rfl⟩, z, hz, rfl⟩ := Submodule.mem_sup.mp hy
  rw [map_add, pairing_d m hm _ hx, pairing_kar m hm _ P.dualHom_p_comp_φ _ hz, add_zero]

/-- The middle form `b([x], [y]) = ⟨x, φ y⟩` on `H^m(C, p)`. -/
def middleForm : BilinForm ℚ (P.middle m) :=
  liftQ₂ ((pairing m hm P.φ).compl₁₂ (PermRep.cycles (dualComplex (inv G S) N P.C) m).subtype
    (PermRep.cycles (dualComplex (inv G S) N P.C) m).subtype) _
    (fun x hx y ↦ by
      change pairing m hm P.φ x.1 y.1 = 0
      rw [pairing_swap m hm _ P.symm, show pairing m hm P.φ y.1 x.1 = 0 from
        P.pairing_karBoundaries m hm y.2 hx, smul_zero])
    (fun x y hy ↦ P.pairing_karBoundaries m hm x.2 hy)

lemma middleForm_mk (x y : PermRep.cycles (dualComplex (inv G S) N P.C) m) :
    P.middleForm m hm (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      pairing m hm P.φ x.1 y.1 := rfl

/-- The middle form is `(-1)^m`-symmetric. -/
theorem middleForm_swap (u v : P.middle m) :
    P.middleForm m hm u v = m.negOnePow • P.middleForm m hm v u := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  have hε : (m * (N - m)).negOnePow = m.negOnePow := by rw [← hm, Int.negOnePow_mul_self]
  rw [middleForm_mk, middleForm_mk, pairing_swap m hm _ P.symm, hε]

/-- The middle form is nondegenerate (Poincaré duality). -/
theorem middleForm_nondegenerate : (P.middleForm m hm).Nondegenerate := by
  have hl : LinearMap.SeparatingLeft (P.middleForm m hm) := fun u hu ↦ by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    exact (Submodule.Quotient.mk_eq_zero _).mpr (P.mem_karBoundaries_of_pairing m hm x.2
      fun y hy ↦ hu (Submodule.Quotient.mk ⟨y, hy⟩))
  refine ⟨hl, fun v hv ↦ hl v fun u ↦ ?_⟩
  rw [P.middleForm_swap m hm, hv, smul_zero]

/-- For even `m` the middle form is a nondegenerate invariant symmetric form. -/
theorem isInvariantForm_middleForm (he : Even m) :
    IsInvariantForm (P.middleRep m) (P.middleForm m hm) where
  isSymm := ⟨fun u v ↦ by
    rw [P.middleForm_swap m hm, Int.negOnePow_even _ he, one_smul]⟩
  nondegenerate := P.middleForm_nondegenerate m hm
  map_map g u v := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    exact pairing_act m hm P.φ g x.1 y.1

/-- `Sign_G(C, p, φ)` (manuscript (3.1)): the equivariant signature of the middle form on
`H^m(C, p)`, `N = 2m`. -/
def sign : G → ℂ :=
  ratEquivariantSignature (P.middleRep m) (P.middleForm m hm)

lemma neg_middleForm : P.neg.middleForm m hm = -P.middleForm m hm :=
  LinearMap.ext₂ fun u v ↦ by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    exact LinearMap.congr_fun₂ (pairing_neg m hm P.φ) x.1 y.1

variable {P Q} in
/-- The map `f^* : H^m(Q) → H^m(P)` of a homotopy isometry `f : P ≃ Q`. -/
def HomotopyIsometry.middleMap (e : HomotopyIsometry P Q) : Q.middle m →ₗ[ℚ] P.middle m :=
  karMap m (dualHom (inv G S) N e.f) (by
    rw [← dualHom_comp, ← dualHom_comp, e.f_comp_p, e.p_comp_f])

variable {P Q} in
/-- `f^*` is an isometry: `⟨f^* x, φ f^* y⟩ = ⟨x, f φ f^* y⟩ = ⟨x, φ' y⟩` on cocycles. -/
lemma HomotopyIsometry.middleForm_middleMap (e : HomotopyIsometry P Q) (u v : Q.middle m) :
    P.middleForm m hm (e.middleMap m u) (e.middleMap m v) = Q.middleForm m hm u v := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  exact (pairing_conj m hm e.f P.φ x.1 y.1).symm.trans (pairing_homotopy m hm e.conj x.2 y.2)

variable (b : ∀ r, BinaryBicone (P.C.X r) (Q.C.X r))

lemma sumInl_comp_p : sumInl b ≫ (P.sum Q b).p = P.p ≫ sumInl b := by simp
lemma sumInr_comp_p : sumInr b ≫ (P.sum Q b).p = Q.p ≫ sumInr b := by simp
lemma p_comp_sumFst : (P.sum Q b).p ≫ sumFst b = sumFst b ≫ P.p := by simp
lemma p_comp_sumSnd : (P.sum Q b).p ≫ sumSnd b = sumSnd b ≫ Q.p := by simp

/-- `(inl^*, inr^*) : H^m(P ⊕ Q) → H^m(P) × H^m(Q)`. -/
def sumToProd : (P.sum Q b).middle m →ₗ[ℚ] P.middle m × Q.middle m :=
  (karMap m (dualHom (inv G S) N (sumInl b))
      (by rw [← dualHom_comp, ← dualHom_comp, sumInl_comp_p])).prod
    (karMap m (dualHom (inv G S) N (sumInr b))
      (by rw [← dualHom_comp, ← dualHom_comp, sumInr_comp_p]))

/-- `fst^* + snd^* : H^m(P) × H^m(Q) → H^m(P ⊕ Q)`. -/
def prodToSum : P.middle m × Q.middle m →ₗ[ℚ] (P.sum Q b).middle m :=
  (karMap m (dualHom (inv G S) N (sumFst b))
      (by rw [← dualHom_comp, ← dualHom_comp, p_comp_sumFst])).coprod
    (karMap m (dualHom (inv G S) N (sumSnd b))
      (by rw [← dualHom_comp, ← dualHom_comp, p_comp_sumSnd]))

lemma pairing_sum (x y : ((P.sum Q b).C.X (N - m)).Sp) :
    pairing m hm (P.sum Q b).φ x y =
      pairing m hm P.φ (toLin ((dualHom (inv G S) N (sumInl b)).f m) x)
          (toLin ((dualHom (inv G S) N (sumInl b)).f m) y) +
        pairing m hm Q.φ (toLin ((dualHom (inv G S) N (sumInr b)).f m) x)
          (toLin ((dualHom (inv G S) N (sumInr b)).f m) y) := by
  rw [sum_φ, pairing_add, LinearMap.add_apply, LinearMap.add_apply, pairing_conj, pairing_conj]

lemma middleForm_sumToProd (u v : (P.sum Q b).middle m) :
    orthSum (P.middleForm m hm) (Q.middleForm m hm) (P.sumToProd Q m b u) (P.sumToProd Q m b v) =
      (P.sum Q b).middleForm m hm u v := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  exact (P.pairing_sum Q m hm b x.1 y.1).symm

lemma middleForm_prodToSum (u v : P.middle m × Q.middle m) :
    (P.sum Q b).middleForm m hm (P.prodToSum Q m b u) (P.prodToSum Q m b v) =
      orthSum (P.middleForm m hm) (Q.middleForm m hm) u v := by
  obtain ⟨u₁, u₂⟩ := u
  obtain ⟨v₁, v₂⟩ := v
  obtain ⟨x₁, rfl⟩ := Submodule.Quotient.mk_surjective _ u₁
  obtain ⟨x₂, rfl⟩ := Submodule.Quotient.mk_surjective _ u₂
  obtain ⟨y₁, rfl⟩ := Submodule.Quotient.mk_surjective _ v₁
  obtain ⟨y₂, rfl⟩ := Submodule.Quotient.mk_surjective _ v₂
  have h₁₁ (w : (P.C.X (N - m)).Sp) : toLin ((dualHom (inv G S) N (sumInl b)).f m)
      (toLin ((dualHom (inv G S) N (sumFst b)).f m) w) = w := by
    rw [← toLin_comp, ← comp_f, dualHom_sumFst_dualHom_sumInl, id_f, toLin_id]
  have h₁₂ (w : (Q.C.X (N - m)).Sp) : toLin ((dualHom (inv G S) N (sumInl b)).f m)
      (toLin ((dualHom (inv G S) N (sumSnd b)).f m) w) = 0 := by
    rw [← toLin_comp, ← comp_f, dualHom_sumSnd_dualHom_sumInl, zero_f, toLin_zero]
  have h₂₁ (w : (P.C.X (N - m)).Sp) : toLin ((dualHom (inv G S) N (sumInr b)).f m)
      (toLin ((dualHom (inv G S) N (sumFst b)).f m) w) = 0 := by
    rw [← toLin_comp, ← comp_f, dualHom_sumFst_dualHom_sumInr, zero_f, toLin_zero]
  have h₂₂ (w : (Q.C.X (N - m)).Sp) : toLin ((dualHom (inv G S) N (sumInr b)).f m)
      (toLin ((dualHom (inv G S) N (sumSnd b)).f m) w) = w := by
    rw [← toLin_comp, ← comp_f, dualHom_sumSnd_dualHom_sumInr, id_f, toLin_id]
  change pairing m hm (P.sum Q b).φ
      (toLin ((dualHom (inv G S) N (sumFst b)).f m) x₁.1 +
        toLin ((dualHom (inv G S) N (sumSnd b)).f m) x₂.1)
      (toLin ((dualHom (inv G S) N (sumFst b)).f m) y₁.1 +
        toLin ((dualHom (inv G S) N (sumSnd b)).f m) y₂.1) =
    pairing m hm P.φ x₁.1 y₁.1 + pairing m hm Q.φ x₂.1 y₂.1
  rw [pairing_sum]
  simp only [map_add, h₁₁, h₁₂, h₂₁, h₂₂, add_zero, zero_add]

lemma prodToSum_middleRep (g : G) (u : P.middle m × Q.middle m) :
    P.prodToSum Q m b (((P.middleRep m).prod (Q.middleRep m)) g u) =
      (P.sum Q b).middleRep m g (P.prodToSum Q m b u) := by
  obtain ⟨u₁, u₂⟩ := u
  rw [Representation.prod_apply_apply, prodToSum]
  erw [LinearMap.coprod_apply, LinearMap.coprod_apply]
  rw [map_add, karMap_karRep, karMap_karRep]

variable [Finite G]

/-- `Sign_G` is invariant under homotopy isometries ([Ran89, 3.10] ⇒ well defined on classes). -/
theorem sign_eq_of_isometry {P Q : SymPoincare (inv G S) N} (he : Even m)
    (e : HomotopyIsometry P Q) : P.sign m hm = Q.sign m hm :=
  ratEquivariantSignature_eq_of_isometries (Q.isInvariantForm_middleForm m hm he)
    (P.isInvariantForm_middleForm m hm he) (e.middleMap m) (e.symm.middleMap m)
    (e.middleForm_middleMap m hm) (e.symm.middleForm_middleMap m hm) (karMap_karRep m _ _)

/-- `Sign_G` is additive. -/
theorem sign_sum (he : Even m) : (P.sum Q b).sign m hm = P.sign m hm + Q.sign m hm := by
  have hP := P.isInvariantForm_middleForm m hm he
  have hQ := Q.isInvariantForm_middleForm m hm he
  rw [sign, sign, sign, ← ratEquivariantSignature_orthSum hP hQ]
  exact ratEquivariantSignature_eq_of_isometries (hP.orthSum hQ)
    ((P.sum Q b).isInvariantForm_middleForm m hm he) (P.prodToSum Q m b) (P.sumToProd Q m b)
    (P.middleForm_prodToSum Q m hm b) (P.middleForm_sumToProd Q m hm b)
    (P.prodToSum_middleRep Q m b)

/-- `Sign_G(-P) = -Sign_G(P)`. -/
theorem sign_neg (he : Even m) : P.neg.sign m hm = -P.sign m hm := by
  rw [sign, sign, neg_middleForm]
  exact ratEquivariantSignature_neg (P.isInvariantForm_middleForm m hm he)

/-- The value of `Sign_G` at `1` is the ordinary signature of the middle form. -/
theorem sign_one (he : Even m) : P.sign m hm 1 = ratSignature (P.middleForm m hm) :=
  let hb := P.isInvariantForm_middleForm m hm he
  ratEquivariantSignature_one hb.isSymm hb.nondegenerate hb.map_map

section Four

variable (P Q : SymPoincare (inv G S) 4)

/-- `Sign_G` of a 4-dimensional complex, read off `H^2(C, p)` (manuscript (3.1)). -/
abbrev sign₄ : G → ℂ := P.sign 2 (by norm_num)

theorem sign₄_eq_of_isometry {P Q : SymPoincare (inv G S) 4} (e : HomotopyIsometry P Q) :
    P.sign₄ = Q.sign₄ :=
  sign_eq_of_isometry 2 _ even_two e

theorem sign₄_sum (b : ∀ r, BinaryBicone (P.C.X r) (Q.C.X r)) :
    (P.sum Q b).sign₄ = P.sign₄ + Q.sign₄ :=
  P.sign_sum Q 2 _ b even_two

theorem sign₄_neg : P.neg.sign₄ = -P.sign₄ := P.sign_neg 2 _ even_two

theorem sign₄_one : P.sign₄ 1 = ratSignature (P.middleForm 2 (by norm_num)) :=
  P.sign_one 2 _ even_two

end Four

end SymPoincare

end

end HSFormal.LTheory
