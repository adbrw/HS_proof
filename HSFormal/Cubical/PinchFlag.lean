import HSFormal.Cubical.GridPair

/-!
# The pinch flag: box-cut B-pairs as tensor products (cubical module C8, part 1)

Closes the gap left by C4 between the restricted complexes of the box cut of
`W = Tⁿ ⊗ CPcell` and the tensor-product cube pairs of `GridPair`.

* `CellIso C D`: a bijection of cells preserving degrees and boundary coefficients (an
  isomorphism of based complexes), with inverse, composition, tensor products, duals
  (`CellIso.dual`) and transport of homotopy equivalences (`HtpyEquiv.transport`).
* Cell bijections between restrictions and products: `CellIso.ofEmb` (a cellular embedding onto
  a locally closed set), `CellIso.ofEmbRestrict` (restricted to a locally closed subset),
  `CellIso.prodRestrict` (`⊗ (C i)|Q i ≅ (⊗ C i)|∀ i, Q i`), `CellIso.restrictTensor`
  (`C|P ⊗ D ≅ (C ⊗ D)|P ∘ fst`).
* For the box `B = ∏ [a_i, a_i + m + 1]` of `T^n_M` (`m + 1 < M`): `torusCP.boxIso` identifies
  `W_B` with `I_{m+1}^{⊗n} ⊗ CPcell`, `torusCP.boxRelIso` identifies `W/W_A = C(W_B, Σ)` with
  `C(Iⁿ, ∂Iⁿ) ⊗ CPcell`; under these the right column of the excision ladder is the tensor
  product of the symmetric cube pair duality with `φ_CP` (`torusCP.boxCut_ladderRight_apply`),
  hence a homotopy equivalence (`torusCP.boxCut_ladderRightEquiv`): **the B-pair of the box cut is
  Poincaré**.
-/

noncomputable section

namespace HSFormal.Cubical

open Matrix
open scoped Kronecker

namespace BasedComplex

variable {C C' D D' E : BasedComplex}

/-! ### Isomorphisms of based complexes -/

/-- A bijection of cells preserving degrees and boundary coefficients. -/
structure CellIso (C D : BasedComplex) where
  toEquiv : C.X ≃ D.X
  deg_eq : ∀ σ, D.deg (toEquiv σ) = C.deg σ
  d_eq : ∀ σ τ, D.d (toEquiv σ) (toEquiv τ) = C.d σ τ

namespace CellIso

/-- The identity. -/
def refl (C : BasedComplex) : CellIso C C := ⟨Equiv.refl _, fun _ ↦ rfl, fun _ _ ↦ rfl⟩

/-- The inverse. -/
def symm (e : CellIso C D) : CellIso D C where
  toEquiv := e.toEquiv.symm
  deg_eq σ := by rw [← e.deg_eq, Equiv.apply_symm_apply]
  d_eq σ τ := by rw [← e.d_eq, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- Composition. -/
def trans (e : CellIso C D) (e' : CellIso D E) : CellIso C E where
  toEquiv := e.toEquiv.trans e'.toEquiv
  deg_eq σ := by simp [e'.deg_eq, e.deg_eq]
  d_eq σ τ := by simp [e'.d_eq, e.d_eq]

@[simp] theorem trans_apply (e : CellIso C D) (e' : CellIso D E) (σ : C.X) :
    (e.trans e').toEquiv σ = e'.toEquiv (e.toEquiv σ) := rfl

@[simp] theorem symm_apply_apply (e : CellIso C D) (σ : C.X) :
    e.symm.toEquiv (e.toEquiv σ) = σ := e.toEquiv.symm_apply_apply σ

@[simp] theorem apply_symm_apply (e : CellIso C D) (σ : D.X) :
    e.toEquiv (e.symm.toEquiv σ) = σ := e.toEquiv.apply_symm_apply σ

theorem sgn_eq (e : CellIso C D) (σ τ : C.X) :
    D.sgn (e.toEquiv σ) (e.toEquiv τ) = C.sgn σ τ := by
  simp [sgn, diagonal_apply, e.toEquiv.injective.eq_iff, e.deg_eq]

/-- The permutation matrix of `e` (target rows). -/
def mat (e : CellIso C D) : Matrix D.X C.X ℚ :=
  Matrix.of fun ρ σ ↦ if ρ = e.toEquiv σ then 1 else 0

theorem mat_mul_apply {Z : Type*} (e : CellIso C D) (M : Matrix C.X Z ℚ) (ρ : D.X) (z : Z) :
    (e.mat * M) ρ z = M (e.symm.toEquiv ρ) z := by
  rw [mul_apply, Finset.sum_eq_single (e.symm.toEquiv ρ)]
  · simp [mat]
  · intro σ _ hσ
    rw [mat, of_apply, ite_eq_right, zero_mul]
    rintro rfl
    exact hσ (e.symm_apply_apply σ).symm
  · simp

theorem mul_mat_apply {Z : Type*} [Fintype Z] (e : CellIso C D) (M : Matrix Z D.X ℚ) (z : Z)
    (σ : C.X) : (M * e.mat) z σ = M z (e.toEquiv σ) := by
  rw [mul_apply, Finset.sum_eq_single (e.toEquiv σ)]
  · simp [mat]
  · intro ρ _ hρ
    rw [mat, of_apply, ite_eq_right hρ, mul_zero]
  · simp

theorem mat_symm_mul_mat (e : CellIso C D) : e.symm.mat * e.mat = 1 := by
  ext σ τ
  rw [mat_mul_apply]
  change (if e.toEquiv σ = e.toEquiv τ then (1 : ℚ) else 0) = _
  simp [one_apply, e.toEquiv.injective.eq_iff]

theorem mat_mul_mat_symm (e : CellIso C D) : e.mat * e.symm.mat = 1 := by
  ext σ τ
  rw [mat_mul_apply]
  change (if e.symm.toEquiv σ = e.symm.toEquiv τ then (1 : ℚ) else 0) = _
  simp [one_apply, e.symm.toEquiv.injective.eq_iff]

theorem mat_hasDeg (e : CellIso C D) : HasDeg C D 0 e.mat := fun ρ σ h ↦ by
  simp only [mat, of_apply, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at h
  subst h
  simp [e.deg_eq]

theorem d_mul_mat (e : CellIso C D) : D.d * e.mat = e.mat * C.d := by
  ext ρ σ
  rw [mul_mat_apply, mat_mul_apply, ← e.d_eq, apply_symm_apply]

/-- The chain isomorphism of `e`. -/
def hom (e : CellIso C D) : Hom C D := ⟨e.mat, e.mat_hasDeg, e.d_mul_mat⟩

/-- `e` as a homotopy equivalence with zero homotopies. -/
def htpyEquiv (e : CellIso C D) : HtpyEquiv C D :=
  HtpyEquiv.ofIso e.hom e.symm.mat e.symm.mat_hasDeg e.mat_symm_mul_mat e.mat_mul_mat_symm

@[simp] theorem htpyEquiv_hom_f (e : CellIso C D) : e.htpyEquiv.hom.f = e.mat := rfl

@[simp] theorem htpyEquiv_inv_f (e : CellIso C D) : e.htpyEquiv.inv.f = e.symm.mat := rfl

theorem dimLE {N : ℕ} (e : CellIso C D) (hD : D.DimLE N) : C.DimLE N := fun σ ↦ by
  rw [← e.deg_eq]; exact hD _

/-- The dual of a cell isomorphism (same bijection). -/
def dual {N : ℕ} (e : CellIso C D) (hC : C.DimLE N) (hD : D.DimLE N) :
    CellIso (C.dual N hC) (D.dual N hD) where
  toEquiv := e.toEquiv
  deg_eq σ := by change N - D.deg _ = N - C.deg σ; rw [e.deg_eq]
  d_eq σ τ := by rw [dual_d_apply, dual_d_apply, e.d_eq, e.deg_eq]

@[simp] theorem dual_apply {N : ℕ} (e : CellIso C D) (hC : C.DimLE N) (hD : D.DimLE N)
    (σ : C.X) : (e.dual hC hD).toEquiv σ = e.toEquiv σ := rfl

/-- The tensor product of cell isomorphisms. -/
def tensor (e : CellIso C C') (e' : CellIso D D') : CellIso (C.tensor D) (C'.tensor D') where
  toEquiv := e.toEquiv.prodCongr e'.toEquiv
  deg_eq p := by simp [e.deg_eq, e'.deg_eq]
  d_eq := by
    rintro ⟨a, b⟩ ⟨c, d⟩
    change (C'.d ⊗ₖ (1 : Matrix D'.X D'.X ℚ) + C'.sgn ⊗ₖ D'.d) (e.toEquiv a, e'.toEquiv b)
      (e.toEquiv c, e'.toEquiv d) = (C.d ⊗ₖ (1 : Matrix D.X D.X ℚ) + C.sgn ⊗ₖ D.d) (a, b) (c, d)
    simp only [Matrix.add_apply, kronecker_apply, e.d_eq, e'.d_eq, e.sgn_eq, one_apply,
      e'.toEquiv.injective.eq_iff]

@[simp] theorem tensor_apply (e : CellIso C C') (e' : CellIso D D') (p : C.X × D.X) :
    (e.tensor e').toEquiv p = (e.toEquiv p.1, e'.toEquiv p.2) := rfl

end CellIso

/-- Transport of a duality equivalence `C^{N-*} ≃ D` along cell isomorphisms `C ≅ C'`,
`D ≅ D'`. -/
def HtpyEquiv.transport {N : ℕ} {hC : C.DimLE N} (f : HtpyEquiv (C.dual N hC) D)
    (eC : CellIso C C') (eD : CellIso D D') (hC' : C'.DimLE N) :
    HtpyEquiv (C'.dual N hC') D' :=
  ((eC.symm.dual hC' hC).htpyEquiv.trans f).trans eD.htpyEquiv

theorem HtpyEquiv.transport_hom_f_apply {N : ℕ} {hC : C.DimLE N} (f : HtpyEquiv (C.dual N hC) D)
    (eC : CellIso C C') (eD : CellIso D D') (hC' : C'.DimLE N) (σ : D.X) (τ : C.X) :
    (f.transport eC eD hC').hom.f (eD.toEquiv σ) (eC.toEquiv τ) = f.hom.f σ τ := by
  change (eD.mat * (f.hom.f * (eC.symm.dual hC' hC).mat)) _ _ = _
  rw [CellIso.mat_mul_apply, CellIso.mul_mat_apply, CellIso.symm_apply_apply,
    CellIso.dual_apply, CellIso.symm_apply_apply]


/-! ### Cellular injections and restrictions -/

/-- An injection of cells preserving degrees and boundary coefficients (its image need not be a
subcomplex), e.g. the cells of a relative complex in the absolute one. -/
structure CellInj (C D : BasedComplex) where
  toFun : C.X → D.X
  inj : Function.Injective toFun
  deg_eq : ∀ σ, D.deg (toFun σ) = C.deg σ
  d_eq : ∀ σ τ, D.d (toFun σ) (toFun τ) = C.d σ τ

namespace CellInj

/-- The identity. -/
def id (C : BasedComplex) : CellInj C C := ⟨_root_.id, Function.injective_id, fun _ ↦ rfl,
  fun _ _ ↦ rfl⟩

/-- Composition. -/
def comp (f : CellInj D E) (g : CellInj C D) : CellInj C E where
  toFun := f.toFun ∘ g.toFun
  inj := f.inj.comp g.inj
  deg_eq σ := by simp [f.deg_eq, g.deg_eq]
  d_eq σ τ := by simp [f.d_eq, g.d_eq]

/-- A cellular embedding. -/
def ofEmb (e : CellEmbedding C D) : CellInj C D := ⟨e.toFun, e.inj, e.deg_eq, e.d_eq⟩

/-- The cells of a restriction. -/
def subtype (P : C.X → Prop) [DecidablePred P] (hP : C.IsLocallyClosed P) :
    CellInj (C.restrict P hP) C := ⟨Subtype.val, Subtype.val_injective, fun _ ↦ rfl, fun _ _ ↦ rfl⟩

theorem sgn_eq (f : CellInj C D) (σ τ : C.X) : D.sgn (f.toFun σ) (f.toFun τ) = C.sgn σ τ := by
  simp [sgn, diagonal_apply, f.inj.eq_iff, f.deg_eq]

/-- The tensor product. -/
def tensor (f : CellInj C C') (g : CellInj D D') : CellInj (C.tensor D) (C'.tensor D') where
  toFun := Prod.map f.toFun g.toFun
  inj := f.inj.prodMap g.inj
  deg_eq p := by simp [f.deg_eq, g.deg_eq]
  d_eq := by
    rintro ⟨a, b⟩ ⟨c, d⟩
    change (C'.d ⊗ₖ (1 : Matrix D'.X D'.X ℚ) + C'.sgn ⊗ₖ D'.d) (f.toFun a, g.toFun b)
      (f.toFun c, g.toFun d) = (C.d ⊗ₖ (1 : Matrix D.X D.X ℚ) + C.sgn ⊗ₖ D.d) (a, b) (c, d)
    simp only [Matrix.add_apply, kronecker_apply, f.d_eq, g.d_eq, f.sgn_eq, one_apply, g.inj.eq_iff]

@[simp] theorem tensor_toFun (f : CellInj C C') (g : CellInj D D') (p : C.X × D.X) :
    (f.tensor g).toFun p = (f.toFun p.1, g.toFun p.2) := rfl

/-- Iterated tensor products. -/
def prod : (n : ℕ) → {C D : Fin n → BasedComplex} → (∀ i, CellInj (C i) (D i)) →
    CellInj (prodComplex n C) (prodComplex n D)
  | 0, _, _, _ => CellInj.id _
  | n + 1, _, _, f => (f 0).tensor (CellInj.prod n fun i ↦ f i.succ)

theorem prod_succ_toFun {n : ℕ} {C D : Fin (n + 1) → BasedComplex} (f : ∀ i, CellInj (C i) (D i))
    (p : (prodComplex (n + 1) C).X) :
    (CellInj.prod (n + 1) f).toFun p = ((f 0).toFun p.1, (CellInj.prod n fun i ↦ f i.succ).toFun p.2) :=
  rfl

theorem coord_prod : (n : ℕ) → {C D : Fin n → BasedComplex} → (f : ∀ i, CellInj (C i) (D i)) →
    (p : (prodComplex n C).X) → (i : Fin n) →
    coord n ((CellInj.prod n f).toFun p) i = (f i).toFun (coord n p i)
  | 0, _, _, _, _, i => i.elim0
  | n + 1, _, _, f, p, i => by
    induction i using Fin.cases with
    | zero => rfl
    | succ i => exact coord_prod n (fun i ↦ f i.succ) p.2 i

/-- The image of an iterated tensor product of injections is the set of cells whose
coordinates lie in the images. -/
theorem prod_range_iff : (n : ℕ) → {C D : Fin n → BasedComplex} → (f : ∀ i, CellInj (C i) (D i)) →
    (σ : (prodComplex n D).X) →
    (∃ p, (CellInj.prod n f).toFun p = σ) ↔ ∀ i, ∃ x, (f i).toFun x = coord n σ i
  | 0, _, _, _, _ => ⟨fun _ i ↦ i.elim0, fun _ ↦ ⟨(), rfl⟩⟩
  | n + 1, _, _, f, ⟨σ, σ'⟩ => by
    constructor
    · rintro ⟨⟨τ, τ'⟩, h⟩ i
      obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
      induction i using Fin.cases with
      | zero => exact ⟨τ, h₁⟩
      | succ i => exact (prod_range_iff n (fun i ↦ f i.succ) σ').mp ⟨τ', h₂⟩ i
    · intro h
      obtain ⟨τ, hτ⟩ := h 0
      obtain ⟨τ', hτ'⟩ := (prod_range_iff n (fun i ↦ f i.succ) σ').mpr fun i ↦ h i.succ
      exact ⟨(τ, τ'), Prod.ext hτ hτ'⟩

/-- A cellular injection is an isomorphism onto its (locally closed) image. -/
def toIso (f : CellInj C D) (P : D.X → Prop) [DecidablePred P] (hP : D.IsLocallyClosed P)
    (h : ∀ σ, P σ ↔ ∃ x, f.toFun x = σ) : CellIso C (D.restrict P hP) where
  toEquiv := Equiv.ofBijective (fun x ↦ ⟨f.toFun x, (h _).mpr ⟨x, rfl⟩⟩)
    ⟨fun x y hxy ↦ f.inj (congrArg Subtype.val hxy), fun σ ↦ by
      obtain ⟨x, hx⟩ := (h σ.1).mp σ.2
      exact ⟨x, Subtype.ext hx⟩⟩
  deg_eq x := f.deg_eq x
  d_eq x y := f.d_eq x y

@[simp] theorem toIso_apply_val (f : CellInj C D) (P : D.X → Prop) [DecidablePred P]
    (hP : D.IsLocallyClosed P) (h : ∀ σ, P σ ↔ ∃ x, f.toFun x = σ) (x : C.X) :
    ((f.toIso P hP h).toEquiv x).1 = f.toFun x := rfl

end CellInj


/-! ### The box of the torus and its relative cells -/

theorem interval.symMat_comm (m : ℕ) (x y : (interval (m + 1)).X) :
    interval.symMat m x y = interval.symMat m y x := by
  rcases x with v | e <;> rcases y with w | f <;> simp [interval.symMat, add_comm]

section Box

variable (M m : ℕ) [NeZero M] (h : m + 1 < M)

/-- The arc `[a, a + m + 1]` of `C_M` carries the non-end cells of `I_{m+1}` exactly onto the
cells off the open arc's complement. -/
theorem circle.arc_rel_range_iff (a : Fin M) (x : (circle M).X) :
    (∃ y : (interval.rel m).X, (circle.arc M a (m + 1) h).toFun y.1 = x) ↔
      ¬circle.OffArc M a (m + 1) x := by
  constructor
  · rintro ⟨⟨y, hy⟩, rfl⟩
    rcases y with j | i
    · simp only [interval.IsEnd, not_or] at hy
      change ¬(((a + Fin.castLE _ j - a : Fin M) : ℕ) = 0 ∨
        m + 1 ≤ ((a + Fin.castLE _ j - a : Fin M) : ℕ))
      rw [add_sub_cancel_left, Fin.val_castLE]
      have h1 : (j : ℕ) ≠ 0 := fun h' ↦ hy.1 (congrArg Sum.inl (Fin.ext (by simpa using h')))
      have h2 : (j : ℕ) ≠ m + 1 := fun h' ↦ hy.2 (congrArg Sum.inl (Fin.ext (by simpa using h')))
      have := j.2
      omega
    · change ¬(m + 1 ≤ ((a + Fin.castLE _ i - a : Fin M) : ℕ))
      rw [add_sub_cancel_left, Fin.val_castLE]
      have := i.2
      omega
  · rcases x with v | e
    · intro hv
      change ¬(((v - a : Fin M) : ℕ) = 0 ∨ m + 1 ≤ ((v - a : Fin M) : ℕ)) at hv
      refine ⟨⟨.inl ⟨((v - a : Fin M) : ℕ), by omega⟩, ?_⟩, ?_⟩
      · simp only [interval.IsEnd, not_or, Sum.inl.injEq, Fin.ext_iff, Fin.val_zero,
          Fin.val_last]
        omega
      · change Sum.inl (a + Fin.castLE _ _) = Sum.inl v
        rw [show Fin.castLE _ _ = v - a from Fin.ext rfl, add_sub_cancel]
    · intro he
      change ¬(m + 1 ≤ ((e - a : Fin M) : ℕ)) at he
      refine ⟨⟨.inr ⟨((e - a : Fin M) : ℕ), by omega⟩, by simp [interval.IsEnd]⟩, ?_⟩
      change Sum.inr (a + Fin.castLE _ _) = Sum.inr e
      rw [show Fin.castLE _ _ = e - a from Fin.ext rfl, add_sub_cancel]

variable {n : ℕ} (a : Fin n → Fin M)

/-- The cells of the box `∏ [a_i, a_i + m + 1]` of `T^n_M`, as the cube `I_{m+1}^{⊗n}`. -/
def torus.boxInj : CellInj (cube (m + 1) n) (torus M n) :=
  CellInj.prod n fun i ↦ CellInj.ofEmb (circle.arc M (a i) (m + 1) h)

/-- The cells of `C(B, ∂B)` (the box minus its boundary), as the relative cube `C(Iⁿ, ∂Iⁿ)`. -/
def torus.boxRelInj : CellInj (cubeRel m n) (torus M n) :=
  CellInj.prod n fun i ↦ (CellInj.ofEmb (circle.arc M (a i) (m + 1) h)).comp
    (CellInj.subtype _ (interval.isSub_isEnd m).isLocallyClosed_compl)

theorem torus.boxInj_range_iff (σ : (torus M n).X) :
    (∃ p, (torus.boxInj M m h a).toFun p = σ) ↔ torus.InBox M n a (fun _ ↦ m + 1) σ :=
  (CellInj.prod_range_iff n _ σ).trans
    (forall_congr' fun i ↦ circle.arc_range_iff M (a i) (m + 1) h _)

theorem torus.boxRelInj_range_iff (σ : (torus M n).X) :
    (∃ p, (torus.boxRelInj M m h a).toFun p = σ) ↔ ¬torus.OffBox M n a (fun _ ↦ m + 1) σ := by
  rw [torus.boxRelInj, CellInj.prod_range_iff, torus.OffBox, not_exists]
  exact forall_congr' fun i ↦ circle.arc_rel_range_iff M m h (a i) _

/-- **The torus duality on the box is the symmetric cube pair duality**: the entries of
`φ_{Tⁿ}` from cochains on `B` to chains of `C(B, ∂B)` are those of
`cube.symAbsDuality : C^{n-*}(Iⁿ) ≃ C(Iⁿ, ∂Iⁿ)`. -/
theorem torus.duality_boxRel_box : (n : ℕ) → (a : Fin n → Fin M) → (x : (cubeRel m n).X) →
    (y : (cube (m + 1) n).X) →
    (torus.duality M n).hom.f ((torus.boxRelInj M m h a).toFun x)
      ((torus.boxInj M m h a).toFun y) = (cube.symAbsDuality m n).hom.f x y
  | 0, _, _, _ => rfl
  | n + 1, a, ⟨x₀, x'⟩, ⟨y₀, y'⟩ => by
    have ih := torus.duality_boxRel_box n (fun i ↦ a i.succ) x' y'
    change (torus.duality M (n + 1)).hom.f
        ((circle.arc M (a 0) (m + 1) h).toFun x₀.1, (torus.boxRelInj M m h fun i ↦ a i.succ).toFun x')
        ((circle.arc M (a 0) (m + 1) h).toFun y₀, (torus.boxInj M m h fun i ↦ a i.succ).toFun y') =
      (((interval.symAbsDuality m).dualTensor (cube.symAbsDuality m n)).castDim
        (Nat.add_comm 1 n) _).hom.f (x₀, x') (y₀, y')
    rw [torus.duality_succ_hom_f, HtpyEquiv.castDim_hom_f, HtpyEquiv.dualTensor_hom_f, koszul,
      koszul, mul_diagonal, mul_diagonal, kronecker_apply, kronecker_apply, ih,
      circle.duality_arc, interval.symAbsDuality_hom_f, interval.symMat_comm,
      (circle.arc M (a 0) (m + 1) h).deg_eq, (torus.boxInj M m h fun i ↦ a i.succ).deg_eq]

end Box


/-! ### The box cut of `W = Tⁿ ⊗ CPcell`: the B-pair is a tensor product -/

section BoxCP

variable (M m : ℕ) [NeZero M] (h : m + 1 < M) {n : ℕ} (a : Fin n → Fin M)

/-- **`W_B ≅ I_{m+1}^{⊗n} ⊗ CPcell`**: the cells of the box cut's B-side. -/
def torusCP.boxIso [DecidablePred (torusCP.WB M n a fun _ ↦ m + 1)]
    (hP : (torusCP M n).IsLocallyClosed (torusCP.WB M n a fun _ ↦ m + 1)) :
    CellIso ((cube (m + 1) n).tensor CPcell)
      ((torusCP M n).restrict (torusCP.WB M n a fun _ ↦ m + 1) hP) :=
  ((torus.boxInj M m h a).tensor (CellInj.id CPcell)).toIso _ hP fun σ ↦ by
    constructor
    · intro hσ
      obtain ⟨p, hp⟩ := (torus.boxInj_range_iff M m h a σ.1).mpr hσ
      exact ⟨(p, σ.2), Prod.ext hp rfl⟩
    · rintro ⟨p, rfl⟩
      exact (torus.boxInj_range_iff M m h a _).mp ⟨p.1, rfl⟩

/-- **`C(W_B, Σ) = W/W_A ≅ C(Iⁿ, ∂Iⁿ) ⊗ CPcell`**: the cells of `W` off the A-side. -/
def torusCP.boxRelIso [DecidablePred (torusCP.WA M n a fun _ ↦ m + 1)]
    (hP : (torusCP M n).IsLocallyClosed fun σ ↦ ¬torusCP.WA M n a (fun _ ↦ m + 1) σ) :
    CellIso ((cubeRel m n).tensor CPcell)
      ((torusCP M n).restrict (fun σ ↦ ¬torusCP.WA M n a (fun _ ↦ m + 1) σ) hP) :=
  ((torus.boxRelInj M m h a).tensor (CellInj.id CPcell)).toIso _ hP fun σ ↦ by
    constructor
    · intro hσ
      obtain ⟨p, hp⟩ := (torus.boxRelInj_range_iff M m h a σ.1).mpr hσ
      exact ⟨(p, σ.2), Prod.ext hp rfl⟩
    · rintro ⟨p, rfl⟩
      exact (torus.boxRelInj_range_iff M m h a _).mp ⟨p.1, rfl⟩

@[simp] theorem torusCP.boxIso_apply [DecidablePred (torusCP.WB M n a fun _ ↦ m + 1)]
    (hP : (torusCP M n).IsLocallyClosed (torusCP.WB M n a fun _ ↦ m + 1))
    (y : ((cube (m + 1) n).tensor CPcell).X) :
    ((torusCP.boxIso M m h a hP).toEquiv y).1 = ((torus.boxInj M m h a).toFun y.1, y.2) := rfl

@[simp] theorem torusCP.boxRelIso_apply [DecidablePred (torusCP.WA M n a fun _ ↦ m + 1)]
    (hP : (torusCP M n).IsLocallyClosed fun σ ↦ ¬torusCP.WA M n a (fun _ ↦ m + 1) σ)
    (x : ((cubeRel m n).tensor CPcell).X) :
    ((torusCP.boxRelIso M m h a hP).toEquiv x).1 = ((torus.boxRelInj M m h a).toFun x.1, x.2) :=
  rfl

variable (n) in
/-- The symmetric B-pair duality `C^{n+4-*}(Iⁿ ⊗ CP) ≃ C(Iⁿ, ∂Iⁿ) ⊗ CP`: the tensor product of
`cube.symAbsDuality` with `φ_CP` through the Koszul isomorphism. -/
def cubeCP.symAbsDuality :
    HtpyEquiv (((cube (m + 1) n).tensor CPcell).dual (n + 4)
      ((cube.dimLE n (m + 1)).tensor CPcell.dimLE)) ((cubeRel m n).tensor CPcell) :=
  (cube.symAbsDuality m n).dualTensor CPcell.duality.toHtpyEquiv

variable [DecidablePred (torusCP.WA M n a fun _ ↦ m + 1)]
  [DecidablePred (torusCP.WB M n a fun _ ↦ m + 1)]

/-- **The C4 gap**: under `W_B ≅ Iⁿ ⊗ CP` and `C(W_B, Σ) ≅ C(Iⁿ, ∂Iⁿ) ⊗ CP`, the right column
of the excision ladder of the box cut is `cube.symAbsDuality ⊗ φ_CP` (entrywise). -/
theorem torusCP.boxCut_ladderRight_apply
    (hloc : ∀ σ τ, (torusCP.duality M n).hom.f σ τ ≠ 0 →
      ¬torusCP.WB M n a (fun _ ↦ m + 1) τ → torusCP.WA M n a (fun _ ↦ m + 1) σ)
    (x : ((cubeRel m n).tensor CPcell).X) (y : ((cube (m + 1) n).tensor CPcell).X) :
    (ladderRight (torusCP.dimLE M n) (torusCP.duality M n).hom (torusCP.isSub_WA M n a _)
      (torusCP.isSub_WB M n a _ fun _ ↦ h) hloc).f
      ((torusCP.boxRelIso M m h a (torusCP.isSub_WA M n a _).isLocallyClosed_compl).toEquiv x)
      ((torusCP.boxIso M m h a (torusCP.isSub_WB M n a _ fun _ ↦ h).isLocallyClosed).toEquiv y) =
    (cubeCP.symAbsDuality m n).hom.f x y := by
  obtain ⟨x, c⟩ := x
  obtain ⟨y, c'⟩ := y
  rw [ladderRight, Hom.restrictDual_f, submatrix_apply, torusCP.boxRelIso_apply,
    torusCP.boxIso_apply, torusCP.duality, SymDuality.tensor_hom_f, cubeCP.symAbsDuality,
    HtpyEquiv.dualTensor_hom_f, koszul, koszul, mul_diagonal, mul_diagonal, kronecker_apply,
    kronecker_apply, torus.duality_boxRel_box, (torus.boxInj M m h a).deg_eq]

/-- **The B-pair of the box cut is Poincaré** (based level): the right column
`C^{n+4-*}(W_B) → C(W_B, Σ)` of the excision ladder is a homotopy equivalence, the transport of
`cube.symAbsDuality ⊗ φ_CP` (`boxCut_ladderRightEquiv_hom`).  Its inverse and homotopies are
those of `interval.symRelDuality` (inverse `e₀^* ε`), which are global on each interval factor:
their propagation is the side length of the box, not the mesh. -/
def torusCP.boxCut_ladderRightEquiv :
    HtpyEquiv (((torusCP M n).restrict (torusCP.WB M n a fun _ ↦ m + 1)
        (torusCP.isSub_WB M n a _ fun _ ↦ h).isLocallyClosed).dual (n + 4)
        ((torusCP.dimLE M n).restrict _ _))
      ((torusCP M n).restrict (fun σ ↦ ¬torusCP.WA M n a (fun _ ↦ m + 1) σ)
        (torusCP.isSub_WA M n a _).isLocallyClosed_compl) :=
  (cubeCP.symAbsDuality m n).transport (torusCP.boxIso M m h a _) (torusCP.boxRelIso M m h a _) _

theorem torusCP.boxCut_ladderRightEquiv_hom
    (hloc : ∀ σ τ, (torusCP.duality M n).hom.f σ τ ≠ 0 →
      ¬torusCP.WB M n a (fun _ ↦ m + 1) τ → torusCP.WA M n a (fun _ ↦ m + 1) σ) :
    (torusCP.boxCut_ladderRightEquiv M m h a).hom =
      ladderRight (torusCP.dimLE M n) (torusCP.duality M n).hom (torusCP.isSub_WA M n a _)
        (torusCP.isSub_WB M n a _ fun _ ↦ h) hloc := by
  refine Hom.ext (Matrix.ext fun ρ σ ↦ ?_)
  obtain ⟨x, rfl⟩ := (torusCP.boxRelIso M m h a
    (torusCP.isSub_WA M n a _).isLocallyClosed_compl).toEquiv.surjective ρ
  obtain ⟨y, rfl⟩ := (torusCP.boxIso M m h a
    (torusCP.isSub_WB M n a _ fun _ ↦ h).isLocallyClosed).toEquiv.surjective σ
  rw [torusCP.boxCut_ladderRightEquiv, HtpyEquiv.transport_hom_f_apply,
    torusCP.boxCut_ladderRight_apply]

end BoxCP

end BasedComplex

end HSFormal.Cubical

end
