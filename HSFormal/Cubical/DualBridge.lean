import HSFormal.Cubical.OneDim
import HSFormal.Cubical.Bridge
import HSFormal.LTheory.SymmetricComplex

/-!
# From based symmetric dualities to `SymPoincare` (cubical module C2, bridge to M1)

A `MatRealization J` realizes finite rational matrices in a preadditive category `V` with strict
involution `J`: an object `obj ι` for each finite cell type, additive and multiplicative
`mat`, and `J.star (mat A) = mat Aᵀ` (manuscript §2: the dual uses the same basis and the
transpose matrix).  Intended instances: based permutation modules (M9a) and the controlled
category over one point.

A based complex becomes `R.complex C : ChainComplex V ℤ` (degree `r` = the `r`-cells), maps
and homotopies are realized blockwise, and `R.dualIso` identifies `Compression.dualComplex` of
the realization with the realization of `C.dual N` (the signs `δ_r = (-1)^r d^*` agree).
A `SymDuality` thereby becomes an M1 `SymPoincare J N` with `p = 1` (`MatRealization.symPoincare`;
the based transposition `ε φᵀ` is Ranicki's `transposeHom`).  `CPcell.symPoincare` is the final
signature-one class; its middle duality component is the identity on `e₂`.
-/

namespace HSFormal.Cubical

open CategoryTheory Category Limits Preadditive Matrix HSFormal.Compression HSFormal.LTheory

universe v u

/-- A realization of finite rational matrices in `V`, compatible with the involution. -/
structure MatRealization {V : Type u} [Category.{v} V] [Preadditive V]
    (J : StrictInvolution V) where
  /-- The object with basis `ι`. -/
  obj : (ι : Type) → [Fintype ι] → V
  /-- The morphism of a matrix (target rows). -/
  mat : {ι κ : Type} → [Fintype ι] → [Fintype κ] → Matrix κ ι ℚ → (obj ι ⟶ obj κ)
  mat_add : ∀ {ι κ : Type} [Fintype ι] [Fintype κ] (A B : Matrix κ ι ℚ),
    mat (A + B) = mat A + mat B
  mat_mul : ∀ {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ] (A : Matrix μ κ ℚ)
    (B : Matrix κ ι ℚ), mat (A * B) = mat B ≫ mat A
  mat_one : ∀ {ι : Type} [Fintype ι] [DecidableEq ι], mat (1 : Matrix ι ι ℚ) = 𝟙 (obj ι)
  star_mat : ∀ {ι κ : Type} [Fintype ι] [Fintype κ] (A : Matrix κ ι ℚ), J.star (mat A) = mat Aᵀ

namespace MatRealization

variable {V : Type u} [Category.{v} V] [Preadditive V] {J : StrictInvolution V}
  (R : MatRealization J)

/-- `mat` as an additive map. -/
def matHom {ι κ : Type} [Fintype ι] [Fintype κ] : Matrix κ ι ℚ →+ (R.obj ι ⟶ R.obj κ) :=
  AddMonoidHom.mk' R.mat R.mat_add

theorem mat_zero {ι κ : Type} [Fintype ι] [Fintype κ] : R.mat (0 : Matrix κ ι ℚ) = 0 :=
  map_zero R.matHom

theorem mat_units_smul {ι κ : Type} [Fintype ι] [Fintype κ] (u : ℤˣ) (A : Matrix κ ι ℚ) :
    u • R.mat A = R.mat ((((u : ℤ) : ℚ)) • A) := by
  rw [Units.smul_def]
  change (u : ℤ) • R.matHom A = R.matHom _
  rw [← map_zsmul]
  congr 1

/-! ### Blocks -/

open BasedComplex

/-- The block of `u` from the cells `P` to the cells `Q`. -/
abbrev blk {X Y : Type} (u : Matrix Y X ℚ) (P : X → Prop) (Q : Y → Prop) :
    Matrix {y // Q y} {x // P x} ℚ :=
  u.submatrix Subtype.val Subtype.val

theorem blk_mul {X Y Z : Type} [Fintype Y] {P : X → Prop} {Q : Y → Prop} {S : Z → Prop}
    [DecidablePred Q] (u : Matrix Z Y ℚ) (w : Matrix Y X ℚ)
    (h : ∀ κ σ, w κ σ ≠ 0 → P σ → Q κ) : blk u Q S * blk w P Q = blk (u * w) P S := by
  ext σ τ
  simp only [mul_apply, submatrix_apply]
  exact sum_subtype_eq (fun κ ↦ u σ.1 κ * w κ τ.1) fun κ hκ ↦ h κ τ.1 (right_ne_zero_of_mul hκ) τ.2

theorem blk_mul' {X Y Z : Type} [Fintype Y] {P : X → Prop} {Q : Y → Prop} {S : Z → Prop}
    [DecidablePred Q] (u : Matrix Z Y ℚ) (w : Matrix Y X ℚ)
    (h : ∀ κ σ, u σ κ ≠ 0 → S σ → Q κ) : blk u Q S * blk w P Q = blk (u * w) P S := by
  ext σ τ
  simp only [mul_apply, submatrix_apply]
  exact sum_subtype_eq (fun κ ↦ u σ.1 κ * w κ τ.1) fun κ hκ ↦ h κ σ.1 (left_ne_zero_of_mul hκ) σ.2

theorem blk_eq_zero {X Y : Type} {P : X → Prop} {Q : Y → Prop} (u : Matrix Y X ℚ)
    (h : ∀ κ σ, u κ σ ≠ 0 → P σ → Q κ → False) : blk u P Q = 0 := by
  ext σ τ; exact by_contra fun h' ↦ h _ _ h' τ.2 σ.2

theorem blk_add {X Y : Type} (u w : Matrix Y X ℚ) (P : X → Prop) (Q : Y → Prop) :
    blk (u + w) P Q = blk u P Q + blk w P Q := rfl

theorem blk_transpose {X Y : Type} (u : Matrix Y X ℚ) (P : X → Prop) (Q : Y → Prop) :
    (blk u P Q)ᵀ = blk uᵀ Q P := rfl

theorem blk_one {X : Type} [DecidableEq X] (P : X → Prop) : blk (1 : Matrix X X ℚ) P P = 1 := by
  ext σ τ; simp [one_apply, Subtype.ext_iff]

/-! ### Complexes, maps and homotopies -/

/-- The realization of a based complex: degree `r` has the basis `Cells C r`. -/
@[simps, reducible]
def complex (C : BasedComplex) : ChainComplex V ℤ where
  X r := R.obj (Cells C r)
  d r r' := R.mat (blk C.d (fun σ ↦ (C.deg σ : ℤ) = r) fun σ ↦ (C.deg σ : ℤ) = r')
  shape r r' h := by
    rw [blk_eq_zero, R.mat_zero]
    intro κ σ h' hσ hκ
    have := C.d_deg κ σ h'
    exact h (by change r' + 1 = r; omega)
  d_comp_d' r r' r'' h _ := by
    rw [← R.mat_mul, blk_mul _ _ fun κ σ h' hσ ↦ by
      have := C.d_deg κ σ h'; change r' + 1 = r at h; omega, C.d_d]
    exact R.mat_zero

variable {C D E : BasedComplex}

/-- The realization of a chain map. -/
@[simps]
def hom (f : BasedComplex.Hom C D) : R.complex C ⟶ R.complex D where
  f r := R.mat (blk f.f (fun σ ↦ (C.deg σ : ℤ) = r) fun σ ↦ (D.deg σ : ℤ) = r)
  comm' r r' h := by
    simp only [complex_d, complex_X]
    rw [← R.mat_mul, ← R.mat_mul, blk_mul _ _ fun κ σ h' hσ ↦ by
      have := f.deg0 κ σ h'; omega, blk_mul _ _ fun κ σ h' hσ ↦ by
      have := C.d_deg κ σ h'; change r' + 1 = r at h; omega, f.comm]

theorem hom_comp (g : BasedComplex.Hom D E) (f : BasedComplex.Hom C D) :
    R.hom (g.comp f) = R.hom f ≫ R.hom g := by
  ext r
  simp only [hom_f, HomologicalComplex.comp_f, ← R.mat_mul, Hom.comp_f]
  rw [blk_mul _ _ fun κ σ h' hσ ↦ by have := f.deg0 κ σ h'; omega]

theorem hom_id (C : BasedComplex) : R.hom (BasedComplex.Hom.id C) = 𝟙 (R.complex C) := by
  ext r
  rw [hom_f, Hom.id_f, blk_one, R.mat_one]
  rfl

/-- The realization of an exact homotopy. -/
def htpy {f g : BasedComplex.Hom C D} (H : Htpy f g) : Homotopy (R.hom f) (R.hom g) where
  hom r r' := R.mat (blk H.h (fun σ ↦ (C.deg σ : ℤ) = r) fun σ ↦ (D.deg σ : ℤ) = r')
  zero r r' h := by
    rw [blk_eq_zero, R.mat_zero]
    intro κ σ h' hσ hκ
    have := H.deg1 κ σ h'
    exact h (by change r + 1 = r'; omega)
  comm r := by
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel r (r - 1) by simp),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (r + 1) r by simp)]
    simp only [complex_d, hom_f]
    rw [← R.mat_mul, ← R.mat_mul, blk_mul _ _ fun κ σ h' hσ ↦ by
        have := C.d_deg κ σ h'; omega,
      blk_mul _ _ fun κ σ h' hσ ↦ by have := H.deg1 κ σ h'; omega, ← R.mat_add, ← R.mat_add]
    congr 1
    rw [← blk_add, ← blk_add]
    congr 1
    have := H.eq
    rw [sub_eq_iff_eq_add] at this
    rw [this]
    abel

theorem negOnePow_cast_eq {N : ℕ} {r : ℤ} {k : ℕ} (hk : (k : ℤ) = N - r) :
    (((r.negOnePow : ℤˣ) : ℤ) : ℚ) = (-1) ^ N * (-1) ^ k := by
  obtain rfl : r = N - k := by omega
  rw [Int.negOnePow_sub, Units.val_mul, Int.cast_mul, Int.cast_negOnePow_natCast,
    Int.cast_negOnePow_natCast]

theorem eqToHom_complex_X (C : BasedComplex) {a b : ℤ} (h : a = b) :
    eqToHom (congrArg (R.complex C).X h) =
      R.mat (blk 1 (fun σ ↦ (C.deg σ : ℤ) = a) fun σ ↦ (C.deg σ : ℤ) = b) := by
  subst h
  rw [eqToHom_refl, blk_one, R.mat_one]

/-! ### Duals and symmetric dualities -/

variable (N : ℕ)

/-- `Compression.dualComplex` of the realization is the realization of the based dual: the
cells of `C^{N-*}` in degree `r` are the `(N - r)`-cells of `C`, and `δ_r = (-1)^r d^*`. -/
def dualIso (C : BasedComplex) (hN : C.DimLE N) :
    dualComplex J N (R.complex C) ≅ R.complex (C.dual N hN) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun r ↦
      { hom := R.mat (blk 1 (fun σ ↦ (C.deg σ : ℤ) = N - r)
          fun σ ↦ ((C.dual N hN).deg σ : ℤ) = r)
        inv := R.mat (blk 1 (fun σ ↦ ((C.dual N hN).deg σ : ℤ) = r)
          fun σ ↦ (C.deg σ : ℤ) = N - r)
        hom_inv_id := by
          rw [← R.mat_mul, blk_mul _ _ fun κ σ h hσ ↦ by
            obtain rfl : κ = σ := by by_contra h'; exact h (one_apply_ne h')
            have := hN κ; change ((N - C.deg κ : ℕ) : ℤ) = r; omega, Matrix.one_mul, blk_one,
            R.mat_one]
        inv_hom_id := by
          rw [← R.mat_mul, blk_mul _ _ fun κ σ h hσ ↦ by
            obtain rfl : κ = σ := by by_contra h'; exact h (one_apply_ne h')
            have := hN κ; change ((N - C.deg κ : ℕ) : ℤ) = r at hσ; omega, Matrix.one_mul,
            blk_one, R.mat_one] })
    (fun r r' h ↦ by
      change r' + 1 = r at h
      simp only [complex_d, dualComplex_d, R.star_mat, R.mat_units_smul, ← R.mat_mul]
      rw [blk_mul _ _ fun κ σ h₁ hσ ↦ by
          obtain rfl : κ = σ := by by_contra h'; exact h₁ (one_apply_ne h')
          have := hN κ; change ((N - C.deg κ : ℕ) : ℤ) = r; omega, Matrix.mul_one]
      rw [show ((((r.negOnePow : ℤˣ) : ℤ) : ℚ) • (blk C.d (fun σ ↦ (C.deg σ : ℤ) = N - r')
          fun σ ↦ (C.deg σ : ℤ) = N - r)ᵀ) = blk ((((r.negOnePow : ℤˣ) : ℤ) : ℚ) • C.dᵀ)
          (fun σ ↦ (C.deg σ : ℤ) = N - r) (fun σ ↦ (C.deg σ : ℤ) = N - r') from rfl,
        blk_mul' _ _ fun κ σ h₁ hσ ↦ by
          obtain rfl : κ = σ := by by_contra h'; exact h₁ (one_apply_ne (Ne.symm h'))
          have := hN κ; change ((N - C.deg κ : ℕ) : ℤ) = r' at hσ; omega, Matrix.one_mul]
      congr 1
      ext σ τ
      have hτ : (C.deg τ.1 : ℤ) = N - r := τ.2
      simp only [submatrix_apply, Matrix.smul_apply, transpose_apply, smul_eq_mul, sgn, mul_diagonal,
        negOnePow_cast_eq hτ]
      ring)

variable {N}

theorem dualIso_hom_f (C : BasedComplex) (hN : C.DimLE N) (r : ℤ) :
    (R.dualIso N C hN).hom.f r = R.mat (blk 1 (fun σ ↦ (C.deg σ : ℤ) = N - r)
      fun σ ↦ ((C.dual N hN).deg σ : ℤ) = r) := rfl

variable {C : BasedComplex} {hN : C.DimLE N}

/-- The realized duality map `φ : (R C)^{N-*} → R C` of `φ : C^{N-*} → C`. -/
def dualityMap (φ : BasedComplex.Hom (C.dual N hN) C) :
    dualComplex J N (R.complex C) ⟶ R.complex C :=
  (R.dualIso N C hN).hom ≫ R.hom φ

theorem dualityMap_f (φ : BasedComplex.Hom (C.dual N hN) C) (r : ℤ) :
    (R.dualityMap φ).f r = R.mat (blk φ.f (fun σ ↦ (C.deg σ : ℤ) = N - r)
      fun σ ↦ (C.deg σ : ℤ) = r) := by
  rw [dualityMap, HomologicalComplex.comp_f, dualIso_hom_f, hom_f, ← R.mat_mul,
    blk_mul _ _ fun κ σ h hσ ↦ by
      obtain rfl : κ = σ := by by_contra h'; exact h (one_apply_ne h')
      have := hN κ; change ((N - C.deg κ : ℕ) : ℤ) = r; omega, Matrix.mul_one]

/-- Based strict symmetry `ε φᵀ = φ` is Ranicki's `Tφ = φ` (`transposeHom`). -/
theorem isStrictSymm_dualityMap {φ : BasedComplex.Hom (C.dual N hN) C} (h : IsSymm hN φ) :
    IsStrictSymm J N (R.dualityMap φ) := by
  show transposeHom J N (R.dualityMap φ) = R.dualityMap φ
  ext r
  rw [transposeHom_f, dualityMap_f, dualityMap_f, R.star_mat, eqToHom_complex_X,
    ← R.mat_mul, blk_transpose, blk_mul' _ _ fun κ σ h₁ hσ ↦ by
      obtain rfl : κ = σ := by by_contra h'; exact h₁ (one_apply_ne (Ne.symm h'))
      change (C.deg κ : ℤ) = r at hσ; omega, Matrix.one_mul, R.mat_units_smul]
  congr 1
  ext σ τ
  have hσ : (C.deg σ.1 : ℤ) = r := σ.2
  have hle := hN σ.1
  have hc : (((r * (N - r)).negOnePow : ℤˣ) : ℤ) =
      (((C.deg σ.1 * (N - C.deg σ.1) : ℕ) : ℤ).negOnePow : ℤˣ) := by
    congr 2; push_cast [Nat.cast_sub hle]; rw [hσ]
  simp only [Matrix.smul_apply, submatrix_apply, transpose_apply, smul_eq_mul, hc,
    Int.cast_negOnePow_natCast, ← eps_eq_neg_one_pow C hN]
  · exact (isSymm_iff φ).mp h σ.1 τ.1
  · omega

/-- A based symmetric duality as an M1 strictly symmetric Poincaré complex, with `p = 1`. -/
@[implicit_reducible] def symPoincare (P : SymDuality C N hN) : SymPoincare J N where
  C := R.complex C
  p := 𝟙 _
  p_idem := by simp
  support r hr := by
    show 𝟙 (R.obj (Cells C r)) = 0
    rw [← R.mat_one, show (1 : Matrix (Cells C r) (Cells C r) ℚ) = 0 from ?_, R.mat_zero]
    ext σ
    have := hN σ.1
    have : (C.deg σ.1 : ℤ) = r := σ.2
    omega
  φ := R.dualityMap P.hom
  φ_kar := by simp
  symm := R.isStrictSymm_dualityMap P.symm
  poincare := by
    refine ⟨R.hom P.inv ≫ (R.dualIso N C hN).inv, by simp, ⟨?_⟩, ⟨?_⟩⟩
    · refine homotopyCongr (R.htpy P.invHom) ?_ (R.hom_id C)
      rw [R.hom_comp]; simp [dualityMap]
    · refine homotopyCongr (((R.htpy P.homInv).compRight (R.dualIso N C hN).inv).compLeft
        (R.dualIso N C hN).hom) ?_ ?_
      · rw [R.hom_comp]; simp [dualityMap]
      · simp [R.hom_id]

theorem symPoincare_φ (P : SymDuality C N hN) : (R.symPoincare P).φ = R.dualityMap P.hom := rfl

end MatRealization

namespace BasedComplex

variable {V : Type u} [Category.{v} V] [Preadditive V] {J : StrictInvolution V}
  (R : MatRealization J)

/-- The final signature-one class (l. 1093): `CPcell` as an M1 strictly symmetric Poincaré
complex of dimension `4`. -/
def CPcell.symPoincare : SymPoincare J 4 := R.symPoincare CPcell.duality

/-- The middle component of its duality map is the identity on the middle cell `e₂`: the
middle form is `⟨1⟩` (`CPcell.middleForm_eq`, `CPcell.ratSignature_middleForm`). -/
theorem CPcell.symPoincare_φ_middle :
    (CPcell.symPoincare R).φ.f 2 = R.mat (MatRealization.blk 1
      (fun σ ↦ (CPcell.deg σ : ℤ) = 4 - 2) fun σ ↦ (CPcell.deg σ : ℤ) = 2) := by
  show (R.symPoincare CPcell.duality).φ.f 2 = _
  rw [MatRealization.symPoincare_φ, MatRealization.dualityMap_f]
  congr 1
  ext ⟨i, hi⟩ ⟨j, hj⟩
  change ((2 * (i : ℕ) : ℕ) : ℤ) = 2 at hi
  change ((2 * (j : ℕ) : ℕ) : ℤ) = (4 : ℕ) - 2 at hj
  have hi' : i = 1 := Fin.ext (by simp; omega)
  have hj' : j = 1 := Fin.ext (by simp; omega)
  subst hi' hj'
  simp [CPcell.duality_hom, CPcell.φ_f]

end BasedComplex

end HSFormal.Cubical
