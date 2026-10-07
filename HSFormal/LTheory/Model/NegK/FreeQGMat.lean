import HSFormal.LTheory.Interface
import Mathlib.RepresentationTheory.Maschke

/-!
# Morphisms of `finSuppFreeQG G T` as `ℚ[Gᵢ]`-linear maps (NegK level 1, module 1)

`blueprint/negK-proof.md` §1 "Per-fibre dictionary".

A morphism `f : M ⟶ N` of `prodFreeQG G` is a family over `i : ℕ` of equivariant rational
matrices `f.1 i : Matrix (Fin (N.rank i) × G i) (Fin (M.rank i) × G i) ℚ`.  With
`Λᵢ = ℚ[Gᵢ] = MonoidAlgebra ℚ (G i)`:

* `toMat f k k' = ∑_g f (k', g) (k, 1) g` is a `Λᵢ`-matrix, and `linOf f : x ↦ x ᵥ* toMat f` is
  left `Λᵢ`-linear on `Fin m → Λᵢ`.  Under the flattening `flat : (Fin m → Λᵢ) ≅ ℚ^{Fin m × Gᵢ}`
  it is the original matrix action (`flat_linOf`, for equivariant `f`), whence functoriality.
* `ofMat C (k', h') (k, h) = C k k' (h⁻¹ h')` is equivariant with `toMat (ofMat C) = C`, and every
  `Λᵢ`-linear map is `x ↦ x ᵥ* C` (`linearMap_eq_vecMul`).

For `B = finSuppFreeQG G T` this gives the fibre functors `lin f i : Fib M i →ₗ[Λᵢ] Fib N i`
(`lin_comp`, `lin_id`, `lin_add`, `lin_zero`, `lin_sum`), jointly faithful (`lin_ext`) and full:
any family over **all** `i` of `Λᵢ`-linear maps is `lin (ofLin L)` (`lin_ofLin`).  Control is
vacuous over `PUnit`.  `instNeZeroCard` supplies the hypothesis of Maschke's theorem, so every
`Λᵢ`-module is semisimple.
-/

namespace HSFormal.LTheory.FreeQGMat

open CategoryTheory Matrix

noncomputable section

/-! ### One group -/

section Generic

variable {Γ : Type} [Group Γ] [Fintype Γ] {l m n : ℕ}

/-- Maschke's hypothesis over `ℚ`. -/
instance instNeZeroCard : NeZero (Fintype.card Γ : ℚ) :=
  ⟨Nat.cast_ne_zero.mpr Fintype.card_ne_zero⟩

/-- The `ℚ[Γ]`-matrix of a `ℚ`-matrix on free `Γ`-bases: `toMat f k k' = ∑_g f (k', g) (k, 1) g`. -/
def toMat (f : Matrix (Fin n × Γ) (Fin m × Γ) ℚ) : Matrix (Fin m) (Fin n) (MonoidAlgebra ℚ Γ) :=
  fun k k' ↦ MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun g ↦ f (k', g) (k, 1))

lemma toMat_apply (f : Matrix (Fin n × Γ) (Fin m × Γ) ℚ) (k : Fin m) (k' : Fin n) (g : Γ) :
    (toMat f k k').coeff g = f (k', g) (k, 1) := rfl

lemma toMat_add (f f' : Matrix (Fin n × Γ) (Fin m × Γ) ℚ) :
    toMat (f + f') = toMat f + toMat f' := by
  ext k k' g
  change (toMat (f + f') k k').coeff g = ((toMat f k k').coeff + (toMat f' k k').coeff) g
  rw [Finsupp.add_apply]
  rfl

lemma toMat_zero : toMat (0 : Matrix (Fin n × Γ) (Fin m × Γ) ℚ) = 0 := by
  ext k k' g
  change (toMat 0 k k').coeff g = (0 : Γ →₀ ℚ) g
  rfl

/-- A `ℚ[Γ]`-matrix as an equivariant `ℚ`-matrix: `ofMat C (k', h') (k, h) = C k k' (h⁻¹ h')`. -/
def ofMat (C : Matrix (Fin m) (Fin n) (MonoidAlgebra ℚ Γ)) : Matrix (Fin n × Γ) (Fin m × Γ) ℚ :=
  fun b' b ↦ (C b.1 b'.1).coeff (b.2⁻¹ * b'.2)

omit [Fintype Γ] in
lemma ofMat_equivariant (C : Matrix (Fin m) (Fin n) (MonoidAlgebra ℚ Γ)) :
    IsEquivariant (ofMat C) := by
  intro g b' b
  simp only [ofMat, mul_inv_rev, mul_assoc, inv_mul_cancel_left]

lemma toMat_ofMat (C : Matrix (Fin m) (Fin n) (MonoidAlgebra ℚ Γ)) : toMat (ofMat C) = C := by
  ext k k' g
  rw [toMat_apply, ofMat]
  simp

/-- Flattening `(Fin m → ℚ[Γ]) → (Fin m × Γ → ℚ)`. -/
def flat (x : Fin m → MonoidAlgebra ℚ Γ) : Fin m × Γ → ℚ := fun b ↦ (x b.1).coeff b.2

omit [Group Γ] [Fintype Γ] in
lemma flat_injective : Function.Injective (flat : (Fin m → MonoidAlgebra ℚ Γ) → Fin m × Γ → ℚ) :=
  fun _ _ h ↦ funext fun k ↦ MonoidAlgebra.ext (Finsupp.ext fun g ↦ congrFun h (k, g))

omit [Group Γ] in
lemma flat_surjective :
    Function.Surjective (flat : (Fin m → MonoidAlgebra ℚ Γ) → Fin m × Γ → ℚ) :=
  fun φ ↦ ⟨fun k ↦ MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun g ↦ φ (k, g)), rfl⟩

/-- **The dictionary**: for equivariant `f`, `x ᵥ* toMat f` is the `ℚ`-action of `f`. -/
theorem flat_vecMul {f : Matrix (Fin n × Γ) (Fin m × Γ) ℚ} (hf : IsEquivariant f)
    (x : Fin m → MonoidAlgebra ℚ Γ) : flat (x ᵥ* toMat f) = f *ᵥ flat x := by
  funext ⟨k', h'⟩
  simp only [flat, vecMul, dotProduct, mulVec]
  rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype _ _ fun _ ↦ zero_mul _]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [toMat_apply, mul_comm]
  congr 1
  simpa using (hf a (k', a⁻¹ * h') (k, 1)).symm

variable (Γ) in
/-- The left `ℚ[Γ]`-linear map `x ↦ x ᵥ* toMat f`. -/
def linOf (f : Matrix (Fin n × Γ) (Fin m × Γ) ℚ) :
    (Fin m → MonoidAlgebra ℚ Γ) →ₗ[MonoidAlgebra ℚ Γ] (Fin n → MonoidAlgebra ℚ Γ) where
  toFun x := x ᵥ* toMat f
  map_add' x y := add_vecMul _ x y
  map_smul' c x := smul_vecMul c x _

lemma linOf_apply (f : Matrix (Fin n × Γ) (Fin m × Γ) ℚ) (x : Fin m → MonoidAlgebra ℚ Γ) :
    linOf Γ f x = x ᵥ* toMat f := rfl

lemma flat_linOf {f : Matrix (Fin n × Γ) (Fin m × Γ) ℚ} (hf : IsEquivariant f)
    (x : Fin m → MonoidAlgebra ℚ Γ) : flat (linOf Γ f x) = f *ᵥ flat x :=
  flat_vecMul hf x

lemma linOf_mul {f : Matrix (Fin n × Γ) (Fin m × Γ) ℚ} {g : Matrix (Fin l × Γ) (Fin n × Γ) ℚ}
    (hf : IsEquivariant f) (hg : IsEquivariant g) :
    linOf Γ (g * f) = (linOf Γ g).comp (linOf Γ f) := by
  refine LinearMap.ext fun x ↦ flat_injective ?_
  rw [LinearMap.comp_apply, flat_linOf (hg.mul hf), flat_linOf hg, flat_linOf hf, mulVec_mulVec]

lemma linOf_add (f f' : Matrix (Fin n × Γ) (Fin m × Γ) ℚ) :
    linOf Γ (f + f') = linOf Γ f + linOf Γ f' := by
  refine LinearMap.ext fun x ↦ ?_
  simp [linOf_apply, toMat_add, vecMul_add]

lemma linOf_zero : linOf Γ (0 : Matrix (Fin n × Γ) (Fin m × Γ) ℚ) = 0 := by
  refine LinearMap.ext fun x ↦ ?_
  simp [linOf_apply, toMat_zero]

lemma linOf_ofMat (C : Matrix (Fin m) (Fin n) (MonoidAlgebra ℚ Γ)) (x : Fin m → MonoidAlgebra ℚ Γ) :
    linOf Γ (ofMat C) x = x ᵥ* C := by
  rw [linOf_apply, toMat_ofMat]

/-- The matrix of a `ℚ[Γ]`-linear map: `repMat L k k' = (L (Pi.single k 1)) k'`. -/
def repMat (L : (Fin m → MonoidAlgebra ℚ Γ) →ₗ[MonoidAlgebra ℚ Γ] (Fin n → MonoidAlgebra ℚ Γ)) :
    Matrix (Fin m) (Fin n) (MonoidAlgebra ℚ Γ) :=
  fun k k' ↦ L (Pi.single k 1) k'

omit [Fintype Γ] in
lemma linearMap_eq_vecMul
    (L : (Fin m → MonoidAlgebra ℚ Γ) →ₗ[MonoidAlgebra ℚ Γ] (Fin n → MonoidAlgebra ℚ Γ))
    (x : Fin m → MonoidAlgebra ℚ Γ) : L x = x ᵥ* repMat L := by
  have hx : x = ∑ k, x k • (Pi.single k (1 : MonoidAlgebra ℚ Γ) : Fin m → MonoidAlgebra ℚ Γ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  funext k'
  simp [map_sum, map_smul, vecMul, dotProduct, Finset.sum_apply, repMat]

lemma linOf_ofMat_repMat
    (L : (Fin m → MonoidAlgebra ℚ Γ) →ₗ[MonoidAlgebra ℚ Γ] (Fin n → MonoidAlgebra ℚ Γ)) :
    linOf Γ (ofMat (repMat L)) = L := by
  refine LinearMap.ext fun x ↦ ?_
  rw [linOf_ofMat, linearMap_eq_vecMul L x]

/-- Equivariant matrices with the same `linOf` are equal. -/
lemma eq_of_linOf_eq {f g : Matrix (Fin n × Γ) (Fin m × Γ) ℚ} (hf : IsEquivariant f)
    (hg : IsEquivariant g) (h : linOf Γ f = linOf Γ g) : f = g := by
  classical
  have h' : ∀ φ : Fin m × Γ → ℚ, f *ᵥ φ = g *ᵥ φ := fun φ ↦ by
    obtain ⟨x, rfl⟩ := flat_surjective φ
    rw [← flat_linOf hf, ← flat_linOf hg, h]
  ext b' b
  have := congrFun (h' (Pi.single b 1)) b'
  simpa [mulVec_single_one] using this

end Generic

/-! ### The fibre functors of `finSuppFreeQG G T` -/

section Category

variable {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)] {T : Set ℕ}

/-- The fibre `Λᵢ^{rank_i M}` of an object. -/
abbrev Fib (M : finSuppFreeQG G T) (i : ℕ) : Type := Fin (M.obj.rank i) → MonoidAlgebra ℚ (G i)

/-- The fibre map of a morphism: `x ↦ x ᵥ* toMat (f i)`. -/
def lin {M N : finSuppFreeQG G T} (f : M ⟶ N) (i : ℕ) :
    Fib M i →ₗ[MonoidAlgebra ℚ (G i)] Fib N i :=
  linOf (G i) (f.hom.1 i)

variable {M N P : finSuppFreeQG G T}

lemma lin_comp (f : M ⟶ N) (g : N ⟶ P) (i : ℕ) : lin (f ≫ g) i = (lin g i).comp (lin f i) :=
  linOf_mul (AsymptoticObject.equivariant f.hom i) (AsymptoticObject.equivariant g.hom i)

lemma lin_id (M : finSuppFreeQG G T) (i : ℕ) : lin (𝟙 M) i = LinearMap.id := by
  classical
  have h : (𝟙 M : M ⟶ M).hom = 𝟙 M.obj := rfl
  refine LinearMap.ext fun x ↦ flat_injective ?_
  rw [lin, h, flat_linOf (AsymptoticObject.equivariant (𝟙 M.obj) i), AsymptoticObject.id_val,
    one_mulVec]
  rfl

lemma lin_add (f g : M ⟶ N) (i : ℕ) : lin (f + g) i = lin f i + lin g i :=
  linOf_add (f.hom.1 i) (g.hom.1 i)

lemma lin_zero (i : ℕ) : lin (0 : M ⟶ N) i = 0 :=
  linOf_zero

lemma lin_sum {ι : Type*} (s : Finset ι) (f : ι → (M ⟶ N)) (i : ℕ) :
    lin (∑ j ∈ s, f j) i = ∑ j ∈ s, lin (f j) i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [lin_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, lin_add, ih]

/-- The fibre functors are jointly faithful. -/
lemma lin_ext {f g : M ⟶ N} (h : ∀ i, lin f i = lin g i) : f = g :=
  ObjectProperty.hom_ext _ <| AsymptoticObject.hom_ext fun i ↦
    eq_of_linOf_eq (AsymptoticObject.equivariant f.hom i) (AsymptoticObject.equivariant g.hom i)
      (h i)

lemma lin_eq_zero {f : M ⟶ N} (h : ∀ i, lin f i = 0) : f = 0 :=
  lin_ext fun i ↦ (h i).trans (lin_zero (M := M) (N := N) i).symm

lemma prop_punit {A B : Type*} (u : Matrix B A ℚ) (s : A → PUnit) (t : B → PUnit) :
    prop u s t = 0 :=
  le_antisymm (prop_le_iff.mpr fun _ _ _ ↦ by simp) bot_le

/-- The morphism with prescribed fibre maps (all `i : ℕ`; control is vacuous). -/
def ofLin (L : ∀ i, Fib M i →ₗ[MonoidAlgebra ℚ (G i)] Fib N i) : M ⟶ N :=
  ObjectProperty.homMk
    ⟨fun i ↦ ofMat (repMat (L i)),
      ⟨fun _ ↦ ofMat_equivariant _,
        tendsto_zero_of_forall_eq_zero fun _ ↦ prop_punit _ _ _⟩⟩

lemma lin_ofLin (L : ∀ i, Fib M i →ₗ[MonoidAlgebra ℚ (G i)] Fib N i) (i : ℕ) :
    lin (ofLin L) i = L i :=
  linOf_ofMat_repMat (L i)

end Category

end

end HSFormal.LTheory.FreeQGMat
