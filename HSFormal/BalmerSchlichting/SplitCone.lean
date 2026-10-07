import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.Algebra.Homology.HomologicalComplexBiprod

/-!
# A split contractible complex

For a chain complex `X` indexed by `ℤ`, `splitCone X` has `X_j ⊞ X_{j+1}` in degree `j`, with
differential the identity from the first summand in degree `j + 1` to the second summand in
degree `j`. It is the direct sum of the cones of the identities of the `X_j`, and is contractible.
-/

namespace HSFormal.HomotopyIdempotent

open CategoryTheory Category Limits Preadditive

universe v u

variable {P : Type u} [Category.{v} P] [Preadditive P]

lemma comm_succ {K L : ChainComplex P ℤ} {f g : K ⟶ L} (h : Homotopy f g) (m : ℤ) :
    f.f (m + 1) = K.d (m + 1) m ≫ h.hom m (m + 1) +
      h.hom (m + 1) (m + 1 + 1) ≫ L.d (m + 1 + 1) (m + 1) + g.f (m + 1) := by
  rw [h.comm (m + 1), dNext_eq _ (show (ComplexShape.down ℤ).Rel (m + 1) m from rfl),
    prevD_eq _ (show (ComplexShape.down ℤ).Rel (m + 1 + 1) (m + 1) from rfl)]

lemma nullHomotopicMap_f_succ {K L : ChainComplex P ℤ} (H : ∀ i j, K.X i ⟶ L.X j) (m : ℤ) :
    (Homotopy.nullHomotopicMap H).f (m + 1) =
      K.d (m + 1) m ≫ H m (m + 1) + H (m + 1) (m + 1 + 1) ≫ L.d (m + 1 + 1) (m + 1) :=
  Homotopy.nullHomotopicMap_f (show (ComplexShape.down ℤ).Rel (m + 1 + 1) (m + 1) from rfl)
    (show (ComplexShape.down ℤ).Rel (m + 1) m from rfl) H

/-- A homotopy between `f` and `g` is one between `f'` and `g'` when `f - g = f' - g'`. -/
@[simps]
def Homotopy.congrSub {K L : ChainComplex P ℤ} {f g f' g' : K ⟶ L} (H : Homotopy f g)
    (w : f - g = f' - g') : Homotopy f' g' where
  hom := H.hom
  zero := H.zero
  comm i := by
    have h₁ := H.comm i
    have h₂ := congrArg (fun φ ↦ φ.f i) w
    simp only [HomologicalComplex.sub_f_apply] at h₂
    rw [← sub_eq_iff_eq_add] at h₁ ⊢
    rw [← h₂, h₁]

variable [HasBinaryBiproducts P]

/-- The split contractible complex with `X_j ⊞ X_{j+1}` in degree `j`. -/
@[reducible] noncomputable def splitCone (X : ChainComplex P ℤ) : ChainComplex P ℤ where
  X j := X.X j ⊞ X.X (j + 1)
  d i j := if h : i = j + 1 then biprod.fst ≫ (X.XIsoOfEq h).hom ≫ biprod.inr else 0
  shape i j hij := dite_eq_right fun h ↦ hij h.symm
  d_comp_d' i j k hij hjk := by
    rw [dite_eq_left hij.symm, dite_eq_left hjk.symm]
    simp

variable (X : ChainComplex P ℤ)

lemma splitCone_d (j : ℤ) :
    (splitCone X).d (j + 1) j = (biprod.fst ≫ biprod.inr : X.X (j + 1) ⊞ _ ⟶ X.X j ⊞ _) := by
  simp [splitCone]

/-- The contraction of `splitCone X`. -/
noncomputable def splitCone.contraction : Homotopy (𝟙 (splitCone X)) 0 where
  hom i j := if h : j = i + 1 then
    (biprod.snd ≫ (X.XIsoOfEq h.symm).hom ≫ biprod.inl : X.X i ⊞ X.X (i + 1) ⟶ X.X j ⊞ _) else 0
  zero i j hij := dite_eq_right fun h ↦ hij h.symm
  comm i := by
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel (m + 1) m from rfl),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (m + 1 + 1) (m + 1) from rfl)]
    simp only [splitCone_d, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, id_comp, dite_true,
      HomologicalComplex.id_f, HomologicalComplex.zero_f, add_zero, assoc, biprod.inr_snd_assoc,
      biprod.inl_fst_assoc]
    exact biprod.total.symm

end HSFormal.HomotopyIdempotent
