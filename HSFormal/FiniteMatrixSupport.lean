import Mathlib.Data.Matrix.Mul

/-!
# Exact finite-matrix support algebra

This is the finite algebra underlying support estimates and based cuts in
manuscript Sections 2 and 9. Matrix entries may lie in any semiring of the
stated type; in particular the results apply to the rational matrices in the
manuscript. No controlled-category or L-theory structure is assumed here.
-/

noncomputable section

namespace HSFormal

open Matrix
open scoped Classical

universe u v w r u' v'

variable {A : Type u} {B : Type v} {C : Type w} {R : Type r}

/-- A relation contains every pair connected by a nonzero matrix entry. The
first index is a target row and the second is a source column. -/
def MatrixSupportedBy [Zero R] (u : Matrix B A R) (support : B → A → Prop) : Prop :=
  ∀ b a, u b a ≠ 0 → support b a

theorem matrixSupportedBy_submatrix [Zero R] {A' : Type u'} {B' : Type v'}
    (u : Matrix B A R) (support : B → A → Prop)
    (f : A' → A) (g : B' → B) (hu : MatrixSupportedBy u support) :
    MatrixSupportedBy (u.submatrix g f) (fun b a ↦ support (g b) (f a)) := by
  intro b a hba
  exact hu (g b) (f a) hba

section Semiring

variable [NonUnitalNonAssocSemiring R]

/-- A nonzero entry of a rectangular product has an actual intermediate index
where both constituent entries are nonzero. -/
theorem matrix_mul_entry_nonzero_witness [Fintype B]
    (u : Matrix B A R) (v : Matrix C B R) (c : C) (a : A)
    (hca : (v * u) c a ≠ 0) :
    ∃ b, v c b ≠ 0 ∧ u b a ≠ 0 := by
  have hsum : (∑ b, v c b * u b a) ≠ 0 := by
    simpa only [Matrix.mul_apply] using hca
  obtain ⟨b, _, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  exact ⟨b, left_ne_zero_of_mul hb, right_ne_zero_of_mul hb⟩

/-- Product support is contained in the relational composite of the two
supports, in the same order as the matrix composition. -/
theorem matrixSupportedBy_mul [Fintype B]
    (u : Matrix B A R) (v : Matrix C B R)
    (supportU : B → A → Prop) (supportV : C → B → Prop)
    (hu : MatrixSupportedBy u supportU) (hv : MatrixSupportedBy v supportV) :
    MatrixSupportedBy (v * u)
      (fun c a ↦ ∃ b, supportV c b ∧ supportU b a) := by
  intro c a hca
  obtain ⟨b, hvb, huba⟩ := matrix_mul_entry_nonzero_witness u v c a hca
  exact ⟨b, hv c b hvb, hu b a huba⟩

theorem matrixSupportedBy_add
    (u v : Matrix B A R) (supportU supportV : B → A → Prop)
    (hu : MatrixSupportedBy u supportU) (hv : MatrixSupportedBy v supportV) :
    MatrixSupportedBy (u + v) (fun b a ↦ supportU b a ∨ supportV b a) := by
  intro b a hba
  change u b a + v b a ≠ 0 at hba
  by_cases hu0 : u b a = 0
  · right
    apply hv b a
    intro hv0
    exact hba (by simp [hu0, hv0])
  · exact Or.inl (hu b a hu0)

/-- Cutting away rows where the prefix is zero gives an exact factorization
through a based subset, without changing any retained coefficients. -/
theorem matrix_mul_factors_through_rows [Fintype B]
    (u : Matrix B A R) (v : Matrix C B R) (rows : Set B)
    (hzero : ∀ b, b ∉ rows → ∀ a, u b a = 0) :
    v * u =
      v.submatrix id (Subtype.val : rows → B) *
      u.submatrix (Subtype.val : rows → B) id := by
  ext c a
  change (∑ b, v c b * u b a) = ∑ b : rows, v c b * u b a
  apply Finset.sum_congr_set rows
  · intro b hb
    rfl
  · intro b hb
    simp [hzero b hb a]

/-- The same exact factorization with its premise stated as containment of all
nonzero prefix rows, as in the manuscript's reachable-row cut. -/
theorem matrix_mul_factors_through_supported_rows [Fintype B]
    (u : Matrix B A R) (v : Matrix C B R) (rows : Set B)
    (hu : MatrixSupportedBy u (fun b _ ↦ b ∈ rows)) :
    v * u =
      v.submatrix id (Subtype.val : rows → B) *
      u.submatrix (Subtype.val : rows → B) id := by
  apply matrix_mul_factors_through_rows u v rows
  intro b hb a
  by_contra hba
  exact hb (hu b a hba)

end Semiring

end HSFormal
