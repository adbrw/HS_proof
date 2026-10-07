import HSFormal.FiniteMatrixSupport
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Propagation and reachable-band factorizations for labelled rational matrices

These are finite-matrix foundations for manuscript Sections 2 and 9.  They prove
support bounds and an exact matrix factorization. They do not define the
asymptotic categories, Poincaré structures, or L-groups used by the manuscript.
-/

noncomputable section

namespace HSFormal

open Filter Matrix
open scoped Classical

universe u v w x u' v'

variable {A : Type u} {B : Type v} {C : Type w} {X : Type x}
variable [PseudoMetricSpace X]

/-- Every nonzero entry connects labels at distance at most `r`. The row label
is the target and the column label is the source. -/
def HasPropagationLE (u : Matrix B A ℚ)
    (source : A → X) (target : B → X) (r : ℝ) : Prop :=
  MatrixSupportedBy u (fun b a ↦ dist (target b) (source a) ≤ r)

theorem hasPropagationLE_mono (u : Matrix B A ℚ)
    (source : A → X) (target : B → X) {r s : ℝ}
    (hu : HasPropagationLE u source target r) (hrs : r ≤ s) :
    HasPropagationLE u source target s := by
  intro b a hba
  exact (hu b a hba).trans hrs

/-- Rectangular matrix multiplication adds propagation bounds; a nonzero
product entry has an actual nonzero intermediate summand. -/
theorem hasPropagationLE_mul [Fintype B]
    (u : Matrix B A ℚ) (v : Matrix C B ℚ)
    (source : A → X) (middle : B → X) (target : C → X)
    (r s : ℝ) (hu : HasPropagationLE u source middle r)
    (hv : HasPropagationLE v middle target s) :
    HasPropagationLE (v * u) source target (r + s) := by
  intro c a hca
  obtain ⟨b, hvb, huba⟩ := matrix_mul_entry_nonzero_witness u v c a hca
  calc
    dist (target c) (source a) ≤
        dist (target c) (middle b) + dist (middle b) (source a) :=
      dist_triangle _ _ _
    _ ≤ s + r := add_le_add (hv c b hvb) (hu b a huba)
    _ = r + s := add_comm _ _

theorem hasPropagationLE_add (u v : Matrix B A ℚ)
    (source : A → X) (target : B → X)
    (r s : ℝ) (hu : HasPropagationLE u source target r)
    (hv : HasPropagationLE v source target s) :
    HasPropagationLE (u + v) source target (max r s) := by
  have hsupport := matrixSupportedBy_add u v
    (fun b a ↦ dist (target b) (source a) ≤ r)
    (fun b a ↦ dist (target b) (source a) ≤ s) hu hv
  intro b a hba
  rcases hsupport b a hba with hr | hs
  · exact hr.trans (le_max_left r s)
  · exact hs.trans (le_max_right r s)

/-- Transpose, the manuscript's duality operation, preserves the bound. -/
theorem hasPropagationLE_transpose (u : Matrix B A ℚ)
    (source : A → X) (target : B → X) (r : ℝ)
    (hu : HasPropagationLE u source target r) :
    HasPropagationLE u.transpose target source r := by
  intro a b hab
  change u b a ≠ 0 at hab
  rw [dist_comm]
  exact hu b a hab

/-- Restricting rows and columns preserves the original labels and bound. -/
theorem hasPropagationLE_submatrix {A' : Type u'} {B' : Type v'}
    (u : Matrix B A ℚ) (source : A → X) (target : B → X)
    (f : A' → A) (g : B' → B) (r : ℝ)
    (hu : HasPropagationLE u source target r) :
    HasPropagationLE (u.submatrix g f) (source ∘ f) (target ∘ g) r := by
  exact matrixSupportedBy_submatrix u (fun b a ↦ dist (target b) (source a) ≤ r) f g hu

theorem hasPropagationLE_one [Fintype A] (label : A → X) :
    HasPropagationLE (1 : Matrix A A ℚ) label label 0 := by
  intro b a hba
  by_cases h : b = a
  · subst a
    simp
  · exact (hba (by simp [h])).elim

/-- Based diagonal projections have propagation zero. -/
theorem hasPropagationLE_diagonal_zero (d : A → ℚ) (label : A → X) :
    HasPropagationLE (Matrix.diagonal d) label label 0 := by
  intro b a hba
  by_cases h : b = a
  · subst a
    simp
  · exact (hba (Matrix.diagonal_apply_ne d h)).elim

/-- Any finite word of matrices of propagation at most `ε` has propagation
at most its length times `ε`. -/
theorem hasPropagationLE_word [Fintype A]
    (label : A → X) (word : List (Matrix A A ℚ)) (ε : ℝ)
    (hword : ∀ u ∈ word, HasPropagationLE u label label ε) :
    HasPropagationLE word.prod label label ((word.length : ℝ) * ε) := by
  revert hword
  induction word with
  | nil =>
      intro _
      simpa using hasPropagationLE_one label
  | cons u word ih =>
      intro hword
      have hu := hword u (by simp)
      have hw : ∀ v ∈ word, HasPropagationLE v label label ε := by
        intro v hv
        exact hword v (by simp [hv])
      have hmul := hasPropagationLE_mul word.prod u label label label
        ((word.length : ℝ) * ε) ε (ih hw) hu
      simpa only [List.prod_cons, List.length_cons, Nat.cast_add, Nat.cast_one,
        add_mul, one_mul] using hmul

/-- The fixed word-length bound needed for uniform control in Section 9. -/
theorem hasPropagationLE_bounded_word [Fintype A]
    (label : A → X) (word : List (Matrix A A ℚ)) (L : ℕ) (ε : ℝ)
    (hε : 0 ≤ ε) (hlength : word.length ≤ L)
    (hword : ∀ u ∈ word, HasPropagationLE u label label ε) :
    HasPropagationLE word.prod label label ((L : ℝ) * ε) := by
  exact hasPropagationLE_mono _ _ _ (hasPropagationLE_word label word ε hword)
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hlength) hε)

/-- Bounded-length matrix words preserve null propagation bounds even when the
basis type and its cardinality vary with the index. -/
theorem bounded_words_have_null_propagation
    (basis : ℕ → Type u) [∀ i, Fintype (basis i)]
    (label : ∀ i, basis i → X)
    (word : ∀ i, List (Matrix (basis i) (basis i) ℚ))
    (L : ℕ) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (nhds 0))
    (hεnonneg : ∀ i, 0 ≤ ε i) (hlength : ∀ i, (word i).length ≤ L)
    (hword : ∀ i, ∀ u ∈ word i, HasPropagationLE u (label i) (label i) (ε i)) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (nhds 0) ∧
      ∀ i, HasPropagationLE (word i).prod (label i) (label i) (δ i) := by
  refine ⟨fun i ↦ (L : ℝ) * ε i, ?_, ?_⟩
  · simpa only [mul_zero] using hε.const_mul (L : ℝ)
  · intro i
    exact hasPropagationLE_bounded_word (label i) (word i) L (ε i)
      (hεnonneg i) (hlength i) (hword i)

/-- The annular set of far rows that can be reached from a source in the
`t + κ` ball by a matrix of propagation at most `r`. -/
def reachableFarBand (middle : B → X) (y : X) (t κ r : ℝ) : Set B :=
  {b | t < dist (middle b) y ∧ dist (middle b) y ≤ t + κ + r}

theorem nonzero_row_mem_reachable_far_band
    (u : Matrix B A ℚ) (source : A → X) (middle : B → X)
    (y : X) (t κ r : ℝ) (hu : HasPropagationLE u source middle r)
    (hsource : ∀ a, dist (source a) y ≤ t + κ)
    (b : B) (a : A) (hba : u b a ≠ 0) (hfar : t < dist (middle b) y) :
    b ∈ reachableFarBand middle y t κ r := by
  refine ⟨hfar, ?_⟩
  calc
    dist (middle b) y ≤ dist (middle b) (source a) + dist (source a) y :=
      dist_triangle _ _ _
    _ ≤ r + (t + κ) := add_le_add (hu b a hba) (hsource a)
    _ = t + κ + r := add_comm _ _

/-- The based projection onto rows outside the radius-`t` ball. -/
def farProjection [Fintype B] (middle : B → X) (y : X) (t : ℝ) : Matrix B B ℚ :=
  Matrix.diagonal fun b ↦ if t < dist (middle b) y then 1 else 0

/-- The far projection is fixed by rational transpose duality. -/
theorem farProjection_transpose [Fintype B]
    (middle : B → X) (y : X) (t : ℝ) :
    (farProjection middle y t).transpose = farProjection middle y t := by
  exact Matrix.diagonal_transpose _

theorem farProjection_idempotent [Fintype B]
    (middle : B → X) (y : X) (t : ℝ) :
    farProjection middle y t * farProjection middle y t = farProjection middle y t := by
  simp only [farProjection, Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext b
  by_cases h : t < dist (middle b) y
  · simp [h]
  · simp [h]

theorem hasPropagationLE_farProjection [Fintype B]
    (middle : B → X) (y : X) (t : ℝ) :
    HasPropagationLE (farProjection middle y t) middle middle 0 := by
  exact hasPropagationLE_diagonal_zero _ middle

/-- An exact reachable-band factorization, rather than a propagation estimate
alone. Both factors are based row/column restrictions of the original maps;
their original propagation bounds are preserved by `hasPropagationLE_submatrix`.
The propagation of the prefix is the only bound needed at the cut. -/
theorem far_projection_factors_through_reachable_band [Fintype B]
    (u : Matrix B A ℚ) (v : Matrix C B ℚ)
    (source : A → X) (middle : B → X)
    (y : X) (t κ r : ℝ) (hu : HasPropagationLE u source middle r)
    (hsource : ∀ a, dist (source a) y ≤ t + κ) :
    v * (farProjection middle y t * u) =
      v.submatrix id (Subtype.val : reachableFarBand middle y t κ r → B) *
      u.submatrix (Subtype.val : reachableFarBand middle y t κ r → B) id := by
  have hsupport : MatrixSupportedBy (farProjection middle y t * u)
      (fun b _ ↦ b ∈ reachableFarBand middle y t κ r) := by
    intro b a hba
    have hfar : t < dist (middle b) y := by
      by_contra hn
      exact hba (by simp [farProjection, Matrix.diagonal_mul, hn])
    have huba : u b a ≠ 0 := by
      intro hu0
      exact hba (by simp [farProjection, Matrix.diagonal_mul, hu0])
    exact nonzero_row_mem_reachable_far_band u source middle y t κ r
      hu hsource b a huba hfar
  have hrestrict :
      (farProjection middle y t * u).submatrix
        (Subtype.val : reachableFarBand middle y t κ r → B) id =
      u.submatrix (Subtype.val : reachableFarBand middle y t κ r → B) id := by
    ext b a
    have hfar : t < dist (middle b) y := b.property.1
    simp only [Matrix.submatrix_apply, farProjection, Matrix.diagonal_mul, id_eq,
      ite_eq_left hfar, one_mul]
  simpa only [hrestrict] using matrix_mul_factors_through_supported_rows
    (farProjection middle y t * u) v (reachableFarBand middle y t κ r) hsupport

end HSFormal
