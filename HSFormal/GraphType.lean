import HSFormal.AsymptoticSupport
import Mathlib.Data.Matrix.Basic

/-!
# Graph type and the free-sheet translation (manuscript §§5, 8–10)

A labelled rational matrix has *graph type* `h ∈ H` (§8, l.544–548) when each nonzero entry
from `a` to `b` has `d(target b, h • source a)` small; `graphProp` is the largest such
distance.  Graph types multiply under composition, are inverted by transpose duality, and the
identity has type `1`.  For `X = T × Y` with `H` acting on `T` only this is the manuscript's pair
of conditions (`graphProp_prod_le_iff`).

For a group `Γ`, `sheet g u = u ⊗ R_{g⁻¹}` copies `u` from sheet `s` to sheet `s g⁻¹` (l.294,
with `R_h : b ↦ b h`, blueprint s10-11 S5).  With the sheet labels `ρ s • ℓ` of (10.1) its
propagation is exactly the graph error of `u` at `ρ g` (`prop_sheet`): graph displacement and
sheet shift cancel (l.851).  Hence families of graph type `τ i j`, uniformly in `j`, become
morphisms of `𝒜_G(X)` and `ℬ_{G,Z}(X)` after the shift, and so do their sums such as the
averaged projector (10.2).  The free-sheet functor `𝒜_1(X) → 𝒜_G(X)` is the type-`1` case.
Finally the reachable-band factorization of Lemma 9.1 is lifted to the sheets.
-/

noncomputable section

namespace HSFormal

open Filter Matrix CategoryTheory CategoryTheory.Limits Metric
open scoped Classical ENNReal Topology Pointwise

universe u

/-! ### Graph type of a labelled matrix -/

section GraphProp

variable {H X A B C : Type*} [Group H] [MulAction H X] [PseudoEMetricSpace X]
  {u v : Matrix B A ℚ} {source : A → X} {target : B → X}

theorem prop_sum_le {ι : Type*} (s : Finset ι) (w : ι → Matrix B A ℚ) :
    prop (∑ j ∈ s, w j) source target ≤ ⨆ j ∈ s, prop (w j) source target := by
  refine prop_le_iff.mpr fun b a hba ↦ ?_
  rw [Matrix.sum_apply] at hba
  obtain ⟨j, hj, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hba
  exact (edist_le_prop hne).trans (le_iSup₂_of_le j hj le_rfl)

/-- The graph-type-`h` error `sup_{u b a ≠ 0} d(target b, h • source a)` of manuscript §8. -/
def graphProp (h : H) (u : Matrix B A ℚ) (source : A → X) (target : B → X) : ℝ≥0∞ :=
  prop u (fun a ↦ h • source a) target

theorem graphProp_le_iff {h : H} {r : ℝ≥0∞} :
    graphProp h u source target ≤ r ↔ ∀ b a, u b a ≠ 0 → edist (target b) (h • source a) ≤ r :=
  prop_le_iff

theorem edist_le_graphProp {h : H} {b : B} {a : A} (hba : u b a ≠ 0) :
    edist (target b) (h • source a) ≤ graphProp h u source target :=
  edist_le_prop (u := u) (source := fun a ↦ h • source a) (target := target) hba

/-- Type `1` is ordinary propagation (2.1). -/
@[simp]
theorem graphProp_one : graphProp (1 : H) u source target = prop u source target := by
  simp [graphProp]

@[simp]
theorem graphProp_zero (h : H) : graphProp h (0 : Matrix B A ℚ) source target = 0 :=
  prop_zero

theorem graphProp_add_le (h : H) :
    graphProp h (u + v) source target ≤
      max (graphProp h u source target) (graphProp h v source target) :=
  prop_add_le

theorem graphProp_smul_le (h : H) (c : ℚ) :
    graphProp h (c • u) source target ≤ graphProp h u source target :=
  prop_smul_le c

@[simp]
theorem graphProp_neg (h : H) : graphProp h (-u) source target = graphProp h u source target :=
  prop_neg

theorem graphProp_sub_le (h : H) :
    graphProp h (u - v) source target ≤
      max (graphProp h u source target) (graphProp h v source target) := by
  simpa [sub_eq_add_neg] using graphProp_add_le (u := u) (v := -v) (source := source)
    (target := target) h

theorem graphProp_submatrix_le {A' B' : Type*} (f : A' → A) (g : B' → B) (h : H) :
    graphProp h (u.submatrix g f) (source ∘ f) (target ∘ g) ≤ graphProp h u source target :=
  prop_submatrix_le (source := fun a ↦ h • source a) f g

/-- Graph-type maps have small propagation in an invariant non-expanding control coordinate,
such as the `f`-coordinate of `T × Sⁿ`. -/
theorem prop_comp_le_graphProp {Y : Type*} [PseudoEMetricSpace Y] {φ : X → Y}
    (hφ : LipschitzWith 1 φ) (hinv : ∀ (h : H) x, φ (h • x) = φ x) (h : H) :
    prop u (φ ∘ source) (φ ∘ target) ≤ graphProp h u source target :=
  prop_le_iff.mpr fun b a hba ↦ by
    have := (hφ.edist_le_mul (target b) (h • source a)).trans
      (by simpa using edist_le_graphProp (h := h) hba)
    simpa [hinv] using this

/-- For `X = T × Y` with `H` acting trivially on `Y`, graph type `h` means that the
`Y`-coordinates approach each other and `d_T(target, h • source) → 0` (manuscript l.546). -/
theorem graphProp_prod_le_iff {T Y : Type*} [PseudoEMetricSpace T] [PseudoEMetricSpace Y]
    [MulAction H T] [MulAction H Y] (htriv : ∀ (h : H) (y : Y), h • y = y)
    {source : A → T × Y} {target : B → T × Y} {h : H} {r : ℝ≥0∞} :
    graphProp h u source target ≤ r ↔ ∀ b a, u b a ≠ 0 →
      edist (target b).1 (h • (source a).1) ≤ r ∧ edist (target b).2 (source a).2 ≤ r := by
  simp only [graphProp_le_iff, Prod.edist_eq, max_le_iff, Prod.smul_fst, Prod.smul_snd, htriv]

variable [IsIsometricSMul H X]

/-- **Graph types multiply:** type `g` after type `h` has type `g * h`. -/
theorem graphProp_mul_le [Fintype B] (g h : H) (w : Matrix C B ℚ) (u : Matrix B A ℚ)
    (source : A → X) (middle : B → X) (target : C → X) :
    graphProp (g * h) (w * u) source target ≤
      graphProp h u source middle + graphProp g w middle target := by
  refine prop_le_iff.mpr fun c a hca ↦ ?_
  obtain ⟨b, hw, hu⟩ := matrix_mul_entry_nonzero_witness u w c a hca
  calc edist (target c) ((g * h) • source a)
      ≤ edist (target c) (g • middle b) + edist (g • middle b) ((g * h) • source a) :=
        edist_triangle _ _ _
    _ = edist (target c) (g • middle b) + edist (middle b) (h • source a) := by
        rw [← smul_smul, edist_smul_left]
    _ ≤ graphProp g w middle target + graphProp h u source middle :=
        add_le_add (edist_le_graphProp hw) (edist_le_graphProp hu)
    _ = _ := add_comm _ _

/-- **Duality inverts graph types.** -/
@[simp]
theorem graphProp_transpose (h : H) :
    graphProp h⁻¹ uᵀ target source = graphProp h u source target := by
  simp only [graphProp, prop, Matrix.transpose_apply]
  rw [iSup_comm]
  refine iSup_congr fun b ↦ iSup_congr fun a ↦ iSup_congr fun _ ↦ ?_
  rw [← edist_smul_left h, smul_inv_smul, edist_comm]

end GraphProp

/-! ### Sheet shifts `u ⊗ R_{g⁻¹}` -/

section Sheet

variable {Γ : Type*} [Group Γ] {A B C : Type*}

/-- The sheet shift `u ⊗ R_{g⁻¹}` of (5.2), (10.2): the block `u` from sheet `s` to `s g⁻¹`. -/
def sheet (g : Γ) (u : Matrix B A ℚ) : Matrix (B × Γ) (A × Γ) ℚ :=
  Matrix.of fun p q ↦ if q.2 = p.2 * g then u p.1 q.1 else 0

@[simp]
theorem sheet_apply (g : Γ) (u : Matrix B A ℚ) (p : B × Γ) (q : A × Γ) :
    sheet g u p q = if q.2 = p.2 * g then u p.1 q.1 else 0 :=
  rfl

theorem sheet_apply_ne_zero {g : Γ} {u : Matrix B A ℚ} {p : B × Γ} {q : A × Γ}
    (h : sheet g u p q ≠ 0) : q.2 = p.2 * g ∧ u p.1 q.1 ≠ 0 := by
  by_cases hq : q.2 = p.2 * g <;> simp_all

@[simp]
theorem sheet_zero (g : Γ) : sheet g (0 : Matrix B A ℚ) = 0 := by
  ext; simp

theorem sheet_add (g : Γ) (u v : Matrix B A ℚ) : sheet g (u + v) = sheet g u + sheet g v := by
  ext p q; by_cases hq : q.2 = p.2 * g <;> simp [hq]

theorem sheet_smul (g : Γ) (c : ℚ) (u : Matrix B A ℚ) : sheet g (c • u) = c • sheet g u := by
  ext p q; by_cases hq : q.2 = p.2 * g <;> simp [hq]

theorem sheet_neg (g : Γ) (u : Matrix B A ℚ) : sheet g (-u) = -sheet g u := by
  ext p q; by_cases hq : q.2 = p.2 * g <;> simp [hq]

theorem sheet_sub (g : Γ) (u v : Matrix B A ℚ) : sheet g (u - v) = sheet g u - sheet g v := by
  ext p q; by_cases hq : q.2 = p.2 * g <;> simp [hq]

/-- The identity is the type-`1` shift of the identity. -/
@[simp]
theorem sheet_one_one [DecidableEq A] : sheet (1 : Γ) (1 : Matrix A A ℚ) = 1 := by
  ext ⟨b, s'⟩ ⟨a, s⟩
  simp only [sheet_apply, mul_one, one_apply, Prod.mk.injEq]
  by_cases hs : s = s'
  · subst hs; simp
  · have : s' ≠ s := Ne.symm hs
    simp [hs, this]

/-- Sheet shifts compose: `(w ⊗ R_{g⁻¹})(u ⊗ R_{h⁻¹}) = wu ⊗ R_{(gh)⁻¹}`. -/
theorem sheet_mul [Fintype B] [Fintype Γ] (g h : Γ) (w : Matrix C B ℚ) (u : Matrix B A ℚ) :
    sheet g w * sheet h u = sheet (g * h) (w * u) := by
  ext ⟨c, s''⟩ ⟨a, s⟩
  simp only [mul_apply, sheet_apply, Fintype.sum_prod_type, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_assoc]
  by_cases hs : s = s'' * (g * h) <;> simp [hs]

/-- Duality reverses the sheet translation. -/
theorem sheet_transpose (g : Γ) (u : Matrix B A ℚ) : (sheet g u)ᵀ = sheet g⁻¹ uᵀ := by
  ext ⟨a, s⟩ ⟨b, s'⟩
  have : s = s' * g ↔ s' = s * g⁻¹ := by
    constructor <;> rintro rfl <;> simp
  simp only [transpose_apply, sheet_apply, this]

theorem isEquivariant_sheet {m n : ℕ} (g : Γ) (u : Matrix (Fin n) (Fin m) ℚ) :
    IsEquivariant (sheet g u) := by
  intro x b' b
  simp only [sheet_apply, mul_assoc, mul_right_inj]

/-- Every equivariant matrix is a sum of sheet shifts, `u = ∑_g u_g ⊗ R_{g⁻¹}` with
`u_g k' k = u (k', 1) (k, g)`; cf. `E_{ab} = q⁻¹ A_{a⁻¹b}` in (5.3). -/
theorem eq_sum_sheet [Fintype Γ] {m n : ℕ} {u : Matrix (Fin n × Γ) (Fin m × Γ) ℚ}
    (hu : IsEquivariant u) : u = ∑ g, sheet g (Matrix.of fun k' k ↦ u (k', 1) (k, g)) := by
  ext ⟨k', s'⟩ ⟨k, s⟩
  rw [Matrix.sum_apply, Finset.sum_eq_single (s'⁻¹ * s)]
  · have := hu s' (k', 1) (k, s'⁻¹ * s)
    simp only [mul_one, mul_inv_cancel_left] at this
    simp [this]
  · intro g _ hg
    rw [sheet_apply, ite_eq_right]
    rintro rfl
    exact hg (by simp)
  · simp

variable {H X : Type*} [Group H] [MulAction H X] [PseudoEMetricSpace X]

/-- The sheet labels (10.1): sheet `s` over `a` is labelled `ρ s • ℓ a`. -/
def sheetLabel (ρ : Γ →* H) (ℓ : A → X) (q : A × Γ) : X :=
  ρ q.2 • ℓ q.1

/-- **Graph displacement and sheet shift cancel** (l.851): the propagation of the shifted
matrix is exactly the graph error of the original. -/
theorem prop_sheet [IsIsometricSMul H X] (ρ : Γ →* H) (g : Γ) (u : Matrix B A ℚ)
    (source : A → X) (target : B → X) :
    prop (sheet g u) (sheetLabel ρ source) (sheetLabel ρ target) =
      graphProp (ρ g) u source target := by
  refine le_antisymm (prop_le_iff.mpr fun p q hpq ↦ ?_) (prop_le_iff.mpr fun b a hba ↦ ?_)
  · obtain ⟨hq, hu⟩ := sheet_apply_ne_zero hpq
    calc edist (sheetLabel ρ target p) (sheetLabel ρ source q)
        = edist (target p.1) (ρ g • source q.1) := by
          rw [sheetLabel, sheetLabel, hq, map_mul, ← smul_smul, edist_smul_left]
      _ ≤ _ := edist_le_graphProp hu
  · have : sheet g u (b, 1) (a, g) ≠ 0 := by simpa using hba
    simpa [sheetLabel] using edist_le_prop (source := sheetLabel ρ source)
      (target := sheetLabel ρ target) this

end Sheet

/-! ### Graph-type families and their sheet shifts in `𝒜_G(X)` -/

section Families

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)]
  {π : ∀ i, G i →* H} {X : Type u} [MulAction H X] [PseudoEMetricSpace X]

namespace AsymptoticObject

/-- Matrix sequences between the orbit representatives, i.e. on one sheet. -/
abbrev ScalarFamily (M N : AsymptoticObject π X) : Type :=
  ∀ i, Matrix (Fin (N.rank i)) (Fin (M.rank i)) ℚ

/-- Families `a i j` of matrix sequences, indexed by `j ∈ J i` (e.g. `J i = G i`). -/
abbrev GraphFamily (J : ℕ → Type*) (M N : AsymptoticObject π X) :=
  ∀ i, J i → Matrix (Fin (N.rank i)) (Fin (M.rank i)) ℚ

omit [PseudoEMetricSpace X] in
theorem fullLabel_eq_sheetLabel (M : AsymptoticObject π X) (i : ℕ) :
    M.fullLabel i = sheetLabel (π i) (M.label i) :=
  rfl

variable {M N P : AsymptoticObject π X} {J J' : ℕ → Type*}

/-- Manuscript §8: the sequence `u` has graph type `g = (g i)`. -/
def IsGraphType (g : ∀ i, G i) (u : ScalarFamily M N) : Prop :=
  Tendsto (fun i ↦ graphProp (π i (g i)) (u i) (M.label i) (N.label i)) atTop (𝓝 0)

/-- The sheet shift `u ⊗ R_{g⁻¹}` of a matrix sequence. -/
def sheetFamily (g : ∀ i, G i) (u : ScalarFamily M N) : Family M N :=
  fun i ↦ sheet (g i) (u i)

/-- The uniform graph error `sup_j` of a family `a i j` of types `τ i j`. -/
def graphPropSeq (τ : ∀ i, J i → G i) (a : GraphFamily J M N) (i : ℕ) : ℝ≥0∞ :=
  ⨆ j, graphProp (π i (τ i j)) (a i j) (M.label i) (N.label i)

/-- Manuscript §8: `a i j` has graph type `τ i j`, uniformly in `j` and `i`.  For `J i = G i`
and `τ i = id` this is "`A_g` has graph type `g` uniformly in `g ∈ G i`". -/
def HasGraphType (τ : ∀ i, J i → G i) (a : GraphFamily J M N) : Prop :=
  Tendsto (graphPropSeq τ a) atTop (𝓝 0)

theorem graphProp_le_graphPropSeq (τ : ∀ i, J i → G i) (a : GraphFamily J M N) (i : ℕ)
    (j : J i) : graphProp (π i (τ i j)) (a i j) (M.label i) (N.label i) ≤ graphPropSeq τ a i :=
  le_iSup (fun j ↦ graphProp (π i (τ i j)) (a i j) (M.label i) (N.label i)) j

namespace IsGraphType

variable {g : ∀ i, G i} {u u' : ScalarFamily M N}

theorem add (hu : IsGraphType g u) (hu' : IsGraphType g u') : IsGraphType g (u + u') :=
  tendsto_zero_of_le (by simpa using hu.max hu') fun _ ↦ graphProp_add_le _

theorem smul (c : ℚ) (hu : IsGraphType g u) : IsGraphType g (c • u) :=
  tendsto_zero_of_le hu fun _ ↦ graphProp_smul_le _ c

theorem neg (hu : IsGraphType g u) : IsGraphType g (-u) := by
  simpa [IsGraphType] using hu

theorem sub (hu : IsGraphType g u) (hu' : IsGraphType g u') : IsGraphType g (u - u') := by
  simpa [sub_eq_add_neg] using hu.add hu'.neg

end IsGraphType

theorem isGraphType_one (M : AsymptoticObject π X) :
    IsGraphType (M := M) (N := M) 1 fun _ ↦ 1 :=
  tendsto_zero_of_forall_eq_zero fun i ↦ by simp [prop_one]

/-- Type `1` is ordinary control of the orbit representatives. -/
theorem isGraphType_one_iff {u : ScalarFamily M N} :
    IsGraphType 1 u ↔ Tendsto (fun i ↦ prop (u i) (M.label i) (N.label i)) atTop (𝓝 0) := by
  simp [IsGraphType]

namespace HasGraphType

variable {τ : ∀ i, J i → G i} {a a' : GraphFamily J M N}

/-- Each choice `j i` gives a sequence of graph type `τ i (j i)`. -/
theorem apply (ha : HasGraphType τ a) (j : ∀ i, J i) :
    IsGraphType (fun i ↦ τ i (j i)) (fun i ↦ a i (j i)) :=
  tendsto_zero_of_le ha fun i ↦ graphProp_le_graphPropSeq τ a i (j i)

theorem reindex (ha : HasGraphType τ a) (e : ∀ i, J' i → J i) :
    HasGraphType (fun i j ↦ τ i (e i j)) (fun i j ↦ a i (e i j)) :=
  tendsto_zero_of_le ha fun i ↦ iSup_le fun j ↦ graphProp_le_graphPropSeq τ a i (e i j)

theorem add (ha : HasGraphType τ a) (ha' : HasGraphType τ a') :
    HasGraphType τ (fun i j ↦ a i j + a' i j) :=
  tendsto_zero_of_le (by simpa using ha.max ha') fun i ↦ iSup_le fun j ↦
    (graphProp_add_le _).trans (max_le_max (graphProp_le_graphPropSeq τ a i j)
      (graphProp_le_graphPropSeq τ a' i j))

/-- Coefficients are unrestricted (manuscript §2). -/
theorem smul (c : ∀ i, J i → ℚ) (ha : HasGraphType τ a) :
    HasGraphType τ (fun i j ↦ c i j • a i j) :=
  tendsto_zero_of_le ha fun i ↦ iSup_le fun j ↦
    (graphProp_smul_le _ _).trans (graphProp_le_graphPropSeq τ a i j)

theorem neg (ha : HasGraphType τ a) : HasGraphType τ (fun i j ↦ -a i j) := by
  have : graphPropSeq τ (fun i j ↦ -a i j) = graphPropSeq τ a := funext fun i ↦ by
    simp [graphPropSeq]
  rwa [HasGraphType, this]

theorem sub (ha : HasGraphType τ a) (ha' : HasGraphType τ a') :
    HasGraphType τ (fun i j ↦ a i j - a' i j) := by
  simpa [sub_eq_add_neg] using ha.add ha'.neg

end HasGraphType

/-- The identity has graph type `1`. -/
theorem hasGraphType_one (M : AsymptoticObject π X) :
    HasGraphType (J := J) (M := M) (N := M) (fun _ _ ↦ 1) fun _ _ ↦ 1 :=
  tendsto_zero_of_forall_eq_zero fun i ↦ le_antisymm (iSup_le fun _ ↦ by simp [prop_one]) bot_le

/-- `∑_j a i j ⊗ R_{(τ i j)⁻¹}`. -/
def graphSumFamily [∀ i, Fintype (J i)] (τ : ∀ i, J i → G i) (a : GraphFamily J M N) :
    Family M N :=
  fun i ↦ ∑ j, sheet (τ i j) (a i j)

/-! #### Isometric actions: graph types multiply and invert -/

variable [IsIsometricSMul H X]

theorem propSeq_sheetFamily (g : ∀ i, G i) (u : ScalarFamily M N) (i : ℕ) :
    propSeq M N (sheetFamily g u) i = graphProp (π i (g i)) (u i) (M.label i) (N.label i) :=
  prop_sheet (π i) (g i) (u i) (M.label i) (N.label i)

/-- **Free-sheet translation.** After the shift `s ↦ s g⁻¹` with sheet labels `χ(s) t`, a
matrix sequence is a morphism of `𝒜_G(X)` exactly when it has graph type `g`. -/
theorem isControlled_sheetFamily_iff {g : ∀ i, G i} {u : ScalarFamily M N} :
    IsControlled M N (sheetFamily g u) ↔ IsGraphType g u := by
  have : propSeq M N (sheetFamily g u) =
      fun i ↦ graphProp (π i (g i)) (u i) (M.label i) (N.label i) :=
    funext (propSeq_sheetFamily g u)
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨fun i ↦ isEquivariant_sheet _ _, ?_⟩⟩
  · have h' := h.tendsto_prop
    rwa [this] at h'
  · rw [this]; exact h

namespace IsGraphType

variable {g h : ∀ i, G i} {u : ScalarFamily M N}

/-- **Graph types multiply:** type `g` followed by type `h` has type `h g`. -/
theorem comp {v : ScalarFamily N P} (hu : IsGraphType g u) (hv : IsGraphType h v) :
    IsGraphType (fun i ↦ h i * g i) (fun i ↦ v i * u i) :=
  tendsto_zero_of_le (by simpa using Filter.Tendsto.add hu hv) fun i ↦ by
    rw [map_mul]; exact graphProp_mul_le _ _ _ _ _ _ _

/-- **Duality inverts graph types.** -/
theorem transpose (hu : IsGraphType g u) :
    IsGraphType (M := N) (N := M) (fun i ↦ (g i)⁻¹) (fun i ↦ (u i)ᵀ) := by
  simpa [IsGraphType] using hu

end IsGraphType

namespace HasGraphType

variable {τ : ∀ i, J i → G i} {a : GraphFamily J M N}

/-- **Graph types multiply** under composition, uniformly. -/
theorem comp {τ' : ∀ i, J i → G i} {b : GraphFamily J N P} (ha : HasGraphType τ a)
    (hb : HasGraphType τ' b) :
    HasGraphType (fun i j ↦ τ' i j * τ i j) (fun i j ↦ b i j * a i j) :=
  tendsto_zero_of_le (by simpa using Filter.Tendsto.add ha hb) fun i ↦ iSup_le fun j ↦ by
    rw [map_mul]
    exact (graphProp_mul_le _ _ _ _ _ _ _).trans (add_le_add
      (graphProp_le_graphPropSeq τ a i j) (graphProp_le_graphPropSeq τ' b i j))

/-- All composites `b j' ∘ a j`, of types `τ' j' * τ j`. -/
theorem prodComp {τ' : ∀ i, J' i → G i} {b : GraphFamily J' N P} (ha : HasGraphType τ a)
    (hb : HasGraphType τ' b) :
    HasGraphType (J := fun i ↦ J i × J' i) (fun i p ↦ τ' i p.2 * τ i p.1)
      (fun i p ↦ b i p.2 * a i p.1) :=
  tendsto_zero_of_le (by simpa using Filter.Tendsto.add ha hb) fun i ↦ iSup_le fun p ↦ by
    rw [map_mul]
    exact (graphProp_mul_le _ _ _ _ _ _ _).trans (add_le_add
      (graphProp_le_graphPropSeq τ a i p.1) (graphProp_le_graphPropSeq τ' b i p.2))

/-- **Duality inverts graph types**, uniformly. -/
theorem transpose (ha : HasGraphType τ a) :
    HasGraphType (M := N) (N := M) (fun i j ↦ (τ i j)⁻¹) (fun i j ↦ (a i j)ᵀ) := by
  have : graphPropSeq (M := N) (N := M) (fun i j ↦ (τ i j)⁻¹) (fun i j ↦ (a i j)ᵀ) =
      graphPropSeq τ a := funext fun i ↦ by simp [graphPropSeq]
  rwa [HasGraphType, this]

end HasGraphType

/-! #### Morphisms of `𝒜_G(X)` from shifted graph-type families -/

variable [∀ i, Fintype (G i)]

/-- The morphism of `𝒜_G(X)` (before eventual equality) given by a graph-type sequence. -/
def sheetHom (g : ∀ i, G i) (u : ScalarFamily M N) (hu : IsGraphType g u) : M ⟶ N :=
  ⟨sheetFamily g u, isControlled_sheetFamily_iff.mpr hu⟩

@[simp]
theorem sheetHom_val (g : ∀ i, G i) (u : ScalarFamily M N) (hu : IsGraphType g u) (i : ℕ) :
    (sheetHom g u hu).1 i = sheet (g i) (u i) :=
  rfl

/-- Shifted graph types compose: type `g` then type `h` gives type `h g`. -/
theorem sheetHom_comp {g h : ∀ i, G i} {u : ScalarFamily M N} {v : ScalarFamily N P}
    (hu : IsGraphType g u) (hv : IsGraphType h v) :
    sheetHom g u hu ≫ sheetHom h v hv = sheetHom _ _ (hu.comp hv) :=
  hom_ext fun _ ↦ sheet_mul _ _ _ _

@[simp]
theorem sheetHom_one (M : AsymptoticObject π X) : sheetHom 1 _ (isGraphType_one M) = 𝟙 M :=
  hom_ext fun _ ↦ sheet_one_one

theorem sheetHom_add {g : ∀ i, G i} {u u' : ScalarFamily M N} (hu : IsGraphType g u)
    (hu' : IsGraphType g u') : sheetHom g u hu + sheetHom g u' hu' = sheetHom g _ (hu.add hu') :=
  hom_ext fun _ ↦ (sheet_add _ _ _).symm

theorem sheetHom_smul {g : ∀ i, G i} {u : ScalarFamily M N} (hu : IsGraphType g u) (c : ℚ) :
    c • sheetHom g u hu = sheetHom g _ (hu.smul c) :=
  hom_ext fun _ ↦ (sheet_smul _ _ _).symm

theorem sheetHom_sub {g : ∀ i, G i} {u u' : ScalarFamily M N} (hu : IsGraphType g u)
    (hu' : IsGraphType g u') : sheetHom g u hu - sheetHom g u' hu' = sheetHom g _ (hu.sub hu') :=
  hom_ext fun _ ↦ (sheet_sub _ _ _).symm

/-- Transposition reverses the sheet translation: type `g` becomes type `g⁻¹`. -/
theorem transpose_sheetHom {g : ∀ i, G i} {u : ScalarFamily M N} (hu : IsGraphType g u) :
    AsymptoticObject.transpose (sheetHom g u hu) = sheetHom _ _ hu.transpose :=
  hom_ext fun _ ↦ sheet_transpose _ _

variable [∀ i, Fintype (J i)] [∀ i, Fintype (J' i)] {τ : ∀ i, J i → G i}

omit [∀ i, Fintype (G i)] in
theorem propSeq_graphSumFamily_le (a : GraphFamily J M N) (i : ℕ) :
    propSeq M N (graphSumFamily τ a) i ≤ graphPropSeq τ a i :=
  (prop_sum_le _ _).trans <| iSup₂_le fun j _ ↦ by
    rw [fullLabel_eq_sheetLabel, fullLabel_eq_sheetLabel, prop_sheet]
    exact graphProp_le_graphPropSeq τ a i j

omit [∀ i, Fintype (G i)] in
/-- **Sums of shifted graph-type families are morphisms of `𝒜_G(X)`**: their propagation is
the maximum of the uniform bounds, however many terms there are. -/
theorem HasGraphType.isControlled_sum {a : GraphFamily J M N} (ha : HasGraphType τ a) :
    IsControlled M N (graphSumFamily τ a) :=
  ⟨fun i ↦ Finset.sum_induction _ IsEquivariant (fun _ _ ↦ IsEquivariant.add)
      IsEquivariant.zero fun j _ ↦ isEquivariant_sheet (τ i j) (a i j),
    tendsto_zero_of_le ha (propSeq_graphSumFamily_le a)⟩

/-- The shifted sum `∑_j a i j ⊗ R_{(τ i j)⁻¹}` as a morphism. -/
def graphSum (τ : ∀ i, J i → G i) (a : GraphFamily J M N) (ha : HasGraphType τ a) : M ⟶ N :=
  ⟨graphSumFamily τ a, ha.isControlled_sum⟩

@[simp]
theorem graphSum_val (a : GraphFamily J M N) (ha : HasGraphType τ a) (i : ℕ) :
    (graphSum τ a ha).1 i = ∑ j, sheet (τ i j) (a i j) :=
  rfl

/-- Manuscript (5.3): the `(s', s)` sheet block of `∑_g A_g ⊗ R_{g⁻¹}` is `A_{s'⁻¹ s}`. -/
theorem graphSum_id_apply (a : GraphFamily G M N) (ha : HasGraphType (fun _ ↦ id) a) (i : ℕ)
    (p : Fin (N.rank i) × G i) (q : Fin (M.rank i) × G i) :
    (graphSum _ a ha).1 i p q = a i (p.2⁻¹ * q.2) p.1 q.1 := by
  rw [graphSum_val, Matrix.sum_apply, Finset.sum_eq_single (p.2⁻¹ * q.2)]
  · simp
  · intro g _ hg
    rw [sheet_apply, ite_eq_right]
    intro h
    exact hg (by simp [h])
  · simp

theorem graphSum_comp {τ' : ∀ i, J' i → G i} {a : GraphFamily J M N} {b : GraphFamily J' N P}
    (ha : HasGraphType τ a) (hb : HasGraphType τ' b) :
    graphSum τ a ha ≫ graphSum τ' b hb = graphSum _ _ (ha.prodComp hb) := by
  refine hom_ext fun i ↦ ?_
  simp only [comp_val, graphSum_val, Matrix.sum_mul, Matrix.mul_sum, sheet_mul,
    Fintype.sum_prod_type]

theorem graphSum_add {a a' : GraphFamily J M N} (ha : HasGraphType τ a)
    (ha' : HasGraphType τ a') : graphSum τ a ha + graphSum τ a' ha' = graphSum τ _ (ha.add ha') :=
  hom_ext fun i ↦ by simp [sheet_add, Finset.sum_add_distrib]

theorem graphSum_smul {a : GraphFamily J M N} (ha : HasGraphType τ a) (c : ℚ) :
    c • graphSum τ a ha = graphSum τ _ (ha.smul fun _ _ ↦ c) :=
  hom_ext fun i ↦ by simp [sheet_smul, Finset.smul_sum]

theorem graphSum_sub {a a' : GraphFamily J M N} (ha : HasGraphType τ a)
    (ha' : HasGraphType τ a') : graphSum τ a ha - graphSum τ a' ha' = graphSum τ _ (ha.sub ha') :=
  hom_ext fun i ↦ by simp [sheet_sub, Finset.sum_sub_distrib]

theorem transpose_graphSum {a : GraphFamily J M N} (ha : HasGraphType τ a) :
    AsymptoticObject.transpose (graphSum τ a ha) = graphSum _ _ ha.transpose :=
  hom_ext fun i ↦ by simp [Matrix.transpose_sum, sheet_transpose]

/-- The averaged projector `E_i = q_i⁻¹ ∑_{g ∈ G_i} A_{g,i} ⊗ R_{g⁻¹}` of (10.2). -/
def graphAverage (A : GraphFamily G M M) (hA : HasGraphType (fun _ ↦ id) A) : M ⟶ M :=
  graphSum _ _ (hA.smul fun i _ ↦ (Fintype.card (G i) : ℚ)⁻¹)

end AsymptoticObject

end Families

/-! ### The free-sheet functor `𝒜_1(X) → 𝒜_G(X)` (l.849) -/

section FreeSheet

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  {π : ∀ i, G i →* H} {X : Type u} [MulAction H X] [PseudoEMetricSpace X] [IsIsometricSMul H X]

variable (H) in
/-- The trivial groups `G i = 1` of the scalar category `𝒜_1(X)`. -/
abbrev scalarHom : ∀ _ : ℕ, Unit →* H := fun _ ↦ 1

theorem infEDist_smul_of_invariant {Z : Set X} (hZ : ∀ h : H, h • Z = Z) (h : H) (x : X) :
    infEDist (h • x) Z = infEDist x Z := by
  conv_lhs => rw [← hZ h]
  exact infEDist_smul h x Z

namespace AsymptoticObject

omit [∀ i, Fintype (G i)] in
/-- For an invariant `Z`, support is measured on the orbit representatives. -/
theorem supportDist_eq_iSup_label {Z : Set X} (hZ : ∀ h : H, h • Z = Z)
    (M : AsymptoticObject π X) (i : ℕ) :
    M.supportDist Z i = ⨆ k, infEDist (M.label i k) Z := by
  refine le_antisymm (iSup_le fun b ↦ ?_) (iSup_le fun k ↦ ?_)
  · rw [fullLabel, infEDist_smul_of_invariant hZ]
    exact le_iSup (fun k ↦ infEDist (M.label i k) Z) b.1
  · simpa using infEDist_le_supportDist (S := Z) (M := M) i (k, 1)

variable (π) in
/-- Free sheets over a scalar object: the same orbit representatives and labels, (10.1). -/
@[implicit_reducible] def freeSheetObj (M : AsymptoticObject (scalarHom H) X) : AsymptoticObject π X :=
  ⟨M.rank, M.label⟩

variable {M N P : AsymptoticObject (scalarHom H) X}

omit [∀ i, Fintype (G i)] in
theorem isSupported_freeSheetObj_iff {Z : Set X} (hZ : ∀ h : H, h • Z = Z) :
    (freeSheetObj π M).IsSupported Z ↔ M.IsSupported Z := by
  rw [IsSupported, IsSupported, funext (supportDist_eq_iSup_label hZ (freeSheetObj π M)),
    funext (supportDist_eq_iSup_label hZ M)]
  rfl

variable (π) in
/-- The scalar matrices of a scalar family. -/
def scalarMatrix (f : Family M N) : ScalarFamily (freeSheetObj π M) (freeSheetObj π N) :=
  fun i ↦ Matrix.of fun k' k ↦ f i (k', ()) (k, ())

omit [IsIsometricSMul H X] [∀ i, Fintype (G i)] in
theorem prop_scalarMatrix (f : Family M N) (i : ℕ) :
    prop (scalarMatrix π f i) (M.label i) (N.label i) = propSeq M N f i := by
  refine le_antisymm (prop_le_iff.mpr fun k' k h ↦ ?_) (prop_le_iff.mpr fun b a h ↦ ?_)
  · simpa [fullLabel, propSeq] using
      edist_le_prop (source := M.fullLabel i) (target := N.fullLabel i) h
  · simpa [fullLabel] using edist_le_prop (source := M.label i) (target := N.label i)
      (u := scalarMatrix π f i) (b := b.1) (a := a.1) h

omit [IsIsometricSMul H X] [∀ i, Fintype (G i)] in
theorem isGraphType_scalarMatrix (f : M ⟶ N) : IsGraphType 1 (scalarMatrix π f.1) :=
  isGraphType_one_iff.mpr <| (tendsto_propSeq f).congr fun i ↦ (prop_scalarMatrix f.1 i).symm

omit [IsIsometricSMul H X] [∀ i, Fintype (G i)] in
theorem scalarMatrix_id (i : ℕ) : scalarMatrix π (𝟙 M : M ⟶ M).1 i = 1 := by
  ext k' k
  by_cases h : k' = k
  · simp [scalarMatrix, one_apply, h]
  · simp [scalarMatrix, one_apply, h] <;> exact fun e ↦ h (congrArg Prod.fst e)

omit [IsIsometricSMul H X] [∀ i, Fintype (G i)] in
theorem scalarMatrix_comp (f : M ⟶ N) (g : N ⟶ P) (i : ℕ) :
    scalarMatrix π (f ≫ g).1 i = scalarMatrix π g.1 i * scalarMatrix π f.1 i := by
  ext k'' k
  simp [scalarMatrix, mul_apply, Fintype.sum_prod_type]
  rfl

variable (π) in
/-- **The free-sheet functor** `𝒜_1(X) → 𝒜_G(X)`: a local scalar matrix is copied on every
sheet (l.849); it is the type-`1` sheet shift. -/
@[implicit_reducible] def freeSheet : AsymptoticObject (scalarHom H) X ⥤ AsymptoticObject π X where
  obj := freeSheetObj π
  map f := sheetHom 1 _ (isGraphType_scalarMatrix f)
  map_id M := hom_ext fun i ↦ by
    simp only [sheetHom_val, id_val, Pi.one_apply, scalarMatrix_id, sheet_one_one]
  map_comp f g := hom_ext fun i ↦ by
    simp only [sheetHom_val, comp_val, Pi.one_apply, scalarMatrix_comp, sheet_mul, mul_one]

theorem freeSheet_map (f : M ⟶ N) :
    (freeSheet π).map f = sheetHom 1 _ (isGraphType_scalarMatrix f) :=
  rfl

/-- The free-sheet functor preserves duality. -/
theorem freeSheet_map_transpose (f : M ⟶ N) :
    (freeSheet π).map (AsymptoticObject.transpose f) =
      AsymptoticObject.transpose ((freeSheet π).map f) :=
  hom_ext fun i ↦ by
    change sheet 1 (scalarMatrix π (AsymptoticObject.transpose f).1 i) =
      (sheet 1 (scalarMatrix π f.1 i))ᵀ
    rw [sheet_transpose, inv_one]
    rfl

end AsymptoticObject

open AsymptoticObject

namespace AsymptoticCategory

variable (π) in
/-- The free-sheet functor on germs, `𝒜_1(X) → 𝒜_G(X)`. -/
def freeSheet : AsymptoticCategory (scalarHom H) X ⥤ AsymptoticCategory π X :=
  CategoryTheory.Quotient.lift _ (AsymptoticObject.freeSheet π ⋙ functor) fun _ _ f g h ↦
    (functor_map_eq_iff _ _).mpr <| h.mono fun i hi ↦ by
      simp only [AsymptoticObject.freeSheet_map, sheetHom_val]
      congr 1
      ext k' k
      simp [scalarMatrix, hi]

theorem freeSheet_map_functor_map {M N : AsymptoticObject (scalarHom H) X} (f : M ⟶ N) :
    (freeSheet π).map (functor.map f) = functor.map ((AsymptoticObject.freeSheet π).map f) :=
  rfl

instance freeSheet_additive : (freeSheet (X := X) π).Additive where
  map_add {A B φ ψ} := by
    obtain ⟨f, rfl⟩ := exists_rep φ
    obtain ⟨g, rfl⟩ := exists_rep ψ
    rw [← Functor.map_add, freeSheet_map_functor_map, freeSheet_map_functor_map,
      freeSheet_map_functor_map]
    erw [← Functor.map_add]
    congr 1
    refine hom_ext fun i ↦ ?_
    change sheet (1 : G i) (scalarMatrix π (f + g).1 i) =
      sheet (1 : G i) (scalarMatrix π f.1 i) + sheet (1 : G i) (scalarMatrix π g.1 i)
    rw [← sheet_add]
    congr 1

theorem freeSheet_map_transpose {A B : AsymptoticCategory (scalarHom H) X} (φ : A ⟶ B) :
    (freeSheet π).map (transpose φ) = transpose ((freeSheet π).map φ) := by
  obtain ⟨f, rfl⟩ := exists_rep φ
  rw [transpose_map, freeSheet_map_functor_map, freeSheet_map_functor_map,
    AsymptoticObject.freeSheet_map_transpose]
  erw [transpose_map]

variable {Z : Set X}

/-- The free-sheet functor preserves the exterior ideal `I_Z` of an invariant `Z`. -/
theorem InIdeal.freeSheet_map (hZ : ∀ h : H, h • Z = Z) {A B : AsymptoticCategory (scalarHom H) X}
    {φ : A ⟶ B} (h : InIdeal Z φ) : InIdeal Z ((freeSheet π).map φ) := by
  obtain ⟨W, hW, u, v, rfl⟩ := h
  exact ⟨(freeSheet π).obj W, (isSupported_freeSheetObj_iff hZ).mpr hW, (freeSheet π).map u,
    (freeSheet π).map v, by simp⟩

end AsymptoticCategory

variable (π) in
/-- The free-sheet functor `ℬ_{1,Z}(X) → ℬ_{G,Z}(X)` for an invariant exterior `Z` (l.849). -/
def ExteriorCategory.freeSheet {Z : Set X} (hZ : ∀ h : H, h • Z = Z) :
    ExteriorCategory (scalarHom H) Z ⥤ ExteriorCategory π Z :=
  CategoryTheory.Quotient.lift _ (AsymptoticCategory.freeSheet π ⋙ ExteriorCategory.functor)
    fun _ _ φ ψ h ↦ (ExteriorCategory.functor_map_eq_iff _ _).mpr <| by
      rw [← Functor.map_sub]
      exact h.freeSheet_map hZ

end FreeSheet

/-! ### Exterior witnesses after the sheet shift -/

section Exterior

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  {π : ∀ i, G i →* H} {X : Type u} [MulAction H X] [PseudoEMetricSpace X] [IsIsometricSMul H X]
  {Z : Set X} {M N : AsymptoticObject π X} {J : ℕ → Type*} [∀ i, Fintype (J i)]
  {τ : ∀ i, J i → G i}

open AsymptoticObject AsymptoticCategory

/-- **Exterior witnesses after the sheet shift.** If the nonzero entries of a family of uniform
graph type have endpoints approaching an invariant exterior `Z` uniformly, its shifted sum lies
in `I_Z`, i.e. vanishes in `ℬ_{G,Z}(X)`; the number of terms is irrelevant. -/
theorem inIdeal_graphSum (hZ : ∀ h : H, h • Z = Z) {a : GraphFamily J M N}
    (ha : HasGraphType τ a) {r : ℕ → ℝ≥0∞} (hr : Tendsto r atTop (𝓝 0))
    (hend : ∀ i j c b, a i j c b ≠ 0 →
      infEDist (N.label i c) Z ≤ r i ∧ infEDist (M.label i b) Z ≤ r i) :
    InIdeal Z (functor.map (graphSum τ a ha)) := by
  rw [inIdeal_map_iff]
  refine tendsto_zero_of_le hr fun i ↦ endpointDist_le_iff.mpr fun p q hpq ↦ ?_
  rw [graphSum_val, Matrix.sum_apply] at hpq
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpq
  simpa [fullLabel, infEDist_smul_of_invariant hZ] using
    hend i j p.1 q.1 (sheet_apply_ne_zero hj).2

/-- Equations between shifted graph-type families hold in `ℬ_{G,Z}(X)` as soon as the
residual has exterior witnesses. -/
theorem exterior_graphSum_eq (hZ : ∀ h : H, h • Z = Z) {a a' : GraphFamily J M N}
    (ha : HasGraphType τ a) (ha' : HasGraphType τ a') {r : ℕ → ℝ≥0∞}
    (hr : Tendsto r atTop (𝓝 0))
    (hend : ∀ i j c b, (a i j - a' i j) c b ≠ 0 →
      infEDist (N.label i c) Z ≤ r i ∧ infEDist (M.label i b) Z ≤ r i) :
    (ExteriorCategory.functor (Z := Z)).map (functor.map (graphSum τ a ha)) =
      ExteriorCategory.functor.map (functor.map (graphSum τ a' ha')) := by
  rw [ExteriorCategory.functor_map_eq_iff, ← Functor.map_sub, graphSum_sub]
  exact inIdeal_graphSum hZ _ hr hend

/-- The single-sequence case of `inIdeal_graphSum`. -/
theorem inIdeal_sheetHom (hZ : ∀ h : H, h • Z = Z) {g : ∀ i, G i} {u : ScalarFamily M N}
    (hu : IsGraphType g u) {r : ℕ → ℝ≥0∞} (hr : Tendsto r atTop (𝓝 0))
    (hend : ∀ i c b, u i c b ≠ 0 →
      infEDist (N.label i c) Z ≤ r i ∧ infEDist (M.label i b) Z ≤ r i) :
    InIdeal Z (functor.map (sheetHom g u hu)) := by
  rw [inIdeal_map_iff]
  refine tendsto_zero_of_le hr fun i ↦ endpointDist_le_iff.mpr fun p q hpq ↦ ?_
  simpa [fullLabel, infEDist_smul_of_invariant hZ] using
    hend i p.1 q.1 (sheet_apply_ne_zero hpq).2

end Exterior

/-! ### Lemma 9.1 on the sheets -/

section Band

variable {Y : Type*} [PseudoMetricSpace Y] {A B C : Type*} [Fintype B]

/-- The based projection onto the far basis elements; for `far` the subcomplex `F_i` this is
`P = 1 - σπ` of (9.1). -/
def farProj (far : B → Prop) : Matrix B B ℚ :=
  diagonal fun b ↦ if far b then 1 else 0

omit [Fintype B] in
/-- The reachable band (9.2): far basis elements with `d(f, y) ≤ t + κ + r`. -/
def reachBand (far : B → Prop) (middle : B → Y) (y : Y) (t κ r : ℝ) : Set B :=
  {b | far b ∧ dist (middle b) y ≤ t + κ + r}

omit [Fintype B] in
/-- The band bounds (9.2), for a far predicate with `far → d(f, y) > t`. -/
theorem reachBand_bounds {far : B → Prop} {middle : B → Y} {y : Y} {t κ r : ℝ}
    (hfar : ∀ b, far b → t < dist (middle b) y) {b : B} (hb : b ∈ reachBand far middle y t κ r) :
    t < dist (middle b) y ∧ dist (middle b) y ≤ t + κ + r :=
  ⟨hfar b hb.1, hb.2⟩

/-- **Lemma 9.1**, exact factorization: a word `v P u` from retained sources factors through
the far basis elements reached by the prefix `u`.  Any far predicate is allowed. -/
theorem farProj_factors_through_reachBand (u : Matrix B A ℚ) (v : Matrix C B ℚ)
    (far : B → Prop) (source : A → Y) (middle : B → Y) (y : Y) (t κ r : ℝ)
    (hu : HasPropagationLE u source middle r) (hsource : ∀ a, dist (source a) y ≤ t + κ) :
    v * (farProj far * u) =
      v.submatrix id ((↑) : reachBand far middle y t κ r → B) * u.submatrix (↑) id := by
  have hsupp : MatrixSupportedBy (farProj far * u)
      (fun b _ ↦ b ∈ reachBand far middle y t κ r) := by
    intro b a hba
    have hfar : far b := by
      by_contra hn
      exact hba (by simp [farProj, diagonal_mul, hn])
    have hu0 : u b a ≠ 0 := fun h0 ↦ hba (by simp [farProj, diagonal_mul, h0])
    refine ⟨hfar, ?_⟩
    calc dist (middle b) y ≤ dist (middle b) (source a) + dist (source a) y := dist_triangle _ _ _
      _ ≤ r + (t + κ) := add_le_add (hu b a hu0) (hsource a)
      _ = t + κ + r := by ring
  rw [matrix_mul_factors_through_supported_rows _ v _ hsupp]
  congr 1
  ext b a
  simp [farProj, diagonal_mul, b.2.1]

/-- **Lemma 9.1 for graph words**: after the sheet shift the factorization persists, the total
translation splitting into the prefix and suffix translations. -/
theorem sheet_farProj_factors_through_reachBand {Γ : Type*} [Group Γ] [Fintype Γ] (g h : Γ)
    (u : Matrix B A ℚ) (v : Matrix C B ℚ) (far : B → Prop) (source : A → Y) (middle : B → Y)
    (y : Y) (t κ r : ℝ) (hu : HasPropagationLE u source middle r)
    (hsource : ∀ a, dist (source a) y ≤ t + κ) :
    sheet (g * h) (v * (farProj far * u)) =
      sheet g (v.submatrix id ((↑) : reachBand far middle y t κ r → B)) *
        sheet h (u.submatrix (↑) id) := by
  rw [farProj_factors_through_reachBand u v far source middle y t κ r hu hsource, sheet_mul]

variable {H X : Type*} [Group H] [MulAction H X] [PseudoEMetricSpace X] [IsIsometricSMul H X]

/-- The estimates of Lemma 9.1 for one graph word `v P u`: if the band has labels `ℓ` in an
invariant exterior `Z`, `u` has graph type `h` into the band and `v` graph type `g` out of it,
then `v P u` has graph type `g h` and its entries have endpoints near `Z`. -/
theorem farProj_word_bounds {Z : Set X} (hZ : ∀ h : H, h • Z = Z) (g h : H)
    (u : Matrix B A ℚ) (v : Matrix C B ℚ) (far : B → Prop) (fsource : A → Y) (middle : B → Y)
    (y : Y) (t κ r : ℝ) (hu : HasPropagationLE u fsource middle r)
    (hsource : ∀ a, dist (fsource a) y ≤ t + κ) (ℓ : B → X) (source : A → X) (target : C → X)
    (e : ℝ≥0∞) (hband : ∀ b ∈ reachBand far middle y t κ r, ℓ b ∈ Z)
    (hug : ∀ b ∈ reachBand far middle y t κ r, ∀ a, u b a ≠ 0 → edist (ℓ b) (h • source a) ≤ e)
    (hvg : ∀ b ∈ reachBand far middle y t κ r, ∀ c, v c b ≠ 0 →
      edist (target c) (g • ℓ b) ≤ e) :
    graphProp (g * h) (v * (farProj far * u)) source target ≤ e + e ∧
      ∀ c a, (v * (farProj far * u)) c a ≠ 0 →
        infEDist (target c) Z ≤ e ∧ infEDist (source a) Z ≤ e := by
  rw [farProj_factors_through_reachBand u v far fsource middle y t κ r hu hsource]
  set R := reachBand far middle y t κ r
  have hu' : graphProp h (u.submatrix ((↑) : R → B) id) source (ℓ ∘ (↑)) ≤ e :=
    graphProp_le_iff.mpr fun b a hba ↦ hug b b.2 a hba
  have hv' : graphProp g (v.submatrix id ((↑) : R → B)) (ℓ ∘ (↑)) target ≤ e :=
    graphProp_le_iff.mpr fun c b hcb ↦ hvg b b.2 c hcb
  refine ⟨(graphProp_mul_le _ _ _ _ _ _ _).trans (add_le_add hu' hv'), fun c a hca ↦ ?_⟩
  obtain ⟨b, hvb, hub⟩ := matrix_mul_entry_nonzero_witness _ _ c a hca
  have hb : infEDist (ℓ b) Z = 0 := infEDist_zero_of_mem (hband b b.2)
  constructor
  · calc infEDist (target c) Z ≤ infEDist (g • ℓ b) Z + edist (target c) (g • ℓ b) :=
          infEDist_le_infEDist_add_edist
      _ ≤ e := by rw [infEDist_smul_of_invariant hZ, hb, zero_add]; exact hvg b b.2 c hvb
  · calc infEDist (source a) Z = infEDist (h • source a) Z :=
          (infEDist_smul_of_invariant hZ h _).symm
      _ ≤ infEDist (ℓ b) Z + edist (h • source a) (ℓ b) := infEDist_le_infEDist_add_edist
      _ ≤ e := by rw [hb, zero_add, edist_comm]; exact hug b b.2 a hub

end Band

section BandCategory

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  {π : ∀ i, G i →* H} {X : Type u} [MulAction H X] [PseudoEMetricSpace X] [IsIsometricSMul H X]
  {Z : Set X} {M N : AsymptoticObject π X} {J : ℕ → Type*} [∀ i, Fintype (J i)]
  {Y : Type*} [PseudoMetricSpace Y]

open AsymptoticObject AsymptoticCategory

/-- **Lemma 9.1 lifted to the sheets.**  Let `u i j` map retained modules (with `f`-labels
within `t + κ i` of `y`) into a middle basis `B i`, with `f`-propagation `r i`, and graph type
`τ i j` into the reachable band; let `v i j` have graph type `τ' i j` out of the band.  If the
band labels `ℓ` lie in the invariant exterior `Z`, then the words `v P u` have uniform graph
type `τ' τ`, and after the sheet shift their sum is a morphism of `𝒜_G(X)` lying in `I_Z`. -/
theorem exists_graphSum_farProj_inIdeal (hZ : ∀ h : H, h • Z = Z) {B : ℕ → Type*}
    [∀ i, Fintype (B i)] (far : ∀ i, B i → Prop) (mid : ∀ i, B i → Y) (ℓ : ∀ i, B i → X)
    (fsrc : ∀ i, Fin (M.rank i) → Y) (y : Y) (t : ℝ) (κ r : ℕ → ℝ) {e : ℕ → ℝ≥0∞}
    (he : Tendsto e atTop (𝓝 0)) {τ τ' : ∀ i, J i → G i}
    (u : ∀ i, J i → Matrix (B i) (Fin (M.rank i)) ℚ) (v : ∀ i, J i → Matrix (Fin (N.rank i)) (B i) ℚ)
    (hsrc : ∀ i k, dist (fsrc i k) y ≤ t + κ i)
    (hu : ∀ i j, HasPropagationLE (u i j) (fsrc i) (mid i) (r i))
    (hband : ∀ i, ∀ b ∈ reachBand (far i) (mid i) y t (κ i) (r i), ℓ i b ∈ Z)
    (hug : ∀ i j, ∀ b ∈ reachBand (far i) (mid i) y t (κ i) (r i), ∀ k, u i j b k ≠ 0 →
      edist (ℓ i b) (π i (τ i j) • M.label i k) ≤ e i)
    (hvg : ∀ i j, ∀ b ∈ reachBand (far i) (mid i) y t (κ i) (r i), ∀ c, v i j c b ≠ 0 →
      edist (N.label i c) (π i (τ' i j) • ℓ i b) ≤ e i) :
    ∃ hw : HasGraphType (fun i j ↦ τ' i j * τ i j) (fun i j ↦ v i j * (farProj (far i) * u i j)),
      InIdeal Z (functor.map (graphSum _ _ hw)) := by
  have key := fun i j ↦ farProj_word_bounds hZ (π i (τ' i j)) (π i (τ i j)) (u i j) (v i j)
    (far i) (fsrc i) (mid i) y t (κ i) (r i) (hu i j) (hsrc i) (ℓ i) (M.label i) (N.label i)
    (e i) (hband i) (hug i j) (hvg i j)
  refine ⟨tendsto_zero_of_le (by simpa using he.add he) fun i ↦ iSup_le fun j ↦ ?_,
    inIdeal_graphSum hZ _ he fun i j c k h ↦ (key i j).2 c k h⟩
  rw [map_mul]
  exact (key i j).1

namespace AsymptoticObject

variable (π) in
/-- The based module whose orbit representatives are a finite type `Q i`, labelled by `ℓ i`. -/
def ofLabels (Q : ℕ → Type*) [∀ i, Fintype (Q i)] (ℓ : ∀ i, Q i → X) : AsymptoticObject π X :=
  ⟨fun i ↦ Fintype.card (Q i), fun i k ↦ ℓ i ((Fintype.equivFin (Q i)).symm k)⟩

/-- The inclusion of the summand `j` of `⨁_{j ∈ J i} R i`, on orbit representatives. -/
def blockIncl {R : ℕ → Type*} [∀ i, Fintype (R i)] (i : ℕ) (j : J i) :
    Matrix (Fin (Fintype.card (J i × R i))) (R i) ℚ :=
  Matrix.of fun k b ↦ if (Fintype.equivFin (J i × R i)).symm k = (j, b) then 1 else 0

theorem blockIncl_ne_zero {R : ℕ → Type*} [∀ i, Fintype (R i)] {i : ℕ}
    {j : J i} {k : Fin (Fintype.card (J i × R i))} {b : R i} (h : blockIncl i j k b ≠ 0) :
    (Fintype.equivFin (J i × R i)).symm k = (j, b) := by
  by_contra hne
  exact h (by simp [blockIncl, hne])

theorem blockIncl_transpose_mul {R : ℕ → Type*} [∀ i, Fintype (R i)] [∀ i, DecidableEq (R i)]
    (i : ℕ) (j j' : J i) :
    (blockIncl (R := R) i j')ᵀ * blockIncl (R := R) i j = if j' = j then 1 else 0 := by
  ext b' b
  simp only [mul_apply, transpose_apply, blockIncl, of_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single ((Fintype.equivFin (J i × R i)) (j, b))]
  · by_cases hj : j' = j
    · subst hj
      by_cases hb : b' = b
      · subst hb; simp
      · have : b ≠ b' := Ne.symm hb
        simp [hb, this]
    · have : j ≠ j' := Ne.symm hj
      simp [hj, this]
  · intro x _ hx
    rw [ite_eq_right]
    rintro h
    exact hx (by rw [← h, Equiv.apply_symm_apply])
  · simp

end AsymptoticObject

/-- **Lemma 9.1 lifted to the sheets, with explicit witnesses.**  Under the hypotheses of
`exists_graphSum_farProj_inIdeal`, the shifted sum of the words `v P u` factors exactly through
the direct sum `W` of the reached bands (a based module labelled in the band (9.2), supported in
`Z`), by a prefix and a suffix morphism of `𝒜_G(X)` whose propagation is at most `e i`. -/
theorem exists_band_factorization (hZ : ∀ h : H, h • Z = Z) {B : ℕ → Type*}
    [∀ i, Fintype (B i)] (far : ∀ i, B i → Prop) (mid : ∀ i, B i → Y) (ℓ : ∀ i, B i → X)
    (fsrc : ∀ i, Fin (M.rank i) → Y) (y : Y) (t : ℝ) (κ r : ℕ → ℝ) {e : ℕ → ℝ≥0∞}
    (he : Tendsto e atTop (𝓝 0)) {τ τ' : ∀ i, J i → G i}
    (u : ∀ i, J i → Matrix (B i) (Fin (M.rank i)) ℚ) (v : ∀ i, J i → Matrix (Fin (N.rank i)) (B i) ℚ)
    (hsrc : ∀ i k, dist (fsrc i k) y ≤ t + κ i)
    (hu : ∀ i j, HasPropagationLE (u i j) (fsrc i) (mid i) (r i))
    (hband : ∀ i, ∀ b ∈ reachBand (far i) (mid i) y t (κ i) (r i), ℓ i b ∈ Z)
    (hug : ∀ i j, ∀ b ∈ reachBand (far i) (mid i) y t (κ i) (r i), ∀ k, u i j b k ≠ 0 →
      edist (ℓ i b) (π i (τ i j) • M.label i k) ≤ e i)
    (hvg : ∀ i j, ∀ b ∈ reachBand (far i) (mid i) y t (κ i) (r i), ∀ c, v i j c b ≠ 0 →
      edist (N.label i c) (π i (τ' i j) • ℓ i b) ≤ e i) :
    ∃ (W : AsymptoticObject π X) (p : M ⟶ W) (q : W ⟶ N)
      (hw : HasGraphType (fun i j ↦ τ' i j * τ i j) (fun i j ↦ v i j * (farProj (far i) * u i j))),
      p ≫ q = graphSum _ _ hw ∧ W.IsSupported Z ∧
      (∀ i k, ∃ b ∈ reachBand (far i) (mid i) y t (κ i) (r i), W.label i k = ℓ i b) ∧
      (∀ i, propSeq M W p.1 i ≤ e i) ∧ ∀ i, propSeq W N q.1 i ≤ e i := by
  let R : ℕ → Type _ := fun i ↦ ↥(reachBand (far i) (mid i) y t (κ i) (r i))
  letI : ∀ i, Fintype (R i) := fun i ↦ Fintype.ofFinite _
  let ι : ∀ i, R i → B i := fun _ b ↦ b.1
  let W : AsymptoticObject π X := ofLabels π (fun i ↦ J i × R i) fun i q ↦ ℓ i (ι i q.2)
  have hWlabel : ∀ i k, W.label i k = ℓ i (ι i ((Fintype.equivFin (J i × R i)).symm k).2) :=
    fun _ _ ↦ rfl
  let a : GraphFamily J M W := fun i j ↦ blockIncl (R := R) i j * (u i j).submatrix (ι i) id
  let b : GraphFamily J W N := fun i j ↦ (v i j).submatrix id (ι i) * (blockIncl (R := R) i j)ᵀ
  have ha : ∀ i, graphPropSeq τ a i ≤ e i := fun i ↦ iSup_le fun j ↦
    graphProp_le_iff.mpr fun k m hkm ↦ by
      obtain ⟨c, hc, hcm⟩ := matrix_mul_entry_nonzero_witness _ _ k m hkm
      rw [hWlabel, blockIncl_ne_zero hc]
      exact hug i j c c.2 m hcm
  have hb : ∀ i, graphPropSeq τ' b i ≤ e i := fun i ↦ iSup_le fun j ↦
    graphProp_le_iff.mpr fun n k hnk ↦ by
      obtain ⟨c, hnc, hck⟩ := matrix_mul_entry_nonzero_witness _ _ n k hnk
      rw [hWlabel, blockIncl_ne_zero hck]
      exact hvg i j c c.2 n hnc
  have ha' : HasGraphType τ a := tendsto_zero_of_le he ha
  have hb' : HasGraphType τ' b := tendsto_zero_of_le he hb
  obtain ⟨hw, -⟩ := exists_graphSum_farProj_inIdeal hZ far mid ℓ fsrc y t κ r he u v hsrc hu
    hband hug hvg
  refine ⟨W, graphSum τ a ha', graphSum τ' b hb', hw, ?_, ?_, fun i k ↦ ⟨_, Subtype.prop _, rfl⟩,
    fun i ↦ (propSeq_graphSumFamily_le a i).trans (ha i),
    fun i ↦ (propSeq_graphSumFamily_le b i).trans (hb i)⟩
  · rw [graphSum_comp]
    refine hom_ext fun i ↦ ?_
    simp only [graphSum_val, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Finset.sum_eq_single j]
    · simp only [b, a]
      erw [Matrix.mul_assoc, ← Matrix.mul_assoc (blockIncl i j)ᵀ]
      rw [blockIncl_transpose_mul, ite_eq_left rfl,
        Matrix.one_mul, farProj_factors_through_reachBand (u i j) (v i j) (far i) (fsrc i)
          (mid i) y t (κ i) (r i) (hu i j) (hsrc i)]
      congr 1
      convert rfl
    · intro j' _ hj'
      simp only [b, a]
      erw [Matrix.mul_assoc, ← Matrix.mul_assoc (blockIncl i j')ᵀ]
      rw [blockIncl_transpose_mul, ite_eq_right hj',
        Matrix.zero_mul, Matrix.mul_zero, sheet_zero]
    · simp
  · refine tendsto_zero_of_forall_eq_zero fun i ↦ ?_
    rw [supportDist_eq_iSup_label hZ]
    exact le_antisymm (iSup_le fun k ↦ (infEDist_zero_of_mem (hband i _ (Subtype.prop _))).le)
      bot_le

end BandCategory

end HSFormal
