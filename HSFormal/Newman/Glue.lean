import HSFormal.Newman.RelHom
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# N2. The gluing lemma (GL) and chart transport (CT) (Newman blueprint, module N2)

* `VanishAbove R X L d`: `H_i(X | L) = 0` for all `i > d`.
* `PointInj R X L d`: a class of `H_d(X | L)` whose restrictions to all points of `L` vanish is
  zero.
* **GL** `eq_zero_of_res_eq_zero`: for closed `L₁, L₂` and `α ∈ H_i(X | L₁ ∪ L₂)` restricting to
  `0` on `L₁` and on `L₂`, `H_{i+1}(X | L₁ ∩ L₂) = 0` forces `α = 0`. Proof: triple
  `(X, X∖L₁, X∖(L₁∪L₂))`, excision `H_i(X∖L₁ | L₁∪L₂) ≅ H_i(X∖(L₁∩L₂) | L₂)`, and the triple
  `(X, X∖(L₁∩L₂), X∖L₂)`. No Hausdorff hypothesis is needed (only closedness of `L₁, L₂`).
* Corollaries `VanishAbove.union`, `PointInj.union`, and the trivial cases `vanishAbove_empty`,
  `pointInj_empty`, `PointInj.of_isZero`.
* **CT** `vanishAbove_iff_of_isOpenEmbedding`, `pointInj_iff_of_isOpenEmbedding` (transport along
  an open embedding `f` with `L = f⁻¹ L'`, `L'` closed in `range f`; for `PointInj` the target is
  `T1`), and the chart forms `vanishAbove_chart_iff`, `pointInj_chart_iff`: for a chart
  `e : OpenPartialHomeomorph X F` and compact `C ⊆ e.target`,
  `V/P(F, C) ↔ V/P(X, e.symm '' C)`.

## Deviations from the blueprint

The blueprint's explicit isomorphism `relHChartIso` and its naturality lemma are replaced by the
transport statements above, which is all that the downstream uses (`V ∧ P` for chart-convex
pieces); an explicit chart isomorphism is the composite of `pushIncl` (excision) isomorphisms and
`relHIsoOfHomeomorph`, should a later module need it.
-/

open CategoryTheory Limits Topology

namespace HSFormal.Newman

variable (R : Type) [CommRing R]

/-- `H_i(X | L) = 0` for all `i > d`. -/
def VanishAbove (X : TopCat.{0}) (L : Set X) (d : ℕ) : Prop :=
  ∀ i, d < i → IsZero (relH R X L i)

/-- A class in `H_d(X | L)` whose restrictions to all points of `L` vanish is `0`. -/
def PointInj (X : TopCat.{0}) (L : Set X) (d : ℕ) : Prop :=
  ∀ α : relH R X L d, (∀ x (hx : x ∈ L), res R (Set.singleton_subset_iff.2 hx) d α = 0) → α = 0

variable {R}

section Glue

variable {X : TopCat.{0}}

/-- The inclusion `X ∖ L₁ ⟶ X ∖ (L₁ ∩ L₂)`. -/
abbrev glueIncl (L₁ L₂ : Set X) : TopCat.of ↥L₁ᶜ ⟶ TopCat.of ↥(L₁ ∩ L₂)ᶜ :=
  TopCat.ofHom (ContinuousMap.inclusion (Set.compl_subset_compl.2 Set.inter_subset_left))

/-- **Gluing lemma (GL).** Let `L₁, L₂` be closed and `α ∈ H_i(X | L₁ ∪ L₂)` with vanishing
restrictions to `L₁` and to `L₂`. If `H_{i+1}(X | L₁ ∩ L₂) = 0`, then `α = 0`. -/
theorem eq_zero_of_res_eq_zero {L₁ L₂ : Set X} (h₁ : IsClosed L₁) (h₂ : IsClosed L₂) {i : ℕ}
    (hint : IsZero (relH R X (L₁ ∩ L₂) (i + 1))) (α : relH R X (L₁ ∪ L₂) i)
    (hα₁ : res R Set.subset_union_left i α = 0) (hα₂ : res R Set.subset_union_right i α = 0) :
    α = 0 := by
  -- Step 1: `α` comes from `H_i(X ∖ L₁ | L₁ ∪ L₂)` (triple `(X, X ∖ L₁, X ∖ (L₁ ∪ L₂))`).
  obtain ⟨β, rfl⟩ := exists_push_incl_eq_of_res_eq_zero Set.subset_union_left α hα₁
  -- Step 2: excision `H_i(X ∖ L₁ | L₁ ∪ L₂) ≅ H_i(X ∖ (L₁ ∩ L₂) | L₂)`.
  have hexc : IsIso (push R (glueIncl L₁ L₂) (L := Subtype.val ⁻¹' (L₁ ∪ L₂))
      (L' := Subtype.val ⁻¹' L₂) (fun x hx => Or.inr hx) i) := by
    refine isIso_push_of_isEmbedding (f := glueIncl L₁ L₂)
      (IsEmbedding.inclusion (Set.compl_subset_compl.2 Set.inter_subset_left)) _
      (fun (x : ↥L₁ᶜ) (hx : x.1 ∈ L₁ ∪ L₂) => hx.resolve_left x.2) ?_ i
    have hcl : IsClosed (Subtype.val ⁻¹' L₂ : Set ↥(L₁ ∩ L₂)ᶜ) :=
      h₂.preimage continuous_subtype_val
    have hop : IsOpen (Set.range (glueIncl L₁ L₂)) := by
      have : Set.range (glueIncl L₁ L₂) = Subtype.val ⁻¹' L₁ᶜ := by
        ext y
        exact ⟨fun ⟨x, hx⟩ => hx ▸ x.2, fun hy => ⟨⟨y.1, hy⟩, rfl⟩⟩
      rw [this]
      exact h₁.isOpen_compl.preimage continuous_subtype_val
    rw [hcl.closure_eq, hop.interior_eq]
    intro y hy
    exact ⟨⟨y.1, fun hy₁ => y.2 ⟨hy₁, hy⟩⟩, rfl⟩
  -- Step 3: `H_i(X ∖ (L₁ ∩ L₂) | L₂) ⟶ H_i(X | L₂)` is injective (triple
  -- `(X, X ∖ (L₁ ∩ L₂), X ∖ L₂)`, using `H_{i+1}(X | L₁ ∩ L₂) = 0`).
  have hc := push_incl_injective (R := R) (L := L₂) Set.inter_subset_right hint
  -- Step 4: both composites are induced by the inclusion `X ∖ L₁ ⟶ X`.
  have key : pushIncl R (L₁ ∩ L₂)ᶜ L₂ i (push R (glueIncl L₁ L₂) (L := Subtype.val ⁻¹' (L₁ ∪ L₂))
      (L' := Subtype.val ⁻¹' L₂) (fun x hx => Or.inr hx) i β) = 0 := by
    have hp : ∀ x : TopCat.of ↥L₁ᶜ, incl L₁ᶜ x ∈ L₂ → x ∈ Subtype.val ⁻¹' (L₁ ∪ L₂) :=
      fun x hx => Or.inr hx
    exact (push_push_apply (glueIncl L₁ L₂) (incl (L₁ ∩ L₂)ᶜ) (incl L₁ᶜ) rfl _ _ hp i β).trans
      ((push_push_apply (incl L₁ᶜ) (𝟙 X) (incl L₁ᶜ) (Category.comp_id _) _ _ hp i β).symm.trans
        hα₂)
  -- Step 5: conclude.
  have he : push R (glueIncl L₁ L₂) (L := Subtype.val ⁻¹' (L₁ ∪ L₂))
      (L' := Subtype.val ⁻¹' L₂) (fun x hx => Or.inr hx) i β = 0 :=
    hc (key.trans (map_zero _).symm)
  have hβ : β = 0 := (ModuleCat.mono_iff_injective _).1 inferInstance (he.trans (map_zero _).symm)
  rw [hβ, map_zero]

lemma isZero_of_forall_eq_zero {M : ModuleCat.{0} R} (h : ∀ x : M, x = 0) : IsZero M :=
  @ModuleCat.isZero_of_subsingleton R _ M ⟨fun a b => (h a).trans (h b).symm⟩

lemma eq_zero_of_isZero {M : ModuleCat.{0} R} (hM : IsZero M) (x : M) : x = 0 :=
  @Subsingleton.elim _ (ModuleCat.isZero_iff_subsingleton.1 hM) x 0

/-- **Mayer–Vietoris for vanishing** (consequence of GL): `V(L₁), V(L₂), V(L₁ ∩ L₂) ⟹ V(L₁ ∪ L₂)`. -/
theorem VanishAbove.union {L₁ L₂ : Set X} (h₁ : IsClosed L₁) (h₂ : IsClosed L₂) {d : ℕ}
    (hv₁ : VanishAbove R X L₁ d) (hv₂ : VanishAbove R X L₂ d)
    (hv : VanishAbove R X (L₁ ∩ L₂) d) : VanishAbove R X (L₁ ∪ L₂) d := fun i hi =>
  isZero_of_forall_eq_zero fun α => eq_zero_of_res_eq_zero h₁ h₂ (hv (i + 1) (by omega)) α
    (eq_zero_of_isZero (hv₁ i hi) _) (eq_zero_of_isZero (hv₂ i hi) _)

/-- **Mayer–Vietoris for pointwise injectivity** (consequence of GL). -/
theorem PointInj.union {L₁ L₂ : Set X} (h₁ : IsClosed L₁) (h₂ : IsClosed L₂) {d : ℕ}
    (hp₁ : PointInj R X L₁ d) (hp₂ : PointInj R X L₂ d)
    (hint : IsZero (relH R X (L₁ ∩ L₂) (d + 1))) : PointInj R X (L₁ ∪ L₂) d := by
  intro α hα
  refine eq_zero_of_res_eq_zero h₁ h₂ hint α (hp₁ _ fun x hx => ?_) (hp₂ _ fun x hx => ?_)
  · exact (res_res_apply _ _ d α).trans (hα x (Or.inl hx))
  · exact (res_res_apply _ _ d α).trans (hα x (Or.inr hx))

lemma vanishAbove_empty (d : ℕ) : VanishAbove R X ∅ d := fun i _ => isZero_relH_empty X i

lemma pointInj_empty (d : ℕ) : PointInj R X ∅ d := fun α _ =>
  eq_zero_of_isZero (isZero_relH_empty X d) α

lemma PointInj.of_isZero {L : Set X} {d : ℕ} (h : IsZero (relH R X L d)) : PointInj R X L d :=
  fun α _ => eq_zero_of_isZero h α

end Glue

section Transport

variable {X Y : TopCat.{0}}

lemma injective_of_isIso {M N : ModuleCat.{0} R} (f : M ⟶ N) [IsIso f] : Function.Injective f :=
  (ModuleCat.mono_iff_injective f).1 inferInstance

lemma surjective_of_isIso {M N : ModuleCat.{0} R} (f : M ⟶ N) [IsIso f] :
    Function.Surjective f :=
  (ModuleCat.epi_iff_surjective f).1 inferInstance

/-- **Transport of `VanishAbove`** along an open embedding `f` with `L = f⁻¹ L'`, `L'` closed
in the range of `f` (excision). -/
theorem vanishAbove_iff_of_isOpenEmbedding {f : X ⟶ Y} (hf : IsOpenEmbedding f) {L : Set X}
    {L' : Set Y} (hL : ∀ x, f x ∈ L' ↔ x ∈ L) (hL' : IsClosed L') (hsub : L' ⊆ Set.range f)
    {d : ℕ} : VanishAbove R X L d ↔ VanishAbove R Y L' d := by
  have hi : ∀ i, IsIso (push R f (fun x => (hL x).1) i) := fun i =>
    isIso_push_of_isOpenEmbedding hf _ (fun x => (hL x).2) hL' hsub i
  exact ⟨fun h i hi' => (h i hi').of_iso (asIso (push R f (fun x => (hL x).1) i)).symm,
    fun h i hi' => (h i hi').of_iso (asIso (push R f (fun x => (hL x).1) i))⟩

/-- **Transport of `PointInj`** along an open embedding `f` with `L = f⁻¹ L'`, `L'` closed in the
range of `f` (excision, also at single points). -/
theorem pointInj_iff_of_isOpenEmbedding [T1Space Y] {f : X ⟶ Y} (hf : IsOpenEmbedding f)
    {L : Set X} {L' : Set Y} (hL : ∀ x, f x ∈ L' ↔ x ∈ L) (hL' : IsClosed L')
    (hsub : L' ⊆ Set.range f) {d : ℕ} : PointInj R X L d ↔ PointInj R Y L' d := by
  have hi : IsIso (push R f (fun x => (hL x).1) d) :=
    isIso_push_of_isOpenEmbedding hf _ (fun x => (hL x).2) hL' hsub d
  -- pushes at single points
  have hpt : ∀ x : X, ∀ z, f z ∈ ({f x} : Set Y) → z ∈ ({x} : Set X) := fun x z hz =>
    hf.injective hz
  have hres : ∀ x (hx : x ∈ L) (α : relH R X L d),
      res R (Set.singleton_subset_iff.2 ((hL x).2 hx)) d (push R f (fun x => (hL x).1) d α) =
        push R f (hpt x) d (res R (Set.singleton_subset_iff.2 hx) d α) := fun x hx α =>
    push_res_apply f _ _ _ _ d α
  constructor
  · intro hP β hβ
    obtain ⟨α, rfl⟩ := surjective_of_isIso (push R f (fun x => (hL x).1) d) β
    have hα : α = 0 := by
      refine hP α fun x hx => ?_
      have h' : ∀ z ∈ ({x} : Set X), f z ∈ ({f x} : Set Y) := by
        intro z hz
        rw [Set.mem_singleton_iff.1 hz]
        exact Set.mem_singleton _
      have hsub' : ({f x} : Set Y) ⊆ Set.range f := by
        intro y hy
        exact ⟨x, (Set.mem_singleton_iff.1 hy).symm⟩
      have hiso : IsIso (push R f (hpt x) d) :=
        isIso_push_of_isOpenEmbedding hf (hpt x) h' isClosed_singleton hsub' d
      refine injective_of_isIso (push R f (hpt x) d) ?_
      rw [map_zero, ← hres x hx α]
      exact hβ (f x) ((hL x).2 hx)
    rw [hα, map_zero]
  · intro hP α hα
    refine injective_of_isIso (push R f (fun x => (hL x).1) d) ?_
    rw [map_zero]
    refine hP _ fun y hy => ?_
    obtain ⟨x, rfl⟩ := hsub hy
    have hx : x ∈ L := (hL x).1 hy
    rw [hres x hx α, hα x hx, map_zero]

/-- The inverse of a chart, as a morphism `e.target ⟶ X`. -/
noncomputable def chartInv {F : Type} [TopologicalSpace F] (e : OpenPartialHomeomorph X F) :
    TopCat.of e.target ⟶ X :=
  TopCat.ofHom ⟨e.target.domRestrict e.symm, e.continuousOn_symm.domRestrict⟩

lemma isOpenEmbedding_chartInv {F : Type} [TopologicalSpace F] (e : OpenPartialHomeomorph X F) :
    IsOpenEmbedding (chartInv e) :=
  e.symm.isOpenEmbedding_restrict

lemma chartInv_mem_image_iff {F : Type} [TopologicalSpace F] (e : OpenPartialHomeomorph X F)
    {C : Set F} (hCt : C ⊆ e.target) (y : TopCat.of e.target) :
    chartInv e y ∈ e.symm '' C ↔ y ∈ Subtype.val ⁻¹' C := by
  constructor
  · rintro ⟨c, hc, hcy⟩
    have : c = y.1 := e.symm.injOn (hCt hc) y.2 hcy
    show y.1 ∈ C
    exact this ▸ hc
  · intro hy
    exact ⟨y.1, hy, rfl⟩

lemma isClosed_chart_image [T2Space X] {F : Type} [TopologicalSpace F] (e : OpenPartialHomeomorph X F) {C : Set F} (hC : IsCompact C)
    (hCt : C ⊆ e.target) : IsClosed (e.symm '' C) :=
  (hC.image_of_continuousOn (e.continuousOn_symm.mono hCt)).isClosed

lemma chart_image_subset_range {F : Type} [TopologicalSpace F] (e : OpenPartialHomeomorph X F) {C : Set F}
    (hCt : C ⊆ e.target) : e.symm '' C ⊆ Set.range (chartInv e) := by
  rintro _ ⟨c, hc, rfl⟩; exact ⟨⟨c, hCt hc⟩, rfl⟩

lemma subset_range_incl {F : Type} [TopologicalSpace F] {O C : Set (TopCat.of F)} (hCt : C ⊆ O) :
    C ⊆ Set.range (incl (X := TopCat.of F) O) :=
  fun c hc => ⟨⟨c, hCt hc⟩, rfl⟩

variable [T2Space X] {F : Type} [TopologicalSpace F] [T2Space F]

/-- **Chart transport (CT) of `VanishAbove`.** For a chart `e` of `X` and a compact
`C ⊆ e.target`, `V(C)` in `F` is equivalent to `V(e.symm '' C)` in `X`. -/
theorem vanishAbove_chart_iff (e : OpenPartialHomeomorph X F) {C : Set F} (hC : IsCompact C)
    (hCt : C ⊆ e.target) {d : ℕ} :
    VanishAbove R (TopCat.of F) C d ↔ VanishAbove R X (e.symm '' C) d := by
  have h1 := vanishAbove_iff_of_isOpenEmbedding (R := R) (d := d) (f := incl e.target)
    (L := Subtype.val ⁻¹' C) (L' := C) (isOpenEmbedding_incl e.open_target)
    (fun _ => Iff.rfl) hC.isClosed (subset_range_incl (F := F) hCt)
  have h2 := vanishAbove_iff_of_isOpenEmbedding (R := R) (d := d) (f := chartInv e)
    (L := Subtype.val ⁻¹' C) (L' := e.symm '' C) (isOpenEmbedding_chartInv e)
    (chartInv_mem_image_iff e hCt) (isClosed_chart_image e hC hCt)
    (chart_image_subset_range e hCt)
  exact h1.symm.trans h2

/-- **Chart transport (CT) of `PointInj`.** -/
theorem pointInj_chart_iff (e : OpenPartialHomeomorph X F) {C : Set F} (hC : IsCompact C)
    (hCt : C ⊆ e.target) {d : ℕ} :
    PointInj R (TopCat.of F) C d ↔ PointInj R X (e.symm '' C) d := by
  have h1 := pointInj_iff_of_isOpenEmbedding (R := R) (d := d) (f := incl e.target)
    (L := Subtype.val ⁻¹' C) (L' := C) (isOpenEmbedding_incl e.open_target)
    (fun _ => Iff.rfl) hC.isClosed (subset_range_incl (F := F) hCt)
  have h2 := pointInj_iff_of_isOpenEmbedding (R := R) (d := d) (f := chartInv e)
    (L := Subtype.val ⁻¹' C) (L' := e.symm '' C) (isOpenEmbedding_chartInv e)
    (chartInv_mem_image_iff e hCt) (isClosed_chart_image e hC hCt)
    (chart_image_subset_range e hCt)
  exact h1.symm.trans h2

end Transport

end HSFormal.Newman
