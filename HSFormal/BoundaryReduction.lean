import HSFormal.Reduction
import Mathlib.Analysis.Convex.Topology

/-!
# Section 12, last paragraph: manifolds with boundary

This file formalizes the boundary step of Section 12 of `fullHS_final.md` (L1134). For a
connected manifold `M` modelled on the half-space `EuclideanHalfSpace d` (`d ≥ 1`), the
*topological interior* `topInterior d M` (points with an open neighbourhood homeomorphic to an
open subset of `ℝ^d`) is open, dense, connected, a boundaryless `d`-manifold, and preserved by
every homeomorphism, so an effective action of a group on `M` restricts to an effective action
on it. Using the topological interior (instead of local homology, as in the manuscript) makes
homeomorphism invariance immediate; the connectedness argument is the closure sandwich
`Q ⊆ N ∩ Int M ⊆ closure Q` for the open half-ball `Q` of a boundary chart.

Main results: `HSFormal.hilbertSmithWithBoundary_of_hilbertSmith`,
`HSFormal.padicExclusionWithBoundary_of_padicExclusion`, and the assembled top-level reduction
`HSFormal.hilbertSmith_all_of_padicExclusion`.
-/

open Set Filter Function
open Topology

namespace HSFormal

section TopInterior

variable (d : ℕ) (M : Type*) [TopologicalSpace M]

/-- The topological interior of a space of dimension `d`: points lying in the source of some
open partial homeomorphism to `ℝ^d`, i.e. having an open neighbourhood homeomorphic to an open
subset of `ℝ^d`. -/
def topInterior : Set M :=
  {x | ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin d)), x ∈ e.source}

variable {d M}

theorem isOpen_topInterior : IsOpen (topInterior d M) :=
  isOpen_iff_forall_mem_open.2 fun _ ⟨e, hx⟩ => ⟨e.source, fun _ hy => ⟨e, hy⟩, e.open_source, hx⟩

/-- Homeomorphisms preserve the topological interior. -/
theorem homeomorph_mem_topInterior (h : M ≃ₜ M) {x : M} (hx : x ∈ topInterior d M) :
    h x ∈ topInterior d M := by
  obtain ⟨e, he⟩ := hx
  exact ⟨h.symm.toOpenPartialHomeomorph.trans e, by simpa using he⟩

variable (d M)

/-- The topological interior is a boundaryless topological `d`-manifold. -/
noncomputable def topInteriorChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin d)) (topInterior d M) where
  atlas := range fun x : topInterior d M =>
    (x.2.choose).subtypeRestr (s := ⟨topInterior d M, isOpen_topInterior⟩) ⟨x⟩
  chartAt x := (x.2.choose).subtypeRestr (s := ⟨topInterior d M, isOpen_topInterior⟩) ⟨x⟩
  mem_chart_source x := by
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact x.2.choose_spec
  chart_mem_atlas x := mem_range_self x

end TopInterior

section Action

variable {d : ℕ} {M : Type*} [TopologicalSpace M] {G : Type*} [Group G] [MulAction G M]
  [ContinuousConstSMul G M]

@[to_additive]
theorem smul_mem_topInterior (g : G) {x : M} (hx : x ∈ topInterior d M) :
    g • x ∈ topInterior d M :=
  homeomorph_mem_topInterior (Homeomorph.smul g) hx

variable (d M G) in
/-- The restriction of an action by homeomorphisms to the topological interior. -/
@[to_additive /-- The restriction of an additive action by homeomorphisms to the topological
interior. -/]
def topInteriorMulAction : MulAction G (topInterior d M) where
  smul g x := ⟨g • x.1, smul_mem_topInterior g x.2⟩
  one_smul x := Subtype.ext (one_smul G x.1)
  mul_smul g h x := Subtype.ext (mul_smul g h x.1)

@[to_additive]
theorem topInterior_continuousSMul [TopologicalSpace G] [ContinuousSMul G M] :
    letI := topInteriorMulAction d M G
    ContinuousSMul G (topInterior d M) :=
  letI := topInteriorMulAction d M G
  ⟨((continuous_fst.smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _)⟩

@[to_additive]
theorem topInterior_faithfulSMul [T2Space M] [FaithfulSMul G M]
    (hdense : Dense (topInterior d M)) :
    letI := topInteriorMulAction d M G
    FaithfulSMul G (topInterior d M) := by
  letI := topInteriorMulAction d M G
  refine ⟨fun {g₁ g₂} h => eq_of_smul_eq_smul (α := M) fun y => ?_⟩
  have := (continuous_const_smul g₁).ext_on hdense (continuous_const_smul g₂)
    fun x hx => congrArg Subtype.val (h ⟨x, hx⟩)
  exact congrFun this y

end Action

section HalfSpace

variable {d : ℕ} [NeZero d]

/-- The open half-space `{0 < x₀}` inside the half-space model. -/
def posHalf (d : ℕ) [NeZero d] : Set (EuclideanHalfSpace d) := {z | 0 < z.1 0}

theorem isOpen_posHalf : IsOpen (posHalf d) :=
  isOpen_lt continuous_const (by fun_prop)

theorem posHalf_isOpenEmbedding :
    IsOpenEmbedding (fun z : posHalf d => (z.1.1 : EuclideanSpace ℝ (Fin d))) := by
  refine ⟨IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal, ?_⟩
  have : range (fun z : posHalf d => (z.1.1 : EuclideanSpace ℝ (Fin d))) =
      {v | 0 < v 0} := by
    ext v
    refine ⟨?_, fun hv => ⟨⟨⟨v, hv.le⟩, hv⟩, rfl⟩⟩
    rintro ⟨z, rfl⟩
    exact z.2
  rw [this]
  exact isOpen_lt continuous_const (by fun_prop)

instance : Nonempty (posHalf d) :=
  ⟨⟨⟨EuclideanSpace.single 0 1, by simp⟩, by simp [posHalf]⟩⟩

/-- The open half-space of the model, as an open partial homeomorphism to `ℝ^d`. -/
noncomputable def posHalfChart (d : ℕ) [NeZero d] :
    OpenPartialHomeomorph (EuclideanHalfSpace d) (EuclideanSpace ℝ (Fin d)) :=
  (posHalf_isOpenEmbedding.toOpenPartialHomeomorph _).lift_openEmbedding
    isOpen_posHalf.isOpenEmbedding_subtypeVal

theorem posHalf_subset_source : posHalf d ⊆ (posHalfChart d).source :=
  fun z hz => ⟨⟨z, hz⟩, mem_univ _, rfl⟩

/-- Every point of the half-space is a limit of points of the open half-space, along a
continuous path. -/
theorem exists_path_posHalf (z : EuclideanHalfSpace d) :
    ∃ f : ℝ → EuclideanHalfSpace d, Continuous f ∧ f 0 = z ∧ ∀ t, 0 < t → f t ∈ posHalf d := by
  refine ⟨fun t => ⟨z.1 + max t 0 • EuclideanSpace.single 0 1, ?_⟩, ?_, ?_, ?_⟩
  · have := z.2
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, ite_true,
      smul_eq_mul, mul_one]
    positivity
  · exact (continuous_const.add ((continuous_id.max continuous_const).smul
      continuous_const)).subtype_mk _
  · ext1; simp
  · intro t ht
    have := z.2
    simp only [posHalf, mem_ofPred_eq, PiLp.add_apply, PiLp.smul_apply,
      PiLp.single_apply, ite_true, smul_eq_mul, mul_one, max_eq_left ht.le]
    linarith

/-- For an open set `B` of the target of a chart `c` of a half-space manifold, the image of `B`
lies in the closure of the image of `B ∩ {0 < x₀}`. -/
theorem symm_image_subset_closure {M : Type*} [TopologicalSpace M]
    (c : OpenPartialHomeomorph M (EuclideanHalfSpace d)) {B : Set (EuclideanHalfSpace d)}
    (hB : IsOpen B) (hBt : B ⊆ c.target) :
    c.symm '' B ⊆ closure (c.symm '' (B ∩ posHalf d)) := by
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨f, hf, hf0, hpos⟩ := exists_path_posHalf z
  have hlim : Tendsto f (𝓝[>] 0) (𝓝 z) := hf0 ▸ hf.continuousAt.continuousWithinAt.tendsto
  refine mem_closure_of_tendsto ((c.continuousAt_symm (hBt hz)).tendsto.comp hlim) ?_
  filter_upwards [hlim (hB.mem_nhds hz), self_mem_nhdsWithin] with t hB' ht
  exact ⟨f t, ⟨hB', hpos t ht⟩, rfl⟩

/-- Chart points with positive first coordinate are interior points. -/
theorem symm_image_posHalf_subset_topInterior {M : Type*} [TopologicalSpace M]
    (c : OpenPartialHomeomorph M (EuclideanHalfSpace d)) :
    c.symm '' (c.target ∩ posHalf d) ⊆ topInterior d M := by
  rintro _ ⟨z, ⟨hzt, hzp⟩, rfl⟩
  refine ⟨c.trans (posHalfChart d), ?_⟩
  simp only [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage]
  exact ⟨c.map_target hzt, by rw [c.right_inv hzt]; exact posHalf_subset_source hzp⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace d) M]

/-- The topological interior of a half-space manifold is dense. -/
theorem dense_topInterior : Dense (topInterior d M) := by
  intro x
  set c := chartAt (EuclideanHalfSpace d) x
  have hx : x ∈ c.symm '' c.target := ⟨c x, c.map_source (mem_chart_source _ x), c.left_inv
    (mem_chart_source _ x)⟩
  exact closure_mono (symm_image_posHalf_subset_topInterior c)
    (symm_image_subset_closure c c.open_target subset_rfl hx)

/-- Every point has an open neighbourhood whose intersection with the interior is preconnected:
for a convex chart ball `B`, `Q = c⁻¹(B ∩ {0 < x₀}) ⊆ c⁻¹(B) ∩ Int M ⊆ closure Q`. -/
theorem exists_isPreconnected_inter_topInterior (x : M) :
    ∃ N : Set M, IsOpen N ∧ x ∈ N ∧ IsPreconnected (N ∩ topInterior d M) := by
  set c := chartAt (EuclideanHalfSpace d) x
  have hxs : x ∈ c.source := mem_chart_source _ x
  obtain ⟨t, ht, htt⟩ : ∃ t ∈ 𝓝 (c x).1, Subtype.val ⁻¹' t ⊆ c.target := by
    have := c.open_target.mem_nhds (c.map_source hxs)
    erw [nhds_subtype, mem_comap] at this; exact this
  obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.1 ht
  set B : Set (EuclideanHalfSpace d) := Subtype.val ⁻¹' Metric.ball (c x).1 r
  have hB : IsOpen B := Metric.isOpen_ball.preimage continuous_subtype_val
  have hBt : B ⊆ c.target := (preimage_mono hrt).trans htt
  have hpc : IsPreconnected (B ∩ posHalf d) := by
    erw [← IsInducing.subtypeVal.isPreconnected_image]
    have : Subtype.val '' (B ∩ posHalf d) = Metric.ball (c x).1 r ∩ {v | 0 < v 0} := by
      ext v
      refine ⟨?_, fun hv => ⟨⟨v, hv.2.le⟩, ⟨hv.1, hv.2⟩, rfl⟩⟩
      rintro ⟨z, ⟨hzB, hzp⟩, rfl⟩
      exact ⟨hzB, hzp⟩
    have hconv : Convex ℝ {v : EuclideanSpace ℝ (Fin d) | 0 < v 0} :=
      convex_halfSpace_gt (f := fun v : EuclideanSpace ℝ (Fin d) => v 0)
        ⟨fun _ _ => rfl, fun _ _ => rfl⟩ 0
    have h2 : IsPreconnected
        (Metric.ball (c x).1 r ∩ {v : EuclideanSpace ℝ (Fin d) | 0 < v 0}) :=
      ((convex_ball _ _).inter hconv).isPreconnected
    convert h2 using 1
    exact this
  refine ⟨c.source ∩ c ⁻¹' B, c.isOpen_inter_preimage hB, ⟨hxs, ?_⟩, ?_⟩
  · simp [B, hr]
  rw [← c.symm_image_eq_source_inter_preimage hBt]
  refine (hpc.image _ (c.continuousOn_symm.mono (inter_subset_left.trans hBt))).subset_closure
    (subset_inter (image_mono inter_subset_left) ?_)
    (inter_subset_left.trans (symm_image_subset_closure c hB hBt))
  exact (image_mono (inter_subset_inter_left _ hBt)).trans
    (symm_image_posHalf_subset_topInterior c)

end HalfSpace

/-- A dense subset of a preconnected space is preconnected as soon as every point has an open
neighbourhood meeting it in a preconnected set. -/
theorem isPreconnected_of_dense_of_local {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {I : Set X} (hI : Dense I) (hloc : ∀ x, ∃ N, IsOpen N ∧ x ∈ N ∧ IsPreconnected (N ∩ I)) :
    IsPreconnected I := by
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hIuv hIuv'
  by_contra hcon
  rw [not_or, not_subset, not_subset] at hcon
  obtain ⟨⟨b, hbI, hbu⟩, ⟨a, haI, hav⟩⟩ := hcon
  let A := {x | ∃ N, IsOpen N ∧ x ∈ N ∧ N ∩ I ⊆ u}
  let B := {x | ∃ N, IsOpen N ∧ x ∈ N ∧ N ∩ I ⊆ v}
  have hA : IsOpen A := isOpen_iff_forall_mem_open.2 fun x ⟨N, hN, hxN, hNu⟩ =>
    ⟨N, fun y hy => ⟨N, hN, hy, hNu⟩, hN, hxN⟩
  have hB : IsOpen B := isOpen_iff_forall_mem_open.2 fun x ⟨N, hN, hxN, hNv⟩ =>
    ⟨N, fun y hy => ⟨N, hN, hy, hNv⟩, hN, hxN⟩
  have hcover : univ ⊆ A ∪ B := by
    intro x _
    obtain ⟨N, hN, hxN, hpc⟩ := hloc x
    rcases isPreconnected_iff_subset_of_disjoint.1 hpc u v hu hv
        (fun y hy => hIuv hy.2)
        (eq_empty_of_subset_empty fun y ⟨⟨_, hyI⟩, hyuv⟩ =>
          hIuv' ▸ (⟨hyI, hyuv⟩ : y ∈ I ∩ (u ∩ v))) with h | h
    · exact Or.inl ⟨N, hN, hxN, h⟩
    · exact Or.inr ⟨N, hN, hxN, h⟩
  have huA : (univ ∩ A).Nonempty := by
    have hau : a ∈ u := ((hIuv haI).resolve_right hav)
    exact ⟨a, mem_univ _, u, hu, hau, inter_subset_left⟩
  have hvB : (univ ∩ B).Nonempty := by
    have hbv : b ∈ v := ((hIuv hbI).resolve_left hbu)
    exact ⟨b, mem_univ _, v, hv, hbv, inter_subset_left⟩
  obtain ⟨x, -, ⟨N₁, hN₁, hx₁, h₁⟩, ⟨N₂, hN₂, hx₂, h₂⟩⟩ :=
    isPreconnected_univ A B hA hB hcover huA hvB
  obtain ⟨y, ⟨hy₁, hy₂⟩, hyI⟩ := hI.inter_open_nonempty (N₁ ∩ N₂) (hN₁.inter hN₂) ⟨x, hx₁, hx₂⟩
  have : y ∈ I ∩ (u ∩ v) := ⟨hyI, h₁ ⟨hy₁, hyI⟩, h₂ ⟨hy₂, hyI⟩⟩
  rw [hIuv'] at this
  exact this

section Assembly

variable {d : ℕ} [NeZero d] {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace d) M] [ConnectedSpace M]

/-- The topological interior of a connected half-space manifold is connected. -/
theorem connectedSpace_topInterior : ConnectedSpace (topInterior d M) := by
  obtain ⟨x₀⟩ : Nonempty M := inferInstance
  have hd := dense_topInterior (d := d) (M := M)
  obtain ⟨x, hx⟩ := hd.nonempty
  exact isConnected_iff_connectedSpace.mp
    ⟨⟨x, hx⟩, isPreconnected_of_dense_of_local hd exists_isPreconnected_inter_topInterior⟩

end Assembly

/-- **Section 12, boundary case** (L1134): the Hilbert–Smith statement for manifolds with
boundary follows from the boundaryless one, applied to the topological interior. -/
theorem hilbertSmithWithBoundary_of_hilbertSmith (h : HilbertSmith) :
    HilbertSmithWithBoundary := by
  intro n M _ _ _ _ _ G _ _ _ _ _ _ _ _ _
  letI := topInteriorChartedSpace (n + 1) M
  haveI := connectedSpace_topInterior (d := n + 1) (M := M)
  letI := topInteriorMulAction (n + 1) M G
  haveI := topInterior_continuousSMul (d := n + 1) (M := M) (G := G)
  haveI := topInterior_faithfulSMul (d := n + 1) (M := M) (G := G) dense_topInterior
  exact h (n + 1) (topInterior (n + 1) M) G

/-- **Section 12, boundary case** (L1134) for the p-adic exclusion. -/
theorem padicExclusionWithBoundary_of_padicExclusion (h : PadicExclusion) :
    PadicExclusionWithBoundary := by
  intro p _ n M _ _ _ _ _ _ _ hfaith
  letI := topInteriorChartedSpace (n + 1) M
  haveI := connectedSpace_topInterior (d := n + 1) (M := M)
  letI := topInteriorAddAction (n + 1) M ℤ_[p]
  haveI := topInterior_continuousVAdd (d := n + 1) (M := M) (G := ℤ_[p])
  haveI := topInterior_faithfulVAdd (d := n + 1) (M := M) (G := ℤ_[p]) dense_topInterior
  exact h p (n + 1) (topInterior (n + 1) M) inferInstance

/-- **Top-level reduction** (Section 1, L21, and Section 12): the p-adic exclusion and the
published inputs [Gol10, §8], [Lee97, Thm 3.1], [Pa18, Theorem (Newman)] give the
Hilbert–Smith statement and the p-adic exclusion for connected manifolds with or without
boundary. -/
theorem hilbertSmith_all_of_padicExclusion (hNSS : NSSIsLie) (hLee : CompactNonLieContainsPadic)
    (hNewman : UniformNewman) (hP : PadicExclusion) :
    HilbertSmith ∧ HilbertSmithWithBoundary ∧ PadicExclusionWithBoundary :=
  have hHS := hilbertSmith_of_padicExclusion hNSS hLee hNewman hP
  ⟨hHS, hilbertSmithWithBoundary_of_hilbertSmith hHS,
    padicExclusionWithBoundary_of_padicExclusion hP⟩

end HSFormal
