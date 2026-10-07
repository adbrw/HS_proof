import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Defs

/-!
# Uniform displacement on compact sets

These lemmas formalize the joint-continuity uniformization used in Sections 7 and 12 of
`fullHS_final.md`. They apply to noncompact metric spaces: only the set on which
displacement is measured must be compact. They do not assert the Hilbert–Smith
conjecture or assume any of the proposed controlled realization statements.
-/

open Set Filter
open scoped Topology

namespace HSFormal

section CompactImage

variable {G X : Type*} [Monoid G] [TopologicalSpace G] [TopologicalSpace X]
  [MulAction G X] [ContinuousSMul G X]

/-- If a compact set lies inside an open chart domain, all its translates by one
identity neighborhood remain inside that domain. -/
@[to_additive]
theorem exists_open_uniform_smul_mem {K U : Set X} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧
      ∀ g ∈ V, ∀ x ∈ K, g • x ∈ U := by
  have hsub : ({1} : Set G) ×ˢ K ⊆
      (fun z : G × X => z.1 • z.2) ⁻¹' U := by
    rintro ⟨g, x⟩ ⟨hg, hx⟩
    rcases Set.mem_singleton_iff.mp hg with rfl
    simpa only [Set.mem_preimage, one_smul] using hKU hx
  obtain ⟨V, W, hV, _, hOne, hKW, hVW⟩ :=
    generalized_tube_lemma isCompact_singleton hK (hU.preimage continuous_smul) hsub
  exact ⟨V, hV, hOne (Set.mem_singleton 1),
    fun g hg x hx => hVW (show (g, x) ∈ V ×ˢ W from ⟨hg, hKW hx⟩)⟩

end CompactImage

section CompactDisplacement

variable {G X : Type*} [Monoid G] [TopologicalSpace G] [MetricSpace X]
  [MulAction G X] [ContinuousSMul G X]

/-- Joint continuity gives a single open identity neighborhood on which every point of
a prescribed compact set moves less than `ε`. No compactness of the group or ambient
space is required. -/
@[to_additive exists_open_uniform_vadd_displacement /-- Joint continuity gives a single open zero neighborhood on which every
point of a prescribed compact set moves less than `ε`. -/]
theorem exists_open_uniform_displacement {K : Set X} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧
      ∀ g ∈ V, ∀ x ∈ K, dist (g • x) x < ε := by
  have hcont : Continuous (fun z : G × X => dist (z.1 • z.2) z.2) :=
    continuous_smul.dist continuous_snd
  have hopen : IsOpen {z : G × X | dist (z.1 • z.2) z.2 < ε} :=
    isOpen_lt hcont continuous_const
  have hsub : ({1} : Set G) ×ˢ K ⊆
      {z : G × X | dist (z.1 • z.2) z.2 < ε} := by
    rintro ⟨g, x⟩ ⟨hg, _⟩
    rcases Set.mem_singleton_iff.mp hg with rfl
    simpa only [one_smul, dist_self, Set.mem_ofPred_eq] using hε
  obtain ⟨V, U, hV, _, hOne, hKU, hVU⟩ :=
    generalized_tube_lemma isCompact_singleton hK hopen hsub
  exact ⟨V, hV, hOne (Set.mem_singleton 1),
    fun g hg x hx => hVU (show (g, x) ∈ V ×ˢ U from ⟨hg, hKU hx⟩)⟩

/-- A neighborhood-filter version of uniform compact displacement. -/
@[to_additive exists_mem_nhds_uniform_vadd_displacement]
theorem exists_mem_nhds_uniform_displacement {K : Set X} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ V ∈ 𝓝 (1 : G), ∀ g ∈ V, ∀ x ∈ K, dist (g • x) x < ε := by
  obtain ⟨V, hV, hOne, hmove⟩ := exists_open_uniform_displacement (G := G) hK hε
  exact ⟨V, hV.mem_nhds hOne, hmove⟩

/-- If a family of sets eventually lies in every identity neighborhood, its action
displacements converge uniformly to zero on each compact set. This is the exact
uniformization needed after choosing shrinking open subgroups in Section 7. -/
@[to_additive eventually_uniform_vadd_displacement_of_shrinking /-- If a family of sets eventually lies in every zero neighborhood, its
action displacements converge uniformly to zero on each compact set. -/]
theorem eventually_uniform_displacement_of_shrinking {I : Type*} {l : Filter I}
    (A : I → Set G)
    (hA : ∀ V ∈ 𝓝 (1 : G), ∀ᶠ i in l, A i ⊆ V)
    {K : Set X} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ g ∈ A i, ∀ x ∈ K, dist (g • x) x < ε := by
  obtain ⟨V, hV, hmove⟩ := exists_mem_nhds_uniform_displacement (G := G) hK hε
  exact (hA V hV).mono fun _ hi g hg x hx => hmove g (hi hg) x hx

end CompactDisplacement

end HSFormal
