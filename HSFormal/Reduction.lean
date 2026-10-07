import HSFormal.Statement
import HSFormal.TopologicalReduction
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-!
# Section 12: Hilbert–Smith from the p-adic exclusion

This file proves the reduction of Section 12 of `fullHS_final.md` (L1130–1132): the
boundaryless Hilbert–Smith statement `HSFormal.HilbertSmith` follows from the proposed
p-adic exclusion `HSFormal.PadicExclusion` together with the three published inputs
`HSFormal.NSSIsLie` [Gol10, §8], `HSFormal.CompactNonLieContainsPadic` [Lee97, Thm 3.1] and
`HSFormal.UniformNewman` [Pa18, Theorem (Newman)], all passed as explicit hypotheses.

* `HSFormal.false_of_padic_hom`: a continuous injective `ℤ_[p] → C` into a group acting
  effectively pulls the action back to an effective `ℤ_[p]`-action (L1130).
* `HSFormal.isLieGroup_of_isCompact`: every compact subgroup is Lie (L1130).
* `HSFormal.noSmallSubgroups_of_metric`: no small subgroups, for a compatible metric (L1132).
* `HSFormal.hilbertSmith_of_padicExclusion`: the main reduction.
* `HSFormal.padicExclusion_of_hilbertSmith`: the (unconditional) converse, a sanity check that
  the two statements are not vacuous; hence `HSFormal.hilbertSmith_iff_padicExclusion`.
-/

open Set Filter
open scoped Topology

namespace HSFormal

section PadicPullback

variable {p : ℕ} [Fact p.Prime] {C M : Type*} [Monoid C] [MulAction C M]

/-- The additive `ℤ_[p]`-action on `M` pulled back along a homomorphism `ι : ℤ_[p] → C`. -/
abbrev padicActionOfHom (ι : Multiplicative ℤ_[p] →* C) : AddAction ℤ_[p] M where
  vadd a x := ι (Multiplicative.ofAdd a) • x
  zero_vadd x := show ι (Multiplicative.ofAdd 0) • x = x by
    rw [ofAdd_zero, map_one, one_smul]
  add_vadd a b x := show ι (Multiplicative.ofAdd (a + b)) • x =
      ι (Multiplicative.ofAdd a) • ι (Multiplicative.ofAdd b) • x by
    rw [ofAdd_add, map_mul, mul_smul]

end PadicPullback

/-- A continuous injective homomorphism `ℤ_[p] → C` into a group acting continuously and
effectively on a connected manifold contradicts the p-adic exclusion (L1130). -/
theorem false_of_padic_hom (hP : PadicExclusion) {p : ℕ} [Fact p.Prime] {n : ℕ} {M : Type}
    [TopologicalSpace M]
    [T2Space M] [SecondCountableTopology M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ConnectedSpace M] {C : Type} [Monoid C] [TopologicalSpace C] [MulAction C M]
    [ContinuousSMul C M] [FaithfulSMul C M] (ι : Multiplicative ℤ_[p] →* C)
    (hcont : Continuous ι) (hinj : Function.Injective ι) : False := by
  letI : AddAction ℤ_[p] M := padicActionOfHom ι
  haveI : ContinuousVAdd ℤ_[p] M :=
    ⟨(hcont.comp (continuous_ofAdd.comp continuous_fst)).smul continuous_snd⟩
  refine hP p n M ⟨fun {a b} h => ?_⟩
  exact Multiplicative.ofAdd.injective (hinj (eq_of_smul_eq_smul (α := M) h))

section Reduction

variable {n : ℕ} {M : Type} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [SecondCountableTopology G]

/-- **Step 12.R1** (L1130). For an effective action on a connected manifold, every compact
subgroup is a Lie group, by [Lee97, Thm 3.1] and the p-adic exclusion. -/
theorem isLieGroup_of_isCompact (hLee : CompactNonLieContainsPadic) (hP : PadicExclusion)
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ConnectedSpace M]
    [MulAction G M] [ContinuousSMul G M] [FaithfulSMul G M]
    (K : Subgroup G) (hK : IsCompact (K : Set G)) : IsLieGroup K := by
  by_contra hnot
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : SecondCountableTopology K := inferInstanceAs (SecondCountableTopology (K : Set G))
  obtain ⟨p, _, ι, hcont, hinj⟩ := hLee n M K hnot
  exact false_of_padic_hom hP (n := n) (M := M) ι hcont hinj

/-- **Step 12.R2** (L1132), for a compatible metric on `M`: the group has no small subgroups.
Take a compact neighbourhood `K` of a point and `U = interior K`, the Newman threshold `ε` on
`U`, an identity neighbourhood `V` moving `K` by less than `ε`, and a compact identity
neighbourhood `W ⊆ V`. The closure of a subgroup inside `W` is compact, hence Lie, hence acts
trivially, hence is trivial. -/
theorem noSmallSubgroups_of_metric (hLee : CompactNonLieContainsPadic)
    (hNewman : UniformNewman) (hP : PadicExclusion) [LocallyCompactSpace G]
    [MetricSpace M] [SecondCountableTopology M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ConnectedSpace M] [MulAction G M] [ContinuousSMul G M] [FaithfulSMul G M] :
    NoSmallSubgroups G := by
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  obtain ⟨x₀⟩ : Nonempty M := inferInstance
  obtain ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x₀
  obtain ⟨ε, hε, hN⟩ := hNewman n M (interior K) isOpen_interior
    ⟨x₀, mem_interior_iff_mem_nhds.2 hKx⟩
  obtain ⟨V, hV, hmove⟩ := exists_mem_nhds_uniform_displacement (G := G) hK hε
  obtain ⟨W, hW, hWV, hWc⟩ := local_compact_nhds hV
  refine ⟨W, hW, fun S hS => ?_⟩
  set T := S.topologicalClosure
  have hTW : (T : Set G) ⊆ W := by
    rw [Subgroup.topologicalClosure_coe]
    exact closure_minimal hS hWc.isClosed
  have hTc : IsCompact (T : Set G) := hWc.of_isClosed_subset S.isClosed_topologicalClosure hTW
  have hLie : IsLieGroup T := isLieGroup_of_isCompact hLee hP (n := n) (M := M) T hTc
  haveI : CompactSpace T := isCompact_iff_compactSpace.mp hTc
  haveI : SecondCountableTopology T := inferInstanceAs (SecondCountableTopology (T : Set G))
  have htriv : ∀ (c : T) (x : M), c • x = x :=
    hN T hLie fun c x hx => hmove c (hWV (hTW c.2)) x (interior_subset hx)
  refine (Subgroup.eq_bot_iff_forall S).2 fun g hg => ?_
  refine eq_of_smul_eq_smul (α := M) fun x => ?_
  rw [one_smul]
  exact htriv ⟨g, S.le_topologicalClosure hg⟩ x

end Reduction

/-- **Section 12** (L1130–1132): the boundaryless Hilbert–Smith statement follows from the p-adic
exclusion and the published inputs [Gol10, §8], [Lee97, Thm 3.1] and [Pa18, Theorem (Newman)]. -/
theorem hilbertSmith_of_padicExclusion (hNSS : NSSIsLie) (hLee : CompactNonLieContainsPadic)
    (hNewman : UniformNewman) (hP : PadicExclusion) : HilbertSmith := by
  intro n M _ _ _ _ _ G _ _ _ _ _ _ _ _ _
  refine hNSS G ?_
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  letI : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  exact noSmallSubgroups_of_metric (n := n) (M := M) hLee hNewman hP

section Converse

variable (p : ℕ) [Fact p.Prime]

/-- `{0}` is not open in `ℤ_[p]`. -/
theorem padicInt_not_isOpen_singleton_zero : ¬ IsOpen ({0} : Set ℤ_[p]) := by
  intro h
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 h 0 rfl
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hp1)
  have hmem : (p : ℤ_[p]) ^ k ∈ Metric.ball (0 : ℤ_[p]) ε := by
    rw [mem_ball_zero_iff, PadicInt.norm_p_pow, zpow_neg, zpow_natCast, ← inv_pow]
    exact hk
  have h0 : (p : ℤ_[p]) ^ k = 0 := hball hmem
  exact pow_ne_zero k (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) h0


/-- `ℤ_[p]` admits no charted-space structure modelled on any `ℝ^d`. -/
theorem padicInt_not_chartedSpace (d : ℕ)
    (cs : ChartedSpace (EuclideanSpace ℝ (Fin d)) (Multiplicative ℤ_[p])) : False := by
  haveI : TotallyDisconnectedSpace (Multiplicative ℤ_[p]) :=
    inferInstanceAs (TotallyDisconnectedSpace ℤ_[p])
  set e := chartAt (EuclideanSpace ℝ (Fin d)) (1 : Multiplicative ℤ_[p])
  have hx : (1 : Multiplicative ℤ_[p]) ∈ e.source := mem_chart_source _ _
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hsrc : e.source = {1} := Subset.antisymm
      (fun y hy => e.injOn hy hx (Subsingleton.elim _ _)) (singleton_subset_iff.2 hx)
    exact padicInt_not_isOpen_singleton_zero p (hsrc ▸ e.open_source)
  · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 e.open_target _ (e.map_source hx)
    set v : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single ⟨0, hd⟩ (r / 2)
    have hv : ‖v‖ = r / 2 := by
      simp [v, PiLp.norm_single, abs_of_pos hr]
    have hy : e 1 + v ∈ Metric.ball (e 1) r := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, hv]
      linarith
    have hpc : IsPreconnected (e.symm '' Metric.ball (e 1) r) :=
      (convex_ball _ _).isPreconnected.image _ (e.continuousOn_symm.mono hball)
    have heq := hpc.subsingleton (mem_image_of_mem _ (Metric.mem_ball_self hr))
      (mem_image_of_mem _ hy)
    have hv0 : v = 0 := by
      have := e.symm.injOn (by rw [e.symm_source]; exact e.map_source hx)
        (by rw [e.symm_source]; exact hball hy) heq
      simpa using this
    have : r / 2 = 0 := by rw [← hv, hv0, norm_zero]
    linarith

/-- `ℤ_[p]` is not a Lie group. -/
theorem not_isLieGroup_padicInt : ¬ IsLieGroup (Multiplicative ℤ_[p]) :=
  fun ⟨d, cs, _⟩ => padicInt_not_chartedSpace p d cs

/-- Sanity check of the statements: `HilbertSmith` implies `PadicExclusion`. -/
theorem padicExclusion_of_hilbertSmith (h : HilbertSmith) : PadicExclusion := by
  intro p _ n M _ _ _ _ _ _ _ hfaith
  haveI : ContinuousSMul (Multiplicative ℤ_[p]) M :=
    ⟨(continuous_toAdd.comp continuous_fst).vadd continuous_snd⟩
  haveI : FaithfulSMul (Multiplicative ℤ_[p]) M :=
    ⟨fun hg => Multiplicative.toAdd.injective (eq_of_vadd_eq_vadd hg)⟩
  exact not_isLieGroup_padicInt p (h n M (Multiplicative ℤ_[p]))

end Converse

/-- Modulo the published inputs, the Hilbert–Smith statement is equivalent to the p-adic
exclusion. -/
theorem hilbertSmith_iff_padicExclusion (hNSS : NSSIsLie) (hLee : CompactNonLieContainsPadic)
    (hNewman : UniformNewman) : HilbertSmith ↔ PadicExclusion :=
  ⟨padicExclusion_of_hilbertSmith, hilbertSmith_of_padicExclusion hNSS hLee hNewman⟩

end HSFormal
