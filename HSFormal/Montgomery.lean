import HSFormal.Statement
import HSFormal.FreePoint
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Montgomery's theorem on pointwise periodic homeomorphisms, from Newman's theorem

This file proves `HSFormal.pointwisePeriodicIsPeriodic_of_uniformNewman`: the published input
`HSFormal.PointwisePeriodicIsPeriodic` ([Mon37]) follows from `HSFormal.UniformNewman`
([Pa18, Theorem (Newman)]), which is used only for finite cyclic groups acting on connected open
subsets of the manifold with *zero* displacement on an open set. No uniformity of `ε` is used.

Write `F N = Fix (f^[N])` (closed, `f`-invariant) and `O = ⋃ N, int F (N+1)`, the set of points
near which the period is bounded.

* `HSFormal.newman_rigidity` (Newman): a periodic homeomorphism of a connected open `D ⊆ M`
  that is the identity on a nonempty open subset of `D` is the identity on `D`. The cyclic group
  it generates is finite and discrete, hence a compact Lie group of dimension `0`, acting
  effectively on the connected manifold `D` with displacement `0 < ε` on the open set.
* `HSFormal.mem_interior_perSet_of_mem_closure`: if `y ∈ int F (K+1) ∩ closure (int F (N+1))`
  then `y ∈ int F (N+1)` (apply rigidity to `f^[N+1]` on the component of `y` in `int F (K+1)`).
* `HSFormal.boundedSet_eq_univ`: `O = M`. Otherwise Baire on the closed set `Z = M \ O` gives `k`
  and an open `V` with `∅ ≠ V ∩ Z ⊆ F (k+1)`. Let `g = f^[k+1]`, `y ∈ V ∩ Z`, and `D` the
  component of `y` in `int (O ∪ F (k+1))`; `g` maps `D` to itself and fixes `D ∩ Z`. Some
  `w ∈ D ∩ O` is moved by `g` (else `y ∈ O`); say `w ∈ int F (m+1)`, and `Ω = D ∩ int F (m+1)`.
  By the previous step `g` fixes `D ∩ frontier Ω`, so `h = g` on `Ω`, `id` off `Ω`, is a
  periodic homeomorphism of `D`. If `Ω` is not dense in `D`, rigidity gives `h = id`,
  contradicting `h w = g w ≠ w`; if it is dense, `g^[m+1] = id` on `D`, so `y ∈ O`.
* Finally each `int F (N+1)` is clopen in `M = O`, so `f^[N+1] = id` on the connected `M`.
-/

open Set Filter Topology
open scoped Manifold ContDiff Topology

namespace HSFormal

/-- A discrete group is a Lie group (of dimension `0`). -/
theorem isLieGroup_of_discreteTopology (C : Type) [Group C] [TopologicalSpace C]
    [DiscreteTopology C] : IsLieGroup C := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 0)) C := ChartedSpace.ofDiscreteTopology
  refine ⟨0, this, ?_⟩
  haveI : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) ∞ C := IsManifold.of_discreteTopology _
  exact { contMDiff_mul := contMDiff_of_discreteTopology,
          contMDiff_inv := contMDiff_of_discreteTopology }

/-- **Newman's rigidity** (from `HSFormal.UniformNewman` for finite cyclic groups): a map `h`
which restricts to a periodic homeomorphism of a connected open set `D` and is the identity on a
nonempty open subset of `D` is the identity on `D`. -/
theorem newman_rigidity (hN : UniformNewman) {n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {D U : Set M} (hD : IsOpen D) (hDc : IsConnected D) (hU : IsOpen U)
    (hUD : (U ∩ D).Nonempty) {h : M → M} (hmaps : MapsTo h D D) (hcont : ContinuousOn h D)
    {m : ℕ} (hper : ∀ x ∈ D, h^[m + 1] x = x) (hfix : ∀ x ∈ U ∩ D, h x = x) :
    ∀ x ∈ D, h x = x := by
  set D' : TopologicalSpace.Opens M := ⟨D, hD⟩
  haveI : ConnectedSpace D' := isConnected_iff_connectedSpace.mp hDc
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  letI : MetricSpace D' := TopologicalSpace.metrizableSpaceMetric D'
  let H : D' → D' := fun x => ⟨h x, hmaps x.2⟩
  have hHit : ∀ (k : ℕ) (x : D'), ((H^[k] x : D') : M) = h^[k] x := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih => intro x; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
  have hHper : ∀ x : D', H^[m + 1] x = x := fun x => Subtype.ext ((hHit _ x).trans (hper x x.2))
  have hHc : Continuous H := (hcont.domRestrict).subtype_mk _
  let σ : Equiv.Perm D' :=
    { toFun := H
      invFun := H^[m]
      left_inv := fun x => by
        rw [← Function.iterate_succ_apply H m x]; exact hHper x
      right_inv := fun x => by
        rw [← Function.iterate_succ_apply' H m x]; exact hHper x }
  have hσpow : ∀ k : ℕ, ⇑(σ ^ k) = H^[k] := fun k => Equiv.Perm.coe_pow σ k
  have hσfin : IsOfFinOrder σ := isOfFinOrder_iff_pow_eq_one.mpr
    ⟨m + 1, Nat.succ_pos m, Equiv.ext fun x => by rw [hσpow]; exact hHper x⟩
  let C := Subgroup.zpowers σ
  letI : TopologicalSpace C := ⊥
  haveI : DiscreteTopology C := ⟨rfl⟩
  haveI : Finite C := finite_zpowers.2 hσfin
  have hCcont : ∀ c : C, Continuous fun x : D' => c • x := by
    intro c
    obtain ⟨k, hk⟩ := (hσfin.mem_powers_iff_mem_zpowers).2 c.2
    have : (fun x : D' => c • x) = H^[k] := by
      funext x
      rw [Subgroup.smul_def, ← hk, Equiv.Perm.smul_def, hσpow]
    rw [this]
    exact hHc.iterate k
  haveI : ContinuousSMul C D' :=
    ⟨continuous_prod_of_discrete_left.2 fun c => hCcont c⟩
  set U' : Set D' := Subtype.val ⁻¹' U
  have hU' : IsOpen U' := hU.preimage continuous_subtype_val
  have hU'ne : U'.Nonempty := by
    obtain ⟨x, hxU, hxD⟩ := hUD
    exact ⟨⟨x, hxD⟩, hxU⟩
  obtain ⟨ε, hε, hC⟩ := hN n D' U' hU' hU'ne
  have hstab : ∀ x ∈ U', ∀ c : C, c • x = x := by
    intro x hx c
    have hσx : σ ∈ MulAction.stabilizer (Equiv.Perm D') x :=
      Subtype.ext (hfix x ⟨hx, x.2⟩)
    have := (Subgroup.zpowers_le.2 hσx) c.2
    exact this
  have htriv := hC C (isLieGroup_of_discreteTopology C)
    (fun c x hx => by rw [hstab x hx c, dist_self]; exact hε)
  intro x hx
  have := htriv ⟨σ, Subgroup.mem_zpowers σ⟩ ⟨x, hx⟩
  exact congrArg Subtype.val this

section Montgomery

variable {M : Type} [TopologicalSpace M]

/-- The points fixed by `f^[N]`. -/
def perSet (f : M ≃ₜ M) (N : ℕ) : Set M := {x | f^[N] x = x}

theorem isClosed_perSet [T2Space M] (f : M ≃ₜ M) (N : ℕ) : IsClosed (perSet f N) :=
  isClosed_eq (f.continuous.iterate N) continuous_id

theorem mapsTo_perSet (f : M ≃ₜ M) (N : ℕ) : MapsTo f (perSet f N) (perSet f N) := by
  intro x hx
  change f^[N] (f x) = f x
  rw [← Function.iterate_succ_apply, Function.iterate_succ_apply', hx]

theorem mapsTo_interior_of_mapsTo (f : M ≃ₜ M) {S : Set M} (hS : MapsTo f S S) :
    MapsTo f (interior S) (interior S) := by
  intro x hx
  have : f '' interior S ⊆ interior S := by
    rw [f.image_interior]; exact interior_mono (image_subset_iff.2 hS)
  exact this (mem_image_of_mem f hx)

theorem iterate_mapsTo_interior_perSet (f : M ≃ₜ M) (N j : ℕ) :
    MapsTo f^[j] (interior (perSet f N)) (interior (perSet f N)) :=
  (mapsTo_interior_of_mapsTo f (mapsTo_perSet f N)).iterate j

/-- A point of period dividing `N` has period dividing every multiple of `N`. -/
theorem iterate_iterate_eq_of_mem_perSet (f : M ≃ₜ M) {N : ℕ} (j : ℕ) {x : M}
    (hx : x ∈ perSet f N) : (f^[j])^[N] x = x := by
  rw [← Function.iterate_mul, mul_comm]
  exact Function.IsPeriodicPt.mul_const hx j

/-- The set of points near which the period is bounded. -/
def boundedSet (f : M ≃ₜ M) : Set M := ⋃ N : ℕ, interior (perSet f (N + 1))

theorem interior_perSet_subset_boundedSet (f : M ≃ₜ M) {N : ℕ} (hN : 0 < N) :
    interior (perSet f N) ⊆ boundedSet f := by
  intro x hx
  obtain ⟨N', rfl⟩ := Nat.exists_eq_add_of_lt hN
  exact mem_iUnion.2 ⟨N', by simpa [add_comm] using hx⟩

/-- **Local closedness** (Newman). If `f^[K+1] = id` near `y` and `y` is a limit of points near
which `f^[N+1] = id`, then `f^[N+1] = id` near `y`. -/
theorem mem_interior_perSet_of_mem_closure (hN : UniformNewman) {n : ℕ} [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M ≃ₜ M) {K N : ℕ} {y : M}
    (hyK : y ∈ interior (perSet f (K + 1)))
    (hyN : y ∈ closure (interior (perSet f (N + 1)))) :
    y ∈ interior (perSet f (N + 1)) := by
  haveI : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  set C := connectedComponentIn (interior (perSet f (K + 1))) y
  have hCo : IsOpen C := isOpen_interior.connectedComponentIn
  have hCc : IsConnected C := isConnected_connectedComponentIn_iff.2 hyK
  have hyC : y ∈ C := mem_connectedComponentIn hyK
  have hCsub : C ⊆ interior (perSet f (K + 1)) := connectedComponentIn_subset _ _
  set g := f^[N + 1]
  have hgc : Continuous g := f.continuous.iterate _
  have hgy : g y = y :=
    (closure_minimal interior_subset (isClosed_perSet f (N + 1))) hyN
  have hgC : MapsTo g C C := by
    intro x hx
    have hsub : g '' C ⊆ C := by
      refine (hCc.isPreconnected.image g hgc.continuousOn).subset_connectedComponentIn
        ⟨y, hyC, hgy⟩ ?_
      rintro _ ⟨z, hz, rfl⟩
      exact iterate_mapsTo_interior_perSet f (K + 1) (N + 1) (hCsub hz)
    exact hsub (mem_image_of_mem g hx)
  have hfix := newman_rigidity hN (n := n) hCo hCc isOpen_interior
      (by
        obtain ⟨z, hz⟩ := mem_closure_iff.1 hyN C hCo hyC
        exact ⟨z, hz.2, hz.1⟩)
      hgC hgc.continuousOn (m := K)
      (fun x hx => iterate_iterate_eq_of_mem_perSet f (N + 1) (interior_subset (hCsub hx)))
      (fun x hx => by have := interior_subset hx.1; exact this)
  have hCN : C ⊆ interior (perSet f (N + 1)) := interior_maximal (fun x hx => hfix x hx) hCo
  exact hCN hyC

theorem mapsTo_boundedSet (f : M ≃ₜ M) : MapsTo f (boundedSet f) (boundedSet f) := by
  intro x hx
  obtain ⟨N, hN⟩ := mem_iUnion.1 hx
  exact mem_iUnion.2 ⟨N, mapsTo_interior_of_mapsTo f (mapsTo_perSet f (N + 1)) hN⟩

/-- **Baire + Newman**: for a pointwise periodic homeomorphism, the period is bounded near every
point. -/
theorem boundedSet_eq_univ (hN : UniformNewman) {n : ℕ} [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (f : M ≃ₜ M) (hf : ∀ x, ∃ k, 0 < k ∧ f^[k] x = x) : boundedSet f = univ := by
  haveI : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  set O := boundedSet f
  by_contra hne
  obtain ⟨y₀, hy₀⟩ : (Oᶜ).Nonempty := by
    rw [nonempty_compl]; exact hne
  -- Baire on the closed set `Z = Oᶜ`.
  have hOo : IsOpen O := isOpen_iUnion fun _ => isOpen_interior
  set Z := Oᶜ
  have hZc : IsClosed Z := hOo.isClosed_compl
  haveI : LocallyCompactSpace Z := hZc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : Nonempty Z := ⟨⟨y₀, hy₀⟩⟩
  obtain ⟨k, hk⟩ := nonempty_interior_of_iUnion_of_closed
    (f := fun k : ℕ => (Subtype.val ⁻¹' perSet f (k + 1) : Set Z))
    (fun k => (isClosed_perSet f (k + 1)).preimage continuous_subtype_val)
    (by
      refine eq_univ_of_forall fun z => mem_iUnion.2 ?_
      obtain ⟨j, hj, hjz⟩ := hf z.1
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hj
      exact ⟨k, by simpa [perSet] using hjz⟩)
  obtain ⟨z, hz⟩ := hk
  obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.1 (isOpen_interior (s := (Subtype.val ⁻¹'
    perSet f (k + 1) : Set Z)))
  have hzV : z.1 ∈ V := by
    have : z ∈ Subtype.val ⁻¹' V := hV.symm ▸ hz
    exact this
  have hVZ : ∀ x ∈ V, x ∉ O → x ∈ perSet f (k + 1) := by
    intro x hxV hxO
    have : (⟨x, hxO⟩ : Z) ∈ interior (Subtype.val ⁻¹' perSet f (k + 1) : Set Z) := by
      rw [← hV]; exact hxV
    exact (interior_subset this : (⟨x, hxO⟩ : Z) ∈ (Subtype.val ⁻¹' perSet f (k + 1) : Set Z))
  -- the connected component `D` of `y` in `V' = int (O ∪ F_{k+1})`
  set y := z.1
  have hyO : y ∉ O := z.2
  set P := perSet f (k + 1)
  set V' := interior (O ∪ P)
  have hVV' : V ⊆ V' := interior_maximal (fun x hx => by
    by_cases hxO : x ∈ O
    · exact Or.inl hxO
    · exact Or.inr (hVZ x hx hxO)) hVo
  have hyV' : y ∈ V' := hVV' hzV
  set g := f^[k + 1]
  have hgc : Continuous g := f.continuous.iterate _
  have hgy : g y = y := hVZ y hzV hyO
  have hgV' : MapsTo g V' V' :=
    (mapsTo_interior_of_mapsTo f ((mapsTo_boundedSet f).union_union (mapsTo_perSet f _))).iterate _
  have hV'Z : ∀ x ∈ V', x ∉ O → g x = x := by
    intro x hx hxO
    rcases interior_subset hx with h | h
    · exact absurd h hxO
    · exact h
  set D := connectedComponentIn V' y
  have hDo : IsOpen D := isOpen_interior.connectedComponentIn
  have hDc : IsConnected D := isConnected_connectedComponentIn_iff.2 hyV'
  have hyD : y ∈ D := mem_connectedComponentIn hyV'
  have hDsub : D ⊆ V' := connectedComponentIn_subset _ _
  have hgD : MapsTo g D D := by
    intro x hx
    have hsub : g '' D ⊆ D :=
      (hDc.isPreconnected.image g hgc.continuousOn).subset_connectedComponentIn
        ⟨y, hyD, hgy⟩ (by rintro _ ⟨w, hw, rfl⟩; exact hgV' (hDsub hw))
    exact hsub (mem_image_of_mem g hx)
  -- some point of `D ∩ O` is moved by `g`
  obtain ⟨w, hwD, hwO, hgw⟩ : ∃ w ∈ D, w ∈ O ∧ g w ≠ w := by
    by_contra hcon
    push Not at hcon
    have hDP : D ⊆ interior P := interior_maximal (fun x hx => by
      by_cases hxO : x ∈ O
      · exact hcon x hx hxO
      · exact hV'Z x (hDsub hx) hxO) hDo
    exact hyO (interior_perSet_subset_boundedSet f (Nat.succ_pos k) (hDP hyD))
  obtain ⟨m, hwm⟩ := mem_iUnion.1 hwO
  set Ω := D ∩ interior (perSet f (m + 1))
  have hΩo : IsOpen Ω := hDo.inter isOpen_interior
  have hwΩ : w ∈ Ω := ⟨hwD, hwm⟩
  have hgΩ : MapsTo g Ω Ω := fun x hx =>
    ⟨hgD hx.1, iterate_mapsTo_interior_perSet f (m + 1) (k + 1) hx.2⟩
  have hΩper : ∀ x ∈ Ω, g^[m + 1] x = x := fun x hx =>
    iterate_iterate_eq_of_mem_perSet f (k + 1) (interior_subset hx.2)
  -- on the frontier of `Ω` inside `D`, `g` is the identity (local closedness)
  have hfront : ∀ x ∈ D, x ∈ closure Ω → x ∉ Ω → g x = x := by
    intro x hxD hxcl hxΩ
    by_cases hxO : x ∈ O
    · obtain ⟨K, hK⟩ := mem_iUnion.1 hxO
      have := mem_interior_perSet_of_mem_closure hN (n := n) f hK
        (closure_mono inter_subset_right hxcl)
      exact absurd ⟨hxD, this⟩ hxΩ
    · exact hV'Z x (hDsub hxD) hxO
  -- the periodic homeomorphism `h` of `D`: `g` on `Ω`, the identity elsewhere
  classical
  set h : M → M := Ω.piecewise g id
  have hhΩ : ∀ x ∈ Ω, h x = g x := fun x hx => Set.piecewise_eq_of_mem _ _ _ hx
  have hhnΩ : ∀ x ∉ Ω, h x = x := fun x hx => Set.piecewise_eq_of_notMem _ _ _ hx
  have hhc : ContinuousOn h D := by
    refine ContinuousOn.piecewise (fun x hx => ?_) hgc.continuousOn continuousOn_id
    rw [hΩo.frontier_eq] at hx
    exact hfront x hx.1 hx.2.1 hx.2.2
  have hhD : MapsTo h D D := by
    intro x hx
    by_cases hxΩ : x ∈ Ω
    · rw [hhΩ x hxΩ]; exact hgD hx
    · rw [hhnΩ x hxΩ]; exact hx
  have hhit : ∀ j : ℕ, ∀ x ∈ Ω, h^[j] x = g^[j] x := by
    intro j
    induction j with
    | zero => intro x _; rfl
    | succ j ih =>
      intro x hx
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih x hx,
        hhΩ _ (hgΩ.iterate j hx)]
  have hhper : ∀ x ∈ D, h^[m + 1] x = x := by
    intro x hx
    by_cases hxΩ : x ∈ Ω
    · rw [hhit _ x hxΩ]; exact hΩper x hxΩ
    · exact Function.iterate_fixed (hhnΩ x hxΩ) _
  by_cases hdense : D ⊆ closure Ω
  · -- then `g^[m+1] = id` on `D`, so `y ∈ O`
    have hDP : D ⊆ interior (perSet f ((k + 1) * (m + 1))) := interior_maximal (fun x hx => by
      change f^[(k + 1) * (m + 1)] x = x
      rw [Function.iterate_mul]
      by_cases hxΩ : x ∈ Ω
      · exact hΩper x hxΩ
      · exact Function.iterate_fixed (hfront x hx (hdense hx) hxΩ) _) hDo
    exact hyO (interior_perSet_subset_boundedSet f (Nat.mul_pos (Nat.succ_pos k)
      (Nat.succ_pos m)) (hDP hyD))
  · -- otherwise `h` is the identity on the open set `D \ closure Ω`: Newman's rigidity
    obtain ⟨x, hxD, hxcl⟩ := not_subset.1 hdense
    have hid := newman_rigidity hN (n := n) hDo hDc isClosed_closure.isOpen_compl
      ⟨x, hxcl, hxD⟩ hhD hhc hhper
      (fun x hx => hhnΩ x fun hxΩ => hx.1 (subset_closure hxΩ))
    exact hgw ((hhΩ w hwΩ).symm.trans (hid w hwD))

end Montgomery

/-- **Montgomery's theorem from Newman's theorem.** The uniform Newman theorem (used only for
finite cyclic groups, with zero displacement on an open set) implies that a pointwise periodic
homeomorphism of a connected manifold without boundary is periodic. -/
theorem pointwisePeriodicIsPeriodic_of_uniformNewman (h : UniformNewman) :
    PointwisePeriodicIsPeriodic := by
  intro n M _ _ _ _ _ f hf
  have hO := boundedSet_eq_univ h (n := n) f hf
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x₀⟩⟩
  · exact ⟨1, one_pos, fun x => (IsEmpty.false x).elim⟩
  obtain ⟨N, hN⟩ := mem_iUnion.1 (hO.symm ▸ mem_univ x₀ : x₀ ∈ boundedSet f)
  have hcl : IsClopen (interior (perSet f (N + 1))) := by
    refine ⟨closure_subset_iff_isClosed.1 fun y hy => ?_, isOpen_interior⟩
    obtain ⟨K, hK⟩ := mem_iUnion.1 (hO.symm ▸ mem_univ y : y ∈ boundedSet f)
    exact mem_interior_perSet_of_mem_closure h (n := n) f hK hy
  have huniv := hcl.eq_univ ⟨x₀, hN⟩
  refine ⟨N + 1, Nat.succ_pos N, fun x => ?_⟩
  have hx : x ∈ interior (perSet f (N + 1)) := huniv.symm ▸ mem_univ x
  exact (interior_subset hx : x ∈ perSet f (N + 1))

end HSFormal
