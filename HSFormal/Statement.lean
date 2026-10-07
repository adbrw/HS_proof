import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Topology.Algebra.MulAction

/-!
# The Hilbert–Smith statement and the external inputs of Section 12

This file fixes the precise `Prop`-valued statements used at the top of the formalization of
`fullHS_final.md`.

* `HSFormal.HilbertSmith` and `HSFormal.HilbertSmithWithBoundary` are the consequence stated in
  Section 1 (L21) for manifolds without, respectively with, boundary.
* `HSFormal.PadicExclusion` and `HSFormal.PadicExclusionWithBoundary` are the proposed p-adic
  exclusion (L21).
* `HSFormal.NSSIsLie`, `HSFormal.CompactNonLieContainsPadic` and `HSFormal.UniformNewman` are the
  published transformation-group inputs of Section 1, item 4 (L37), each stated within (and if
  anything inside) its published range. They are used as explicit hypotheses, never as axioms.

Conventions (L15): actions are jointly continuous (`ContinuousSMul`/`ContinuousVAdd`), effective
means faithful (`FaithfulSMul`/`FaithfulVAdd`), and manifolds are Hausdorff, second countable,
connected and finite-dimensional. A topological manifold of dimension `n` without boundary is a
`ChartedSpace (EuclideanSpace ℝ (Fin n))` over the given topology (no smoothness is assumed).
All spaces and groups live in `Type`.
-/

open scoped Manifold ContDiff Topology

namespace HSFormal

/-- `G` is a Lie group: for some `d`, the *given* topology of `G` carries a charted-space structure
modelled on `ℝ^d` that makes `G` a `C^∞` Lie group. (`LieGroup` extends `IsManifold`, so the atlas
is smoothly compatible.) Since the charts are partial homeomorphisms for the existing topology, the
Lie structure induces the original topology. -/
def IsLieGroup (G : Type) [Group G] [TopologicalSpace G] : Prop :=
  ∃ (d : ℕ) (_ : ChartedSpace (EuclideanSpace ℝ (Fin d)) G),
    LieGroup 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ G

/-- No small subgroups: some neighbourhood of the identity contains no nontrivial subgroup. -/
def NoSmallSubgroups (G : Type) [Group G] [TopologicalSpace G] : Prop :=
  ∃ W ∈ 𝓝 (1 : G), ∀ S : Subgroup G, (S : Set G) ⊆ W → S = ⊥

/-- **Hilbert–Smith conjecture** (boundaryless form, L21): a second-countable locally compact
Hausdorff group acting continuously and effectively on a connected (Hausdorff, second-countable)
topological manifold without boundary is a Lie group. -/
def HilbertSmith : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ConnectedSpace M]
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [SecondCountableTopology G] [MulAction G M] [ContinuousSMul G M]
    [FaithfulSMul G M], IsLieGroup G

/-- **Hilbert–Smith conjecture** for manifolds with boundary of dimension `n + 1 ≥ 1`, modelled on
the closed half-space. (Boundaryless manifolds of dimension `n + 1` also admit such charts; the
connected manifolds of dimension `0` are points and are covered by `HilbertSmith`.) -/
def HilbertSmithWithBoundary : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [ConnectedSpace M]
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [SecondCountableTopology G] [MulAction G M] [ContinuousSMul G M]
    [FaithfulSMul G M], IsLieGroup G

/-- **p-adic exclusion** (proposed theorem, L21, boundaryless form): for every prime `p`, no
jointly continuous action of `ℤ_[p]` on a connected manifold without boundary is effective. -/
def PadicExclusion : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ConnectedSpace M]
    [AddAction ℤ_[p] M] [ContinuousVAdd ℤ_[p] M], ¬ FaithfulVAdd ℤ_[p] M

/-- **p-adic exclusion** for manifolds with boundary of dimension `n + 1 ≥ 1`. -/
def PadicExclusionWithBoundary : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [ConnectedSpace M]
    [AddAction ℤ_[p] M] [ContinuousVAdd ℤ_[p] M], ¬ FaithfulVAdd ℤ_[p] M

/-! ### Published inputs (Section 1, item 4) -/

/-- **[Gol10, §8]** (Gleason–Yamabe, Montgomery–Zippin): a locally compact Hausdorff group with no
small subgroups is a Lie group in its original topology. Second countability of `G` is added as a
(redundant for the published theorem) hypothesis; it holds in the only application. -/
def NSSIsLie : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [SecondCountableTopology G], NoSmallSubgroups G → IsLieGroup G

/-- **[Lee97, Thm 3.1]**: a compact (Hausdorff) group acting continuously and effectively on a
connected manifold without boundary, and not a Lie group, contains a topological subgroup
isomorphic to `ℤ_[p]` for some prime `p`. Since `ℤ_[p]` is compact and `C` is Hausdorff, a
continuous injective homomorphism is the same as a closed topological embedding. Second
countability of `C` (automatic for a compact group acting effectively on a second-countable
manifold) is added as a hypothesis. -/
def CompactNonLieContainsPadic : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ConnectedSpace M]
    (C : Type) [Group C] [TopologicalSpace C] [IsTopologicalGroup C] [CompactSpace C]
    [T2Space C] [SecondCountableTopology C] [MulAction C M] [ContinuousSMul C M]
    [FaithfulSMul C M], ¬ IsLieGroup C →
    ∃ (p : ℕ) (_ : Fact p.Prime) (ι : Multiplicative ℤ_[p] →* C),
      Continuous ι ∧ Function.Injective ι

/-- **[Pa18, Theorem (Newman)]**, uniform Newman theorem: for a nonempty open subset `U` of a
connected manifold `M` without boundary with a compatible metric, there is `ε > 0` such that every
compact Lie group acting on `M` with displacement `< ε` on `U` acts trivially. Pardon's statement
uses `≤ ε` and arbitrary (not necessarily effective) actions; this version additionally assumes
the action effective and the group second countable, so it is a special case. -/
def UniformNewman : Prop :=
  ∀ (n : ℕ) (M : Type) [MetricSpace M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ConnectedSpace M] (U : Set M),
    IsOpen U → U.Nonempty →
    ∃ ε > 0, ∀ (C : Type) [Group C] [TopologicalSpace C] [IsTopologicalGroup C]
      [CompactSpace C] [T2Space C] [SecondCountableTopology C] [MulAction C M]
      [ContinuousSMul C M] [FaithfulSMul C M], IsLieGroup C →
      (∀ c : C, ∀ x ∈ U, dist (c • x) x < ε) → ∀ (c : C) (x : M), c • x = x

end HSFormal
