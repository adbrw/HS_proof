import Mathlib
import HSFormal.HilbertSmithNegK

/-!
# Solution to `Challenge.lean`

The statement of `hilbert_smith` is copied verbatim from `Challenge.lean`. It is, by definition,
`HSFormal.HilbertSmith` (`HSFormal/Statement.lean`), which is proved as `HSFormal.hilbertSmith` in
`HSFormal/HilbertSmithNegK.lean`.

`import Mathlib` is not needed by the proof. It makes the imports of this file a superset of those
of `Challenge.lean`, which SafeVerify requires.
-/

open scoped Manifold ContDiff

theorem hilbert_smith
    (n : ℕ)
    (M : Type) [TopologicalSpace M]
    [T2Space M]
    [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ConnectedSpace M]
    (G : Type) [Group G]
    [TopologicalSpace G]
    [IsTopologicalGroup G]
    [LocallyCompactSpace G]
    [T2Space G]
    [SecondCountableTopology G]
    [MulAction G M]
    [ContinuousSMul G M]
    [FaithfulSMul G M] :
    ∃ (d : ℕ) (_ : ChartedSpace (EuclideanSpace ℝ (Fin d)) G),
      LieGroup 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ G :=
  HSFormal.hilbertSmith n M G
