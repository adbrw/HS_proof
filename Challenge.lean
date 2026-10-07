import Mathlib

/-!
# Challenge: the Hilbert–Smith conjecture

**Hilbert–Smith conjecture.** *Let `G` be a locally compact Hausdorff topological group that acts
continuously and effectively (= faithfully) on a connected topological manifold `M`. Then `G` is a
Lie group.*

This file states it as the single theorem `hilbert_smith` below, with proof `sorry`. It imports
only Mathlib and has no auxiliary definitions, so the statement can be read on its own.

## Hypotheses

* `n : ℕ` is the dimension of the manifold.
* `M` is a **topological `n`-manifold without boundary**. It is a topological space that is
  - Hausdorff (`T2Space M`),
  - second countable (`SecondCountableTopology M`),
  - locally homeomorphic to `ℝⁿ` (`ChartedSpace (EuclideanSpace ℝ (Fin n)) M`): an atlas of
    charts, each a homeomorphism from an open subset of `M` onto an open subset of `ℝⁿ`, whose
    domains cover `M`. `EuclideanSpace ℝ (Fin n)` is `ℝⁿ` with its usual topology. **No
    smoothness is assumed**: the charts need not be compatible in any differentiable sense, so
    `M` is just a topological manifold;
  - connected and nonempty (`ConnectedSpace M`).
* `G` is a **locally compact Hausdorff second-countable topological group**: a group
  (`Group G`) with a topology (`TopologicalSpace G`) in which multiplication and inversion are
  continuous (`IsTopologicalGroup G`), and which is locally compact (`LocallyCompactSpace G`),
  Hausdorff (`T2Space G`) and second countable (`SecondCountableTopology G`). These last two lose
  no generality. Point stabilizers are closed (the action is continuous and `M` is Hausdorff) and,
  by effectiveness, intersect in `{1}`, so `G` is Hausdorff. An open σ-compact subgroup of `G`
  still acts effectively on `M`, is metrizable (its compact subsets embed in the homeomorphism
  group of `M`) and hence second countable, and if it is a Lie group then so is `G`.
* `G` **acts** on `M` (`MulAction G M`, written `g • x`, with `1 • x = x` and
  `(g * h) • x = g • (h • x)`):
  - continuously, as a map `G × M → M` (`ContinuousSMul G M`, joint continuity);
  - effectively (`FaithfulSMul G M`): if `g • x = h • x` for all `x : M`, then `g = h`.
    Equivalently, the only element of `G` that fixes every point of `M` is `1`.

## Conclusion

`G` is a **Lie group**: for some `d : ℕ` there is an atlas on `G`, modelled on `ℝᵈ`
(`EuclideanSpace ℝ (Fin d)`), that makes `G` a `C^∞` Lie group. In Lean, the conclusion is
```
∃ (d : ℕ) (_ : ChartedSpace (EuclideanSpace ℝ (Fin d)) G),
  LieGroup 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ G
```
* The charts are partial homeomorphisms (open subsets of `G` onto open subsets of `ℝᵈ`) for the
  **given** topology of `G`: a `ChartedSpace` structure is built on top of the existing
  `TopologicalSpace G` instance. So the Lie group structure induces the original topology.
* `LieGroup 𝓘(ℝ, ℝᵈ) ∞ G` says that the atlas is a `C^∞` atlas (`LieGroup` extends `ContMDiffMul`, which extends `IsManifold`)
  and that multiplication and inversion of `G` (the given `Group G` instance) are `C^∞` maps for
  it. `𝓘(ℝ, ℝᵈ)` is the trivial model (no boundary, no corners).
* `∞` (notation from `open scoped ContDiff`) is `((⊤ : ℕ∞) : WithTop ℕ∞)`, that is `C^∞`
  smoothness; real-analyticity would be written `ω`. (Smooth and analytic Lie groups are the
  same, so this choice does not matter mathematically.)

## Remarks

* **Every main hypothesis is needed.** If faithfulness is dropped, a non-Lie group such as the
  `p`-adic integers `ℤ_[p]` can act trivially. If connectedness is dropped, the Cantor group
  `(ℤ/2)^ℕ` acts effectively and continuously on a countable discrete set (a `0`-manifold) by
  flipping pairs of points. If local compactness is dropped, `ℚ` (with its usual topology) acts
  effectively by translations on `ℝ`. If continuity of the action is dropped, `ℤ_[p]` (which, as
  an abstract group, embeds in `ℝ`) acts effectively on `ℝ` by discontinuous translations.
* **Classical equivalent form.** By the Gleason–Montgomery–Zippin solution of Hilbert's fifth
  problem and work of Newman and others, the conjecture is equivalent to: *for every prime `p`,
  the additive group `ℤ_[p]` of `p`-adic integers does not act effectively (and continuously) on
  any connected topological manifold.*
* Universes: `M` and `G` live in `Type` (universe `0`). This loses no generality, since a
  second-countable Hausdorff manifold, and a second-countable Hausdorff group, have cardinality
  at most that of `ℝ`, so every instance in a higher universe is isomorphic to one in `Type`.
* Manifolds with boundary are not covered here; that case follows from this one by restricting
  the action to the interior of `M`, which is connected, dense, `G`-invariant and without
  boundary, and on which `G` still acts effectively.
-/

open scoped Manifold ContDiff

/-- **The Hilbert–Smith conjecture.** A locally compact Hausdorff second-countable topological
group `G` acting continuously and effectively on a connected, Hausdorff, second-countable
topological `n`-manifold `M` (without boundary) is a Lie group: for some `d`, `G` carries a
`C^∞` atlas modelled on `ℝᵈ`, whose charts are homeomorphisms for the given topology of `G`, for
which multiplication and inversion are `C^∞`. -/
theorem hilbert_smith
    -- the dimension of the manifold `M`
    (n : ℕ)
    -- `M` is a topological space ...
    (M : Type) [TopologicalSpace M]
    -- ... that is Hausdorff ...
    [T2Space M]
    -- ... second countable ...
    [SecondCountableTopology M]
    -- ... locally homeomorphic to `ℝⁿ` (topological charts only, no smoothness) ...
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    -- ... and connected (and nonempty).
    [ConnectedSpace M]
    -- `G` is a group ...
    (G : Type) [Group G]
    -- ... with a topology ...
    [TopologicalSpace G]
    -- ... making multiplication and inversion continuous (a topological group) ...
    [IsTopologicalGroup G]
    -- ... which is locally compact ...
    [LocallyCompactSpace G]
    -- ... Hausdorff ...
    [T2Space G]
    -- ... and second countable.
    [SecondCountableTopology G]
    -- `G` acts on `M` (`g • x`) ...
    [MulAction G M]
    -- ... continuously, as a map `G × M → M` ...
    [ContinuousSMul G M]
    -- ... and effectively: only `1 : G` fixes every point of `M`.
    [FaithfulSMul G M] :
    -- Conclusion: for some `d`, `G` has an atlas modelled on `ℝᵈ` (charts are homeomorphisms for
    -- the given topology of `G`) that makes `G` a `C^∞` Lie group.
    ∃ (d : ℕ) (_ : ChartedSpace (EuclideanSpace ℝ (Fin d)) G),
      LieGroup 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ G := by
  sorry
