import HSFormal.PadicStabilizers
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Section 7, first step: a free point of an effective p-adic action

`HSFormal.PointwisePeriodicIsPeriodic` is the published input [Rob75, Theorem 2] in the only case
used by the manuscript (L37, L458): the discrete group `ℤ`, i.e. Montgomery's theorem on pointwise
periodic homeomorphisms. It is an explicit hypothesis, never an axiom.

`HSFormal.exists_stabilizer_eq_bot` is the free-point claim of L458: an effective continuous
`ℤ_[p]`-action on a connected manifold without boundary has a point with trivial stabilizer.
-/

namespace HSFormal

/-- **[Mon37] = [Rob75, Theorem 2] for `Γ = ℤ`** (L37, L458).
D. Montgomery, *Pointwise periodic homeomorphisms*, Amer. J. Math. 59 (1937), 118–120: a
homeomorphism of a connected manifold without boundary all of whose points are periodic is
periodic. J. W. Roberts, *Pointwise finite families of mappings*, Canad. Math. Bull. 18 (1975),
Theorem 2, is the same statement for transformation groups with finite orbits (finite image
modulo the global kernel); for `ℤ` acting through `f` this is exactly the periodicity of `f`.
Manifolds are Hausdorff, second countable, connected, topological (no smoothness), without
boundary, of some dimension `n` (the case `n = 0` is trivial). -/
def PointwisePeriodicIsPeriodic : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ConnectedSpace M] (f : M ≃ₜ M),
    (∀ x, ∃ k, 0 < k ∧ f^[k] x = x) → ∃ m, 0 < m ∧ ∀ x, f^[m] x = x

variable {p : ℕ} [Fact p.Prime] {X : Type*} [AddAction ℤ_[p] X]

theorem iterate_vadd_one (k : ℕ) (x : X) :
    (fun y : X => (1 : ℤ_[p]) +ᵥ y)^[k] x = (k : ℤ_[p]) +ᵥ x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, vadd_vadd, Nat.cast_succ, add_comm]

/-- A nonzero point stabilizer contains a positive integer. -/
theorem exists_pos_nat_mem_stabilizer [TopologicalSpace X] [T2Space X] [ContinuousVAdd ℤ_[p] X]
    (x : X) (hx : AddAction.stabilizer ℤ_[p] x ≠ ⊥) :
    ∃ k : ℕ, 0 < k ∧ (k : ℤ_[p]) ∈ AddAction.stabilizer ℤ_[p] x := by
  obtain ⟨j, hj⟩ := padicClosedSubgroup_eq_power _ (padicStabilizer_isClosed x) hx
  refine ⟨p ^ j, pow_pos (Fact.out : p.Prime).pos j, ?_⟩
  rw [hj]
  change ((p ^ j : ℕ) : ℤ_[p]) ∈ (Ideal.span {(p : ℤ_[p]) ^ j} : Ideal ℤ_[p])
  rw [Nat.cast_pow]
  exact Ideal.mem_span_singleton_self _

/-- **Free point** (L458): an effective jointly continuous `ℤ_[p]`-action on a connected
manifold without boundary has a point with trivial stabilizer. If every stabilizer were nonzero,
each would be some `p^j ℤ_[p]`, so `1` would act by a pointwise periodic homeomorphism; by
Montgomery's theorem some `m > 0` would act trivially, and `(m : ℤ_[p]) ≠ 0`. -/
theorem exists_stabilizer_eq_bot (hMon : PointwisePeriodicIsPeriodic) {n : ℕ} {M : Type}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ConnectedSpace M]
    [AddAction ℤ_[p] M] [ContinuousVAdd ℤ_[p] M] [FaithfulVAdd ℤ_[p] M] :
    ∃ x : M, AddAction.stabilizer ℤ_[p] x = ⊥ := by
  by_contra hcon
  push Not at hcon
  have hper : ∀ x : M, ∃ k, 0 < k ∧ (Homeomorph.vadd (1 : ℤ_[p]) : M ≃ₜ M)^[k] x = x := by
    intro x
    obtain ⟨k, hk, hkx⟩ := exists_pos_nat_mem_stabilizer x (hcon x)
    exact ⟨k, hk, (iterate_vadd_one k x).trans hkx⟩
  obtain ⟨m, hm, hmx⟩ := hMon n M _ hper
  have hm0 : ((m : ℕ) : ℤ_[p]) = 0 := eq_of_vadd_eq_vadd (P := M) fun x =>
    ((iterate_vadd_one m x).symm.trans (hmx x)).trans (zero_vadd _ x).symm
  exact (Nat.cast_ne_zero.mpr hm.ne') hm0

end HSFormal
