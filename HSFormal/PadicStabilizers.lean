import HSFormal.PadicSubgroups

/-!
# Stabilizers of points moved by a p-adic tail

Power subgroups of `ℤ_[p]` are ordered by reversed exponents. Together with the
closed-subgroup classification, this shows that a closed subgroup that does not
contain `p^j ℤ_[p]` lies in `p^(j+1) ℤ_[p]`.

For a continuous action on a Hausdorff space, point stabilizers are closed.
Consequently, a point outside the fixed-point set of the `j`th tail has its
stabilizer inside the next tail. This conclusion uses actual nonfixedness of
the point; it does not assert existence of such points or exclude faithful
p-adic actions on manifolds.
-/

namespace HSFormal

open Topology

section SubgroupOrder

variable {p : ℕ} [Fact p.Prime]

/-- Power subgroups are ordered by reversed exponents. -/
theorem padicPowerSubgroup_le_iff (m n : ℕ) :
    padicPowerSubgroup p m ≤ padicPowerSubgroup p n ↔ n ≤ m := by
  simp only [padicPowerSubgroup, Submodule.toAddSubgroup_le,
    Ideal.span_singleton_le_span_singleton]
  exact pow_dvd_pow_iff (NeZero.ne _) PadicInt.irreducible_p.not_isUnit

/-- A closed subgroup that fails to contain one tail lies inside the next tail. -/
theorem padicClosedSubgroup_le_nextPower_of_not_power_le (H : AddSubgroup ℤ_[p])
    (hH : IsClosed (H : Set ℤ_[p])) (j : ℕ) (hnot : ¬ padicPowerSubgroup p j ≤ H) :
    H ≤ padicPowerSubgroup p (j + 1) := by
  by_cases hzero : H = ⊥
  · rw [hzero]
    exact bot_le
  obtain ⟨n, rfl⟩ := padicClosedSubgroup_eq_power H hH hzero
  have hn : j < n := lt_of_not_ge (fun hnj =>
    hnot ((padicPowerSubgroup_le_iff j n).mpr hnj))
  exact (padicPowerSubgroup_le_iff n (j + 1)).mpr (Nat.succ_le_of_lt hn)

end SubgroupOrder

section Stabilizers

variable {p : ℕ} [Fact p.Prime] {X : Type*} [TopologicalSpace X]
  [T2Space X] [AddAction ℤ_[p] X] [ContinuousVAdd ℤ_[p] X]

/-- Point stabilizers of a continuous p-adic action on a Hausdorff space are closed. -/
theorem padicStabilizer_isClosed (x : X) :
    IsClosed (AddAction.stabilizer ℤ_[p] x : Set ℤ_[p]) := by
  change IsClosed {a : ℤ_[p] | a +ᵥ x = x}
  exact isClosed_eq (continuous_id.vadd continuous_const) continuous_const

/-- A point not fixed by the whole `j`th tail has stabilizer contained in the next tail. -/
theorem padicStabilizer_le_nextPower_of_not_fixed (j : ℕ) (x : X)
    (hnot : x ∉ AddAction.fixedPoints (padicPowerSubgroup p j) X) :
    AddAction.stabilizer ℤ_[p] x ≤ padicPowerSubgroup p (j + 1) := by
  apply padicClosedSubgroup_le_nextPower_of_not_power_le _ (padicStabilizer_isClosed x) j
  intro hle
  apply hnot
  exact AddAction.mem_fixedPoints.mpr (fun a =>
    AddAction.mem_stabilizer_iff.mp (hle a.property))

end Stabilizers

end HSFormal
