import Mathlib.Algebra.Group.Action.End
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.Algebra.MulAction

/-!
# Closed additive subgroups of the p-adic integers

Integer density makes a closed additive subgroup of `ℤ_[p]` stable under every
`ℤ_[p]`-scalar. It is therefore an ideal, and the discrete valuation ring
classification identifies each nonzero such subgroup with `p^n ℤ_[p]`.

The action-kernel results below are conditional on a nontrivial kernel. They do
not establish that a p-adic action on a manifold has a nontrivial kernel.
-/

namespace HSFormal

open Topology

/-- The additive subgroup `p^n ℤ_[p]`. -/
noncomputable def padicPowerSubgroup (p : ℕ) [Fact p.Prime] (n : ℕ) : AddSubgroup ℤ_[p] :=
  (Ideal.span {(p : ℤ_[p]) ^ n} : Ideal ℤ_[p]).toAddSubgroup

section ClosedSubgroups

variable {p : ℕ} [Fact p.Prime]

/-- Closedness and integer density extend the integer scalar action to every p-adic scalar. -/
theorem padicClosedSubgroup_mul_mem (H : AddSubgroup ℤ_[p])
    (hH : IsClosed (H : Set ℤ_[p])) {x : ℤ_[p]} (hx : x ∈ H) (a : ℤ_[p]) : a * x ∈ H := by
  refine PadicInt.denseRange_intCast.induction_on a ?_ ?_
  · exact hH.preimage (continuous_id.mul continuous_const)
  · intro n
    simpa only [zsmul_eq_mul] using H.zsmul_mem hx n

/-- The ideal whose carrier is the given closed additive subgroup. -/
def padicClosedSubgroupIdeal (H : AddSubgroup ℤ_[p]) (hH : IsClosed (H : Set ℤ_[p])) :
    Ideal ℤ_[p] where
  carrier := H
  zero_mem' := H.zero_mem
  add_mem' := fun hx hy => H.add_mem hx hy
  smul_mem' := fun a _ hx => padicClosedSubgroup_mul_mem H hH hx a

@[simp]
theorem padicClosedSubgroupIdeal_toAddSubgroup (H : AddSubgroup ℤ_[p])
    (hH : IsClosed (H : Set ℤ_[p])) : (padicClosedSubgroupIdeal H hH).toAddSubgroup = H := rfl

/-- Every nontrivial closed additive subgroup of `ℤ_[p]` is a power of `p`. -/
theorem padicClosedSubgroup_eq_power (H : AddSubgroup ℤ_[p])
    (hH : IsClosed (H : Set ℤ_[p])) (hne : H ≠ ⊥) :
    ∃ n : ℕ, H = padicPowerSubgroup p n := by
  have hI : padicClosedSubgroupIdeal H hH ≠ ⊥ := by
    intro h
    apply hne
    exact (padicClosedSubgroupIdeal_toAddSubgroup H hH).symm.trans
      (congrArg (fun I : Ideal ℤ_[p] => I.toAddSubgroup) h)
  obtain ⟨n, hn⟩ := PadicInt.ideal_eq_span_pow_p hI
  refine ⟨n, ?_⟩
  change H = (Ideal.span {(p : ℤ_[p]) ^ n} : Ideal ℤ_[p]).toAddSubgroup
  rw [← hn, padicClosedSubgroupIdeal_toAddSubgroup]

/-- The full closed-subgroup classification, including the zero subgroup. -/
theorem padicClosedSubgroup_eq_bot_or_power (H : AddSubgroup ℤ_[p])
    (hH : IsClosed (H : Set ℤ_[p])) : H = ⊥ ∨ ∃ n : ℕ, H = padicPowerSubgroup p n := by
  by_cases h : H = ⊥
  · exact Or.inl h
  · exact Or.inr (padicClosedSubgroup_eq_power H hH h)

/-- The power subgroup is a closed ball for the usual p-adic metric. -/
theorem padicPowerSubgroup_eq_closedBall (n : ℕ) :
    (padicPowerSubgroup p n : Set ℤ_[p]) =
      Metric.closedBall (0 : ℤ_[p]) ((p : ℝ) ^ (-(n : ℤ))) := by
  ext x
  change x ∈ (Ideal.span {(p : ℤ_[p]) ^ n} : Ideal ℤ_[p]) ↔
    x ∈ Metric.closedBall (0 : ℤ_[p]) ((p : ℝ) ^ (-(n : ℤ)))
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (PadicInt.norm_le_pow_iff_mem_span_pow x n).symm

/-- Every power subgroup is open; ultrametric closed balls of positive radius are open. -/
theorem padicPowerSubgroup_isOpen (n : ℕ) : IsOpen (padicPowerSubgroup p n : Set ℤ_[p]) := by
  rw [padicPowerSubgroup_eq_closedBall]
  exact IsUltrametricDist.isOpen_closedBall _
    (zpow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))

/-- Every power subgroup is closed. -/
theorem padicPowerSubgroup_isClosed (n : ℕ) : IsClosed (padicPowerSubgroup p n : Set ℤ_[p]) := by
  rw [padicPowerSubgroup_eq_closedBall]
  exact Metric.isClosed_closedBall

/-- A nontrivial closed additive subgroup of `ℤ_[p]` is open. -/
theorem padicClosedSubgroup_isOpen (H : AddSubgroup ℤ_[p])
    (hH : IsClosed (H : Set ℤ_[p])) (hne : H ≠ ⊥) : IsOpen (H : Set ℤ_[p]) := by
  obtain ⟨n, rfl⟩ := padicClosedSubgroup_eq_power H hH hne
  exact padicPowerSubgroup_isOpen n

/-- Every proper closed additive subgroup lies in `p ℤ_[p]`. -/
theorem padicClosedSubgroup_le_firstPower (H : AddSubgroup ℤ_[p])
    (hH : IsClosed (H : Set ℤ_[p])) (hproper : H ≠ ⊤) : H ≤ padicPowerSubgroup p 1 := by
  by_cases hzero : H = ⊥
  · rw [hzero]
    exact bot_le
  obtain ⟨n, hn⟩ := padicClosedSubgroup_eq_power H hH hzero
  cases n with
  | zero =>
    exfalso
    apply hproper
    rw [hn]
    ext x
    simp [padicPowerSubgroup]
  | succ n =>
    rw [hn]
    intro x hx
    have hI : (Ideal.span {(p : ℤ_[p]) ^ (n + 1)} : Ideal ℤ_[p]) ≤
        Ideal.span {(p : ℤ_[p])} :=
      Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self _ (Nat.succ_ne_zero n))
    have hxI : x ∈ (Ideal.span {(p : ℤ_[p]) ^ (n + 1)} : Ideal ℤ_[p]) := hx
    simpa only [padicPowerSubgroup, Submodule.mem_toAddSubgroup, pow_one] using hI hxI

end ClosedSubgroups

section ActionKernel

variable {p : ℕ} [Fact p.Prime] {X : Type*} [AddAction ℤ_[p] X]

/-- The actual global kernel of a p-adic additive action. -/
noncomputable def padicActionKernel : AddSubgroup ℤ_[p] := (AddAction.toPermHom ℤ_[p] X).ker

@[simp]
theorem mem_padicActionKernel (a : ℤ_[p]) :
    a ∈ padicActionKernel (p := p) (X := X) ↔ ∀ x : X, a +ᵥ x = x := by
  change AddAction.toPerm a = (1 : Equiv.Perm X) ↔ _
  exact Equiv.ext_iff

variable [TopologicalSpace X] [T2Space X] [ContinuousVAdd ℤ_[p] X]

/-- The kernel of a continuous action on a Hausdorff space is closed. -/
theorem padicActionKernel_isClosed : IsClosed (padicActionKernel (p := p) (X := X) : Set ℤ_[p]) := by
  have hset : (padicActionKernel (p := p) (X := X) : Set ℤ_[p]) =
      ⋂ x : X, {a : ℤ_[p] | a +ᵥ x = x} := by
    ext a
    change (a ∈ padicActionKernel (p := p) (X := X)) ↔ _
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, mem_padicActionKernel]
  rw [hset]
  exact isClosed_iInter (fun x =>
    isClosed_eq (continuous_id.vadd continuous_const) continuous_const)

/-- If the global kernel is nontrivial, it is exactly one open power subgroup. -/
theorem padicActionKernel_eq_power (hne : padicActionKernel (p := p) (X := X) ≠ ⊥) :
    ∃ n : ℕ, padicActionKernel (p := p) (X := X) = padicPowerSubgroup p n :=
  padicClosedSubgroup_eq_power _ padicActionKernel_isClosed hne

/-- If the global kernel is nontrivial, it is open. -/
theorem padicActionKernel_isOpen (hne : padicActionKernel (p := p) (X := X) ≠ ⊥) :
    IsOpen (padicActionKernel (p := p) (X := X) : Set ℤ_[p]) :=
  padicClosedSubgroup_isOpen _ padicActionKernel_isClosed hne

end ActionKernel

end HSFormal
