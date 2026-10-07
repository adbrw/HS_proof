import HSFormal.TopologicalReduction
import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Uniform displacement of actual p-adic power subgroups

The principal ideals `p^n ℤ_[p]` are open additive subgroups and shrink to zero.
Their displacement therefore tends uniformly to zero on every compact set for a
jointly continuous action. This is the actual p-adic specialization used in Section 7
of `fullHS_final.md`, without an assumed shrinking-family premise.
-/

open Set Filter
open scoped Topology

namespace HSFormal

section PadicDisplacement

/-- The principal ideal representing `p^n ℤ_[p]` is an open additive subgroup. -/
theorem padic_power_subgroup_isOpen (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) :
    IsOpen (Ideal.span {(p : ℤ_[p]) ^ n} : Set ℤ_[p]) := by
  have hset : (Ideal.span {(p : ℤ_[p]) ^ n} : Set ℤ_[p]) =
      {g : ℤ_[p] | ‖g‖ < (p : ℝ) ^ (-(n : ℤ) + 1)} := by
    ext g
    exact (PadicInt.norm_le_pow_iff_mem_span_pow g n).symm.trans
      (PadicInt.norm_le_pow_iff_norm_lt_pow_add_one g (-(n : ℤ)))
  rw [hset]
  exact isOpen_lt continuous_norm continuous_const

/-- The actual subgroups `p^n ℤ_[p]`, represented by their principal ideals, eventually
lie in every zero neighborhood. This uses the compatible p-adic norm, not a separate
shrinking-subgroups hypothesis. -/
theorem padic_power_subgroups_shrink (p : ℕ) [Fact (Nat.Prime p)]
    (V : Set ℤ_[p]) (hV : V ∈ 𝓝 (0 : ℤ_[p])) :
    ∀ᶠ n : ℕ in atTop, (Ideal.span {(p : ℤ_[p]) ^ n} : Set ℤ_[p]) ⊆ V := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨N, hN⟩ := PadicInt.exists_pow_neg_lt p hε
  refine eventually_atTop.2 ⟨N, fun n hn g hg => hball ?_⟩
  have hp : 1 ≤ (p : ℝ) := by
    exact_mod_cast (Nat.Prime.one_lt (Fact.out : Nat.Prime p)).le
  have hpow : (p : ℝ) ^ (-(n : ℤ)) ≤ (p : ℝ) ^ (-(N : ℤ)) :=
    zpow_le_zpow_right₀ hp (neg_le_neg (Int.ofNat_le.mpr hn))
  have hnorm : ‖g‖ ≤ (p : ℝ) ^ (-(n : ℤ)) :=
    (PadicInt.norm_le_pow_iff_mem_span_pow g n).mpr hg
  simpa only [Metric.mem_ball, dist_zero_right] using
    (hnorm.trans hpow).trans_lt hN

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {X : Type*} [MetricSpace X] [AddAction ℤ_[p] X] [ContinuousVAdd ℤ_[p] X]

/-- The displacements of the actual open p-adic subgroups tend uniformly to zero on
each compact set, as used in the choice of `H` and `K_i` in Section 7. -/
theorem eventually_padic_power_uniform_displacement {K : Set X} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ g ∈ (Ideal.span {(p : ℤ_[p]) ^ n} : Set ℤ_[p]),
      ∀ x ∈ K, dist (g +ᵥ x) x < ε := by
  exact eventually_uniform_vadd_displacement_of_shrinking
    (fun n => (Ideal.span {(p : ℤ_[p]) ^ n} : Set ℤ_[p]))
    (padic_power_subgroups_shrink p) hK hε

/-- Any sequence or net of depths tending to infinity has uniformly vanishing
compact-set displacement. The depths may be chosen after the fixed geometric data. -/
theorem eventually_padic_depth_uniform_displacement {I : Type*} {l : Filter I}
    (depth : I → ℕ) (hdepth : Tendsto depth l atTop)
    {K : Set X} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ g ∈ (Ideal.span {(p : ℤ_[p]) ^ depth i} : Set ℤ_[p]),
      ∀ x ∈ K, dist (g +ᵥ x) x < ε := by
  exact hdepth.eventually (eventually_padic_power_uniform_displacement (p := p) hK hε)

end PadicDisplacement

end HSFormal
