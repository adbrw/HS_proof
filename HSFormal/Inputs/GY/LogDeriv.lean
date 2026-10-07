import HSFormal.Inputs.GY.Adjoint
import TauCeti.Analysis.Calculus.ParametricIntegral

/-!
# The derivative of `μ (-W, W + K)` at `K = 0` (blueprint C2, §5 H2 steps 2–4)

For `S : LocalExpStructure G E` (`G` a topological group, `E` finite-dimensional) let
`μ X Y = S.mu X Y = log (exp X * exp Y)` and

  `Gop W = ∫₀¹ exp (-t • ad W) dt  : E →L[ℝ] E`.

* `contDiff_Gop : ContDiff ℝ ∞ S.Gop` and `Gop_zero : S.Gop 0 = 1`.
* `tendsto_riemannSum`: Riemann sums of a continuous function on `[0, 1]` converge to its integral.
* `prod_estimate`: `log (exp Z₁ ⋯ exp Z_k) = Σ Zᵢ + O((Σ ‖Zᵢ‖)²)` (from `c11`, by induction).
* `exists_norm_mu_neg_add_sub_le` (formula (22)): `‖μ (-W, W + K) - Gop W K‖ ≤ C ‖K‖²` for small
  `K`, and `hasFDerivAt_mu_neg_add`: `K ↦ μ (-W, W + K)` has derivative `Gop W` at `0`.

Proof of (22) (blueprint H2 step 4): with `a = exp (W/m)` and `b = exp (K/m)`,
`exp (-W) (a b)^m = a^{-m} (a b)^m = Π_{j = m-1}^{0} a^{-j} b a^{j}` (`inv_pow_mul_mul_pow`), and by
`Ad_spec` and the Hadamard formula `a^{-j} b a^j = exp (Z_j)` with
`Z_j = m⁻¹ • exp (-(j/m) • ad W) K`. The product estimate bounds
`log (exp (-W) (a b)^m) - Σ_j Z_j` by `A (α ‖K‖)²`; as `m → ∞` the left factor converges to
`μ (-W, W + K)` (Trotter, `c11` and continuity of `log` on the chart target) and the Riemann sums
`Σ_j Z_j` converge to `Gop W K`.
-/

noncomputable section

namespace HSFormal.GY

open Filter Topology MeasureTheory
open scoped ContDiff

/-! ### Riemann sums -/

/-- Riemann sums of a continuous function on `[0, 1]` converge to its integral. -/
theorem tendsto_riemannSum {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {F : ℝ → V} (hF : Continuous F) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ j ∈ Finset.range n, F (j / n)) atTop
      (𝓝 (∫ t in Set.Icc (0 : ℝ) 1, F t)) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨η, hη, hunif⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hF.continuousOn) (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := exists_nat_gt η⁻¹
  refine ⟨N, fun n hn => ?_⟩
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le ((inv_pos.2 hη).trans hN) hNn
  have h1n : (n : ℝ)⁻¹ < η := by
    rw [inv_lt_comm₀ hn0 hη]; exact lt_of_lt_of_le hN hNn
  set a : ℕ → ℝ := fun j => j / n with ha_def
  have hint : ∀ k < n, IntervalIntegrable F volume (a k) (a (k + 1)) :=
    fun k _ => hF.intervalIntegrable _ _
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  have ha0 : a 0 = 0 := by simp [a]
  have han : a n = 1 := by simp [a, div_self hn0.ne']
  rw [ha0, han] at hsum
  rw [← hsum, dist_eq_norm, Finset.smul_sum, ← Finset.sum_sub_distrib]
  have hlen : ∀ j : ℕ, a (j + 1) - a j = (n : ℝ)⁻¹ := fun j => by
    simp only [a]; push_cast; field_simp; ring
  calc ‖∑ j ∈ Finset.range n, ((n : ℝ)⁻¹ • F (j / n) - ∫ x in a j..a (j + 1), F x)‖
      ≤ ∑ j ∈ Finset.range n, ‖(n : ℝ)⁻¹ • F (j / n) - ∫ x in a j..a (j + 1), F x‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range n, ε / 2 * (n : ℝ)⁻¹ := by
        gcongr with j hj
        have hj' : (j : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.1 hj
        have hconst : (n : ℝ)⁻¹ • F (j / n) = ∫ _ in a j..a (j + 1), F (j / n) := by
          rw [intervalIntegral.integral_const, hlen]
        rw [hconst, ← intervalIntegral.integral_sub intervalIntegrable_const
          (hF.intervalIntegrable _ _)]
        have hle : a j ≤ a (j + 1) := by linarith [hlen j, inv_pos.2 hn0]
        calc _ ≤ ε / 2 * |a (j + 1) - a j| := by
              refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
              rw [Set.uIoc_of_le hle] at hx
              obtain ⟨hx1, hx2⟩ := hx
              have hx1' : (j : ℝ) / n < x := hx1
              have hx2' : x ≤ ((j + 1 : ℕ) : ℝ) / n := hx2
              have hj0 : (0 : ℝ) ≤ j / n := by positivity
              have hjx : x - j / n ≤ (n : ℝ)⁻¹ := by
                have := hlen j; simp only [a] at this; linarith
              have hx1n : x ≤ 1 := by
                refine hx2'.trans ?_
                rw [div_le_one hn0]; push_cast; exact hj'
              rw [← dist_eq_norm]
              refine (hunif (j / n) ⟨hj0, ?_⟩ x ⟨by linarith, hx1n⟩ ?_).le
              · linarith
              · rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
          _ = ε / 2 * (n : ℝ)⁻¹ := by rw [hlen, abs_of_pos (inv_pos.2 hn0)]
    _ = ε / 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
    _ < ε := half_lt_self hε

/-- `a^{-n} (a b)^n = Π_{j = n-1}^{0} a^{-j} b a^j` in any group. -/
theorem inv_pow_mul_mul_pow {M : Type*} [Group M] (a b : M) (n : ℕ) :
    a⁻¹ ^ n * (a * b) ^ n = ((List.range n).reverse.map fun j => a⁻¹ ^ j * b * a ^ j).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.map_cons, List.prod_cons, ← ih, pow_succ, pow_succ' (a * b)]
    generalize (a * b) ^ n = c
    rw [inv_pow]
    group

theorem norm_list_sum_le' {V : Type*} [SeminormedAddCommGroup V] (l : List V) :
    ‖l.sum‖ ≤ (l.map (‖·‖)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.sum_cons, List.map_cons]
    exact (norm_add_le _ _).trans (by linarith)

theorem list_sum_map_range {V : Type*} [AddCommMonoid V] (f : ℕ → V) (n : ℕ) :
    ((List.range n).reverse.map f).sum = ∑ j ∈ Finset.range n, f j := by
  rw [List.map_reverse, List.sum_reverse]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

namespace LocalExpStructure

variable {G : Type*} [Group G] [TopologicalSpace G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (S : LocalExpStructure G E)

/-! ### The product estimate (blueprint H2 step 3) -/

/-- **Product estimate**: `log (exp Z₁ ⋯ exp Z_k) = Σ Zᵢ + O((Σ ‖Zᵢ‖)²)` for `Σ ‖Zᵢ‖ ≤ ε`. -/
theorem prod_estimate : ∃ ε > 0, ∃ A ≥ 0, ∀ l : List E, (l.map (‖·‖)).sum ≤ ε →
    (l.map S.exp).prod ∈ S.chart.target ∧
      ‖S.chart.symm (l.map S.exp).prod - l.sum‖ ≤ A * (l.map (‖·‖)).sum ^ 2 := by
  obtain ⟨δ, hδ, K, hK⟩ := S.c11
  set A : ℝ := 2 * (|K| + 1) with hA
  have hA0 : 0 < A := by positivity
  refine ⟨min (δ / 4) A⁻¹, by positivity, A, hA0.le, fun l => ?_⟩
  induction l with
  | nil => intro _; simp [S.one_mem_target]
  | cons Z l ih =>
    intro hσ
    simp only [List.map_cons, List.sum_cons, List.prod_cons] at hσ ⊢
    set σ' := (l.map (‖·‖)).sum with hσ'_def
    have hσ'0 : 0 ≤ σ' := List.sum_nonneg (by simp)
    have hZ0 := norm_nonneg Z
    have hσ' : σ' ≤ min (δ / 4) A⁻¹ := by linarith
    have hσ'δ : σ' ≤ δ / 4 := hσ'.trans (min_le_left _ _)
    have hσ'A : A * σ' ≤ 1 :=
      calc A * σ' ≤ A * A⁻¹ := by gcongr; exact hσ'.trans (min_le_right _ _)
        _ = 1 := mul_inv_cancel₀ hA0.ne'
    obtain ⟨hmem, hbd⟩ := ih hσ'
    set S' := S.chart.symm (l.map S.exp).prod with hS'_def
    have hS' : ‖S'‖ ≤ 2 * σ' := by
      have h1 : ‖S'‖ ≤ ‖S' - l.sum‖ + ‖l.sum‖ := by
        simpa using norm_add_le (S' - l.sum) l.sum
      have h2 := norm_list_sum_le' l
      have h3 : A * σ' ^ 2 ≤ σ' := by nlinarith
      linarith
    have hexpS' : S.exp S' = (l.map S.exp).prod := S.exp_symm hmem
    have hZδ : ‖Z‖ < δ := by
      have : ‖Z‖ ≤ δ / 4 := by linarith [min_le_left (δ / 4) A⁻¹]
      linarith
    have hS'δ : ‖S'‖ < δ := by linarith
    obtain ⟨h1, h2⟩ := hK Z S' hZδ hS'δ
    rw [← hexpS']
    refine ⟨h1, ?_⟩
    have h3 : ‖S.chart.symm (S.exp Z * S.exp S') - (Z + l.sum)‖ ≤
        ‖S.chart.symm (S.exp Z * S.exp S') - (Z + S')‖ + ‖S' - l.sum‖ := by
      rw [show S.chart.symm (S.exp Z * S.exp S') - (Z + l.sum) =
        (S.chart.symm (S.exp Z * S.exp S') - (Z + S')) + (S' - l.sum) by abel]
      exact norm_add_le _ _
    have h4 : K * ‖Z‖ * ‖S'‖ ≤ (|K| + 1) * ‖Z‖ * (2 * σ') := by
      have := le_abs_self K
      have := mul_nonneg hZ0 (norm_nonneg S')
      calc K * ‖Z‖ * ‖S'‖ ≤ (|K| + 1) * ‖Z‖ * ‖S'‖ := by
            rw [mul_assoc, mul_assoc]; gcongr; linarith
        _ ≤ (|K| + 1) * ‖Z‖ * (2 * σ') := by gcongr
    calc ‖S.chart.symm (S.exp Z * S.exp S') - (Z + l.sum)‖
        ≤ (|K| + 1) * ‖Z‖ * (2 * σ') + A * σ' ^ 2 := by linarith
      _ ≤ A * (‖Z‖ + σ') ^ 2 := by
          have hc : 0 ≤ |K| + 1 := by positivity
          rw [hA]
          nlinarith [mul_nonneg hc (mul_nonneg hZ0 hZ0), mul_nonneg hc (mul_nonneg hZ0 hσ'0)]

theorem mu_neg_self (W : E) : S.mu (-W) W = 0 := by
  rw [mu_def, exp_neg, inv_mul_cancel, symm_one]

/-! ### The operator `Gop W = ∫₀¹ exp (-t • ad W) dt` (blueprint H2 step 2) -/

variable [IsTopologicalGroup G] [FiniteDimensional ℝ E]

attribute [local instance] TauCeti.normedAlgebraRatOfReal

local instance completeSpaceOfFD' : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- `Gop W = ∫₀¹ exp (-t • ad W) dt`, the derivative of `K ↦ μ (-W, W + K)` at `0`. -/
def Gop (W : E) : E →L[ℝ] E := ∫ t in Set.Icc (0 : ℝ) 1, NormedSpace.exp ((-t) • S.ad W)

theorem continuous_exp_neg_smul_ad (W : E) :
    Continuous fun t : ℝ => NormedSpace.exp ((-t) • S.ad W) :=
  NormedSpace.exp_continuous.comp (continuous_neg.smul continuous_const)

theorem contDiff_Gop : ContDiff ℝ ∞ S.Gop := by
  have hexp : ContDiff ℝ ∞ (NormedSpace.exp : (E →L[ℝ] E) → (E →L[ℝ] E)) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic x).contDiffAt
  have h : ContDiff ℝ ∞
      (Function.uncurry fun (W : E) (t : ℝ) => NormedSpace.exp ((-t) • S.ad W)) :=
    hexp.comp ((contDiff_snd.neg).smul (S.ad.contDiff.comp contDiff_fst))
  exact contDiff_integral_Icc_of_contDiff ⊤ _ h

theorem continuous_Gop : Continuous S.Gop := S.contDiff_Gop.continuous

theorem Gop_zero : S.Gop 0 = 1 := by
  simp [Gop]

/-! ### Formula (22) (blueprint H2 step 4) -/

/-- **Formula (22)**: `‖μ (-W, W + K) - Gop W K‖ ≤ C ‖K‖²` for small `W` and `K`. -/
theorem exists_norm_mu_neg_add_sub_le : ∃ ρ > 0, ∀ W : E, ‖W‖ < ρ → ∃ κ > 0, ∃ C : ℝ,
    ∀ K : E, ‖K‖ < κ → ‖S.mu (-W) (W + K) - S.Gop W K‖ ≤ C * ‖K‖ ^ 2 := by
  obtain ⟨δ, hδ, K₁, hK₁⟩ := S.c11
  obtain ⟨ε, hε, A, hA0, hA⟩ := S.prod_estimate
  refine ⟨δ, hδ, fun W hW => ?_⟩
  set F : ℝ → E →L[ℝ] E := fun s => NormedSpace.exp ((-s) • S.ad W) with hF_def
  have hF : Continuous F := S.continuous_exp_neg_smul_ad W
  obtain ⟨α, hα⟩ := isCompact_Icc.exists_bound_of_continuousOn hF.continuousOn
  set α' := max α 1 with hα'_def
  have hα'0 : 0 < α' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hκ0 : 0 < min (ε / α') (δ - ‖W‖) := lt_min (div_pos hε hα'0) (by linarith)
  refine ⟨min (ε / α') (δ - ‖W‖), hκ0, A * α' ^ 2, fun K hK => ?_⟩
  have hKε : α' * ‖K‖ ≤ ε := by
    have := hK.le.trans (min_le_left _ _)
    rw [le_div_iff₀ hα'0] at this; linarith
  have hKδ : ‖W + K‖ < δ := by
    have := hK.trans_le (min_le_right _ _)
    linarith [norm_add_le W K]
  -- The vectors `Z m j = m⁻¹ • exp (-(j/m) • ad W) K`.
  set Z : ℕ → ℕ → E := fun m j => (m : ℝ)⁻¹ • F (j / m) K with hZ_def
  set P : ℕ → G := fun m =>
    S.exp (-W) * (S.exp ((m : ℝ)⁻¹ • W) * S.exp ((m : ℝ)⁻¹ • K)) ^ m with hP_def
  have hP : ∀ m : ℕ, 1 ≤ m → P m = (((List.range m).reverse.map (Z m)).map S.exp).prod := by
    intro m hm
    have hm0 : (m : ℝ) ≠ 0 := by positivity
    set a := S.exp ((m : ℝ)⁻¹ • W)
    set b := S.exp ((m : ℝ)⁻¹ • K)
    have hainv : ∀ j : ℕ, a⁻¹ ^ j = S.exp ((-((j : ℝ) / m)) • W) := fun j => by
      rw [← exp_neg, ← exp_natCast_smul, smul_neg, smul_smul, neg_smul, div_eq_mul_inv]
    have hW' : S.exp (-W) = a⁻¹ ^ m := by
      rw [hainv, div_self hm0, neg_smul, one_smul]
    have hterm : (fun j : ℕ => a⁻¹ ^ j * b * a ^ j) = S.exp ∘ Z m := by
      funext j
      rw [Function.comp_apply, ← inv_inv (a ^ j), ← inv_pow, hainv, Ad_spec, Ad_exp_smul]
      simp only [hZ_def, hF_def, map_smul]
    simp only [hP_def]
    rw [hW', inv_pow_mul_mul_pow, hterm, List.map_map]
  have hσ : ∀ m : ℕ, 1 ≤ m → (((List.range m).reverse.map (Z m)).map (‖·‖)).sum ≤ α' * ‖K‖ := by
    intro m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hbound : ∀ x ∈ ((List.range m).reverse.map (Z m)).map (‖·‖),
        x ≤ (m : ℝ)⁻¹ * (α' * ‖K‖) := by
      intro x hx
      simp only [List.map_map, List.mem_map, List.mem_reverse, List.mem_range,
        Function.comp_apply] at hx
      obtain ⟨j, hj, rfl⟩ := hx
      have hjm : (j : ℝ) / m ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨by positivity, by rw [div_le_one hm0]; exact_mod_cast hj.le⟩
      rw [hZ_def, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hm0.le)]
      gcongr
      calc ‖F (j / m) K‖ ≤ ‖F (j / m)‖ * ‖K‖ := (F (j / m)).le_opNorm K
        _ ≤ α' * ‖K‖ := by gcongr; exact (hα _ hjm).trans (le_max_left _ _)
    have := List.sum_le_length_nsmul _ _ hbound
    rw [List.length_map, List.length_map, List.length_reverse, List.length_range,
      nsmul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hm0.ne', one_mul] at this
    exact this
  have hsum : ∀ m : ℕ, ((List.range m).reverse.map (Z m)).sum =
      (m : ℝ)⁻¹ • ∑ j ∈ Finset.range m, F (j / m) K := by
    intro m
    rw [list_sum_map_range, Finset.smul_sum]
  -- Limits.
  have hQ : S.exp (-W) * S.exp (W + K) ∈ S.chart.target :=
    (hK₁ (-W) (W + K) (by simpa using hW) hKδ).1
  have hPlim : Tendsto P atTop (𝓝 (S.exp (-W) * S.exp (W + K))) :=
    ((show Continuous fun g : G => S.exp (-W) * g by fun_prop).tendsto _).comp (S.trotter W K)
  have hlogP : Tendsto (fun m => S.chart.symm (P m)) atTop (𝓝 (S.mu (-W) (W + K))) :=
    (S.chart.continuousAt_symm hQ).tendsto.comp hPlim
  have hR : Tendsto (fun m : ℕ => (m : ℝ)⁻¹ • ∑ j ∈ Finset.range m, F (j / m) K) atTop
      (𝓝 (S.Gop W K)) := by
    have h := tendsto_riemannSum (hF.clm_apply continuous_const : Continuous fun s => F s K)
    rwa [← ContinuousLinearMap.integral_apply (hF.integrableOn_Icc) K] at h
  have hlim := (hlogP.sub hR).norm
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  obtain ⟨-, hbd⟩ := hA _ ((hσ m hm).trans hKε)
  rw [← hP m hm, hsum] at hbd
  calc _ ≤ A * ((((List.range m).reverse.map (Z m)).map (‖·‖)).sum) ^ 2 := hbd
    _ ≤ A * (α' * ‖K‖) ^ 2 := by
        gcongr
        · exact List.sum_nonneg (by simp)
        · exact hσ m hm
    _ = A * α' ^ 2 * ‖K‖ ^ 2 := by ring

/-- **The derivative of `μ (-W, ·)` at `W`**: `K ↦ μ (-W, W + K)` has derivative `Gop W` at `0`. -/
theorem hasFDerivAt_mu_neg_add : ∃ ρ > 0, ∀ W : E, ‖W‖ < ρ →
    HasFDerivAt (fun K => S.mu (-W) (W + K)) (S.Gop W) 0 := by
  obtain ⟨ρ, hρ, h⟩ := S.exists_norm_mu_neg_add_sub_le
  refine ⟨ρ, hρ, fun W hW => ?_⟩
  obtain ⟨κ, hκ, C, hC⟩ := h W hW
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add, add_zero, S.mu_neg_self, sub_zero]
  refine Asymptotics.IsBigO.trans_isLittleO (g := fun K : E => ‖K‖ ^ 2) ?_
    (Asymptotics.isLittleO_norm_pow_id one_lt_two)
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [Metric.ball_mem_nhds (0 : E) hκ] with K hK
  rw [mem_ball_zero_iff] at hK
  rw [Real.norm_of_nonneg (by positivity)]
  exact hC K hK

end LocalExpStructure

end HSFormal.GY
