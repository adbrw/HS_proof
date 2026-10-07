import HSFormal.Inputs.GY.OneParamNorm

/-!
# The exponential chart (B5)

For a Gleason norm `𝒢` on a locally compact Hausdorff topological group `G`, with
`exp : LieAlg 𝒢 → G`, `exp X = X 1`:

* `LieAlg.image_closedBall_mem_nhds` (Prop 21, Hirschfeld's argument, blueprint §5 H3): the image of
  every closed ball `closedBall 0 r`, `r > 0`, is a neighbourhood of `1`;
* `LieAlg.isOpen_image_exp`: `exp` maps open subsets of a small ball to open sets, and is
  injective there (bilipschitz);
* `LieAlg.localExpStructure : LocalExpStructure G (LieAlg 𝒢)` (chart `exp` on a small ball,
  `c11` from Prop 22 and the bilipschitz bound, `conj` from `LieAlg.conj`);
* `GleasonNorm.exists_localExpStructure :
    ∃ d, Nonempty (LocalExpStructure G (EuclideanSpace ℝ (Fin d)))`
  (transport along `ContinuousLinearEquiv.ofFinrankEq`).
-/

noncomputable section

namespace HSFormal.GY

open Filter Topology

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace LieAlg

open OneParam

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] {𝒢 : GleasonNorm G}

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
theorem N_apply_one_le (X : LieAlg 𝒢) : 𝒢.N (X 1) ≤ ‖X‖ := by
  simpa using N_apply_le X 1

/-! ## Prop 21 -/

private theorem image_closedBall_mem_nhds_aux {r : ℝ} (hr : 0 < r)
    (hr₀ : r ≤ (8 * 𝒢.C ^ 2)⁻¹) :
    (fun X : LieAlg 𝒢 => X 1) '' Metric.closedBall 0 r ∈ 𝓝 (1 : G) := by
  have hC := 𝒢.C_pos
  have hC1 := 𝒢.one_le_C
  set e : LieAlg 𝒢 → G := fun X => X 1 with he_def
  set K := Metric.closedBall (0 : LieAlg 𝒢) r with hK_def
  have he0 : e 0 = 1 := rfl
  by_contra hnot
  -- 1. points `g n → 1` outside `e '' K`
  have hseq : ∀ n : ℕ, ∃ g : G, 𝒢.N g < 1 / ((n : ℝ) + 1) ∧ g ∉ e '' K := by
    intro n
    by_contra h
    push Not at h
    exact hnot (Filter.mem_of_superset (𝒢.setOf_lt_mem_nhds (by positivity)) fun g hg => h g hg)
  choose g hgN hgK using hseq
  -- 2. minimisers of `d(g n, e ·)` on `K`
  have hKc : IsCompact K := isCompact_closedBall 0 r
  have hmin : ∀ n, ∃ ψ ∈ K, IsMinOn (fun X => 𝒢.d (g n) (e X)) K ψ := fun n =>
    hKc.exists_isMinOn ⟨0, Metric.mem_closedBall_self hr.le⟩
      ((𝒢.continuous_d_right _).comp continuous_exp).continuousOn
  choose ψ hψK hψmin using hmin
  set h : ℕ → G := fun n => e (ψ n) with hh_def
  set k : ℕ → G := fun n => (h n)⁻¹ * g n with hk_def
  have hgk : ∀ n, g n = h n * k n := fun n => by simp [hk_def]
  have hkd : ∀ n, 𝒢.N (k n) = 𝒢.d (g n) (h n) := fun n => by
    rw [𝒢.d_comm]; rfl
  have hkg : ∀ n, 𝒢.N (k n) ≤ 𝒢.N (g n) := fun n => by
    rw [hkd]
    have := (isMinOn_iff.1 (hψmin n)) 0 (Metric.mem_closedBall_self hr.le)
    simpa [he0] using this
  have hkpos : ∀ n, 0 < 𝒢.N (k n) := fun n => by
    refine 𝒢.N_pos fun h1 => hgK n ⟨ψ n, hψK n, ?_⟩
    have : g n = h n := by rw [hgk n, h1, mul_one]
    exact this.symm
  have hhg : ∀ n, 𝒢.N (h n) ≤ 2 * 𝒢.N (g n) := fun n => by
    have := 𝒢.d_triangle 1 (g n) (h n)
    rw [𝒢.d_one_left, 𝒢.d_one_left, ← hkd] at this
    linarith [hkg n]
  have hψh : ∀ n, ‖ψ n‖ ≤ 4 * 𝒢.C * 𝒢.N (h n) := fun n => by
    have hψr : ‖ψ n‖ ≤ (8 * 𝒢.C ^ 2)⁻¹ := (mem_closedBall_zero_iff.1 (hψK n)).trans hr₀
    have := norm_sub_le_d hψr (by rw [norm_zero']; positivity)
    rwa [sub_zero, zero_apply, 𝒢.d_one_right] at this
  -- 3. limits as `n → ∞`
  have hg0 : Tendsto (fun n => 𝒢.N (g n)) atTop (𝓝 0) :=
    squeeze_zero (fun n => 𝒢.nonneg _) (fun n => (hgN n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  have hk0 : Tendsto (fun n => 𝒢.N (k n)) atTop (𝓝 0) :=
    squeeze_zero (fun n => 𝒢.nonneg _) hkg hg0
  have hh0 : Tendsto (fun n => 𝒢.N (h n)) atTop (𝓝 0) := by
    have := hg0.const_mul 2; rw [mul_zero] at this
    exact squeeze_zero (fun n => 𝒢.nonneg _) hhg this
  have hψ0 : Tendsto (fun n => ‖ψ n‖) atTop (𝓝 0) := by
    have := hh0.const_mul (4 * 𝒢.C); rw [mul_zero] at this
    exact squeeze_zero (fun n => norm_nonneg _) hψh this
  -- the scale `ε₁` and the times `M n = ⌊ε₁ / N(k n)⌋`
  obtain ⟨rK, hrK, hKK⟩ := 𝒢.exists_isCompact_le
  set ε₁ : ℝ := min rK (4 * 𝒢.C ^ 3)⁻¹ with hε₁_def
  have hε₁ : 0 < ε₁ := lt_min hrK (by positivity)
  have hε₁C : 𝒢.C * ε₁ ≤ (4 * 𝒢.C ^ 2)⁻¹ := by
    calc 𝒢.C * ε₁ ≤ 𝒢.C * (4 * 𝒢.C ^ 3)⁻¹ := by gcongr; exact min_le_right _ _
      _ = (4 * 𝒢.C ^ 2)⁻¹ := by field_simp
  have hε₁4 : ε₁ ≤ (4 * 𝒢.C ^ 2)⁻¹ := le_trans (le_mul_of_one_le_left hε₁.le hC1) hε₁C
  have hε₁2 : ε₁ ≤ (2 * 𝒢.C ^ 2)⁻¹ := hε₁4.trans (inv_anti₀ (by positivity) (by nlinarith))
  set M : ℕ → ℕ := fun n => ⌊ε₁ / 𝒢.N (k n)⌋₊ with hM_def
  have hMtop : Tendsto M atTop atTop := by
    have h1 : Tendsto (fun n => 𝒢.N (k n)) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨hk0, Eventually.of_forall hkpos⟩
    have h2 := (h1.inv_tendsto_nhdsGT_zero).const_mul_atTop hε₁
    refine tendsto_nat_floor_atTop.comp (h2.congr fun n => ?_)
    simp [div_eq_mul_inv]
  have hx : ∀ n, ∀ j ≤ M n, 𝒢.N (k n ^ j) ≤ ε₁ := fun n j hj => by
    have hfl := Nat.floor_le (div_nonneg hε₁.le (hkpos n).le : 0 ≤ ε₁ / 𝒢.N (k n))
    have hj' : (j : ℝ) ≤ M n := by exact_mod_cast hj
    calc 𝒢.N (k n ^ j) ≤ j * 𝒢.N (k n) := 𝒢.N_pow_le _ _
      _ ≤ (ε₁ / 𝒢.N (k n)) * 𝒢.N (k n) :=
          mul_le_mul_of_nonneg_right (hj'.trans hfl) (𝒢.nonneg _)
      _ = ε₁ := by field_simp [(hkpos n).ne']
  -- the limiting one-parameter subgroup
  set 𝒰 : Ultrafilter ℕ := hyperfilter ℕ
  have hU : (𝒰 : Filter ℕ) ≤ atTop := hyperfilter_le_cofinite.trans Nat.cofinite_eq_atTop.le
  obtain ⟨φ, hφlim, hφN⟩ := 𝒢.exists_ultralimit 𝒰 k M (hMtop.mono_left hU) hε₁2
    (𝒢.isCompact_setOf_le_of_le hKK (min_le_left _ _)) hx
  set Φ : LieAlg 𝒢 := ofOneParam φ with hΦ_def
  have hΦ : ‖Φ‖ ≤ 𝒢.C * ε₁ := norm_le_of_forall_abs fun t =>
    𝒢.N_le_of_isLip one_pos (fun s hs => hφN s (abs_le.1 hs)) t
  have hφ1 : Tendsto (fun n => k n ^ M n) (𝒰 : Filter ℕ) (𝓝 (φ 1)) := by
    have := hφlim 1 ⟨by norm_num, le_rfl⟩
    simpa only [one_mul, Int.floor_natCast, zpow_natCast] using this
  obtain ⟨δ, hδ, A, hA⟩ := 𝒢.dist_mul_add_le
  set A' := max A 0
  -- 4. choose a good index
  have hev1 : ∀ᶠ n in (𝒰 : Filter ℕ), 1 ≤ M n :=
    (hMtop.mono_left hU).eventually (eventually_ge_atTop 1)
  have hMr : Tendsto (fun n => 𝒢.C * ε₁ / (M n : ℝ)) (𝒰 : Filter ℕ) (𝓝 0) :=
    (tendsto_natCast_atTop_atTop.comp (hMtop.mono_left hU)).const_div_atTop _
  have hev2 : ∀ᶠ n in (𝒰 : Filter ℕ), ‖ψ n‖ < min (r / 2) δ :=
    (hψ0.mono_left hU).eventually (gt_mem_nhds (lt_min (half_pos hr) hδ))
  have hev3 : ∀ᶠ n in (𝒰 : Filter ℕ), 𝒢.C * ε₁ / (M n : ℝ) < min (r / 2) δ :=
    hMr.eventually (gt_mem_nhds (lt_min (half_pos hr) hδ))
  have hbr : Tendsto (fun n => 2 * 𝒢.C * 𝒢.d (k n ^ M n) (φ 1) + A' * 𝒢.N (h n) * (𝒢.C * ε₁))
      (𝒰 : Filter ℕ) (𝓝 (2 * 𝒢.C * 𝒢.d (φ 1) (φ 1) + A' * 0 * (𝒢.C * ε₁))) :=
    (((𝒢.continuous_d_left (φ 1)).continuousAt.tendsto.comp hφ1).const_mul _).add
      (((hh0.mono_left hU).const_mul A').mul_const _)
  simp only [𝒢.d_self, mul_zero, zero_mul, add_zero] at hbr
  have hev4 : ∀ᶠ n in (𝒰 : Filter ℕ),
      2 * 𝒢.C * 𝒢.d (k n ^ M n) (φ 1) + A' * 𝒢.N (h n) * (𝒢.C * ε₁) < ε₁ / 2 :=
    hbr.eventually (gt_mem_nhds (half_pos hε₁))
  obtain ⟨n, hn1, hn2, hn3, hn4⟩ := (hev1.and (hev2.and (hev3.and hev4))).exists
  -- 5. the competitor `W = ψ n + (1 / M n) • Φ` beats the minimiser
  set m : ℕ := M n with hm_def
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hn1
  set Φm : LieAlg 𝒢 := (m : ℝ)⁻¹ • Φ with hΦm_def
  have hΦm : ‖Φm‖ ≤ 𝒢.C * ε₁ / m := by
    rw [hΦm_def, norm_smul, Real.norm_eq_abs, abs_inv, Nat.abs_cast, inv_mul_eq_div]
    gcongr
  set W : LieAlg 𝒢 := ψ n + Φm with hW_def
  have hWK : W ∈ K := by
    rw [hK_def, mem_closedBall_zero_iff]
    calc ‖W‖ ≤ ‖ψ n‖ + ‖Φm‖ := norm_add_le _ _
      _ ≤ r / 2 + r / 2 := by
          gcongr
          · exact hn2.le.trans (min_le_left _ _)
          · exact hΦm.trans (hn3.le.trans (min_le_left _ _))
      _ = r := by ring
  have hmin' := (isMinOn_iff.1 (hψmin n)) W hWK
  -- (i) left invariance
  have hi : 𝒢.d (g n) (h n * e Φm) = 𝒢.d (k n) (e Φm) := by rw [hgk n, 𝒢.d_mul_left]
  -- (ii) Lemma 16(b) at power `m`
  have heΦm : e Φm = φ (m : ℝ)⁻¹ := by
    show φ ((m : ℝ)⁻¹ * 1) = _; rw [mul_one]
  have hNeΦm : 𝒢.N (e Φm) ≤ 𝒢.C * ε₁ / m := (N_apply_one_le Φm).trans hΦm
  have hpow : e Φm ^ m = φ 1 := by
    rw [heΦm, ← OneParam.map_natCast_mul, mul_inv_cancel₀ hm0.ne']
  have hkm : (m : ℝ) * 𝒢.N (k n) ≤ (4 * 𝒢.C ^ 2)⁻¹ := by
    have hfl := Nat.floor_le (div_nonneg hε₁.le (hkpos n).le : 0 ≤ ε₁ / 𝒢.N (k n))
    calc (m : ℝ) * 𝒢.N (k n) ≤ (ε₁ / 𝒢.N (k n)) * 𝒢.N (k n) :=
          mul_le_mul_of_nonneg_right hfl (𝒢.nonneg _)
      _ = ε₁ := by field_simp [(hkpos n).ne']
      _ ≤ (4 * 𝒢.C ^ 2)⁻¹ := hε₁4
  have hΦmm : (m : ℝ) * 𝒢.N (e Φm) ≤ (4 * 𝒢.C ^ 2)⁻¹ := by
    calc (m : ℝ) * 𝒢.N (e Φm) ≤ m * (𝒢.C * ε₁ / m) := by gcongr
      _ = 𝒢.C * ε₁ := by field_simp
      _ ≤ (4 * 𝒢.C ^ 2)⁻¹ := hε₁C
  have h16 := 𝒢.mul_d_le_d_pow hkm hΦmm
  rw [hpow] at h16
  -- (iii) Prop 22
  have h22 := hA (toOneParam (ψ n)) (toOneParam Φm) fun t ht =>
    ⟨(N_apply_le (ψ n) t).trans (by
        have : |t| ≤ 1 := abs_le.2 ht
        calc ‖ψ n‖ * |t| ≤ ‖ψ n‖ * 1 := by gcongr
          _ ≤ δ := by rw [mul_one]; exact hn2.le.trans (min_le_right _ _)),
     (N_apply_le Φm t).trans (by
        have : |t| ≤ 1 := abs_le.2 ht
        calc ‖Φm‖ * |t| ≤ ‖Φm‖ * 1 := by gcongr
          _ ≤ δ := by rw [mul_one]; exact hΦm.trans (hn3.le.trans (min_le_right _ _)))⟩
  change 𝒢.d (h n * e Φm) (e W) ≤ A * 𝒢.N (h n) * 𝒢.N (e Φm) at h22
  have h22' : 𝒢.d (h n * e Φm) (e W) ≤ A' * 𝒢.N (h n) * (𝒢.C * ε₁ / m) := by
    refine h22.trans ?_
    have h0 := 𝒢.nonneg (h n)
    have h0' := 𝒢.nonneg (e Φm)
    have hA' : 0 ≤ A' * 𝒢.N (h n) := mul_nonneg (le_max_right _ _) h0
    calc A * 𝒢.N (h n) * 𝒢.N (e Φm) ≤ A' * 𝒢.N (h n) * 𝒢.N (e Φm) := by
          gcongr; exact le_max_left _ _
      _ ≤ A' * 𝒢.N (h n) * (𝒢.C * ε₁ / m) := mul_le_mul_of_nonneg_left hNeΦm hA'
  -- (iv) combine
  have hupper : 𝒢.d (g n) (e W) < ε₁ / (2 * m) := by
    have t := 𝒢.d_triangle (g n) (h n * e Φm) (e W)
    rw [hi] at t
    have hd : 𝒢.d (k n) (e Φm) ≤ 2 * 𝒢.C * 𝒢.d (k n ^ m) (φ 1) / m := by
      rw [le_div_iff₀ hm0]; linarith
    have : 𝒢.d (g n) (e W) ≤
        (2 * 𝒢.C * 𝒢.d (k n ^ m) (φ 1) + A' * 𝒢.N (h n) * (𝒢.C * ε₁)) / m := by
      have e1 : (2 * 𝒢.C * 𝒢.d (k n ^ m) (φ 1) + A' * 𝒢.N (h n) * (𝒢.C * ε₁)) / m =
          2 * 𝒢.C * 𝒢.d (k n ^ m) (φ 1) / m + A' * 𝒢.N (h n) * (𝒢.C * ε₁ / m) := by ring
      rw [e1]; linarith
    calc 𝒢.d (g n) (e W) ≤ _ := this
      _ < (ε₁ / 2) / m := by gcongr
      _ = ε₁ / (2 * m) := by ring
  -- (v) the minimiser is at distance `N (k n) ≥ ε₁ / (2 m)`
  have hlower : ε₁ / (2 * m) ≤ 𝒢.d (g n) (e (ψ n)) := by
    rw [← hkd n]
    have hlt : ε₁ / 𝒢.N (k n) < (m : ℝ) + 1 := Nat.lt_floor_add_one _
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hn1
    rw [div_lt_iff₀ (hkpos n)] at hlt
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hkpos n]
  linarith

/-- **Prop 21** (Hirschfeld's argument, blueprint §5 H3): `exp (closedBall 0 r)` is a
neighbourhood of `1` for every `r > 0`. -/
theorem image_closedBall_mem_nhds {r : ℝ} (hr : 0 < r) :
    (fun X : LieAlg 𝒢 => X 1) '' Metric.closedBall 0 r ∈ 𝓝 (1 : G) := by
  have hC := 𝒢.C_pos
  refine Filter.mem_of_superset (image_closedBall_mem_nhds_aux (lt_min hr (by positivity))
    (min_le_right r (8 * 𝒢.C ^ 2)⁻¹)) ?_
  exact Set.image_mono (Metric.closedBall_subset_closedBall (min_le_left _ _))

/-! ## `exp` is a local homeomorphism near `0` -/

/-- `exp` is injective on balls of radius `≤ (8C²)⁻¹` (lower bilipschitz bound). -/
theorem injOn_exp {r : ℝ} (hr : r ≤ (8 * 𝒢.C ^ 2)⁻¹) :
    Set.InjOn (fun X : LieAlg 𝒢 => X 1) (Metric.closedBall 0 r) := by
  intro X hX Y hY hXY
  have hX' : ‖X‖ ≤ (8 * 𝒢.C ^ 2)⁻¹ := (mem_closedBall_zero_iff.1 hX).trans hr
  have hY' : ‖Y‖ ≤ (8 * 𝒢.C ^ 2)⁻¹ := (mem_closedBall_zero_iff.1 hY).trans hr
  have := norm_sub_le_d hX' hY'
  simp only at hXY
  rw [hXY, 𝒢.d_self, mul_zero] at this
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

/-- Radii for the exponential chart: `exp (closedBall 0 (8C²)⁻¹) ⊇ {N < ρ₀}` and `2 r₁ ≤ ρ₀`,
`2 r₁ ≤ (8C²)⁻¹`. -/
theorem exists_chart_radius : ∃ r₁ > 0, ∃ ρ₀ > 0, 2 * r₁ ≤ ρ₀ ∧ 2 * r₁ ≤ (8 * 𝒢.C ^ 2)⁻¹ ∧
    {g | 𝒢.N g < ρ₀} ⊆ (fun X : LieAlg 𝒢 => X 1) '' Metric.closedBall 0 (8 * 𝒢.C ^ 2)⁻¹ := by
  have hC := 𝒢.C_pos
  obtain ⟨ρ₀, hρ₀, hsub⟩ := 𝒢.small_subset _ (image_closedBall_mem_nhds (𝒢 := 𝒢)
    (by positivity : (0 : ℝ) < (8 * 𝒢.C ^ 2)⁻¹))
  refine ⟨min ρ₀ (8 * 𝒢.C ^ 2)⁻¹ / 2, by positivity, ρ₀, hρ₀, ?_, ?_, hsub⟩
  · linarith [min_le_left ρ₀ (8 * 𝒢.C ^ 2)⁻¹]
  · linarith [min_le_right ρ₀ (8 * 𝒢.C ^ 2)⁻¹]

/-- `exp` maps open subsets of `ball 0 r₁` to open sets. -/
theorem isOpen_image_exp {r₁ ρ₀ : ℝ} (h2ρ : 2 * r₁ ≤ ρ₀) (h2r : 2 * r₁ ≤ (8 * 𝒢.C ^ 2)⁻¹)
    (hρ : {g | 𝒢.N g < ρ₀} ⊆ (fun X : LieAlg 𝒢 => X 1) '' Metric.closedBall 0 (8 * 𝒢.C ^ 2)⁻¹)
    {V : Set (LieAlg 𝒢)} (hV : V ⊆ Metric.ball 0 r₁) (hVo : IsOpen V) :
    IsOpen ((fun X : LieAlg 𝒢 => X 1) '' V) := by
  have hC := 𝒢.C_pos
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨X₀, hX₀V, rfl⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hVo X₀ hX₀V
  have hX₀ : ‖X₀‖ < r₁ := mem_ball_zero_iff.1 (hV hX₀V)
  have hr₁ : 0 < r₁ := lt_of_le_of_lt (norm_nonneg _) hX₀
  set σ : ℝ := min (ε / (8 * 𝒢.C)) (r₁ / 2) with hσ_def
  have hσ : 0 < σ := lt_min (by positivity) (half_pos hr₁)
  have hnb : (fun z => X₀ 1 * z) '' ((fun X : LieAlg 𝒢 => X 1) '' Metric.closedBall 0 σ) ∈
      𝓝 (X₀ 1) := by
    rw [← map_mul_left_nhds_one]
    exact image_mem_map (image_closedBall_mem_nhds hσ)
  refine Filter.mem_of_superset hnb ?_
  rintro _ ⟨_, ⟨Z, hZ, rfl⟩, rfl⟩
  have hZσ : ‖Z‖ ≤ σ := mem_closedBall_zero_iff.1 hZ
  have hNg : 𝒢.N (X₀ 1 * Z 1) < ρ₀ := by
    have h1 := 𝒢.mul_le (X₀ 1) (Z 1)
    have h2 := N_apply_one_le X₀
    have h3 := N_apply_one_le Z
    have h4 : σ ≤ r₁ / 2 := min_le_right _ _
    linarith
  obtain ⟨W, hW, hWg⟩ := hρ hNg
  refine ⟨W, hball ?_, hWg⟩
  rw [Metric.mem_ball, dist_eq_norm]
  have hW' : ‖W‖ ≤ (8 * 𝒢.C ^ 2)⁻¹ := mem_closedBall_zero_iff.1 hW
  have hX₀' : ‖X₀‖ ≤ (8 * 𝒢.C ^ 2)⁻¹ := by linarith
  have := norm_sub_le_d hW' hX₀'
  simp only at hWg
  rw [hWg, 𝒢.d_mul_self] at this
  have h3 := N_apply_one_le Z
  have h5 : σ ≤ ε / (8 * 𝒢.C) := min_le_left _ _
  calc ‖W - X₀‖ ≤ 4 * 𝒢.C * 𝒢.N (Z 1) := this
    _ ≤ 4 * 𝒢.C * (ε / (8 * 𝒢.C)) := by gcongr; linarith
    _ = ε / 2 := by field_simp; ring
    _ < ε := half_lt_self hε

variable (𝒢) in
/-- The radius of the exponential chart. -/
def chartRadius : ℝ := Classical.choose (exists_chart_radius (𝒢 := 𝒢))

theorem chartRadius_spec : 0 < chartRadius 𝒢 ∧ ∃ ρ₀ > 0, 2 * chartRadius 𝒢 ≤ ρ₀ ∧
    2 * chartRadius 𝒢 ≤ (8 * 𝒢.C ^ 2)⁻¹ ∧
    {g | 𝒢.N g < ρ₀} ⊆ (fun X : LieAlg 𝒢 => X 1) '' Metric.closedBall 0 (8 * 𝒢.C ^ 2)⁻¹ :=
  Classical.choose_spec (exists_chart_radius (𝒢 := 𝒢))

theorem chartRadius_pos : 0 < chartRadius 𝒢 := chartRadius_spec.1

theorem two_mul_chartRadius_le : 2 * chartRadius 𝒢 ≤ (8 * 𝒢.C ^ 2)⁻¹ :=
  chartRadius_spec.2.choose_spec.2.2.1

theorem chartRadius_le : chartRadius 𝒢 ≤ (8 * 𝒢.C ^ 2)⁻¹ := by
  linarith [two_mul_chartRadius_le (𝒢 := 𝒢), chartRadius_pos (𝒢 := 𝒢)]

variable (𝒢) in
/-- The exponential chart: `exp` restricted to `ball 0 (chartRadius 𝒢)`. -/
def expChart : OpenPartialHomeomorph (LieAlg 𝒢) G :=
  LocalExpStructure.chartOfInjOn (fun X : LieAlg 𝒢 => X 1) continuous_exp Metric.isOpen_ball
    ((injOn_exp chartRadius_le).mono Metric.ball_subset_closedBall)
    fun _ hV hVo => by
      obtain ⟨-, ρ₀, -, h2ρ, h2r, hρ⟩ := chartRadius_spec (𝒢 := 𝒢)
      exact isOpen_image_exp h2ρ h2r hρ hV hVo

@[simp] theorem coe_expChart : ⇑(expChart 𝒢) = fun X : LieAlg 𝒢 => X 1 := rfl

@[simp] theorem expChart_source : (expChart 𝒢).source = Metric.ball 0 (chartRadius 𝒢) := rfl

@[simp] theorem expChart_target :
    (expChart 𝒢).target = (fun X : LieAlg 𝒢 => X 1) '' Metric.ball 0 (chartRadius 𝒢) := rfl

/-! ## The local exponential structure -/

theorem exp_c11 : ∃ δ > 0, ∃ K : ℝ, ∀ X Y : LieAlg 𝒢, ‖X‖ < δ → ‖Y‖ < δ →
    X 1 * Y 1 ∈ (expChart 𝒢).target ∧
      ‖(expChart 𝒢).symm (X 1 * Y 1) - (X + Y)‖ ≤ K * ‖X‖ * ‖Y‖ := by
  have hC := 𝒢.C_pos
  have hr₁ := chartRadius_pos (𝒢 := 𝒢)
  have hr₁8 := chartRadius_le (𝒢 := 𝒢)
  obtain ⟨δ₂₂, hδ₂₂, A, hA⟩ := 𝒢.dist_mul_add_le
  set A' := max A 0
  have htarget : (expChart 𝒢).target ∈ 𝓝 (1 : G) := by
    refine (expChart 𝒢).open_target.mem_nhds ?_
    exact ⟨0, Metric.mem_ball_self hr₁, rfl⟩
  obtain ⟨ρ₁, hρ₁, hsub⟩ := 𝒢.small_subset _ htarget
  set δ : ℝ := min (chartRadius 𝒢 / 2) (min (ρ₁ / 2) δ₂₂) with hδ_def
  have hδ : 0 < δ := lt_min (half_pos hr₁) (lt_min (half_pos hρ₁) hδ₂₂)
  have hδ1 : δ ≤ chartRadius 𝒢 / 2 := min_le_left _ _
  have hδ2 : δ ≤ ρ₁ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ3 : δ ≤ δ₂₂ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, hδ, 4 * 𝒢.C * A', fun X Y hX hY => ?_⟩
  have hmem : X 1 * Y 1 ∈ (expChart 𝒢).target := by
    refine hsub ?_
    show 𝒢.N (X 1 * Y 1) < ρ₁
    have := 𝒢.mul_le (X 1) (Y 1)
    linarith [N_apply_one_le X, N_apply_one_le Y]
  refine ⟨hmem, ?_⟩
  set W := (expChart 𝒢).symm (X 1 * Y 1) with hW_def
  have hWs : W ∈ (expChart 𝒢).source := (expChart 𝒢).map_target hmem
  have hWe : W 1 = X 1 * Y 1 := (expChart 𝒢).right_inv hmem
  have hW8 : ‖W‖ ≤ (8 * 𝒢.C ^ 2)⁻¹ :=
    (mem_ball_zero_iff.1 hWs).le.trans hr₁8
  have hXY8 : ‖X + Y‖ ≤ (8 * 𝒢.C ^ 2)⁻¹ := by
    have := norm_add_le X Y; linarith
  have hb := norm_sub_le_d hW8 hXY8
  rw [hWe] at hb
  have h22 := hA (toOneParam X) (toOneParam Y) fun t ht =>
    ⟨(N_apply_le X t).trans (by
        calc ‖X‖ * |t| ≤ ‖X‖ * 1 := by gcongr; exact abs_le.2 ht
          _ ≤ δ₂₂ := by linarith),
     (N_apply_le Y t).trans (by
        calc ‖Y‖ * |t| ≤ ‖Y‖ * 1 := by gcongr; exact abs_le.2 ht
          _ ≤ δ₂₂ := by linarith)⟩
  change 𝒢.d (X 1 * Y 1) ((X + Y) 1) ≤ A * 𝒢.N (X 1) * 𝒢.N (Y 1) at h22
  have h22' : 𝒢.d (X 1 * Y 1) ((X + Y) 1) ≤ A' * ‖X‖ * ‖Y‖ := by
    refine h22.trans ?_
    have h0 := 𝒢.nonneg (X 1)
    have h0' := 𝒢.nonneg (Y 1)
    calc A * 𝒢.N (X 1) * 𝒢.N (Y 1) ≤ A' * 𝒢.N (X 1) * 𝒢.N (Y 1) := by
          gcongr; exact le_max_left _ _
      _ ≤ A' * ‖X‖ * ‖Y‖ := by
          have hA' : 0 ≤ A' := le_max_right _ _
          gcongr
          · exact N_apply_one_le X
          · exact N_apply_one_le Y
  calc ‖W - (X + Y)‖ ≤ 4 * 𝒢.C * 𝒢.d (X 1 * Y 1) ((X + Y) 1) := hb
    _ ≤ 4 * 𝒢.C * (A' * ‖X‖ * ‖Y‖) := by gcongr
    _ = 4 * 𝒢.C * A' * ‖X‖ * ‖Y‖ := by ring

variable (𝒢) in
/-- **The local exponential structure** of `G` on `L(G) = LieAlg 𝒢` (blueprint B5). -/
def localExpStructure : LocalExpStructure G (LieAlg 𝒢) where
  exp X := X 1
  continuous_exp := continuous_exp
  exp_add_smul X s t := by
    simp only [smul_apply, mul_one]
    exact LieAlg.map_add X s t
  chart := expChart 𝒢
  chart_coe := rfl
  zero_mem_source := Metric.mem_ball_self chartRadius_pos
  c11 := exp_c11
  conj g := ⟨LinearMap.toContinuousLinearMap (conj g), fun X => by
    simp [conj_apply]⟩

@[simp] theorem localExpStructure_exp (X : LieAlg 𝒢) : (localExpStructure 𝒢).exp X = X 1 := rfl

end LieAlg

namespace GleasonNorm

/-- **B5**: a Gleason norm on a locally compact Hausdorff group yields a local exponential
structure modelled on some `ℝ^d`. -/
theorem exists_localExpStructure [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (𝒢 : GleasonNorm G) : ∃ d : ℕ, Nonempty (LocalExpStructure G (EuclideanSpace ℝ (Fin d))) :=
  ⟨Module.finrank ℝ (LieAlg 𝒢), ⟨(LieAlg.localExpStructure 𝒢).transport
    (ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm)⟩⟩

end GleasonNorm

end HSFormal.GY

end
