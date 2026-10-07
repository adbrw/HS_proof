import HSFormal.Inputs.GY.Defs
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Local homomorphisms, Lipschitz bounds and ultralimits of one-parameter subgroups (B2)

* `OneParam.exists_extend`: a continuous local homomorphism `[-T, T] → G` extends (uniquely, by
  `OneParam.ext_of_eqOn`) to a one-parameter subgroup, `X t = Φ (t / m) ^ m` for large `m`.
* `WeakGleasonNorm.oneParam_lipschitz`: `N (X t) ≤ L |t|` near `0` (escape to scale).
* `WeakGleasonNorm.exists_ultralimit`: the ultralimit `t ↦ lim_𝒰 x_i ^ ⌊t M_i⌋` of a sequence of
  "escaping slowly" elements is (the restriction to `[-1, 1]` of) a one-parameter subgroup `X`
  with `N (X t) ≤ C δ |t|`. Used in Prop 21 (blueprint H3).
* `WeakGleasonNorm.exists_ultralimit_oneParam`: pointwise ultralimits of a family of uniformly
  Lipschitz one-parameter subgroups form a one-parameter subgroup (blueprint H4, compact balls).

Only the weak Gleason norm is used. The compactness of the relevant ball is a hypothesis
(`IsCompact {g | N g ≤ δ}`); `WeakGleasonNorm.exists_ultralimit'` packages it with
`exists_isCompact_le` in the `∃ δ₀ > 0` form of the blueprint.
-/

noncomputable section

namespace HSFormal.GY

open Filter Topology

variable {G : Type*} [Group G] [TopologicalSpace G]

/-! ## Extension of local homomorphisms -/

namespace OneParam

section Extend

variable {Φ : ℝ → G} {T : ℝ}

omit [TopologicalSpace G] in
private theorem lh_zero (hT : 0 < T)
    (hadd : ∀ s t, |s| ≤ T → |t| ≤ T → |s + t| ≤ T → Φ (s + t) = Φ s * Φ t) : Φ 0 = 1 := by
  have h := hadd 0 0 (by simp [hT.le]) (by simp [hT.le]) (by simp [hT.le])
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

omit [TopologicalSpace G] in
private theorem lh_pow (hT : 0 < T)
    (hadd : ∀ s t, |s| ≤ T → |t| ≤ T → |s + t| ≤ T → Φ (s + t) = Φ s * Φ t)
    {a : ℝ} (ha : |a| ≤ T) (k : ℕ) (hk : |(k : ℝ) * a| ≤ T) : Φ (k * a) = Φ a ^ k := by
  induction k with
  | zero => simpa using lh_zero hT hadd
  | succ k ih =>
    have hk' : |(k : ℝ) * a| ≤ T := by
      refine le_trans ?_ hk
      rw [abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast]
      gcongr; linarith
    rw [Nat.cast_succ, add_mul, one_mul, hadd _ _ hk' ha (by simpa [add_mul] using hk), ih hk',
      pow_succ]

omit [TopologicalSpace G] in
/-- `Φ (t / m) ^ m` does not depend on `m ≥ 1` as long as `|t| ≤ m T`. -/
private theorem lh_root (hT : 0 < T)
    (hadd : ∀ s t, |s| ≤ T → |t| ≤ T → |s + t| ≤ T → Φ (s + t) = Φ s * Φ t)
    {t : ℝ} {m m' : ℕ} (hm : 1 ≤ m) (hm' : 1 ≤ m') (ht : |t| ≤ m * T) (ht' : |t| ≤ m' * T) :
    Φ (t / m) ^ m = Φ (t / m') ^ m' := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm0' : (0 : ℝ) < m' := by exact_mod_cast hm'
  -- `Φ (t / m) = Φ (t / (m m')) ^ m'`
  have key : ∀ {p q : ℕ} (hp : (0 : ℝ) < p) (hq : (0 : ℝ) < q), |t| ≤ p * T →
      Φ (t / p) = Φ (t / (p * q)) ^ q := by
    intro p q hp hq htp
    have h1 : |t / p| ≤ T := by rw [abs_div, Nat.abs_cast, div_le_iff₀ hp]; linarith
    have h2 : |t / (p * q)| ≤ T := by
      refine le_trans ?_ h1
      rw [abs_div, abs_div, Nat.abs_cast, abs_mul, Nat.abs_cast, Nat.abs_cast]
      apply div_le_div_of_nonneg_left (abs_nonneg t) hp
      have : (1 : ℝ) ≤ q := by
        rcases Nat.eq_zero_or_pos q with h | h
        · subst h; simp at hq
        · exact_mod_cast h
      nlinarith
    have h3 : (q : ℝ) * (t / (p * q)) = t / p := by field_simp
    rw [← lh_pow hT hadd h2 q (by rwa [h3]), h3]
  rw [key hm0 hm0' ht, key hm0' hm0 ht', ← pow_mul, ← pow_mul, mul_comm (m : ℝ), mul_comm m']

omit [TopologicalSpace G] in
/-- The extension `t ↦ Φ (t / m) ^ m`, `m = ⌈|t| / T⌉₊ + 1`. -/
def extendFun (Φ : ℝ → G) (T : ℝ) (t : ℝ) : G :=
  Φ (t / (⌈|t| / T⌉₊ + 1 : ℕ)) ^ (⌈|t| / T⌉₊ + 1)

private theorem le_extend_index (hT : 0 < T) (t : ℝ) : |t| ≤ ((⌈|t| / T⌉₊ + 1 : ℕ) : ℝ) * T := by
  have := Nat.le_ceil (|t| / T)
  rw [div_le_iff₀ hT] at this
  push_cast
  nlinarith

omit [TopologicalSpace G] in
private theorem extendFun_eq (hT : 0 < T)
    (hadd : ∀ s t, |s| ≤ T → |t| ≤ T → |s + t| ≤ T → Φ (s + t) = Φ s * Φ t)
    {t : ℝ} {m : ℕ} (hm : 1 ≤ m) (ht : |t| ≤ m * T) : extendFun Φ T t = Φ (t / m) ^ m :=
  lh_root hT hadd (Nat.le_add_left 1 _) hm (le_extend_index hT t) ht

/-- **Extension of local homomorphisms** (blueprint B2). A continuous local homomorphism
`[-T, T] → G` is the restriction of a one-parameter subgroup. -/
theorem exists_extend [ContinuousMul G] (hT : 0 < T)
    (hadd : ∀ s t, |s| ≤ T → |t| ≤ T → |s + t| ≤ T → Φ (s + t) = Φ s * Φ t)
    (hc : ContinuousOn Φ (Set.Icc (-T) T)) : ∃ X : OneParam G, Set.EqOn X Φ (Set.Icc (-T) T) := by
  have hmap : ∀ s t, extendFun Φ T (s + t) = extendFun Φ T s * extendFun Φ T t := by
    intro s t
    set m : ℕ := ⌈(|s| + |t|) / T⌉₊ + 1 with hm_def
    have hm1 : 1 ≤ m := Nat.le_add_left 1 _
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have hst : |s| + |t| ≤ m * T := by
      have := Nat.le_ceil ((|s| + |t|) / T)
      rw [div_le_iff₀ hT] at this
      rw [hm_def]; push_cast; nlinarith
    have hs : |s| ≤ m * T := by linarith [abs_nonneg t]
    have ht : |t| ≤ m * T := by linarith [abs_nonneg s]
    have hst' : |s + t| ≤ m * T := (abs_add_le s t).trans hst
    have hsm : |s / m| ≤ T := by rw [abs_div, Nat.abs_cast, div_le_iff₀ hm0]; linarith
    have htm : |t / m| ≤ T := by rw [abs_div, Nat.abs_cast, div_le_iff₀ hm0]; linarith
    have hstm : |s / m + t / m| ≤ T := by
      rw [← add_div, abs_div, Nat.abs_cast, div_le_iff₀ hm0]; linarith
    have hcomm : Commute (Φ (s / m)) (Φ (t / m)) := by
      rw [Commute, SemiconjBy, ← hadd _ _ hsm htm hstm, ← hadd _ _ htm hsm (by rwa [add_comm]),
        add_comm]
    rw [extendFun_eq hT hadd hm1 hst', extendFun_eq hT hadd hm1 hs, extendFun_eq hT hadd hm1 ht,
      add_div, hadd _ _ hsm htm hstm, hcomm.mul_pow]
  have hcont : Continuous (extendFun Φ T) := by
    refine continuous_iff_continuousAt.2 fun t₀ => ?_
    set k : ℕ := ⌈|t₀| / T⌉₊ + 1 with hk_def
    have hk1 : 1 ≤ k := Nat.le_add_left 1 _
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    have ht₀ : |t₀| < k * T := by
      have := Nat.le_ceil (|t₀| / T)
      rw [div_le_iff₀ hT] at this
      rw [hk_def]; push_cast; nlinarith
    have hev : ∀ᶠ t in 𝓝 t₀, extendFun Φ T t = Φ (t / k) ^ k := by
      have hopen : IsOpen {t : ℝ | |t| < k * T} := isOpen_lt continuous_abs continuous_const
      filter_upwards [hopen.mem_nhds ht₀] with t ht
      exact extendFun_eq hT hadd hk1 ht.le
    have hin : t₀ / k ∈ Set.Ioo (-T) T := by
      rw [Set.mem_Ioo, ← abs_lt, abs_div, Nat.abs_cast, div_lt_iff₀ hk0]; linarith
    have hΦ : ContinuousAt Φ (t₀ / k) :=
      hc.continuousAt (Icc_mem_nhds hin.1 hin.2)
    have hdiv : ContinuousAt (fun t : ℝ => t / k) t₀ := (continuous_id.div_const _).continuousAt
    exact ((ContinuousAt.comp (g := Φ) (f := fun t : ℝ => t / (k : ℝ)) (x := t₀) hΦ hdiv).pow
      k).congr (hev.mono fun _ h => h.symm)
  refine ⟨⟨extendFun Φ T, hmap, hcont⟩, fun t ht => ?_⟩
  have ht' : |t| ≤ ((1 : ℕ) : ℝ) * T := by rw [Nat.cast_one, one_mul, abs_le]; exact ht
  simp only [coe_mk]
  rw [extendFun_eq hT hadd le_rfl ht']
  simp

/-- The extension of a continuous local homomorphism is unique. -/
theorem existsUnique_extend [ContinuousMul G] (hT : 0 < T)
    (hadd : ∀ s t, |s| ≤ T → |t| ≤ T → |s + t| ≤ T → Φ (s + t) = Φ s * Φ t)
    (hc : ContinuousOn Φ (Set.Icc (-T) T)) : ∃! X : OneParam G, Set.EqOn X Φ (Set.Icc (-T) T) := by
  obtain ⟨X, hX⟩ := exists_extend hT hadd hc
  exact ⟨X, hX, fun Y hY => ext_of_eqOn hT fun t ht => (hY ht).trans (hX ht).symm⟩

end Extend

end OneParam

/-! ## Lipschitz bounds and ultralimits -/

namespace WeakGleasonNorm

variable (𝒩 : WeakGleasonNorm G)

/-- **Lipschitz bound** (blueprint B2): every one-parameter subgroup satisfies
`N (X t) ≤ L |t|` for `|t| ≤ T`. -/
theorem oneParam_lipschitz (X : OneParam G) :
    ∃ T > 0, ∃ L ≥ 0, ∀ t, |t| ≤ T → 𝒩.N (X t) ≤ L * |t| := by
  set δ : ℝ := (2 * 𝒩.C ^ 2)⁻¹ with hδ_def
  have hC := 𝒩.C_pos
  have hδ : 0 < δ := by positivity
  have hcont : Continuous fun t => 𝒩.N (X t) := 𝒩.continuous.comp X.continuous
  obtain ⟨ρ, hρ, hball⟩ := Metric.continuousAt_iff.1 hcont.continuousAt δ hδ
  refine ⟨ρ / 2, half_pos hρ, 2 * 𝒩.C * δ / (ρ / 2), by positivity, fun t ht => ?_⟩
  have hsmall : ∀ s : ℝ, |s| ≤ ρ / 2 → 𝒩.N (X s) ≤ δ := fun s hs => by
    have := hball (x := s) (by rw [Real.dist_eq, sub_zero]; linarith)
    rw [Real.dist_eq, OneParam.map_zero, 𝒩.N_one, sub_zero, abs_of_nonneg (𝒩.nonneg _)] at this
    exact this.le
  rcases eq_or_ne t 0 with rfl | ht0
  · simp
  have hta : 0 < |t| := abs_pos.2 ht0
  set n : ℕ := ⌊(ρ / 2) / |t|⌋₊ with hn_def
  have hn1 : 1 ≤ n := by
    rw [hn_def, Nat.one_le_floor_iff, le_div_iff₀ hta]; linarith
  have hnt : (n : ℝ) * |t| ≤ ρ / 2 := by
    have := Nat.floor_le (div_nonneg (half_pos hρ).le hta.le : 0 ≤ (ρ / 2) / |t|)
    rw [← hn_def, le_div_iff₀ hta] at this; exact this
  have hx : ∀ k : ℕ, 1 ≤ k → k ≤ n → 𝒩.N (X t ^ k) ≤ δ := fun k _ hk => by
    rw [← OneParam.map_natCast_mul]
    refine hsmall _ ?_
    rw [abs_mul, Nat.abs_cast]
    exact le_trans (by gcongr) hnt
  have hesc := 𝒩.N_le_of_pow_le le_rfl hn1 hx
  -- `n + 1 > (ρ/2)/|t|`, hence `1 / n ≤ 2 |t| / (ρ / 2)`
  have hlt : (ρ / 2) / |t| < n + 1 := Nat.lt_floor_add_one _
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  rw [div_lt_iff₀ hta] at hlt
  refine hesc.trans ?_
  rw [div_le_iff₀ hn0]
  have hCδ : 0 ≤ 𝒩.C * δ := by positivity
  have key : ρ / 2 ≤ 2 * |t| * n := by nlinarith
  calc 𝒩.C * δ = 𝒩.C * δ / (ρ / 2) * (ρ / 2) := by field_simp
    _ ≤ 𝒩.C * δ / (ρ / 2) * (2 * |t| * n) := by gcongr
    _ = 2 * 𝒩.C * δ / (ρ / 2) * |t| * n := by ring

/-- Ultralimits of points eventually in a compact set exist. -/
theorem _root_.HSFormal.GY.exists_tendsto_ultrafilter_of_isCompact {X : Type*}
    [TopologicalSpace X] {ι : Type*} (𝒰 : Ultrafilter ι) {K : Set X} (hK : IsCompact K)
    {f : ι → X} (hf : ∀ᶠ i in (𝒰 : Filter ι), f i ∈ K) :
    ∃ y ∈ K, Tendsto f 𝒰 (𝓝 y) := by
  obtain ⟨y, hyK, hy⟩ := hK.ultrafilter_le_nhds (𝒰.map f)
    (by rw [Ultrafilter.coe_map, Filter.le_principal_iff]; exact hf)
  exact ⟨y, hyK, by rwa [Ultrafilter.coe_map] at hy⟩

private theorem N_zpow_le_of_natAbs_le {x : G} {M : ℕ} {δ : ℝ}
    (hx : ∀ j ≤ M, 𝒩.N (x ^ j) ≤ δ) {j : ℤ} (hj : j.natAbs ≤ M) : 𝒩.N (x ^ j) ≤ δ := by
  rcases Int.natAbs_eq j with h | h
  · rw [h, zpow_natCast]; exact hx _ hj
  · rw [h, zpow_neg, zpow_natCast, 𝒩.N_inv]; exact hx _ hj

private theorem natAbs_floor_mul_le {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) (M : ℕ) :
    (⌊t * M⌋).natAbs ≤ M := by
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have h1 : -(M : ℝ) ≤ t * M := by nlinarith [ht.1]
  have h2 : t * M ≤ (M : ℝ) := by nlinarith [ht.2]
  have h3 : -(M : ℤ) ≤ ⌊t * M⌋ := Int.le_floor.2 (by push_cast; exact h1)
  have h4 : ⌊t * M⌋ ≤ (M : ℤ) := by
    have := Int.floor_le (t * M)
    exact_mod_cast this.trans h2
  omega

private theorem abs_floor_sub_floor_le (a b : ℝ) : |((⌊a⌋ - ⌊b⌋ : ℤ) : ℝ)| ≤ |a - b| + 1 := by
  have ha := Int.floor_le a
  have ha' := Int.lt_floor_add_one a
  have hb := Int.floor_le b
  have hb' := Int.lt_floor_add_one b
  push_cast
  rw [abs_le]
  constructor
  · have : -(|a - b|) ≤ a - b := neg_abs_le _
    linarith
  · have : a - b ≤ |a - b| := le_abs_self _
    linarith

private theorem floor_add_sub_mem (a b : ℝ) :
    ⌊a + b⌋ - ⌊a⌋ - ⌊b⌋ = 0 ∨ ⌊a + b⌋ - ⌊a⌋ - ⌊b⌋ = 1 := by
  have h1 : ⌊a⌋ + ⌊b⌋ ≤ ⌊a + b⌋ := Int.le_floor_add a b
  have h2 : ⌊a + b⌋ ≤ ⌊a⌋ + ⌊b⌋ + 1 := by
    have ha' := Int.lt_floor_add_one a
    have hb' := Int.lt_floor_add_one b
    have hab := Int.floor_le (a + b)
    have : (⌊a + b⌋ : ℝ) < ⌊a⌋ + ⌊b⌋ + 2 := by linarith
    have : ⌊a + b⌋ < ⌊a⌋ + ⌊b⌋ + 2 := by exact_mod_cast this
    omega
  omega

/-- **Ultralimit** (blueprint B2). Let `x_i ∈ G` and `M_i → ∞` along an ultrafilter `𝒰`, with
`N (x_i ^ j) ≤ δ` for `j ≤ M_i`, where `δ ≤ (2C²)⁻¹` and `{N ≤ δ}` is compact. Then there is a
one-parameter subgroup `X` with `x_i ^ ⌊t M_i⌋ → X t` along `𝒰` and `N (X t) ≤ C δ |t|` for
`t ∈ [-1, 1]`. -/
theorem exists_ultralimit [IsTopologicalGroup G] [T2Space G] {ι : Type*} (𝒰 : Ultrafilter ι)
    (x : ι → G) (M : ι → ℕ) {δ : ℝ} (hM : Tendsto M 𝒰 atTop) (hδ : δ ≤ (2 * 𝒩.C ^ 2)⁻¹)
    (hK : IsCompact {g | 𝒩.N g ≤ δ}) (hx : ∀ i, ∀ j ≤ M i, 𝒩.N (x i ^ j) ≤ δ) :
    ∃ X : OneParam G,
      (∀ t ∈ Set.Icc (-1 : ℝ) 1, Tendsto (fun i => x i ^ ⌊t * M i⌋) 𝒰 (𝓝 (X t))) ∧
      ∀ t ∈ Set.Icc (-1 : ℝ) 1, 𝒩.N (X t) ≤ 𝒩.C * δ * |t| := by
  have hC := 𝒩.C_pos
  obtain ⟨i₀⟩ : Nonempty ι := (𝒰 : Filter ι).nonempty_of_neBot
  have hδ0 : 0 ≤ δ := by simpa using hx i₀ 0 (Nat.zero_le _)
  set f : ℝ → ι → G := fun t i => x i ^ ⌊t * M i⌋ with hf_def
  -- `N (x_i) ≤ C δ / M_i` eventually, and `C δ / M_i → 0`
  have hM1 : ∀ᶠ i in (𝒰 : Filter ι), 1 ≤ M i := hM.eventually (eventually_ge_atTop 1)
  have hxi : ∀ᶠ i in (𝒰 : Filter ι), 𝒩.N (x i) ≤ 𝒩.C * δ / M i := by
    filter_upwards [hM1] with i hi
    exact 𝒩.N_le_of_pow_le hδ hi fun k _ hk => hx i k hk
  have hMr : Tendsto (fun i => (M i : ℝ)) 𝒰 atTop := tendsto_natCast_atTop_atTop.comp hM
  have hε : Tendsto (fun i => 𝒩.C * δ / M i) 𝒰 (𝓝 0) := hMr.const_div_atTop _
  have hx1 : Tendsto x 𝒰 (𝓝 1) := by
    rw [𝒩.tendsto_nhds_one_iff]
    refine squeeze_zero' (Eventually.of_forall fun i => 𝒩.nonneg _) hxi hε
  -- existence of the limits
  have hmemK : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ∀ i, f t i ∈ {g | 𝒩.N g ≤ δ} := fun t ht i =>
    𝒩.N_zpow_le_of_natAbs_le (hx i) (natAbs_floor_mul_le ht (M i))
  have hex : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ∃ y, Tendsto (f t) 𝒰 (𝓝 y) := fun t ht => by
    obtain ⟨y, -, hy⟩ := exists_tendsto_ultrafilter_of_isCompact 𝒰 hK
      (Eventually.of_forall (hmemK t ht))
    exact ⟨y, hy⟩
  set Φ : ℝ → G := fun t => @limUnder _ _ _ ⟨1⟩ (𝒰 : Filter ι) (f t) with hΦ_def
  have hlim : ∀ t ∈ Set.Icc (-1 : ℝ) 1, Tendsto (f t) 𝒰 (𝓝 (Φ t)) := fun t ht => by
    obtain ⟨y, hy⟩ := hex t ht
    rw [hΦ_def]; simp only; rw [hy.limUnder_eq]; exact hy
  have hΦ0 : Φ 0 = 1 := by
    have : Tendsto (f 0) 𝒰 (𝓝 1) := by simp [hf_def]
    exact tendsto_nhds_unique (hlim 0 ⟨by norm_num, by norm_num⟩) this
  -- the Lipschitz bound `N (Φ s⁻¹ * Φ t) ≤ C δ |t - s|`
  have hlip : ∀ s ∈ Set.Icc (-1 : ℝ) 1, ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      𝒩.N ((Φ s)⁻¹ * Φ t) ≤ 𝒩.C * δ * |t - s| := by
    intro s hs t ht
    have hT : Tendsto (fun i => 𝒩.N ((f s i)⁻¹ * f t i)) 𝒰 (𝓝 (𝒩.N ((Φ s)⁻¹ * Φ t))) :=
      (𝒩.continuous.tendsto _).comp ((hlim s hs).inv.mul (hlim t ht))
    have hB : Tendsto (fun i => 𝒩.C * δ * |t - s| + 𝒩.C * δ / M i) 𝒰
        (𝓝 (𝒩.C * δ * |t - s| + 0)) := tendsto_const_nhds.add hε
    rw [add_zero] at hB
    refine le_of_tendsto_of_tendsto hT hB ?_
    filter_upwards [hxi, hM1] with i hi hi1
    have hMi : (0 : ℝ) < M i := by exact_mod_cast hi1
    have e : (f s i)⁻¹ * f t i = x i ^ (⌊t * M i⌋ - ⌊s * M i⌋) := by
      simp only [hf_def]; rw [← zpow_neg, ← zpow_add, neg_add_eq_sub]
    rw [e]
    refine (𝒩.N_zpow_le _ _).trans ?_
    have h1 := abs_floor_sub_floor_le (t * M i) (s * M i)
    rw [← sub_mul, abs_mul, Nat.abs_cast] at h1
    calc |((⌊t * M i⌋ - ⌊s * M i⌋ : ℤ) : ℝ)| * 𝒩.N (x i)
        ≤ (|t - s| * M i + 1) * (𝒩.C * δ / M i) := by
          gcongr
          exact 𝒩.nonneg _
      _ = 𝒩.C * δ * |t - s| + 𝒩.C * δ / M i := by field_simp
  -- local homomorphism
  have hadd : ∀ s t, |s| ≤ 1 → |t| ≤ 1 → |s + t| ≤ 1 → Φ (s + t) = Φ s * Φ t := by
    intro s t hs ht hst
    replace hs : s ∈ Set.Icc (-1 : ℝ) 1 := abs_le.1 hs
    replace ht : t ∈ Set.Icc (-1 : ℝ) 1 := abs_le.1 ht
    replace hst : s + t ∈ Set.Icc (-1 : ℝ) 1 := abs_le.1 hst
    -- `f (s + t) i = f s i * f t i * x i ^ e_i` with `e_i ∈ {0, 1}`
    have he : ∀ i, f (s + t) i = f s i * f t i * x i ^ (⌊s * M i + t * M i⌋ - ⌊s * M i⌋ -
        ⌊t * M i⌋) := fun i => by
      simp only [hf_def, add_mul]
      rw [← zpow_add, ← zpow_add]; congr 1; ring
    have hsmall : Tendsto (fun i => x i ^ (⌊s * M i + t * M i⌋ - ⌊s * M i⌋ - ⌊t * M i⌋)) 𝒰
        (𝓝 1) := by
      have hNx : Tendsto (fun i => 𝒩.N (x i)) 𝒰 (𝓝 0) := 𝒩.tendsto_nhds_one_iff.1 hx1
      rw [𝒩.tendsto_nhds_one_iff]
      refine squeeze_zero (fun i => 𝒩.nonneg _) (fun i => ?_) hNx
      rcases floor_add_sub_mem (s * M i) (t * M i) with h | h
      · rw [h, zpow_zero, 𝒩.N_one]; exact 𝒩.nonneg _
      · rw [h, zpow_one]
    have h1 : Tendsto (f (s + t)) 𝒰 (𝓝 (Φ s * Φ t * 1)) := by
      have hfun : f (s + t) = fun i => f s i * f t i * x i ^ (⌊s * M i + t * M i⌋ - ⌊s * M i⌋ -
          ⌊t * M i⌋) := funext he
      rw [hfun]
      exact ((hlim s hs).mul (hlim t ht)).mul hsmall
    rw [mul_one] at h1
    exact tendsto_nhds_unique (hlim (s + t) hst) h1
  -- continuity on `[-1, 1]`
  have hcont : ContinuousOn Φ (Set.Icc (-1) 1) := by
    intro s hs
    have h1 : Tendsto (fun t => (Φ s)⁻¹ * Φ t) (𝓝[Set.Icc (-1) 1] s) (𝓝 1) := by
      rw [𝒩.tendsto_nhds_one_iff]
      have hz : Tendsto (fun t => 𝒩.C * δ * |t - s|) (𝓝[Set.Icc (-1) 1] s) (𝓝 0) := by
        have : Tendsto (fun t => 𝒩.C * δ * |t - s|) (𝓝 s) (𝓝 (𝒩.C * δ * |s - s|)) :=
          ((continuous_id.sub continuous_const).abs.const_mul _).tendsto s
        simpa using this.mono_left nhdsWithin_le_nhds
      refine squeeze_zero' (Eventually.of_forall fun t => 𝒩.nonneg _) ?_ hz
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact hlip s hs t ht
    have h2 := (tendsto_const_nhds (x := Φ s)).mul h1
    simp only [mul_inv_cancel_left, mul_one] at h2
    exact h2
  obtain ⟨X, hX⟩ := OneParam.exists_extend one_pos hadd hcont
  refine ⟨X, fun t ht => ?_, fun t ht => ?_⟩
  · rw [hX ht]; exact hlim t ht
  · rw [hX ht]
    simpa [hΦ0] using hlip 0 ⟨by norm_num, by norm_num⟩ t ht

/-- The ultralimit lemma in the `∃ δ₀ > 0` form of the blueprint (ℕ-indexed, locally compact
`G`). -/
theorem exists_ultralimit' [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] :
    ∃ δ₀ > 0, ∀ (𝒰 : Ultrafilter ℕ) (x : ℕ → G) (M : ℕ → ℕ) (δ : ℝ), Tendsto M 𝒰 atTop →
      δ ≤ δ₀ → (∀ n, ∀ j ≤ M n, 𝒩.N (x n ^ j) ≤ δ) →
      ∃ X : OneParam G,
        (∀ t ∈ Set.Icc (-1 : ℝ) 1, Tendsto (fun n => x n ^ ⌊t * M n⌋) 𝒰 (𝓝 (X t))) ∧
        ∀ t ∈ Set.Icc (-1 : ℝ) 1, 𝒩.N (X t) ≤ 𝒩.C * δ * |t| := by
  obtain ⟨r₀, hr₀, hK⟩ := 𝒩.exists_isCompact_le
  have hC := 𝒩.C_pos
  refine ⟨min r₀ (2 * 𝒩.C ^ 2)⁻¹, lt_min hr₀ (by positivity), fun 𝒰 x M δ hM hδ hx => ?_⟩
  exact 𝒩.exists_ultralimit 𝒰 x M hM (hδ.trans (min_le_right _ _))
    (𝒩.isCompact_setOf_le_of_le hK (hδ.trans (min_le_left _ _))) hx

/-- **Ultralimits of uniformly Lipschitz one-parameter subgroups** (blueprint H4): if
`N (X_i t) ≤ L |t|` for `|t| ≤ T` and `{N ≤ L T}` is compact, the pointwise `𝒰`-limits on
`[-T, T]` are the values of a one-parameter subgroup `Y` with `N (Y t) ≤ L |t|` there. -/
theorem exists_ultralimit_oneParam [IsTopologicalGroup G] [T2Space G] {ι : Type*}
    (𝒰 : Ultrafilter ι) (X : ι → OneParam G) {T L : ℝ} (hT : 0 < T)
    (hK : IsCompact {g | 𝒩.N g ≤ L * T}) (hX : ∀ i t, |t| ≤ T → 𝒩.N (X i t) ≤ L * |t|) :
    ∃ Y : OneParam G, (∀ t ∈ Set.Icc (-T) T, Tendsto (fun i => X i t) 𝒰 (𝓝 (Y t))) ∧
      ∀ t ∈ Set.Icc (-T) T, 𝒩.N (Y t) ≤ L * |t| := by
  obtain ⟨i₀⟩ : Nonempty ι := (𝒰 : Filter ι).nonempty_of_neBot
  have hL : 0 ≤ L := by
    have h := hX i₀ T (by rw [abs_of_pos hT])
    rw [abs_of_pos hT] at h
    exact nonneg_of_mul_nonneg_left ((𝒩.nonneg _).trans h) hT
  have hex : ∀ t ∈ Set.Icc (-T) T, ∃ y, Tendsto (fun i => X i t) 𝒰 (𝓝 y) := fun t ht => by
    have ht' : |t| ≤ T := abs_le.2 ht
    obtain ⟨y, -, hy⟩ := exists_tendsto_ultrafilter_of_isCompact 𝒰 hK
      (Eventually.of_forall fun i => show 𝒩.N (X i t) ≤ L * T from
        (hX i t ht').trans (by gcongr))
    exact ⟨y, hy⟩
  set Φ : ℝ → G := fun t => @limUnder _ _ _ ⟨1⟩ (𝒰 : Filter ι) (fun i => X i t) with hΦ_def
  have hlim : ∀ t ∈ Set.Icc (-T) T, Tendsto (fun i => X i t) 𝒰 (𝓝 (Φ t)) := fun t ht => by
    obtain ⟨y, hy⟩ := hex t ht
    rw [hΦ_def]; simp only; rw [hy.limUnder_eq]; exact hy
  have hbound : ∀ t ∈ Set.Icc (-T) T, 𝒩.N (Φ t) ≤ L * |t| := fun t ht =>
    le_of_tendsto ((𝒩.continuous.tendsto _).comp (hlim t ht))
      (Eventually.of_forall fun i => hX i t (abs_le.2 ht))
  have hadd : ∀ s t, |s| ≤ T → |t| ≤ T → |s + t| ≤ T → Φ (s + t) = Φ s * Φ t := by
    intro s t hs ht hst
    rw [abs_le] at hs ht hst
    have h1 : Tendsto (fun i => X i (s + t)) 𝒰 (𝓝 (Φ s * Φ t)) := by
      simp only [OneParam.map_add]; exact (hlim s hs).mul (hlim t ht)
    exact tendsto_nhds_unique (hlim (s + t) hst) h1
  have hcont : ContinuousOn Φ (Set.Icc (-T) T) := by
    intro s hs
    -- `Φ s⁻¹ * Φ t = lim X_i (t - s)`, of norm `≤ L |t - s|` when `|t - s| ≤ T`
    have hdiff : ∀ t ∈ Set.Icc (-T) T, |t - s| ≤ T → 𝒩.N ((Φ s)⁻¹ * Φ t) ≤ L * |t - s| := by
      intro t ht hts
      have hT' : Tendsto (fun i => 𝒩.N ((X i s)⁻¹ * X i t)) 𝒰 (𝓝 (𝒩.N ((Φ s)⁻¹ * Φ t))) :=
        (𝒩.continuous.tendsto _).comp ((hlim s hs).inv.mul (hlim t ht))
      refine le_of_tendsto hT' (Eventually.of_forall fun i => ?_)
      rw [← OneParam.map_neg, ← OneParam.map_add, neg_add_eq_sub]
      exact hX i _ hts
    have h1 : Tendsto (fun t => (Φ s)⁻¹ * Φ t) (𝓝[Set.Icc (-T) T] s) (𝓝 1) := by
      rw [𝒩.tendsto_nhds_one_iff]
      have hz : Tendsto (fun t => L * |t - s|) (𝓝[Set.Icc (-T) T] s) (𝓝 0) := by
        have : Tendsto (fun t => L * |t - s|) (𝓝 s) (𝓝 (L * |s - s|)) :=
          ((continuous_id.sub continuous_const).abs.const_mul _).tendsto s
        simpa using this.mono_left nhdsWithin_le_nhds
      have hnear : ∀ᶠ t in 𝓝[Set.Icc (-T) T] s, |t - s| ≤ T := by
        have : ∀ᶠ t in 𝓝 s, |t - s| < T := by
          have hc : Continuous fun t : ℝ => |t - s| := (continuous_id.sub continuous_const).abs
          exact hc.continuousAt.eventually (gt_mem_nhds (by simpa using hT))
        exact (this.filter_mono nhdsWithin_le_nhds).mono fun _ h => h.le
      refine squeeze_zero' (Eventually.of_forall fun t => 𝒩.nonneg _) ?_ hz
      filter_upwards [self_mem_nhdsWithin, hnear] with t ht hts
      exact hdiff t ht hts
    have h2 := (tendsto_const_nhds (x := Φ s)).mul h1
    simp only [mul_inv_cancel_left, mul_one] at h2
    exact h2
  obtain ⟨Y, hY⟩ := OneParam.exists_extend hT hadd hcont
  exact ⟨Y, fun t ht => by rw [hY ht]; exact hlim t ht,
    fun t ht => by rw [hY ht]; exact hbound t ht⟩

end WeakGleasonNorm

end HSFormal.GY

end
