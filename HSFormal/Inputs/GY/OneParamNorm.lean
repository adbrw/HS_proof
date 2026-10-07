import HSFormal.Inputs.GY.OneParamModule
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The norm on `L(G)`, bilipschitz estimates and finite dimension (B4)

For a Gleason norm `𝒢` on a locally compact Hausdorff topological group `G`:

* `‖X‖ = ⨆ t > 0, N (X t) / t` (`WeakGleasonNorm.oneParamNorm`) makes `LieAlg 𝒢` a real normed
  space (`NormedAddCommGroup.ofCore`), with `LieAlg.N_apply_le : N (X t) ≤ ‖X‖ * |t|`;
* `LieAlg.exists_bilipschitz` (blueprint H4): for `‖X‖, ‖Y‖ ≤ r₀ = (8C²)⁻¹`,
  `(4C)⁻¹ ‖X - Y‖ ≤ d(X 1, Y 1) ≤ 2 ‖X - Y‖`;
* closed balls of small radius are compact (ultralimits of uniformly Lipschitz one-parameter
  subgroups, `WeakGleasonNorm.exists_ultralimit_oneParam`), hence
  `instance : FiniteDimensional ℝ (LieAlg 𝒢)` (Riesz, `FiniteDimensional.of_isCompact_closedBall₀`);
* `LieAlg.continuous_exp : Continuous fun X : LieAlg 𝒢 => X 1`.
-/

noncomputable section

namespace HSFormal.GY

open Filter Topology

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace WeakGleasonNorm

variable (𝒩 : WeakGleasonNorm G)

/-- A Lipschitz bound near `0` propagates to all times: `X t = X (t / k) ^ k`. -/
theorem N_le_of_isLip {X : OneParam G} {T L : ℝ} (hT : 0 < T)
    (hX : ∀ s, |s| ≤ T → 𝒩.N (X s) ≤ L * |s|) (t : ℝ) : 𝒩.N (X t) ≤ L * |t| := by
  obtain ⟨k, hk⟩ := exists_nat_gt (|t| / T)
  have hk0 : (0 : ℝ) < k := lt_of_le_of_lt (div_nonneg (abs_nonneg t) hT.le) hk
  have hs : |t / k| ≤ T := by
    rw [abs_div, Nat.abs_cast, div_le_iff₀ hk0]
    rw [div_lt_iff₀ hT] at hk; linarith
  have e : X t = X (t / k) ^ k := by rw [← OneParam.map_natCast_mul, mul_div_cancel₀ _ hk0.ne']
  rw [e]
  calc 𝒩.N (X (t / k) ^ k) ≤ k * 𝒩.N (X (t / k)) := 𝒩.N_pow_le _ _
    _ ≤ k * (L * |t / k|) := by gcongr; exact hX _ hs
    _ = L * |t| := by rw [abs_div, Nat.abs_cast]; field_simp

theorem exists_N_le_mul_abs (X : OneParam G) : ∃ L ≥ 0, ∀ t, 𝒩.N (X t) ≤ L * |t| := by
  obtain ⟨T, hT, L, hL, h⟩ := 𝒩.oneParam_lipschitz X
  exact ⟨L, hL, 𝒩.N_le_of_isLip hT h⟩

/-- Tao's norm on `L(G)`: `‖X‖ = sup_{t > 0} N (X t) / t`. -/
def oneParamNorm (X : OneParam G) : ℝ := ⨆ t : Set.Ioi (0 : ℝ), 𝒩.N (X t) / t

instance : Nonempty (Set.Ioi (0 : ℝ)) := ⟨⟨1, Set.mem_Ioi.2 one_pos⟩⟩

theorem bddAbove_oneParamNorm (X : OneParam G) :
    BddAbove (Set.range fun t : Set.Ioi (0 : ℝ) => 𝒩.N (X t) / t) := by
  obtain ⟨L, -, h⟩ := 𝒩.exists_N_le_mul_abs X
  refine ⟨L, ?_⟩
  rintro _ ⟨⟨t, ht⟩, rfl⟩
  have h1 := h t
  have ht' : (0 : ℝ) < t := ht
  rw [abs_of_pos ht'] at h1
  show 𝒩.N (X t) / t ≤ L
  rwa [div_le_iff₀ ht']

theorem N_le_oneParamNorm_mul (X : OneParam G) (t : ℝ) :
    𝒩.N (X t) ≤ 𝒩.oneParamNorm X * |t| := by
  rcases lt_trichotomy t 0 with h | rfl | h
  · have h' : (0 : ℝ) < -t := neg_pos.2 h
    have := le_ciSup (𝒩.bddAbove_oneParamNorm X) ⟨-t, h'⟩
    simp only at this
    rw [div_le_iff₀ h', OneParam.map_neg, 𝒩.N_inv] at this
    rwa [abs_of_neg h]
  · simp
  · have := le_ciSup (𝒩.bddAbove_oneParamNorm X) ⟨t, h⟩
    simp only at this
    rw [div_le_iff₀ h] at this
    rwa [abs_of_pos h]

theorem oneParamNorm_le {X : OneParam G} {L : ℝ} (h : ∀ t, 0 < t → 𝒩.N (X t) ≤ L * t) :
    𝒩.oneParamNorm X ≤ L :=
  ciSup_le fun ⟨t, ht⟩ => by
    have ht' : (0 : ℝ) < t := ht
    show 𝒩.N (X t) / t ≤ L
    rw [div_le_iff₀ ht']; exact h t ht'

theorem oneParamNorm_nonneg (X : OneParam G) : 0 ≤ 𝒩.oneParamNorm X :=
  le_trans (by simpa using 𝒩.nonneg (X 1))
    (le_ciSup (𝒩.bddAbove_oneParamNorm X) ⟨1, Set.mem_Ioi.2 one_pos⟩)

end WeakGleasonNorm

/-! ## The normed space `LieAlg 𝒢` -/

namespace LieAlg

open OneParam

variable {𝒢 : GleasonNorm G}

instance : Norm (LieAlg 𝒢) := ⟨fun X => 𝒢.oneParamNorm (toOneParam X)⟩

theorem norm_def (X : LieAlg 𝒢) : ‖X‖ = 𝒢.oneParamNorm (toOneParam X) := rfl

/-- `N (X t) ≤ ‖X‖ |t|` (blueprint `LieAlg.N_apply_le`). -/
theorem N_apply_le (X : LieAlg 𝒢) (t : ℝ) : 𝒢.N (X t) ≤ ‖X‖ * |t| :=
  𝒢.N_le_oneParamNorm_mul (toOneParam X) t

theorem norm_le_of_forall {X : LieAlg 𝒢} {L : ℝ} (h : ∀ t, 0 < t → 𝒢.N (X t) ≤ L * t) :
    ‖X‖ ≤ L :=
  𝒢.oneParamNorm_le h

theorem norm_le_of_forall_abs {X : LieAlg 𝒢} {L : ℝ} (h : ∀ t, 𝒢.N (X t) ≤ L * |t|) : ‖X‖ ≤ L :=
  norm_le_of_forall fun t ht => by simpa [abs_of_pos ht] using h t

theorem norm_nonneg' (X : LieAlg 𝒢) : 0 ≤ ‖X‖ := 𝒢.oneParamNorm_nonneg (toOneParam X)

theorem norm_zero' : ‖(0 : LieAlg 𝒢)‖ = 0 :=
  le_antisymm (norm_le_of_forall fun t _ => by simp) (norm_nonneg' _)

theorem norm_smul_le' (c : ℝ) (X : LieAlg 𝒢) : ‖c • X‖ ≤ |c| * ‖X‖ :=
  norm_le_of_forall fun t ht => by
    rw [smul_apply]
    refine (N_apply_le X (c * t)).trans (le_of_eq ?_)
    rw [abs_mul, abs_of_pos ht]; ring

theorem norm_smul' (c : ℝ) (X : LieAlg 𝒢) : ‖c • X‖ = |c| * ‖X‖ := by
  refine le_antisymm (norm_smul_le' c X) ?_
  rcases eq_or_ne c 0 with rfl | hc
  · simp [norm_nonneg']
  have e : c⁻¹ • c • X = X := LieAlg.ext fun t => by
    rw [smul_apply, smul_apply, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  have h := norm_smul_le' c⁻¹ (c • X)
  rw [e, abs_inv] at h
  have hc' : 0 < |c| := abs_pos.2 hc
  rw [inv_mul_eq_div, le_div_iff₀ hc'] at h
  linarith

theorem eq_zero_of_norm_eq_zero {X : LieAlg 𝒢} (h : ‖X‖ = 0) : X = 0 :=
  LieAlg.ext fun t => by
    have := N_apply_le X t
    rw [h, zero_mul] at this
    rw [zero_apply]
    exact 𝒢.eq_one _ (le_antisymm this (𝒢.nonneg _))

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]

theorem N_add_apply_le (X Y : LieAlg 𝒢) (t : ℝ) : 𝒢.N ((X + Y) t) ≤ (‖X‖ + ‖Y‖) * |t| := by
  obtain ⟨T, hT, hS⟩ := isTrotterSum_add X Y
  refine 𝒢.N_le_of_isLip hT (fun s hs => ?_) t
  have hlim := hS s (abs_le.1 hs)
  refine le_of_tendsto ((𝒢.continuous.tendsto _).comp hlim) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  show 𝒢.N (trotterSeq (toOneParam X) (toOneParam Y) n s) ≤ (‖X‖ + ‖Y‖) * |s|
  rw [trotterSeq_def]
  have h1 := 𝒢.N_pow_le (X (s / n) * Y (s / n)) n
  have h2 := 𝒢.mul_le (X (s / n)) (Y (s / n))
  have h3 := N_apply_le X (s / n)
  have h4 := N_apply_le Y (s / n)
  rw [abs_div, Nat.abs_cast] at h3 h4
  calc 𝒢.N ((X (s / n) * Y (s / n)) ^ n) ≤ n * (‖X‖ * (|s| / n) + ‖Y‖ * (|s| / n)) := by
        refine h1.trans ?_; gcongr; linarith
    _ = (‖X‖ + ‖Y‖) * |s| := by field_simp

theorem norm_add_le' (X Y : LieAlg 𝒢) : ‖X + Y‖ ≤ ‖X‖ + ‖Y‖ :=
  norm_le_of_forall_abs (N_add_apply_le X Y)

theorem normedSpaceCore : NormedSpace.Core ℝ (LieAlg 𝒢) where
  norm_nonneg := norm_nonneg'
  norm_smul c X := by rw [norm_smul', Real.norm_eq_abs]
  norm_triangle := norm_add_le'
  norm_eq_zero_iff X := ⟨eq_zero_of_norm_eq_zero, fun h => h ▸ norm_zero'⟩

instance : NormedAddCommGroup (LieAlg 𝒢) := NormedAddCommGroup.ofCore normedSpaceCore

instance : NormedSpace ℝ (LieAlg 𝒢) := NormedSpace.ofCore normedSpaceCore

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
@[simp] theorem norm_neg_apply_le (X : LieAlg 𝒢) (t : ℝ) : 𝒢.N ((-X) t) ≤ ‖X‖ * |t| := by
  rw [neg_apply, map_neg, 𝒢.N_inv]; exact N_apply_le X t

/-! ## Bilipschitz estimates (blueprint H4) -/

/-- **Lower bilipschitz bound**: `‖X - Y‖ ≤ 4C d(X 1, Y 1)` for `‖X‖, ‖Y‖ ≤ (8C²)⁻¹`. -/
theorem norm_sub_le_d {X Y : LieAlg 𝒢} (hX : ‖X‖ ≤ (8 * 𝒢.C ^ 2)⁻¹)
    (hY : ‖Y‖ ≤ (8 * 𝒢.C ^ 2)⁻¹) : ‖X - Y‖ ≤ 4 * 𝒢.C * 𝒢.d (X 1) (Y 1) := by
  have hC := 𝒢.C_pos
  have hC1 := 𝒢.one_le_C
  set r₀ : ℝ := (8 * 𝒢.C ^ 2)⁻¹ with hr₀_def
  set D := 𝒢.d (X 1) (Y 1) with hD_def
  have hD : 0 ≤ D := 𝒢.d_nonneg _ _
  have hr0 : 0 ≤ r₀ := by positivity
  have hr4 : r₀ ≤ (4 * 𝒢.C ^ 2)⁻¹ := inv_anti₀ (by positivity) (by nlinarith)
  have hrC : 2 * r₀ ≤ 𝒢.C⁻¹ := by
    have e : 2 * r₀ = (4 * 𝒢.C ^ 2)⁻¹ := by rw [hr₀_def]; field_simp; norm_num
    rw [e]; exact inv_anti₀ hC (by nlinarith)
  have lipX : ∀ s, |s| ≤ 1 → 𝒢.N (toOneParam X s) ≤ r₀ * |s| := fun s _ =>
    (N_apply_le X s).trans (by gcongr)
  have lipY' : ∀ s, |s| ≤ 1 → 𝒢.N (toOneParam (-Y) s) ≤ r₀ * |s| := fun s _ =>
    (norm_neg_apply_le Y s).trans (by gcongr)
  have hr8 : r₀ * 1 ≤ (8 * 𝒢.C ^ 2)⁻¹ := by rw [mul_one]
  -- `N((X - Y)(1/m)) ≤ 4 C D / m`
  have step : ∀ m : ℕ, 1 ≤ m → 𝒢.N ((X - Y) (1 / m)) ≤ 4 * 𝒢.C * D / m := by
    intro m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have h1m : |(1 : ℝ) / m| ≤ 1 := by
      rw [abs_div, abs_one, Nat.abs_cast]; exact div_le_one_of_le₀ hm1 hm0.le
    have hlim := 𝒢.tendsto_trotter hr0 lipX lipY' hr8 h1m
    have e : OneParam.add (toOneParam X) (toOneParam (-Y)) (1 / m) = (X - Y) (1 / m) := by
      rw [sub_eq_add_neg]; rfl
    rw [e] at hlim
    refine le_of_tendsto ((𝒢.continuous.tendsto _).comp hlim) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hmn0 : (0 : ℝ) < m * n := by positivity
    have hs : (1 : ℝ) / m / n = 1 / (m * n) := by rw [div_div]
    set g := X (1 / (m * n)) with hg_def
    set h := Y (1 / (m * n)) with hh_def
    have eg : toOneParam X ((1 : ℝ) / m / n) = g := by rw [hs]; rfl
    have eh : toOneParam (-Y) ((1 : ℝ) / m / n) = h⁻¹ := by
      show (-Y) _ = _; rw [neg_apply, map_neg, hs]
    show 𝒢.N (trotterSeq (toOneParam X) (toOneParam (-Y)) n (1 / m)) ≤ 4 * 𝒢.C * D / m
    rw [trotterSeq_def, eg, eh]
    have habs : |(1 : ℝ) / (m * n)| = 1 / (m * n) := abs_of_pos (by positivity)
    have hNg : 𝒢.N g ≤ r₀ * (1 / (m * n)) := by
      have := N_apply_le X (1 / (m * n)); rw [habs] at this; exact this.trans (by gcongr)
    have hNh : 𝒢.N h ≤ r₀ * (1 / (m * n)) := by
      have := N_apply_le Y (1 / (m * n)); rw [habs] at this; exact this.trans (by gcongr)
    have hsmall : r₀ * (1 / (m * n)) ≤ r₀ := by
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      rw [mul_one_div]; exact div_le_self hr0 (one_le_mul_of_one_le_of_one_le hm1 hn1)
    -- `N(g h⁻¹) ≤ 2 d(g, h)` (conjugation estimate)
    have hconj : 𝒢.N (g * h⁻¹) ≤ 2 * 𝒢.d g h := by
      have e1 : g * h⁻¹ = h * (h⁻¹ * g) * h⁻¹ := by group
      have hNhC : 𝒢.N h ≤ 𝒢.C⁻¹ := by linarith
      have hdhg : 𝒢.N (h⁻¹ * g) ≤ 𝒢.C⁻¹ := by
        have := 𝒢.mul_le h⁻¹ g; rw [𝒢.N_inv] at this; linarith
      have := 𝒢.N_conj_le hdhg hNhC
      rw [← e1] at this
      have hCh : 1 + 𝒢.C * 𝒢.N h ≤ 2 := by
        have : 𝒢.C * 𝒢.N h ≤ 𝒢.C * 𝒢.C⁻¹ := by gcongr
        rw [mul_inv_cancel₀ hC.ne'] at this; linarith
      have hdd : 𝒢.N (h⁻¹ * g) = 𝒢.d g h := by rw [𝒢.d_comm]; rfl
      calc 𝒢.N (g * h⁻¹) ≤ (1 + 𝒢.C * 𝒢.N h) * 𝒢.N (h⁻¹ * g) := this
        _ ≤ 2 * 𝒢.N (h⁻¹ * g) := by gcongr; exact 𝒢.nonneg _
        _ = 2 * 𝒢.d g h := by rw [hdd]
    -- Lemma 16(b) at power `m n`
    have hgmn : ((m * n : ℕ) : ℝ) * 𝒢.N g ≤ (4 * 𝒢.C ^ 2)⁻¹ := by
      push_cast
      calc (m : ℝ) * n * 𝒢.N g ≤ m * n * (r₀ * (1 / (m * n))) := by gcongr
        _ = r₀ := by field_simp
        _ ≤ (4 * 𝒢.C ^ 2)⁻¹ := hr4
    have hhmn : ((m * n : ℕ) : ℝ) * 𝒢.N h ≤ (4 * 𝒢.C ^ 2)⁻¹ := by
      push_cast
      calc (m : ℝ) * n * 𝒢.N h ≤ m * n * (r₀ * (1 / (m * n))) := by gcongr
        _ = r₀ := by field_simp
        _ ≤ (4 * 𝒢.C ^ 2)⁻¹ := hr4
    have h16 := 𝒢.mul_d_le_d_pow hgmn hhmn
    have egp : g ^ (m * n) = X 1 := by
      rw [hg_def, ← map_natCast_mul]; congr 1; push_cast; field_simp
    have ehp : h ^ (m * n) = Y 1 := by
      rw [hh_def, ← map_natCast_mul]; congr 1; push_cast; field_simp
    rw [egp, ehp] at h16
    push_cast at h16
    have hdgh : 𝒢.d g h ≤ 2 * 𝒢.C * D / (m * n) := by rw [le_div_iff₀ hmn0]; linarith
    calc 𝒢.N ((g * h⁻¹) ^ n) ≤ n * 𝒢.N (g * h⁻¹) := 𝒢.N_pow_le _ _
      _ ≤ n * (2 * (2 * 𝒢.C * D / (m * n))) := by gcongr; linarith
      _ = 4 * 𝒢.C * D / m := by field_simp; ring
  -- all positive times, by density
  have hall : ∀ t, 0 < t → 𝒢.N ((X - Y) t) ≤ 4 * 𝒢.C * D * t := by
    intro t ht
    have hq : Tendsto (fun m : ℕ => (⌊t * m⌋₊ : ℝ) / m) atTop (𝓝 t) :=
      (tendsto_nat_floor_mul_div_atTop ht.le).comp tendsto_natCast_atTop_atTop
    have hcont : Tendsto (fun m : ℕ => 𝒢.N ((X - Y) ((⌊t * m⌋₊ : ℝ) / m))) atTop
        (𝓝 (𝒢.N ((X - Y) t))) :=
      (𝒢.continuous.tendsto _).comp (((X - Y).continuous.tendsto t).comp hq)
    refine le_of_tendsto_of_tendsto hcont (hq.const_mul (4 * 𝒢.C * D)) ?_
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have e : (X - Y) ((⌊t * m⌋₊ : ℝ) / m) = (X - Y) (1 / m) ^ ⌊t * m⌋₊ := by
      rw [← map_natCast_mul]; congr 1; ring
    rw [e]
    calc 𝒢.N ((X - Y) (1 / m) ^ ⌊t * m⌋₊) ≤ ⌊t * m⌋₊ * 𝒢.N ((X - Y) (1 / m)) := 𝒢.N_pow_le _ _
      _ ≤ ⌊t * m⌋₊ * (4 * 𝒢.C * D / m) := by gcongr; exact step m hm
      _ = 4 * 𝒢.C * D * ((⌊t * m⌋₊ : ℝ) / m) := by ring
  exact norm_le_of_forall fun t ht => by
    have := hall t ht; linarith

/-- **Upper bilipschitz bound**: `d(X 1, Y 1) ≤ 2 ‖X - Y‖` for `‖X‖, ‖Y‖ ≤ (8C²)⁻¹`. -/
theorem d_le_norm_sub {X Y : LieAlg 𝒢} (hX : ‖X‖ ≤ (8 * 𝒢.C ^ 2)⁻¹)
    (hY : ‖Y‖ ≤ (8 * 𝒢.C ^ 2)⁻¹) : 𝒢.d (X 1) (Y 1) ≤ 2 * ‖X - Y‖ := by
  have hC := 𝒢.C_pos
  have hC1 := 𝒢.one_le_C
  set r₀ : ℝ := (8 * 𝒢.C ^ 2)⁻¹ with hr₀_def
  have hr0 : 0 ≤ r₀ := by positivity
  have hr4 : r₀ ≤ (4 * 𝒢.C ^ 2)⁻¹ := inv_anti₀ (by positivity) (by nlinarith)
  have lipX' : ∀ s, |s| ≤ 1 → 𝒢.N (toOneParam (-X) s) ≤ r₀ * |s| := fun s _ =>
    (norm_neg_apply_le X s).trans (by gcongr)
  have lipY : ∀ s, |s| ≤ 1 → 𝒢.N (toOneParam Y s) ≤ r₀ * |s| := fun s _ =>
    (N_apply_le Y s).trans (by gcongr)
  have hr8 : r₀ * 1 ≤ (8 * 𝒢.C ^ 2)⁻¹ := by rw [mul_one]
  have hbound : ∀ n : ℕ, 1 ≤ n →
      𝒢.d (X 1) (Y 1) ≤ 2 * ‖X - Y‖ + 8 * 𝒢.C * r₀ ^ 2 / n := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    set s : ℝ := 1 / n with hs_def
    have hs_abs : |s| = 1 / n := abs_of_pos (by positivity)
    have hs1 : |s| ≤ 1 := by rw [hs_abs]; exact div_le_one_of_le₀ hn1 hn0.le
    have e1 : ∀ Z : LieAlg 𝒢, Z s ^ n = Z 1 := fun Z => by
      rw [← map_natCast_mul, hs_def, mul_one_div_cancel hn0.ne']
    have hsmall : ∀ Z : LieAlg 𝒢, ‖Z‖ ≤ r₀ → (n : ℝ) * 𝒢.N (Z s) ≤ (4 * 𝒢.C ^ 2)⁻¹ :=
      fun Z hZ => by
        have := N_apply_le Z s
        rw [hs_abs] at this
        calc (n : ℝ) * 𝒢.N (Z s) ≤ n * (r₀ * (1 / n)) := by gcongr; exact this.trans (by gcongr)
          _ = r₀ := by field_simp
          _ ≤ (4 * 𝒢.C ^ 2)⁻¹ := hr4
    have hb := 𝒢.d_pow_le_mul_d (hsmall X hX) (hsmall Y hY)
    rw [e1, e1] at hb
    -- `d(X s, Y s) = N((-X) s * Y s)` and local Prop 22 for `(-X, Y)`
    have p22 := 𝒢.d_mul_add_le_sq hr0 lipX' lipY hr8 hs1
    have e2 : OneParam.add (toOneParam (-X)) (toOneParam Y) s = (-X + Y) s := rfl
    rw [e2] at p22
    have e3 : 𝒢.d (X s) (Y s) = 𝒢.N ((-X) s * Y s) := by
      rw [WeakGleasonNorm.d_def, neg_apply, map_neg]
    have hnorm : ‖-X + Y‖ = ‖X - Y‖ := by rw [neg_add_eq_sub, norm_sub_rev]
    have hN := N_apply_le (-X + Y) s
    rw [hnorm, hs_abs] at hN
    have htri := 𝒢.d_triangle 1 ((-X + Y) s) ((-X) s * Y s)
    rw [𝒢.d_one_left, 𝒢.d_one_left, 𝒢.d_comm] at htri
    have hds : 𝒢.d (X s) (Y s) ≤ ‖X - Y‖ * (1 / n) + 4 * 𝒢.C * r₀ ^ 2 * s ^ 2 := by
      show 𝒢.d (toOneParam X s) (toOneParam Y s) ≤ _
      rw [show toOneParam X s = X s from rfl, show toOneParam Y s = Y s from rfl, e3]
      have : 𝒢.d (toOneParam (-X) s * toOneParam Y s) ((-X + Y) s) ≤ 4 * 𝒢.C * r₀ ^ 2 * s ^ 2 :=
        p22
      change 𝒢.d ((-X) s * Y s) ((-X + Y) s) ≤ _ at this
      linarith
    calc 𝒢.d (X 1) (Y 1) ≤ 2 * n * 𝒢.d (X s) (Y s) := hb
      _ ≤ 2 * n * (‖X - Y‖ * (1 / n) + 4 * 𝒢.C * r₀ ^ 2 * s ^ 2) := by gcongr
      _ = 2 * ‖X - Y‖ + 8 * 𝒢.C * r₀ ^ 2 / n := by rw [hs_def]; field_simp; ring
  have hR : Tendsto (fun n : ℕ => 2 * ‖X - Y‖ + 8 * 𝒢.C * r₀ ^ 2 / n) atTop
      (𝓝 (2 * ‖X - Y‖ + 0)) :=
    tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat _)
  rw [add_zero] at hR
  exact ge_of_tendsto hR ((eventually_ge_atTop 1).mono hbound)

/-- **Bilipschitz estimate** (blueprint `LieAlg.exists_bilipschitz`), with `r₀ = (8C²)⁻¹`,
`a = (4C)⁻¹`, `A = 2`. -/
theorem exists_bilipschitz : ∃ r₀ > 0, ∃ a > 0, ∃ A, ∀ X Y : LieAlg 𝒢, ‖X‖ ≤ r₀ → ‖Y‖ ≤ r₀ →
    a * ‖X - Y‖ ≤ 𝒢.d (X 1) (Y 1) ∧ 𝒢.d (X 1) (Y 1) ≤ A * ‖X - Y‖ := by
  have hC := 𝒢.C_pos
  refine ⟨(8 * 𝒢.C ^ 2)⁻¹, by positivity, (4 * 𝒢.C)⁻¹, by positivity, 2,
    fun X Y hX hY => ⟨?_, d_le_norm_sub hX hY⟩⟩
  have := norm_sub_le_d hX hY
  rw [inv_mul_le_iff₀ (by positivity)]
  exact this

/-! ## Compact balls and finite dimension -/

/-- Small closed balls of `LieAlg 𝒢` are compact. -/
theorem isCompact_closedBall_of_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ (8 * 𝒢.C ^ 2)⁻¹)
    (hK : IsCompact {g | 𝒢.N g ≤ r}) : IsCompact (Metric.closedBall (0 : LieAlg 𝒢) r) := by
  classical
  rw [isCompact_iff_ultrafilter_le_nhds']
  intro 𝒰 hball
  set F : LieAlg 𝒢 → OneParam G := fun i => if ‖i‖ ≤ r then toOneParam i else OneParam.one
    with hF_def
  have hF : ∀ i t, |t| ≤ 1 → 𝒢.N (F i t) ≤ r * |t| := by
    intro i t _
    by_cases hi : ‖i‖ ≤ r
    · simp only [hF_def, hi, ↓reduceIte]
      exact (N_apply_le i t).trans (by gcongr)
    · simp only [hF_def, hi, ↓reduceIte, OneParam.one_apply, 𝒢.N_one]
      exact mul_nonneg hr0 (abs_nonneg t)
  have hK' : IsCompact {g | 𝒢.N g ≤ r * 1} := by simpa using hK
  obtain ⟨Y, hYlim, hYb⟩ := 𝒢.exists_ultralimit_oneParam 𝒰 F one_pos hK' hF
  set φ : LieAlg 𝒢 := ofOneParam Y with hφ_def
  have hφ : ‖φ‖ ≤ r := norm_le_of_forall_abs fun t =>
    𝒢.N_le_of_isLip one_pos (fun s hs => hYb s (abs_le.1 hs)) t
  refine ⟨φ, mem_closedBall_zero_iff.2 hφ, ?_⟩
  have hd : Tendsto (fun i => 𝒢.d (F i 1) (Y 1)) (𝒰 : Filter (LieAlg 𝒢)) (𝓝 0) := by
    have h := (𝒢.continuous_d_left (Y 1)).continuousAt.tendsto.comp
      (hYlim 1 ⟨by norm_num, le_rfl⟩)
    rw [𝒢.d_self] at h
    exact h
  have hnorm : Tendsto (fun i => ‖i - φ‖) (𝒰 : Filter (LieAlg 𝒢)) (𝓝 0) := by
    have hd' := hd.const_mul (4 * 𝒢.C)
    rw [mul_zero] at hd'
    refine squeeze_zero' (Eventually.of_forall fun i => norm_nonneg _) ?_ hd'
    filter_upwards [hball] with i hi
    have hi' : ‖i‖ ≤ r := mem_closedBall_zero_iff.1 hi
    have hFi : F i = toOneParam i := by simp only [hF_def, hi', ↓reduceIte]
    rw [hFi]
    exact norm_sub_le_d (hi'.trans hr) (hφ.trans hr)
  exact Filter.tendsto_id'.1 (tendsto_iff_norm_sub_tendsto_zero.2 hnorm)

theorem exists_isCompact_closedBall :
    ∃ r > 0, IsCompact (Metric.closedBall (0 : LieAlg 𝒢) r) := by
  obtain ⟨r₀, hr₀, hK⟩ := 𝒢.exists_isCompact_le
  have hC := 𝒢.C_pos
  set r := min r₀ (8 * 𝒢.C ^ 2)⁻¹
  exact ⟨r, lt_min hr₀ (by positivity), isCompact_closedBall_of_le
    (le_min hr₀.le (by positivity)) (min_le_right _ _)
    (𝒢.isCompact_setOf_le_of_le hK (min_le_left _ _))⟩

/-- `L(G)` is finite dimensional (Riesz's theorem). -/
instance : FiniteDimensional ℝ (LieAlg 𝒢) := by
  obtain ⟨r, hr, h⟩ := exists_isCompact_closedBall (𝒢 := 𝒢)
  exact FiniteDimensional.of_isCompact_closedBall₀ ℝ hr h

/-! ## Continuity of the exponential -/

theorem continuousAt_exp_of_norm_lt {X₀ : LieAlg 𝒢} (h : ‖X₀‖ < (8 * 𝒢.C ^ 2)⁻¹) :
    ContinuousAt (fun X : LieAlg 𝒢 => X 1) X₀ := by
  rw [ContinuousAt, 𝒢.tendsto_nhds_iff]
  have hball : ∀ᶠ X in 𝓝 X₀, ‖X‖ < (8 * 𝒢.C ^ 2)⁻¹ :=
    (continuous_norm.tendsto X₀).eventually (gt_mem_nhds h)
  have hlim : Tendsto (fun X : LieAlg 𝒢 => 2 * ‖X₀ - X‖) (𝓝 X₀) (𝓝 0) := by
    have h2 : Continuous fun X : LieAlg 𝒢 => ‖X₀ - X‖ := (continuous_const.sub continuous_id).norm
    have := (h2.tendsto X₀).const_mul 2
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun X => 𝒢.d_nonneg _ _) ?_ hlim
  filter_upwards [hball] with X hX
  exact d_le_norm_sub h.le hX.le

/-- The exponential `X ↦ X 1` is continuous (blueprint `LieAlg.continuous_exp`). -/
theorem continuous_exp : Continuous fun X : LieAlg 𝒢 => X 1 := by
  have hC := 𝒢.C_pos
  refine continuous_iff_continuousAt.2 fun X₀ => ?_
  obtain ⟨k, hk⟩ := exists_nat_gt (‖X₀‖ / (8 * 𝒢.C ^ 2)⁻¹)
  have hk0 : (0 : ℝ) < k := lt_of_le_of_lt (div_nonneg (norm_nonneg _) (by positivity)) hk
  have e : (fun X : LieAlg 𝒢 => X 1) = fun X => ((k : ℝ)⁻¹ • X) 1 ^ k := funext fun X => by
    rw [smul_apply, mul_one, ← map_natCast_mul, mul_inv_cancel₀ hk0.ne']
  rw [e]
  have h1 : ‖(k : ℝ)⁻¹ • X₀‖ < (8 * 𝒢.C ^ 2)⁻¹ := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, Nat.abs_cast, inv_mul_lt_iff₀ hk0]
    rw [div_lt_iff₀ (by positivity)] at hk; linarith
  exact ((continuousAt_exp_of_norm_lt h1).comp (continuous_const_smul _).continuousAt).pow k

end LieAlg

end HSFormal.GY

end
