import HSFormal.Inputs.GY.GleasonEstimates
import HSFormal.Inputs.GY.LocalHom

/-!
# Addition of one-parameter subgroups: the Trotter limit (B3a)

For one-parameter subgroups `X Y : OneParam G` let `trotterSeq X Y n t = (X (t/n) * Y (t/n)) ^ n`.

* `OneParam.IsTrotterSum X Y Z`: `trotterSeq X Y n t → Z t` for all `t` near `0`. In a Hausdorff
  group it determines `Z` (`OneParam.IsTrotterSum.unique`, via `OneParam.ext_of_eqOn`).
* `OneParam.add X Y` is the Trotter sum when it exists (chosen; otherwise `X`). The definition is
  intrinsic to the topological group; `OneParam.add_eq_of_isTrotterSum` characterises it.
* `GleasonNorm.exists_isTrotterSum`: for a Gleason norm on a locally compact Hausdorff group every
  pair `X, Y` has a Trotter sum. The local homomorphism property of the limit comes for free from
  the ultralimit lemma `WeakGleasonNorm.exists_ultralimit` (applied to `x_N = X(1/N) Y(1/N)`,
  `M_N = N`); genuine convergence of the Trotter sequence comes from the Cauchy estimate
  `GleasonNorm.d_pow_pow_mul_pow_le` (Lemma 16(a) then 16(b)) and the time-Lipschitz estimate
  `GleasonNorm.d_trotterSeq_time_le`.
* Quantitative Trotter (`GleasonNorm.d_trotterSeq_add_le`, `GleasonNorm.tendsto_trotter`): if
  `N (X s), N (Y s) ≤ L |s|` for `|s| ≤ T` and `L T ≤ (8C²)⁻¹`, then for `|t| ≤ T` and `n ≥ 1`,
  `d((X(t/n) Y(t/n))ⁿ, (X + Y)(t)) ≤ 4C L² t² / n`. With `n = 1` this is the local form of Prop 22,
  `GleasonNorm.d_mul_add_le_sq`: `d(X s * Y s, (X + Y) s) ≤ 4C L² s²`.
* Prop 22 in the blueprint form: `GleasonNorm.dist_mul_add_le`.
* `LieAlg 𝒢 := OneParam G` with `Zero`, `Neg`, `SMul ℝ` (`(c • X) t = X (c * t)`) and `Add`.
-/

noncomputable section

namespace HSFormal.GY

open Filter Topology

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace OneParam

/-! ## Elementary operations -/

/-- The trivial one-parameter subgroup. -/
def one : OneParam G where
  toFun _ := 1
  map_add' _ _ := (mul_one 1).symm
  continuous' := continuous_const

@[simp] theorem one_apply (t : ℝ) : (one : OneParam G) t = 1 := rfl

/-- Reparametrisation `t ↦ X (c * t)`. -/
def rescale (c : ℝ) (X : OneParam G) : OneParam G where
  toFun t := X (c * t)
  map_add' s t := by rw [mul_add, map_add]
  continuous' := X.continuous.comp (continuous_const.mul continuous_id)

@[simp] theorem rescale_apply (c : ℝ) (X : OneParam G) (t : ℝ) : rescale c X t = X (c * t) := rfl

/-- Conjugate of a one-parameter subgroup. -/
def conj [ContinuousMul G] (g : G) (X : OneParam G) : OneParam G where
  toFun t := g * X t * g⁻¹
  map_add' s t := by rw [map_add]; group
  continuous' := (continuous_const.mul X.continuous).mul continuous_const

@[simp] theorem conj_apply [ContinuousMul G] (g : G) (X : OneParam G) (t : ℝ) :
    conj g X t = g * X t * g⁻¹ := rfl

/-! ## Trotter sequences and Trotter sums -/

/-- The Trotter sequence `(X (t / n) * Y (t / n)) ^ n`. -/
def trotterSeq (X Y : OneParam G) (n : ℕ) (t : ℝ) : G := (X (t / n) * Y (t / n)) ^ n

theorem trotterSeq_def (X Y : OneParam G) (n : ℕ) (t : ℝ) :
    trotterSeq X Y n t = (X (t / n) * Y (t / n)) ^ n := rfl

@[simp] theorem trotterSeq_one (X Y : OneParam G) (t : ℝ) : trotterSeq X Y 1 t = X t * Y t := by
  simp [trotterSeq]

@[simp] theorem trotterSeq_zero_time (X Y : OneParam G) (n : ℕ) : trotterSeq X Y n 0 = 1 := by
  simp [trotterSeq]

theorem trotterSeq_mul (X Y : OneParam G) (k n : ℕ) (t : ℝ) :
    trotterSeq X Y (k * n) t = trotterSeq X Y n (t / k) ^ k := by
  simp only [trotterSeq, ← pow_mul, Nat.cast_mul, div_div]
  rw [mul_comm n k]

theorem trotterSeq_rescale (c : ℝ) (X Y : OneParam G) (n : ℕ) (t : ℝ) :
    trotterSeq (rescale c X) (rescale c Y) n t = trotterSeq X Y n (c * t) := by
  simp only [trotterSeq, rescale_apply, mul_div_assoc]

/-- Trotter sequences at negative times are inverses of conjugates. -/
theorem trotterSeq_neg (X Y : OneParam G) (n : ℕ) (u : ℝ) :
    trotterSeq X Y n (-u) = ((X (u / n))⁻¹ * trotterSeq X Y n u * X (u / n))⁻¹ := by
  rw [trotterSeq_def, trotterSeq_def, neg_div, OneParam.map_neg, OneParam.map_neg]
  have h := conj_pow (a := (X (u / n))⁻¹) (b := X (u / n) * Y (u / n)) (i := n)
  rw [inv_inv] at h
  rw [← h, show (X (u / n))⁻¹ * (X (u / n) * Y (u / n)) * X (u / n) = Y (u / n) * X (u / n) by
    group, ← inv_pow, mul_inv_rev]

theorem continuous_trotterSeq [ContinuousMul G] (X Y : OneParam G) (n : ℕ) :
    Continuous (trotterSeq X Y n) :=
  ((X.continuous.comp (continuous_id.div_const _)).mul
    (Y.continuous.comp (continuous_id.div_const _))).pow n

/-- `Z` is the Trotter sum of `X` and `Y`: `(X (t/n) Y (t/n)) ^ n → Z t` for all `t` near `0`. -/
def IsTrotterSum (X Y Z : OneParam G) : Prop :=
  ∃ T > 0, ∀ t ∈ Set.Icc (-T) T, Tendsto (fun n : ℕ => trotterSeq X Y n t) atTop (𝓝 (Z t))

theorem IsTrotterSum.unique [T2Space G] {X Y Z Z' : OneParam G} (h : IsTrotterSum X Y Z)
    (h' : IsTrotterSum X Y Z') : Z = Z' := by
  obtain ⟨T, hT, hZ⟩ := h
  obtain ⟨T', hT', hZ'⟩ := h'
  refine ext_of_eqOn (lt_min hT hT') fun t ht => ?_
  have h1 : t ∈ Set.Icc (-T) T :=
    ⟨le_trans (neg_le_neg (min_le_left _ _)) ht.1, ht.2.trans (min_le_left _ _)⟩
  have h2 : t ∈ Set.Icc (-T') T' :=
    ⟨le_trans (neg_le_neg (min_le_right _ _)) ht.1, ht.2.trans (min_le_right _ _)⟩
  exact tendsto_nhds_unique (hZ t h1) (hZ' t h2)

/-- The Trotter sum of `X` and `Y` if it exists (it always does for groups with a Gleason norm,
`GleasonNorm.exists_isTrotterSum`), and `X` otherwise. -/
def add (X Y : OneParam G) : OneParam G := by
  classical
  exact if h : ∃ Z, IsTrotterSum X Y Z then h.choose else X

theorem isTrotterSum_add {X Y : OneParam G} (h : ∃ Z, IsTrotterSum X Y Z) :
    IsTrotterSum X Y (add X Y) := by
  classical
  simp only [add, h, ↓reduceDIte]
  exact h.choose_spec

theorem add_eq_of_isTrotterSum [T2Space G] {X Y Z : OneParam G} (h : IsTrotterSum X Y Z) :
    add X Y = Z :=
  (isTrotterSum_add ⟨Z, h⟩).unique h

theorem IsTrotterSum.rescale {X Y Z : OneParam G} (h : IsTrotterSum X Y Z) {c : ℝ} (hc : c ≠ 0) :
    IsTrotterSum (rescale c X) (rescale c Y) (rescale c Z) := by
  obtain ⟨T, hT, hZ⟩ := h
  have hc' : 0 < |c| := abs_pos.2 hc
  refine ⟨T / |c|, div_pos hT hc', fun t ht => ?_⟩
  have hct : c * t ∈ Set.Icc (-T) T := by
    rw [Set.mem_Icc, ← abs_le] at ht ⊢
    rw [abs_mul]
    rwa [le_div_iff₀ hc', mul_comm] at ht
  simpa only [trotterSeq_rescale, rescale_apply] using hZ _ hct

end OneParam

/-! ## Estimates for Trotter sequences -/

namespace GleasonNorm

open OneParam

variable (𝒢 : GleasonNorm G)

private theorem inv8_le_inv : (8 * 𝒢.C ^ 2)⁻¹ ≤ 𝒢.C⁻¹ := by
  have := 𝒢.one_le_C
  exact inv_anti₀ 𝒢.C_pos (by nlinarith)

private theorem two_mul_inv8 : 2 * (8 * 𝒢.C ^ 2)⁻¹ = (4 * 𝒢.C ^ 2)⁻¹ := by
  have := 𝒢.C_pos
  field_simp
  norm_num

variable {X Y : OneParam G} {T L : ℝ}

theorem N_trotterSeq_le (hX : ∀ s, |s| ≤ T → 𝒢.N (X s) ≤ L * |s|)
    (hY : ∀ s, |s| ≤ T → 𝒢.N (Y s) ≤ L * |s|) {t : ℝ} (ht : |t| ≤ T) (n : ℕ) :
    𝒢.N (trotterSeq X Y n t) ≤ 2 * L * |t| := by
  have hLt : 0 ≤ L * |t| := (𝒢.nonneg _).trans (hX t ht)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [trotterSeq, pow_zero, 𝒢.N_one]; linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : |t / n| ≤ T := by
    rw [abs_div, Nat.abs_cast]; exact (div_le_self (abs_nonneg t) hn1).trans ht
  have h1 := 𝒢.N_pow_le (X (t / n) * Y (t / n)) n
  have h2 := 𝒢.mul_le (X (t / n)) (Y (t / n))
  have h3 := hX _ hs
  have h4 := hY _ hs
  rw [abs_div, Nat.abs_cast] at h3 h4
  calc 𝒢.N (trotterSeq X Y n t) ≤ n * (L * (|t| / n) + L * (|t| / n)) := by
        rw [trotterSeq]; refine h1.trans ?_; gcongr; linarith
    _ = 2 * L * |t| := by field_simp; ring

/-- **Cauchy estimate** for Trotter sequences (16(a) at power `m`, then 16(b) at power `n`). -/
theorem d_trotterSeq_mul_le (hL : 0 ≤ L) (hX : ∀ s, |s| ≤ T → 𝒢.N (X s) ≤ L * |s|)
    (hY : ∀ s, |s| ≤ T → 𝒢.N (Y s) ≤ L * |s|) (hLT : L * T ≤ (8 * 𝒢.C ^ 2)⁻¹) {t : ℝ}
    (ht : |t| ≤ T) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    𝒢.d (trotterSeq X Y n t) (trotterSeq X Y (n * m) t) ≤ 4 * 𝒢.C * L ^ 2 * t ^ 2 / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hC := 𝒢.C_pos
  set s : ℝ := t / ((n * m : ℕ) : ℝ) with hs_def
  have hs_eq : s = t / (n * m) := by rw [hs_def]; push_cast; ring
  have habs : |s| = |t| / (n * m) := by rw [hs_eq, abs_div, abs_mul, Nat.abs_cast, Nat.abs_cast]
  have hsT : |s| ≤ T := by
    rw [habs]; exact (div_le_self (abs_nonneg t) (by nlinarith)).trans ht
  have hg := hX s hsT
  have hh := hY s hsT
  rw [habs] at hg hh
  have hLt : L * |t| ≤ (8 * 𝒢.C ^ 2)⁻¹ := le_trans (by gcongr) hLT
  have hmn : (m : ℝ) * n * (L * (|t| / (n * m))) = L * |t| := by field_simp
  have hg' : ((m : ℝ) * n) * 𝒢.N (X s) ≤ (8 * 𝒢.C ^ 2)⁻¹ := by
    calc ((m : ℝ) * n) * 𝒢.N (X s) ≤ (m * n) * (L * (|t| / (n * m))) := by gcongr
      _ ≤ (8 * 𝒢.C ^ 2)⁻¹ := by rw [hmn]; exact hLt
  have hh' : ((m : ℝ) * n) * 𝒢.N (Y s) ≤ (8 * 𝒢.C ^ 2)⁻¹ := by
    calc ((m : ℝ) * n) * 𝒢.N (Y s) ≤ (m * n) * (L * (|t| / (n * m))) := by gcongr
      _ ≤ (8 * 𝒢.C ^ 2)⁻¹ := by rw [hmn]; exact hLt
  have key := 𝒢.d_pow_pow_mul_pow_le hg' hh'
  have e1 : X s ^ m = X (t / n) := by
    rw [← map_natCast_mul, hs_eq]; congr 1; field_simp
  have e2 : Y s ^ m = Y (t / n) := by
    rw [← map_natCast_mul, hs_eq]; congr 1; field_simp
  have e3 : (X s * Y s) ^ (m * n) = trotterSeq X Y (n * m) t := by
    rw [trotterSeq, mul_comm m n]
  rw [e1, e2, e3] at key
  refine key.trans ?_
  have hX0 := 𝒢.nonneg (X s)
  have hY0 := 𝒢.nonneg (Y s)
  calc 4 * 𝒢.C * n * (m : ℝ) ^ 2 * 𝒢.N (X s) * 𝒢.N (Y s)
      ≤ 4 * 𝒢.C * n * (m : ℝ) ^ 2 * (L * (|t| / (n * m))) * (L * (|t| / (n * m))) := by
        gcongr
    _ = 4 * 𝒢.C * L ^ 2 * |t| ^ 2 / n := by field_simp
    _ = 4 * 𝒢.C * L ^ 2 * t ^ 2 / n := by rw [sq_abs]

/-- Pairwise Cauchy estimate. -/
theorem d_trotterSeq_le (hL : 0 ≤ L) (hX : ∀ s, |s| ≤ T → 𝒢.N (X s) ≤ L * |s|)
    (hY : ∀ s, |s| ≤ T → 𝒢.N (Y s) ≤ L * |s|) (hLT : L * T ≤ (8 * 𝒢.C ^ 2)⁻¹) {t : ℝ}
    (ht : |t| ≤ T) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    𝒢.d (trotterSeq X Y n t) (trotterSeq X Y m t) ≤
      4 * 𝒢.C * L ^ 2 * t ^ 2 / n + 4 * 𝒢.C * L ^ 2 * t ^ 2 / m := by
  have h1 := 𝒢.d_trotterSeq_mul_le hL hX hY hLT ht hn hm
  have h2 := 𝒢.d_trotterSeq_mul_le hL hX hY hLT ht hm hn
  rw [mul_comm m n, 𝒢.d_comm] at h2
  linarith [𝒢.d_triangle (trotterSeq X Y n t) (trotterSeq X Y (n * m) t) (trotterSeq X Y m t)]

/-- **Time-Lipschitz estimate**: `d(zₚ(u), zₚ(u')) ≤ 6 L |u - u'|`, uniformly in `p`. -/
theorem d_trotterSeq_time_le (hL : 0 ≤ L) (hX : ∀ s, |s| ≤ T → 𝒢.N (X s) ≤ L * |s|)
    (hY : ∀ s, |s| ≤ T → 𝒢.N (Y s) ≤ L * |s|) (hLT : L * T ≤ (8 * 𝒢.C ^ 2)⁻¹) {p : ℕ}
    (hp : 1 ≤ p) {u u' : ℝ} (hu : |u| ≤ T) (hu' : |u'| ≤ T) (huu : |u - u'| ≤ T) :
    𝒢.d (trotterSeq X Y p u) (trotterSeq X Y p u') ≤ 6 * L * |u - u'| := by
  have hC := 𝒢.C_pos
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have h8 := 𝒢.inv8_le_inv
  set a := X (u / p)
  set b := Y (u / p)
  set a' := X (u' / p)
  set b' := Y (u' / p)
  have hsmall : ∀ w : ℝ, |w| ≤ T → |w / p| ≤ T ∧ |w / p| = |w| / p := fun w hw => by
    rw [abs_div, Nat.abs_cast]; exact ⟨(div_le_self (abs_nonneg w) hp1).trans hw, rfl⟩
  -- the increments
  have hdiff : ∀ Z : OneParam G, (∀ s, |s| ≤ T → 𝒢.N (Z s) ≤ L * |s|) →
      𝒢.d (Z (u / p)) (Z (u' / p)) ≤ L * |u - u'| / p := fun Z hZ => by
    have e : (Z (u / p))⁻¹ * Z (u' / p) = Z ((u' - u) / p) := by
      rw [← OneParam.map_neg, ← OneParam.map_add]; congr 1; ring
    rw [WeakGleasonNorm.d_def, e]
    have hw : |u' - u| ≤ T := by rwa [abs_sub_comm]
    obtain ⟨h1, h2⟩ := hsmall _ hw
    refine (hZ _ h1).trans (le_of_eq ?_)
    rw [h2, abs_sub_comm]; ring
  have hda := hdiff X hX
  have hdb := hdiff Y hY
  have hLuu : L * |u - u'| / p ≤ L * T := by
    rw [div_le_iff₀ hp0]
    calc L * |u - u'| ≤ L * T := by gcongr
      _ ≤ L * T * p := le_mul_of_one_le_right (mul_nonneg hL ((abs_nonneg u).trans hu)) hp1
  have hb : 𝒢.N b ≤ L * (|u| / p) := by
    have := hY _ (hsmall u hu).1; rwa [(hsmall u hu).2] at this
  have hbC : 𝒢.N b ≤ 𝒢.C⁻¹ := by
    refine hb.trans (le_trans ?_ (hLT.trans h8))
    gcongr
    exact (div_le_self (abs_nonneg u) hp1).trans hu
  have hdaC : 𝒢.d a a' ≤ 𝒢.C⁻¹ := hda.trans (hLuu.trans (hLT.trans h8))
  have hstep1 := 𝒢.d_mul_right_le hdaC hbC
  have hCb : 1 + 𝒢.C * 𝒢.N b ≤ 2 := by
    have : 𝒢.C * 𝒢.N b ≤ 𝒢.C * 𝒢.C⁻¹ := by gcongr
    rw [mul_inv_cancel₀ hC.ne'] at this; linarith
  have hstep2 : 𝒢.d (a' * b) (a' * b') = 𝒢.d b b' := 𝒢.d_mul_left _ _ _
  have hprod : 𝒢.d (a * b) (a' * b') ≤ 3 * (L * |u - u'| / p) := by
    have t1 := 𝒢.d_triangle (a * b) (a' * b) (a' * b')
    have : (1 + 𝒢.C * 𝒢.N b) * 𝒢.d a a' ≤ 2 * (L * |u - u'| / p) := by
      have := 𝒢.d_nonneg a a'
      calc (1 + 𝒢.C * 𝒢.N b) * 𝒢.d a a' ≤ 2 * 𝒢.d a a' := by gcongr
        _ ≤ 2 * (L * |u - u'| / p) := by gcongr
    linarith
  -- the outer estimate (16(b), upper bound)
  have hNab : ∀ w : ℝ, |w| ≤ T → (p : ℝ) * 𝒢.N (X (w / p) * Y (w / p)) ≤ (4 * 𝒢.C ^ 2)⁻¹ :=
    fun w hw => by
      obtain ⟨h1, h2⟩ := hsmall w hw
      have hx := hX _ h1
      have hy := hY _ h1
      rw [h2] at hx hy
      have hm := 𝒢.mul_le (X (w / p)) (Y (w / p))
      calc (p : ℝ) * 𝒢.N (X (w / p) * Y (w / p)) ≤ p * (L * (|w| / p) + L * (|w| / p)) := by
            gcongr; linarith
        _ = 2 * (L * |w|) := by field_simp; ring
        _ ≤ 2 * (L * T) := by gcongr
        _ ≤ 2 * (8 * 𝒢.C ^ 2)⁻¹ := by gcongr
        _ = (4 * 𝒢.C ^ 2)⁻¹ := 𝒢.two_mul_inv8
  have hout := 𝒢.d_pow_le_mul_d (hNab u hu) (hNab u' hu')
  rw [trotterSeq_def, trotterSeq_def]
  calc 𝒢.d ((a * b) ^ p) ((a' * b') ^ p) ≤ 2 * p * 𝒢.d (a * b) (a' * b') := hout
    _ ≤ 2 * p * (3 * (L * |u - u'| / p)) := by gcongr
    _ = 6 * L * |u - u'| := by field_simp; ring

/-- In a topological group, if `a_i → z` and `d(a_i, b_i) → 0` then `b_i → z`. -/
theorem tendsto_of_tendsto_d [IsTopologicalGroup G] {ι : Type*} {l : Filter ι} {a b : ι → G}
    {z : G} (ha : Tendsto a l (𝓝 z)) (hd : Tendsto (fun i => 𝒢.d (a i) (b i)) l (𝓝 0)) :
    Tendsto b l (𝓝 z) := by
  have h1 : Tendsto (fun i => (a i)⁻¹ * b i) l (𝓝 1) := 𝒢.tendsto_nhds_one_iff.2 hd
  simpa using ha.mul h1

theorem continuous_d_left [IsTopologicalGroup G] (y : G) : Continuous fun x => 𝒢.d x y :=
  𝒢.continuous.comp (continuous_inv.mul continuous_const)

theorem continuous_d_right [IsTopologicalGroup G] (x : G) : Continuous fun y => 𝒢.d x y :=
  𝒢.continuous.comp (continuous_const.mul continuous_id)

/-- A uniform bound `N (X t) ≤ δ ≤ (2C²)⁻¹` on `[-T, T]` gives the Lipschitz bound
`N (X s) ≤ (2 C δ / T) |s|` there (escape to scale). -/
theorem N_oneParam_le_of_le {X : OneParam G} {T δ : ℝ} (hT : 0 < T)
    (hδ : δ ≤ (2 * 𝒢.C ^ 2)⁻¹) (hX : ∀ t, |t| ≤ T → 𝒢.N (X t) ≤ δ) :
    ∀ s, |s| ≤ T → 𝒢.N (X s) ≤ 2 * 𝒢.C * δ / T * |s| := by
  have hC := 𝒢.C_pos
  have hδ0 : 0 ≤ δ := by simpa using hX 0 (by simp [hT.le])
  intro s hs
  rcases eq_or_ne s 0 with rfl | hs0
  · simp
  have hsa : 0 < |s| := abs_pos.2 hs0
  set n : ℕ := ⌊T / |s|⌋₊ with hn_def
  have hn1 : 1 ≤ n := by rw [hn_def, Nat.one_le_floor_iff, le_div_iff₀ hsa]; linarith
  have hns : (n : ℝ) * |s| ≤ T := by
    have := Nat.floor_le (div_nonneg hT.le hsa.le : 0 ≤ T / |s|)
    rw [← hn_def, le_div_iff₀ hsa] at this; exact this
  have hx : ∀ k : ℕ, 1 ≤ k → k ≤ n → 𝒢.N (X s ^ k) ≤ δ := fun k _ hk => by
    rw [← OneParam.map_natCast_mul]
    refine hX _ ?_
    rw [abs_mul, Nat.abs_cast]
    exact le_trans (by gcongr) hns
  have hesc := 𝒢.N_le_of_pow_le hδ hn1 hx
  have hlt : T / |s| < n + 1 := Nat.lt_floor_add_one _
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  rw [div_lt_iff₀ hsa] at hlt
  refine hesc.trans ?_
  rw [div_le_iff₀ hn0]
  have key : T ≤ 2 * |s| * n := by nlinarith
  have hCδ : 0 ≤ 𝒢.C * δ := by positivity
  calc 𝒢.C * δ = 𝒢.C * δ / T * T := by field_simp
    _ ≤ 𝒢.C * δ / T * (2 * |s| * n) := by gcongr
    _ = 2 * 𝒢.C * δ / T * |s| * n := by ring

/-! ## Existence of Trotter sums -/

/-- Trotter sums exist for one-parameter subgroups that are `L`-Lipschitz on `[-1, 1]` with `L`
small, provided `{N ≤ 2L}` is compact; the Trotter sequence then converges on all of `[-1, 1]`. -/
theorem exists_trotter_of_small [IsTopologicalGroup G] [T2Space G] {X Y : OneParam G} {L : ℝ}
    (hL : 0 ≤ L) (hX : ∀ s, |s| ≤ 1 → 𝒢.N (X s) ≤ L * |s|)
    (hY : ∀ s, |s| ≤ 1 → 𝒢.N (Y s) ≤ L * |s|) (hL8 : 2 * L ≤ (8 * 𝒢.C ^ 2)⁻¹)
    (hK : IsCompact {g | 𝒢.N g ≤ 2 * L}) :
    ∃ Z : OneParam G, ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      Tendsto (fun n : ℕ => trotterSeq X Y n t) atTop (𝓝 (Z t)) := by
  have hC := 𝒢.C_pos
  have hLT : L * 1 ≤ (8 * 𝒢.C ^ 2)⁻¹ := by linarith
  set v : ℕ → G := fun N => X (1 / N) * Y (1 / N) with hv
  set 𝒰 : Ultrafilter ℕ := hyperfilter ℕ
  have hM : Tendsto (fun N : ℕ => N) (𝒰 : Filter ℕ) atTop :=
    (hyperfilter_le_cofinite).trans Nat.cofinite_eq_atTop.le
  have hδ : 2 * L ≤ (2 * 𝒢.C ^ 2)⁻¹ :=
    hL8.trans (inv_anti₀ (by positivity) (by nlinarith))
  have hx : ∀ N : ℕ, ∀ j ≤ N, 𝒢.N (v N ^ j) ≤ 2 * L := by
    intro N j hj
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · rw [Nat.le_zero.1 hj, pow_zero, 𝒢.N_one]; linarith
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have h1 : |(1 : ℝ) / N| ≤ 1 := by
      rw [abs_div, abs_one, Nat.abs_cast]; exact div_le_one_of_le₀ hN1 hN0.le
    have h2 : |(1 : ℝ) / N| = 1 / N := by rw [abs_div, abs_one, Nat.abs_cast]
    have hxN := hX _ h1
    have hyN := hY _ h1
    rw [h2] at hxN hyN
    have hm := 𝒢.mul_le (X (1 / N)) (Y (1 / N))
    have hj' : (j : ℝ) ≤ N := by exact_mod_cast hj
    calc 𝒢.N (v N ^ j) ≤ j * 𝒢.N (v N) := 𝒢.N_pow_le _ _
      _ ≤ N * (L * (1 / N) + L * (1 / N)) := by
          have := 𝒢.nonneg (v N)
          gcongr
          simp only [hv]; linarith
      _ = 2 * L := by field_simp; ring
  obtain ⟨Z, hZlim, -⟩ := 𝒢.exists_ultralimit 𝒰 v (fun N => N) hM hδ hK hx
  -- positive times
  have hpos : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      Tendsto (fun n : ℕ => trotterSeq X Y n t) atTop (𝓝 (Z t)) := by
    rintro t ⟨ht0, ht1⟩
    have htI : t ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith, ht1⟩
    have htT : |t| ≤ 1 := by rw [abs_of_pos ht0]; exact ht1
    set K : ℝ := 4 * 𝒢.C * L ^ 2 * t ^ 2 with hK_def
    set p : ℕ → ℕ := fun N => ⌊t * N⌋₊ with hp_def
    have hpTop : Tendsto p (𝒰 : Filter ℕ) atTop :=
      tendsto_nat_floor_atTop.comp ((tendsto_natCast_atTop_atTop.comp hM).const_mul_atTop ht0)
    have hp1 : ∀ᶠ N in (𝒰 : Filter ℕ), 1 ≤ p N := hpTop.eventually (eventually_ge_atTop 1)
    have hN1 : ∀ᶠ N in (𝒰 : Filter ℕ), 1 ≤ N := hM.eventually (eventually_ge_atTop 1)
    -- `v N ^ ⌊t N⌋ = z_{p N} (p N / N)`
    have hident : ∀ᶠ N in (𝒰 : Filter ℕ),
        v N ^ ⌊t * (N : ℝ)⌋ = trotterSeq X Y (p N) ((p N : ℝ) / N) := by
      filter_upwards [hp1] with N hN
      have hpN0 : ((p N : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show p N ≠ 0 by omega)
      rw [← Int.natCast_floor_eq_floor (by positivity), zpow_natCast, trotterSeq_def]
      simp only [hv]
      congr 3 <;> field_simp
    have h1 : Tendsto (fun N => trotterSeq X Y (p N) ((p N : ℝ) / N)) (𝒰 : Filter ℕ)
        (𝓝 (Z t)) := (hZlim t htI).congr' hident
    -- time-Lipschitz: `d(z_{p N}(p N / N), z_{p N}(t)) ≤ 6 L / N`
    have h2 : Tendsto (fun N => 𝒢.d (trotterSeq X Y (p N) ((p N : ℝ) / N))
        (trotterSeq X Y (p N) t)) (𝒰 : Filter ℕ) (𝓝 0) := by
      have hlim : Tendsto (fun N : ℕ => 6 * L / (N : ℝ)) (𝒰 : Filter ℕ) (𝓝 0) :=
        (tendsto_natCast_atTop_atTop.comp hM).const_div_atTop _
      refine squeeze_zero' (Eventually.of_forall fun N => 𝒢.d_nonneg _ _) ?_ hlim
      filter_upwards [hp1, hN1] with N hpN hN
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
      have hfl := Nat.floor_le (by positivity : 0 ≤ t * N)
      have hfl' := Nat.lt_floor_add_one (t * N)
      have hpN' : ((p N : ℕ) : ℝ) ≤ t * N := hfl
      have hpN'' : t * N < (p N : ℝ) + 1 := hfl'
      have hp0 : (0 : ℝ) ≤ p N := Nat.cast_nonneg _
      have hu : |(p N : ℝ) / N| ≤ 1 := by
        rw [abs_of_nonneg (by positivity), div_le_one hN0]; nlinarith
      have hdiff : |(p N : ℝ) / N - t| ≤ 1 / N := by
        rw [abs_le]; constructor
        · rw [← sub_nonneg]
          have : (p N : ℝ) / N - t + 1 / N = ((p N : ℝ) + 1 - t * N) / N := by field_simp; ring
          rw [show (p N : ℝ) / N - t - -(1 / N) = (p N : ℝ) / N - t + 1 / N by ring, this]
          exact div_nonneg (by linarith) hN0.le
        · rw [← sub_nonneg]
          have : 1 / N - ((p N : ℝ) / N - t) = (1 + (t * N - p N)) / N := by field_simp; ring
          rw [this]; exact div_nonneg (by linarith) hN0.le
      have hdiff1 : |(p N : ℝ) / N - t| ≤ 1 :=
        hdiff.trans (div_le_one_of_le₀ (by exact_mod_cast hN) hN0.le)
      calc 𝒢.d (trotterSeq X Y (p N) ((p N : ℝ) / N)) (trotterSeq X Y (p N) t)
          ≤ 6 * L * |(p N : ℝ) / N - t| :=
            𝒢.d_trotterSeq_time_le hL hX hY hLT hpN hu htT hdiff1
        _ ≤ 6 * L * (1 / N) := by gcongr
        _ = 6 * L / N := by ring
    have h3 : Tendsto (fun N => trotterSeq X Y (p N) t) (𝒰 : Filter ℕ) (𝓝 (Z t)) :=
      𝒢.tendsto_of_tendsto_d h1 h2
    -- the error bound `d(z_n t, Z t) ≤ K / n`
    have hbound : ∀ n : ℕ, 1 ≤ n → 𝒢.d (trotterSeq X Y n t) (Z t) ≤ K / n := by
      intro n hn
      have hR : Tendsto (fun N => K / n + K / (p N : ℝ) + 𝒢.d (trotterSeq X Y (p N) t) (Z t))
          (𝒰 : Filter ℕ) (𝓝 (K / n + 0 + 𝒢.d (Z t) (Z t))) :=
        (tendsto_const_nhds.add ((tendsto_natCast_atTop_atTop.comp hpTop).const_div_atTop K)).add
          ((𝒢.continuous_d_left (Z t)).continuousAt.tendsto.comp h3)
      rw [𝒢.d_self, add_zero, add_zero] at hR
      refine le_of_tendsto_of_tendsto tendsto_const_nhds hR ?_
      filter_upwards [hp1] with N hpN
      have hc := 𝒢.d_trotterSeq_le hL hX hY hLT htT hn hpN
      linarith [𝒢.d_triangle (trotterSeq X Y n t) (trotterSeq X Y (p N) t) (Z t)]
    rw [𝒢.tendsto_nhds_iff]
    refine squeeze_zero' (Eventually.of_forall fun n => 𝒢.d_nonneg _ _) ?_
      (tendsto_const_div_atTop_nhds_zero_nat K)
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [𝒢.d_comm]; exact hbound n hn
  refine ⟨Z, fun t ht => ?_⟩
  rcases lt_trichotomy t 0 with hneg | rfl | hpos'
  · -- negative times: conjugation by `X (u / n) → 1`, `u = -t`
    obtain ⟨u, rfl⟩ : ∃ u, t = -u := ⟨-t, (neg_neg t).symm⟩
    have hu0 : 0 < u := by linarith
    have hlim := hpos u ⟨hu0, by linarith [ht.1]⟩
    have hXn : Tendsto (fun n : ℕ => X (u / n)) atTop (𝓝 1) := by
      have h0 := (X.continuous.tendsto 0).comp (tendsto_const_div_atTop_nhds_zero_nat u)
      rw [OneParam.map_zero] at h0
      exact h0
    have hconj : Tendsto (fun n : ℕ => ((X (u / n))⁻¹ * trotterSeq X Y n u * X (u / n))⁻¹)
        atTop (𝓝 ((1⁻¹ * Z u * 1)⁻¹)) := ((hXn.inv.mul hlim).mul hXn).inv
    rw [inv_one, one_mul, mul_one, ← OneParam.map_neg] at hconj
    exact hconj.congr fun n => (trotterSeq_neg X Y n u).symm
  · simp
  · exact hpos t ⟨hpos', ht.2⟩

include 𝒢 in
/-- **Existence of Trotter sums** (B3a). -/
theorem exists_isTrotterSum [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (X Y : OneParam G) : ∃ Z, IsTrotterSum X Y Z := by
  have hC := 𝒢.C_pos
  obtain ⟨T₁, hT₁, L₁, hL₁, h₁⟩ := 𝒢.oneParam_lipschitz X
  obtain ⟨T₂, hT₂, L₂, hL₂, h₂⟩ := 𝒢.oneParam_lipschitz Y
  obtain ⟨r₀, hr₀, hK⟩ := 𝒢.exists_isCompact_le
  set L := max L₁ L₂ with hL_def
  have hL0 : 0 ≤ L := le_max_of_le_left hL₁
  set ε : ℝ := min (16 * 𝒢.C ^ 2)⁻¹ (r₀ / 2) with hε_def
  have hε : 0 < ε := lt_min (by positivity) (half_pos hr₀)
  set c : ℝ := min (min T₁ T₂) (ε / (L + 1)) with hc_def
  have hc : 0 < c := lt_min (lt_min hT₁ hT₂) (by positivity)
  have hLc : L * c ≤ ε := by
    calc L * c ≤ L * (ε / (L + 1)) := by gcongr; exact min_le_right _ _
      _ ≤ ε := by
          rw [mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
  have hlip : ∀ Z : OneParam G, ∀ T' L', 0 < T' → c ≤ T' → L' ≤ L →
      (∀ s, |s| ≤ T' → 𝒢.N (Z s) ≤ L' * |s|) →
      ∀ s, |s| ≤ 1 → 𝒢.N (OneParam.rescale c Z s) ≤ (L * c) * |s| := by
    intro Z T' L' _ hcT hL' hZ s hs
    have hcs : |c * s| ≤ T' := by
      rw [abs_mul, abs_of_pos hc]
      calc c * |s| ≤ c * 1 := by gcongr
        _ ≤ T' := by linarith
    rw [OneParam.rescale_apply]
    refine (hZ _ hcs).trans ?_
    rw [abs_mul, abs_of_pos hc]
    have := abs_nonneg s
    calc L' * (c * |s|) ≤ L * (c * |s|) := by gcongr
      _ = L * c * |s| := by ring
  have hX' := hlip X T₁ L₁ hT₁ ((min_le_left _ _).trans (min_le_left _ _)) (le_max_left _ _) h₁
  have hY' := hlip Y T₂ L₂ hT₂ ((min_le_left _ _).trans (min_le_right _ _)) (le_max_right _ _) h₂
  have h8 : 2 * (L * c) ≤ (8 * 𝒢.C ^ 2)⁻¹ := by
    have : ε ≤ (16 * 𝒢.C ^ 2)⁻¹ := min_le_left _ _
    have e : 2 * (16 * 𝒢.C ^ 2)⁻¹ = (8 * 𝒢.C ^ 2)⁻¹ := by field_simp; norm_num
    linarith
  have hr : 2 * (L * c) ≤ r₀ := by
    have : ε ≤ r₀ / 2 := min_le_right _ _
    linarith
  obtain ⟨Z', hZ'⟩ := 𝒢.exists_trotter_of_small (mul_nonneg hL0 hc.le) hX' hY' h8
    (𝒢.isCompact_setOf_le_of_le hK hr)
  refine ⟨OneParam.rescale c⁻¹ Z', c, hc, fun t ht => ?_⟩
  have htI : c⁻¹ * t ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [Set.mem_Icc, ← abs_le] at ht ⊢
    rw [abs_mul, abs_of_pos (inv_pos.2 hc), inv_mul_le_iff₀ hc, mul_one]; exact ht
  have := hZ' _ htI
  simp only [trotterSeq_rescale, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at this
  simpa using this

/-! ## Quantitative Trotter formula and Prop 22 -/

/-- **Quantitative Trotter formula.** If `X, Y` are `L`-Lipschitz on `[-T, T]` with
`L T ≤ (8C²)⁻¹`, then `d((X(t/n) Y(t/n))ⁿ, (X + Y) t) ≤ 4C L² t² / n` for `|t| ≤ T`, `n ≥ 1`. -/
theorem d_trotterSeq_add_le [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (hL : 0 ≤ L) (hX : ∀ s, |s| ≤ T → 𝒢.N (X s) ≤ L * |s|)
    (hY : ∀ s, |s| ≤ T → 𝒢.N (Y s) ≤ L * |s|) (hLT : L * T ≤ (8 * 𝒢.C ^ 2)⁻¹) {t : ℝ}
    (ht : |t| ≤ T) {n : ℕ} (hn : 1 ≤ n) :
    𝒢.d (trotterSeq X Y n t) (OneParam.add X Y t) ≤ 4 * 𝒢.C * L ^ 2 * t ^ 2 / n := by
  obtain ⟨T₀, hT₀, hW⟩ := isTrotterSum_add (𝒢.exists_isTrotterSum X Y)
  set W := OneParam.add X Y
  set K : ℝ := 4 * 𝒢.C * L ^ 2 * t ^ 2
  obtain ⟨k, hk⟩ := exists_nat_gt (|t| / T₀)
  have hk0 : (0 : ℝ) < k := lt_of_le_of_lt (div_nonneg (abs_nonneg t) hT₀.le) hk
  have hk1 : 1 ≤ k := by exact_mod_cast hk0
  have htk : t / k ∈ Set.Icc (-T₀) T₀ := by
    rw [Set.mem_Icc, ← abs_le, abs_div, Nat.abs_cast, div_le_iff₀ hk0]
    rw [div_lt_iff₀ hT₀] at hk; linarith
  have hsub : Tendsto (fun n' : ℕ => trotterSeq X Y (k * n') t) atTop (𝓝 (W t)) := by
    have := (hW _ htk).pow k
    rw [← OneParam.map_natCast_mul, mul_div_cancel₀ _ hk0.ne'] at this
    simpa only [trotterSeq_mul] using this
  have hR : Tendsto (fun n' : ℕ => K / n + K / ((k * n' : ℕ) : ℝ) +
      𝒢.d (trotterSeq X Y (k * n') t) (W t)) atTop (𝓝 (K / n + 0 + 𝒢.d (W t) (W t))) := by
    refine (tendsto_const_nhds.add ?_).add
      ((𝒢.continuous_d_left (W t)).continuousAt.tendsto.comp hsub)
    exact (tendsto_natCast_atTop_atTop.comp
      (tendsto_id.const_mul_atTop' (by omega : 0 < k))).const_div_atTop K
  rw [𝒢.d_self, add_zero, add_zero] at hR
  refine le_of_tendsto_of_tendsto tendsto_const_nhds hR ?_
  filter_upwards [eventually_ge_atTop 1] with n' hn'
  have hkn : 1 ≤ k * n' := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hc := 𝒢.d_trotterSeq_le hL hX hY hLT ht hn hkn
  linarith [𝒢.d_triangle (trotterSeq X Y n t) (trotterSeq X Y (k * n') t) (W t)]

/-- **Trotter formula** for the sum (blueprint `LieAlg.tendsto_trotter`). -/
theorem tendsto_trotter [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (hL : 0 ≤ L) (hX : ∀ s, |s| ≤ T → 𝒢.N (X s) ≤ L * |s|)
    (hY : ∀ s, |s| ≤ T → 𝒢.N (Y s) ≤ L * |s|) (hLT : L * T ≤ (8 * 𝒢.C ^ 2)⁻¹) {t : ℝ}
    (ht : |t| ≤ T) :
    Tendsto (fun n : ℕ => trotterSeq X Y n t) atTop (𝓝 (OneParam.add X Y t)) := by
  rw [𝒢.tendsto_nhds_iff]
  refine squeeze_zero' (Eventually.of_forall fun n => 𝒢.d_nonneg _ _) ?_
    (tendsto_const_div_atTop_nhds_zero_nat (4 * 𝒢.C * L ^ 2 * t ^ 2))
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [𝒢.d_comm]; exact 𝒢.d_trotterSeq_add_le hL hX hY hLT ht hn

/-- Local form of **Prop 22**: `d(X t * Y t, (X + Y) t) ≤ 4C L² t²`. -/
theorem d_mul_add_le_sq [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (hL : 0 ≤ L) (hX : ∀ s, |s| ≤ T → 𝒢.N (X s) ≤ L * |s|)
    (hY : ∀ s, |s| ≤ T → 𝒢.N (Y s) ≤ L * |s|) (hLT : L * T ≤ (8 * 𝒢.C ^ 2)⁻¹) {t : ℝ}
    (ht : |t| ≤ T) : 𝒢.d (X t * Y t) (OneParam.add X Y t) ≤ 4 * 𝒢.C * L ^ 2 * t ^ 2 := by
  have := 𝒢.d_trotterSeq_add_le hL hX hY hLT ht le_rfl
  simpa using this

/-- **Prop 22** (blueprint `LieAlg.dist_mul_add_le`), with `δ = (16 C³)⁻¹` and `A = 2C³`. -/
theorem dist_mul_add_le [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] :
    ∃ δ > 0, ∃ A, ∀ X Y : OneParam G,
      (∀ t ∈ Set.Icc (-1 : ℝ) 1, 𝒢.N (X t) ≤ δ ∧ 𝒢.N (Y t) ≤ δ) →
      𝒢.d (X 1 * Y 1) (OneParam.add X Y 1) ≤ A * 𝒢.N (X 1) * 𝒢.N (Y 1) := by
  have hC := 𝒢.C_pos
  have hC1 := 𝒢.one_le_C
  refine ⟨(16 * 𝒢.C ^ 3)⁻¹, by positivity, 2 * 𝒢.C ^ 3, fun X Y hXY => ?_⟩
  set δ : ℝ := (16 * 𝒢.C ^ 3)⁻¹ with hδ_def
  have hδ2 : δ ≤ (2 * 𝒢.C ^ 2)⁻¹ := inv_anti₀ (by positivity) (by nlinarith)
  set L : ℝ := 2 * 𝒢.C * δ / 1 with hL_def
  have hLval : L = (8 * 𝒢.C ^ 2)⁻¹ := by rw [hL_def, hδ_def]; field_simp; ring
  have hL0 : 0 ≤ L := by rw [hLval]; positivity
  have hX := 𝒢.N_oneParam_le_of_le one_pos hδ2 fun t ht => (hXY t (abs_le.1 ht)).1
  have hY := 𝒢.N_oneParam_le_of_le one_pos hδ2 fun t ht => (hXY t (abs_le.1 ht)).2
  have hLT : L * 1 ≤ (8 * 𝒢.C ^ 2)⁻¹ := by rw [mul_one, hLval]
  have hlim := 𝒢.tendsto_trotter hL0 hX hY hLT (t := 1) (by simp)
  have hR : Tendsto (fun n : ℕ => 𝒢.d (X 1 * Y 1) (trotterSeq X Y n 1)) atTop
      (𝓝 (𝒢.d (X 1 * Y 1) (OneParam.add X Y 1))) :=
    (𝒢.continuous_d_right _).continuousAt.tendsto.comp hlim
  refine le_of_tendsto hR ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1n : |(1 : ℝ) / n| ≤ 1 := by
    rw [abs_div, abs_one, Nat.abs_cast]; exact div_le_one_of_le₀ hn1 hn0.le
  have hsmall : ∀ Z : OneParam G, (∀ s, |s| ≤ 1 → 𝒢.N (Z s) ≤ L * |s|) →
      (n : ℝ) * 𝒢.N (Z (1 / n)) ≤ 𝒢.C⁻¹ := fun Z hZ => by
    have := hZ _ h1n
    rw [abs_div, abs_one, Nat.abs_cast] at this
    calc (n : ℝ) * 𝒢.N (Z (1 / n)) ≤ n * (L * (1 / n)) := by gcongr
      _ = L := by field_simp
      _ ≤ 𝒢.C⁻¹ := by rw [hLval]; exact 𝒢.inv8_le_inv
  have key := 𝒢.d_pow_mul_pow_le_pow (hsmall X hX) (hsmall Y hY)
  have e : ∀ Z : OneParam G, Z (1 / n) ^ n = Z 1 := fun Z => by
    rw [← OneParam.map_natCast_mul, mul_one_div_cancel hn0.ne']
  rw [e X, e Y] at key
  simpa [trotterSeq_def] using key

end GleasonNorm

/-! ## The type `LieAlg 𝒢` -/

/-- Tao's `L(G)`: the one-parameter subgroups of `G`, as a type synonym indexed by the Gleason norm
`𝒢` (the algebra instances of B3b use `𝒢` in their proofs). -/
def LieAlg (_𝒢 : GleasonNorm G) : Type _ := OneParam G

namespace LieAlg

variable {𝒢 : GleasonNorm G}

instance : FunLike (LieAlg 𝒢) ℝ G := inferInstanceAs (FunLike (OneParam G) ℝ G)

/-- View a one-parameter subgroup as an element of `LieAlg 𝒢`. -/
def ofOneParam (X : OneParam G) : LieAlg 𝒢 := X

/-- The underlying one-parameter subgroup. -/
def toOneParam (X : LieAlg 𝒢) : OneParam G := X

@[simp] theorem coe_toOneParam (X : LieAlg 𝒢) : ⇑(toOneParam X) = ⇑X := rfl

@[simp] theorem coe_ofOneParam (X : OneParam G) : ⇑(ofOneParam X : LieAlg 𝒢) = ⇑X := rfl

@[ext] theorem ext {X Y : LieAlg 𝒢} (h : ∀ t, X t = Y t) : X = Y := DFunLike.ext _ _ h

theorem map_add (X : LieAlg 𝒢) (s t : ℝ) : X (s + t) = X s * X t := OneParam.map_add X s t

@[simp] theorem map_zero (X : LieAlg 𝒢) : X 0 = 1 := OneParam.map_zero X

theorem continuous (X : LieAlg 𝒢) : Continuous X := OneParam.continuous X

instance : Zero (LieAlg 𝒢) := ⟨ofOneParam OneParam.one⟩

instance : Neg (LieAlg 𝒢) := ⟨fun X => ofOneParam (OneParam.rescale (-1) (toOneParam X))⟩

instance : SMul ℝ (LieAlg 𝒢) := ⟨fun c X => ofOneParam (OneParam.rescale c (toOneParam X))⟩

instance : Add (LieAlg 𝒢) :=
  ⟨fun X Y => ofOneParam (OneParam.add (toOneParam X) (toOneParam Y))⟩

@[simp] theorem zero_apply (t : ℝ) : (0 : LieAlg 𝒢) t = 1 := rfl

@[simp] theorem neg_apply (X : LieAlg 𝒢) (t : ℝ) : (-X) t = X (-t) := by
  change X (-1 * t) = X (-t); rw [neg_one_mul]

@[simp] theorem smul_apply (c : ℝ) (X : LieAlg 𝒢) (t : ℝ) : (c • X) t = X (c * t) := rfl

theorem add_def (X Y : LieAlg 𝒢) :
    X + Y = ofOneParam (OneParam.add (toOneParam X) (toOneParam Y)) := rfl

theorem add_apply (X Y : LieAlg 𝒢) (t : ℝ) :
    (X + Y) t = OneParam.add (toOneParam X) (toOneParam Y) t := rfl

end LieAlg

end HSFormal.GY

end
