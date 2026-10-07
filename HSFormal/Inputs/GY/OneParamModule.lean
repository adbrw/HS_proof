import HSFormal.Inputs.GY.OneParamAdd

/-!
# `L(G)` is a real vector space (B3b)

For a Gleason norm `𝒢` on a locally compact Hausdorff topological group `G`, the one-parameter
subgroups `LieAlg 𝒢 = OneParam G` form a real vector space:

* `instance : AddCommGroup (LieAlg 𝒢)` and `instance : Module ℝ (LieAlg 𝒢)`, with
  `(X + Y) t = lim (X(t/n) Y(t/n))ⁿ` (`OneParam.add`), `(c • X) t = X (c t)`, `(-X) t = X (-t)`,
  `0 t = 1`;
* `LieAlg.conj g : LieAlg 𝒢 →ₗ[ℝ] LieAlg 𝒢`, `(conj g X) t = g X(t) g⁻¹`.

Every axiom is reduced to the uniqueness of Trotter sums (`OneParam.add_eq_of_isTrotterSum`):
`zero_add`, `neg_add_cancel`, `add_smul` hold because the defining sequences are eventually
constant, `add_comm` because `(Y X)ⁿ` is `(X Y)ⁿ` conjugated by `X(t/n) → 1`, `smul_add` and the
linearity of `conj` because rescaling and conjugation commute with Trotter limits, and `add_assoc`
because both `((X+Y)(s) Z(s))ⁿ` and `(X(s) (Y+Z)(s))ⁿ`, `s = t/n`, are `O(1/n)`-close to
`(X(s) Y(s) Z(s))ⁿ` (local Prop 22 `GleasonNorm.d_mul_add_le_sq`, approximate right invariance, and
Lemma 16(b)).
-/

noncomputable section

namespace HSFormal.GY

open Filter Topology

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace OneParam

/-! ## Trotter sums that need no estimates -/

theorem tendsto_apply_div_nhds_one (X : OneParam G) (t : ℝ) :
    Tendsto (fun n : ℕ => X (t / n)) atTop (𝓝 1) := by
  have h0 := (X.continuous.tendsto 0).comp (tendsto_const_div_atTop_nhds_zero_nat t)
  rw [OneParam.map_zero] at h0
  exact h0

theorem pow_apply_div (X : OneParam G) {n : ℕ} (hn : n ≠ 0) (t : ℝ) : X (t / n) ^ n = X t := by
  rw [← map_natCast_mul, mul_div_cancel₀ _ (by exact_mod_cast hn)]

/-- An eventually constant Trotter sequence. -/
theorem isTrotterSum_of_eventually {X Y Z : OneParam G}
    (h : ∀ t, ∀ n : ℕ, n ≠ 0 → trotterSeq X Y n t = Z t) : IsTrotterSum X Y Z :=
  ⟨1, one_pos, fun t _ => tendsto_const_nhds.congr'
    ((eventually_ne_atTop 0).mono fun n hn => (h t n hn).symm)⟩

theorem isTrotterSum_one_left (X : OneParam G) : IsTrotterSum one X X :=
  isTrotterSum_of_eventually fun t n hn => by
    rw [trotterSeq_def, one_apply, one_mul, pow_apply_div X hn]

theorem isTrotterSum_one_right (X : OneParam G) : IsTrotterSum X one X :=
  isTrotterSum_of_eventually fun t n hn => by
    rw [trotterSeq_def, one_apply, mul_one, pow_apply_div X hn]

theorem isTrotterSum_neg_left (X : OneParam G) : IsTrotterSum (rescale (-1) X) X one :=
  isTrotterSum_of_eventually fun t n _ => by
    rw [trotterSeq_def, rescale_apply, neg_one_mul, OneParam.map_neg, inv_mul_cancel, one_pow,
      one_apply]

theorem isTrotterSum_rescale_add (X : OneParam G) (a b : ℝ) :
    IsTrotterSum (rescale a X) (rescale b X) (rescale (a + b) X) :=
  isTrotterSum_of_eventually fun t n hn => by
    rw [trotterSeq_def, rescale_apply, rescale_apply, ← OneParam.map_add, ← add_mul,
      rescale_apply, mul_div_assoc', pow_apply_div X hn]

theorem rescale_zero (X : OneParam G) : rescale 0 X = one := by
  ext t; simp

theorem rescale_one (X : OneParam G) : rescale 1 X = X := by
  ext t; simp

theorem rescale_rescale (a b : ℝ) (X : OneParam G) :
    rescale a (rescale b X) = rescale (b * a) X := by
  ext t; simp [mul_assoc]

theorem trotterSeq_swap (X Y : OneParam G) (n : ℕ) (t : ℝ) :
    trotterSeq Y X n t = (X (t / n))⁻¹ * trotterSeq X Y n t * X (t / n) := by
  rw [trotterSeq_def, trotterSeq_def]
  have h := conj_pow (a := (X (t / n))⁻¹) (b := X (t / n) * Y (t / n)) (i := n)
  rw [inv_inv] at h
  rw [← h]
  congr 1
  group

theorem IsTrotterSum.swap [IsTopologicalGroup G] {X Y Z : OneParam G} (h : IsTrotterSum X Y Z) :
    IsTrotterSum Y X Z := by
  obtain ⟨T, hT, hZ⟩ := h
  refine ⟨T, hT, fun t ht => ?_⟩
  have hX := X.tendsto_apply_div_nhds_one t
  have := ((hX.inv.mul (hZ t ht)).mul hX)
  rw [inv_one, one_mul, mul_one] at this
  exact this.congr fun n => (trotterSeq_swap X Y n t).symm

theorem trotterSeq_conj [ContinuousMul G] (g : G) (X Y : OneParam G) (n : ℕ) (t : ℝ) :
    trotterSeq (conj g X) (conj g Y) n t = g * trotterSeq X Y n t * g⁻¹ := by
  rw [trotterSeq_def, trotterSeq_def, conj_apply, conj_apply, ← conj_pow]
  congr 1
  group

theorem IsTrotterSum.conj [IsTopologicalGroup G] {X Y Z : OneParam G} (h : IsTrotterSum X Y Z)
    (g : G) : IsTrotterSum (conj g X) (conj g Y) (conj g Z) := by
  obtain ⟨T, hT, hZ⟩ := h
  refine ⟨T, hT, fun t ht => ?_⟩
  have := (tendsto_const_nhds (x := g)).mul (hZ t ht) |>.mul (tendsto_const_nhds (x := g⁻¹))
  exact this.congr fun n => (trotterSeq_conj g X Y n t).symm

/-! ## Algebraic identities for `OneParam.add` -/

variable [T2Space G]

theorem one_add (X : OneParam G) : add one X = X :=
  add_eq_of_isTrotterSum (isTrotterSum_one_left X)

theorem add_one (X : OneParam G) : add X one = X :=
  add_eq_of_isTrotterSum (isTrotterSum_one_right X)

theorem neg_add_cancel (X : OneParam G) : add (rescale (-1) X) X = one :=
  add_eq_of_isTrotterSum (isTrotterSum_neg_left X)

theorem rescale_add_rescale (X : OneParam G) (a b : ℝ) :
    add (rescale a X) (rescale b X) = rescale (a + b) X :=
  add_eq_of_isTrotterSum (isTrotterSum_rescale_add X a b)

theorem add_comm_of_exists [IsTopologicalGroup G] {X Y : OneParam G}
    (h : ∃ Z, IsTrotterSum X Y Z) : add Y X = add X Y :=
  add_eq_of_isTrotterSum (isTrotterSum_add h).swap

theorem rescale_add_of_exists {X Y : OneParam G} (h : ∃ Z, IsTrotterSum X Y Z) (c : ℝ) :
    add (rescale c X) (rescale c Y) = rescale c (add X Y) := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [rescale_zero, rescale_zero, rescale_zero, one_add]
  · exact add_eq_of_isTrotterSum ((isTrotterSum_add h).rescale hc)

theorem conj_add_of_exists [IsTopologicalGroup G] {X Y : OneParam G}
    (h : ∃ Z, IsTrotterSum X Y Z) (g : G) : add (conj g X) (conj g Y) = conj g (add X Y) :=
  add_eq_of_isTrotterSum ((isTrotterSum_add h).conj g)

end OneParam

/-! ## Associativity -/

namespace GleasonNorm

open OneParam

variable {𝒢 : GleasonNorm G}

/-- `X` is `L`-Lipschitz on `[-T, T]` for `𝒢`. -/
def IsLip (𝒢 : GleasonNorm G) (X : OneParam G) (T L : ℝ) : Prop :=
  ∀ s, |s| ≤ T → 𝒢.N (X s) ≤ L * |s|

theorem IsLip.mono {X : OneParam G} {T L T' L' : ℝ} (h : 𝒢.IsLip X T L) (hT : T' ≤ T)
    (hL : L ≤ L') : 𝒢.IsLip X T' L' := fun s hs =>
  (h s (hs.trans hT)).trans (mul_le_mul_of_nonneg_right hL (abs_nonneg s))

/-- Finitely many one-parameter subgroups are uniformly Lipschitz near `0`, with `L T` as small as
we like. -/
theorem exists_isLip_list (𝒢 : GleasonNorm G) (l : List (OneParam G)) {ε : ℝ} (hε : 0 < ε) :
    ∃ T > 0, ∃ L ≥ 0, L * T ≤ ε ∧ ∀ X ∈ l, 𝒢.IsLip X T L := by
  induction l with
  | nil => exact ⟨1, one_pos, 0, le_rfl, by simp [hε.le], by simp⟩
  | cons X l ih =>
    obtain ⟨T₁, hT₁, L₁, hL₁, h₁⟩ := 𝒢.oneParam_lipschitz X
    obtain ⟨T₂, hT₂, L₂, hL₂, -, h₂⟩ := ih
    set L := max L₁ L₂
    have hL : 0 ≤ L := le_max_of_le_left hL₁
    refine ⟨min (min T₁ T₂) (ε / (L + 1)), lt_min (lt_min hT₁ hT₂) (by positivity), L, hL, ?_, ?_⟩
    · calc L * min (min T₁ T₂) (ε / (L + 1)) ≤ L * (ε / (L + 1)) := by
            gcongr; exact min_le_right _ _
        _ ≤ ε := by rw [mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
    · intro Y hY
      rcases List.mem_cons.1 hY with rfl | hY
      · exact IsLip.mono h₁ ((min_le_left _ _).trans (min_le_left _ _)) (le_max_left _ _)
      · exact (h₂ Y hY).mono ((min_le_left _ _).trans (min_le_right _ _)) (le_max_right _ _)

private theorem tendsto_zero_of_le_div {f : ℕ → ℝ} (K : ℝ) (h0 : ∀ n, 0 ≤ f n)
    (h : ∀ n : ℕ, 1 ≤ n → f n ≤ K / n) : Tendsto f atTop (𝓝 0) :=
  squeeze_zero' (Eventually.of_forall h0) ((eventually_ge_atTop 1).mono h)
    (tendsto_const_div_atTop_nhds_zero_nat K)

/-- Smallness bookkeeping: for `0 ≤ x ≤ (16 C²)⁻¹`. -/
private theorem small_facts (𝒢 : GleasonNorm G) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ (16 * 𝒢.C ^ 2)⁻¹) :
    x ≤ 𝒢.C⁻¹ ∧ 4 * 𝒢.C * x ^ 2 ≤ 𝒢.C⁻¹ ∧ 3 * x ≤ (4 * 𝒢.C ^ 2)⁻¹ ∧
      x ≤ (8 * 𝒢.C ^ 2)⁻¹ := by
  have hC := 𝒢.C_pos
  have hC1 := 𝒢.one_le_C
  have hCx : 𝒢.C * x ≤ 1 / 16 := by
    have : 𝒢.C * x ≤ 𝒢.C * (16 * 𝒢.C ^ 2)⁻¹ := by gcongr
    have e : 𝒢.C * (16 * 𝒢.C ^ 2)⁻¹ = (16 * 𝒢.C)⁻¹ := by field_simp
    rw [e] at this
    exact this.trans (by rw [one_div]; exact inv_anti₀ (by norm_num) (by linarith))
  have h16 : (16 * 𝒢.C ^ 2)⁻¹ ≤ 𝒢.C⁻¹ := inv_anti₀ hC (by nlinarith)
  have h1 : x ≤ 𝒢.C⁻¹ := hx.trans h16
  refine ⟨h1, ?_, ?_, hx.trans (inv_anti₀ (by positivity) (by nlinarith))⟩
  · calc 4 * 𝒢.C * x ^ 2 = 4 * (𝒢.C * x) * x := by ring
      _ ≤ 4 * (1 / 16) * x := by gcongr
      _ ≤ 𝒢.C⁻¹ := by linarith
  · have e : 3 * (16 * 𝒢.C ^ 2)⁻¹ = 3 / 4 * (4 * 𝒢.C ^ 2)⁻¹ := by field_simp; ring
    have : 0 ≤ (4 * 𝒢.C ^ 2)⁻¹ := by positivity
    linarith

/-- **Associativity** of the Trotter sum: both `((X+Y)(s) Z(s))ⁿ` and `(X(s) (Y+Z)(s))ⁿ`, `s = t/n`,
are `O(1/n)`-close to `(X(s) Y(s) Z(s))ⁿ`. -/
theorem add_assoc' [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] (𝒢 : GleasonNorm G)
    (X Y Z : OneParam G) : add (add X Y) Z = add X (add Y Z) := by
  have hC := 𝒢.C_pos
  set W := add X Y with hW_def
  set V := add Y Z with hV_def
  obtain ⟨T, hT, L, hL, hLT, hlip⟩ :=
    𝒢.exists_isLip_list [X, Y, Z, W, V] (ε := (16 * 𝒢.C ^ 2)⁻¹) (by positivity)
  have hX : 𝒢.IsLip X T L := hlip X (by simp)
  have hY : 𝒢.IsLip Y T L := hlip Y (by simp)
  have hZ : 𝒢.IsLip Z T L := hlip Z (by simp)
  have hW : 𝒢.IsLip W T L := hlip W (by simp)
  have hV : 𝒢.IsLip V T L := hlip V (by simp)
  obtain ⟨-, -, hL3, hL8⟩ := small_facts 𝒢 (mul_nonneg hL hT.le) hLT
  have key : ∀ t, |t| ≤ T → ∀ n : ℕ, 1 ≤ n →
      𝒢.d (trotterSeq W Z n t) ((X (t / n) * Y (t / n) * Z (t / n)) ^ n) ≤
        16 * 𝒢.C * L ^ 2 * t ^ 2 / n ∧
      𝒢.d (trotterSeq X V n t) ((X (t / n) * Y (t / n) * Z (t / n)) ^ n) ≤
        8 * 𝒢.C * L ^ 2 * t ^ 2 / n := by
    intro t ht n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    set s := t / n with hs_def
    have hs_abs : |s| = |t| / n := by rw [hs_def, abs_div, Nat.abs_cast]
    have hsT : |s| ≤ T := by rw [hs_abs]; exact (div_le_self (abs_nonneg t) hn1).trans ht
    have hLs : L * |s| ≤ (16 * 𝒢.C ^ 2)⁻¹ := le_trans (by gcongr) hLT
    obtain ⟨hLsC, hLs2, -, -⟩ := small_facts 𝒢 (mul_nonneg hL (abs_nonneg s)) hLs
    have nX := hX s hsT
    have nY := hY s hsT
    have nZ := hZ s hsT
    have nW := hW s hsT
    have nV := hV s hsT
    have hnLs : (n : ℝ) * (L * |s|) = L * |t| := by rw [hs_abs]; field_simp
    have hLt : L * |t| ≤ L * T := by gcongr
    have hsq : 4 * 𝒢.C * L ^ 2 * s ^ 2 = 4 * 𝒢.C * (L * |s|) ^ 2 := by rw [mul_pow, sq_abs]; ring
    have p22W : 𝒢.d (X s * Y s) (W s) ≤ 4 * 𝒢.C * L ^ 2 * s ^ 2 :=
      𝒢.d_mul_add_le_sq hL hX hY hL8 hsT
    have p22V : 𝒢.d (Y s * Z s) (V s) ≤ 4 * 𝒢.C * L ^ 2 * s ^ 2 :=
      𝒢.d_mul_add_le_sq hL hY hZ hL8 hsT
    have hd1 : 𝒢.d (W s * Z s) (X s * Y s * Z s) ≤ 2 * (4 * 𝒢.C * L ^ 2 * s ^ 2) := by
      have hWXY : 𝒢.d (W s) (X s * Y s) ≤ 𝒢.C⁻¹ := by
        rw [𝒢.d_comm]; exact p22W.trans (hsq ▸ hLs2)
      have h1 := 𝒢.d_mul_right_le hWXY (nZ.trans hLsC)
      have hCZ : 1 + 𝒢.C * 𝒢.N (Z s) ≤ 2 := by
        have : 𝒢.C * 𝒢.N (Z s) ≤ 𝒢.C * 𝒢.C⁻¹ := by gcongr; exact nZ.trans hLsC
        rw [mul_inv_cancel₀ hC.ne'] at this; linarith
      have h0 := 𝒢.d_nonneg (X s * Y s) (W s)
      calc 𝒢.d (W s * Z s) (X s * Y s * Z s)
          ≤ (1 + 𝒢.C * 𝒢.N (Z s)) * 𝒢.d (W s) (X s * Y s) := h1
        _ ≤ 2 * (4 * 𝒢.C * L ^ 2 * s ^ 2) := by
            rw [𝒢.d_comm (W s)]; gcongr
    have hd2 : 𝒢.d (X s * V s) (X s * Y s * Z s) ≤ 4 * 𝒢.C * L ^ 2 * s ^ 2 := by
      rw [mul_assoc (X s), 𝒢.d_mul_left, 𝒢.d_comm]; exact p22V
    have hNb : (n : ℝ) * 𝒢.N (X s * Y s * Z s) ≤ (4 * 𝒢.C ^ 2)⁻¹ := by
      have := 𝒢.mul_le (X s * Y s) (Z s)
      have := 𝒢.mul_le (X s) (Y s)
      calc (n : ℝ) * 𝒢.N (X s * Y s * Z s) ≤ n * (3 * (L * |s|)) := by gcongr; linarith
        _ = 3 * (L * |t|) := by rw [← hnLs]; ring
        _ ≤ 3 * (L * T) := by gcongr
        _ ≤ (4 * 𝒢.C ^ 2)⁻¹ := hL3
    have hNa : ∀ A : OneParam G, 𝒢.N (A s) ≤ L * |s| → ∀ B : OneParam G,
        𝒢.N (B s) ≤ L * |s| → (n : ℝ) * 𝒢.N (A s * B s) ≤ (4 * 𝒢.C ^ 2)⁻¹ := by
      intro A hA B hB
      have := 𝒢.mul_le (A s) (B s)
      have h3 : 0 ≤ L * |t| := mul_nonneg hL (abs_nonneg t)
      calc (n : ℝ) * 𝒢.N (A s * B s) ≤ n * (2 * (L * |s|)) := by gcongr; linarith
        _ = 2 * (L * |t|) := by rw [← hnLs]; ring
        _ ≤ 3 * (L * T) := by linarith
        _ ≤ (4 * 𝒢.C ^ 2)⁻¹ := hL3
    have hp1 := 𝒢.d_pow_le_mul_d (hNa W nW Z nZ) hNb
    have hp2 := 𝒢.d_pow_le_mul_d (hNa X nX V nV) hNb
    have hs2 : (n : ℝ) * s ^ 2 = t ^ 2 / n := by rw [hs_def]; field_simp
    constructor
    · rw [trotterSeq_def]
      calc 𝒢.d ((W s * Z s) ^ n) ((X s * Y s * Z s) ^ n)
          ≤ 2 * n * 𝒢.d (W s * Z s) (X s * Y s * Z s) := hp1
        _ ≤ 2 * n * (2 * (4 * 𝒢.C * L ^ 2 * s ^ 2)) := by gcongr
        _ = 16 * 𝒢.C * L ^ 2 * (n * s ^ 2) := by ring
        _ = 16 * 𝒢.C * L ^ 2 * t ^ 2 / n := by rw [hs2]; ring
    · rw [trotterSeq_def]
      calc 𝒢.d ((X s * V s) ^ n) ((X s * Y s * Z s) ^ n)
          ≤ 2 * n * 𝒢.d (X s * V s) (X s * Y s * Z s) := hp2
        _ ≤ 2 * n * (4 * 𝒢.C * L ^ 2 * s ^ 2) := by gcongr
        _ = 8 * 𝒢.C * L ^ 2 * (n * s ^ 2) := by ring
        _ = 8 * 𝒢.C * L ^ 2 * t ^ 2 / n := by rw [hs2]; ring
  obtain ⟨TS, hTS, hS⟩ := isTrotterSum_add (𝒢.exists_isTrotterSum W Z)
  symm
  refine add_eq_of_isTrotterSum ⟨min T TS, lt_min hT hTS, fun t ht => ?_⟩
  have htT : |t| ≤ T := abs_le.2 ⟨le_trans (neg_le_neg (min_le_left _ _)) ht.1,
    ht.2.trans (min_le_left _ _)⟩
  have htS : t ∈ Set.Icc (-TS) TS :=
    ⟨le_trans (neg_le_neg (min_le_right _ _)) ht.1, ht.2.trans (min_le_right _ _)⟩
  have h1 : Tendsto (fun n : ℕ => (X (t / n) * Y (t / n) * Z (t / n)) ^ n) atTop
      (𝓝 (add W Z t)) :=
    𝒢.tendsto_of_tendsto_d (hS t htS) (tendsto_zero_of_le_div _ (fun n => 𝒢.d_nonneg _ _)
      fun n hn => (key t htT n hn).1)
  exact 𝒢.tendsto_of_tendsto_d h1 (tendsto_zero_of_le_div _ (fun n => 𝒢.d_nonneg _ _)
    fun n hn => by rw [𝒢.d_comm]; exact (key t htT n hn).2)

end GleasonNorm

/-! ## The vector space `LieAlg 𝒢` -/

namespace LieAlg

open OneParam

section Basic

variable {𝒢 : GleasonNorm G}

@[simp] theorem map_neg (X : LieAlg 𝒢) (t : ℝ) : X (-t) = (X t)⁻¹ := OneParam.map_neg X t

theorem map_sub (X : LieAlg 𝒢) (s t : ℝ) : X (s - t) = X s * (X t)⁻¹ := OneParam.map_sub X s t

theorem map_natCast_mul (X : LieAlg 𝒢) (n : ℕ) (t : ℝ) : X (n * t) = X t ^ n :=
  OneParam.map_natCast_mul X n t

theorem map_intCast_mul (X : LieAlg 𝒢) (n : ℤ) (t : ℝ) : X (n * t) = X t ^ n :=
  OneParam.map_intCast_mul X n t

theorem commute (X : LieAlg 𝒢) (s t : ℝ) : Commute (X s) (X t) := OneParam.commute X s t

@[simp] theorem toOneParam_apply (X : LieAlg 𝒢) (t : ℝ) : toOneParam X t = X t := rfl

end Basic

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] {𝒢 : GleasonNorm G}

theorem isTrotterSum_add (X Y : LieAlg 𝒢) :
    IsTrotterSum (toOneParam X) (toOneParam Y) (toOneParam (X + Y)) :=
  OneParam.isTrotterSum_add (𝒢.exists_isTrotterSum _ _)

instance : AddCommGroup (LieAlg 𝒢) where
  add := (· + ·)
  zero := 0
  neg := Neg.neg
  add_assoc X Y Z := 𝒢.add_assoc' (toOneParam X) (toOneParam Y) (toOneParam Z)
  zero_add X := OneParam.one_add (toOneParam X)
  add_zero X := OneParam.add_one (toOneParam X)
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel X := OneParam.neg_add_cancel (toOneParam X)
  add_comm X Y := OneParam.add_comm_of_exists (𝒢.exists_isTrotterSum (toOneParam Y) (toOneParam X))

instance : Module ℝ (LieAlg 𝒢) where
  smul := (· • ·)
  one_smul X := LieAlg.ext fun t => by simp
  mul_smul a b X := LieAlg.ext fun t => by simp only [smul_apply]; ring_nf
  smul_zero c := LieAlg.ext fun t => by simp
  smul_add c X Y :=
    (OneParam.rescale_add_of_exists (𝒢.exists_isTrotterSum (toOneParam X) (toOneParam Y)) c).symm
  add_smul a b X := (OneParam.rescale_add_rescale (toOneParam X) a b).symm
  zero_smul X := LieAlg.ext fun t => by simp

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
theorem natCast_smul_apply (n : ℕ) (X : LieAlg 𝒢) (t : ℝ) : ((n : ℝ) • X) t = X t ^ n := by
  rw [smul_apply]; exact OneParam.map_natCast_mul (toOneParam X) n t

/-- Conjugation acts linearly on `L(G)`. -/
def conj (g : G) : LieAlg 𝒢 →ₗ[ℝ] LieAlg 𝒢 where
  toFun X := ofOneParam (OneParam.conj g (toOneParam X))
  map_add' X Y :=
    (OneParam.conj_add_of_exists (𝒢.exists_isTrotterSum (toOneParam X) (toOneParam Y)) g).symm
  map_smul' _ _ := LieAlg.ext fun _ => rfl

@[simp] theorem conj_apply (g : G) (X : LieAlg 𝒢) (t : ℝ) : conj g X t = g * X t * g⁻¹ := rfl

end LieAlg

end HSFormal.GY

end
