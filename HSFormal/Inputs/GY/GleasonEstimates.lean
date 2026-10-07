import HSFormal.Inputs.GY.Defs

/-!
# Gleason norms: conjugation, commutation and power estimates (B1)

Tao 254A Notes 2, §3: for a Gleason norm `𝒢` (constant `C`, metric `d g h = N (g⁻¹ * h)`):

* `GleasonNorm.N_conj_le`: `N (h * g * h⁻¹) ≤ (1 + C N h) N g`, from `h g h⁻¹ = g · [g, h⁻¹]`;
* `GleasonNorm.d_mul_right_le`: approximate right invariance `d(ak, bk) ≤ (1 + C N k) d(a, b)`;
* `GleasonNorm.d_mul_comm_le`: Tao (2), `d(gh, hg) ≤ C N g N h`;
* `GleasonNorm.d_pow_mul_pow_le`: Lemma 16(a), `d(gⁿhⁿ, (gh)ⁿ) ≤ 2C n² N g N h`;
* `GleasonNorm.mul_d_le_d_pow` and `GleasonNorm.d_pow_le_mul_d`: Lemma 16(b),
  `n d(g,h) ≤ 2C d(gⁿ,hⁿ)` and `d(gⁿ,hⁿ) ≤ 2n d(g,h)`;
* `GleasonNorm.exists_pow_estimates`: the blueprint's packaged form, with `ε₀ = (4C²)⁻¹`, `A = 2C`;
* `GleasonNorm.d_pow_mul_pow_le_pow`: Lemma 16(a) + escape, `d(aⁿbⁿ, (ab)ⁿ) ≤ 2C³ N(aⁿ) N(bⁿ)`
  (the form needed for Prop 22);
* `GleasonNorm.d_pow_pow_mul_pow_le`: 16(a) at power `m` then 16(b) at power `n`,
  `d((gᵐhᵐ)ⁿ, (gh)^(mn)) ≤ 4C n m² N g N h` (the Cauchy estimate of the Trotter limit, B3a).

All smallness hypotheses are explicit (`N g ≤ C⁻¹`, `n N g ≤ C⁻¹`, or `n N g ≤ (4C²)⁻¹`), and the
hypothesis `1 ≤ n` of the blueprint is only kept in `exists_pow_estimates`.
-/

noncomputable section

namespace HSFormal.GY

namespace GleasonNorm

variable {G : Type*} [Group G] [TopologicalSpace G] (𝒢 : GleasonNorm G)

/-- Conjugation estimate: `h g h⁻¹ = g · (g⁻¹ h g h⁻¹)` and the second factor is Tao's commutator
`[g, h⁻¹]`. -/
theorem N_conj_le {g h : G} (hg : 𝒢.N g ≤ 𝒢.C⁻¹) (hh : 𝒢.N h ≤ 𝒢.C⁻¹) :
    𝒢.N (h * g * h⁻¹) ≤ (1 + 𝒢.C * 𝒢.N h) * 𝒢.N g := by
  have h1 := 𝒢.commutator g h⁻¹ hg (by rwa [𝒢.N_inv])
  have h2 := 𝒢.mul_le g (g⁻¹ * h⁻¹⁻¹ * g * h⁻¹)
  rw [show g * (g⁻¹ * h⁻¹⁻¹ * g * h⁻¹) = h * g * h⁻¹ by group] at h2
  rw [𝒢.N_inv] at h1
  nlinarith

/-- Conjugation estimate, other side. -/
theorem N_conj_le' {g h : G} (hg : 𝒢.N g ≤ 𝒢.C⁻¹) (hh : 𝒢.N h ≤ 𝒢.C⁻¹) :
    𝒢.N (h⁻¹ * g * h) ≤ (1 + 𝒢.C * 𝒢.N h) * 𝒢.N g := by
  have := 𝒢.N_conj_le hg (h := h⁻¹) (by rwa [𝒢.N_inv])
  rwa [inv_inv, 𝒢.N_inv] at this

/-- Approximate right invariance of `d`. -/
theorem d_mul_right_le {a b k : G} (hab : 𝒢.d a b ≤ 𝒢.C⁻¹) (hk : 𝒢.N k ≤ 𝒢.C⁻¹) :
    𝒢.d (a * k) (b * k) ≤ (1 + 𝒢.C * 𝒢.N k) * 𝒢.d a b := by
  have := 𝒢.N_conj_le' hab hk
  simp only [WeakGleasonNorm.d_def] at this ⊢
  rwa [show (a * k)⁻¹ * (b * k) = k⁻¹ * (a⁻¹ * b) * k by group]

/-- Approximate conjugation invariance of `d`. -/
theorem d_conj_le {a b k : G} (hab : 𝒢.d a b ≤ 𝒢.C⁻¹) (hk : 𝒢.N k ≤ 𝒢.C⁻¹) :
    𝒢.d (k * a * k⁻¹) (k * b * k⁻¹) ≤ (1 + 𝒢.C * 𝒢.N k) * 𝒢.d a b := by
  have := 𝒢.N_conj_le hab hk
  simp only [WeakGleasonNorm.d_def] at this ⊢
  rwa [show (k * a * k⁻¹)⁻¹ * (k * b * k⁻¹) = k * (a⁻¹ * b) * k⁻¹ by group]

/-- Tao (2): `d(gh, hg) = N([h, g]) ≤ C N g N h`. -/
theorem d_mul_comm_le {g h : G} (hg : 𝒢.N g ≤ 𝒢.C⁻¹) (hh : 𝒢.N h ≤ 𝒢.C⁻¹) :
    𝒢.d (g * h) (h * g) ≤ 𝒢.C * 𝒢.N g * 𝒢.N h := by
  have := 𝒢.commutator h g hh hg
  rw [WeakGleasonNorm.d_def, show (g * h)⁻¹ * (h * g) = h⁻¹ * g⁻¹ * h * g by group]
  linarith

/-- One step of the telescoping in Lemma 16(a): `d(gⁿh·hⁿ, hgⁿ·hⁿ) ≤ 2C n N g N h`. -/
theorem d_step_le {g h : G} {n : ℕ} (hg : ((n : ℝ) + 1) * 𝒢.N g ≤ 𝒢.C⁻¹)
    (hh : ((n : ℝ) + 1) * 𝒢.N h ≤ 𝒢.C⁻¹) :
    𝒢.d (g ^ n * h * h ^ n) (h * g ^ n * h ^ n) ≤ 2 * 𝒢.C * n * 𝒢.N g * 𝒢.N h := by
  have hC := 𝒢.C_pos
  have hx := 𝒢.nonneg g
  have hy := 𝒢.nonneg h
  have hgn := 𝒢.N_pow_le g n
  have hhn := 𝒢.N_pow_le h n
  have hgn0 := 𝒢.nonneg (g ^ n)
  have hhn0 := 𝒢.nonneg (h ^ n)
  have hgnC : 𝒢.N (g ^ n) ≤ 𝒢.C⁻¹ := hgn.trans (by nlinarith)
  have hhnC : 𝒢.N (h ^ n) ≤ 𝒢.C⁻¹ := hhn.trans (by nlinarith)
  have hhC : 𝒢.N h ≤ 𝒢.C⁻¹ := le_trans (by nlinarith) hh
  have hcomm := 𝒢.d_mul_comm_le hgnC hhC
  have hCinv : 𝒢.C * 𝒢.C⁻¹ = 1 := mul_inv_cancel₀ hC.ne'
  have hd : 𝒢.d (g ^ n * h) (h * g ^ n) ≤ 𝒢.C⁻¹ := by
    refine hcomm.trans ?_
    calc 𝒢.C * 𝒢.N (g ^ n) * 𝒢.N h ≤ 𝒢.C * 𝒢.C⁻¹ * 𝒢.C⁻¹ := by gcongr
      _ = 𝒢.C⁻¹ := by rw [hCinv, one_mul]
  have hstep := 𝒢.d_mul_right_le hd hhnC
  have h1 : 1 + 𝒢.C * 𝒢.N (h ^ n) ≤ 2 := by
    have : 𝒢.C * 𝒢.N (h ^ n) ≤ 𝒢.C * 𝒢.C⁻¹ := by gcongr
    linarith
  have h2 : 𝒢.C * 𝒢.N (g ^ n) * 𝒢.N h ≤ 𝒢.C * (n * 𝒢.N g) * 𝒢.N h := by gcongr
  calc 𝒢.d (g ^ n * h * h ^ n) (h * g ^ n * h ^ n)
      ≤ (1 + 𝒢.C * 𝒢.N (h ^ n)) * 𝒢.d (g ^ n * h) (h * g ^ n) := hstep
    _ ≤ 2 * (𝒢.C * (n * 𝒢.N g) * 𝒢.N h) := by
        gcongr
        · exact 𝒢.d_nonneg _ _
        · exact hcomm.trans h2
    _ = 2 * 𝒢.C * n * 𝒢.N g * 𝒢.N h := by ring

/-- **Lemma 16(a)** (Tao 254A Notes 2): `d(gⁿhⁿ, (gh)ⁿ) ≤ 2C n² N g N h` when
`n N g, n N h ≤ C⁻¹`. -/
theorem d_pow_mul_pow_le {g h : G} {n : ℕ} (hg : (n : ℝ) * 𝒢.N g ≤ 𝒢.C⁻¹)
    (hh : (n : ℝ) * 𝒢.N h ≤ 𝒢.C⁻¹) :
    𝒢.d (g ^ n * h ^ n) ((g * h) ^ n) ≤ 2 * 𝒢.C * (n : ℝ) ^ 2 * 𝒢.N g * 𝒢.N h := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hx := 𝒢.nonneg g
    have hy := 𝒢.nonneg h
    have hC := 𝒢.C_pos
    push_cast at hg hh ⊢
    have ih' := ih (by nlinarith) (by nlinarith)
    have hstep := 𝒢.d_step_le hg hh
    -- the middle point `g * h * (gⁿ hⁿ)`
    have e1 : g ^ (n + 1) * h ^ (n + 1) = g * (g ^ n * h * h ^ n) := by
      rw [pow_succ', pow_succ']; group
    have e2 : g * h * (g ^ n * h ^ n) = g * (h * g ^ n * h ^ n) := by group
    have e3 : (g * h) ^ (n + 1) = g * h * (g * h) ^ n := pow_succ' _ _
    have hmid1 : 𝒢.d (g * (g ^ n * h * h ^ n)) (g * (h * g ^ n * h ^ n)) =
        𝒢.d (g ^ n * h * h ^ n) (h * g ^ n * h ^ n) := 𝒢.d_mul_left _ _ _
    have hmid2 : 𝒢.d (g * (h * g ^ n * h ^ n)) (g * h * (g * h) ^ n) =
        𝒢.d (g ^ n * h ^ n) ((g * h) ^ n) := by
      rw [← e2]; exact 𝒢.d_mul_left _ _ _
    have t1 := 𝒢.d_triangle (g * (g ^ n * h * h ^ n)) (g * (h * g ^ n * h ^ n))
      (g * h * (g * h) ^ n)
    rw [e1, e3]
    have hsq : 2 * 𝒢.C * n * 𝒢.N g * 𝒢.N h + 2 * 𝒢.C * (n : ℝ) ^ 2 * 𝒢.N g * 𝒢.N h ≤
        2 * 𝒢.C * ((n : ℝ) + 1) ^ 2 * 𝒢.N g * 𝒢.N h := by
      have : 0 ≤ 2 * 𝒢.C * 𝒢.N g * 𝒢.N h := by positivity
      nlinarith
    linarith

/-- Lemma 16(a) in terms of the `n`-th powers (the form used for Prop 22 in B3a, with
`a = X (1/n)`, `b = Y (1/n)`): `d(aⁿbⁿ, (ab)ⁿ) ≤ 2C³ N(aⁿ) N(bⁿ)` when `n N a, n N b ≤ C⁻¹`. -/
theorem d_pow_mul_pow_le_pow {a b : G} {n : ℕ} (ha : (n : ℝ) * 𝒢.N a ≤ 𝒢.C⁻¹)
    (hb : (n : ℝ) * 𝒢.N b ≤ 𝒢.C⁻¹) :
    𝒢.d (a ^ n * b ^ n) ((a * b) ^ n) ≤ 2 * 𝒢.C ^ 3 * 𝒢.N (a ^ n) * 𝒢.N (b ^ n) := by
  have hC := 𝒢.C_pos
  have h1 := 𝒢.escape a n ha
  have h2 := 𝒢.escape b n hb
  have hna : 0 ≤ (n : ℝ) * 𝒢.N a := mul_nonneg (Nat.cast_nonneg n) (𝒢.nonneg a)
  have hnb : 0 ≤ (n : ℝ) * 𝒢.N b := mul_nonneg (Nat.cast_nonneg n) (𝒢.nonneg b)
  refine (𝒢.d_pow_mul_pow_le ha hb).trans ?_
  calc 2 * 𝒢.C * (n : ℝ) ^ 2 * 𝒢.N a * 𝒢.N b = 2 * 𝒢.C * ((n : ℝ) * 𝒢.N a) * ((n : ℝ) * 𝒢.N b) := by
        ring
    _ ≤ 2 * 𝒢.C * (𝒢.C * 𝒢.N (a ^ n)) * (𝒢.C * 𝒢.N (b ^ n)) := by
        have := 𝒢.nonneg (a ^ n)
        gcongr
    _ = 2 * 𝒢.C ^ 3 * 𝒢.N (a ^ n) * 𝒢.N (b ^ n) := by ring

/-- `d(hⁿkⁿ, (hk)ⁿ)` bound used in Lemma 16(b), in the form `≤ n N k / (2C)`. -/
private theorem d_pow_aux {h k : G} {n : ℕ} (hh : (n : ℝ) * 𝒢.N h ≤ (4 * 𝒢.C ^ 2)⁻¹)
    (hk : (n : ℝ) * 𝒢.N k ≤ 𝒢.C⁻¹) :
    𝒢.d (h ^ n * k ^ n) ((h * k) ^ n) ≤ (n : ℝ) * 𝒢.N k / (2 * 𝒢.C) := by
  have hC := 𝒢.C_pos
  have hC1 := 𝒢.one_le_C
  have hx := 𝒢.nonneg h
  have hy := 𝒢.nonneg k
  have h4 : (4 * 𝒢.C ^ 2)⁻¹ ≤ 𝒢.C⁻¹ := inv_anti₀ hC (by nlinarith)
  have ha := 𝒢.d_pow_mul_pow_le (hh.trans h4) hk
  refine ha.trans ?_
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have e : 2 * 𝒢.C * (n : ℝ) ^ 2 * 𝒢.N h * 𝒢.N k = 2 * 𝒢.C * (n * 𝒢.N h) * (n * 𝒢.N k) := by
    ring
  rw [e, le_div_iff₀ (by positivity)]
  have hnk : 0 ≤ (n : ℝ) * 𝒢.N k := by positivity
  calc 2 * 𝒢.C * (n * 𝒢.N h) * (n * 𝒢.N k) * (2 * 𝒢.C)
      ≤ 2 * 𝒢.C * (4 * 𝒢.C ^ 2)⁻¹ * (n * 𝒢.N k) * (2 * 𝒢.C) := by gcongr
    _ = n * 𝒢.N k := by field_simp; ring

/-- Smallness bookkeeping for Lemma 16(b). -/
private theorem small_aux {g h : G} {n : ℕ} (hg : (n : ℝ) * 𝒢.N g ≤ (4 * 𝒢.C ^ 2)⁻¹)
    (hh : (n : ℝ) * 𝒢.N h ≤ (4 * 𝒢.C ^ 2)⁻¹) : (n : ℝ) * 𝒢.N (h⁻¹ * g) ≤ 𝒢.C⁻¹ := by
  have hC := 𝒢.C_pos
  have hC1 := 𝒢.one_le_C
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hk := 𝒢.mul_le h⁻¹ g
  rw [𝒢.N_inv] at hk
  have h2 : 2 * (4 * 𝒢.C ^ 2)⁻¹ ≤ 𝒢.C⁻¹ := by
    rw [← div_eq_mul_inv, div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ hC]
    nlinarith
  calc (n : ℝ) * 𝒢.N (h⁻¹ * g) ≤ n * (𝒢.N h + 𝒢.N g) := by gcongr
    _ ≤ 2 * (4 * 𝒢.C ^ 2)⁻¹ := by linarith
    _ ≤ 𝒢.C⁻¹ := h2

/-- **Lemma 16(b), lower bound**: `n d(g,h) ≤ 2C d(gⁿ,hⁿ)` when `n N g, n N h ≤ (4C²)⁻¹`. -/
theorem mul_d_le_d_pow {g h : G} {n : ℕ} (hg : (n : ℝ) * 𝒢.N g ≤ (4 * 𝒢.C ^ 2)⁻¹)
    (hh : (n : ℝ) * 𝒢.N h ≤ (4 * 𝒢.C ^ 2)⁻¹) :
    (n : ℝ) * 𝒢.d g h ≤ 2 * 𝒢.C * 𝒢.d (g ^ n) (h ^ n) := by
  have hC := 𝒢.C_pos
  have hsmall := 𝒢.small_aux hg hh
  obtain ⟨k, rfl⟩ : ∃ k, g = h * k := ⟨h⁻¹ * g, by group⟩
  rw [inv_mul_cancel_left] at hsmall
  have haux := 𝒢.d_pow_aux hh hsmall
  have hesc := 𝒢.escape' hsmall
  -- `N (kⁿ) = d(hⁿ, hⁿkⁿ) ≤ d(hⁿ, (hk)ⁿ) + d(hⁿkⁿ, (hk)ⁿ)`
  have t := 𝒢.d_triangle (h ^ n) ((h * k) ^ n) (h ^ n * k ^ n)
  rw [𝒢.d_self_mul, 𝒢.d_comm ((h * k) ^ n)] at t
  rw [𝒢.d_mul_self, 𝒢.d_comm ((h * k) ^ n)]
  have h1 : (n : ℝ) * 𝒢.N k / (2 * 𝒢.C) ≤ 𝒢.d (h ^ n) ((h * k) ^ n) := by
    have : (n : ℝ) * 𝒢.N k / 𝒢.C = 2 * ((n : ℝ) * 𝒢.N k / (2 * 𝒢.C)) := by
      field_simp
    linarith
  rwa [div_le_iff₀ (by positivity), mul_comm (𝒢.d _ _)] at h1

/-- **Lemma 16(b), upper bound**: `d(gⁿ,hⁿ) ≤ 2n d(g,h)` when `n N g, n N h ≤ (4C²)⁻¹`. -/
theorem d_pow_le_mul_d {g h : G} {n : ℕ} (hg : (n : ℝ) * 𝒢.N g ≤ (4 * 𝒢.C ^ 2)⁻¹)
    (hh : (n : ℝ) * 𝒢.N h ≤ (4 * 𝒢.C ^ 2)⁻¹) :
    𝒢.d (g ^ n) (h ^ n) ≤ 2 * n * 𝒢.d g h := by
  have hC := 𝒢.C_pos
  have hC1 := 𝒢.one_le_C
  have hsmall := 𝒢.small_aux hg hh
  obtain ⟨k, rfl⟩ : ∃ k, g = h * k := ⟨h⁻¹ * g, by group⟩
  rw [inv_mul_cancel_left] at hsmall
  have haux := 𝒢.d_pow_aux hh hsmall
  have hkn := 𝒢.N_pow_le k n
  -- `d(hⁿ, (hk)ⁿ) ≤ d(hⁿ, hⁿkⁿ) + d(hⁿkⁿ, (hk)ⁿ) = N (kⁿ) + d(hⁿkⁿ, (hk)ⁿ)`
  have t := 𝒢.d_triangle (h ^ n) (h ^ n * k ^ n) ((h * k) ^ n)
  rw [𝒢.d_self_mul] at t
  rw [𝒢.d_mul_self, 𝒢.d_comm]
  have hnk : 0 ≤ (n : ℝ) * 𝒢.N k := mul_nonneg (Nat.cast_nonneg n) (𝒢.nonneg k)
  have h3 : (n : ℝ) * 𝒢.N k / (2 * 𝒢.C) ≤ (n : ℝ) * 𝒢.N k := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  nlinarith

/-- **Lemma 16** (Tao 254A Notes 2), in the packaged form of blueprint B1, with `ε₀ = (4C²)⁻¹`
and `A = 2C`. -/
theorem exists_pow_estimates : ∃ ε₀ > 0, ∃ A ≥ 1, ∀ (g h : G) (n : ℕ), 1 ≤ n →
    (n : ℝ) * 𝒢.N g ≤ ε₀ → (n : ℝ) * 𝒢.N h ≤ ε₀ →
      𝒢.d (g ^ n * h ^ n) ((g * h) ^ n) ≤ A * (n : ℝ) ^ 2 * 𝒢.N g * 𝒢.N h ∧
      (n : ℝ) * 𝒢.d g h ≤ A * 𝒢.d (g ^ n) (h ^ n) ∧
      𝒢.d (g ^ n) (h ^ n) ≤ A * n * 𝒢.d g h := by
  have hC := 𝒢.C_pos
  have hC2 := 𝒢.two_le_C
  have h4 : (4 * 𝒢.C ^ 2)⁻¹ ≤ 𝒢.C⁻¹ := inv_anti₀ hC (by nlinarith)
  refine ⟨(4 * 𝒢.C ^ 2)⁻¹, by positivity, 2 * 𝒢.C, by linarith, fun g h n _ hg hh => ?_⟩
  refine ⟨𝒢.d_pow_mul_pow_le (hg.trans h4) (hh.trans h4), 𝒢.mul_d_le_d_pow hg hh, ?_⟩
  refine (𝒢.d_pow_le_mul_d hg hh).trans ?_
  have := mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (𝒢.d_nonneg g h)
  nlinarith

/-- Lemma 16(a) at power `m` followed by Lemma 16(b) at power `n`: the Cauchy estimate behind the
Trotter limit of B3a, `d((gᵐhᵐ)ⁿ, (gh)^(mn)) ≤ 4C n m² N g N h` when `mn N g, mn N h ≤ (8C²)⁻¹`.
(With `g = X(t/(mn))`, `h = Y(t/(mn))` this is `d(z_n(t), z_{mn}(t)) ≤ 4C L² t² / n`.) -/
theorem d_pow_pow_mul_pow_le {g h : G} {m n : ℕ}
    (hg : ((m : ℝ) * n) * 𝒢.N g ≤ (8 * 𝒢.C ^ 2)⁻¹) (hh : ((m : ℝ) * n) * 𝒢.N h ≤ (8 * 𝒢.C ^ 2)⁻¹) :
    𝒢.d ((g ^ m * h ^ m) ^ n) ((g * h) ^ (m * n)) ≤
      4 * 𝒢.C * n * (m : ℝ) ^ 2 * 𝒢.N g * 𝒢.N h := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hC := 𝒢.C_pos
  have hC1 := 𝒢.one_le_C
  have hx := 𝒢.nonneg g
  have hy := 𝒢.nonneg h
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h8 : (8 * 𝒢.C ^ 2)⁻¹ ≤ 𝒢.C⁻¹ := inv_anti₀ hC (by nlinarith)
  have h84 : 2 * (8 * 𝒢.C ^ 2)⁻¹ = (4 * 𝒢.C ^ 2)⁻¹ := by field_simp; norm_num
  -- the inner estimate at power `m`
  have hgm : (m : ℝ) * 𝒢.N g ≤ 𝒢.C⁻¹ :=
    le_trans (by nlinarith [mul_nonneg hm0 hx]) (hg.trans h8)
  have hhm : (m : ℝ) * 𝒢.N h ≤ 𝒢.C⁻¹ :=
    le_trans (by nlinarith [mul_nonneg hm0 hy]) (hh.trans h8)
  have hin := 𝒢.d_pow_mul_pow_le hgm hhm
  -- the outer estimate at power `n`
  have ha : (n : ℝ) * 𝒢.N (g ^ m * h ^ m) ≤ (4 * 𝒢.C ^ 2)⁻¹ := by
    have := 𝒢.mul_le (g ^ m) (h ^ m)
    have := 𝒢.N_pow_le g m
    have := 𝒢.N_pow_le h m
    calc (n : ℝ) * 𝒢.N (g ^ m * h ^ m) ≤ n * (m * 𝒢.N g + m * 𝒢.N h) := by
          gcongr; linarith
      _ = (m * n) * 𝒢.N g + (m * n) * 𝒢.N h := by ring
      _ ≤ (4 * 𝒢.C ^ 2)⁻¹ := by linarith
  have hb : (n : ℝ) * 𝒢.N ((g * h) ^ m) ≤ (4 * 𝒢.C ^ 2)⁻¹ := by
    have := 𝒢.mul_le g h
    have := 𝒢.N_pow_le (g * h) m
    calc (n : ℝ) * 𝒢.N ((g * h) ^ m) ≤ n * (m * (𝒢.N g + 𝒢.N h)) := by
          gcongr; nlinarith
      _ = (m * n) * 𝒢.N g + (m * n) * 𝒢.N h := by ring
      _ ≤ (4 * 𝒢.C ^ 2)⁻¹ := by linarith
  have hout := 𝒢.d_pow_le_mul_d ha hb
  rw [pow_mul]
  calc 𝒢.d ((g ^ m * h ^ m) ^ n) (((g * h) ^ m) ^ n)
      ≤ 2 * n * 𝒢.d (g ^ m * h ^ m) ((g * h) ^ m) := hout
    _ ≤ 2 * n * (2 * 𝒢.C * (m : ℝ) ^ 2 * 𝒢.N g * 𝒢.N h) := by gcongr
    _ = 4 * 𝒢.C * n * (m : ℝ) ^ 2 * 𝒢.N g * 𝒢.N h := by ring

end GleasonNorm

end HSFormal.GY

end
