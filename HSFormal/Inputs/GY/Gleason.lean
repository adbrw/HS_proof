import HSFormal.Inputs.GY.Defs
import HSFormal.Inputs.GY.Convolution

/-!
# Weak Gleason norm ⇒ Gleason norm (module A5)

Tao 254A Notes 4, Theorem 14 ("every weak Gleason metric is a Gleason metric"). Main results:

```
theorem WeakGleasonNorm.exists_commutator_le [IsTopologicalGroup G] [LocallyCompactSpace G]
    (𝒩 : WeakGleasonNorm G) : ∃ K c : ℝ, 0 < c ∧ ∀ g h : G, 𝒩.N g ≤ c → 𝒩.N h ≤ c →
      𝒩.N (g⁻¹ * h⁻¹ * g * h) ≤ K * 𝒩.N g * 𝒩.N h
theorem WeakGleasonNorm.exists_gleasonNorm_N_eq [IsTopologicalGroup G] [LocallyCompactSpace G]
    (𝒩 : WeakGleasonNorm G) : ∃ 𝒢 : GleasonNorm G, 𝒢.N = 𝒩.N
theorem WeakGleasonNorm.nonempty_gleasonNorm [IsTopologicalGroup G] [LocallyCompactSpace G]
    (𝒩 : WeakGleasonNorm G) : Nonempty (GleasonNorm G)
```
(no `T2Space` is needed).

## Proof

Write `N = 𝒩.N`, `C = 𝒩.C`. Fix `ε > 0` with `{N ≤ 2ε}` compact and `5ε ≤ (2C²)⁻¹`, Haar `μ`,
`ψ = max (1 - N/ε) 0` (`WeakGleasonNorm.bumpN`) and `φ = ψ ⋆ ψ` (A2's `conv`).

* `|∂_g ψ| ≤ N g / ε` (`abs_ldiff_bumpN_le`), `supp ψ ⊆ {N < ε}`, `ψ ≥ 1/2` on `{N ≤ ε/2}`.
* Conjugation (`N_conj_le_of_le`): for `N y ≤ 2ε`, `N k ≤ ε/2`, `N (y⁻¹ k y) ≤ 10 C N k`
  (escape to scale, in the form `N_le_of_pow_le_mul`).
* (8) (`abs_ldiff_ldiff_conv_le`): for `N g ≤ ε`, `N k ≤ ε/2`,
  `|∂_k ∂_g φ| ≤ K₈ N g N k` with `K₈ = 10 C μ{N ≤ 2ε} / ε²` (A2's Tao (10)).
* Commutator for `‖·‖_φ` (`tnorm_commutator_le'`): `‖[g,h]‖_φ ≤ 2 K₈ N g N h`.
* Claim 1 (`N_le_tnorm`): `‖x‖_φ ≤ φ(1)/4 ⇒ N x ≤ (8 C ε / φ(1)) ‖x‖_φ`.

Hence `N [g,h] ≤ (16 C ε K₈ / φ(1)) N g N h` for `N g, N h` small, and Defs'
`WeakGleasonNorm.toGleasonNorm` produces the Gleason norm.

Deviation from the blueprint: the Gleason norm keeps the norm `N` of the weak Gleason norm
(the commutator estimate is transferred to `N` through Claim 1) instead of switching to
`‖·‖_φ`; so Claim 2, the continuity of `φ` and the remaining `WeakGleasonNorm` fields of
`‖·‖_φ` are not needed. The result is stronger (`exists_gleasonNorm_N_eq`).
-/

noncomputable section

namespace HSFormal.GY

open MeasureTheory Filter Topology Set
open scoped Pointwise ENNReal

namespace WeakGleasonNorm

variable {G : Type*} [Group G] [TopologicalSpace G] (𝒩 : WeakGleasonNorm G)

/-! ## Escape to scale and conjugation -/

/-- Escape to scale in multiplicative form: if `δ ≤ (2C²)⁻¹`, `0 ≤ a ≤ 1/2` and
`N (x ^ m) ≤ δ` whenever `1 ≤ m` and `m a ≤ 1`, then `N x ≤ 2 C δ a`. -/
theorem N_le_of_pow_le_mul {x : G} {δ a : ℝ} (hδ : δ ≤ (2 * 𝒩.C ^ 2)⁻¹) (hδ0 : 0 ≤ δ)
    (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2)
    (hx : ∀ m : ℕ, 1 ≤ m → (m : ℝ) * a ≤ 1 → 𝒩.N (x ^ m) ≤ δ) :
    𝒩.N x ≤ 2 * 𝒩.C * δ * a := by
  rcases ha.eq_or_lt with rfl | hapos
  · have : x = 1 := 𝒩.eq_one_of_forall_pow_le hδ fun m => by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simpa using hδ0
      · exact hx m hm (by simp)
    simp [this]
  · set n := ⌊a⁻¹⌋₊ with hn
    have hinv2 : 2 ≤ a⁻¹ := by
      rw [le_inv_comm₀ two_pos hapos]; linarith
    have hn1 : 1 ≤ n := by rw [hn, Nat.one_le_floor_iff]; linarith
    have hnle : (n : ℝ) ≤ a⁻¹ := Nat.floor_le (by positivity)
    have hnlt : a⁻¹ < n + 1 := Nat.lt_floor_add_one _
    have h := 𝒩.N_le_of_pow_le hδ hn1 fun m hm hmn => hx m hm (by
      have hm' : (m : ℝ) ≤ n := by exact_mod_cast hmn
      calc (m : ℝ) * a ≤ n * a := by gcongr
        _ ≤ a⁻¹ * a := by gcongr
        _ = 1 := inv_mul_cancel₀ hapos.ne')
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have h1 : 1 < a * (n + 1) := (inv_lt_iff_one_lt_mul₀' hapos).1 hnlt
    have h2 : 1 ≤ 2 * a * n := by nlinarith
    have hCδ : 0 ≤ 𝒩.C * δ := mul_nonneg 𝒩.C_pos.le hδ0
    calc 𝒩.N x ≤ 𝒩.C * δ / n := h
      _ ≤ 2 * 𝒩.C * δ * a := by
        rw [div_le_iff₀ hn0]
        nlinarith [mul_le_mul_of_nonneg_left h2 hCδ]

/-- **Conjugation estimate** (Tao, proof of Theorem 14): for `N y ≤ 2ε` and `N k ≤ ε/2`,
`N (y⁻¹ k y) ≤ 10 C N k`. -/
theorem N_conj_le_of_le {ε : ℝ} (hε : 0 < ε) (hε5 : 5 * ε ≤ (2 * 𝒩.C ^ 2)⁻¹) {y k : G}
    (hy : 𝒩.N y ≤ 2 * ε) (hk : 𝒩.N k ≤ ε / 2) : 𝒩.N (y⁻¹ * k * y) ≤ 10 * 𝒩.C * 𝒩.N k := by
  have h := 𝒩.N_le_of_pow_le_mul (x := y⁻¹ * k * y) (a := 𝒩.N k / ε) hε5 (by linarith)
    (div_nonneg (𝒩.nonneg k) hε.le) (by rw [div_le_iff₀ hε]; linarith) fun m _ hma => by
      have hmk : (m : ℝ) * 𝒩.N k ≤ ε := by
        rwa [mul_div_assoc', div_le_one hε] at hma
      have e : (y⁻¹ * k * y) ^ m = y⁻¹ * k ^ m * y := by
        simpa using conj_pow (i := m) (a := y⁻¹) (b := k)
      rw [e]
      have h1 := 𝒩.mul_le (y⁻¹ * k ^ m) y
      have h2 := 𝒩.mul_le y⁻¹ (k ^ m)
      have h3 := 𝒩.N_pow_le k m
      rw [𝒩.N_inv] at h2
      linarith
  calc 𝒩.N (y⁻¹ * k * y) ≤ 2 * 𝒩.C * (5 * ε) * (𝒩.N k / ε) := h
    _ = 10 * 𝒩.C * 𝒩.N k := by field_simp; ring

/-! ## The Lipschitz bump `ψ = max (1 - N/ε) 0` -/

/-- Tao's bump `ψ(x) = (1 - ‖x‖/ε)₊`. -/
def bumpN (ε : ℝ) (x : G) : ℝ := max (1 - 𝒩.N x / ε) 0

variable {ε : ℝ}

theorem bumpN_nonneg (x : G) : 0 ≤ 𝒩.bumpN ε x := le_max_right _ _

theorem abs_bumpN_le (hε : 0 < ε) (x : G) : |𝒩.bumpN ε x| ≤ 1 := by
  rw [abs_of_nonneg (𝒩.bumpN_nonneg x)]
  refine max_le ?_ zero_le_one
  have := div_nonneg (𝒩.nonneg x) hε.le
  linarith

theorem bumpN_eq_zero (hε : 0 < ε) {x : G} (hx : ε ≤ 𝒩.N x) : 𝒩.bumpN ε x = 0 := by
  refine max_eq_right ?_
  have : 1 ≤ 𝒩.N x / ε := by rw [le_div_iff₀ hε]; linarith
  linarith

theorem N_lt_of_bumpN_ne_zero (hε : 0 < ε) {x : G} (hx : 𝒩.bumpN ε x ≠ 0) : 𝒩.N x < ε := by
  by_contra h
  exact hx (𝒩.bumpN_eq_zero hε (not_lt.1 h))

theorem half_le_bumpN (hε : 0 < ε) {x : G} (hx : 𝒩.N x ≤ ε / 2) : 1 / 2 ≤ 𝒩.bumpN ε x := by
  refine le_max_of_le_left ?_
  have : 𝒩.N x / ε ≤ 1 / 2 := by rw [div_le_iff₀ hε]; linarith
  linarith

/-- `|N x - N (g⁻¹ x)| ≤ N g`. -/
theorem abs_N_sub_N_inv_mul_le (g x : G) : |𝒩.N x - 𝒩.N (g⁻¹ * x)| ≤ 𝒩.N g := by
  have h1 := 𝒩.mul_le g (g⁻¹ * x)
  have h2 := 𝒩.mul_le g⁻¹ x
  rw [mul_inv_cancel_left] at h1
  rw [𝒩.N_inv] at h2
  rw [abs_le]; constructor <;> linarith

/-- Tao (6): `|∂_g ψ| ≤ N g / ε`. -/
theorem abs_ldiff_bumpN_le (hε : 0 < ε) (g x : G) :
    |ldiff g (𝒩.bumpN ε) x| ≤ 𝒩.N g / ε := by
  rw [ldiff_apply, bumpN, bumpN]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  have e : 1 - 𝒩.N x / ε - (1 - 𝒩.N (g⁻¹ * x) / ε) = -((𝒩.N x - 𝒩.N (g⁻¹ * x)) / ε) := by
    ring
  rw [e, abs_neg, abs_div, abs_of_pos hε]
  exact div_le_div_of_nonneg_right (𝒩.abs_N_sub_N_inv_mul_le g x) hε.le

theorem continuous_bumpN (ε : ℝ) : Continuous (𝒩.bumpN ε) :=
  ((continuous_const.sub (𝒩.continuous.div_const ε)).max continuous_const)

/-! ## The convolution `φ = ψ ⋆ ψ` -/

section Haar

variable [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
  [μ.IsHaarMeasure]

omit [IsTopologicalGroup G] in
theorem measurable_bumpN (ε : ℝ) : Measurable (𝒩.bumpN ε) :=
  (𝒩.continuous_bumpN ε).measurable

omit [IsTopologicalGroup G] [BorelSpace G] in
theorem measure_lt_ne_top (hε : 0 < ε) (hK : IsCompact {g | 𝒩.N g ≤ 2 * ε}) :
    μ {g | 𝒩.N g < ε} ≠ ∞ :=
  ((measure_mono fun g (hg : 𝒩.N g < ε) => (show 𝒩.N g ≤ 2 * ε by linarith)).trans_lt
    hK.measure_lt_top).ne

omit [IsTopologicalGroup G] in
theorem integrable_bumpN (hε : 0 < ε) (hK : IsCompact {g | 𝒩.N g ≤ 2 * ε}) :
    Integrable (𝒩.bumpN ε) μ :=
  integrable_of_bdd_of_notMem_eq_zero (𝒩.measurable_bumpN ε) (𝒩.abs_bumpN_le hε)
    (𝒩.measure_lt_ne_top μ hε hK) fun _ hy => 𝒩.bumpN_eq_zero hε (not_lt.1 hy)

omit [IsTopologicalGroup G] [BorelSpace G] in
/-- `|φ| ≤ μ {N < ε}`. -/
theorem abs_conv_bumpN_le (hε : 0 < ε) (hK : IsCompact {g | 𝒩.N g ≤ 2 * ε}) (x : G) :
    |conv μ (𝒩.bumpN ε) (𝒩.bumpN ε) x| ≤ (μ {g | 𝒩.N g < ε}).toReal := by
  have := abs_conv_le (μ := μ) (S := {g | 𝒩.N g < ε}) (𝒩.measure_lt_ne_top μ hε hK)
    (fun y _ => 𝒩.abs_bumpN_le hε y) (fun _ hy => 𝒩.bumpN_eq_zero hε (not_lt.1 hy))
    (𝒩.abs_bumpN_le hε) x
  rwa [one_mul, one_mul] at this

omit [IsTopologicalGroup G] [BorelSpace G] [μ.IsHaarMeasure] in
/-- `supp φ ⊆ {N < 2ε}`. -/
theorem N_lt_of_conv_bumpN_ne_zero (hε : 0 < ε) {x : G}
    (hx : conv μ (𝒩.bumpN ε) (𝒩.bumpN ε) x ≠ 0) : 𝒩.N x < 2 * ε := by
  have hsupp : Function.support (𝒩.bumpN ε) ⊆ {g | 𝒩.N g < ε} :=
    fun y hy => 𝒩.N_lt_of_bumpN_ne_zero hε hy
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_mul_of_conv_ne_zero hsupp hsupp hx
  have ha' : 𝒩.N a < ε := ha
  have hb' : 𝒩.N b < ε := hb
  linarith [𝒩.mul_le a b]

/-- `φ(1) > 0`. -/
theorem conv_bumpN_one_pos (hε : 0 < ε) (hK : IsCompact {g | 𝒩.N g ≤ 2 * ε}) :
    0 < conv μ (𝒩.bumpN ε) (𝒩.bumpN ε) 1 := by
  set U : Set G := {g | 𝒩.N g < ε / 2}
  have hUo : IsOpen U := 𝒩.isOpen_setOf_lt _
  have hU1 : (1 : G) ∈ U := by
    show 𝒩.N 1 < ε / 2
    rw [𝒩.N_one]; linarith
  have hUfin : μ U ≠ ∞ :=
    ((measure_mono fun g (hg : 𝒩.N g < ε / 2) => (show 𝒩.N g ≤ 2 * ε by linarith)).trans_lt
      hK.measure_lt_top).ne
  have hUpos : 0 < (μ U).toReal := ENNReal.toReal_pos (hUo.measure_pos μ ⟨1, hU1⟩).ne' hUfin
  have h := le_conv (μ := μ) (U := U) (c := 1 / 4) hUo.measurableSet (𝒩.integrable_bumpN μ hε hK)
    (𝒩.measurable_bumpN ε) (𝒩.abs_bumpN_le hε) 𝒩.bumpN_nonneg 𝒩.bumpN_nonneg (x := 1)
    fun y hy => by
      have hy' : 𝒩.N y ≤ ε / 2 := (show 𝒩.N y < ε / 2 from hy).le
      have h1 := 𝒩.half_le_bumpN hε hy'
      have h2 := 𝒩.half_le_bumpN hε (x := y⁻¹ * 1) (by rw [mul_one, 𝒩.N_inv]; exact hy')
      nlinarith
  have : 0 < 1 / 4 * (μ U).toReal := by positivity
  linarith

/-- **Tao (8).** For `N g ≤ ε` and `N k ≤ ε/2`, `|∂_k ∂_g φ| ≤ K₈ N g N k` with
`K₈ = 10 C μ{N ≤ 2ε} / ε²`. -/
theorem abs_ldiff_ldiff_conv_le (hε : 0 < ε) (hε5 : 5 * ε ≤ (2 * 𝒩.C ^ 2)⁻¹)
    (hK : IsCompact {g | 𝒩.N g ≤ 2 * ε}) {g k : G} (hg : 𝒩.N g ≤ ε) (hk : 𝒩.N k ≤ ε / 2)
    (x : G) :
    |ldiff k (ldiff g (conv μ (𝒩.bumpN ε) (𝒩.bumpN ε))) x|
      ≤ 10 * 𝒩.C * (μ {g | 𝒩.N g ≤ 2 * ε}).toReal / ε ^ 2 * 𝒩.N g * 𝒩.N k := by
  rw [ldiff_ldiff_conv (𝒩.integrable_bumpN μ hε hK) (𝒩.measurable_bumpN ε)
    (𝒩.abs_bumpN_le hε) g k x]
  have hC := 𝒩.C_pos
  have hNg := 𝒩.nonneg g
  have hNk := 𝒩.nonneg k
  refine (abs_integral_le_mul_measure (S := {y | 𝒩.N y ≤ 2 * ε}) hK.measure_lt_top.ne
    (c := 𝒩.N g / ε * (10 * 𝒩.C * 𝒩.N k / ε)) (fun y hy => ?_) (fun y hy => ?_)).trans
    (le_of_eq ?_)
  · rw [abs_mul]
    have hy' : 𝒩.N y ≤ 2 * ε := hy
    have h1 := 𝒩.abs_ldiff_bumpN_le hε g y
    have h2 := 𝒩.abs_ldiff_bumpN_le hε (y⁻¹ * k * y) (y⁻¹ * x)
    have h3 := 𝒩.N_conj_le_of_le hε hε5 hy' hk
    refine mul_le_mul h1 (h2.trans ?_) (abs_nonneg _) (by positivity)
    exact div_le_div_of_nonneg_right h3 hε.le
  · have hy' : 2 * ε < 𝒩.N y := lt_of_not_ge hy
    have h1 : 𝒩.bumpN ε y = 0 := 𝒩.bumpN_eq_zero hε (by linarith)
    have h2 : 𝒩.bumpN ε (g⁻¹ * y) = 0 := 𝒩.bumpN_eq_zero hε (by
      have := 𝒩.mul_le g (g⁻¹ * y)
      rw [mul_inv_cancel_left] at this
      linarith)
    rw [ldiff_apply, h1, h2, sub_zero, zero_mul]
  · field_simp

/-- Commutator bound for `‖·‖_φ`: `‖g⁻¹h⁻¹gh‖_φ ≤ 2 K₈ N g N h` for `N g, N h ≤ ε/2`. -/
theorem tnorm_conv_commutator_le (hε : 0 < ε) (hε5 : 5 * ε ≤ (2 * 𝒩.C ^ 2)⁻¹)
    (hK : IsCompact {g | 𝒩.N g ≤ 2 * ε}) {g h : G} (hg : 𝒩.N g ≤ ε / 2) (hh : 𝒩.N h ≤ ε / 2) :
    tnorm (conv μ (𝒩.bumpN ε) (𝒩.bumpN ε)) (g⁻¹ * h⁻¹ * g * h)
      ≤ 2 * (10 * 𝒩.C * (μ {g | 𝒩.N g ≤ 2 * ε}).toReal / ε ^ 2) * 𝒩.N g * 𝒩.N h := by
  have hB := 𝒩.abs_conv_bumpN_le μ hε hK
  have hg' : 𝒩.N g ≤ ε := by linarith
  have hh' : 𝒩.N h ≤ ε := by linarith
  have a := tnorm_le fun x => 𝒩.abs_ldiff_ldiff_conv_le μ hε hε5 hK hg' hh x
  have b := tnorm_le fun x => 𝒩.abs_ldiff_ldiff_conv_le μ hε hε5 hK hh' hg x
  refine (tnorm_commutator_le hB g h).trans ?_
  linarith

/-- **Claim 1** (Tao, proof of Theorem 14): if `‖x‖_φ ≤ φ(1)/4` then
`N x ≤ (8 C ε / φ(1)) ‖x‖_φ`. -/
theorem N_le_tnorm (hε : 0 < ε) (hε5 : 5 * ε ≤ (2 * 𝒩.C ^ 2)⁻¹)
    (hK : IsCompact {g | 𝒩.N g ≤ 2 * ε}) {x : G}
    (hx : tnorm (conv μ (𝒩.bumpN ε) (𝒩.bumpN ε)) x
      ≤ conv μ (𝒩.bumpN ε) (𝒩.bumpN ε) 1 / 4) :
    𝒩.N x ≤ 8 * 𝒩.C * ε / conv μ (𝒩.bumpN ε) (𝒩.bumpN ε) 1
      * tnorm (conv μ (𝒩.bumpN ε) (𝒩.bumpN ε)) x := by
  have hB := 𝒩.abs_conv_bumpN_le μ hε hK
  have hp0 := 𝒩.conv_bumpN_one_pos μ hε hK
  have hsupp := fun y => 𝒩.N_lt_of_conv_bumpN_ne_zero μ hε (x := y)
  generalize conv μ (𝒩.bumpN ε) (𝒩.bumpN ε) = φ at hB hp0 hsupp hx ⊢
  have hs0 : 0 ≤ tnorm φ x := tnorm_nonneg φ x
  have h2ε : 2 * ε ≤ (2 * 𝒩.C ^ 2)⁻¹ := by linarith
  have h := 𝒩.N_le_of_pow_le_mul (x := x) (a := 2 * tnorm φ x / φ 1) h2ε (by linarith)
    (by positivity) (by rw [div_le_iff₀ hp0]; linarith) fun m _ hma => by
      have hms : (m : ℝ) * tnorm φ x ≤ φ 1 / 2 := by
        rw [mul_div_assoc', div_le_one hp0] at hma; linarith
      have h1 : |ldiff (x⁻¹ ^ m) φ 1| ≤ tnorm φ (x⁻¹ ^ m) := abs_ldiff_le_tnorm hB _ 1
      have h2 : tnorm φ (x⁻¹ ^ m) ≤ m * tnorm φ x⁻¹ := tnorm_pow_le hB _ _
      rw [tnorm_inv hB] at h2
      have h3 : ldiff (x⁻¹ ^ m) φ 1 = φ 1 - φ (x ^ m) := by
        simp [ldiff_apply, inv_pow]
      refine (hsupp _ fun h0 => ?_).le
      rw [h3, h0, sub_zero, abs_of_pos hp0] at h1
      linarith
  calc 𝒩.N x ≤ 2 * 𝒩.C * (2 * ε) * (2 * tnorm φ x / φ 1) := h
    _ = 8 * 𝒩.C * ε / φ 1 * tnorm φ x := by ring

include μ in
/-- The commutator estimate for the weak Gleason norm itself, given a Haar measure. -/
theorem exists_commutator_le_of_haar (hε : 0 < ε) (hε5 : 5 * ε ≤ (2 * 𝒩.C ^ 2)⁻¹)
    (hK : IsCompact {g | 𝒩.N g ≤ 2 * ε}) :
    ∃ K c : ℝ, 0 < c ∧ ∀ g h : G, 𝒩.N g ≤ c → 𝒩.N h ≤ c →
      𝒩.N (g⁻¹ * h⁻¹ * g * h) ≤ K * 𝒩.N g * 𝒩.N h := by
  set φ := conv μ (𝒩.bumpN ε) (𝒩.bumpN ε) with hφ
  set p := φ 1 with hp
  set K₈ := 10 * 𝒩.C * (μ {g | 𝒩.N g ≤ 2 * ε}).toReal / ε ^ 2 with hK₈
  have hp0 : 0 < p := 𝒩.conv_bumpN_one_pos μ hε hK
  have hK₈0 : 0 ≤ K₈ := by have := 𝒩.C_pos; positivity
  set c := min (ε / 2) (min 1 (p / (8 * K₈ + 1))) with hc
  have hc0 : 0 < c := by positivity
  have hcε : c ≤ ε / 2 := min_le_left _ _
  have hc1 : c ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hcp : c ≤ p / (8 * K₈ + 1) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨8 * 𝒩.C * ε / p * (2 * K₈), c, hc0, fun g h hg hh => ?_⟩
  have hNg := 𝒩.nonneg g
  have hNh := 𝒩.nonneg h
  have hcomm := 𝒩.tnorm_conv_commutator_le μ hε hε5 hK (hg.trans hcε) (hh.trans hcε)
  rw [← hφ, ← hK₈] at hcomm
  have hsmall : 2 * K₈ * 𝒩.N g * 𝒩.N h ≤ p / 4 := by
    have e1 : 2 * K₈ * 𝒩.N g * 𝒩.N h ≤ 2 * K₈ * c * c := by gcongr
    have e2 : 2 * K₈ * c * c ≤ 2 * K₈ * c := by
      have := mul_le_mul_of_nonneg_left hc1 (by positivity : 0 ≤ 2 * K₈ * c)
      linarith
    have e3 : 2 * K₈ * c ≤ 2 * K₈ * (p / (8 * K₈ + 1)) := by gcongr
    have e4 : 2 * K₈ * (p / (8 * K₈ + 1)) ≤ p / 4 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have h1 := 𝒩.N_le_tnorm μ hε hε5 hK (x := g⁻¹ * h⁻¹ * g * h) (by
    rw [← hφ, ← hp]; linarith)
  rw [← hφ, ← hp] at h1
  have hcoef : 0 ≤ 8 * 𝒩.C * ε / p := by have := 𝒩.C_pos; positivity
  calc 𝒩.N (g⁻¹ * h⁻¹ * g * h) ≤ 8 * 𝒩.C * ε / p * tnorm φ (g⁻¹ * h⁻¹ * g * h) := h1
    _ ≤ 8 * 𝒩.C * ε / p * (2 * K₈ * 𝒩.N g * 𝒩.N h) := by gcongr
    _ = 8 * 𝒩.C * ε / p * (2 * K₈) * 𝒩.N g * 𝒩.N h := by ring

end Haar

/-! ## Main results -/

variable [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- **Tao (Notes 4, Theorem 14), commutator estimate.** A weak Gleason norm on a locally compact
group satisfies `N (g⁻¹ h⁻¹ g h) ≤ K N g N h` for `N g, N h ≤ c`. -/
theorem exists_commutator_le :
    ∃ K c : ℝ, 0 < c ∧ ∀ g h : G, 𝒩.N g ≤ c → 𝒩.N h ≤ c →
      𝒩.N (g⁻¹ * h⁻¹ * g * h) ≤ K * 𝒩.N g * 𝒩.N h := by
  borelize G
  obtain ⟨r₀, hr₀, hK₀⟩ := 𝒩.exists_isCompact_le
  have hδ : 0 < (2 * 𝒩.C ^ 2)⁻¹ := by have := 𝒩.C_pos; positivity
  set ε := min (r₀ / 2) ((2 * 𝒩.C ^ 2)⁻¹ / 5) with hε
  have hε0 : 0 < ε := by positivity
  have hε5 : 5 * ε ≤ (2 * 𝒩.C ^ 2)⁻¹ := by
    have := min_le_right (r₀ / 2) ((2 * 𝒩.C ^ 2)⁻¹ / 5); linarith
  have hεr : 2 * ε ≤ r₀ := by
    have := min_le_left (r₀ / 2) ((2 * 𝒩.C ^ 2)⁻¹ / 5); linarith
  exact 𝒩.exists_commutator_le_of_haar (Measure.haar : Measure G) hε0 hε5
    (𝒩.isCompact_setOf_le_of_le hK₀ hεr)

include 𝒩 in
/-- **Tao (Notes 4, Theorem 14).** Every weak Gleason norm on a locally compact group is a
Gleason norm (with the same `N`, after enlarging `C`). -/
theorem exists_gleasonNorm_N_eq : ∃ 𝒢 : GleasonNorm G, 𝒢.N = 𝒩.N := by
  obtain ⟨K, c, hc, h⟩ := 𝒩.exists_commutator_le
  exact ⟨𝒩.toGleasonNorm hc h, rfl⟩

include 𝒩 in
/-- **Tao (Notes 4, Theorem 14).** A locally compact group with a weak Gleason norm has a
Gleason norm. -/
theorem nonempty_gleasonNorm : Nonempty (GleasonNorm G) :=
  let ⟨𝒢, _⟩ := 𝒩.exists_gleasonNorm_N_eq
  ⟨𝒢⟩

end WeakGleasonNorm

end HSFormal.GY
