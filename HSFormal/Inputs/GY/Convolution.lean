import Mathlib

/-!
# Convolution on a non-abelian group (Gleason–Yamabe, module A2)

Tao 254A Notes 4, §2. For a group `G` with a measure `μ` we define

* `HSFormal.GY.ldiff g f x = f x - f (g⁻¹ * x)`  (Tao's `∂_g f`, i.e. `f - τ_g f`);
* `HSFormal.GY.tnorm φ g = ⨆ x, |ldiff g φ x|`  (Tao's `‖g‖_φ = ‖φ - τ_g φ‖_∞`);
* `HSFormal.GY.conv μ ψ η x = ∫ y, ψ y * η (y⁻¹ * x) ∂μ`  (Tao's `ψ ⋆ η`).

mathlib's `MeasureTheory.convolution` is stated for additive groups with a bilinear map and
`MeasureTheory.mlconvolution` is `ℝ≥0∞`-valued, so neither fits signed real functions on a
non-abelian group (differences `∂_g ψ` are signed); hence the dedicated `conv`.

Only **left** invariance of `μ` is used (`IsMulLeftInvariant μ`); the modular function never
appears. No Fubini, no `σ`-finiteness and no second countability are needed: every statement
is either pure algebra or a single integral over `y`. `μ` is arbitrary, e.g.
`MeasureTheory.Measure.haar` (with `borelize G` in the caller).

Main results:
* algebra of `ldiff`: `ldiff_mul_apply`, `ldiff_inv_apply`, `ldiff_pow_apply`,
  `ldiff_commutator_apply`;
* `tnorm` is a (pseudo) norm for bounded `φ`: `tnorm_one`, `tnorm_inv`, `tnorm_mul_le`,
  `tnorm_pow_le`, `tnorm_pow_ge` (Tao's telescoping), `tnorm_commutator_le`, `continuous_tnorm`;
  for continuous compactly supported `φ`, `tendsto_tnorm_nhds_one` (left uniform continuity);
* convolution: `ldiff_conv` (Tao (9)), `ldiff_ldiff_conv` (Tao (10)), supports
  (`support_conv_subset`, `mem_mul_of_conv_ne_zero`, `hasCompactSupport_conv`), bounds
  (`abs_conv_le`, `abs_conv_le_of_right`, `abs_conv_le_integral`, `le_conv`), translation
  (`conv_comp_mul_left`, `conv_mul_right`), `tnorm_conv_le`, `tendsto_tnorm_conv`, continuity
  (`continuous_conv_of_left`, `continuous_conv_of_right`).
-/

namespace HSFormal.GY

open MeasureTheory Set Filter Topology Function
open scoped ENNReal Pointwise

/-! ### A generic integral bound -/

section Generic

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- If `|F| ≤ c` on `S`, `F = 0` off `S` and `μ S < ∞`, then `|∫ F| ≤ c μ(S)`.
No measurability or integrability is needed. -/
theorem abs_integral_le_mul_measure {F : α → ℝ} {S : Set α} {c : ℝ} (hμS : μ S ≠ ∞)
    (hF : ∀ y ∈ S, |F y| ≤ c) (h0 : ∀ y ∉ S, F y = 0) :
    |∫ y, F y ∂μ| ≤ c * (μ S).toReal := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero h0, ← Real.norm_eq_abs]
  exact norm_setIntegral_le_of_norm_le_const hμS.lt_top fun y hy => by
    rw [Real.norm_eq_abs]; exact hF y hy

/-- A measurable bounded real function vanishing off a set of finite measure is integrable. -/
theorem integrable_of_bdd_of_notMem_eq_zero {f : α → ℝ} {S : Set α} {a : ℝ}
    (hf : Measurable f) (hb : ∀ y, |f y| ≤ a) (hμS : μ S ≠ ∞) (h0 : ∀ y ∉ S, f y = 0) :
    Integrable f μ :=
  (Measure.integrableOn_of_bounded (M := a) hμS hf.aestronglyMeasurable
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hb y)
    ).integrable_of_forall_notMem_eq_zero h0

end Generic

/-! ### The left difference operator -/

section Diff

variable {G : Type*} [Group G]

/-- Tao's `∂_g f x = f x - f (g⁻¹ x)`, i.e. `f - τ_g f` with `τ_g f = f (g⁻¹ ·)`. -/
def ldiff (g : G) (f : G → ℝ) : G → ℝ := fun x => f x - f (g⁻¹ * x)

@[simp] theorem ldiff_apply (g : G) (f : G → ℝ) (x : G) : ldiff g f x = f x - f (g⁻¹ * x) := rfl

@[simp] theorem ldiff_one (f : G → ℝ) : ldiff 1 f = 0 := by
  ext x; simp [ldiff]

/-- `∂_g f` vanishes off `S ∪ g • S` when `f` vanishes off `S`. -/
theorem ldiff_eq_zero_of_notMem {f : G → ℝ} {S : Set G} (hS : ∀ y ∉ S, f y = 0) {g y : G}
    (h1 : y ∉ S) (h2 : y ∉ g • S) : ldiff g f y = 0 := by
  rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul] at h2
  simp [hS y h1, hS _ h2]

/-- `∂_{gh} f x = ∂_g f x + ∂_h f (g⁻¹ x)`. -/
theorem ldiff_mul_apply (g h : G) (f : G → ℝ) (x : G) :
    ldiff (g * h) f x = ldiff g f x + ldiff h f (g⁻¹ * x) := by
  simp only [ldiff, mul_inv_rev, mul_assoc]; ring

/-- `∂_{g⁻¹} f x = - ∂_g f (g x)`. -/
theorem ldiff_inv_apply (g : G) (f : G → ℝ) (x : G) :
    ldiff g⁻¹ f x = -ldiff g f (g * x) := by
  simp [ldiff]

theorem ldiff_sub (g : G) (f₁ f₂ : G → ℝ) : ldiff g (f₁ - f₂) = ldiff g f₁ - ldiff g f₂ := by
  ext x; simp [ldiff]; ring

/-- Telescoping: `∂_{gⁿ} f x = Σ_{i<n} ∂_g f (g⁻ⁱ x)`. -/
theorem ldiff_pow_apply_eq_sum (g : G) (f : G → ℝ) (n : ℕ) (x : G) :
    ldiff (g ^ n) f x = ∑ i ∈ Finset.range n, ldiff g f ((g ^ i)⁻¹ * x) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ldiff_mul_apply, ih, Finset.sum_range_succ]

/-- Tao's identity `∂_{gⁿ} = n ∂_g - Σ_{1 ≤ i < n} ∂_{gⁱ} ∂_g`. -/
theorem ldiff_pow_apply (g : G) (f : G → ℝ) (n : ℕ) (x : G) :
    ldiff (g ^ n) f x
      = n * ldiff g f x - ∑ i ∈ Finset.Ico 1 n, ldiff (g ^ i) (ldiff g f) x := by
  have h1 : ∑ i ∈ Finset.range n, ldiff (g ^ i) (ldiff g f) x
      = ∑ i ∈ Finset.Ico 1 n, ldiff (g ^ i) (ldiff g f) x := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hn]; simp
  rw [← h1, ldiff_pow_apply_eq_sum]
  simp only [ldiff_apply, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  ring

/-- Commutator identity (Tao's commutator `[g,h] = g⁻¹h⁻¹gh`):
`∂_{[g,h]} f (g⁻¹h⁻¹x) = ∂_h ∂_g f x - ∂_g ∂_h f x`. -/
theorem ldiff_commutator_apply (g h : G) (f : G → ℝ) (x : G) :
    ldiff (g⁻¹ * h⁻¹ * g * h) f (g⁻¹ * h⁻¹ * x)
      = ldiff h (ldiff g f) x - ldiff g (ldiff h f) x := by
  have e1 : (g⁻¹ * h⁻¹ * g * h)⁻¹ * (g⁻¹ * h⁻¹ * x) = h⁻¹ * g⁻¹ * x := by group
  rw [ldiff_apply, e1]
  simp only [ldiff_apply, mul_assoc]
  ring

end Diff

/-! ### The translation seminorm `‖g‖_φ` -/

section TNorm

variable {G : Type*} [Group G]

/-- Tao's `‖g‖_φ = sup_x |∂_g φ x| = ‖φ - τ_g φ‖_∞`. (Junk value `0` if `φ` is unbounded; all
lemmas below assume a bound `|φ| ≤ B`.) -/
noncomputable def tnorm (φ : G → ℝ) (g : G) : ℝ := ⨆ x, |ldiff g φ x|

variable {φ : G → ℝ} {B : ℝ}

theorem tnorm_def (φ : G → ℝ) (g : G) : tnorm φ g = ⨆ x, |ldiff g φ x| := rfl

theorem abs_ldiff_le (hB : ∀ x, |φ x| ≤ B) (g x : G) : |ldiff g φ x| ≤ 2 * B := by
  rw [ldiff_apply]
  linarith [abs_sub (φ x) (φ (g⁻¹ * x)), hB x, hB (g⁻¹ * x)]

theorem bddAbove_ldiff (hB : ∀ x, |φ x| ≤ B) (g : G) :
    BddAbove (range fun x => |ldiff g φ x|) :=
  ⟨2 * B, by rintro _ ⟨x, rfl⟩; exact abs_ldiff_le hB g x⟩

theorem abs_ldiff_le_tnorm (hB : ∀ x, |φ x| ≤ B) (g x : G) : |ldiff g φ x| ≤ tnorm φ g :=
  le_ciSup (bddAbove_ldiff hB g) x

theorem tnorm_le {g : G} {c : ℝ} (h : ∀ x, |ldiff g φ x| ≤ c) : tnorm φ g ≤ c :=
  ciSup_le h

theorem tnorm_nonneg (φ : G → ℝ) (g : G) : 0 ≤ tnorm φ g :=
  Real.iSup_nonneg fun _ => abs_nonneg _

@[simp] theorem tnorm_one (φ : G → ℝ) : tnorm φ 1 = 0 :=
  le_antisymm (tnorm_le fun x => by simp) (tnorm_nonneg φ 1)

theorem tnorm_le_two_mul (hB : ∀ x, |φ x| ≤ B) (g : G) : tnorm φ g ≤ 2 * B :=
  tnorm_le (abs_ldiff_le hB g)

theorem tnorm_mul_le (hB : ∀ x, |φ x| ≤ B) (g h : G) :
    tnorm φ (g * h) ≤ tnorm φ g + tnorm φ h :=
  tnorm_le fun x => by
    rw [ldiff_mul_apply]
    exact (abs_add_le _ _).trans
      (add_le_add (abs_ldiff_le_tnorm hB g x) (abs_ldiff_le_tnorm hB h _))

/-- For `0 ≤ φ ≤ B`, `‖g‖_φ ≤ B` (sharper than `tnorm_le_two_mul`). -/
theorem tnorm_le_of_nonneg_of_le (h0 : ∀ x, 0 ≤ φ x) (hB : ∀ x, φ x ≤ B) (g : G) :
    tnorm φ g ≤ B :=
  tnorm_le fun x => by
    rw [ldiff_apply, abs_le]
    constructor <;> linarith [h0 x, hB x, h0 (g⁻¹ * x), hB (g⁻¹ * x)]

theorem tnorm_list_prod_le (hB : ∀ x, |φ x| ≤ B) (l : List G) :
    tnorm φ l.prod ≤ (l.map (tnorm φ)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.prod_cons, List.map_cons, List.sum_cons]
    exact (tnorm_mul_le hB a l.prod).trans (add_le_add le_rfl ih)

theorem tnorm_inv (hB : ∀ x, |φ x| ≤ B) (g : G) : tnorm φ g⁻¹ = tnorm φ g := by
  apply le_antisymm
  · exact tnorm_le fun x => by
      rw [ldiff_inv_apply, abs_neg]; exact abs_ldiff_le_tnorm hB g _
  · exact tnorm_le fun x => by
      have := ldiff_inv_apply g⁻¹ φ x
      rw [inv_inv] at this
      rw [this, abs_neg]; exact abs_ldiff_le_tnorm hB g⁻¹ _

theorem tnorm_pow_le (hB : ∀ x, |φ x| ≤ B) (g : G) (n : ℕ) :
    tnorm φ (g ^ n) ≤ n * tnorm φ g := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    calc tnorm φ (g ^ n * g) ≤ tnorm φ (g ^ n) + tnorm φ g := tnorm_mul_le hB _ _
      _ ≤ n * tnorm φ g + tnorm φ g := by linarith
      _ = (n + 1 : ℕ) * tnorm φ g := by push_cast; ring

/-- `|∂_g φ| ≤ 2B`, packaged for use as the bound of `tnorm (ldiff g φ)`. -/
theorem abs_ldiff_ldiff_le_tnorm (hB : ∀ x, |φ x| ≤ B) (g k x : G) :
    |ldiff k (ldiff g φ) x| ≤ tnorm (ldiff g φ) k :=
  abs_ldiff_le_tnorm (abs_ldiff_le hB g) k x

/-- Tao's telescoping lower bound (Notes 4, proof of Prop. 24):
`n ‖g‖_φ ≤ ‖gⁿ‖_φ + Σ_{1 ≤ i < n} ‖∂_{gⁱ} ∂_g φ‖_∞`
(note `tnorm (ldiff g φ) (g ^ i) = ⨆ x, |ldiff (g ^ i) (ldiff g φ) x|` by definition). -/
theorem tnorm_pow_ge (hB : ∀ x, |φ x| ≤ B) (g : G) (n : ℕ) :
    n * tnorm φ g ≤ tnorm φ (g ^ n) + ∑ i ∈ Finset.Ico 1 n, tnorm (ldiff g φ) (g ^ i) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← le_div_iff₀' hn']
  refine tnorm_le fun x => ?_
  rw [le_div_iff₀' hn', ← abs_of_pos hn', ← abs_mul]
  have key := ldiff_pow_apply g φ n x
  have : (n : ℝ) * ldiff g φ x
      = ldiff (g ^ n) φ x + ∑ i ∈ Finset.Ico 1 n, ldiff (g ^ i) (ldiff g φ) x := by
    linarith
  rw [this]
  refine (abs_add_le _ _).trans (add_le_add (abs_ldiff_le_tnorm hB _ x) ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  exact abs_ldiff_ldiff_le_tnorm hB g _ x

/-- Form of `tnorm_pow_ge` used with a uniform second-difference bound `c`. -/
theorem tnorm_pow_ge_of_le (hB : ∀ x, |φ x| ≤ B) (g : G) (n : ℕ) {c : ℝ}
    (hc : ∀ i ∈ Finset.Ico 1 n, ∀ x, |ldiff (g ^ i) (ldiff g φ) x| ≤ c) :
    n * tnorm φ g ≤ tnorm φ (g ^ n) + ((n - 1 : ℕ) : ℝ) * c := by
  refine (tnorm_pow_ge hB g n).trans (add_le_add le_rfl ?_)
  have := Finset.sum_le_card_nsmul (Finset.Ico 1 n) (fun i => tnorm (ldiff g φ) (g ^ i)) c
    fun i hi => tnorm_le (hc i hi)
  simpa [Nat.card_Ico, nsmul_eq_mul] using this

/-- Commutator bound: `‖g⁻¹h⁻¹gh‖_φ ≤ ‖∂_h ∂_g φ‖_∞ + ‖∂_g ∂_h φ‖_∞`. -/
theorem tnorm_commutator_le (hB : ∀ x, |φ x| ≤ B) (g h : G) :
    tnorm φ (g⁻¹ * h⁻¹ * g * h) ≤ tnorm (ldiff g φ) h + tnorm (ldiff h φ) g :=
  tnorm_le fun z => by
    have := ldiff_commutator_apply g h φ (h * g * z)
    have e : g⁻¹ * h⁻¹ * (h * g * z) = z := by group
    rw [e] at this
    rw [this]
    exact (abs_sub _ _).trans
      (add_le_add (abs_ldiff_ldiff_le_tnorm hB g h _) (abs_ldiff_ldiff_le_tnorm hB h g _))

theorem abs_tnorm_sub_tnorm_le (hB : ∀ x, |φ x| ≤ B) (g h : G) :
    |tnorm φ g - tnorm φ h| ≤ tnorm φ (g⁻¹ * h) := by
  have h1 := tnorm_mul_le hB g (g⁻¹ * h)
  have h2 := tnorm_mul_le hB h (h⁻¹ * g)
  rw [mul_inv_cancel_left] at h1 h2
  have h3 : tnorm φ (h⁻¹ * g) = tnorm φ (g⁻¹ * h) := by
    rw [← tnorm_inv hB (g⁻¹ * h), mul_inv_rev, inv_inv]
  rw [abs_le]; constructor <;> linarith

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- If `‖g‖_φ → 0` as `g → 1` then `g ↦ ‖g‖_φ` is continuous. -/
theorem continuous_tnorm (hB : ∀ x, |φ x| ≤ B) (h1 : Tendsto (tnorm φ) (𝓝 1) (𝓝 0)) :
    Continuous (tnorm φ) := by
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  have ht : Tendsto (fun g => g₀⁻¹ * g) (𝓝 g₀) (𝓝 1) := by
    have : Tendsto (fun g : G => g₀⁻¹ * g) (𝓝 g₀) (𝓝 (g₀⁻¹ * g₀)) :=
      (continuous_const.mul continuous_id).tendsto g₀
    rwa [inv_mul_cancel] at this
  have h2 := h1.comp ht
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun g => ?_) h2
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact abs_tnorm_sub_tnorm_le hB g₀ g

/-- If `‖g‖_φ → 0` as `g → 1` then `φ` is continuous. -/
theorem continuous_of_tendsto_tnorm (hB : ∀ x, |φ x| ≤ B)
    (h1 : Tendsto (tnorm φ) (𝓝 1) (𝓝 0)) : Continuous φ := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  have ht : Tendsto (fun x => x₀ * x⁻¹) (𝓝 x₀) (𝓝 1) := by
    have := (continuous_const.mul continuous_inv).tendsto x₀ (f := fun x : G => x₀ * x⁻¹)
    simpa using this
  have h2 := h1.comp ht
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun x => ?_) h2
  have := abs_ldiff_le_tnorm hB (x₀ * x⁻¹) x₀
  rw [ldiff_apply, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one] at this
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact this

/-- **Left uniform continuity.** For continuous compactly supported `φ`,
`‖τ_g φ - φ‖_∞ → 0` as `g → 1`. -/
theorem tendsto_tnorm_nhds_one (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Tendsto (tnorm φ) (𝓝 1) (𝓝 0) := by
  set K := tsupport φ
  have key : ∀ ε > 0, ∀ᶠ g in 𝓝 (1 : G), ∀ x, |ldiff g φ x| < ε := by
    intro ε hε
    have P1 : ∀ᶠ g in 𝓝 (1 : G), ∀ y ∈ K, |φ (g⁻¹ * y) - φ y| < ε := by
      refine hc.eventually_forall_of_forall_eventually fun y _ => ?_
      have hcont : Continuous fun z : G × G => |φ (z.1⁻¹ * z.2) - φ z.2| := by fun_prop
      exact (hcont.tendsto (1, y)).eventually_lt_const (by simpa using hε)
    have P2 : ∀ᶠ g in 𝓝 (1 : G), ∀ y ∈ K, |φ (g * y) - φ y| < ε := by
      refine hc.eventually_forall_of_forall_eventually fun y _ => ?_
      have hcont : Continuous fun z : G × G => |φ (z.1 * z.2) - φ z.2| := by fun_prop
      exact (hcont.tendsto (1, y)).eventually_lt_const (by simpa using hε)
    filter_upwards [P1, P2] with g h1 h2 x
    rw [ldiff_apply]
    by_cases hx : x ∈ K
    · rw [abs_sub_comm]; exact h1 x hx
    by_cases hy : g⁻¹ * x ∈ K
    · have := h2 _ hy
      rwa [mul_inv_cancel_left] at this
    rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hy]
    simpa using hε
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [key (ε / 2) (half_pos hε)] with g hg
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (tnorm_nonneg φ g)]
  exact (tnorm_le fun x => (hg x).le).trans_lt (half_lt_self hε)

end TNorm

/-! ### Convolution -/

section Conv

variable {G : Type*} [Group G] [MeasurableSpace G] {μ : Measure G} {ψ η : G → ℝ}

/-- `conv μ ψ η x = ∫ y, ψ y * η (y⁻¹ * x) ∂μ` (Tao's `ψ ⋆ η`). -/
noncomputable def conv (μ : Measure G) (ψ η : G → ℝ) (x : G) : ℝ := ∫ y, ψ y * η (y⁻¹ * x) ∂μ

theorem conv_apply (μ : Measure G) (ψ η : G → ℝ) (x : G) :
    conv μ ψ η x = ∫ y, ψ y * η (y⁻¹ * x) ∂μ := rfl

/-- Right translation commutes with convolution (pure algebra). -/
theorem conv_mul_right (μ : Measure G) (ψ η : G → ℝ) (x h : G) :
    conv μ ψ η (x * h) = conv μ ψ (fun z => η (z * h)) x := by
  simp only [conv_apply, mul_assoc]

theorem exists_ne_zero_of_conv_ne_zero {x : G} (h : conv μ ψ η x ≠ 0) :
    ∃ y, ψ y ≠ 0 ∧ η (y⁻¹ * x) ≠ 0 := by
  by_contra hne
  push Not at hne
  apply h
  rw [conv_apply]
  have : (fun y => ψ y * η (y⁻¹ * x)) = fun _ => 0 := by
    ext y
    by_cases hy : ψ y = 0
    · simp [hy]
    · simp [hne y hy]
  rw [this, integral_zero]

/-- `supp (ψ ⋆ η) ⊆ supp ψ · supp η`. -/
theorem support_conv_subset : support (conv μ ψ η) ⊆ support ψ * support η := by
  intro x hx
  obtain ⟨y, hy, hy'⟩ := exists_ne_zero_of_conv_ne_zero hx
  exact ⟨y, hy, y⁻¹ * x, hy', mul_inv_cancel_left y x⟩

/-- Tao: if `(ψ ⋆ η)(x) ≠ 0` (e.g. `> 0`) with `supp ψ ⊆ S`, `supp η ⊆ T`, then `x ∈ S * T`. -/
theorem mem_mul_of_conv_ne_zero {S T : Set G} (hS : support ψ ⊆ S) (hT : support η ⊆ T)
    {x : G} (h : conv μ ψ η x ≠ 0) : x ∈ S * T :=
  mul_subset_mul hS hT (support_conv_subset h)

theorem hasCompactSupport_conv [TopologicalSpace G] [ContinuousMul G] [T2Space G]
    (hψ : HasCompactSupport ψ) (hη : HasCompactSupport η) : HasCompactSupport (conv μ ψ η) := by
  have hK : IsCompact (tsupport ψ * tsupport η) := hψ.mul hη
  refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
  exact support_conv_subset.trans (mul_subset_mul subset_closure subset_closure)

theorem conv_nonneg (hψ : ∀ y, 0 ≤ ψ y) (hη : ∀ z, 0 ≤ η z) (x : G) : 0 ≤ conv μ ψ η x :=
  integral_nonneg fun y => mul_nonneg (hψ y) (hη _)

/-- Sup bound through the support of the left factor: `|ψ ⋆ η| ≤ ‖ψ‖_∞ ‖η‖_∞ μ(S)`. -/
theorem abs_conv_le {S : Set G} {a b : ℝ} (hμS : μ S ≠ ∞) (hψ : ∀ y ∈ S, |ψ y| ≤ a)
    (hψS : ∀ y ∉ S, ψ y = 0) (hη : ∀ z, |η z| ≤ b) (x : G) :
    |conv μ ψ η x| ≤ a * b * (μ S).toReal := by
  refine abs_integral_le_mul_measure hμS (fun y hy => ?_) (fun y hy => by simp [hψS y hy])
  rw [abs_mul]
  exact mul_le_mul (hψ y hy) (hη _) (abs_nonneg _) ((abs_nonneg _).trans (hψ y hy))

theorem conv_le {S : Set G} {a b : ℝ} (hμS : μ S ≠ ∞) (hψ : ∀ y ∈ S, |ψ y| ≤ a)
    (hψS : ∀ y ∉ S, ψ y = 0) (hη : ∀ z, |η z| ≤ b) (x : G) :
    conv μ ψ η x ≤ a * b * (μ S).toReal :=
  (le_abs_self _).trans (abs_conv_le hμS hψ hψS hη x)

/-- Sup bound through the support `T` of the right factor (left invariance:
`μ {y | y⁻¹ x ∈ T} = μ T⁻¹`). -/
theorem abs_conv_le_of_right [MeasurableMul G] [μ.IsMulLeftInvariant] {T : Set G} {a b : ℝ}
    (hμT : μ T⁻¹ ≠ ∞) (hψ : ∀ y, |ψ y| ≤ a) (hη : ∀ z ∈ T, |η z| ≤ b)
    (hηT : ∀ z ∉ T, η z = 0) (x : G) :
    |conv μ ψ η x| ≤ a * b * (μ T⁻¹).toReal := by
  have hmem : ∀ y, y ∈ (fun y => x⁻¹ * y) ⁻¹' T⁻¹ ↔ y⁻¹ * x ∈ T := by
    intro y; simp [mul_inv_rev]
  rw [← measure_preimage_mul μ x⁻¹ T⁻¹] at hμT ⊢
  refine abs_integral_le_mul_measure hμT (fun y hy => ?_) (fun y hy => ?_)
  · rw [abs_mul]
    exact mul_le_mul (hψ y) (hη _ ((hmem y).1 hy)) (abs_nonneg _) ((abs_nonneg _).trans (hψ y))
  · simp [hηT _ (fun h => hy ((hmem y).2 h))]

/-- `‖ψ ⋆ η‖_∞ ≤ ‖ψ‖₁ ‖η‖_∞`. -/
theorem abs_conv_le_integral {b : ℝ} (hψ : Integrable ψ μ) (hη : ∀ z, |η z| ≤ b) (x : G) :
    |conv μ ψ η x| ≤ (∫ y, |ψ y| ∂μ) * b := by
  rw [← integral_mul_const, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (hψ.abs.mul_const b) (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (hη _) (abs_nonneg _)

variable [MeasurableMul G]

theorem integrable_ldiff [μ.IsMulLeftInvariant] (hψ : Integrable ψ μ) (g : G) :
    Integrable (ldiff g ψ) μ :=
  hψ.sub (hψ.comp_mul_left g⁻¹)

theorem measurable_ldiff {f : G → ℝ} (hf : Measurable f) (g : G) : Measurable (ldiff g f) :=
  hf.sub (hf.comp (measurable_const_mul g⁻¹))

/-- `μ (g • S) = μ S` (left invariance; any set `S`). -/
theorem measure_smul_set [μ.IsMulLeftInvariant] (g : G) (S : Set G) : μ (g • S) = μ S := by
  rw [← Set.preimage_smul_inv, ← measure_preimage_mul μ g⁻¹ S]
  rfl

/-- Left translation commutes with convolution (left invariance of `μ`):
`(τ_{g⁻¹} ψ) ⋆ η = τ_{g⁻¹} (ψ ⋆ η)`. -/
theorem conv_comp_mul_left [μ.IsMulLeftInvariant] (g x : G) :
    conv μ (fun y => ψ (g * y)) η x = conv μ ψ η (g * x) := by
  rw [conv_apply, conv_apply,
    ← integral_mul_left_eq_self (fun y => ψ y * η (y⁻¹ * (g * x))) g]
  congr 1; ext y
  congr 2; group

variable [MeasurableInv G]

theorem integrable_conv_integrand {b : ℝ} (hψ : Integrable ψ μ) (hη : Measurable η)
    (hηb : ∀ z, |η z| ≤ b) (x : G) : Integrable (fun y => ψ y * η (y⁻¹ * x)) μ :=
  hψ.mul_bdd (hη.comp (measurable_inv.mul_const x)).aestronglyMeasurable
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hηb _)

/-- Lower bound: if `ψ, η ≥ 0` and `ψ y η(y⁻¹x) ≥ c` on a measurable `U`, then
`c μ(U) ≤ (ψ ⋆ η)(x)`. -/
theorem le_conv {U : Set G} {b c : ℝ} (hU : MeasurableSet U) (hψ : Integrable ψ μ)
    (hη : Measurable η) (hηb : ∀ z, |η z| ≤ b) (hψ0 : ∀ y, 0 ≤ ψ y) (hη0 : ∀ z, 0 ≤ η z)
    {x : G} (hc : ∀ y ∈ U, c ≤ ψ y * η (y⁻¹ * x)) : c * (μ U).toReal ≤ conv μ ψ η x := by
  by_cases hμU : μ U = ∞
  · simpa [hμU] using conv_nonneg hψ0 hη0 x
  have hi := integrable_conv_integrand hψ hη hηb x
  calc c * (μ U).toReal ≤ ∫ y in U, ψ y * η (y⁻¹ * x) ∂μ :=
        setIntegral_ge_of_const_le_real hU hμU hc hi.integrableOn
    _ ≤ conv μ ψ η x :=
        setIntegral_le_integral hi (Eventually.of_forall fun y => mul_nonneg (hψ0 y) (hη0 _))

theorem conv_sub_left {b : ℝ} {ψ₁ ψ₂ : G → ℝ} (hψ₁ : Integrable ψ₁ μ) (hψ₂ : Integrable ψ₂ μ)
    (hη : Measurable η) (hηb : ∀ z, |η z| ≤ b) (x : G) :
    conv μ (ψ₁ - ψ₂) η x = conv μ ψ₁ η x - conv μ ψ₂ η x := by
  simp only [conv_apply, Pi.sub_apply, sub_mul]
  exact integral_sub (integrable_conv_integrand hψ₁ hη hηb x)
    (integrable_conv_integrand hψ₂ hη hηb x)

theorem conv_sub_right {b₁ b₂ : ℝ} {η₁ η₂ : G → ℝ} (hψ : Integrable ψ μ)
    (hη₁ : Measurable η₁) (hη₁b : ∀ z, |η₁ z| ≤ b₁) (hη₂ : Measurable η₂)
    (hη₂b : ∀ z, |η₂ z| ≤ b₂) (x : G) :
    conv μ ψ (η₁ - η₂) x = conv μ ψ η₁ x - conv μ ψ η₂ x := by
  simp only [conv_apply, Pi.sub_apply, mul_sub]
  exact integral_sub (integrable_conv_integrand hψ hη₁ hη₁b x)
    (integrable_conv_integrand hψ hη₂ hη₂b x)

/-- **Tao (9).** `∂_g (ψ ⋆ η) = (∂_g ψ) ⋆ η`. -/
theorem ldiff_conv [μ.IsMulLeftInvariant] {b : ℝ} (hψ : Integrable ψ μ) (hη : Measurable η)
    (hηb : ∀ z, |η z| ≤ b) (g : G) : ldiff g (conv μ ψ η) = conv μ (ldiff g ψ) η := by
  ext x
  have h := conv_sub_left hψ (hψ.comp_mul_left g⁻¹) hη hηb x
  rw [conv_comp_mul_left] at h
  rw [ldiff_apply, ← h]
  rfl

/-- **Tao (10).** `∂_k ∂_g (ψ ⋆ η)(x) = ∫ ∂_g ψ(y) · ∂_{y⁻¹ k y} η (y⁻¹ x) dμ(y)`. -/
theorem ldiff_ldiff_conv [μ.IsMulLeftInvariant] {b : ℝ} (hψ : Integrable ψ μ)
    (hη : Measurable η) (hηb : ∀ z, |η z| ≤ b) (g k x : G) :
    ldiff k (ldiff g (conv μ ψ η)) x
      = ∫ y, ldiff g ψ y * ldiff (y⁻¹ * k * y) η (y⁻¹ * x) ∂μ := by
  rw [ldiff_conv hψ hη hηb g, ldiff_apply, conv_apply, conv_apply,
    ← integral_sub (integrable_conv_integrand (integrable_ldiff hψ g) hη hηb x)
      (integrable_conv_integrand (integrable_ldiff hψ g) hη hηb (k⁻¹ * x))]
  congr 1; ext y
  have e : (y⁻¹ * k * y)⁻¹ * (y⁻¹ * x) = y⁻¹ * (k⁻¹ * x) := by group
  simp only [ldiff_apply]
  rw [e, mul_sub]

/-- **Translation seminorm of a convolution.** If `|ψ| ≤ a` vanishes off `S` (`μ S < ∞`) and
`|η| ≤ b`, then `‖g‖_{ψ ⋆ η} ≤ 2 μ(S) b ‖g‖_ψ`. -/
theorem tnorm_conv_le [μ.IsMulLeftInvariant] {S : Set G} {a b : ℝ} (hμS : μ S ≠ ∞)
    (hψ : Measurable ψ) (hψb : ∀ y, |ψ y| ≤ a) (hψS : ∀ y ∉ S, ψ y = 0)
    (hη : Measurable η) (hηb : ∀ z, |η z| ≤ b) (g : G) :
    tnorm (conv μ ψ η) g ≤ 2 * (μ S).toReal * b * tnorm ψ g := by
  have hψi : Integrable ψ μ := integrable_of_bdd_of_notMem_eq_zero hψ hψb hμS hψS
  set S' : Set G := S ∪ (fun y => g⁻¹ * y) ⁻¹' S
  have hS'le : μ S' ≤ μ S + μ S :=
    (measure_union_le _ _).trans (by rw [measure_preimage_mul])
  have hμS' : μ S' ≠ ∞ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hμS, hμS⟩) hS'le
  have hS'real : (μ S').toReal ≤ 2 * (μ S).toReal := by
    rw [two_mul, ← ENNReal.toReal_add hμS hμS]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hμS, hμS⟩) hS'le
  have hb0 : 0 ≤ b := (abs_nonneg _).trans (hηb 1)
  refine tnorm_le fun x => ?_
  rw [ldiff_conv hψi hη hηb g]
  refine (abs_conv_le hμS' (fun y _ => abs_ldiff_le_tnorm hψb g y) (fun y hy => ?_) hηb x).trans ?_
  · simp only [S', mem_union, mem_preimage, not_or] at hy
    simp [hψS _ hy.1, hψS _ hy.2]
  · have := mul_le_mul_of_nonneg_left hS'real (mul_nonneg (tnorm_nonneg ψ g) hb0)
    linarith

/-- Right-translation continuity estimate (no invariance of `μ` needed):
`|(ψ ⋆ η)(x h) - (ψ ⋆ η)(x)| ≤ ‖ψ‖₁ · ‖h‖_{η ∘ inv}`. -/
theorem abs_conv_mul_right_sub_le {b : ℝ} (hψ : Integrable ψ μ) (hη : Measurable η)
    (hηb : ∀ z, |η z| ≤ b) (x h : G) :
    |conv μ ψ η (x * h) - conv μ ψ η x|
      ≤ (∫ y, |ψ y| ∂μ) * tnorm (fun z => η z⁻¹) h := by
  have hη' : ∀ z, |(fun z => η z⁻¹) z| ≤ b := fun z => hηb _
  rw [conv_mul_right, ← conv_sub_right (η₁ := fun z => η (z * h)) hψ
    (hη.comp (measurable_mul_const h)) (fun z => hηb _) hη hηb x]
  refine abs_conv_le_integral hψ (fun z => ?_) x
  have := abs_ldiff_le_tnorm hη' h z⁻¹
  simp only [ldiff_apply, inv_inv, mul_inv_rev] at this
  rw [Pi.sub_apply, abs_sub_comm]
  exact this

variable [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]

/-- **Uniform continuity of a convolution.** For `ψ` continuous with compact support and `η`
measurable bounded, `‖τ_g(ψ ⋆ η) - ψ ⋆ η‖_∞ → 0` as `g → 1`. -/
theorem tendsto_tnorm_conv [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] {b : ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hη : Measurable η)
    (hηb : ∀ z, |η z| ≤ b) : Tendsto (tnorm (conv μ ψ η)) (𝓝 1) (𝓝 0) := by
  obtain ⟨a, ha⟩ := hψc.exists_bound_of_continuous hψ
  have hμS : μ (tsupport ψ) ≠ ∞ := hψc.measure_lt_top.ne
  have h0 : ∀ y ∉ tsupport ψ, ψ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  have hle := tnorm_conv_le (μ := μ) hμS hψ.measurable (fun y => ha y) h0 hη hηb
  have ht := (tendsto_tnorm_nhds_one hψ hψc).const_mul (2 * (μ (tsupport ψ)).toReal * b)
  rw [mul_zero] at ht
  exact squeeze_zero (fun g => tnorm_nonneg _ g) hle ht

/-- Continuity of `ψ ⋆ η` for `ψ` continuous compactly supported, `η` measurable bounded. -/
theorem continuous_conv_of_left [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] {b : ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hη : Measurable η)
    (hηb : ∀ z, |η z| ≤ b) : Continuous (conv μ ψ η) := by
  obtain ⟨a, ha⟩ := hψc.exists_bound_of_continuous hψ
  have hμS : μ (tsupport ψ) ≠ ∞ := hψc.measure_lt_top.ne
  have h0 : ∀ y ∉ tsupport ψ, ψ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  exact continuous_of_tendsto_tnorm
    (abs_conv_le hμS (fun y _ => ha y) h0 hηb) (tendsto_tnorm_conv hψ hψc hη hηb)

/-- Continuity of `ψ ⋆ η` for `ψ` integrable (e.g. a lower semicontinuous bump), `η` continuous
compactly supported. No invariance of `μ` is needed. -/
theorem continuous_conv_of_right (hψ : Integrable ψ μ) (hη : Continuous η)
    (hηc : HasCompactSupport η) : Continuous (conv μ ψ η) := by
  obtain ⟨b, hb⟩ := hηc.exists_bound_of_continuous hη
  have hηb : ∀ z, |η z| ≤ b := fun z => hb z
  have hη' : Continuous fun z : G => η z⁻¹ := hη.comp continuous_inv
  have hηc' : HasCompactSupport fun z : G => η z⁻¹ :=
    hηc.comp_homeomorph (Homeomorph.inv G)
  have h1 := tendsto_tnorm_nhds_one hη' hηc'
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  have ht : Tendsto (fun x => x₀⁻¹ * x) (𝓝 x₀) (𝓝 1) := by
    have : Tendsto (fun x : G => x₀⁻¹ * x) (𝓝 x₀) (𝓝 (x₀⁻¹ * x₀)) :=
      (continuous_const.mul continuous_id).tendsto x₀
    rwa [inv_mul_cancel] at this
  have h2 := (h1.comp ht).const_mul (∫ y, |ψ y| ∂μ)
  rw [mul_zero] at h2
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun x => ?_) h2
  have := abs_conv_mul_right_sub_le hψ hη.measurable hηb x₀ (x₀⁻¹ * x)
  rw [mul_inv_cancel_left] at this
  rw [Real.norm_eq_abs]
  exact this

end Conv

end HSFormal.GY
