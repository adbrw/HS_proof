import HSFormal.Statement
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Gleason–Yamabe (`HSFormal.NSSIsLie`): frozen interfaces

This file fixes the data passed between the tracks of `blueprint/gleason-yamabe.md`:

* `WeakGleasonNorm G` (Tao 254A Notes 4): output of track A4, input of A5 and of track B.
* `GleasonNorm G` (Tao 254A Notes 2, Def. 6): output of A5, input of track B.
* `OneParam G`: continuous one-parameter subgroups `ℝ → G` (Tao's `L(G)`), used by B2–B5.
* `LocalExpStructure G E`: output of track B (B5), input of track C.
* `LocalExpStructure.mu` and `LocalExpStructure.ContDiffMu`: the conclusion of C3 and the hypothesis
  of C4.

together with the shared lemmas of blueprint §3 (escape-to-scale `WeakGleasonNorm.N_le_of_pow_le`,
compactness of small balls `WeakGleasonNorm.exists_isCompact_le`, `OneParam.ext_of_eqOn`) and the
elementary API that several tracks need.

Conventions. `d(g, h) := N (g⁻¹ * h)` is `WeakGleasonNorm.d`. The commutator in
`GleasonNorm.commutator` is Tao's `g⁻¹ * h⁻¹ * g * h` (not mathlib's `⁅g, h⁆ = g * h * g⁻¹ * h⁻¹`).

## Changes with respect to blueprint §3

1. `WeakGleasonNorm.nonneg` is a theorem, not a field: it follows from `map_one`, `map_inv`,
   `mul_le` (`N 1 ≤ N g + N g⁻¹ = 2 N g`). Producers have one field less; consumers use
   `𝒩.nonneg g` exactly as before.
2. `LocalExpStructure.trotter` is a theorem, not a field, and it holds for **all** `X Y : E`
   (no smallness assumption): it follows from `c11`, `exp_add_smul` and `continuous_exp`, since
   `(exp (X/n) * exp (Y/n)) ^ n = exp (n • μ(X/n, Y/n))` and `‖n • μ(X/n,Y/n) - (X+Y)‖ ≤ K‖X‖‖Y‖/n`.
   So B5 does not have to provide it.
3. Added `LocalExpStructure.mu` (`μ X Y = chart.symm (exp X * exp Y)`) and the `Prop`
   `LocalExpStructure.ContDiffMu` (blueprint: "conclusion of `contDiffOn_mu`"), so that C3 proves
   `S.ContDiffMu` and C4 assumes `hμ : S.ContDiffMu`, with no risk of the two statements drifting.
4. Producer helpers (no change of the structures): `WeakGleasonNorm.ofLE` (raise `C`),
   `WeakGleasonNorm.toGleasonNorm` (a commutator estimate with any constant `K` and any threshold
   `c > 0` gives a `GleasonNorm` with the same `N`), `WeakGleasonNorm.continuous_of_mul_le`
   (in a topological group, a symmetric subadditive `N` whose sublevel sets `{N < r}`, `r > 0`, are
   neighbourhoods of `1` is continuous), `LocalExpStructure.chartOfInjOn` (the `chart` field from
   an exponential injective and open on an open set; `chart_coe` is then `rfl`), and
   `LocalExpStructure.transport` (blueprint B5's `transport`, moved here).
5. `OneParam G` has a `FunLike` instance (so `X t` and `DFunLike.ext` work), and
   `LocalExpStructure.toOneParam` turns a ray `t ↦ exp (t • X)` into a `OneParam`.
6. Consumer helpers for track C: `LocalExpStructure.clm_ext` (the linear map in `conj g` is unique,
   so C1's `Ad` is well defined) and the ray-lifting lemma
   `LocalExpStructure.symm_exp_of_forall_mem_target` (if `exp (s • W) ∈ chart.target` for all
   `s ∈ [0,1]` then `chart.symm (exp W) = W`; this gives `Ad g X = log (g exp X g⁻¹)` for `g` near
   `1`, i.e. the continuity of `Ad`, in spite of `exp` not being globally injective).

Sanity checks at the end: for a real normed space `E`, the additive group `Multiplicative E` carries
a `GleasonNorm` (`‖·‖`, `C = 2`), a `OneParam` through every vector, and `LocalExpStructure`s with
`exp = ofAdd` (with a global chart, satisfying `ContDiffMu`, and with the local chart
`chartOfInjOn … (ball 0 1)`); and every weak Gleason norm forces `NoSmallSubgroups`
(`WeakGleasonNorm.noSmallSubgroups`), which checks the direction of the escape field.
-/

noncomputable section

namespace HSFormal.GY

open Filter Topology
open scoped ContDiff

/-! ## Weak Gleason norms -/

/-- Tao 254A Notes 4, weak Gleason metric: `d(g,h) = N (g⁻¹ * h)` is a left-invariant metric
generating the topology (`continuous`, `small_subset`), with the escape property. -/
structure WeakGleasonNorm (G : Type*) [Group G] [TopologicalSpace G] where
  /-- The norm `N g = d(1, g)`. -/
  N : G → ℝ
  /-- The constant of the escape property (and of the commutator estimate of `GleasonNorm`). -/
  C : ℝ
  two_le_C : 2 ≤ C
  map_one : N 1 = 0
  map_inv : ∀ g, N g⁻¹ = N g
  mul_le : ∀ g h, N (g * h) ≤ N g + N h
  eq_one : ∀ g, N g = 0 → g = 1
  continuous : Continuous N
  small_subset : ∀ U ∈ 𝓝 (1 : G), ∃ r > 0, {g | N g < r} ⊆ U
  escape : ∀ (g : G) (n : ℕ), (n : ℝ) * N g ≤ C⁻¹ → (n : ℝ) * N g ≤ C * N (g ^ n)

/-- Tao 254A Notes 2, Def. 6: a weak Gleason norm with the commutator estimate. The commutator is
Tao's `g⁻¹ * h⁻¹ * g * h` (not mathlib's `⁅g, h⁆ = g * h * g⁻¹ * h⁻¹`). -/
structure GleasonNorm (G : Type*) [Group G] [TopologicalSpace G] extends WeakGleasonNorm G where
  commutator : ∀ g h, N g ≤ C⁻¹ → N h ≤ C⁻¹ → N (g⁻¹ * h⁻¹ * g * h) ≤ C * N g * N h

namespace WeakGleasonNorm

variable {G : Type*} [Group G] [TopologicalSpace G] (𝒩 : WeakGleasonNorm G)

theorem nonneg (g : G) : 0 ≤ 𝒩.N g := by
  have h := 𝒩.mul_le g g⁻¹
  rw [mul_inv_cancel, 𝒩.map_one, 𝒩.map_inv] at h
  linarith

theorem C_pos : 0 < 𝒩.C := by linarith [𝒩.two_le_C]

theorem one_le_C : 1 ≤ 𝒩.C := by linarith [𝒩.two_le_C]

theorem C_inv_pos : 0 < 𝒩.C⁻¹ := inv_pos.2 𝒩.C_pos

theorem C_inv_le_half : 𝒩.C⁻¹ ≤ 1 / 2 := by
  rw [one_div]; exact inv_anti₀ (by norm_num) 𝒩.two_le_C

theorem C_inv_le_one : 𝒩.C⁻¹ ≤ 1 := 𝒩.C_inv_le_half.trans (by norm_num)

@[simp] theorem N_one : 𝒩.N 1 = 0 := 𝒩.map_one

@[simp] theorem N_inv (g : G) : 𝒩.N g⁻¹ = 𝒩.N g := 𝒩.map_inv g

theorem N_eq_zero {g : G} : 𝒩.N g = 0 ↔ g = 1 :=
  ⟨𝒩.eq_one g, fun h => h ▸ 𝒩.map_one⟩

theorem N_pos {g : G} (hg : g ≠ 1) : 0 < 𝒩.N g :=
  (𝒩.nonneg g).lt_of_ne (fun h => hg (𝒩.eq_one g h.symm))

theorem N_mul_le (g h : G) : 𝒩.N (g * h) ≤ 𝒩.N g + 𝒩.N h := 𝒩.mul_le g h

theorem N_pow_le (g : G) (n : ℕ) : 𝒩.N (g ^ n) ≤ n * 𝒩.N g := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    calc 𝒩.N (g ^ n * g) ≤ 𝒩.N (g ^ n) + 𝒩.N g := 𝒩.mul_le _ _
      _ ≤ n * 𝒩.N g + 𝒩.N g := by linarith
      _ = ((n + 1 : ℕ) : ℝ) * 𝒩.N g := by push_cast; ring

theorem N_zpow_le (g : G) (n : ℤ) : 𝒩.N (g ^ n) ≤ |(n : ℝ)| * 𝒩.N g := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · simpa using 𝒩.N_pow_le g m
  · simpa using 𝒩.N_pow_le g m

theorem N_list_prod_le (l : List G) : 𝒩.N l.prod ≤ (l.map 𝒩.N).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.prod_cons, List.map_cons, List.sum_cons]
    linarith [𝒩.mul_le a l.prod]

/-- `|N g - N h| ≤ N (g⁻¹ * h)`. -/
theorem abs_sub_le (g h : G) : |𝒩.N g - 𝒩.N h| ≤ 𝒩.N (g⁻¹ * h) := by
  have h1 := 𝒩.mul_le g (g⁻¹ * h)
  have h2 := 𝒩.mul_le h (h⁻¹ * g)
  rw [mul_inv_cancel_left] at h1 h2
  have h3 : 𝒩.N (h⁻¹ * g) = 𝒩.N (g⁻¹ * h) := by rw [← 𝒩.map_inv]; group
  rw [abs_le]; constructor <;> linarith

/-- The escape property in the form `N (g ^ n) ≥ n N g / C`. -/
theorem escape' {g : G} {n : ℕ} (h : (n : ℝ) * 𝒩.N g ≤ 𝒩.C⁻¹) :
    (n : ℝ) * 𝒩.N g / 𝒩.C ≤ 𝒩.N (g ^ n) := by
  rw [div_le_iff₀ 𝒩.C_pos, mul_comm (𝒩.N _)]; exact 𝒩.escape g n h

/-! ### The left-invariant metric `d g h = N (g⁻¹ * h)` -/

/-- The left-invariant metric `d(g,h) = N (g⁻¹ * h)` attached to `N`. -/
def d (g h : G) : ℝ := 𝒩.N (g⁻¹ * h)

theorem d_def (g h : G) : 𝒩.d g h = 𝒩.N (g⁻¹ * h) := rfl

theorem d_nonneg (g h : G) : 0 ≤ 𝒩.d g h := 𝒩.nonneg _

@[simp] theorem d_self (g : G) : 𝒩.d g g = 0 := by simp [d]

theorem d_comm (g h : G) : 𝒩.d g h = 𝒩.d h g := by
  rw [d, d, ← 𝒩.map_inv]; group

theorem d_triangle (g h k : G) : 𝒩.d g k ≤ 𝒩.d g h + 𝒩.d h k := by
  have := 𝒩.mul_le (g⁻¹ * h) (h⁻¹ * k)
  rwa [show g⁻¹ * h * (h⁻¹ * k) = g⁻¹ * k by group] at this

@[simp] theorem d_mul_left (k g h : G) : 𝒩.d (k * g) (k * h) = 𝒩.d g h := by
  rw [d, d]; congr 1; group

@[simp] theorem d_one_left (g : G) : 𝒩.d 1 g = 𝒩.N g := by simp [d]

@[simp] theorem d_one_right (g : G) : 𝒩.d g 1 = 𝒩.N g := by simp [d]

@[simp] theorem d_self_mul (g h : G) : 𝒩.d g (g * h) = 𝒩.N h := by simp [d]

@[simp] theorem d_mul_self (g h : G) : 𝒩.d (g * h) g = 𝒩.N h := by
  rw [d_comm]; simp [d]

theorem d_eq_zero {g h : G} : 𝒩.d g h = 0 ↔ g = h := by
  rw [d, 𝒩.N_eq_zero, inv_mul_eq_one]

/-- Telescoping triangle inequality. -/
theorem d_le_sum (P : ℕ → G) (n : ℕ) :
    𝒩.d (P 0) (P n) ≤ ∑ i ∈ Finset.range n, 𝒩.d (P i) (P (i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact (𝒩.d_triangle _ (P n) _).trans (by linarith)

/-! ### Topology -/

theorem isOpen_setOf_lt (r : ℝ) : IsOpen {g | 𝒩.N g < r} :=
  isOpen_lt 𝒩.continuous continuous_const

theorem isClosed_setOf_le (r : ℝ) : IsClosed {g | 𝒩.N g ≤ r} :=
  isClosed_le 𝒩.continuous continuous_const

theorem setOf_lt_mem_nhds {r : ℝ} (hr : 0 < r) : {g | 𝒩.N g < r} ∈ 𝓝 (1 : G) :=
  (𝒩.isOpen_setOf_lt r).mem_nhds (by simpa using hr)

theorem setOf_le_mem_nhds {r : ℝ} (hr : 0 < r) : {g | 𝒩.N g ≤ r} ∈ 𝓝 (1 : G) :=
  Filter.mem_of_superset (𝒩.setOf_lt_mem_nhds hr) fun x (hx : 𝒩.N x < r) => (hx.le : 𝒩.N x ≤ r)

/-- The sublevel sets `{N < r}`, `r > 0`, form a basis of neighbourhoods of `1`. -/
theorem hasBasis_nhds_one :
    (𝓝 (1 : G)).HasBasis (fun r : ℝ => 0 < r) (fun r => {g | 𝒩.N g < r}) :=
  ⟨fun U => ⟨fun hU => 𝒩.small_subset U hU,
    fun ⟨_, hr, h⟩ => Filter.mem_of_superset (𝒩.setOf_lt_mem_nhds hr) h⟩⟩

theorem tendsto_nhds_one_iff {α : Type*} {l : Filter α} {f : α → G} :
    Tendsto f l (𝓝 1) ↔ Tendsto (fun x => 𝒩.N (f x)) l (𝓝 0) := by
  rw [𝒩.hasBasis_nhds_one.tendsto_right_iff, Metric.tendsto_nhds]
  refine forall₂_congr fun r _ => ?_
  simp [abs_of_nonneg (𝒩.nonneg _)]

/-- In a topological group, the `d`-balls form a basis of neighbourhoods of every point. -/
theorem hasBasis_nhds [IsTopologicalGroup G] (g : G) :
    (𝓝 g).HasBasis (fun r : ℝ => 0 < r) (fun r => {h | 𝒩.d g h < r}) := by
  rw [← map_mul_left_nhds_one g]
  refine (𝒩.hasBasis_nhds_one.map _).to_hasBasis (fun r hr => ⟨r, hr, ?_⟩)
    (fun r hr => ⟨r, hr, ?_⟩)
  · intro h hh; exact ⟨g⁻¹ * h, by simpa [d] using hh, by simp⟩
  · rintro _ ⟨k, hk, rfl⟩; simpa [d] using hk

/-- In a topological group, convergence is convergence of `d y (f x) → 0`. -/
theorem tendsto_nhds_iff [IsTopologicalGroup G] {α : Type*} {l : Filter α} {f : α → G} {y : G} :
    Tendsto f l (𝓝 y) ↔ Tendsto (fun x => 𝒩.d y (f x)) l (𝓝 0) := by
  rw [(𝒩.hasBasis_nhds y).tendsto_right_iff, Metric.tendsto_nhds]
  refine forall₂_congr fun r _ => ?_
  simp [abs_of_nonneg (𝒩.d_nonneg _ _)]

/-- A `d`-Cauchy sequence in a compact set converges. -/
theorem exists_tendsto_of_cauchy [IsTopologicalGroup G] {K : Set G} (hK : IsCompact K)
    {z : ℕ → G} (hzK : ∀ n, z n ∈ K)
    (hz : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, 𝒩.d (z m) (z n) < ε) :
    ∃ y ∈ K, Tendsto z atTop (𝓝 y) := by
  obtain ⟨y, hyK, hy⟩ := hK.exists_clusterPt (f := map z atTop)
    (Filter.le_principal_iff.2 (Filter.mem_map.2 (Eventually.of_forall hzK)))
  refine ⟨y, hyK, (𝒩.hasBasis_nhds y).tendsto_right_iff.2 fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hz (ε / 2) (half_pos hε)
  have hfreq : ∃ᶠ n in atTop, z n ∈ {h | 𝒩.d y h < ε / 2} :=
    mapClusterPt_iff_frequently.1 hy _ ((𝒩.hasBasis_nhds y).mem_of_mem (half_pos hε))
  obtain ⟨m, hmN, hm⟩ := frequently_atTop.1 hfreq N
  filter_upwards [eventually_ge_atTop N] with n hn
  have h1 := hN m hmN n hn
  have h2 : 𝒩.d y (z m) < ε / 2 := hm
  show 𝒩.d y (z n) < ε
  linarith [𝒩.d_triangle y (z m) (z n)]

/-- A uniform `d`-limit of continuous maps is continuous. -/
theorem continuousOn_of_uniform_approx [IsTopologicalGroup G] {α : Type*} [TopologicalSpace α]
    {s : Set α} {F : ℕ → α → G} {f : α → G} (hF : ∀ n, ContinuousOn (F n) s)
    (hunif : ∀ ε > 0, ∃ n, ∀ t ∈ s, 𝒩.d (F n t) (f t) < ε) : ContinuousOn f s := by
  intro t₀ ht₀
  refine (𝒩.hasBasis_nhds (f t₀)).tendsto_right_iff.2 fun ε hε => ?_
  obtain ⟨n, hn⟩ := hunif (ε / 3) (by positivity)
  have hc := (𝒩.hasBasis_nhds (F n t₀)).tendsto_right_iff.1 (hF n t₀ ht₀) (ε / 3) (by positivity)
  filter_upwards [hc, self_mem_nhdsWithin] with t ht hts
  have h1 : 𝒩.d (F n t₀) (F n t) < ε / 3 := ht
  have h2 := hn t hts
  have h3 := hn t₀ ht₀
  show 𝒩.d (f t₀) (f t) < ε
  have t1 := 𝒩.d_triangle (f t₀) (F n t₀) (f t)
  have t2 := 𝒩.d_triangle (F n t₀) (F n t) (f t)
  have t3 := 𝒩.d_comm (f t₀) (F n t₀)
  linarith

/-- Small closed balls are compact. -/
theorem exists_isCompact_le [LocallyCompactSpace G] : ∃ r₀ > 0, IsCompact {g | 𝒩.N g ≤ r₀} := by
  obtain ⟨K, hKc, hK⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨r, hr, hsub⟩ := 𝒩.small_subset K hK
  refine ⟨r / 2, half_pos hr, hKc.of_isClosed_subset (𝒩.isClosed_setOf_le _) ?_⟩
  intro g hg
  exact hsub (show 𝒩.N g < r by have hg' : 𝒩.N g ≤ r / 2 := hg; linarith)

theorem isCompact_setOf_le_of_le {r₀ r : ℝ} (h₀ : IsCompact {g | 𝒩.N g ≤ r₀}) (hr : r ≤ r₀) :
    IsCompact {g | 𝒩.N g ≤ r} :=
  h₀.of_isClosed_subset (𝒩.isClosed_setOf_le r) fun _ hg => le_trans hg hr

/-! ### Escape to scale -/

/-- **Escape-to-scale** (blueprint §3). If `δ ≤ (2 C²)⁻¹`, `1 ≤ n` and `N (x ^ k) ≤ δ` for
`1 ≤ k ≤ n`, then `N x ≤ C δ / n`. -/
theorem N_le_of_pow_le {x : G} {n : ℕ} {δ : ℝ} (hδ : δ ≤ (2 * 𝒩.C ^ 2)⁻¹) (hn : 1 ≤ n)
    (hx : ∀ k : ℕ, 1 ≤ k → k ≤ n → 𝒩.N (x ^ k) ≤ δ) : 𝒩.N x ≤ 𝒩.C * δ / n := by
  have hC := 𝒩.two_le_C
  have hCpos : 0 < 𝒩.C := by linarith
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have ha : 𝒩.N x ≤ δ := by simpa using hx 1 le_rfl hn
  have ha0 := 𝒩.nonneg x
  have hδ0 : 0 ≤ δ := ha0.trans ha
  rcases ha0.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  set a := 𝒩.N x with ha_def
  set C := 𝒩.C with hC_def
  have hCa0 : 0 < C * a := mul_pos hCpos hpos
  have h2C : 2 * C * δ ≤ C⁻¹ := by
    calc 2 * C * δ ≤ 2 * C * (2 * C ^ 2)⁻¹ := by gcongr
      _ = C⁻¹ := by field_simp
  have hCa : C * a ≤ 1 / 2 := by
    have : C * a ≤ C * δ := by gcongr
    have h1 : C * δ ≤ C⁻¹ / 2 := by linarith
    have h2 : C⁻¹ / 2 ≤ 1 / 4 := by linarith [𝒩.C_inv_le_half]
    linarith
  set q := ⌊(C * a)⁻¹⌋₊ with hq_def
  have hq1 : 1 ≤ q := by
    rw [Nat.one_le_floor_iff]
    rw [le_inv_comm₀ one_pos hCa0]; linarith
  have hqa : (q : ℝ) * a ≤ C⁻¹ := by
    have := Nat.floor_le (inv_nonneg.2 hCa0.le)
    calc (q : ℝ) * a ≤ (C * a)⁻¹ * a := by gcongr
      _ = C⁻¹ := by field_simp
  rcases le_or_gt n q with hnq | hqn
  · have h1 : (n : ℝ) * a ≤ C⁻¹ :=
      le_trans (by gcongr) hqa
    have h2 := 𝒩.escape x n h1
    have h3 := hx n hn le_rfl
    rw [le_div_iff₀ hn']
    nlinarith
  · exfalso
    have h2 := 𝒩.escape x q hqa
    have h3 := hx q hq1 hqn.le
    have h4 : (C * a)⁻¹ < q + 1 := Nat.lt_floor_add_one _
    have h5 : C⁻¹ < (q + 1) * a := by
      calc C⁻¹ = (C * a)⁻¹ * a := by field_simp
        _ < (q + 1) * a := by gcongr
    have h6 : (q : ℝ) * a ≤ C * δ := h2.trans (by gcongr)
    have h7 : δ ≤ C * δ := le_mul_of_one_le_left hδ0 (by linarith)
    nlinarith

/-- Escape-to-scale, applied to the intermediate powers. -/
theorem N_pow_le_of_pow_le {x : G} {n j : ℕ} {δ : ℝ} (hδ : δ ≤ (2 * 𝒩.C ^ 2)⁻¹) (hn : 1 ≤ n)
    (hx : ∀ k : ℕ, 1 ≤ k → k ≤ n → 𝒩.N (x ^ k) ≤ δ) : 𝒩.N (x ^ j) ≤ j * (𝒩.C * δ / n) :=
  (𝒩.N_pow_le x j).trans (by gcongr; exact 𝒩.N_le_of_pow_le hδ hn hx)

/-- If all powers of `x` stay in `{N ≤ δ}` with `δ ≤ (2 C²)⁻¹`, then `x = 1`. -/
theorem eq_one_of_forall_pow_le {x : G} {δ : ℝ} (hδ : δ ≤ (2 * 𝒩.C ^ 2)⁻¹)
    (hx : ∀ k : ℕ, 𝒩.N (x ^ k) ≤ δ) : x = 1 := by
  by_contra hne
  have hpos := 𝒩.N_pos hne
  obtain ⟨n, hn⟩ := exists_nat_gt (𝒩.C * δ / 𝒩.N x)
  have hn1 : 1 ≤ n := by
    have : 0 ≤ 𝒩.C * δ / 𝒩.N x :=
      div_nonneg (mul_nonneg 𝒩.C_pos.le ((𝒩.nonneg x).trans (by simpa using hx 1))) hpos.le
    exact_mod_cast (show (1 : ℝ) ≤ n by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp only [Nat.cast_zero] at hn; linarith
      · exact_mod_cast h)
  have h := 𝒩.N_le_of_pow_le hδ hn1 (fun k _ _ => hx k)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [div_lt_iff₀ hpos] at hn
  rw [le_div_iff₀ hn'] at h
  linarith

/-- Consistency check of the escape field: a weak Gleason norm rules out small subgroups. -/
theorem noSmallSubgroups {G : Type} [Group G] [TopologicalSpace G] (𝒩 : WeakGleasonNorm G) :
    NoSmallSubgroups G := by
  have hδ : (0 : ℝ) < (2 * 𝒩.C ^ 2)⁻¹ := by have := 𝒩.C_pos; positivity
  refine ⟨{g | 𝒩.N g < (2 * 𝒩.C ^ 2)⁻¹}, 𝒩.setOf_lt_mem_nhds hδ, fun S hS => ?_⟩
  rw [eq_bot_iff]
  intro x hx
  exact 𝒩.eq_one_of_forall_pow_le le_rfl fun k => (hS (S.pow_mem hx k)).le

/-! ### Producer helpers -/

/-- Raise the constant `C` (the escape property survives). -/
def ofLE (C' : ℝ) (hC' : 𝒩.C ≤ C') : WeakGleasonNorm G where
  N := 𝒩.N
  C := C'
  two_le_C := 𝒩.two_le_C.trans hC'
  map_one := 𝒩.map_one
  map_inv := 𝒩.map_inv
  mul_le := 𝒩.mul_le
  eq_one := 𝒩.eq_one
  continuous := 𝒩.continuous
  small_subset := 𝒩.small_subset
  escape g n h := by
    have h' : (n : ℝ) * 𝒩.N g ≤ 𝒩.C⁻¹ := h.trans (inv_anti₀ 𝒩.C_pos hC')
    exact (𝒩.escape g n h').trans (by gcongr; exact 𝒩.nonneg _)

@[simp] theorem ofLE_N (C' : ℝ) (hC' : 𝒩.C ≤ C') : (𝒩.ofLE C' hC').N = 𝒩.N := rfl

@[simp] theorem ofLE_C (C' : ℝ) (hC' : 𝒩.C ≤ C') : (𝒩.ofLE C' hC').C = C' := rfl

/-- A commutator estimate with an arbitrary constant `K` and threshold `c > 0` upgrades a weak
Gleason norm to a Gleason norm with the same `N` (and `C = max 𝒩.C (max K c⁻¹)`). -/
def toGleasonNorm {K c : ℝ} (hc : 0 < c)
    (hcomm : ∀ g h, 𝒩.N g ≤ c → 𝒩.N h ≤ c → 𝒩.N (g⁻¹ * h⁻¹ * g * h) ≤ K * 𝒩.N g * 𝒩.N h) :
    GleasonNorm G where
  toWeakGleasonNorm := 𝒩.ofLE (max 𝒩.C (max K c⁻¹)) (le_max_left _ _)
  commutator g h hg hh := by
    simp only [ofLE_N, ofLE_C] at hg hh ⊢
    have hCpos : 0 < max 𝒩.C (max K c⁻¹) := lt_of_lt_of_le 𝒩.C_pos (le_max_left _ _)
    have hcC : (max 𝒩.C (max K c⁻¹))⁻¹ ≤ c := by
      rw [inv_le_comm₀ hCpos hc]; exact (le_max_right _ _).trans' (le_max_right _ _)
    refine (hcomm g h (hg.trans hcC) (hh.trans hcC)).trans ?_
    have hK : K ≤ max 𝒩.C (max K c⁻¹) := (le_max_left _ _).trans (le_max_right _ _)
    have := mul_nonneg (𝒩.nonneg g) (𝒩.nonneg h)
    rw [mul_assoc, mul_assoc]; gcongr

@[simp] theorem toGleasonNorm_N {K c : ℝ} (hc : 0 < c)
    (hcomm : ∀ g h, 𝒩.N g ≤ c → 𝒩.N h ≤ c → 𝒩.N (g⁻¹ * h⁻¹ * g * h) ≤ K * 𝒩.N g * 𝒩.N h) :
    (𝒩.toGleasonNorm hc hcomm).N = 𝒩.N := rfl

/-- Producer helper for the `continuous` field: in a topological group, a symmetric subadditive
function whose sublevel sets `{N < r}` (`r > 0`) are neighbourhoods of `1` is continuous. -/
theorem continuous_of_mul_le [IsTopologicalGroup G] {N : G → ℝ} (map_inv : ∀ g, N g⁻¹ = N g)
    (mul_le : ∀ g h, N (g * h) ≤ N g + N h) (hN : ∀ r > 0, {g | N g < r} ∈ 𝓝 (1 : G)) :
    Continuous N := by
  refine continuous_iff_continuousAt.2 fun g => Metric.tendsto_nhds.2 fun ε hε => ?_
  have hlim : Tendsto (fun h => g⁻¹ * h) (𝓝 g) (𝓝 1) := by
    exact Continuous.tendsto' (by fun_prop) g 1 (inv_mul_cancel g)
  filter_upwards [hlim (hN ε hε)] with h hh
  have h1 := mul_le g (g⁻¹ * h)
  have h2 := mul_le h (h⁻¹ * g)
  rw [mul_inv_cancel_left] at h1 h2
  have h3 : N (h⁻¹ * g) = N (g⁻¹ * h) := by rw [← map_inv]; group
  have hh' : N (g⁻¹ * h) < ε := hh
  rw [Real.dist_eq, abs_lt]; constructor <;> linarith

end WeakGleasonNorm

/-! ## One-parameter subgroups -/

/-- A continuous one-parameter subgroup `ℝ → G` (an element of Tao's `L(G)`). It is a separate
structure so that no algebra instance leaks; `B3a` builds `LieAlg 𝒢 := OneParam G`. -/
structure OneParam (G : Type*) [Group G] [TopologicalSpace G] where
  toFun : ℝ → G
  map_add' : ∀ s t, toFun (s + t) = toFun s * toFun t
  continuous' : Continuous toFun

namespace OneParam

variable {G : Type*} [Group G] [TopologicalSpace G]

instance : FunLike (OneParam G) ℝ G where
  coe := OneParam.toFun
  coe_injective X Y h := by cases X; cases Y; congr

@[simp] theorem toFun_eq_coe (X : OneParam G) : X.toFun = ⇑X := rfl

@[simp] theorem coe_mk (f : ℝ → G) (h₁ h₂) : ⇑(⟨f, h₁, h₂⟩ : OneParam G) = f := rfl

@[ext] theorem ext {X Y : OneParam G} (h : ∀ t, X t = Y t) : X = Y := DFunLike.ext _ _ h

variable (X : OneParam G)

theorem map_add (s t : ℝ) : X (s + t) = X s * X t := X.map_add' s t

@[continuity, fun_prop] theorem continuous : Continuous X := X.continuous'

@[simp] theorem map_zero : X 0 = 1 := by
  have h := X.map_add 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

@[simp] theorem map_neg (t : ℝ) : X (-t) = (X t)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← X.map_add, neg_add_cancel, map_zero]

theorem map_sub (s t : ℝ) : X (s - t) = X s * (X t)⁻¹ := by
  rw [sub_eq_add_neg, map_add, map_neg]

theorem map_natCast_mul (n : ℕ) (t : ℝ) : X (n * t) = X t ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, map_add, ih, pow_succ]

theorem map_intCast_mul (n : ℤ) (t : ℝ) : X (n * t) = X t ^ n := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · simpa using X.map_natCast_mul m t
  · rw [Int.cast_neg, neg_mul, map_neg, Int.cast_natCast, map_natCast_mul, zpow_neg, zpow_natCast]

theorem commute (s t : ℝ) : Commute (X s) (X t) := by
  rw [Commute, SemiconjBy, ← map_add, ← map_add, add_comm]

/-- **Extensionality** (blueprint §3): one-parameter subgroups agreeing on `[-T, T]`, `T > 0`, are
equal, since `X t = X (t / k) ^ k`. -/
theorem ext_of_eqOn {X Y : OneParam G} {T : ℝ} (hT : 0 < T) (h : Set.EqOn X Y (Set.Icc (-T) T)) :
    X = Y := by
  ext t
  obtain ⟨k, hk⟩ := exists_nat_gt (|t| / T)
  have hk0 : (0 : ℝ) < k := lt_of_le_of_lt (div_nonneg (abs_nonneg t) hT.le) hk
  have hmem : t / k ∈ Set.Icc (-T) T := by
    rw [Set.mem_Icc, ← abs_le, abs_div, Nat.abs_cast, div_le_iff₀ hk0]
    rw [div_lt_iff₀ hT] at hk; linarith
  have ht : t = (k : ℝ) * (t / k) := by field_simp
  rw [ht, map_natCast_mul, map_natCast_mul, h hmem]

end OneParam

/-! ## Local exponential structures -/

/-- Output of track B and input of track C: a continuous "exponential" `exp : E → G` that is a
one-parameter subgroup on every ray, an open partial homeomorphism `chart` with `⇑chart = exp`
around `0`, the `C^{1,1}` estimate `c11` for `log (exp X * exp Y)` (`log = chart.symm`), and
conjugation by every `g` acting linearly. (Trotter's formula is the theorem
`LocalExpStructure.trotter`.) -/
structure LocalExpStructure (G : Type*) [Group G] [TopologicalSpace G]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  exp : E → G
  continuous_exp : Continuous exp
  exp_add_smul : ∀ (X : E) (s t : ℝ), exp ((s + t) • X) = exp (s • X) * exp (t • X)
  chart : OpenPartialHomeomorph E G
  chart_coe : ⇑chart = exp
  zero_mem_source : (0 : E) ∈ chart.source
  c11 : ∃ δ > 0, ∃ K : ℝ, ∀ X Y : E, ‖X‖ < δ → ‖Y‖ < δ →
    exp X * exp Y ∈ chart.target ∧ ‖chart.symm (exp X * exp Y) - (X + Y)‖ ≤ K * ‖X‖ * ‖Y‖
  conj : ∀ g : G, ∃ A : E →L[ℝ] E, ∀ X : E, g * exp X * g⁻¹ = exp (A X)

namespace LocalExpStructure

variable {G : Type*} [Group G] [TopologicalSpace G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (S : LocalExpStructure G E)

@[simp] theorem exp_zero : S.exp 0 = 1 := by
  have h := S.exp_add_smul 0 0 0
  simp only [add_zero, smul_zero] at h
  exact mul_eq_left.1 h.symm

theorem exp_smul_add (X : E) (s t : ℝ) : S.exp ((s + t) • X) = S.exp (s • X) * S.exp (t • X) :=
  S.exp_add_smul X s t

@[simp] theorem exp_neg (X : E) : S.exp (-X) = (S.exp X)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  have h := S.exp_add_smul X (-1) 1
  simp only [neg_add_cancel, zero_smul, neg_smul, one_smul, exp_zero] at h
  exact h.symm

theorem exp_natCast_smul (n : ℕ) (X : E) : S.exp ((n : ℝ) • X) = S.exp X ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, S.exp_add_smul, ih, one_smul, pow_succ]

theorem exp_nsmul (n : ℕ) (X : E) : S.exp (n • X) = S.exp X ^ n := by
  rw [← Nat.cast_smul_eq_nsmul ℝ, exp_natCast_smul]

theorem exp_intCast_smul (n : ℤ) (X : E) : S.exp ((n : ℝ) • X) = S.exp X ^ n := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · simpa using S.exp_natCast_smul m X
  · rw [Int.cast_neg, neg_smul, exp_neg, Int.cast_natCast, exp_natCast_smul, zpow_neg,
      zpow_natCast]

theorem commute_exp_smul (X : E) (s t : ℝ) : Commute (S.exp (s • X)) (S.exp (t • X)) := by
  rw [Commute, SemiconjBy, ← S.exp_add_smul, ← S.exp_add_smul, add_comm]

/-- The ray `t ↦ exp (t • X)` as a one-parameter subgroup. -/
def toOneParam (X : E) : OneParam G where
  toFun t := S.exp (t • X)
  map_add' s t := S.exp_add_smul X s t
  continuous' := S.continuous_exp.comp (continuous_id.smul continuous_const)

@[simp] theorem toOneParam_apply (X : E) (t : ℝ) : S.toOneParam X t = S.exp (t • X) := rfl

theorem exp_mem_target {X : E} (hX : X ∈ S.chart.source) : S.exp X ∈ S.chart.target := by
  rw [← S.chart_coe]; exact S.chart.map_source hX

theorem symm_exp {X : E} (hX : X ∈ S.chart.source) : S.chart.symm (S.exp X) = X := by
  rw [← S.chart_coe]; exact S.chart.left_inv hX

theorem exp_symm {y : G} (hy : y ∈ S.chart.target) : S.exp (S.chart.symm y) = y := by
  rw [← S.chart_coe]; exact S.chart.right_inv hy

theorem symm_mem_source {y : G} (hy : y ∈ S.chart.target) : S.chart.symm y ∈ S.chart.source :=
  S.chart.map_target hy

theorem one_mem_target : (1 : G) ∈ S.chart.target := by
  simpa using S.exp_mem_target S.zero_mem_source

@[simp] theorem symm_one : S.chart.symm 1 = 0 := by
  simpa using S.symm_exp S.zero_mem_source

theorem injOn_exp : Set.InjOn S.exp S.chart.source := by
  rw [← S.chart_coe]; exact S.chart.injOn

theorem source_mem_nhds : S.chart.source ∈ 𝓝 (0 : E) :=
  S.chart.open_source.mem_nhds S.zero_mem_source

theorem target_mem_nhds : S.chart.target ∈ 𝓝 (1 : G) :=
  S.chart.open_target.mem_nhds S.one_mem_target

/-- Two continuous linear maps `A`, `B` with `exp ∘ A = exp ∘ B` are equal, since `exp` is
injective near `0`. So the map `A` in `conj g` is unique (this is what makes C1's `Ad` well
defined and multiplicative). -/
theorem clm_ext {A B : E →L[ℝ] E} (h : ∀ X, S.exp (A X) = S.exp (B X)) : A = B := by
  have hA : Tendsto A (𝓝 0) (𝓝 0) := by simpa using A.continuous.tendsto 0
  have hB : Tendsto B (𝓝 0) (𝓝 0) := by simpa using B.continuous.tendsto 0
  have hU : {X : E | A X ∈ S.chart.source ∧ B X ∈ S.chart.source} ∈ 𝓝 (0 : E) :=
    Filter.inter_mem (hA S.source_mem_nhds) (hB S.source_mem_nhds)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  ext X
  set c : ℝ := ε / (2 * (‖X‖ + 1)) with hc_def
  have hc : 0 < c := by positivity
  have hcX : c • X ∈ Metric.ball (0 : E) ε := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg hc.le]
    calc c * ‖X‖ < c * (‖X‖ + 1) := by gcongr; linarith
      _ = ε / 2 := by rw [hc_def]; field_simp
      _ < ε := half_lt_self hε
  obtain ⟨h1, h2⟩ := hball hcX
  have := S.injOn_exp h1 h2 (h _)
  rw [map_smul, map_smul] at this
  exact smul_right_injective E hc.ne' this

/-- **Ray lifting.** If the whole ray `exp (s • W)`, `s ∈ [0, 1]`, stays in the chart target, then
`chart.symm (exp W) = W` (and so `W ∈ chart.source`). This is the uniqueness of lifts of paths
through the local homeomorphism `exp`; e.g. it identifies `Ad g X` with `log (g * exp X * g⁻¹)`. -/
theorem symm_exp_of_forall_mem_target {W : E}
    (h : ∀ s ∈ Set.Icc (0 : ℝ) 1, S.exp (s • W) ∈ S.chart.target) :
    S.chart.symm (S.exp W) = W := by
  set T : Set ℝ := {s | S.chart.symm (S.exp (s • W)) = s • W} with hT
  have hray : Continuous fun s : ℝ => s • W := continuous_id.smul continuous_const
  have hsub : Set.Icc (0 : ℝ) 1 ⊆ T := by
    refine IsClosed.Icc_subset_of_forall_mem_nhdsWithin ?_ ?_ ?_
    · have hc : ContinuousOn (fun s : ℝ => (S.chart.symm (S.exp (s • W)), s • W))
          (Set.Icc 0 1) :=
        (S.chart.continuousOn_symm.comp (S.continuous_exp.comp hray).continuousOn
          fun s hs => h s hs).prodMk hray.continuousOn
      have := hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_diagonal
      convert this using 1
      ext s
      simp only [hT, Set.mem_inter_iff, Set.mem_preimage, Set.mem_diagonal_iff, Set.mem_ofPred_eq]
      exact and_comm
    · simp [hT]
    · rintro x ⟨hxT, hx⟩
      have hxs : x • W ∈ S.chart.source := by
        have hx' : S.chart.symm (S.exp (x • W)) = x • W := hxT
        rw [← hx']; exact S.symm_mem_source (h x (Set.Ico_subset_Icc_self hx))
      have hev : ∀ᶠ s in 𝓝 x, s • W ∈ S.chart.source :=
        hray.continuousAt.preimage_mem_nhds (S.chart.open_source.mem_nhds hxs)
      exact nhdsWithin_le_nhds (hev.mono fun s hs => S.symm_exp hs)
  have h1 : S.chart.symm (S.exp ((1 : ℝ) • W)) = (1 : ℝ) • W := hsub ⟨zero_le_one, le_rfl⟩
  simpa using h1

theorem mem_source_of_forall_mem_target {W : E}
    (h : ∀ s ∈ Set.Icc (0 : ℝ) 1, S.exp (s • W) ∈ S.chart.target) : W ∈ S.chart.source := by
  rw [← S.symm_exp_of_forall_mem_target h]
  exact S.symm_mem_source (by simpa using h 1 ⟨zero_le_one, le_rfl⟩)

/-- Multiplication in exponential coordinates: `μ X Y = log (exp X * exp Y)`, `log = chart.symm`.
It is meaningful when `exp X * exp Y ∈ S.chart.target` (e.g. for small `X`, `Y`, by `c11`). -/
def mu (X Y : E) : E := S.chart.symm (S.exp X * S.exp Y)

theorem mu_def (X Y : E) : S.mu X Y = S.chart.symm (S.exp X * S.exp Y) := rfl

theorem exp_mu {X Y : E} (h : S.exp X * S.exp Y ∈ S.chart.target) :
    S.exp (S.mu X Y) = S.exp X * S.exp Y :=
  S.exp_symm h

/-- Conclusion of C3 (`LocalExpStructure.contDiffOn_mu`) and hypothesis `hμ` of C4
(`LocalExpStructure.isLieGroup`): `μ` is `C^∞` on a product of balls around `0`, on which
`exp X * exp Y` stays in the chart target. -/
def ContDiffMu : Prop :=
  ∃ ρ > 0, ContDiffOn ℝ ∞ (fun p : E × E => S.mu p.1 p.2) (Metric.ball 0 ρ ×ˢ Metric.ball 0 ρ) ∧
    ∀ X Y : E, ‖X‖ < ρ → ‖Y‖ < ρ → S.exp X * S.exp Y ∈ S.chart.target

/-- **Trotter product formula**, for all `X Y : E`; a consequence of `c11` (blueprint: a field). -/
theorem trotter (X Y : E) :
    Tendsto (fun n : ℕ => (S.exp ((n : ℝ)⁻¹ • X) * S.exp ((n : ℝ)⁻¹ • Y)) ^ n) atTop
      (𝓝 (S.exp (X + Y))) := by
  obtain ⟨δ, hδ, K, hK⟩ := S.c11
  have h0 : ∀ Z : E, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • Z) atTop (𝓝 0) := fun Z => by
    simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const Z
  have hsmall : ∀ᶠ n : ℕ in atTop, ‖(n : ℝ)⁻¹ • X‖ < δ ∧ ‖(n : ℝ)⁻¹ • Y‖ < δ :=
    ((h0 X).norm.eventually (gt_mem_nhds (by simpa using hδ))).and
      ((h0 Y).norm.eventually (gt_mem_nhds (by simpa using hδ)))
  set Z : ℕ → E := fun n => S.mu ((n : ℝ)⁻¹ • X) ((n : ℝ)⁻¹ • Y) with hZ
  have heq : ∀ᶠ n : ℕ in atTop,
      S.exp ((n : ℝ) • Z n) = (S.exp ((n : ℝ)⁻¹ • X) * S.exp ((n : ℝ)⁻¹ • Y)) ^ n := by
    filter_upwards [hsmall] with n hn
    rw [exp_natCast_smul, hZ, S.exp_mu (hK _ _ hn.1 hn.2).1]
  have hbound : ∀ᶠ n : ℕ in atTop, ‖(n : ℝ) • Z n - (X + Y)‖ ≤ K * ‖X‖ * ‖Y‖ * (n : ℝ)⁻¹ := by
    filter_upwards [hsmall, eventually_ge_atTop 1] with n hn hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have h1 := (hK _ _ hn.1 hn.2).2
    have h2 : (n : ℝ) • Z n - (X + Y) =
        (n : ℝ) • (Z n - ((n : ℝ)⁻¹ • X + (n : ℝ)⁻¹ • Y)) := by
      rw [smul_sub, smul_add, smul_inv_smul₀ hn0.ne', smul_inv_smul₀ hn0.ne']
    rw [h2, norm_smul, Real.norm_of_nonneg hn0.le]
    calc (n : ℝ) * ‖Z n - ((n : ℝ)⁻¹ • X + (n : ℝ)⁻¹ • Y)‖
        ≤ n * (K * ‖(n : ℝ)⁻¹ • X‖ * ‖(n : ℝ)⁻¹ • Y‖) := by gcongr; exact h1
      _ = K * ‖X‖ * ‖Y‖ * (n : ℝ)⁻¹ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hn0.le)]
        field_simp
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) • Z n) atTop (𝓝 (X + Y)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) hbound ?_
    simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (K * ‖X‖ * ‖Y‖)
  exact ((S.continuous_exp.tendsto _).comp hlim).congr' heq

/-- Producer helper for the `chart` field (B5): a continuous `exp` that is injective on an open set
`U` and maps open subsets of `U` to open sets is an open partial homeomorphism with source `U`,
target `exp '' U` and coercion `exp` (so `chart_coe` holds by `rfl`). -/
def chartOfInjOn (exp : E → G) (hexp : Continuous exp) {U : Set E} (hU : IsOpen U)
    (hinj : Set.InjOn exp U) (hopen : ∀ V ⊆ U, IsOpen V → IsOpen (exp '' V)) :
    OpenPartialHomeomorph E G :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict (hinj.toPartialEquiv exp U) hexp.continuousOn
    (by
      show IsOpenMap (U.domRestrict exp)
      intro W hW
      obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.1 hW
      have : U.domRestrict exp '' (Subtype.val ⁻¹' V) = exp '' (V ∩ U) := by
        ext y
        simp only [Set.mem_image, Set.mem_preimage, Subtype.exists, Set.domRestrict,
          Set.mem_inter_iff]
        constructor
        · rintro ⟨x, hxU, hxV, rfl⟩; exact ⟨x, ⟨hxV, hxU⟩, rfl⟩
        · rintro ⟨x, ⟨hxV, hxU⟩, rfl⟩; exact ⟨x, hxU, hxV, rfl⟩
      rw [this]
      exact hopen _ Set.inter_subset_right (hV.inter hU))
    hU

omit [Group G] [NormedSpace ℝ E] in
@[simp] theorem coe_chartOfInjOn (exp : E → G) (hexp : Continuous exp) {U : Set E} (hU : IsOpen U)
    (hinj : Set.InjOn exp U) (hopen : ∀ V ⊆ U, IsOpen V → IsOpen (exp '' V)) :
    ⇑(chartOfInjOn exp hexp hU hinj hopen) = exp := rfl

omit [Group G] [NormedSpace ℝ E] in
@[simp] theorem chartOfInjOn_source (exp : E → G) (hexp : Continuous exp) {U : Set E}
    (hU : IsOpen U) (hinj : Set.InjOn exp U) (hopen : ∀ V ⊆ U, IsOpen V → IsOpen (exp '' V)) :
    (chartOfInjOn exp hexp hU hinj hopen).source = U := rfl

omit [Group G] [NormedSpace ℝ E] in
@[simp] theorem chartOfInjOn_target (exp : E → G) (hexp : Continuous exp) {U : Set E}
    (hU : IsOpen U) (hinj : Set.InjOn exp U) (hopen : ∀ V ⊆ U, IsOpen V → IsOpen (exp '' V)) :
    (chartOfInjOn exp hexp hU hinj hopen).target = exp '' U := rfl

/-- Transport along a continuous linear equivalence `e : E ≃L[ℝ] E'` (B5 uses it to pass from
`LieAlg 𝒢` to `EuclideanSpace ℝ (Fin d)`). -/
def transport {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] (e : E ≃L[ℝ] E') :
    LocalExpStructure G E' where
  exp X := S.exp (e.symm X)
  continuous_exp := S.continuous_exp.comp e.symm.continuous
  exp_add_smul X s t := by simp only [map_smul]; exact S.exp_add_smul _ s t
  chart := e.symm.toHomeomorph.transOpenPartialHomeomorph S.chart
  chart_coe := by ext X; simp [S.chart_coe]
  zero_mem_source := by simpa using S.zero_mem_source
  c11 := by
    obtain ⟨δ, hδ, K, hK⟩ := S.c11
    set a := ‖(e.symm : E' →L[ℝ] E)‖ + 1 with ha
    have ha0 : 0 < a := by positivity
    have hsmall : ∀ X : E', ‖X‖ < δ / a → ‖e.symm X‖ ≤ a * ‖X‖ ∧ ‖e.symm X‖ < δ := fun X hX => by
      have h1 : ‖e.symm X‖ ≤ a * ‖X‖ :=
        ((e.symm : E' →L[ℝ] E).le_opNorm X).trans (by gcongr; linarith)
      refine ⟨h1, h1.trans_lt ?_⟩
      rwa [lt_div_iff₀ ha0, mul_comm] at hX
    refine ⟨δ / a, by positivity, ‖(e : E →L[ℝ] E')‖ * |K| * a ^ 2, fun X Y hX hY => ?_⟩
    obtain ⟨hX1, hX2⟩ := hsmall X hX
    obtain ⟨hY1, hY2⟩ := hsmall Y hY
    obtain ⟨h1, h2⟩ := hK _ _ hX2 hY2
    refine ⟨by simpa using h1, ?_⟩
    have heq : e (S.chart.symm (S.exp (e.symm X) * S.exp (e.symm Y))) - (X + Y) =
        e (S.chart.symm (S.exp (e.symm X) * S.exp (e.symm Y)) - (e.symm X + e.symm Y)) := by
      simp
    change ‖e (S.chart.symm (S.exp (e.symm X) * S.exp (e.symm Y))) - (X + Y)‖ ≤ _
    rw [heq]
    calc ‖e (S.chart.symm (S.exp (e.symm X) * S.exp (e.symm Y)) - (e.symm X + e.symm Y))‖
        ≤ ‖(e : E →L[ℝ] E')‖ *
            ‖S.chart.symm (S.exp (e.symm X) * S.exp (e.symm Y)) - (e.symm X + e.symm Y)‖ :=
          (e : E →L[ℝ] E').le_opNorm _
      _ ≤ ‖(e : E →L[ℝ] E')‖ * (|K| * (a * ‖X‖) * (a * ‖Y‖)) := by
          gcongr
          refine h2.trans ?_
          gcongr
          · exact le_abs_self K
      _ = ‖(e : E →L[ℝ] E')‖ * |K| * a ^ 2 * ‖X‖ * ‖Y‖ := by ring
  conj g := by
    obtain ⟨A, hA⟩ := S.conj g
    exact ⟨(e : E →L[ℝ] E').comp (A.comp (e.symm : E' →L[ℝ] E)), fun X => by simp [hA]⟩

@[simp] theorem transport_exp {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (e : E ≃L[ℝ] E') (X : E') : (S.transport e).exp X = S.exp (e.symm X) := rfl

end LocalExpStructure

/-! ## Sanity checks: the interfaces are inhabited -/

namespace Sanity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The norm of a real normed space is a weak Gleason norm on its additive group. -/
def normWeakGleason : WeakGleasonNorm (Multiplicative E) where
  N g := ‖Multiplicative.toAdd g‖
  C := 2
  two_le_C := le_rfl
  map_one := by simp
  map_inv g := by simp
  mul_le g h := by simpa using norm_add_le (Multiplicative.toAdd g) (Multiplicative.toAdd h)
  eq_one g h := by simpa using h
  continuous := continuous_norm.comp continuous_toAdd
  small_subset U hU := by
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (show U ∈ 𝓝 (0 : E) from hU)
    exact ⟨ε, hε, fun g (hg : ‖Multiplicative.toAdd g‖ < ε) =>
      hball (show dist (Multiplicative.toAdd g) 0 < ε by simpa using hg)⟩
  escape g n _ := by
    simp only [toAdd_pow, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul, Real.norm_natCast]
    nlinarith [norm_nonneg (Multiplicative.toAdd g), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- ... and a Gleason norm (the group is abelian, so commutators vanish). -/
def normGleason : GleasonNorm (Multiplicative E) :=
  normWeakGleason.toGleasonNorm (K := 0) one_pos fun g h _ _ => by
    simp [normWeakGleason, mul_comm g⁻¹, mul_assoc]

/-- The line through `v` is a one-parameter subgroup. -/
def lineOneParam (v : E) : OneParam (Multiplicative E) where
  toFun t := Multiplicative.ofAdd (t • v)
  map_add' s t := by simp [add_smul]
  continuous' := continuous_ofAdd.comp (continuous_id.smul continuous_const)

/-- `ofAdd : E → Multiplicative E` as a homeomorphism. -/
def ofAddHomeomorph : E ≃ₜ Multiplicative E where
  toEquiv := Multiplicative.ofAdd
  continuous_toFun := continuous_ofAdd
  continuous_invFun := continuous_toAdd

/-- The identity chart of a real normed space is a local exponential structure. -/
def normLocalExp : LocalExpStructure (Multiplicative E) E where
  exp := Multiplicative.ofAdd
  continuous_exp := continuous_ofAdd
  exp_add_smul X s t := by simp [add_smul]
  chart := ofAddHomeomorph.toOpenPartialHomeomorph
  chart_coe := rfl
  zero_mem_source := by simp
  c11 := ⟨1, one_pos, 0, fun X Y _ _ => ⟨by simp, by simp [ofAddHomeomorph]⟩⟩
  conj g := ⟨ContinuousLinearMap.id ℝ E, fun X => by simp [mul_comm g]⟩

/-- The same exponential with a *local* chart (source `ball 0 1`) built by
`LocalExpStructure.chartOfInjOn`; checks that `c11` is workable when `chart.symm` is only a local
inverse. -/
example : LocalExpStructure (Multiplicative E) E where
  exp := Multiplicative.ofAdd
  continuous_exp := continuous_ofAdd
  exp_add_smul X s t := by simp [add_smul]
  chart := LocalExpStructure.chartOfInjOn Multiplicative.ofAdd continuous_ofAdd Metric.isOpen_ball
    Multiplicative.ofAdd.injective.injOn fun V _ hV => (ofAddHomeomorph (E := E)).isOpenMap V hV
  chart_coe := rfl
  zero_mem_source := Metric.mem_ball_self one_pos
  c11 := by
    refine ⟨1 / 2, by norm_num, 0, fun X Y hX hY => ?_⟩
    set e := LocalExpStructure.chartOfInjOn (E := E) Multiplicative.ofAdd continuous_ofAdd
      Metric.isOpen_ball Multiplicative.ofAdd.injective.injOn
      fun V _ hV => (ofAddHomeomorph (E := E)).isOpenMap V hV
    have hXY : X + Y ∈ e.source := by
      show X + Y ∈ Metric.ball (0 : E) 1
      rw [Metric.mem_ball, dist_zero_right]
      linarith [norm_add_le X Y]
    have heq : Multiplicative.ofAdd X * Multiplicative.ofAdd Y = e (X + Y) := rfl
    refine ⟨by rw [heq]; exact e.map_source hXY, ?_⟩
    rw [heq, e.left_inv hXY]
    simp
  conj g := ⟨ContinuousLinearMap.id ℝ E, fun X => by simp [mul_comm g]⟩

example : (normLocalExp (E := E)).ContDiffMu := by
  refine ⟨1, one_pos, ?_, fun _ _ _ _ => by simp [normLocalExp]⟩
  have : (fun p : E × E => (normLocalExp (E := E)).mu p.1 p.2) = fun p => p.1 + p.2 := by
    ext p; simp [LocalExpStructure.mu, normLocalExp, ofAddHomeomorph]
  rw [this]
  exact (contDiff_fst.add contDiff_snd).contDiffOn

example (X Y : E) :
    Tendsto (fun n : ℕ => (Multiplicative.ofAdd ((n : ℝ)⁻¹ • X) *
      Multiplicative.ofAdd ((n : ℝ)⁻¹ • Y)) ^ n) atTop (𝓝 (Multiplicative.ofAdd (X + Y))) :=
  (normLocalExp (E := E)).trotter X Y

example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] : NoSmallSubgroups (Multiplicative E) :=
  (normWeakGleason (E := E)).noSmallSubgroups

end Sanity

end HSFormal.GY

end
