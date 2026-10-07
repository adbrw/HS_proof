import HSFormal.Inputs.GY.Defs

/-!
# Escape norms (Gleason–Yamabe, module A1)

Tao 254A Notes 4, §3 (eq. (11), Exercise 21, eq. (12)).

* `escNorm U g` is Tao's escape norm `‖g‖_{e,U} = inf {1/(n+1) | g, g², …, gⁿ ∈ U}`. We define
  it through the *exit time*: if some power `g ^ m`, `m ≥ 1`, leaves `U` and `m` is the least such
  exponent, then `escNorm U g = 1 / m`; if all positive powers stay in `U`, `escNorm U g = 0`.
  This is the same number as Tao's infimum (`escNorm_eq_sInf` is the blueprint's definition,
  `escNorm_le_inv_iff` its characterisation), but the workhorse is the real-parameter
  characterisation
  `escNorm_le_iff : escNorm U g ≤ c ↔ ∀ i ≥ 1, i * c < 1 → g ^ i ∈ U` (for `c ≥ 0`).
* `NSSBase G`: an open symmetric neighbourhood `Ub` of `1` with compact closure, such that no
  `g ≠ 1` has all its powers in `closure Ub`. `exists_nssBase` produces one from
  `NoSmallSubgroups G` in a locally compact Hausdorff group.
* `NSSBase.exists_pow_mem` (Tao, Exercise 21): for `U ⊆ Ub` and any neighbourhood `V` of `1`
  there is `m` with `g, …, g^m ∈ U → g ∈ V` (ultrafilter-compactness argument).
* `NSSBase.escNorm_le` (Tao (12)): `escNorm U' ≤ c · escNorm U` for `U ⊆ Ub`, `U' ∈ 𝓝 1`.
* `NSSBase.eq_one_of_escNorm_eq_zero`: `escNorm U g = 0 → g = 1` for `U ⊆ Ub`.

Also: `le_mul_escNorm_add` (turns "for every `n` such that `g, …, g^{n-1} ∈ U`,
`f ≤ A/n + c`" into `f ≤ A · escNorm U g + c`; used for the Lipschitz bound (f) in A3) and
`setOf_escNorm_le_mem_nhds` (small sublevel sets of `escNorm U` are neighbourhoods of `1`).
-/

noncomputable section

namespace HSFormal.GY

open Filter Topology
open scoped Pointwise

/-! ## The escape norm -/

section EscNorm

variable {G : Type*} [Group G]

open Classical in
/-- Tao's escape norm `‖g‖_{e,U}` (Notes 4, (11)): `1 / m` where `m ≥ 1` is the first exponent
with `g ^ m ∉ U`, and `0` if all positive powers of `g` lie in `U`. -/
def escNorm (U : Set G) (g : G) : ℝ :=
  if h : ∃ n : ℕ, 1 ≤ n ∧ g ^ n ∉ U then ((Nat.find h : ℕ) : ℝ)⁻¹ else 0

variable {U V : Set G} {g : G}

/-- The two cases of the definition. -/
theorem escNorm_cases (U : Set G) (g : G) :
    (escNorm U g = 0 ∧ ∀ n : ℕ, 1 ≤ n → g ^ n ∈ U) ∨
      ∃ m : ℕ, 1 ≤ m ∧ g ^ m ∉ U ∧ (∀ i : ℕ, 1 ≤ i → i < m → g ^ i ∈ U) ∧
        escNorm U g = (m : ℝ)⁻¹ := by
  classical
  by_cases h : ∃ n : ℕ, 1 ≤ n ∧ g ^ n ∉ U
  · right
    obtain ⟨h1, h2⟩ := Nat.find_spec h
    refine ⟨Nat.find h, h1, h2, fun i hi hlt => ?_, ?_⟩
    · by_contra hi'
      exact Nat.find_min h hlt ⟨hi, hi'⟩
    · simp only [escNorm, h, ↓reduceDIte]
  · left
    push Not at h
    have h' : ¬ ∃ n : ℕ, 1 ≤ n ∧ g ^ n ∉ U := by push Not; exact h
    refine ⟨?_, h⟩
    simp only [escNorm, h', ↓reduceDIte]

theorem escNorm_nonneg (U : Set G) (g : G) : 0 ≤ escNorm U g := by
  rcases escNorm_cases U g with ⟨h, -⟩ | ⟨m, -, -, -, h⟩
  · rw [h]
  · rw [h]; positivity

theorem escNorm_le_one (U : Set G) (g : G) : escNorm U g ≤ 1 := by
  rcases escNorm_cases U g with ⟨h, -⟩ | ⟨m, hm, -, -, h⟩
  · rw [h]; exact zero_le_one
  · rw [h]; exact inv_le_one_of_one_le₀ (by exact_mod_cast hm)

/-- **Characterisation of the escape norm.** For `c ≥ 0`, `escNorm U g ≤ c` iff every power
`g ^ i` with `1 ≤ i` and `i c < 1` lies in `U`. -/
theorem escNorm_le_iff {c : ℝ} (hc : 0 ≤ c) :
    escNorm U g ≤ c ↔ ∀ i : ℕ, 1 ≤ i → (i : ℝ) * c < 1 → g ^ i ∈ U := by
  rcases escNorm_cases U g with ⟨h, hall⟩ | ⟨m, hm, hgm, hlt, h⟩
  · rw [h]
    exact ⟨fun _ i hi _ => hall i hi, fun _ => hc⟩
  · rw [h]
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    constructor
    · intro hle i hi hic
      refine hlt i hi ?_
      by_contra hmi
      push Not at hmi
      have h1 : (1 : ℝ) ≤ m * c := by
        rw [inv_le_iff_one_le_mul₀' hm'] at hle; exact hle
      have h2 : (m : ℝ) * c ≤ i * c := by gcongr
      linarith
    · intro hall
      by_contra hlt'
      push Not at hlt'
      apply hgm
      refine hall m hm ?_
      rw [← one_div, lt_div_iff₀ hm'] at hlt'
      linarith [mul_comm c (m : ℝ)]

/-- Blueprint form of the characterisation: `escNorm U g ≤ 1/(n+1)` iff `g, …, gⁿ ∈ U`. -/
theorem escNorm_le_inv_iff (n : ℕ) :
    escNorm U g ≤ ((n : ℝ) + 1)⁻¹ ↔ ∀ i ∈ Finset.Icc 1 n, g ^ i ∈ U := by
  rw [escNorm_le_iff (by positivity)]
  have hn : (0 : ℝ) < n + 1 := by positivity
  refine forall_congr' fun i => ?_
  rw [Finset.mem_Icc, ← div_eq_mul_inv, div_lt_one hn]
  constructor
  · rintro h ⟨hi, hin⟩; exact h hi (by exact_mod_cast Nat.lt_succ_of_le hin)
  · rintro h hi hin
    exact h ⟨hi, Nat.le_of_lt_succ (by exact_mod_cast hin)⟩

/-- The escape norm is Tao's `inf {1/(n+1) | g, …, gⁿ ∈ U}` (the definition of blueprint A1). -/
theorem escNorm_eq_sInf (U : Set G) (g : G) :
    escNorm U g =
      sInf ((fun n : ℕ => ((n : ℝ) + 1)⁻¹) '' {n | ∀ i ∈ Finset.Icc 1 n, g ^ i ∈ U}) := by
  set S := (fun n : ℕ => ((n : ℝ) + 1)⁻¹) '' {n | ∀ i ∈ Finset.Icc 1 n, g ^ i ∈ U} with hS
  have hne : S.Nonempty := ⟨((0 : ℕ) + 1 : ℝ)⁻¹, 0, fun i hi => by simp at hi, by simp⟩
  have hbdd : BddBelow S := ⟨0, by rintro _ ⟨n, -, rfl⟩; positivity⟩
  refine le_antisymm (le_csInf hne ?_) ?_
  · rintro _ ⟨n, hn, rfl⟩
    exact (escNorm_le_inv_iff n).2 hn
  · rcases escNorm_cases U g with ⟨he, hall⟩ | ⟨m, hm, -, hlt, he⟩
    · rw [he]
      by_contra hpos
      push Not at hpos
      obtain ⟨n, hn⟩ := exists_nat_gt (sInf S)⁻¹
      have hmem : ((n : ℝ) + 1)⁻¹ ∈ S := ⟨n, fun i hi => hall i (Finset.mem_Icc.1 hi).1, rfl⟩
      have h1 := csInf_le hbdd hmem
      have h2 : ((n : ℝ) + 1)⁻¹ < sInf S := by
        rw [inv_lt_comm₀ (by positivity) hpos]; linarith
      linarith
    · rw [he]
      refine csInf_le hbdd ⟨m - 1, fun i hi => hlt i (Finset.mem_Icc.1 hi).1 ?_, ?_⟩
      · have := (Finset.mem_Icc.1 hi).2; omega
      · simp [Nat.cast_sub hm]

theorem pow_mem_of_mul_escNorm_lt {i : ℕ} (hi : 1 ≤ i) (h : (i : ℝ) * escNorm U g < 1) :
    g ^ i ∈ U :=
  (escNorm_le_iff (escNorm_nonneg U g)).1 le_rfl i hi h

theorem inv_le_escNorm_of_pow_notMem {q : ℕ} (hq : 1 ≤ q) (h : g ^ q ∉ U) :
    (q : ℝ)⁻¹ ≤ escNorm U g := by
  by_contra hlt
  push Not at hlt
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  apply h
  refine pow_mem_of_mul_escNorm_lt hq ?_
  rw [← one_div, lt_div_iff₀ hq'] at hlt
  linarith [mul_comm (escNorm U g) (q : ℝ)]

theorem escNorm_eq_one_of_notMem (h : g ∉ U) : escNorm U g = 1 :=
  le_antisymm (escNorm_le_one U g) (by
    simpa using inv_le_escNorm_of_pow_notMem (q := 1) le_rfl (by simpa using h))

theorem mem_of_escNorm_lt_one (h : escNorm U g < 1) : g ∈ U := by
  simpa using pow_mem_of_mul_escNorm_lt (U := U) (g := g) (i := 1) le_rfl (by simpa using h)

theorem escNorm_of_forall_pow_mem (h : ∀ n : ℕ, 1 ≤ n → g ^ n ∈ U) : escNorm U g = 0 :=
  le_antisymm ((escNorm_le_iff le_rfl).2 fun i hi _ => h i hi) (escNorm_nonneg U g)

theorem escNorm_one (h : (1 : G) ∈ U) : escNorm U (1 : G) = 0 :=
  escNorm_of_forall_pow_mem fun n _ => by simpa using h

/-- A larger set has a smaller escape norm. -/
theorem escNorm_anti (h : U ⊆ V) (g : G) : escNorm V g ≤ escNorm U g :=
  (escNorm_le_iff (escNorm_nonneg U g)).2 fun _ hi hic => h (pow_mem_of_mul_escNorm_lt hi hic)

theorem escNorm_inv_le (hU : U⁻¹ = U) (g : G) : escNorm U g⁻¹ ≤ escNorm U g := by
  refine (escNorm_le_iff (escNorm_nonneg U g)).2 fun i hi hic => ?_
  have h := pow_mem_of_mul_escNorm_lt hi hic
  rw [inv_pow, ← Set.mem_inv, hU]
  simpa using h

/-- For a symmetric `U`, `escNorm U g⁻¹ = escNorm U g`. -/
theorem escNorm_inv (hU : U⁻¹ = U) (g : G) : escNorm U g⁻¹ = escNorm U g :=
  le_antisymm (escNorm_inv_le hU g) (by simpa using escNorm_inv_le hU g⁻¹)

/-- If `g ^ m ∉ U` for the exit time `m ≥ 1`, then `escNorm U g = 1 / m`. -/
theorem escNorm_eq_inv {m : ℕ} (hm : 1 ≤ m) (hgm : g ^ m ∉ U)
    (hlt : ∀ i : ℕ, 1 ≤ i → i < m → g ^ i ∈ U) : escNorm U g = (m : ℝ)⁻¹ := by
  rcases escNorm_cases U g with ⟨-, hall⟩ | ⟨m', hm', hgm', hlt', h⟩
  · exact absurd (hall m hm) hgm
  · rw [h]
    congr 1
    have : m' = m := by
      rcases lt_trichotomy m' m with hlt'' | heq | hgt
      · exact absurd (hlt m' hm' hlt'') hgm'
      · exact heq
      · exact absurd (hlt' m hm hgt) hgm
    rw [this]

/-- Turning "exit-time" bounds into a bound by the escape norm: if `f ≤ A / n + c` for every
`n ≥ 1` such that `g, …, g^{n-1} ∈ U`, then `f ≤ A · escNorm U g + c`. -/
theorem le_mul_escNorm_add {f A c : ℝ} (hA : 0 ≤ A)
    (h : ∀ n : ℕ, 1 ≤ n → (∀ i : ℕ, 1 ≤ i → i < n → g ^ i ∈ U) → f ≤ A / n + c) :
    f ≤ A * escNorm U g + c := by
  rcases escNorm_cases U g with ⟨he, hall⟩ | ⟨m, hm, -, hlt, he⟩
  · rw [he, mul_zero, zero_add]
    by_contra hfc
    push Not at hfc
    obtain ⟨n, hn⟩ := exists_nat_gt (A / (f - c))
    have hfc' : 0 < f - c := by linarith
    have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg hA hfc'.le) hn
    have hn1 : 1 ≤ n := by exact_mod_cast hn0
    have h1 := h n hn1 fun i hi _ => hall i hi
    rw [div_lt_iff₀ hfc'] at hn
    have h2 : A / n < f - c := by rw [div_lt_iff₀ hn0]; linarith
    linarith
  · rw [he, ← div_eq_mul_inv]
    exact h m hm hlt

/-- For `c > 0`, `escNorm U g < c` iff every power `g ^ i` with `1 ≤ i` and `i c ≤ 1` lies in
`U`. -/
theorem escNorm_lt_iff {c : ℝ} (hc : 0 < c) :
    escNorm U g < c ↔ ∀ i : ℕ, 1 ≤ i → (i : ℝ) * c ≤ 1 → g ^ i ∈ U := by
  rcases escNorm_cases U g with ⟨h, hall⟩ | ⟨m, hm, hgm, hlt, h⟩
  · rw [h]
    exact ⟨fun _ i hi _ => hall i hi, fun _ => hc⟩
  · rw [h]
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    rw [inv_lt_iff_one_lt_mul₀' hm']
    constructor
    · intro hlt1 i hi hic
      refine hlt i hi ?_
      by_contra hmi
      push Not at hmi
      have h2 : (m : ℝ) * c ≤ i * c := by gcongr
      linarith
    · intro hall
      by_contra hle
      push Not at hle
      exact hgm (hall m hm hle)

section Topology

variable [TopologicalSpace G] [ContinuousMul G]

/-- Sublevel sets of the escape norm of an open set are open. -/
theorem isOpen_setOf_escNorm_lt (hU : IsOpen U) (c : ℝ) : IsOpen {g : G | escNorm U g < c} := by
  rcases le_or_gt c 0 with hc | hc
  · convert isOpen_empty
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    exact hc.trans (escNorm_nonneg U g)
  · have : {g : G | escNorm U g < c} =
        ⋂ i ∈ (Finset.Icc 1 ⌊c⁻¹⌋₊ : Set ℕ), (fun g : G => g ^ i) ⁻¹' U := by
      ext g
      simp only [Set.mem_ofPred_eq, escNorm_lt_iff hc, Finset.coe_Icc, Set.mem_iInter,
        Set.mem_Icc, Set.mem_preimage]
      refine forall_congr' fun i => ?_
      constructor
      · rintro h ⟨hi, hic⟩
        refine h hi ?_
        have := (Nat.le_floor_iff (inv_nonneg.2 hc.le)).1 hic
        rwa [← one_div, le_div_iff₀ hc] at this
      · intro h hi hic
        refine h ⟨hi, (Nat.le_floor_iff (inv_nonneg.2 hc.le)).2 ?_⟩
        rwa [← one_div, le_div_iff₀ hc]
    rw [this]
    exact isOpen_biInter_finset fun i _ => hU.preimage (continuous_pow i)

/-- Small sublevel sets of the escape norm of a neighbourhood of `1` are neighbourhoods of `1`. -/
theorem setOf_escNorm_le_mem_nhds (hU : U ∈ 𝓝 (1 : G)) {c : ℝ} (hc : 0 < c) :
    {g : G | escNorm U g ≤ c} ∈ 𝓝 (1 : G) := by
  have hev : ∀ᶠ g in 𝓝 (1 : G), ∀ i ∈ Finset.range (⌊c⁻¹⌋₊ + 1), g ^ i ∈ U := by
    rw [Finset.eventually_all]
    intro i _
    have ht : Tendsto (fun g : G => g ^ i) (𝓝 1) (𝓝 1) := by
      simpa using (continuous_pow i).tendsto (1 : G)
    exact ht hU
  filter_upwards [hev] with g hg
  show escNorm U g ≤ c
  rw [escNorm_le_iff hc.le]
  intro i _ hic
  refine hg i (Finset.mem_range.2 (Nat.lt_succ_of_le ?_))
  rw [Nat.le_floor_iff (inv_nonneg.2 hc.le), ← one_div, le_div_iff₀ hc]
  exact hic.le

end Topology

end EscNorm

/-! ## NSS bases -/

/-- An open symmetric neighbourhood `Ub` of `1` with compact closure, such that the only element
all of whose powers lie in `closure Ub` is `1` (blueprint A1). -/
structure NSSBase (G : Type*) [Group G] [TopologicalSpace G] where
  Ub : Set G
  isOpen : IsOpen Ub
  one_mem : (1 : G) ∈ Ub
  inv_eq : Ub⁻¹ = Ub
  isCompact_closure : IsCompact (closure Ub)
  pow_closed : ∀ g : G, (∀ n : ℕ, g ^ n ∈ closure Ub) → g = 1

/-- An NSS locally compact Hausdorff group has an `NSSBase`. -/
theorem exists_nssBase {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] (h : NoSmallSubgroups G) : Nonempty (NSSBase G) := by
  obtain ⟨W, hW, hWS⟩ := h
  obtain ⟨K, hK, hKW, hKc⟩ := local_compact_nhds hW
  set V : Set G := interior K ∩ (interior K)⁻¹ with hV
  have hVo : IsOpen V := isOpen_interior.inter isOpen_interior.inv
  have h1K : (1 : G) ∈ interior K := mem_interior_iff_mem_nhds.2 hK
  have h1 : (1 : G) ∈ V := ⟨h1K, by simpa using h1K⟩
  have hVinv : V⁻¹ = V := by
    rw [hV, Set.inter_inv, inv_inv, Set.inter_comm]
  have hVK : closure V ⊆ K :=
    closure_minimal (Set.inter_subset_left.trans interior_subset) hKc.isClosed
  refine ⟨⟨V, hVo, h1, hVinv, hKc.of_isClosed_subset isClosed_closure hVK, fun g hg => ?_⟩⟩
  have hsub : (Subgroup.zpowers g : Set G) ⊆ W := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    apply hKW
    apply hVK
    rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
    · simpa using hg n
    · have h' : (g ^ n)⁻¹ ∈ (closure V)⁻¹ := by simpa using hg n
      rw [inv_closure, hVinv] at h'
      simpa using h'
  exact Subgroup.zpowers_eq_bot.1 (hWS _ hsub)

namespace NSSBase

variable {G : Type*} [Group G] [TopologicalSpace G] (B : NSSBase G)

theorem one_mem_closure : (1 : G) ∈ closure B.Ub := subset_closure B.one_mem

theorem mem_nhds : B.Ub ∈ 𝓝 (1 : G) := B.isOpen.mem_nhds B.one_mem

/-- If `U ⊆ Ub` then `escNorm U g = 0` forces `g = 1` (no small subgroups). -/
theorem eq_one_of_escNorm_eq_zero {U : Set G} (hU : U ⊆ B.Ub) {g : G} (h : escNorm U g = 0) :
    g = 1 := by
  apply B.pow_closed
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using B.one_mem_closure
  · exact subset_closure (hU (pow_mem_of_mul_escNorm_lt hn (by rw [h]; simp)))

theorem escNorm_pos {U : Set G} (hU : U ⊆ B.Ub) {g : G} (hg : g ≠ 1) : 0 < escNorm U g :=
  (escNorm_nonneg U g).lt_of_ne fun h => hg (B.eq_one_of_escNorm_eq_zero hU h.symm)

variable [IsTopologicalGroup G]

/-- **Tao, Exercise 21.** If `U ⊆ Ub` and `V` is a neighbourhood of `1`, there is `m` such that
`g, g², …, g^m ∈ U` implies `g ∈ V`. -/
theorem exists_pow_mem {U V : Set G} (hU : U ⊆ B.Ub) (hV : V ∈ 𝓝 (1 : G)) :
    ∃ m : ℕ, ∀ g : G, (∀ i : ℕ, 1 ≤ i → i ≤ m → g ^ i ∈ U) → g ∈ V := by
  by_contra hcon
  push Not at hcon
  choose x hxU hxV using hcon
  set 𝒰 : Ultrafilter ℕ := hyperfilter ℕ
  have hatTop : (𝒰 : Filter ℕ) ≤ atTop := hyperfilter_le_cofinite.trans Nat.cofinite_eq_atTop.le
  have hle : (↑(𝒰.map x) : Filter G) ≤ 𝓟 (closure B.Ub) := by
    rw [Ultrafilter.coe_map, le_principal_iff, mem_map]
    filter_upwards [hatTop (eventually_ge_atTop 1)] with m hm
    exact subset_closure (hU (by simpa using hxU m 1 le_rfl hm))
  obtain ⟨y, -, hy⟩ := B.isCompact_closure.ultrafilter_le_nhds _ hle
  have hy' : Tendsto x 𝒰 (𝓝 y) := by rwa [Ultrafilter.coe_map] at hy
  have hpow : ∀ n : ℕ, y ^ n ∈ closure B.Ub := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using B.one_mem_closure
    · refine closure_mono hU (mem_closure_of_tendsto (hy'.pow n) ?_)
      filter_upwards [hatTop (eventually_ge_atTop n)] with m hm using hxU m n hn hm
  have hy1 : y = 1 := B.pow_closed y hpow
  have hyV : y ∈ closure (interior V)ᶜ :=
    mem_closure_of_tendsto hy' (Eventually.of_forall fun m h => hxV m (interior_subset h))
  rw [isOpen_interior.isClosed_compl.closure_eq, hy1] at hyV
  exact hyV (mem_interior_iff_mem_nhds.2 hV)

/-- `exists_pow_mem` in the `Finset.Icc` form of the blueprint. -/
theorem exists_pow_mem' {U V : Set G} (hU : U ⊆ B.Ub) (hV : V ∈ 𝓝 (1 : G)) :
    ∃ m : ℕ, ∀ g : G, (∀ i ∈ Finset.Icc 1 m, g ^ i ∈ U) → g ∈ V := by
  obtain ⟨m, hm⟩ := B.exists_pow_mem hU hV
  exact ⟨m, fun g hg => hm g fun i hi him => hg i (Finset.mem_Icc.2 ⟨hi, him⟩)⟩

/-- **Tao (12).** For `U ⊆ Ub` and any neighbourhood `U'` of `1`, `escNorm U' ≤ c · escNorm U`. -/
theorem escNorm_le {U U' : Set G} (hU : U ⊆ B.Ub) (hU' : U' ∈ 𝓝 (1 : G)) :
    ∃ c ≥ (1 : ℝ), ∀ g : G, escNorm U' g ≤ c * escNorm U g := by
  obtain ⟨m, hm⟩ := B.exists_pow_mem hU hU'
  refine ⟨(m : ℝ) + 1, by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)], fun g => ?_⟩
  have he := escNorm_nonneg U g
  rw [escNorm_le_iff (by positivity)]
  intro j hj hjc
  apply hm
  intro i hi him
  rw [← pow_mul]
  refine pow_mem_of_mul_escNorm_lt (Nat.one_le_iff_ne_zero.2 (by positivity)) ?_
  have hi' : (i : ℝ) ≤ m + 1 := by
    have : (i : ℝ) ≤ m := by exact_mod_cast him
    linarith
  calc ((j * i : ℕ) : ℝ) * escNorm U g = j * (i * escNorm U g) := by push_cast; ring
    _ ≤ j * ((m + 1) * escNorm U g) := by gcongr
    _ = j * ((m + 1) * escNorm U g) := rfl
    _ < 1 := by linarith

end NSSBase

end HSFormal.GY
