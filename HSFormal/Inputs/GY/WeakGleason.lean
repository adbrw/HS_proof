import HSFormal.Inputs.GY.GleasonLemma

/-!
# NSS ⇒ weak Gleason norm (module A4)

Tao 254A Notes 4, Theorem 22. Main result:

```
theorem nonempty_weakGleasonNorm {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    (h : NoSmallSubgroups G) : Nonempty (WeakGleasonNorm G)
```

The norm is Tao's modified escape norm `‖g‖_* = inf {Σ ‖gᵢ‖_{e,U₀} | g = g₁ ⋯ gₙ}`
(`GleasonAux.prodInf (escNorm U₀)`), which is symmetric and subadditive, and comparable to `‖·‖_{e,U₀}` by
Gleason's lemma (A3): `‖g‖_{e,U₀} / K₀ ≤ ‖g‖_* ≤ ‖g‖_{e,U₀}`.

* definiteness: A1's `eq_one_of_escNorm_eq_zero`;
* `small_subset`: Tao's Exercise 21 (`NSSBase.exists_pow_mem`);
* continuity: `WeakGleasonNorm.continuous_of_mul_le` and `setOf_escNorm_le_mem_nhds`;
* escape: Tao's exit-time argument (the least multiple `q n` of `n` beyond the exit time `m` of
  `g` from `U₀` has `g^{qn} ∉ U₁`, `U₁² ⊆ U₀`), then (12).

The intermediate statement `NSSBase.nonempty_weakGleasonNorm_of_prod_le` only uses the conclusion
of Gleason's lemma.
-/

noncomputable section

namespace HSFormal.GY

open Filter Topology
open scoped Pointwise

/-! ## The infimum over factorisations -/

namespace GleasonAux

section ProdInf

variable {G : Type*} [Group G]

/-- `prodInf ν g = inf {Σ ν lᵢ | l.prod = g}` (Tao's modified escape norm `‖g‖_{*,U₀}` for
`ν = escNorm U₀`). -/
def prodInf (ν : G → ℝ) (g : G) : ℝ := ⨅ l : {l : List G // l.prod = g}, (l.1.map ν).sum

variable {ν : G → ℝ}

instance nonempty_factorisation (g : G) : Nonempty {l : List G // l.prod = g} :=
  ⟨⟨[g], by simp⟩⟩

theorem bddBelow_prodInf (hν : ∀ g, 0 ≤ ν g) (g : G) :
    BddBelow (Set.range fun l : {l : List G // l.prod = g} => (l.1.map ν).sum) :=
  ⟨0, by rintro _ ⟨l, rfl⟩; exact sum_map_nonneg hν l.1⟩

theorem prodInf_nonneg (hν : ∀ g, 0 ≤ ν g) (g : G) : 0 ≤ prodInf ν g :=
  Real.iInf_nonneg fun l => sum_map_nonneg hν l.1

theorem prodInf_le (hν : ∀ g, 0 ≤ ν g) {g : G} (l : List G) (hl : l.prod = g) :
    prodInf ν g ≤ (l.map ν).sum :=
  ciInf_le (bddBelow_prodInf hν g) ⟨l, hl⟩

theorem prodInf_le_self (hν : ∀ g, 0 ≤ ν g) (g : G) : prodInf ν g ≤ ν g := by
  simpa using prodInf_le hν [g] (by simp)

theorem prodInf_one (hν : ∀ g, 0 ≤ ν g) : prodInf ν (1 : G) = 0 :=
  le_antisymm (by simpa using prodInf_le hν (g := (1 : G)) [] rfl) (prodInf_nonneg hν 1)

theorem prodInf_mul_le (hν : ∀ g, 0 ≤ ν g) (g h : G) :
    prodInf ν (g * h) ≤ prodInf ν g + prodInf ν h := by
  have key : ∀ (l₁ : {l : List G // l.prod = g}) (l₂ : {l : List G // l.prod = h}),
      prodInf ν (g * h) ≤ (l₁.1.map ν).sum + (l₂.1.map ν).sum := by
    intro l₁ l₂
    have := prodInf_le hν (l₁.1 ++ l₂.1) (by rw [List.prod_append, l₁.2, l₂.2])
    simpa [List.map_append, List.sum_append] using this
  have h1 : ∀ l₁ : {l : List G // l.prod = g},
      prodInf ν (g * h) - (l₁.1.map ν).sum ≤ prodInf ν h :=
    fun l₁ => le_ciInf fun l₂ => by linarith [key l₁ l₂]
  have h2 : prodInf ν (g * h) - prodInf ν h ≤ prodInf ν g :=
    le_ciInf fun l₁ => by linarith [h1 l₁]
  linarith

theorem prodInf_inv_le (hν : ∀ g, 0 ≤ ν g) (hsymm : ∀ g, ν g⁻¹ = ν g) (g : G) :
    prodInf ν g⁻¹ ≤ prodInf ν g := by
  refine le_ciInf fun l => ?_
  have hl : ((l.1.map fun x => x⁻¹).reverse).prod = g⁻¹ := by
    rw [← List.prod_inv_reverse, l.2]
  refine (prodInf_le hν _ hl).trans (le_of_eq ?_)
  rw [List.map_reverse, List.sum_reverse, List.map_map]
  congr 2
  funext x
  simp [hsymm]

theorem prodInf_inv (hν : ∀ g, 0 ≤ ν g) (hsymm : ∀ g, ν g⁻¹ = ν g) (g : G) :
    prodInf ν g⁻¹ = prodInf ν g :=
  le_antisymm (prodInf_inv_le hν hsymm g) (by simpa using prodInf_inv_le hν hsymm g⁻¹)

theorem prodInf_pow_le (hν : ∀ g, 0 ≤ ν g) (g : G) (n : ℕ) :
    prodInf ν (g ^ n) ≤ n * prodInf ν g := by
  induction n with
  | zero => simp [prodInf_one hν]
  | succ n ih =>
    rw [pow_succ]
    calc prodInf ν (g ^ n * g) ≤ prodInf ν (g ^ n) + prodInf ν g := prodInf_mul_le hν _ _
      _ ≤ n * prodInf ν g + prodInf ν g := by linarith
      _ = ((n + 1 : ℕ) : ℝ) * prodInf ν g := by push_cast; ring

/-- If `ν (l.prod) ≤ K Σ ν lᵢ` for all lists, then `ν g ≤ K prodInf ν g`. -/
theorem le_mul_prodInf {K : ℝ} (hK : 0 < K)
    (h : ∀ l : List G, ν l.prod ≤ K * (l.map ν).sum) (g : G) : ν g ≤ K * prodInf ν g := by
  have : ν g / K ≤ prodInf ν g := le_ciInf fun l => by
    rw [div_le_iff₀ hK]
    have := h l.1
    rw [l.2] at this
    linarith
  rwa [div_le_iff₀ hK, mul_comm] at this

end ProdInf

end GleasonAux

open GleasonAux

/-! ## The weak Gleason norm -/

section Main

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Tao, Theorem 22, from Gleason's lemma.** If `U₀ ⊆ Ub` is an open symmetric neighbourhood
of `1` whose escape norm satisfies the approximate triangle inequality, then `prodInf (escNorm U₀)`
is a weak Gleason norm. -/
theorem NSSBase.nonempty_weakGleasonNorm_of_prod_le (B : NSSBase G) {U₀ : Set G}
    (hU₀o : IsOpen U₀) (h1 : (1 : G) ∈ U₀) (hinv : U₀⁻¹ = U₀) (hU₀B : U₀ ⊆ B.Ub) {K₀ : ℝ}
    (hK₀ : 1 ≤ K₀) (hK : ∀ l : List G, escNorm U₀ l.prod ≤ K₀ * (l.map (escNorm U₀)).sum) :
    Nonempty (WeakGleasonNorm G) := by
  set N : G → ℝ := prodInf (escNorm U₀) with hNdef
  have hν : ∀ g, 0 ≤ escNorm U₀ g := escNorm_nonneg U₀
  have hsymm : ∀ g, escNorm U₀ g⁻¹ = escNorm U₀ g := escNorm_inv hinv
  have hK₀pos : 0 < K₀ := by linarith
  have hN0 : ∀ g, 0 ≤ N g := prodInf_nonneg hν
  have hNle : ∀ g, N g ≤ escNorm U₀ g := prodInf_le_self hν
  have hleN : ∀ g, escNorm U₀ g ≤ K₀ * N g := le_mul_prodInf hK₀pos hK
  have hN1 : N 1 = 0 := prodInf_one hν
  have hNinv : ∀ g, N g⁻¹ = N g := prodInf_inv hν hsymm
  have hNmul : ∀ g h, N (g * h) ≤ N g + N h := prodInf_mul_le hν
  have hU₀n : U₀ ∈ 𝓝 (1 : G) := hU₀o.mem_nhds h1
  -- neighbourhoods
  have hsmall : ∀ U ∈ 𝓝 (1 : G), ∃ r > 0, {g | N g < r} ⊆ U := by
    intro U hU
    obtain ⟨m, hm⟩ := B.exists_pow_mem hU₀B hU
    refine ⟨(K₀ * (m + 1))⁻¹, by positivity, fun g hg => hm g fun i hi him => ?_⟩
    apply pow_mem_of_mul_escNorm_lt hi
    have hg' : N g < (K₀ * (m + 1))⁻¹ := hg
    have h3 : escNorm U₀ g < ((m : ℝ) + 1)⁻¹ := by
      calc escNorm U₀ g ≤ K₀ * N g := hleN g
        _ < K₀ * (K₀ * (m + 1))⁻¹ := by gcongr
        _ = ((m : ℝ) + 1)⁻¹ := by field_simp
    have h4 : (i : ℝ) ≤ m := by exact_mod_cast him
    have h5 := hν g
    calc (i : ℝ) * escNorm U₀ g ≤ m * escNorm U₀ g := by gcongr
      _ ≤ m * ((m : ℝ) + 1)⁻¹ := by gcongr
      _ < 1 := by
        rw [← div_eq_mul_inv, div_lt_one (by positivity)]
        linarith
  have hnhds : ∀ r > 0, {g | N g < r} ∈ 𝓝 (1 : G) := by
    intro r hr
    filter_upwards [setOf_escNorm_le_mem_nhds hU₀n (half_pos hr)] with g hg
    exact (hNle g).trans_lt (lt_of_le_of_lt hg (half_lt_self hr))
  -- the escape constant
  obtain ⟨V, hVo, hV1, hVV⟩ := exists_open_nhds_one_mul_subset hU₀n
  set U₁ : Set G := V ∩ V⁻¹ with hU₁
  have hU₁n : U₁ ∈ 𝓝 (1 : G) :=
    inter_mem (hVo.mem_nhds hV1) (inv_mem_nhds_one G (hVo.mem_nhds hV1))
  have hU₁inv : U₁⁻¹ = U₁ := by rw [hU₁, Set.inter_inv, inv_inv, Set.inter_comm]
  have hU₁U₀ : U₁ * U₁ ⊆ U₀ :=
    (Set.mul_subset_mul Set.inter_subset_left Set.inter_subset_left).trans hVV
  have h1U₁ : (1 : G) ∈ U₁ := mem_of_mem_nhds hU₁n
  have hU₁sub : U₁ ⊆ U₀ := fun x hx => hU₁U₀ ⟨x, hx, 1, h1U₁, mul_one x⟩
  obtain ⟨c₁, hc₁, hc₁le⟩ := B.escNorm_le hU₀B hU₁n
  obtain ⟨r₁, hr₁, hr₁sub⟩ := hsmall U₁ hU₁n
  set C : ℝ := max 2 (max (2 * K₀ * c₁) (2 / r₁)) with hC
  have hC2 : 2 ≤ C := le_max_left _ _
  have hC0 : 0 < C := by linarith
  have hCK : 2 * K₀ * c₁ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCr : 2 / r₁ ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hCinv : C⁻¹ < r₁ := by
    rw [inv_lt_comm₀ hC0 hr₁]
    calc r₁⁻¹ < 2 / r₁ := by
          rw [div_eq_mul_inv]; linarith [inv_pos.2 hr₁]
      _ ≤ C := hCr
  have hescape : ∀ (g : G) (n : ℕ), (n : ℝ) * N g ≤ C⁻¹ → (n : ℝ) * N g ≤ C * N (g ^ n) := by
    intro g n hgn
    rcases eq_or_ne g 1 with rfl | hg
    · rw [hN1, mul_zero]; exact mul_nonneg hC0.le (hN0 _)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [Nat.cast_zero, zero_mul]; exact mul_nonneg hC0.le (hN0 _)
    have hpow : ∀ i : ℕ, 1 ≤ i → i ≤ n → g ^ i ∈ U₁ := by
      intro i _ hin
      refine hr₁sub ?_
      show N (g ^ i) < r₁
      have hi' : (i : ℝ) ≤ n := by exact_mod_cast hin
      calc N (g ^ i) ≤ i * N g := prodInf_pow_le hν g i
        _ ≤ n * N g := by gcongr; exact hN0 g
        _ ≤ C⁻¹ := hgn
        _ < r₁ := hCinv
    -- the exit time `m` of `g` from `U₀`
    rcases escNorm_cases U₀ g with ⟨he, -⟩ | ⟨m, hm, hgm, -, he⟩
    · exact absurd (B.eq_one_of_escNorm_eq_zero hU₀B he) hg
    have hnm : n < m := by
      by_contra hmn
      push Not at hmn
      exact hgm (hU₁sub (hpow m hm hmn))
    set q := m / n + 1 with hq
    have hqn_gt : m < q * n := by rw [hq, add_mul, one_mul]; exact Nat.lt_div_mul_add hn
    have hqn_le : q * n ≤ m + n := by
      rw [hq, add_mul, one_mul]; have := Nat.div_mul_le_self m n; omega
    have hq1 : 1 ≤ q := Nat.le_add_left 1 _
    have hnot : (g ^ n) ^ q ∉ U₁ := by
      intro hmem
      have hi1 : 1 ≤ q * n - m := by omega
      have hin : q * n - m ≤ n := by omega
      have e : g ^ m = g ^ (n * q) * (g ^ (q * n - m))⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq, ← pow_add]
        congr 1
        rw [mul_comm n q]
        omega
      have hi : g ^ (q * n - m) ∈ U₁⁻¹ := by rw [hU₁inv]; exact hpow _ hi1 hin
      apply hgm
      rw [e]
      refine hU₁U₀ (Set.mul_mem_mul ?_ (Set.mem_inv.1 hi))
      rwa [pow_mul]
    have hesc : (q : ℝ)⁻¹ ≤ escNorm U₁ (g ^ n) := inv_le_escNorm_of_pow_notMem hq1 hnot
    have hqm : (q : ℝ) * n ≤ 2 * m := by exact_mod_cast (by omega : q * n ≤ 2 * m)
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
    calc (n : ℝ) * N g ≤ n * escNorm U₀ g := by gcongr; exact hNle g
      _ = n / m := by rw [he, div_eq_mul_inv]
      _ ≤ 2 / q := by rw [div_le_div_iff₀ hm0 hq0]; linarith
      _ ≤ 2 * escNorm U₁ (g ^ n) := by rw [div_eq_mul_inv]; gcongr
      _ ≤ 2 * (c₁ * escNorm U₀ (g ^ n)) := by gcongr; exact hc₁le _
      _ ≤ 2 * (c₁ * (K₀ * N (g ^ n))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hleN _) (by linarith))
            (by norm_num)
      _ = 2 * K₀ * c₁ * N (g ^ n) := by ring
      _ ≤ C * N (g ^ n) := by gcongr; exact hN0 _
  exact ⟨{
    N := N
    C := C
    two_le_C := hC2
    map_one := hN1
    map_inv := hNinv
    mul_le := hNmul
    eq_one := fun g hg => B.eq_one_of_escNorm_eq_zero hU₀B
      (le_antisymm (by simpa [hg] using hleN g) (hν g))
    continuous := WeakGleasonNorm.continuous_of_mul_le hNinv hNmul hnhds
    small_subset := hsmall
    escape := hescape }⟩

/-- **Tao 254A Notes 4, Theorem 22.** A locally compact Hausdorff NSS group has a weak Gleason
norm. -/
theorem nonempty_weakGleasonNorm {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] (h : NoSmallSubgroups G) :
    Nonempty (WeakGleasonNorm G) := by
  obtain ⟨B⟩ := exists_nssBase h
  obtain ⟨U₀, hU₀o, h1, hinv, hU₀4, K₀, hK₀, hK⟩ := B.exists_escNorm_prod_le
  have hU₀B : U₀ ⊆ B.Ub := by
    refine subset_trans ?_ hU₀4
    have h3 : (1 : G) ∈ U₀ ^ 3 := by simpa using Set.pow_mem_pow (n := 3) h1
    intro x hx
    rw [pow_succ]
    exact ⟨1, h3, x, hx, one_mul x⟩
  exact B.nonempty_weakGleasonNorm_of_prod_le hU₀o h1 hinv hU₀B hK₀ hK

end Main

end HSFormal.GY
