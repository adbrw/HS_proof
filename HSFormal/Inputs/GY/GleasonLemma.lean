import HSFormal.Inputs.GY.Escape
import HSFormal.Inputs.GY.Convolution

/-!
# Gleason's lemma: the approximate triangle inequality for the escape norm (module A3)

Tao 254A Notes 4, Proposition 24; blueprint §5 H1. Main result:

```
theorem NSSBase.exists_escNorm_prod_le [IsTopologicalGroup G] [LocallyCompactSpace G]
    (B : NSSBase G) :
    ∃ U₀ : Set G, IsOpen U₀ ∧ (1 : G) ∈ U₀ ∧ U₀⁻¹ = U₀ ∧ U₀ ^ 4 ⊆ B.Ub ∧
      ∃ K₀ : ℝ, 1 ≤ K₀ ∧ ∀ l : List G, escNorm U₀ l.prod ≤ K₀ * (l.map (escNorm U₀)).sum
```

## Proof structure (blueprint H1, with simplifications)

* `chainDist ν U x = inf {Σ ν lᵢ | l.prod⁻¹ * x ∈ U}` and `bump M ν U = max (1 - M · chainDist) 0`
  are a general construction of "Lipschitz" bumps: `bump = 1` on `U`, `|∂_g bump| ≤ M ν g` for
  symmetric `ν`, `bump` is lower semicontinuous (hence measurable) when `U` is open.
  Both of Tao's functions are of this form:
  * `ψ = bump M ν_ε U₀` with `ν_ε g = escNorm U₀ g + ε`. (Tao uses
    `(1 - M dist_*(x, U₀))_+`; `chainDist ν_ε U₀ x` *is* `inf_{u ∈ U₀} ‖x u⁻¹‖_{*,ε}`.)
  * `η = bump 1 ν₁ U₀` with `ν₁ g = 1/L` on `U₁` and `1` off `U₁`. (This is Tao's
    `sup {1 - j/L | x ∈ U₁^j U₀}`.)
* `GleasonData G μ` bundles the choices that do not depend on `ε` and `M`
  (blueprint "constants independent of `ε` and `M`"): `U₀, U₁, U₂, L` and the two constants of
  (12) that are used (`m₄`, `c₂`).
* With `φ = ψ ⋆ η` (A2's `conv`): (17) `escNorm_le_tnorm`, (e) `abs_ldiff_ldiff_φ_le`,
  (f) `tnorm_φ_le`, (g) `bootstrap`: `(13)_M ⇒ (13)_{Bc + M/2}`.
* Iteration from `(13)_{1/ε}` (`H13_init`) and `ε → 0` (`escNorm_prod_le`).

The generic helpers (`chainDist`, `bump`, list lemmas) live in the namespace
`HSFormal.GY.GleasonAux` to avoid name clashes with other modules.

Deviations from the blueprint (all simplifications, no change of the statement except that the
conclusion is strengthened by `1 ≤ K₀`):
* (17) is proved as `escNorm U₀ g ≤ (m₄ / a₀) ‖g‖_φ` without the case split `s ≥ a₀/2`, using the
  characterisation `escNorm_le_iff`.
* The Lipschitz bound for `ψ` is used in the form `|∂_g ψ| ≤ M ν_ε g` directly (no modified
  escape norm `‖·‖_{*ε}` is needed).
* `U₁` is not required to be open (only `η`'s superlevel sets must be open, and those are unions
  of translates of the open `U₀`).
-/

noncomputable section

namespace HSFormal.GY

open MeasureTheory Filter Topology Set
open scoped Pointwise ENNReal

/-! ## List helpers -/

namespace GleasonAux

section ListAux

variable {G : Type*}

theorem sum_map_nonneg {ν : G → ℝ} (hν : ∀ g, 0 ≤ ν g) (l : List G) : 0 ≤ (l.map ν).sum :=
  List.sum_nonneg fun x hx => by
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    exact hν a

theorem le_sum_map_of_mem {ν : G → ℝ} (hν : ∀ g, 0 ≤ ν g) {l : List G} {a : G} (ha : a ∈ l) :
    ν a ≤ (l.map ν).sum :=
  List.single_le_sum (fun x hx => by obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx; exact hν b) _
    (List.mem_map_of_mem ha)

theorem length_mul_le_sum_map {ν : G → ℝ} {c : ℝ} (hν : ∀ g, c ≤ ν g) (l : List G) :
    (l.length : ℝ) * c ≤ (l.map ν).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    push_cast
    linarith [hν a]

theorem sum_map_add_const (ν : G → ℝ) (ε : ℝ) (l : List G) :
    (l.map fun g => ν g + ε).sum = (l.map ν).sum + l.length * ε := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    push_cast
    ring

/-- Products of at most `L` elements of a small neighbourhood of `1` stay in a given
neighbourhood of `1`. -/
theorem exists_nhds_list_prod_mem [Monoid G] [TopologicalSpace G] [ContinuousMul G] (L : ℕ)
    {V : Set G} (hV : V ∈ 𝓝 (1 : G)) :
    ∃ W ∈ 𝓝 (1 : G), ∀ l : List G, (∀ h ∈ l, h ∈ W) → l.length ≤ L → l.prod ∈ V := by
  induction L generalizing V with
  | zero =>
    refine ⟨V, hV, fun l _ hl => ?_⟩
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hl), List.prod_nil]
    exact mem_of_mem_nhds hV
  | succ L ih =>
    obtain ⟨V', hV'o, hV'1, hV'⟩ := exists_open_nhds_one_mul_subset hV
    obtain ⟨W, hW, hWl⟩ := ih (hV'o.mem_nhds hV'1)
    refine ⟨W ∩ V', inter_mem hW (hV'o.mem_nhds hV'1), fun l hl hlen => ?_⟩
    cases l with
    | nil => simpa using mem_of_mem_nhds hV
    | cons a l =>
      rw [List.prod_cons]
      apply hV'
      refine Set.mul_mem_mul (hl a (List.mem_cons.2 (Or.inl rfl))).2 ?_
      refine hWl l (fun h hh => (hl h (List.mem_cons.2 (Or.inr hh))).1) ?_
      simpa using hlen

end ListAux

/-! ## Lipschitz bumps from chain distances -/

section Bump

variable {G : Type*} [Group G]

/-- `chainDist ν U x = inf {Σ ν lᵢ | l.prod⁻¹ * x ∈ U}`: the `ν`-chain distance from `x` to `U`
(for `ν = ν_ε` this is `inf_{u ∈ U} ‖x u⁻¹‖_{*,ε}`). -/
def chainDist (ν : G → ℝ) (U : Set G) (x : G) : ℝ :=
  ⨅ l : {l : List G // l.prod⁻¹ * x ∈ U}, (l.1.map ν).sum

/-- The bump `max (1 - M · chainDist ν U x) 0`. -/
def bump (M : ℝ) (ν : G → ℝ) (U : Set G) (x : G) : ℝ := max (1 - M * chainDist ν U x) 0

variable {ν : G → ℝ} {U : Set G} {M : ℝ}

theorem chainDist_nonneg (hν : ∀ g, 0 ≤ ν g) (x : G) : 0 ≤ chainDist ν U x :=
  Real.iInf_nonneg fun l => sum_map_nonneg hν l.1

theorem bddBelow_chainDist (hν : ∀ g, 0 ≤ ν g) (x : G) :
    BddBelow (range fun l : {l : List G // l.prod⁻¹ * x ∈ U} => (l.1.map ν).sum) :=
  ⟨0, by rintro _ ⟨l, rfl⟩; exact sum_map_nonneg hν l.1⟩

theorem chainDist_le (hν : ∀ g, 0 ≤ ν g) {x : G} (l : List G) (hl : l.prod⁻¹ * x ∈ U) :
    chainDist ν U x ≤ (l.map ν).sum :=
  ciInf_le (bddBelow_chainDist hν x) ⟨l, hl⟩

theorem chainDist_eq_zero (hν : ∀ g, 0 ≤ ν g) {x : G} (hx : x ∈ U) : chainDist ν U x = 0 :=
  le_antisymm (by simpa using chainDist_le hν (U := U) [] (by simpa using hx))
    (chainDist_nonneg hν x)

theorem nonempty_chain (h1 : (1 : G) ∈ U) (x : G) :
    Nonempty {l : List G // l.prod⁻¹ * x ∈ U} :=
  ⟨⟨[x], by simpa using h1⟩⟩

theorem chainDist_lt_iff (hν : ∀ g, 0 ≤ ν g) (h1 : (1 : G) ∈ U) {x : G} {c : ℝ} :
    chainDist ν U x < c ↔ ∃ l : List G, l.prod⁻¹ * x ∈ U ∧ (l.map ν).sum < c := by
  have := nonempty_chain h1 x
  rw [chainDist, ciInf_lt_iff (bddBelow_chainDist hν x)]
  constructor
  · rintro ⟨l, hl⟩; exact ⟨l.1, l.2, hl⟩
  · rintro ⟨l, hl, hc⟩; exact ⟨⟨l, hl⟩, hc⟩

theorem chainDist_mul_le (hν : ∀ g, 0 ≤ ν g) (h1 : (1 : G) ∈ U) (h x : G) :
    chainDist ν U (h * x) ≤ ν h + chainDist ν U x := by
  have := nonempty_chain h1 x
  rw [← sub_le_iff_le_add']
  refine le_ciInf fun l => ?_
  rw [sub_le_iff_le_add']
  have hmem : (h :: l.1).prod⁻¹ * (h * x) ∈ U := by
    simpa [List.prod_cons, mul_inv_rev, mul_assoc] using l.2
  simpa using chainDist_le hν (h :: l.1) hmem

theorem abs_chainDist_sub_le (hν : ∀ g, 0 ≤ ν g) (hsymm : ∀ g, ν g⁻¹ = ν g)
    (h1 : (1 : G) ∈ U) (g x : G) :
    |chainDist ν U x - chainDist ν U (g⁻¹ * x)| ≤ ν g := by
  have a := chainDist_mul_le hν h1 g⁻¹ x
  have b := chainDist_mul_le hν h1 g (g⁻¹ * x)
  rw [mul_inv_cancel_left] at b
  rw [hsymm] at a
  rw [abs_le]; constructor <;> linarith

theorem bump_nonneg (x : G) : 0 ≤ bump M ν U x := le_max_right _ _

theorem bump_le_one (hM : 0 ≤ M) (hν : ∀ g, 0 ≤ ν g) (x : G) : bump M ν U x ≤ 1 :=
  max_le (by nlinarith [chainDist_nonneg hν (U := U) x]) zero_le_one

theorem abs_bump_le (hM : 0 ≤ M) (hν : ∀ g, 0 ≤ ν g) (x : G) : |bump M ν U x| ≤ 1 := by
  rw [abs_of_nonneg (bump_nonneg x)]; exact bump_le_one hM hν x

theorem bump_eq_one (hν : ∀ g, 0 ≤ ν g) {x : G} (hx : x ∈ U) : bump M ν U x = 1 := by
  simp [bump, chainDist_eq_zero hν hx]

theorem abs_ldiff_bump_le (hM : 0 ≤ M) (hν : ∀ g, 0 ≤ ν g) (hsymm : ∀ g, ν g⁻¹ = ν g)
    (h1 : (1 : G) ∈ U) (g x : G) : |ldiff g (bump M ν U) x| ≤ M * ν g := by
  rw [ldiff_apply, bump, bump]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  have e : 1 - M * chainDist ν U x - (1 - M * chainDist ν U (g⁻¹ * x))
      = -(M * (chainDist ν U x - chainDist ν U (g⁻¹ * x))) := by ring
  rw [e, abs_neg, abs_mul, abs_of_nonneg hM]
  exact mul_le_mul_of_nonneg_left (abs_chainDist_sub_le hν hsymm h1 g x) hM

theorem exists_of_bump_ne_zero (hM : 0 < M) (hν : ∀ g, 0 ≤ ν g) (h1 : (1 : G) ∈ U) {x : G}
    (hx : bump M ν U x ≠ 0) : ∃ l : List G, l.prod⁻¹ * x ∈ U ∧ M * (l.map ν).sum < 1 := by
  have h : M * chainDist ν U x < 1 := by
    by_contra h
    push Not at h
    exact hx (max_eq_right (by linarith))
  have h' : chainDist ν U x < 1 / M := by rw [lt_div_iff₀ hM]; linarith
  obtain ⟨l, hl, hs⟩ := (chainDist_lt_iff hν h1).1 h'
  exact ⟨l, hl, by rw [lt_div_iff₀ hM] at hs; linarith⟩

variable [TopologicalSpace G] [ContinuousMul G]

theorem isOpen_setOf_chainDist_lt (hν : ∀ g, 0 ≤ ν g) (h1 : (1 : G) ∈ U) (hU : IsOpen U)
    (c : ℝ) : IsOpen {x | chainDist ν U x < c} := by
  have : {x | chainDist ν U x < c}
      = ⋃ l ∈ {l : List G | (l.map ν).sum < c}, (fun x => l.prod⁻¹ * x) ⁻¹' U := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage, exists_prop,
      chainDist_lt_iff hν h1]
    exact ⟨fun ⟨l, h, h'⟩ => ⟨l, h', h⟩, fun ⟨l, h, h'⟩ => ⟨l, h', h⟩⟩
  rw [this]
  exact isOpen_biUnion fun l _ => hU.preimage (continuous_const_mul _)

theorem measurable_bump [MeasurableSpace G] [OpensMeasurableSpace G] (hM : 0 < M)
    (hν : ∀ g, 0 ≤ ν g) (h1 : (1 : G) ∈ U) (hU : IsOpen U) : Measurable (bump M ν U) := by
  refine measurable_of_Ioi fun t => IsOpen.measurableSet ?_
  rcases lt_or_ge t 0 with ht | ht
  · convert isOpen_univ
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_univ, iff_true]
    exact ht.trans_le (bump_nonneg x)
  · have : bump M ν U ⁻¹' Set.Ioi t = {x | chainDist ν U x < (1 - t) / M} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_ofPred_eq, bump, lt_max_iff,
        lt_div_iff₀ hM]
      constructor
      · rintro (h | h)
        · linarith
        · linarith
      · intro h; left; linarith
    rw [this]
    exact isOpen_setOf_chainDist_lt hν h1 hU _

end Bump

end GleasonAux

open GleasonAux

/-! ## The data of the bootstrap -/

/-- The choices of blueprint H1 that do not depend on `ε` and `M`. `S₄ = U₀ * U₀ * (U₀ * U₀)` is
Tao's `U₀⁴` and `S₃ = U₀ * (U₀ * U₀)` his `U₀³`. -/
structure GleasonData (G : Type*) [Group G] [TopologicalSpace G] [MeasurableSpace G]
    (μ : Measure G) where
  B : NSSBase G
  U₀ : Set G
  U₁ : Set G
  U₂ : Set G
  L : ℕ
  m₄ : ℝ
  c₂ : ℝ
  isOpen_U₀ : IsOpen U₀
  one_mem_U₀ : (1 : G) ∈ U₀
  inv_U₀ : U₀⁻¹ = U₀
  S₄_sub : U₀ * U₀ * (U₀ * U₀) ⊆ B.Ub
  L_pos : 0 < L
  inv_U₁ : U₁⁻¹ = U₁
  prod_mem : ∀ l : List G, (∀ h ∈ l, h ∈ U₁) → l.length ≤ L → l.prod ∈ U₀
  U₂_sub : U₂ ⊆ U₀
  conj_mem : ∀ k ∈ U₂, ∀ y ∈ U₀ * (U₀ * U₀), y⁻¹ * k * y ∈ U₁
  m₄_nonneg : 0 ≤ m₄
  escNorm_le_m₄ : ∀ g, escNorm U₀ g ≤ m₄ * escNorm (U₀ * U₀ * (U₀ * U₀)) g
  c₂_nonneg : 0 ≤ c₂
  escNorm_le_c₂ : ∀ g, escNorm U₂ g ≤ c₂ * escNorm U₀ g
  L_large : m₄ / (μ U₀).toReal * (μ (U₀ * (U₀ * U₀))).toReal / L ≤ 1 / 2

namespace GleasonData

section Defs

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] {μ : Measure G}
  (D : GleasonData G μ)

/-- `ν_ε g = ‖g‖_{e,U₀} + ε`. -/
def ν (ε : ℝ) (g : G) : ℝ := escNorm D.U₀ g + ε

open Classical in
/-- `ν₁ g = 1/L` on `U₁`, `1` off `U₁`. -/
def ν₁ (g : G) : ℝ := if g ∈ D.U₁ then (D.L : ℝ)⁻¹ else 1

/-- Tao's `ψ`. -/
def ψ (M ε : ℝ) : G → ℝ := bump M (D.ν ε) D.U₀

/-- Tao's `η`. -/
def η : G → ℝ := bump 1 D.ν₁ D.U₀

/-- Tao's `φ = ψ ⋆ η`. -/
def φ (M ε : ℝ) : G → ℝ := conv μ (D.ψ M ε) D.η

/-- `a₀ = μ U₀`. -/
def a₀ : ℝ := (μ D.U₀).toReal

/-- `b₃ = μ U₀³`. -/
def b₃ : ℝ := (μ (D.U₀ * (D.U₀ * D.U₀))).toReal

/-- `B₀ = μ U₀²`, a bound for `φ`. -/
def B₀ : ℝ := (μ (D.U₀ * D.U₀)).toReal

/-- The additive constant of the bootstrap. -/
def Bc : ℝ := D.m₄ / D.a₀ * D.B₀ * D.c₂

/-- Hypothesis `(13)_M` of Tao, in list form, for `ν_ε`. -/
def H13 (M ε : ℝ) : Prop := ∀ l : List G, escNorm D.U₀ l.prod ≤ M * (l.map (D.ν ε)).sum

theorem a₀_nonneg : 0 ≤ D.a₀ := ENNReal.toReal_nonneg

theorem b₃_nonneg : 0 ≤ D.b₃ := ENNReal.toReal_nonneg

theorem B₀_nonneg : 0 ≤ D.B₀ := ENNReal.toReal_nonneg

theorem Bc_nonneg : 0 ≤ D.Bc := by
  have := D.m₄_nonneg; have := D.a₀_nonneg; have := D.B₀_nonneg; have := D.c₂_nonneg
  unfold Bc; positivity

theorem L_large' : D.m₄ / D.a₀ * D.b₃ / D.L ≤ 1 / 2 := D.L_large

theorem one_mem_S₂ : (1 : G) ∈ D.U₀ * D.U₀ := ⟨1, D.one_mem_U₀, 1, D.one_mem_U₀, one_mul 1⟩

theorem S₂_sub_S₃ : D.U₀ * D.U₀ ⊆ D.U₀ * (D.U₀ * D.U₀) :=
  fun y hy => ⟨1, D.one_mem_U₀, y, hy, one_mul y⟩

theorem U₀_sub_S₂ : D.U₀ ⊆ D.U₀ * D.U₀ := fun y hy => ⟨1, D.one_mem_U₀, y, hy, one_mul y⟩

theorem S₃_sub_S₄ : D.U₀ * (D.U₀ * D.U₀) ⊆ D.U₀ * D.U₀ * (D.U₀ * D.U₀) :=
  Set.mul_subset_mul D.U₀_sub_S₂ subset_rfl

theorem S₂_sub_S₄ : D.U₀ * D.U₀ ⊆ D.U₀ * D.U₀ * (D.U₀ * D.U₀) :=
  D.S₂_sub_S₃.trans D.S₃_sub_S₄

theorem U₀_sub_Ub : D.U₀ ⊆ D.B.Ub := (D.U₀_sub_S₂.trans D.S₂_sub_S₄).trans D.S₄_sub

theorem ν_nonneg {ε : ℝ} (hε : 0 ≤ ε) (g : G) : 0 ≤ D.ν ε g :=
  add_nonneg (escNorm_nonneg _ _) hε

theorem ν_inv (ε : ℝ) (g : G) : D.ν ε g⁻¹ = D.ν ε g := by
  simp only [ν, escNorm_inv D.inv_U₀]

theorem escNorm_le_ν {ε : ℝ} (hε : 0 ≤ ε) (g : G) : escNorm D.U₀ g ≤ D.ν ε g :=
  le_add_of_nonneg_right hε

theorem L_pos' : (0 : ℝ) < D.L := by exact_mod_cast D.L_pos

theorem ν₁_nonneg (g : G) : 0 ≤ D.ν₁ g := by
  unfold ν₁; split_ifs
  · exact inv_nonneg.2 D.L_pos'.le
  · exact zero_le_one

theorem inv_L_le_ν₁ (g : G) : (D.L : ℝ)⁻¹ ≤ D.ν₁ g := by
  unfold ν₁; split_ifs
  · exact le_rfl
  · exact inv_le_one_of_one_le₀ (by exact_mod_cast D.L_pos)

theorem ν₁_of_mem {g : G} (hg : g ∈ D.U₁) : D.ν₁ g = (D.L : ℝ)⁻¹ := by simp [ν₁, hg]

theorem ν₁_of_notMem {g : G} (hg : g ∉ D.U₁) : D.ν₁ g = 1 := by simp [ν₁, hg]

theorem ν₁_inv (g : G) : D.ν₁ g⁻¹ = D.ν₁ g := by
  have : g⁻¹ ∈ D.U₁ ↔ g ∈ D.U₁ := by
    rw [← Set.mem_inv, D.inv_U₁]
  by_cases hg : g ∈ D.U₁
  · rw [D.ν₁_of_mem hg, D.ν₁_of_mem (this.2 hg)]
  · rw [D.ν₁_of_notMem hg, D.ν₁_of_notMem (fun h => hg (this.1 h))]

theorem H13_mono {M M' ε : ℝ} (h : D.H13 M ε) (hMM : M ≤ M') (hε : 0 ≤ ε) : D.H13 M' ε :=
  fun l => (h l).trans (mul_le_mul_of_nonneg_right hMM (sum_map_nonneg (D.ν_nonneg hε) l))

/-- `(13)_{1/ε}` holds: a non-empty factorisation has `Σ ν_ε ≥ ε`. -/
theorem H13_init {ε : ℝ} (hε : 0 < ε) : D.H13 ε⁻¹ ε := by
  intro l
  cases l with
  | nil => simp [escNorm_one D.one_mem_U₀]
  | cons a l =>
    have h1 : ε ≤ ((a :: l).map (D.ν ε)).sum := by
      have := le_sum_map_of_mem (D.ν_nonneg hε.le) (List.mem_cons.2 (Or.inl rfl) : a ∈ a :: l)
      have h3 : ε ≤ D.ν ε a := le_add_of_nonneg_left (escNorm_nonneg _ _)
      linarith
    calc escNorm D.U₀ (a :: l).prod ≤ 1 := escNorm_le_one _ _
      _ = ε⁻¹ * ε := (inv_mul_cancel₀ hε.ne').symm
      _ ≤ ε⁻¹ * ((a :: l).map (D.ν ε)).sum := by gcongr

/-- Support of `ψ` (uses `(13)_M`): `ψ x ≠ 0 → x ∈ U₀²`. -/
theorem mem_S₂_of_ψ_ne_zero {M ε : ℝ} (hM : 0 < M) (hε : 0 ≤ ε) (h13 : D.H13 M ε) {x : G}
    (hx : D.ψ M ε x ≠ 0) : x ∈ D.U₀ * D.U₀ := by
  obtain ⟨l, hl, hs⟩ := exists_of_bump_ne_zero hM (D.ν_nonneg hε) D.one_mem_U₀ hx
  have hp := mem_of_escNorm_lt_one ((h13 l).trans_lt hs)
  have e : x = l.prod * (l.prod⁻¹ * x) := by group
  rw [e]
  exact Set.mul_mem_mul hp hl

/-- Support of `η`: `η x ≠ 0 → x ∈ U₀²`. -/
theorem mem_S₂_of_η_ne_zero {x : G} (hx : D.η x ≠ 0) : x ∈ D.U₀ * D.U₀ := by
  obtain ⟨l, hl, hs⟩ := exists_of_bump_ne_zero one_pos D.ν₁_nonneg D.one_mem_U₀ hx
  rw [one_mul] at hs
  have hall : ∀ h ∈ l, h ∈ D.U₁ := by
    intro h hh
    by_contra hn
    have := le_sum_map_of_mem D.ν₁_nonneg hh
    rw [D.ν₁_of_notMem hn] at this
    linarith
  have hlen : l.length ≤ D.L := by
    have h1 := length_mul_le_sum_map D.inv_L_le_ν₁ l
    have h2 : (l.length : ℝ) * (D.L : ℝ)⁻¹ < 1 := h1.trans_lt hs
    rw [← div_eq_mul_inv, div_lt_one D.L_pos'] at h2
    exact_mod_cast h2.le
  have hp := D.prod_mem l hall hlen
  have e : x = l.prod * (l.prod⁻¹ * x) := by group
  rw [e]
  exact Set.mul_mem_mul hp hl

theorem ψ_eq_zero {M ε : ℝ} (hM : 0 < M) (hε : 0 ≤ ε) (h13 : D.H13 M ε) {x : G}
    (hx : x ∉ D.U₀ * D.U₀) : D.ψ M ε x = 0 := by
  by_contra h; exact hx (D.mem_S₂_of_ψ_ne_zero hM hε h13 h)

theorem η_eq_zero {x : G} (hx : x ∉ D.U₀ * D.U₀) : D.η x = 0 := by
  by_contra h; exact hx (D.mem_S₂_of_η_ne_zero h)

theorem ψ_nonneg (M ε : ℝ) (x : G) : 0 ≤ D.ψ M ε x := bump_nonneg x

theorem η_nonneg (x : G) : 0 ≤ D.η x := bump_nonneg x

theorem abs_ψ_le {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε) (x : G) : |D.ψ M ε x| ≤ 1 :=
  abs_bump_le hM (D.ν_nonneg hε) x

theorem abs_η_le (x : G) : |D.η x| ≤ 1 := abs_bump_le zero_le_one D.ν₁_nonneg x

theorem ψ_eq_one (M : ℝ) {ε : ℝ} (hε : 0 ≤ ε) {x : G} (hx : x ∈ D.U₀) : D.ψ M ε x = 1 :=
  bump_eq_one (D.ν_nonneg hε) hx

theorem η_eq_one {x : G} (hx : x ∈ D.U₀) : D.η x = 1 := bump_eq_one D.ν₁_nonneg hx

/-- Tao (15): `|∂_g ψ| ≤ M ν_ε g`. -/
theorem abs_ldiff_ψ_le {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε) (g x : G) :
    |ldiff g (D.ψ M ε) x| ≤ M * D.ν ε g :=
  abs_ldiff_bump_le hM (D.ν_nonneg hε) (D.ν_inv ε) D.one_mem_U₀ g x

/-- Tao (16): `|∂_k η| ≤ 1/L` for `k ∈ U₁`. -/
theorem abs_ldiff_η_le {k : G} (hk : k ∈ D.U₁) (x : G) : |ldiff k D.η x| ≤ (D.L : ℝ)⁻¹ := by
  have := abs_ldiff_bump_le zero_le_one D.ν₁_nonneg D.ν₁_inv D.one_mem_U₀ k x
  rwa [one_mul, D.ν₁_of_mem hk] at this

end Defs

/-! ## The convolution `φ = ψ ⋆ η` and the bootstrap step -/

section Conv

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure] (D : GleasonData G μ)

omit [IsTopologicalGroup G] [BorelSpace G] in
theorem measure_ne_top {S : Set G} (hS : S ⊆ D.B.Ub) : μ S ≠ ∞ :=
  ((measure_mono (hS.trans subset_closure)).trans_lt
    D.B.isCompact_closure.measure_lt_top).ne

omit [IsTopologicalGroup G] [BorelSpace G] in
theorem a₀_pos : 0 < D.a₀ :=
  ENNReal.toReal_pos (D.isOpen_U₀.measure_pos μ ⟨1, D.one_mem_U₀⟩).ne'
    (D.measure_ne_top D.U₀_sub_Ub)

omit [IsTopologicalGroup G] [BorelSpace G] in
theorem measure_S₂_ne_top : μ (D.U₀ * D.U₀) ≠ ∞ := D.measure_ne_top (D.S₂_sub_S₄.trans D.S₄_sub)

omit [IsTopologicalGroup G] [BorelSpace G] in
theorem measure_S₃_ne_top : μ (D.U₀ * (D.U₀ * D.U₀)) ≠ ∞ :=
  D.measure_ne_top (D.S₃_sub_S₄.trans D.S₄_sub)

omit [μ.IsHaarMeasure] in
theorem measurable_ψ {M ε : ℝ} (hM : 0 < M) (hε : 0 ≤ ε) : Measurable (D.ψ M ε) :=
  measurable_bump hM (D.ν_nonneg hε) D.one_mem_U₀ D.isOpen_U₀

omit [μ.IsHaarMeasure] in
theorem measurable_η : Measurable D.η :=
  measurable_bump one_pos D.ν₁_nonneg D.one_mem_U₀ D.isOpen_U₀

theorem integrable_ψ {M ε : ℝ} (hM : 0 < M) (hε : 0 ≤ ε) (h13 : D.H13 M ε) :
    Integrable (D.ψ M ε) μ :=
  integrable_of_bdd_of_notMem_eq_zero (D.measurable_ψ hM hε) (D.abs_ψ_le hM.le hε)
    D.measure_S₂_ne_top fun _ hy => D.ψ_eq_zero hM hε h13 hy

omit [IsTopologicalGroup G] [BorelSpace G] [μ.IsHaarMeasure] in
theorem φ_nonneg (M ε : ℝ) (x : G) : 0 ≤ D.φ M ε x :=
  conv_nonneg (D.ψ_nonneg M ε) D.η_nonneg x

omit [IsTopologicalGroup G] [BorelSpace G] in
/-- `|φ| ≤ B₀ = μ U₀²`. -/
theorem abs_φ_le {M ε : ℝ} (hM : 0 < M) (hε : 0 ≤ ε) (h13 : D.H13 M ε) (x : G) :
    |D.φ M ε x| ≤ D.B₀ := by
  have := abs_conv_le (μ := μ) (S := D.U₀ * D.U₀) D.measure_S₂_ne_top
    (fun y _ => D.abs_ψ_le hM.le hε y) (fun _ hy => D.ψ_eq_zero hM hε h13 hy) D.abs_η_le x
  rw [one_mul, one_mul] at this
  exact this

omit [IsTopologicalGroup G] [BorelSpace G] [μ.IsHaarMeasure] in
/-- Support of `φ`: `φ x ≠ 0 → x ∈ U₀⁴`. -/
theorem mem_S₄_of_φ_ne_zero {M ε : ℝ} (hM : 0 < M) (hε : 0 ≤ ε) (h13 : D.H13 M ε) {x : G}
    (hx : D.φ M ε x ≠ 0) : x ∈ D.U₀ * D.U₀ * (D.U₀ * D.U₀) :=
  mem_mul_of_conv_ne_zero (fun _ hy => D.mem_S₂_of_ψ_ne_zero hM hε h13 hy)
    (fun _ hy => D.mem_S₂_of_η_ne_zero hy) hx

/-- `φ 1 ≥ μ U₀`. -/
theorem a₀_le_φ_one {M ε : ℝ} (hM : 0 < M) (hε : 0 ≤ ε) (h13 : D.H13 M ε) :
    D.a₀ ≤ D.φ M ε 1 := by
  have := le_conv (μ := μ) (U := D.U₀) (c := 1) D.isOpen_U₀.measurableSet
    (D.integrable_ψ hM hε h13) D.measurable_η D.abs_η_le (D.ψ_nonneg M ε) D.η_nonneg
    (x := 1) fun y hy => by
      have hy' : y⁻¹ ∈ D.U₀ := by rw [← Set.mem_inv, D.inv_U₀]; exact hy
      rw [D.ψ_eq_one M hε hy, mul_one, D.η_eq_one hy', mul_one]
  rw [one_mul] at this
  exact this

/-- **Tao (17).** `‖g‖_{e,U₀} ≤ (m₄ / a₀) ‖g‖_φ`. -/
theorem escNorm_le_tnorm {M ε : ℝ} (hM : 0 < M) (hε : 0 ≤ ε) (h13 : D.H13 M ε) (g : G) :
    escNorm D.U₀ g ≤ D.m₄ / D.a₀ * tnorm (D.φ M ε) g := by
  have hB := D.abs_φ_le hM hε h13
  have ha₀ := D.a₀_pos
  have hs := tnorm_nonneg (D.φ M ε) g
  have key : escNorm (D.U₀ * D.U₀ * (D.U₀ * D.U₀)) g ≤ tnorm (D.φ M ε) g / D.a₀ := by
    rw [escNorm_le_iff (div_nonneg hs ha₀.le)]
    intro i hi hic
    have his : (i : ℝ) * tnorm (D.φ M ε) g < D.a₀ := by
      rw [mul_div_assoc', div_lt_one ha₀] at hic; exact hic
    have h1 : |ldiff (g⁻¹ ^ i) (D.φ M ε) 1| ≤ tnorm (D.φ M ε) (g⁻¹ ^ i) :=
      abs_ldiff_le_tnorm hB _ 1
    have h2 : tnorm (D.φ M ε) (g⁻¹ ^ i) ≤ i * tnorm (D.φ M ε) g⁻¹ := tnorm_pow_le hB _ _
    rw [tnorm_inv hB] at h2
    have h3 : ldiff (g⁻¹ ^ i) (D.φ M ε) 1 = D.φ M ε 1 - D.φ M ε (g ^ i) := by
      simp [ldiff_apply, inv_pow]
    have h4 := D.a₀_le_φ_one hM hε h13
    refine D.mem_S₄_of_φ_ne_zero hM hε h13 fun h0 => ?_
    rw [h3, h0, sub_zero, abs_of_nonneg (D.φ_nonneg M ε 1)] at h1
    linarith
  calc escNorm D.U₀ g ≤ D.m₄ * escNorm (D.U₀ * D.U₀ * (D.U₀ * D.U₀)) g := D.escNorm_le_m₄ g
    _ ≤ D.m₄ * (tnorm (D.φ M ε) g / D.a₀) := by gcongr; exact D.m₄_nonneg
    _ = D.m₄ / D.a₀ * tnorm (D.φ M ε) g := by ring

/-- **Second differences (e).** For `g ∈ U₀` and `k ∈ U₂`,
`|∂_k ∂_g φ| ≤ M ν_ε(g) b₃ / L`. -/
theorem abs_ldiff_ldiff_φ_le {M ε : ℝ} (hM : 0 < M) (hε : 0 ≤ ε) (h13 : D.H13 M ε) {g k : G}
    (hg : g ∈ D.U₀) (hk : k ∈ D.U₂) (x : G) :
    |ldiff k (ldiff g (D.φ M ε)) x| ≤ M * D.ν ε g * (D.L : ℝ)⁻¹ * D.b₃ := by
  have hψi := D.integrable_ψ hM hε h13
  rw [φ, ldiff_ldiff_conv hψi D.measurable_η D.abs_η_le g k x]
  refine abs_integral_le_mul_measure (S := D.U₀ * (D.U₀ * D.U₀)) D.measure_S₃_ne_top
    (fun y hy => ?_) (fun y hy => ?_)
  · rw [abs_mul]
    have := D.ν_nonneg hε g
    exact mul_le_mul (D.abs_ldiff_ψ_le hM.le hε g y) (D.abs_ldiff_η_le (D.conj_mem k hk y hy) _)
      (abs_nonneg _) (by positivity)
  · have h1 : D.ψ M ε y = 0 := D.ψ_eq_zero hM hε h13 fun h => hy (D.S₂_sub_S₃ h)
    have h2 : D.ψ M ε (g⁻¹ * y) = 0 := D.ψ_eq_zero hM hε h13 fun h =>
      hy ⟨g, hg, g⁻¹ * y, h, mul_inv_cancel_left g y⟩
    rw [ldiff_apply, h1, h2, sub_zero, zero_mul]

/-- **Lipschitz bound (f).** `‖g‖_φ ≤ (B₀ c₂ + M b₃ / L) ν_ε(g)`. -/
theorem tnorm_φ_le {M ε : ℝ} (hM : 0 < M) (hε : 0 ≤ ε) (h13 : D.H13 M ε) (g : G) :
    tnorm (D.φ M ε) g ≤ (D.B₀ * D.c₂ + M * D.b₃ / D.L) * D.ν ε g := by
  have hB := D.abs_φ_le hM hε h13
  set c := M * D.ν ε g * (D.L : ℝ)⁻¹ * D.b₃ with hc
  have hc0 : 0 ≤ c := by
    have := D.ν_nonneg hε g; have := D.b₃_nonneg; have := D.L_pos'
    positivity
  have step : tnorm (D.φ M ε) g ≤ D.B₀ * escNorm D.U₂ g + c := by
    refine le_mul_escNorm_add D.B₀_nonneg fun n hn hpow => ?_
    have h := tnorm_pow_ge_of_le hB g n (c := c) fun i hi x => by
      obtain ⟨hi1, hin⟩ := Finset.mem_Ico.1 hi
      have hg1 : g ∈ D.U₂ := by simpa using hpow 1 le_rfl (lt_of_le_of_lt hi1 hin)
      exact D.abs_ldiff_ldiff_φ_le hM hε h13 (D.U₂_sub hg1) (hpow i hi1 hin) x
    have hgn : tnorm (D.φ M ε) (g ^ n) ≤ D.B₀ :=
      tnorm_le_of_nonneg_of_le (D.φ_nonneg M ε) (fun x => (le_abs_self _).trans (hB x)) _
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hcast : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
    have hcn := mul_le_mul_of_nonneg_right hcast hc0
    rw [div_add' _ _ _ hn0.ne', le_div_iff₀ hn0]
    linarith
  have h2 := D.escNorm_le_c₂ g
  have h3 := D.escNorm_le_ν hε g
  have hB₀ := D.B₀_nonneg
  have hc₂ := D.c₂_nonneg
  calc tnorm (D.φ M ε) g ≤ D.B₀ * escNorm D.U₂ g + c := step
    _ ≤ D.B₀ * (D.c₂ * D.ν ε g) + c := by
        gcongr
        exact h2.trans (mul_le_mul_of_nonneg_left h3 hc₂)
    _ = (D.B₀ * D.c₂ + M * D.b₃ / D.L) * D.ν ε g := by rw [hc]; ring

/-- **The bootstrap step (g).** `(13)_M ⇒ (13)_{Bc + M/2}`. -/
theorem bootstrap {M ε : ℝ} (hM : 0 < M) (hε : 0 ≤ ε) (h13 : D.H13 M ε) :
    D.H13 (D.Bc + M / 2) ε := by
  intro l
  have hB := D.abs_φ_le hM hε h13
  have hK : 0 ≤ D.m₄ / D.a₀ := div_nonneg D.m₄_nonneg D.a₀_nonneg
  have hS := sum_map_nonneg (D.ν_nonneg hε) l
  have hcoef : D.m₄ / D.a₀ * (D.B₀ * D.c₂ + M * D.b₃ / D.L) ≤ D.Bc + M / 2 := by
    have e : D.m₄ / D.a₀ * (D.B₀ * D.c₂ + M * D.b₃ / D.L)
        = D.Bc + M * (D.m₄ / D.a₀ * D.b₃ / D.L) := by unfold Bc; ring
    rw [e]
    have := mul_le_mul_of_nonneg_left D.L_large' hM.le
    linarith
  calc escNorm D.U₀ l.prod ≤ D.m₄ / D.a₀ * tnorm (D.φ M ε) l.prod :=
        D.escNorm_le_tnorm hM hε h13 _
    _ ≤ D.m₄ / D.a₀ * (l.map (tnorm (D.φ M ε))).sum := by
        gcongr; exact tnorm_list_prod_le hB l
    _ ≤ D.m₄ / D.a₀ * (l.map fun g => (D.B₀ * D.c₂ + M * D.b₃ / D.L) * D.ν ε g).sum := by
        gcongr; exact List.sum_le_sum fun g _ => D.tnorm_φ_le hM hε h13 g
    _ = D.m₄ / D.a₀ * (D.B₀ * D.c₂ + M * D.b₃ / D.L) * (l.map (D.ν ε)).sum := by
        rw [List.sum_map_mul_left]; ring
    _ ≤ (D.Bc + M / 2) * (l.map (D.ν ε)).sum := by gcongr

/-- Iterating the bootstrap from `(13)_{1/ε}`. -/
theorem H13_iter {ε : ℝ} (hε : 0 < ε) (k : ℕ) : D.H13 (2 * D.Bc + ε⁻¹ / 2 ^ k) ε := by
  induction k with
  | zero =>
    refine D.H13_mono (D.H13_init hε) ?_ hε.le
    simp only [pow_zero, div_one]
    linarith [D.Bc_nonneg]
  | succ k ih =>
    have hM : 0 < 2 * D.Bc + ε⁻¹ / 2 ^ k := by have := D.Bc_nonneg; positivity
    have h := D.bootstrap hM hε.le ih
    have e : D.Bc + (2 * D.Bc + ε⁻¹ / 2 ^ k) / 2 = 2 * D.Bc + ε⁻¹ / 2 ^ (k + 1) := by
      rw [pow_succ]; field_simp; ring
    rw [e] at h
    exact h

theorem H13_final {ε : ℝ} (hε : 0 < ε) : D.H13 (2 * D.Bc + 1) ε := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ε⁻¹ (one_lt_two : (1 : ℝ) < 2)
  refine D.H13_mono (D.H13_iter hε k) ?_ hε.le
  have : ε⁻¹ / 2 ^ k ≤ 1 := by
    rw [div_le_one (by positivity)]; exact hk.le
  linarith

/-- **Tao, Proposition 24** for the data `D`: `‖l.prod‖ ≤ (2 Bc + 1) Σ ‖lᵢ‖`. -/
theorem escNorm_prod_le (l : List G) :
    escNorm D.U₀ l.prod ≤ (2 * D.Bc + 1) * (l.map (escNorm D.U₀)).sum := by
  set K := 2 * D.Bc + 1 with hK
  have hK1 : 1 ≤ K := by linarith [D.Bc_nonneg]
  have hS := sum_map_nonneg (escNorm_nonneg D.U₀) l
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hlen : (0 : ℝ) < l.length + 1 := by positivity
  set ε := δ / (K * (l.length + 1)) with hε
  have hε0 : 0 < ε := by positivity
  have h := D.H13_final hε0 l
  have e : (l.map (D.ν ε)).sum = (l.map (escNorm D.U₀)).sum + l.length * ε :=
    sum_map_add_const (escNorm D.U₀) ε l
  rw [e] at h
  have h2 : K * (l.length * ε) ≤ δ := by
    rw [hε]
    have hKpos : 0 < K := by linarith
    rw [show K * (l.length * (δ / (K * (l.length + 1)))) = δ * (l.length / (l.length + 1)) by
      field_simp]
    have : (l.length : ℝ) / (l.length + 1) ≤ 1 := by
      rw [div_le_one hlen]; linarith
    nlinarith
  nlinarith

end Conv

end GleasonData

/-! ## Construction of the data and the main theorem -/

section Main

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The choices of blueprint H1 exist for every `NSSBase` and every Haar measure. -/
theorem NSSBase.exists_gleasonData [MeasurableSpace G] [BorelSpace G] (B : NSSBase G)
    (μ : Measure G) [μ.IsHaarMeasure] : ∃ D : GleasonData G μ, D.B = B := by
  -- `U₀`: open, symmetric, `U₀⁴ ⊆ Ub`
  obtain ⟨V₁, hV₁o, hV₁1, hV₁⟩ := exists_open_nhds_one_mul_subset B.mem_nhds
  obtain ⟨V₂, hV₂o, hV₂1, hV₂⟩ := exists_open_nhds_one_mul_subset (hV₁o.mem_nhds hV₁1)
  set U₀ : Set G := V₂ ∩ V₂⁻¹ with hU₀
  have hU₀o : IsOpen U₀ := hV₂o.inter hV₂o.inv
  have h1 : (1 : G) ∈ U₀ := ⟨hV₂1, by simpa using hV₂1⟩
  have hinv : U₀⁻¹ = U₀ := by rw [hU₀, Set.inter_inv, inv_inv, Set.inter_comm]
  have hU₀V₂ : U₀ ⊆ V₂ := Set.inter_subset_left
  have hS₂ : U₀ * U₀ ⊆ V₁ := (Set.mul_subset_mul hU₀V₂ hU₀V₂).trans hV₂
  have hS₄ : U₀ * U₀ * (U₀ * U₀) ⊆ B.Ub := (Set.mul_subset_mul hS₂ hS₂).trans hV₁
  have hU₀S₂ : U₀ ⊆ U₀ * U₀ := fun y hy => ⟨1, h1, y, hy, one_mul y⟩
  have h1S₂ : (1 : G) ∈ U₀ * U₀ := ⟨1, h1, 1, h1, one_mul 1⟩
  have hS₂S₄ : U₀ * U₀ ⊆ U₀ * U₀ * (U₀ * U₀) := fun y hy => ⟨1, h1S₂, y, hy, one_mul y⟩
  have hU₀Ub : U₀ ⊆ B.Ub := (hU₀S₂.trans hS₂S₄).trans hS₄
  have hU₀n : U₀ ∈ 𝓝 (1 : G) := hU₀o.mem_nhds h1
  -- the constant `m₄` of (12)
  obtain ⟨m₄, hm₄1, hm₄⟩ := B.escNorm_le hS₄ hU₀n
  -- `L`
  set a₀ := (μ U₀).toReal with ha₀
  set b₃ := (μ (U₀ * (U₀ * U₀))).toReal with hb₃
  have hb₃0 : 0 ≤ b₃ := ENNReal.toReal_nonneg
  have ha₀0 : 0 ≤ a₀ := ENNReal.toReal_nonneg
  set L : ℕ := ⌈2 * (m₄ / a₀ * b₃)⌉₊ + 1 with hL
  have hLpos : 0 < L := Nat.succ_pos _
  have hLlarge : m₄ / a₀ * b₃ / L ≤ 1 / 2 := by
    have hL0 : (0 : ℝ) < L := by exact_mod_cast hLpos
    have : 2 * (m₄ / a₀ * b₃) ≤ L := (Nat.le_ceil _).trans (by rw [hL]; push_cast; linarith)
    rw [div_le_iff₀ hL0]
    linarith
  -- `U₁`
  obtain ⟨W, hW, hWprod⟩ := exists_nhds_list_prod_mem L hU₀n
  set U₁ : Set G := W ∩ W⁻¹ with hU₁
  have hU₁n : U₁ ∈ 𝓝 (1 : G) := inter_mem hW (inv_mem_nhds_one G hW)
  have hU₁inv : U₁⁻¹ = U₁ := by rw [hU₁, Set.inter_inv, inv_inv, Set.inter_comm]
  -- `U₂`: conjugation by `closure Ub` maps `U₂` into `U₁`
  have hev : ∀ᶠ k in 𝓝 (1 : G), ∀ y ∈ closure B.Ub, y⁻¹ * k * y ∈ U₁ := by
    refine B.isCompact_closure.eventually_forall_of_forall_eventually fun y _ => ?_
    have hc : Continuous fun z : G × G => z.2⁻¹ * z.1 * z.2 := by fun_prop
    have ht : Tendsto (fun z : G × G => z.2⁻¹ * z.1 * z.2) (𝓝 (1, y)) (𝓝 1) := by
      simpa using hc.tendsto (1, y)
    exact ht hU₁n
  set U₂ : Set G := {k | ∀ y ∈ closure B.Ub, y⁻¹ * k * y ∈ U₁} ∩ U₀ with hU₂
  have hU₂n : U₂ ∈ 𝓝 (1 : G) := inter_mem hev hU₀n
  obtain ⟨c₂, hc₂1, hc₂⟩ := B.escNorm_le hU₀Ub hU₂n
  have hS₃Ub : U₀ * (U₀ * U₀) ⊆ B.Ub :=
    (Set.mul_subset_mul hU₀S₂ subset_rfl).trans hS₄
  exact ⟨{
    B := B
    U₀ := U₀
    U₁ := U₁
    U₂ := U₂
    L := L
    m₄ := m₄
    c₂ := c₂
    isOpen_U₀ := hU₀o
    one_mem_U₀ := h1
    inv_U₀ := hinv
    S₄_sub := hS₄
    L_pos := hLpos
    inv_U₁ := hU₁inv
    prod_mem := fun l hl hlen => hWprod l (fun h hh => (hl h hh).1) hlen
    U₂_sub := Set.inter_subset_right
    conj_mem := fun k hk y hy => hk.1 y (subset_closure (hS₃Ub hy))
    m₄_nonneg := by linarith
    escNorm_le_m₄ := hm₄
    c₂_nonneg := by linarith
    escNorm_le_c₂ := hc₂
    L_large := hLlarge }, rfl⟩

/-- **Gleason's lemma (Tao 254A Notes 4, Proposition 24).** For an `NSSBase` of a locally compact
group there is an open symmetric neighbourhood `U₀` of `1` with `U₀⁴ ⊆ Ub` such that the escape
norm `‖·‖_{e,U₀}` satisfies the approximate triangle inequality
`‖g₁ ⋯ gₙ‖_{e,U₀} ≤ K₀ Σ ‖gᵢ‖_{e,U₀}`. -/
theorem NSSBase.exists_escNorm_prod_le [LocallyCompactSpace G] (B : NSSBase G) :
    ∃ U₀ : Set G, IsOpen U₀ ∧ (1 : G) ∈ U₀ ∧ U₀⁻¹ = U₀ ∧ U₀ ^ 4 ⊆ B.Ub ∧
      ∃ K₀ : ℝ, 1 ≤ K₀ ∧ ∀ l : List G, escNorm U₀ l.prod ≤ K₀ * (l.map (escNorm U₀)).sum := by
  borelize G
  obtain ⟨D, rfl⟩ := B.exists_gleasonData (Measure.haar : Measure G)
  refine ⟨D.U₀, D.isOpen_U₀, D.one_mem_U₀, D.inv_U₀, ?_, 2 * D.Bc + 1,
    by linarith [D.Bc_nonneg], D.escNorm_prod_le⟩
  have : D.U₀ ^ 4 = D.U₀ * D.U₀ * (D.U₀ * D.U₀) := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [this]
  exact D.S₄_sub

end Main

end HSFormal.GY
