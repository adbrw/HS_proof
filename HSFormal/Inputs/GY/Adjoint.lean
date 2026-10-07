import HSFormal.Inputs.GY.Defs
import TauCeti.Geometry.Lie.Exponential.Classification
import TauCeti.Geometry.Lie.Exponential.Trotter
import TauCeti.Geometry.Lie.Exponential.Units.Compatibility

/-!
# The adjoint action of a local exponential structure (blueprint C1)

Let `S : LocalExpStructure G E`. The field `S.conj g` says that conjugation by `g` acts linearly in
exponential coordinates; by `LocalExpStructure.clm_ext` the linear map is unique. This file
packages it as a group homomorphism and proves the Hadamard formula.

* `LocalExpStructure.Ad : G →* (E →L[ℝ] E)ˣ` with `Ad_spec : g * exp X * g⁻¹ = exp (Ad g X)`.
* `LocalExpStructure.continuous_Ad` (norm topology on `E →L[ℝ] E`) and
  `LocalExpStructure.continuous_Ad_units`, for a topological group `G` and finite-dimensional `E`.
* `LocalExpStructure.ad : E →L[ℝ] (E →L[ℝ] E)` and the Hadamard formula
  `Ad_exp_smul : Ad (exp (t • X)) = NormedSpace.exp (t • ad X)` (`Ad_exp` at `t = 1`).

Proof of the Hadamard formula (blueprint §4 C1): `t ↦ Ad (exp (t • X))` is a continuous
one-parameter subgroup of `GL(E) = (E →L[ℝ] E)ˣ`. TauCeti's classification of the continuous
one-parameter subgroups of a finite-dimensional Lie group
(`exists_eq_mulInvariantOneParameterSubgroup`), together with
`mulInvariantOneParameterSubgroup_eq_expUnitHom`, writes it as `t ↦ exp (t • a)`, and `a` is
unique (`TauCeti.eq_of_forall_exp_smul_eq`). Homogeneity of `X ↦ a` follows from uniqueness, and
additivity from the Trotter formula of `S` (`LocalExpStructure.trotter`), the continuity of `Ad`
and TauCeti's Trotter formula on `GL(E)`
(`tendsto_mulInvariantExp_smul_mul_mulInvariantExp_smul_pow`).

Deviation from the blueprint: TauCeti's classification is used in its tangent-vector form
(`exists_eq_mulInvariantOneParameterSubgroup`, `tendsto_mulInvariantExp_…`) rather than through
left-invariant derivations; this avoids `unitsLieAlgebraEquiv`.
-/

noncomputable section

namespace HSFormal.GY

open Filter Topology Manifold
open scoped ContDiff Manifold

namespace LocalExpStructure

variable {G : Type*} [Group G] [TopologicalSpace G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (S : LocalExpStructure G E)

/-! ### The adjoint representation -/

/-- The (unique) continuous linear map of `S.conj g`. -/
def AdAux (g : G) : E →L[ℝ] E := Classical.choose (S.conj g)

theorem AdAux_spec (g : G) (X : E) : g * S.exp X * g⁻¹ = S.exp (S.AdAux g X) :=
  Classical.choose_spec (S.conj g) X

theorem AdAux_eq {g : G} {A : E →L[ℝ] E} (hA : ∀ X, g * S.exp X * g⁻¹ = S.exp (A X)) :
    S.AdAux g = A :=
  S.clm_ext fun X => by rw [← AdAux_spec, hA]

theorem AdAux_one : S.AdAux 1 = 1 :=
  S.AdAux_eq fun X => by simp

theorem AdAux_mul (g h : G) : S.AdAux (g * h) = S.AdAux g * S.AdAux h :=
  S.AdAux_eq fun X => by
    rw [mul_apply_eq_comp, ← AdAux_spec, ← AdAux_spec]
    group

/-- `Ad` as a monoid homomorphism into `E →L[ℝ] E`. -/
def AdHom : G →* (E →L[ℝ] E) where
  toFun := S.AdAux
  map_one' := S.AdAux_one
  map_mul' := S.AdAux_mul

/-- The adjoint representation `Ad : G →* GL(E)`: `g * exp X * g⁻¹ = exp (Ad g X)`. -/
def Ad : G →* (E →L[ℝ] E)ˣ := S.AdHom.toHomUnits

@[simp] theorem coe_Ad (g : G) : (S.Ad g : E →L[ℝ] E) = S.AdAux g := rfl

theorem coe_Ad_inv (g : G) : ((S.Ad g)⁻¹ : (E →L[ℝ] E)ˣ) = S.Ad g⁻¹ := (map_inv S.Ad g).symm

theorem Ad_spec (g : G) (X : E) : g * S.exp X * g⁻¹ = S.exp ((S.Ad g : E →L[ℝ] E) X) :=
  S.AdAux_spec g X

/-- `Ad g` is characterised by `Ad_spec`. -/
theorem Ad_eq {g : G} {A : E →L[ℝ] E} (hA : ∀ X, g * S.exp X * g⁻¹ = S.exp (A X)) :
    (S.Ad g : E →L[ℝ] E) = A :=
  S.AdAux_eq hA

theorem Ad_mul_apply (g h : G) (X : E) :
    (S.Ad (g * h) : E →L[ℝ] E) X = (S.Ad g : E →L[ℝ] E) ((S.Ad h : E →L[ℝ] E) X) := by
  rw [map_mul, Units.val_mul, mul_apply_eq_comp]

/-! ### Continuity of `Ad` -/

section Continuity

variable [IsTopologicalGroup G]

/-- Near `1`, `Ad g Y = log (g * exp Y * g⁻¹)` for a fixed `Y` whose ray `[0, 1] • Y` lies in the
chart source; hence `Ad g Y → Y` as `g → 1`. -/
theorem tendsto_Ad_apply_of_forall_mem_source {Y : E}
    (hY : ∀ s ∈ Set.Icc (0 : ℝ) 1, s • Y ∈ S.chart.source) :
    Tendsto (fun g => (S.Ad g : E →L[ℝ] E) Y) (𝓝 1) (𝓝 Y) := by
  have hcont : Continuous fun p : G × ℝ => p.1 * S.exp (p.2 • Y) * p.1⁻¹ := by
    have : Continuous fun p : G × ℝ => S.exp (p.2 • Y) :=
      S.continuous_exp.comp (continuous_snd.smul continuous_const)
    exact (continuous_fst.mul this).mul continuous_fst.inv
  have hev : ∀ᶠ g in 𝓝 (1 : G), ∀ s ∈ Set.Icc (0 : ℝ) 1,
      g * S.exp (s • Y) * g⁻¹ ∈ S.chart.target := by
    refine isCompact_Icc.eventually_forall_of_forall_eventually fun s hs => ?_
    have hmem : (1 : G) * S.exp (s • Y) * (1 : G)⁻¹ ∈ S.chart.target := by
      simpa using S.exp_mem_target (hY s hs)
    exact hcont.continuousAt.preimage_mem_nhds (S.chart.open_target.mem_nhds hmem)
  have heq : ∀ᶠ g in 𝓝 (1 : G),
      S.chart.symm (g * S.exp Y * g⁻¹) = (S.Ad g : E →L[ℝ] E) Y := by
    filter_upwards [hev] with g hg
    rw [Ad_spec]
    refine S.symm_exp_of_forall_mem_target fun s hs => ?_
    rw [← map_smul, ← Ad_spec]
    exact hg s hs
  have hY1 : S.exp Y ∈ S.chart.target :=
    S.exp_mem_target (by simpa using hY 1 ⟨zero_le_one, le_rfl⟩)
  have hlim : Tendsto (fun g : G => g * S.exp Y * g⁻¹) (𝓝 1) (𝓝 (S.exp Y)) := by
    have : Continuous fun g : G => g * S.exp Y * g⁻¹ := by fun_prop
    simpa using this.tendsto (1 : G)
  have h2 := (S.chart.continuousAt_symm hY1).tendsto.comp hlim
  rw [S.symm_exp (by simpa using hY 1 ⟨zero_le_one, le_rfl⟩)] at h2
  exact h2.congr' heq

theorem tendsto_Ad_apply_one (X : E) :
    Tendsto (fun g => (S.Ad g : E →L[ℝ] E) X) (𝓝 1) (𝓝 X) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 S.source_mem_nhds
  set c : ℝ := r / (2 * (‖X‖ + 1)) with hc_def
  have hc : 0 < c := by positivity
  have hcX : ‖c • X‖ < r := by
    rw [norm_smul, Real.norm_of_nonneg hc.le]
    calc c * ‖X‖ < c * (‖X‖ + 1) := by gcongr; linarith
      _ = r / 2 := by rw [hc_def]; field_simp
      _ < r := half_lt_self hr
  have hY : ∀ s ∈ Set.Icc (0 : ℝ) 1, s • (c • X) ∈ S.chart.source := by
    intro s hs
    apply hball
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg hs.1]
    calc s * ‖c • X‖ ≤ 1 * ‖c • X‖ := by gcongr; exact hs.2
      _ < r := by rwa [one_mul]
  have h := (S.tendsto_Ad_apply_of_forall_mem_source hY).const_smul c⁻¹
  simp only [map_smul, smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at h
  exact h

theorem continuous_Ad_apply (X : E) : Continuous fun g => (S.Ad g : E →L[ℝ] E) X := by
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  have h1 : Tendsto (fun g : G => g₀⁻¹ * g) (𝓝 g₀) (𝓝 1) := by
    have : Continuous fun g : G => g₀⁻¹ * g := by fun_prop
    simpa using this.tendsto g₀
  have h2 := ((S.Ad g₀ : E →L[ℝ] E).continuous.tendsto X).comp
    ((S.tendsto_Ad_apply_one X).comp h1)
  refine h2.congr fun g => ?_
  simp only [Function.comp_apply]
  rw [← Ad_mul_apply, mul_inv_cancel_left]

variable [FiniteDimensional ℝ E]

/-- `Ad` is continuous for the norm topology of `E →L[ℝ] E`. -/
theorem continuous_Ad : Continuous fun g => (S.Ad g : E →L[ℝ] E) :=
  continuous_clm_apply.2 S.continuous_Ad_apply

/-- `Ad` is continuous as a map into the topological group `GL(E)`. -/
theorem continuous_Ad_units : Continuous S.Ad := by
  refine Units.continuous_iff.2 ⟨S.continuous_Ad, ?_⟩
  have : (fun g => ((S.Ad g)⁻¹ : (E →L[ℝ] E)ˣ).val) = fun g => (S.Ad g⁻¹ : E →L[ℝ] E) := by
    funext g; rw [coe_Ad_inv]
  rw [this]
  exact S.continuous_Ad.comp continuous_inv

end Continuity

/-! ### The Hadamard formula `Ad (exp X) = exp (ad X)` -/

section Hadamard

variable [IsTopologicalGroup G] [FiniteDimensional ℝ E]

attribute [local instance] TauCeti.normedAlgebraRatOfReal

local instance completeSpaceOfFD : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The continuous one-parameter subgroup `t ↦ Ad (exp (t • X))` of `GL(E)`. -/
def AdLine (X : E) : ContinuousMonoidHom (Multiplicative ℝ) (E →L[ℝ] E)ˣ where
  toFun t := S.Ad (S.exp (Multiplicative.toAdd t • X))
  map_one' := by simp
  map_mul' s t := by simp only [toAdd_mul, S.exp_add_smul, map_mul]
  continuous_toFun :=
    S.continuous_Ad_units.comp (S.continuous_exp.comp (continuous_toAdd.smul continuous_const))

theorem exists_Ad_exp_smul (X : E) :
    ∃ a : E →L[ℝ] E, ∀ t : ℝ, (S.Ad (S.exp (t • X)) : E →L[ℝ] E) = NormedSpace.exp (t • a) := by
  obtain ⟨v, hv⟩ := exists_eq_mulInvariantOneParameterSubgroup
    (I := 𝓘(ℝ, E →L[ℝ] E)) (G := (E →L[ℝ] E)ˣ) (S.AdLine X)
  let a : E →L[ℝ] E := v
  have h := hv.trans (mulInvariantOneParameterSubgroup_eq_expUnitHom a)
  refine ⟨a, fun t => ?_⟩
  have := congrArg (fun φ : ContinuousMonoidHom (Multiplicative ℝ) (E →L[ℝ] E)ˣ =>
    (φ (Multiplicative.ofAdd t) : E →L[ℝ] E)) h
  simp only [TauCeti.expUnitHom_apply, TauCeti.expUnit_coe] at this
  exact this

/-- The generator `ad X` of `t ↦ Ad (exp (t • X))` (before bundling as a linear map). -/
def adFun (X : E) : E →L[ℝ] E := Classical.choose (S.exists_Ad_exp_smul X)

theorem Ad_exp_smul_adFun (X : E) (t : ℝ) :
    (S.Ad (S.exp (t • X)) : E →L[ℝ] E) = NormedSpace.exp (t • S.adFun X) :=
  Classical.choose_spec (S.exists_Ad_exp_smul X) t

theorem adFun_eq {X : E} {a : E →L[ℝ] E}
    (ha : ∀ t : ℝ, (S.Ad (S.exp (t • X)) : E →L[ℝ] E) = NormedSpace.exp (t • a)) :
    S.adFun X = a :=
  TauCeti.eq_of_forall_exp_smul_eq fun t => by rw [← Ad_exp_smul_adFun, ha]

theorem adFun_smul (c : ℝ) (X : E) : S.adFun (c • X) = c • S.adFun X :=
  S.adFun_eq fun t => by rw [smul_smul, Ad_exp_smul_adFun, smul_smul]

/-- `Ad ∘ exp` along a ray, as units: `Ad (exp (t • X)) = expUnit (t • ad X)`. -/
theorem Ad_exp_smul_eq_expUnit (X : E) (t : ℝ) :
    S.Ad (S.exp (t • X)) = TauCeti.expUnit (t • S.adFun X) :=
  Units.ext (by rw [TauCeti.expUnit_coe, Ad_exp_smul_adFun])

/-- Trotter's formula on `GL(E)` (TauCeti), for the Banach-algebra exponential. -/
theorem _root_.HSFormal.GY.tendsto_expUnit_trotter (a b : E →L[ℝ] E) (t : ℝ) :
    Tendsto (fun n : ℕ => (TauCeti.expUnit ((t / n) • a) * TauCeti.expUnit ((t / n) • b)) ^ n)
      atTop (𝓝 (TauCeti.expUnit (t • (a + b)))) := by
  have h := tendsto_mulInvariantExp_smul_mul_mulInvariantExp_smul_pow
    (I := 𝓘(ℝ, E →L[ℝ] E)) (G := (E →L[ℝ] E)ˣ) a b t
  have hexp : ∀ v : E →L[ℝ] E,
      mulInvariantExp (I := 𝓘(ℝ, E →L[ℝ] E)) (G := (E →L[ℝ] E)ˣ) v = TauCeti.expUnit v := by
    intro v
    have := congrArg (fun φ : ContinuousMonoidHom (Multiplicative ℝ) (E →L[ℝ] E)ˣ =>
      φ (Multiplicative.ofAdd 1)) (mulInvariantOneParameterSubgroup_eq_expUnitHom v)
    simp only [TauCeti.expUnitHom_apply, one_smul] at this
    exact this
  convert h using 4 with n
  · exact (hexp _).symm
  · exact (hexp _).symm
  · exact (hexp _).symm

theorem adFun_add (X Y : E) : S.adFun (X + Y) = S.adFun X + S.adFun Y := by
  refine S.adFun_eq fun t => ?_
  -- Trotter in `G`, pushed forward by the continuous homomorphism `Ad`.
  have h1 := (S.continuous_Ad_units.tendsto _).comp (S.trotter (t • X) (t • Y))
  have h2 := tendsto_expUnit_trotter (S.adFun X) (S.adFun Y) t
  have heq : (fun n : ℕ => (TauCeti.expUnit ((t / n) • S.adFun X) *
      TauCeti.expUnit ((t / n) • S.adFun Y)) ^ n) =
      S.Ad ∘ fun n : ℕ => (S.exp ((n : ℝ)⁻¹ • t • X) * S.exp ((n : ℝ)⁻¹ • t • Y)) ^ n := by
    funext n
    simp only [Function.comp_apply, map_pow, map_mul, smul_smul, Ad_exp_smul_eq_expUnit]
    rw [div_eq_inv_mul]
  rw [heq] at h2
  have := tendsto_nhds_unique h1 h2
  rw [smul_add, this, TauCeti.expUnit_coe]

/-- The infinitesimal adjoint action `ad : E →L[ℝ] (E →L[ℝ] E)`, the generator of
`t ↦ Ad (exp (t • X))`. -/
def ad : E →L[ℝ] (E →L[ℝ] E) :=
  LinearMap.toContinuousLinearMap
    { toFun := S.adFun
      map_add' := S.adFun_add
      map_smul' := S.adFun_smul }

theorem ad_apply (X : E) : S.ad X = S.adFun X := rfl

/-- **Hadamard formula** along rays: `Ad (exp (t • X)) = exp (t • ad X)`. -/
theorem Ad_exp_smul (X : E) (t : ℝ) :
    (S.Ad (S.exp (t • X)) : E →L[ℝ] E) = NormedSpace.exp (t • S.ad X) :=
  S.Ad_exp_smul_adFun X t

/-- **Hadamard formula** `Ad (exp X) = exp (ad X)`. -/
theorem Ad_exp (X : E) : (S.Ad (S.exp X) : E →L[ℝ] E) = NormedSpace.exp (S.ad X) := by
  simpa using S.Ad_exp_smul X 1

/-- `ad X` is the unique generator of `t ↦ Ad (exp (t • X))`. -/
theorem ad_eq {X : E} {a : E →L[ℝ] E}
    (ha : ∀ t : ℝ, (S.Ad (S.exp (t • X)) : E →L[ℝ] E) = NormedSpace.exp (t • a)) : S.ad X = a :=
  S.adFun_eq ha

/-- Conjugation by `exp X` in exponential coordinates:
`exp X * exp Y * exp (-X) = exp (e^{ad X} Y)`. -/
theorem exp_mul_exp_mul_exp_neg (X Y : E) :
    S.exp X * S.exp Y * S.exp (-X) = S.exp (NormedSpace.exp (S.ad X) Y) := by
  rw [exp_neg, Ad_spec, Ad_exp]

end Hadamard

end LocalExpStructure

end HSFormal.GY
