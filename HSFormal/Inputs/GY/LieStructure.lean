import HSFormal.Inputs.GY.Defs
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Instances.Real

/-!
# A Lie group structure from a local exponential structure (blueprint C4)

Let `S : LocalExpStructure G E` on a topological group `G` with `μ X Y = S.mu X Y` smooth near
`(0, 0)` (`hμ : S.ContDiffMu`, the conclusion of C3). Then `G` is a `C^∞` Lie group modelled on `E`
for its **given** topology:

* `LocalExpStructure.logChart r`: `log = chart.symm` restricted to `exp (ball 0 r)`;
* `LocalExpStructure.leftChart r g`: the left translate `x ↦ log (g⁻¹ * x)`;
* `LocalExpStructure.expChartedSpace r hr : ChartedSpace E G` with atlas `range (leftChart r)`;
* `LocalExpStructure.lieGroup_expChartedSpace`: with `r = ρ` from `hμ`, this charted space makes `G`
  a Lie group;
* `LocalExpStructure.isLieGroup : IsLieGroup G` for `E = EuclideanSpace ℝ (Fin d)`.

Proof.
* Transitions: `(leftChart g).symm ≫ₕ leftChart h` is `X ↦ log (k * exp X)` with `k = h⁻¹ g`. Near a
  point `X₀` of its source, with `exp Y₀ = k exp X₀`, it equals `μ (Y₀, μ (-X₀, X))` (pure algebra:
  `k exp X = exp Y₀ * (exp (-X₀) * exp X)`), which is `C^∞` (`contDiffAt_log_mul_exp`).
* Multiplication: in the charts at `(g, h)` and `g h` it is `(X, Y) ↦ μ (Ad_{h⁻¹} X, Y)`, by
  `h⁻¹ exp X h = exp (Ad_{h⁻¹} X)` (the field `conj`); smooth at `(0, 0)`.
* Inversion: in the charts at `g` and `g⁻¹` it is `X ↦ log (exp (-(Ad_g X)))`, which equals the
  linear map `-Ad_g` near `0`.
-/

noncomputable section

namespace HSFormal.GY

open Filter Topology Metric Manifold
open scoped ContDiff Manifold

namespace LocalExpStructure

variable {G : Type*} [Group G] [TopologicalSpace G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (S : LocalExpStructure G E)

/-! ### The charts -/

/-- The logarithm `chart.symm`, restricted to `exp (ball 0 r)`. -/
def logChart (r : ℝ) : OpenPartialHomeomorph G E :=
  (S.chart.restrOpen (ball (0 : E) r) isOpen_ball).symm

theorem coe_logChart (r : ℝ) : ⇑(S.logChart r) = S.chart.symm := rfl

theorem coe_logChart_symm (r : ℝ) : ⇑(S.logChart r).symm = S.exp := by
  rw [← S.chart_coe]; rfl

theorem logChart_source (r : ℝ) :
    (S.logChart r).source = S.chart.target ∩ S.chart.symm ⁻¹' ball 0 r := rfl

theorem logChart_target (r : ℝ) : (S.logChart r).target = S.chart.source ∩ ball 0 r := rfl

theorem one_mem_logChart_source {r : ℝ} (hr : 0 < r) : (1 : G) ∈ (S.logChart r).source :=
  ⟨S.one_mem_target, by simp [hr]⟩

variable [IsTopologicalGroup G]

/-- The chart at `g`: `x ↦ log (g⁻¹ * x)` on `g * exp (ball 0 r)`. -/
def leftChart (r : ℝ) (g : G) : OpenPartialHomeomorph G E :=
  (Homeomorph.mulLeft g⁻¹).toOpenPartialHomeomorph.trans (S.logChart r)

theorem leftChart_apply (r : ℝ) (g x : G) : S.leftChart r g x = S.chart.symm (g⁻¹ * x) := rfl

theorem leftChart_symm_apply (r : ℝ) (g : G) (X : E) :
    (S.leftChart r g).symm X = g * S.exp X := by
  show (Homeomorph.mulLeft g⁻¹).symm ((S.logChart r).symm X) = g * S.exp X
  rw [Homeomorph.mulLeft_symm, Homeomorph.coe_mulLeft, inv_inv, coe_logChart_symm]

theorem coe_leftChart_symm (r : ℝ) (g : G) : ⇑(S.leftChart r g).symm = fun X => g * S.exp X :=
  funext (S.leftChart_symm_apply r g)

theorem mem_leftChart_source {r : ℝ} {g x : G} :
    x ∈ (S.leftChart r g).source ↔ g⁻¹ * x ∈ (S.logChart r).source := by
  simp [leftChart]

theorem leftChart_target (r : ℝ) (g : G) :
    (S.leftChart r g).target = (S.logChart r).target := by
  simp [leftChart]

/-- The charted space on `G` (for its given topology) made of the left translates of the
exponential chart restricted to `ball 0 r`. -/
@[instance_reducible]
def expChartedSpace (r : ℝ) (hr : 0 < r) : ChartedSpace E G where
  atlas := Set.range (S.leftChart r)
  chartAt := S.leftChart r
  mem_chart_source g := by
    rw [mem_leftChart_source, inv_mul_cancel]; exact S.one_mem_logChart_source hr
  chart_mem_atlas g := ⟨g, rfl⟩

/-! ### Smoothness of the transition maps -/

omit [IsTopologicalGroup G] in
theorem mu_neg_self' (W : E) : S.mu (-W) W = 0 := by
  rw [mu_def, exp_neg, inv_mul_cancel, symm_one]

section Smooth

variable {ρ : ℝ}
  (hμ : ContDiffOn ℝ ∞ (fun p : E × E => S.mu p.1 p.2) (ball 0 ρ ×ˢ ball 0 ρ))
  (htar : ∀ X Y : E, ‖X‖ < ρ → ‖Y‖ < ρ → S.exp X * S.exp Y ∈ S.chart.target)
include hμ htar

omit [IsTopologicalGroup G] in
/-- **Smooth left translations in exponential coordinates**: if `k * exp X₀ = exp Y₀` with
`X₀, Y₀ ∈ ball 0 ρ`, then `X ↦ log (k * exp X)` is `C^∞` at `X₀` (it is `μ (Y₀, μ (-X₀, X))`). -/
theorem contDiffAt_log_mul_exp (k : G) {X₀ Y₀ : E} (hX₀ : ‖X₀‖ < ρ) (hY₀ : ‖Y₀‖ < ρ)
    (hk : k * S.exp X₀ = S.exp Y₀) :
    ContDiffAt ℝ ∞ (fun X => S.chart.symm (k * S.exp X)) X₀ := by
  have hΩ : IsOpen (ball (0 : E) ρ ×ˢ ball (0 : E) ρ) := isOpen_ball.prod isOpen_ball
  have heq : (fun X => S.mu Y₀ (S.mu (-X₀) X)) =ᶠ[𝓝 X₀] fun X => S.chart.symm (k * S.exp X) := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hX₀)] with X hX
    rw [mem_ball_zero_iff] at hX
    have h1 := S.exp_mu (htar (-X₀) X (by simpa using hX₀) hX)
    rw [S.mu_def Y₀, h1, ← hk, exp_neg]
    congr 1
    group
  have h1 : ContDiffAt ℝ ∞ (fun X => S.mu (-X₀) X) X₀ := by
    have h := (hμ.contDiffAt (hΩ.mem_nhds (show ((-X₀, X₀) : E × E) ∈ _ from
      ⟨by simpa using hX₀, by simpa using hX₀⟩))).comp X₀
      (contDiffAt_const.prodMk contDiffAt_id)
    exact h
  have h2 : ContDiffAt ℝ ∞ (fun X => S.mu Y₀ (S.mu (-X₀) X)) X₀ := by
    have hmem : ((Y₀, S.mu (-X₀) X₀) : E × E) ∈ ball (0 : E) ρ ×ˢ ball (0 : E) ρ := by
      rw [S.mu_neg_self']
      exact ⟨mem_ball_zero_iff.2 hY₀, mem_ball_self (lt_of_le_of_lt (norm_nonneg _) hX₀)⟩
    have h := (hμ.contDiffAt (hΩ.mem_nhds hmem)).comp X₀ (contDiffAt_const.prodMk h1)
    exact h
  exact h2.congr_of_eventuallyEq heq.symm

/-- The transition maps of `expChartedSpace ρ` are `C^∞`. -/
theorem isManifold_expChartedSpace (hρ : 0 < ρ) :
    letI := S.expChartedSpace ρ hρ
    IsManifold 𝓘(ℝ, E) ∞ G := by
  let _ := S.expChartedSpace ρ hρ
  apply isManifold_of_contDiffOn
  rintro e e' ⟨g, rfl⟩ ⟨h, rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id,
    Set.preimage_id, Set.inter_univ, Function.id_comp, Function.comp_id]
  intro X₀ hX₀
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hX₀
  obtain ⟨hX₀t, hX₀s⟩ := hX₀
  rw [leftChart_target, logChart_target] at hX₀t
  rw [Set.mem_preimage, mem_leftChart_source, leftChart_symm_apply, logChart_source] at hX₀s
  obtain ⟨hmemt, hY₀⟩ := hX₀s
  have hfun : ⇑((S.leftChart ρ g).symm.trans (S.leftChart ρ h)) =
      fun X => S.chart.symm ((h⁻¹ * g) * S.exp X) := by
    funext X
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, leftChart_symm_apply,
      leftChart_apply, mul_assoc]
  rw [hfun]
  refine (S.contDiffAt_log_mul_exp hμ htar (h⁻¹ * g) (mem_ball_zero_iff.1 hX₀t.2)
    (Y₀ := S.chart.symm (h⁻¹ * (g * S.exp X₀))) (mem_ball_zero_iff.1 hY₀) ?_).contDiffWithinAt
  rw [S.exp_symm hmemt, mul_assoc]

/-! ### Smoothness of multiplication and inversion -/

omit htar in
/-- In the charts at `(g, h)` and `g * h`, multiplication is `(X, Y) ↦ μ (Ad_{h⁻¹} X, Y)`. -/
theorem contMDiff_mul_expChartedSpace (hρ : 0 < ρ) :
    letI := S.expChartedSpace ρ hρ
    ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ fun p : G × G => p.1 * p.2 := by
  let _ := S.expChartedSpace ρ hρ
  rintro ⟨g, h⟩
  rw [contMDiffAt_iff]
  refine ⟨continuous_mul.continuousAt, ?_⟩
  obtain ⟨A, hA⟩ := S.conj h⁻¹
  have hF : (extChartAt 𝓘(ℝ, E) ((g, h).1 * (g, h).2) ∘ (fun p : G × G => p.1 * p.2) ∘
      (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E)) (g, h)).symm) = fun q : E × E => S.mu (A q.1) q.2 := by
    funext q
    simp only [Function.comp_apply, extChartAt_prod, PartialEquiv.prod_symm,
      PartialEquiv.prod_coe, extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.id_comp]
    show S.leftChart ρ (g * h) ((S.leftChart ρ g).symm q.1 * (S.leftChart ρ h).symm q.2) = _
    rw [leftChart_apply, leftChart_symm_apply, leftChart_symm_apply, mu_def, ← hA q.1, inv_inv]
    congr 1
    group
  have hpt : extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E)) (g, h) (g, h) = (0, 0) := by
    simp only [extChartAt_prod, PartialEquiv.prod_coe, extChartAt_coe, modelWithCornersSelf_coe,
      Function.id_comp]
    show (S.leftChart ρ g g, S.leftChart ρ h h) = (0, 0)
    rw [leftChart_apply, leftChart_apply, inv_mul_cancel, inv_mul_cancel, symm_one]
  rw [hF, hpt]
  refine ContDiffAt.contDiffWithinAt ?_
  have hΩ : IsOpen (ball (0 : E) ρ ×ˢ ball (0 : E) ρ) := isOpen_ball.prod isOpen_ball
  have hmem : ((A 0, 0) : E × E) ∈ ball (0 : E) ρ ×ˢ ball (0 : E) ρ := by
    rw [map_zero]; exact ⟨mem_ball_self hρ, mem_ball_self hρ⟩
  have hc := (hμ.contDiffAt (hΩ.mem_nhds hmem)).comp ((0, 0) : E × E)
    ((A.contDiff.comp contDiff_fst).prodMk contDiff_snd).contDiffAt
  exact hc

omit hμ htar in
/-- In the charts at `g` and `g⁻¹`, inversion is `X ↦ log (exp (-(Ad_g X)))`, i.e. `-Ad_g` near
`0`. -/
theorem contMDiff_inv_expChartedSpace (hρ : 0 < ρ) :
    letI := S.expChartedSpace ρ hρ
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ fun a : G => a⁻¹ := by
  let _ := S.expChartedSpace ρ hρ
  intro g
  rw [contMDiffAt_iff]
  refine ⟨continuous_inv.continuousAt, ?_⟩
  obtain ⟨B, hB⟩ := S.conj g
  have hF : (extChartAt 𝓘(ℝ, E) g⁻¹ ∘ (fun a : G => a⁻¹) ∘ (extChartAt 𝓘(ℝ, E) g).symm) =
      fun X => S.chart.symm (S.exp (-(B X))) := by
    funext X
    simp only [Function.comp_apply, extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id]
    show S.leftChart ρ g⁻¹ ((S.leftChart ρ g).symm X)⁻¹ = _
    rw [leftChart_apply, leftChart_symm_apply, inv_inv, ← map_neg, ← hB (-X), exp_neg]
    congr 1
    group
  have hpt : extChartAt 𝓘(ℝ, E) g g = 0 := by
    simp only [extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp]
    show S.leftChart ρ g g = 0
    rw [leftChart_apply, inv_mul_cancel, symm_one]
  rw [hF, hpt]
  refine ContDiffAt.contDiffWithinAt ?_
  have hlin : ContDiffAt ℝ ∞ (fun X => -(B X)) 0 := (-B).contDiff.contDiffAt
  refine hlin.congr_of_eventuallyEq ?_
  have hlim : Tendsto (fun X => -(B X)) (𝓝 0) (𝓝 0) := by
    simpa using (B.continuous.tendsto 0).neg
  filter_upwards [hlim S.source_mem_nhds] with X hX
  exact S.symm_exp hX

/-- **C4**: `expChartedSpace ρ` makes `G` a `C^∞` Lie group. -/
theorem lieGroup_expChartedSpace (hρ : 0 < ρ) :
    letI := S.expChartedSpace ρ hρ
    LieGroup 𝓘(ℝ, E) ∞ G := by
  let _ := S.expChartedSpace ρ hρ
  exact { toIsManifold := S.isManifold_expChartedSpace hμ htar hρ
          contMDiff_mul := S.contMDiff_mul_expChartedSpace hμ hρ
          contMDiff_inv := S.contMDiff_inv_expChartedSpace hρ }

end Smooth

/-- **C4**: if `μ` is smooth near `(0, 0)` (the conclusion of C3), then the given topology of `G`
carries a charted space modelled on `E` making `G` a `C^∞` Lie group. -/
theorem exists_lieGroup (hμ : S.ContDiffMu) :
    ∃ _ : ChartedSpace E G, LieGroup 𝓘(ℝ, E) ∞ G := by
  obtain ⟨ρ, hρ, hsm, htar⟩ := hμ
  exact ⟨S.expChartedSpace ρ hρ, S.lieGroup_expChartedSpace hsm htar hρ⟩

/-- **C4** (blueprint `LocalExpStructure.isLieGroup`): a local exponential structure on `ℝ^d` with
smooth `μ` makes `G` a Lie group in the sense of `HSFormal.IsLieGroup`. -/
theorem isLieGroup {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {d : ℕ}
    (S : LocalExpStructure G (EuclideanSpace ℝ (Fin d))) (hμ : S.ContDiffMu) : IsLieGroup G := by
  obtain ⟨cs, hL⟩ := S.exists_lieGroup hμ
  exact ⟨d, cs, hL⟩

end LocalExpStructure

end HSFormal.GY
