import HSFormal.ChartData

/-!
# Section 7: the fixed geometric data from a hypothetical effective action

`HSFormal.FixedData` packages the fixed data of Section 7 of `fullHS_final.md` (L456–539) in the
paper's choice order `(x₀, chart, H) ≺ (ρ₊, ρ, f, Z⁺, T, ρ̃, r, R, t, u) ≺ K_i`:

* the fields are the free choices, with their defining properties;
* `Ω`, `F₀`, `Z⁺`, `f`, `fhat`, `Z₀`, `Z` are derived definitions, given by the paper's formulas;
* the properties (7.1)–(7.9) are theorems below;
* `HSFormal.exists_fixedData`: the data exist for every effective jointly continuous
  `ℤ_[p]`-action on a connected manifold without boundary, given Montgomery's theorem
  `HSFormal.PointwisePeriodicIsPeriodic`.

Degree one (L500) is proved in its homotopy form: the compactified map `fhat` is homotopic rel `∞`
to the identity of `Sⁿ = OnePoint ℝⁿ`, through the homotopy (7.6) and the scaling homotopy of the
pinch. The only further consequence drawn here, `Z⁺ ≠ ∅`, uses the non-contractibility of spheres,
isolated as the explicit hypothesis `HSFormal.SphereSelfMapSurjective`.
-/

noncomputable section

open Set Filter Metric MeasureTheory OnePoint Topology
open scoped unitInterval

namespace HSFormal

/-- The fixed data of Section 7 for an action of `ℤ_[p]` on `M` with charts in `ℝⁿ`. -/
structure FixedData (p : ℕ) [Fact p.Prime] (n : ℕ) (M : Type*) [TopologicalSpace M]
    [AddAction ℤ_[p] M] extends ChartData p n M where
  /-- `ρ₊ < 1/4` such that `B̄(0,ρ₊)` misses `Fix(H)` (L483). -/
  ρplus : ℝ
  ρplus_pos : 0 < ρplus
  ρplus_lt : ρplus < 1 / 4
  notMem_fixH : ∀ x ∈ φ.source, ‖φ x‖ ≤ ρplus → x ∉ toChartData.fixH
  /-- The pinch radius `0 < ρ < ρ₊` (L492). -/
  ρ : ℝ
  ρ_pos : 0 < ρ
  ρ_lt : ρ < ρplus
  /-- The equivariant map `ρ̃ : Z⁺ → T = S^{2m-1} ⊆ ℂ^m` of (7.7), continuous with values in `T`
  on an open neighbourhood of `Z⁺`. -/
  m : ℕ
  ρtilde : M → EuclideanSpace ℂ (Fin m)
  ρtilde_spec : ∃ U, IsOpen U ∧ toChartData.carrier ρplus ⊆ U ∧ ContinuousOn ρtilde U ∧
    ∀ x ∈ U, ‖ρtilde x‖ = 1
  ρtilde_vadd : ∀ h ∈ padicPowerSubgroup p j, ∀ x,
    ρtilde (h +ᵥ x) = (padicChar p j h : ℂ) • ρtilde x
  /-- The radii `0 < r < R < t < u < d(y, ∞)` of (7.8), for the round metric, `y = s_ρ(0)`. -/
  r : ℝ
  R : ℝ
  t : ℝ
  u : ℝ
  r_pos : 0 < r
  r_lt_R : r < R
  R_lt_t : R < t
  t_lt_u : t < u
  u_lt : u < roundDist (pinch ρ (0 : EuclideanSpace ℝ (Fin n))) ∞

namespace FixedData

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {M : Type*} [TopologicalSpace M] [AddAction ℤ_[p] M]
  (d : FixedData p n M)

/-- The carrier `Z⁺ = F₀⁻¹ B̄(0,ρ₊)` (7.4). -/
abbrev Zplus : Set M := d.carrier d.ρplus

/-- `T = S^{2m-1} ⊆ ℂ^m`, with `C_p` acting by the scalars `χ(h)` (L517). -/
abbrev T : Set (EuclideanSpace ℂ (Fin d.m)) := sphere 0 1

/-- `y = s_ρ(0)` (L519). -/
abbrev y : OnePoint (EuclideanSpace ℝ (Fin n)) := pinch d.ρ 0

/-- `Z₀ = {z : d(y,z) ≥ R}` (7.8). -/
def Z₀ : Set (OnePoint (EuclideanSpace ℝ (Fin n))) := {z | d.R ≤ roundDist d.y z}

/-- The fixed exterior `Z = T × Z₀` (7.8). -/
def Z : Set (EuclideanSpace ℂ (Fin d.m) × OnePoint (EuclideanSpace ℝ (Fin n))) := d.T ×ˢ d.Z₀

open scoped Classical in
/-- The invariant map `f = s_ρ ∘ F₀` on `Ω`, `f = ∞` elsewhere (7.5). -/
def f (x : M) : OnePoint (EuclideanSpace ℝ (Fin n)) :=
  if x ∈ d.Ω then pinch d.ρ (d.F₀ x) else ∞

theorem ρ_add_two_D_lt : d.ρ + 2 * d.D < 1 / 2 := by
  linarith [d.ρ_lt, d.ρplus_lt, d.D_lt]

/-- The cutoff annulus `|x| ≥ 1/2 - 2D` stays outside the nonconstant locus (L538, L617). -/
theorem ρ_add_two_D_lt_half_sub : d.ρ + 2 * d.D < 1 / 2 - 2 * d.D := by
  linarith [d.ρ_lt, d.ρplus_lt, d.D_lt]

theorem roundDist_y_infty : roundDist d.y ∞ = 2 := by
  rw [y, pinch_zero d.ρ_pos, roundDist_zero_infty]

theorem f_ne_infty_iff {x : M} : d.f x ≠ ∞ ↔ x ∈ d.Ω ∧ ‖d.F₀ x‖ < d.ρ := by
  by_cases hx : x ∈ d.Ω <;> simp [f, hx, pinch_eq_infty_iff]

/-- `f` is `H`-invariant. -/
theorem f_vadd {h : ℤ_[p]} (hh : h ∈ d.H) (x : M) : d.f (h +ᵥ x) = d.f x := by
  by_cases hx : x ∈ d.Ω
  · simp [f, hx, (d.vadd_mem_Ω_iff hh).2 hx, d.F₀_vadd hh]
  · have hx' : h +ᵥ x ∉ d.Ω := fun h' => hx ((d.vadd_mem_Ω_iff hh).1 h')
    simp [f, hx, hx']

theorem mem_Zplus_of_F₀_eq_zero {x : M} (hx : x ∈ d.Ω) (h0 : d.F₀ x = 0) : x ∈ d.Zplus :=
  ⟨hx, by simp [h0, d.ρplus_pos.le]⟩

theorem notMem_fixH_of_mem_Zplus {x : M} (hx : x ∈ d.Zplus) : x ∉ d.fixH :=
  d.notMem_fixH_of_mem_carrier d.notMem_fixH hx

theorem continuousOn_ρtilde : ContinuousOn d.ρtilde d.Zplus := by
  obtain ⟨U, -, hZU, hcont, -⟩ := d.ρtilde_spec
  exact hcont.mono hZU

theorem ρtilde_mem_T {x : M} (hx : x ∈ d.Zplus) : d.ρtilde x ∈ d.T := by
  obtain ⟨U, -, hZU, -, hnorm⟩ := d.ρtilde_spec
  exact mem_sphere_zero_iff_norm.2 (hnorm x (hZU hx))

/-- `C_p` acts freely on `T` (L517). -/
theorem mem_H'_of_smul_eq {h : ℤ_[p]} {v : EuclideanSpace ℂ (Fin d.m)} (hv : v ∈ d.T)
    (heq : (padicChar p d.j h : ℂ) • v = v) : h ∈ d.H' :=
  mem_of_padicChar_smul_eq (ne_zero_of_mem_unit_sphere ⟨v, hv⟩) heq

/-- `K_i = H_{ℓ_i} ⊆ H'` once `ℓ_i > j` (7.9). -/
theorem tail_le_H' {l : ℕ} (hl : d.j + 1 ≤ l) : padicPowerSubgroup p l ≤ d.H' :=
  (padicPowerSubgroup_le_iff l (d.j + 1)).2 hl

/-- The homotopy `s_ρ((1-t) F₀ + t x)` of (7.6), in chart coordinates. -/
def chartHomotopyFun (q : I × EuclideanSpace ℝ (Fin n)) : OnePoint (EuclideanSpace ℝ (Fin n)) :=
  if ‖q.2‖ < 2 then
    pinch d.ρ ((1 - (q.1 : ℝ)) • d.F₀ (d.φ.symm q.2) + (q.1 : ℝ) • q.2)
  else ∞

section Action

variable [ContinuousVAdd ℤ_[p] M]

/-- The nonconstant locus of `f` lies in `φ⁻¹ B(0, ρ + 2D)` (L500). -/
theorem mem_of_f_ne_infty {x : M} (hx : d.f x ≠ ∞) :
    x ∈ d.φ.source ∧ ‖d.φ x‖ < d.ρ + 2 * d.D := by
  obtain ⟨hΩ, hF⟩ := d.f_ne_infty_iff.1 hx
  refine ⟨d.Ω_subset_source hΩ, ?_⟩
  have h := d.norm_F₀_sub_le hΩ
  calc ‖d.φ x‖ = ‖d.F₀ x - (d.F₀ x - d.φ x)‖ := by rw [sub_sub_cancel]
    _ ≤ ‖d.F₀ x‖ + ‖d.F₀ x - d.φ x‖ := norm_sub_le _ _
    _ < d.ρ + 2 * d.D := by linarith

theorem norm_F₀_symm_sub_le {v : EuclideanSpace ℝ (Fin n)} (hv : ‖v‖ < 2) :
    ‖d.F₀ (d.φ.symm v) - v‖ ≤ 2 * d.D := by
  have h := d.norm_F₀_sub_le (d.symm_mem_Ω hv)
  rwa [d.φ.right_inv (d.mem_target_of_norm_lt hv.le (by norm_num))] at h

/-- (7.6) is `∞` outside the fixed compact set `B̄(0, ρ + 2D)`, uniformly in `t` (L507). -/
theorem chartHomotopyFun_eq_infty {q : I × EuclideanSpace ℝ (Fin n)}
    (hq : d.ρ + 2 * d.D < ‖q.2‖) : d.chartHomotopyFun q = ∞ := by
  obtain ⟨t, v⟩ := q
  simp only at hq
  unfold chartHomotopyFun
  split_ifs with h2
  · apply pinch_of_le
    set F := d.F₀ (d.φ.symm v)
    have hFv := d.norm_F₀_symm_sub_le h2
    have ht0 : 0 ≤ 1 - (t : ℝ) := sub_nonneg.2 t.2.2
    have hw : v = ((1 - (t : ℝ)) • F + (t : ℝ) • v) - (1 - (t : ℝ)) • (F - v) := by
      simp only [smul_sub, sub_smul, one_smul]
      abel
    have h := norm_sub_le ((1 - (t : ℝ)) • F + (t : ℝ) • v) ((1 - (t : ℝ)) • (F - v))
    rw [← hw, norm_smul, Real.norm_of_nonneg ht0] at h
    nlinarith [mul_nonneg t.2.1 (norm_nonneg (F - v))]
  · rfl

/-- Stabilizers on `Z⁺` lie in `H' = H_{j+1}`, so `C_p = H/H'` acts freely on `Z⁺/H'` (L509). -/
theorem stabilizer_le_H' [T2Space M] {x : M} (hx : x ∈ d.Zplus) :
    AddAction.stabilizer ℤ_[p] x ≤ d.H' :=
  padicStabilizer_le_nextPower_of_not_fixed d.j x (d.notMem_fixH_of_mem_Zplus hx)

/-- (7.9): for depths `ℓ_i → ∞`, the displacement of `K_i = H_{ℓ_i}` on the fixed compact chart
saturation `Q = H · φ⁻¹ B̄(0,2) ⊇ Ω` tends to zero uniformly, and `K_i` keeps `Q` in the chart. -/
theorem eventually_displacement_lt {ℓ : ℕ → ℕ} (hℓ : Tendsto ℓ atTop atTop) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∀ k ∈ padicPowerSubgroup p (ℓ i), ∀ x ∈ d.Q,
      k +ᵥ x ∈ d.φ.source ∧ ‖d.φ (k +ᵥ x) - d.φ x‖ < ε := by
  obtain ⟨V, hV, hVQ⟩ :=
    exists_nhds_chart_displacement (p := p) d.φ d.isCompact_Q d.Q_subset_source hε
  exact (hℓ.eventually (padic_power_subgroups_shrink p V hV)).mono fun i hi k hk x hx =>
    hVQ k (hi hk) x hx

section Homotopy

/-! ### Degree one: the homotopy (7.6) on the compactified chart -/

variable [LocallyCompactSpace M] [FirstCountableTopology M]

theorem continuous_chartHomotopyFun : Continuous d.chartHomotopyFun := by
  set A : Set (I × EuclideanSpace ℝ (Fin n)) := {q | ‖q.2‖ < 2}
  have hA : IsOpen A := isOpen_lt (continuous_norm.comp continuous_snd) continuous_const
  have hF : ContinuousOn (fun q : I × EuclideanSpace ℝ (Fin n) => d.F₀ (d.φ.symm q.2)) A :=
    d.continuousOn_F₀.comp (d.φ.continuousOn_symm.comp continuous_snd.continuousOn
      fun q hq => d.mem_target_of_norm_lt (le_of_lt hq) (by norm_num))
      fun q hq => d.symm_mem_Ω hq
  have hw : ContinuousOn (fun q : I × EuclideanSpace ℝ (Fin n) =>
      (1 - (q.1 : ℝ)) • d.F₀ (d.φ.symm q.2) + (q.1 : ℝ) • q.2) A :=
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).continuousOn.smul
      hF).add ((continuous_subtype_val.comp continuous_fst).smul continuous_snd).continuousOn
  have hlt := d.ρ_add_two_D_lt
  refine continuous_iff_continuousAt.2 fun q => ?_
  by_cases hq : ‖q.2‖ < 2
  · have hev : (fun q' : I × EuclideanSpace ℝ (Fin n) =>
        pinch d.ρ ((1 - (q'.1 : ℝ)) • d.F₀ (d.φ.symm q'.2) + (q'.1 : ℝ) • q'.2)) =ᶠ[𝓝 q]
        d.chartHomotopyFun := by
      filter_upwards [hA.mem_nhds hq] with q' hq'
      simp only [chartHomotopyFun, ite_eq_left (show ‖q'.2‖ < 2 from hq')]
    exact ((continuous_pinch d.ρ_pos).continuousAt.comp
      (hw.continuousAt (hA.mem_nhds hq))).congr hev
  · have hq' : d.ρ + 2 * d.D < ‖q.2‖ := by push Not at hq; linarith
    have hev : (fun _ => ∞) =ᶠ[𝓝 q] d.chartHomotopyFun := by
      filter_upwards [(isOpen_lt continuous_const (continuous_norm.comp continuous_snd)).mem_nhds
        hq'] with q' hq'
      exact (d.chartHomotopyFun_eq_infty hq').symm
    exact continuousAt_const.congr hev

/-- The homotopy (7.6) on the compactified chart `I × Sⁿ → Sⁿ`. -/
def chartHomotopy : C(I × OnePoint (EuclideanSpace ℝ (Fin n)), OnePoint (EuclideanSpace ℝ (Fin n)))
    where
  toFun q := q.2.elim ∞ fun v => d.chartHomotopyFun (q.1, v)
  continuous_toFun := continuous_elim_prod d.continuous_chartHomotopyFun fun s hs =>
    ⟨closedBall 0 (d.ρ + 2 * d.D), isClosed_closedBall, isCompact_closedBall _ _, fun t v hv => by
      rw [d.chartHomotopyFun_eq_infty (by simpa using hv)]
      exact mem_of_mem_nhds hs⟩

/-- `f` on the artificial sphere obtained by compactifying coordinate space (L500). -/
def fhat : C(OnePoint (EuclideanSpace ℝ (Fin n)), OnePoint (EuclideanSpace ℝ (Fin n))) :=
  d.chartHomotopy.comp ⟨fun z => (0, z), by fun_prop⟩

@[simp]
theorem fhat_infty : d.fhat ∞ = ∞ := rfl

theorem fhat_coe (v : EuclideanSpace ℝ (Fin n)) :
    d.fhat v = if ‖v‖ < 2 then pinch d.ρ (d.F₀ (d.φ.symm v)) else ∞ := by
  simp [fhat, chartHomotopy, chartHomotopyFun]

/-- `fhat` is `f` read in the chart, and `∞` off the chart. -/
theorem fhat_coe_of_mem_target {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ d.φ.target) :
    d.fhat v = d.f (d.φ.symm v) := by
  rw [fhat_coe]
  split_ifs with h2
  · simp [f, d.symm_mem_Ω h2]
  · by_contra hne
    have h := (d.mem_of_f_ne_infty (Ne.symm hne)).2
    rw [d.φ.right_inv hv] at h
    linarith [d.ρ_add_two_D_lt]

/-- (7.6): a homotopy rel `∞` from `fhat` to the chart pinch, constant `∞` outside the fixed
compact set `B̄(0, ρ + 2D)`. -/
def homotopy76 : d.fhat.HomotopyRel (pinchMap d.ρ_pos) {∞} where
  toContinuousMap := d.chartHomotopy
  map_zero_left _ := rfl
  map_one_left z := by
    induction z using OnePoint.rec with
    | infty => rfl
    | coe v =>
      change d.chartHomotopyFun (1, v) = pinch d.ρ v
      unfold chartHomotopyFun
      split_ifs with h2
      · simp
      · have h2' : 2 ≤ ‖v‖ := not_lt.1 h2
        exact (pinch_of_le (by linarith [d.ρ_add_two_D_lt, d.D_nonneg])).symm
  prop' t z hz := by
    rw [mem_singleton_iff] at hz
    subst hz
    rfl

/-- **Degree one** (L500): `fhat` is homotopic rel `∞` to the identity of `Sⁿ`. -/
theorem fhat_homotopicRel_id : d.fhat.HomotopicRel (ContinuousMap.id _) {∞} :=
  ⟨d.homotopy76.trans (pinchHomotopy d.ρ_pos (by linarith [d.ρ_lt, d.ρplus_lt])).symm⟩

/-- A degree-one consequence: `F₀` vanishes somewhere on `Ω`. -/
theorem exists_F₀_eq_zero (hB : SphereSelfMapSurjective) : ∃ x ∈ d.Ω, d.F₀ x = 0 := by
  obtain ⟨z, hz⟩ := hB n d.fhat d.fhat_homotopicRel_id.homotopic
    ((0 : EuclideanSpace ℝ (Fin n)) : OnePoint (EuclideanSpace ℝ (Fin n)))
  have hz' : z ≠ ∞ := by
    rintro rfl
    exact infty_ne_coe _ hz
  obtain ⟨v, rfl⟩ := OnePoint.ne_infty_iff_exists.1 hz'
  rw [fhat_coe] at hz
  split_ifs at hz with h2
  · have hne : pinch d.ρ (d.F₀ (d.φ.symm v)) ≠ ∞ := by rw [hz]; exact coe_ne_infty _
    have hlt : ‖d.F₀ (d.φ.symm v)‖ < d.ρ := not_le.1 fun h => hne (pinch_of_le h)
    rw [pinch_of_lt hlt, OnePoint.coe_eq_coe, smul_eq_zero] at hz
    refine ⟨d.φ.symm v, d.symm_mem_Ω h2, hz.resolve_left ?_⟩
    exact inv_ne_zero (sub_pos.2 hlt).ne'
  · exact absurd hz (infty_ne_coe _)

/-- `Z⁺ ≠ ∅`, by degree one and the non-contractibility of spheres. -/
theorem Zplus_nonempty (hB : SphereSelfMapSurjective) : d.Zplus.Nonempty := by
  obtain ⟨x, hx, h0⟩ := d.exists_F₀_eq_zero hB
  exact ⟨x, d.mem_Zplus_of_F₀_eq_zero hx h0⟩

/-! ### Continuity of `f`, compactness of `Z⁺`, the labels (7.8) -/

variable [T2Space M]

theorem continuous_f : Continuous d.f := by
  set K := d.φ.source ∩ d.φ ⁻¹' closedBall 0 (d.ρ + 2 * d.D)
  have hlt := d.ρ_add_two_D_lt
  have hK : IsCompact K := d.isCompact_chartBall (by linarith)
  refine continuous_iff_continuousAt.2 fun x => ?_
  by_cases hx : x ∈ d.Ω
  · have hev : (fun y => pinch d.ρ (d.F₀ y)) =ᶠ[𝓝 x] d.f := by
      filter_upwards [d.isOpen_Ω.mem_nhds hx] with y hy
      simp [f, hy]
    exact ((continuous_pinch d.ρ_pos).continuousAt.comp
      (d.continuousOn_F₀.continuousAt (d.isOpen_Ω.mem_nhds hx))).congr hev
  · have hxK : x ∉ K := fun hxK => hx (d.mem_Ω_of_norm_lt hxK.1
      ((mem_closedBall_zero_iff.1 hxK.2).trans_lt (by linarith)))
    have hev : (fun _ => ∞) =ᶠ[𝓝 x] d.f := by
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hxK] with y hy
      by_contra hne
      obtain ⟨hs, hφ⟩ := d.mem_of_f_ne_infty (Ne.symm hne)
      exact hy ⟨hs, mem_closedBall_zero_iff.2 hφ.le⟩
    exact continuousAt_const.congr hev

theorem isCompact_Zplus : IsCompact d.Zplus := d.isCompact_carrier d.ρplus_lt

/-- For every closed `C ⊆ Sⁿ` avoiding `∞`, `f⁻¹ C` is a compact subset of `int Z⁺`. -/
theorem preimage_subset_interior_Zplus {C : Set (OnePoint (EuclideanSpace ℝ (Fin n)))}
    (hC : IsClosed C) (hinf : ∞ ∉ C) :
    IsCompact (d.f ⁻¹' C) ∧ d.f ⁻¹' C ⊆ interior d.Zplus := by
  have hW : IsOpen (d.Ω ∩ d.F₀ ⁻¹' ball 0 d.ρplus) :=
    d.continuousOn_F₀.isOpen_inter_preimage d.isOpen_Ω isOpen_ball
  have hWZ : d.Ω ∩ d.F₀ ⁻¹' ball 0 d.ρplus ⊆ interior d.Zplus :=
    interior_maximal (inter_subset_inter_right _ (preimage_mono ball_subset_closedBall)) hW
  have hsub : d.f ⁻¹' C ⊆ interior d.Zplus := fun x hx => by
    obtain ⟨hΩ, hF⟩ := d.f_ne_infty_iff.1 fun h => hinf (h ▸ hx)
    exact hWZ ⟨hΩ, mem_ball_zero_iff.2 (hF.trans d.ρ_lt)⟩
  exact ⟨d.isCompact_Zplus.of_isClosed_subset (hC.preimage d.continuous_f)
    (hsub.trans interior_subset), hsub⟩

/-- (7.8): `f⁻¹ B̄(y,u)` is compact and lies inside `int Z⁺` (L527). -/
theorem label_preimage :
    IsCompact (d.f ⁻¹' {z | roundDist d.y z ≤ d.u}) ∧
      d.f ⁻¹' {z | roundDist d.y z ≤ d.u} ⊆ interior d.Zplus := by
  have hc : Continuous fun z : OnePoint (EuclideanSpace ℝ (Fin n)) => roundDist d.y z :=
    continuous_roundDist_left _
  have hu : d.u < 2 := d.u_lt.trans_eq d.roundDist_y_infty
  refine d.preimage_subset_interior_Zplus (isClosed_le hc continuous_const) fun h => ?_
  have h' : roundDist d.y ∞ ≤ d.u := h
  rw [d.roundDist_y_infty] at h'
  exact absurd (h'.trans_lt hu) (lt_irrefl 2)

end Homotopy

end Action

end FixedData

/-! ### Existence -/

section Existence

variable (hMon : PointwisePeriodicIsPeriodic) {p : ℕ} [Fact p.Prime] {n : ℕ} {M : Type}
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ConnectedSpace M]
  [AddAction ℤ_[p] M] [ContinuousVAdd ℤ_[p] M] [FaithfulVAdd ℤ_[p] M]
include hMon

/-- The data `(x₀, φ, H, D)` of (7.1) exist for an effective action (L458–466). -/
theorem exists_chartData : Nonempty (ChartData p n M) := by
  obtain ⟨x₀, hx₀⟩ := exists_stabilizer_eq_bot (p := p) hMon (n := n) (M := M)
  obtain ⟨φ, hx₀s, hφx₀, hball⟩ := exists_chart_ball (n := n) x₀
  have hsub : closedBall (0 : EuclideanSpace ℝ (Fin n)) 2 ⊆ φ.target := fun v hv =>
    hball (mem_ball_zero_iff.2 ((mem_closedBall_zero_iff.1 hv).trans_lt (by norm_num)))
  have hK : IsCompact (φ.source ∩ φ ⁻¹' closedBall 0 2) := by
    rw [← φ.symm_image_eq_source_inter_preimage hsub]
    exact (isCompact_closedBall 0 2).image_of_continuousOn (φ.continuousOn_symm.mono hsub)
  obtain ⟨V, hV, hVK⟩ := exists_nhds_chart_displacement (p := p) φ hK inter_subset_left
    (by norm_num : (0 : ℝ) < 1 / 128)
  obtain ⟨j, hj⟩ := (padic_power_subgroups_shrink p V hV).exists
  exact ⟨{
    x₀ := x₀
    stabilizer_x₀ := hx₀
    φ := φ
    x₀_mem_source := hx₀s
    φ_x₀ := hφx₀
    ball_subset_target := hball
    j := j
    D := 1 / 128
    D_nonneg := by norm_num
    D_lt := by norm_num
    vadd_mem_source := fun h hh x hx hx2 =>
      (hVK h (hj hh) x ⟨hx, mem_closedBall_zero_iff.2 hx2⟩).1
    displacement_le := fun h hh x hx hx2 =>
      (hVK h (hj hh) x ⟨hx, mem_closedBall_zero_iff.2 hx2⟩).2.le }⟩

/-- **Section 7**: an effective jointly continuous `ℤ_[p]`-action on a connected manifold without
boundary has the fixed data `HSFormal.FixedData`, given Montgomery's theorem. -/
theorem exists_fixedData : Nonempty (FixedData p n M) := by
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  obtain ⟨c⟩ := exists_chartData (p := p) (n := n) (M := M) hMon
  obtain ⟨ρplus, hρ0, hρ1, hfix⟩ := c.exists_ρplus
  obtain ⟨m, ρt, hU, hvadd⟩ := exists_equivariant_sphere_map c.j (c.isCompact_carrier hρ1)
    fun x hx => c.notMem_fixH_of_mem_carrier hfix hx
  have hd : roundDist (pinch (ρplus / 2) (0 : EuclideanSpace ℝ (Fin n))) ∞ = 2 := by
    rw [pinch_zero (by positivity), roundDist_zero_infty]
  exact ⟨{ c with
    ρplus := ρplus
    ρplus_pos := hρ0
    ρplus_lt := hρ1
    notMem_fixH := hfix
    ρ := ρplus / 2
    ρ_pos := by positivity
    ρ_lt := half_lt_self hρ0
    m := m
    ρtilde := ρt
    ρtilde_spec := hU
    ρtilde_vadd := hvadd
    r := 1 / 2
    R := 1
    t := 3 / 2
    u := 7 / 4
    r_pos := by norm_num
    r_lt_R := by norm_num
    R_lt_t := by norm_num
    t_lt_u := by norm_num
    u_lt := by rw [hd]; norm_num }⟩

end Existence

end HSFormal
