import HSFormal.Cubical.ChainModelBounds
import HSFormal.SphereNonContractible

/-!
# The chain-model data of §8 (cubical module C6, part 4): `ChainModelData`

The `(ρ̃, f)`-labels of the cells of `W_i` (`labS`, values in `T × Sⁿ = LabelSpace`), honest on the
buffered region `buf = {d(y, f) ≤ u}` (l.544–548, (7.8)):

* `graphTendsto_buf`: a family whose entries from buffered cells land within `δ → 0` of
  `ĥ_{θ}(source)` has graph type `χ(θ)` there, uniformly — by (8.2) `f ĥ = f`, (7.7)
  `ρ̃(h x) = χ(h) ρ̃(x)` and uniform continuity of `ρ̃ ∘ φ⁻¹` at the compact set `φ(H · f⁻¹B̄(y,u))`.
* Buffered graph type of `a_g` (type `g`), `B_{g,h}` (type `gh`), `U_g` (type `1`), `V_g`
  (type `g`, through the inner track identities `ĥ_g ĥ_{g⁻¹} = k` on `|x| ≤ 1/2`), and of
  `d, φ, b, H, H'` (type `1`).
* The far subcomplexes `F_i` (cells whose closed carrier misses `f⁻¹B̄(y, t)`, l.710).

`chainModelData d : ChainModelData d` packages everything with the field layout of
`HSFormal.Prop92.ChainModelInput` (for `cd = d.control`, `π = d.π`), plus `a_z` (8.4) and the
slant homotopies `U` (8.6).  `D` is literally the germ complex of `HSFormal.manifoldGerm` for
`c = f̂` (`D_eq_germ`): mesh `16/(i+2)`, `torusCP.duality`, labels `f̂ ∘ q ∘ centre`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Filter Metric Topology Set Matrix
open HSFormal.Cubical HSFormal.Cubical.BasedComplex
open scoped Kronecker ENNReal

namespace HSFormal.FixedData

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {M : Type*} [TopologicalSpace M] [AddAction ℤ_[p] M]
  (d : FixedData p n M)

/-! ### `ρ̃` near the buffered region -/

section Rho

variable [ContinuousVAdd ℤ_[p] M] [LocallyCompactSpace M] [FirstCountableTopology M] [T2Space M]

/-- The buffered points: `d(y, f) ≤ u` (7.8). -/
def bufPt (x : Fin n → AddCircle (16 : ℝ)) : Prop := dist d.yS (d.torusLabel x) ≤ d.u

/-- `K = f⁻¹ B̄(y, u)`, compact inside `int Z⁺` (7.8). -/
abbrev Kf : Set M := d.fS ⁻¹' closedBall d.yS d.u

theorem Kf_subset_Zplus : d.Kf ⊆ d.Zplus := d.label_preimage_closedBall.2.trans interior_subset

/-- The compact chart set `φ(H · K)`, where `ρ̃ ∘ φ⁻¹` is continuous. -/
def Sset : Set (EuclideanSpace ℝ (Fin n)) :=
  (fun q : ℤ_[p] × M ↦ d.φ (q.1 +ᵥ q.2)) '' ((d.H : Set ℤ_[p]) ×ˢ d.Kf)

theorem isCompact_Sset : IsCompact d.Sset := by
  refine ((padicPowerSubgroup_isClosed _).isCompact.prod
    d.label_preimage_closedBall.1).image_of_continuousOn fun q hq ↦ ?_
  have hmem : q.1 +ᵥ q.2 ∈ d.φ.source :=
    d.vadd_mem_source_of_mem_Ω (d.Kf_subset_Zplus hq.2).1 hq.1
  exact (ContinuousAt.comp (g := d.φ) (f := fun q : ℤ_[p] × M ↦ q.1 +ᵥ q.2)
    (d.φ.continuousAt hmem) (continuousAt_fst.vadd continuousAt_snd)).continuousWithinAt

theorem continuousAt_rhoChart {w : EuclideanSpace ℝ (Fin n)} (hw : w ∈ d.Sset) :
    ContinuousAt d.rhoChart w := by
  obtain ⟨⟨a, x⟩, ⟨ha, hx⟩, rfl⟩ := hw
  obtain ⟨U, hU, hZU, hcont, -⟩ := d.ρtilde_spec
  have hZ : a +ᵥ x ∈ d.Zplus := (d.vadd_mem_carrier_iff ha).2 (d.Kf_subset_Zplus hx)
  have hsrc : a +ᵥ x ∈ d.φ.source := d.Ω_subset_source hZ.1
  have h1 : ContinuousAt d.φ.symm (d.φ (a +ᵥ x)) := d.φ.continuousAt_symm (d.φ.map_source hsrc)
  have h2 : ContinuousAt d.ρtilde (d.φ.symm (d.φ (a +ᵥ x))) := by
    rw [d.φ.left_inv hsrc]; exact hcont.continuousAt (hU.mem_nhds (hZU hZ))
  exact h2.comp h1

/-- **Uniform continuity of `ρ̃` at the buffered region** (l.548). -/
theorem exists_rhoChart_close {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ w ∈ d.Sset,
    ∀ w', dist w w' < δ → dist (d.rhoChart w) (d.rhoChart w') < ε := by
  have := d.isCompact_Sset.uniformContinuousAt_of_continuousAt d.rhoChart
    (fun w hw ↦ d.continuousAt_rhoChart hw) (Metric.dist_mem_uniformity hε)
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_uniformity_dist.mp this
  exact ⟨δ, hδ, fun w hw w' hww' ↦ hsub hww' hw⟩

/-- A base point of `T` (`Z⁺ ≠ ∅` by degree one, `sphereSelfMapSurjective`). -/
def basePt : sphere (0 : EuclideanSpace ℂ (Fin d.m)) 1 :=
  ⟨d.ρtilde (d.Zplus_nonempty sphereSelfMapSurjective).some,
    d.ρtilde_mem_T (d.Zplus_nonempty sphereSelfMapSurjective).some_mem⟩

/-- Radial projection to `T` (the base point at `0`); the identity on `T`. -/
def toT (v : EuclideanSpace ℂ (Fin d.m)) : sphere (0 : EuclideanSpace ℂ (Fin d.m)) 1 :=
  if h : v = 0 then d.basePt else ⟨‖v‖⁻¹ • v, by simp [norm_smul, norm_ne_zero_iff.mpr h]⟩

theorem toT_of_norm_eq_one {v : EuclideanSpace ℂ (Fin d.m)} (hv : ‖v‖ = 1) :
    (d.toT v : EuclideanSpace ℂ (Fin d.m)) = v := by
  have : v ≠ 0 := fun h ↦ by simp [h] at hv
  simp [toT, this, hv]

theorem dist_toT_le {v w : EuclideanSpace ℂ (Fin d.m)} (hw : ‖w‖ = 1) :
    dist (d.toT v : EuclideanSpace ℂ (Fin d.m)) w ≤ 2 * dist v w := by
  by_cases hv : v = 0
  · subst hv
    have e : d.toT 0 = d.basePt := by simp [toT]
    rw [e, dist_zero_left, hw, mul_one]
    have := d.basePt.2
    rw [mem_sphere_zero_iff_norm] at this
    rw [dist_eq_norm]
    linarith [norm_sub_le (d.basePt : EuclideanSpace ℂ (Fin d.m)) w]
  · simp only [toT, dif_neg hv]
    have hv' : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have e : ‖(‖v‖⁻¹ • v : EuclideanSpace ℂ (Fin d.m)) - v‖ = |1 - ‖v‖| := by
      rw [show (‖v‖⁻¹ • v : EuclideanSpace ℂ (Fin d.m)) - v = (‖v‖⁻¹ - 1) • v by
        rw [sub_smul, one_smul], norm_smul, Real.norm_eq_abs]
      rw [show ‖v‖⁻¹ - 1 = (1 - ‖v‖) / ‖v‖ by field_simp, abs_div, abs_of_pos hv',
        div_mul_cancel₀ _ hv'.ne']
    have h₁ : |1 - ‖v‖| ≤ dist v w := by
      rw [← hw, dist_eq_norm, abs_sub_comm]; exact abs_norm_sub_norm_le v w
    rw [dist_eq_norm] at h₁
    rw [dist_eq_norm, dist_eq_norm]
    calc ‖(‖v‖⁻¹ • v : EuclideanSpace ℂ (Fin d.m)) - w‖
        ≤ ‖(‖v‖⁻¹ • v : EuclideanSpace ℂ (Fin d.m)) - v‖ + ‖v - w‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2 * ‖v - w‖ := by rw [e]; linarith

/-- **The `(ρ̃, f)`-label** of a point of the torus, in `T × Sⁿ` (§9, l.721). -/
def labS (x : Fin n → AddCircle (16 : ℝ)) : LabelSpace d.m n :=
  (d.toT (d.rhoChart (liftVec 16 x)), d.torusLabel x)

theorem norm_liftVec_of_bufPt {x : Fin n → AddCircle (16 : ℝ)} (hx : d.bufPt x) :
    ‖liftVec 16 x‖ ≤ d.ρ + 2 * d.D := by
  by_contra h
  push_neg at h
  have h' : d.torusLabel x = RoundSphere.infty := d.fhat_eq_infty h
  have hu : d.u < 2 := d.u_lt.trans_eq d.roundDist_y_infty
  rw [bufPt, h', d.dist_yS_infty] at hx
  linarith

theorem symm_mem_Kf {x : Fin n → AddCircle (16 : ℝ)} (hx : d.bufPt x) :
    d.φ.symm (liftVec 16 x) ∈ d.Kf := by
  have hv := d.norm_liftVec_of_bufPt hx
  have h4 : ‖liftVec 16 x‖ ≤ 2 := by linarith [d.ρ_add_two_D_lt]
  change dist (d.fS (d.φ.symm (liftVec 16 x))) d.yS ≤ d.u
  rw [dist_comm]
  have e : d.fS (d.φ.symm (liftVec 16 x)) = d.torusLabel x := by
    change RoundSphere.toOnePoint.symm (d.f _) = d.fhat (liftVec 16 x)
    rw [d.fhat_coe_of_mem_target (d.mem_target_of_norm_lt h4 (by norm_num))]; rfl
  rw [e]; exact hx

theorem chartAct_mem_Sset {a : ℤ_[p]} (ha : a ∈ d.H) {x : Fin n → AddCircle (16 : ℝ)}
    (hx : d.bufPt x) : d.chartAct a (liftVec 16 x) ∈ d.Sset :=
  ⟨(a, d.φ.symm (liftVec 16 x)), ⟨ha, d.symm_mem_Kf hx⟩, rfl⟩

theorem norm_rhoChart_of_bufPt {x : Fin n → AddCircle (16 : ℝ)} (hx : d.bufPt x) :
    ‖d.rhoChart (liftVec 16 x)‖ = 1 := by
  obtain ⟨U, -, hZU, -, hnorm⟩ := d.ρtilde_spec
  exact hnorm _ (hZU (d.Kf_subset_Zplus (d.symm_mem_Kf hx)))


theorem coe_smul_labS_fst {c : PadicTail p d.j} {x : Fin n → AddCircle (16 : ℝ)} (hx : d.bufPt x) :
    (((d.χ c • d.labS x).1 : sphere (0 : EuclideanSpace ℂ (Fin d.m)) 1) :
      EuclideanSpace ℂ (Fin d.m)) = d.rhoChart (d.chartAct c.val (liftVec 16 x)) := by
  have hv := d.norm_liftVec_of_bufPt hx
  rw [d.rhoChart_chartAct c.val_mem (by linarith [d.ρ_add_two_D_lt])]
  change ((d.χ c : Circle) : ℂ) • ((d.toT (d.rhoChart (liftVec 16 x)) :
    sphere (0 : EuclideanSpace ℂ (Fin d.m)) 1) : EuclideanSpace ℂ (Fin d.m)) = _
  rw [d.toT_of_norm_eq_one (d.norm_rhoChart_of_bufPt hx), coe_χ]

/-- **Buffered graph type from carrier bounds** (l.544–548): if every entry `y ← x` from a
buffered `x` lands within `δ` of `ĥ_{θ}(x)`, eventually for every `δ > 0`, the family has graph
type `χ(θ)` on the buffer in the `(ρ̃, f)`-labels, uniformly. -/
theorem graphTendsto_buf {J α β : ℕ → Type*} (src : ∀ i, α i → Fin n → AddCircle (16 : ℝ))
    (tgt : ∀ i, β i → Fin n → AddCircle (16 : ℝ)) (u : ∀ i, J i → Matrix (β i) (α i) ℚ)
    (θ : ∀ i, J i → PadicTail p d.j)
    (h : ∀ δ > 0, ∀ᶠ i in atTop, ∀ j y x, d.bufPt (src i x) → u i j y x ≠ 0 →
      dist (tgt i y) (d.hatT (θ i j).val (src i x)) < δ) :
    GraphTendsto (fun i x ↦ d.bufPt (src i x)) (fun i j ↦ d.χ (θ i j)) u
      (fun i x ↦ d.labS (src i x)) (fun i y ↦ d.labS (tgt i y)) := by
  refine ENNReal.tendsto_nhds_zero.mpr fun ε hε ↦ ?_
  obtain ⟨r, hr, hrε⟩ := exists_real_le hε
  obtain ⟨δf, hδf, hf⟩ := Metric.uniformContinuous_iff.mp d.uniformContinuous_torusLabel r hr
  obtain ⟨δρ, hδρ, hρ⟩ := d.exists_rhoChart_close (half_pos hr)
  have hn : 0 < √n + 1 := by positivity
  set δ := min δf (min (δρ / (√n + 1)) 1) with hδdef
  have hδ : 0 < δ := lt_min hδf (lt_min (div_pos hδρ hn) one_pos)
  filter_upwards [h δ hδ] with i hi
  refine graphErr_le_iff.mpr fun j y x hx hu ↦ ?_
  have hyx := hi j y x hx hu
  have ha : (θ i j).val ∈ d.H := (θ i j).val_mem
  have hv := d.norm_liftVec_of_bufPt hx
  have hv1 : ‖liftVec 16 (src i x)‖ ≤ 1 := by linarith [d.ρ_add_two_D_lt]
  have hw := d.liftVec_hatT_of_le_one ha hv1
  have hfd : dist (d.torusLabel (tgt i y)) (d.torusLabel (src i x)) < r := by
    rw [← d.torusLabel_hatT ha (src i x)]; exact hf (hyx.trans_le (min_le_left _ _))
  have hw6 : ‖liftVec 16 (d.hatT (θ i j).val (src i x))‖ ≤ 6 := by
    rw [hw]; linarith [d.norm_chartAct_le ha (by linarith : ‖liftVec 16 (src i x)‖ ≤ 2), d.D_lt]
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have hδρ' : √n * δ < δρ := by
    have : δ ≤ δρ / (√n + 1) := (min_le_right _ _).trans (min_le_left _ _)
    rw [le_div_iff₀ hn] at this
    nlinarith
  have hlift := norm_liftVec_sub_le hw6 (hyx.le.trans hδ1)
  have hρd : dist (d.rhoChart (d.chartAct (θ i j).val (liftVec 16 (src i x))))
      (d.rhoChart (liftVec 16 (tgt i y))) < r / 2 := by
    refine hρ _ (d.chartAct_mem_Sset ha hx) _ ?_
    rw [← hw, dist_eq_norm, norm_sub_rev]
    calc _ ≤ √n * dist (tgt i y) (d.hatT (θ i j).val (src i x)) := hlift
      _ ≤ √n * δ := by gcongr
      _ < δρ := hδρ'
  have hunit : ‖d.rhoChart (d.chartAct (θ i j).val (liftVec 16 (src i x)))‖ = 1 := by
    rw [d.rhoChart_chartAct ha (by linarith), norm_smul, Circle.norm_coe, one_mul,
      d.norm_rhoChart_of_bufPt hx]
  have hρ' : dist (d.labS (tgt i y)).1 (d.χ (θ i j) • d.labS (src i x)).1 < r := by
    rw [Subtype.dist_eq, d.coe_smul_labS_fst hx]
    refine (d.dist_toT_le hunit).trans_lt ?_
    rw [dist_comm]; linarith
  rw [Prod.edist_eq]
  refine max_le ?_ ?_
  · rw [edist_dist]
    exact (ENNReal.ofReal_le_ofReal hρ'.le).trans hrε
  · change edist (d.torusLabel (tgt i y)) (d.χ (θ i j) • d.torusLabel (src i x)) ≤ ε
    rw [RoundSphere.smul_eq, edist_dist]
    exact (ENNReal.ofReal_le_ofReal hfd.le).trans hrε

/-- A single sequence on the buffer, as type-`1` control (`PropTendstoOn`). -/
theorem propTendstoOn_buf {α β : ℕ → Type*} (src : ∀ i, α i → Fin n → AddCircle (16 : ℝ))
    (tgt : ∀ i, β i → Fin n → AddCircle (16 : ℝ)) (u : ∀ i, Matrix (β i) (α i) ℚ)
    (h : ∀ δ > 0, ∀ᶠ i in atTop, ∀ y x, d.bufPt (src i x) → u i y x ≠ 0 →
      dist (tgt i y) (src i x) < δ) :
    PropTendstoOn (fun i x ↦ d.bufPt (src i x)) u (fun i x ↦ d.labS (src i x))
      (fun i y ↦ d.labS (tgt i y)) := by
  have hG := d.graphTendsto_buf (J := fun _ ↦ Unit) src tgt (fun i _ ↦ u i) (fun _ _ ↦ 1)
    fun δ hδ ↦ (h δ hδ).mono fun i hi _ y x hx hu ↦ by
      rw [PadicTail.val_one, hatT_zero]; exact hi y x hx hu
  refine tendsto_zero_of_le hG fun i ↦ ?_
  refine le_trans ?_ (graphPropOn_le_graphErr (θ := fun _ _ ↦ d.χ 1) (u := fun i _ ↦ u i) i ())
  rw [map_one, graphPropOn_one]

end Rho

/-! ### The `(ρ̃, f)`-labels of `W_i` and buffered control -/

section Buffered

variable [ContinuousVAdd ℤ_[p] M] [LocallyCompactSpace M] [FirstCountableTopology M] [T2Space M]

/-- The `T`-coordinate `ρ̃` of the cells of `W_i`. -/
def rhoW (i : ℕ) (q : (W n i).X) : sphere (0 : EuclideanSpace ℂ (Fin d.m)) 1 :=
  d.toT (d.rhoChart (liftVec 16 (cW i q)))

/-- The buffered cells of `W_i`. -/
def bufW (i : ℕ) (q : (W n i).X) : Prop := d.bufPt (cW i q)

/-- The `(ρ̃, f)`-labels of the cells (`pairLabel ρ̃ D.label` of `Prop92`). -/
abbrev labW (i : ℕ) (q : (W n i).X) : LabelSpace d.m n := (d.rhoW i q, d.seqW.label i q)

theorem labW_eq (i : ℕ) : d.labW i = fun q ↦ d.labS (cW i q) := rfl

theorem dist_of_prop_le {α β : Type*} {u : Matrix β α ℚ} {a : α → Fin n → AddCircle (16 : ℝ)}
    {b : β → Fin n → AddCircle (16 : ℝ)} {r : ℝ} (hr : 0 ≤ r)
    (h : prop u a b ≤ ENNReal.ofReal r) {y : β} {x : α} (hu : u y x ≠ 0) : dist (b y) (a x) ≤ r := by
  have := (edist_le_prop hu).trans h
  rwa [edist_dist, ENNReal.ofReal_le_ofReal_iff hr] at this

theorem tendsto_mesh_germ : Tendsto (fun i ↦ mesh 16 (germMesh i)) atTop (𝓝 0) :=
  tendsto_comp_germ tendsto_mesh_atTop

/-- A matrix sequence whose entries have centres within `r · η_i` is type-`1` on the buffer. -/
theorem propTendstoOn_bufW_of_prop {u : ∀ i, Matrix (W n i).X (W n i).X ℚ} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ i, prop (u i) (cW i) (cW i) ≤ ENNReal.ofReal (r * mesh 16 (germMesh i))) :
    PropTendstoOn d.bufW u d.labW d.labW := by
  refine d.propTendstoOn_buf (fun i ↦ cW i) (fun i ↦ cW i) u fun δ hδ ↦ ?_
  have := (tendsto_mesh_germ.const_mul r).eventually (gt_mem_nhds (by simpa using hδ))
  filter_upwards [this] with i hi y x _ hu
  exact (dist_of_prop_le (mul_nonneg hr (mesh_nonneg _)) (h i) hu).trans_lt hi

theorem prop_dW (i : ℕ) : prop (W n i).d (cW i) (cW i) ≤
    ENNReal.ofReal ((1 / 2) * mesh 16 (germMesh i)) := by
  rw [one_div_mul_eq_div]; exact torusCP.prop_d_le 16 (germMesh i) n

/-- `d` is `(ρ̃, f)`-controlled on the buffer. -/
theorem d_buf : PropTendstoOn d.bufW (fun i ↦ (W n i).d) d.labW d.labW :=
  d.propTendstoOn_bufW_of_prop (by norm_num) fun i ↦ prop_dW i

/-- `φ, b, H, H'` are `(ρ̃, f)`-controlled on the buffer (radii `η/2`, `η/2`, `η`, `η`). -/
theorem phi_buf : PropTendstoOn d.bufW (fun i ↦ (torusCP.duality (germMesh i) n).hom.f)
    d.labW d.labW :=
  d.propTendstoOn_bufW_of_prop (r := 1 / 2) (by norm_num) fun i ↦ by
    rw [one_div_mul_eq_div]; exact (torusCP.propLE 16 (germMesh i) n).hom

theorem inv_buf : PropTendstoOn d.bufW (fun i ↦ (torusCP.duality (germMesh i) n).inv.f)
    d.labW d.labW :=
  d.propTendstoOn_bufW_of_prop (r := 1 / 2) (by norm_num) fun i ↦ by
    rw [one_div_mul_eq_div]; exact (torusCP.propLE 16 (germMesh i) n).inv

theorem homInv_buf : PropTendstoOn d.bufW (fun i ↦ (torusCP.duality (germMesh i) n).homInv.h)
    d.labW d.labW :=
  d.propTendstoOn_bufW_of_prop (r := 1) (by norm_num) fun i ↦ by
    rw [one_mul]; exact (torusCP.propLE 16 (germMesh i) n).homInv

theorem invHom_buf : PropTendstoOn d.bufW (fun i ↦ (torusCP.duality (germMesh i) n).invHom.h)
    d.labW d.labW :=
  d.propTendstoOn_bufW_of_prop (r := 1) (by norm_num) fun i ↦ by
    rw [one_mul]; exact (torusCP.propLE 16 (germMesh i) n).invHom

theorem phiW_dist {i : ℕ} {y x : (W n i).X} (h : (torusCP.duality (germMesh i) n).hom.f y x ≠ 0) :
    dist (cW i y) (cW i x) ≤ mesh 16 (germMesh i) / 2 :=
  dist_of_prop_le (by linarith [mesh_nonneg (germMesh i)]) (torusCP.propLE 16 (germMesh i) n).hom h

/-- **`a_g` has graph type `g` on the buffer**, uniformly. -/
theorem a_buf : GraphTendsto d.bufW (fun i g ↦ d.π i g) (fun i g ↦ (d.aI i g).f) d.labW d.labW := by
  refine (d.graphTendsto_buf (fun i ↦ cW i) (fun i ↦ cW i) _ (fun i g ↦ d.rep i g)
    fun δ hδ ↦ ?_).congr (funext₂ fun i g ↦ d.χ_rep i g) rfl
  filter_upwards [d.tendsto_RA_germ.eventually (gt_mem_nhds hδ), d.eventually_good_germ]
    with i hi hG g y x _ hu
  exact (d.aI_dist hG hu).trans_lt hi

theorem hatT_rep_one_val (i : ℕ) {g : d.G i} (hg : g = 1) (x : Fin n → AddCircle (16 : ℝ)) :
    d.hatT (d.rep i g).val x = x := by
  rw [hg, rep_one, PadicTail.val_one, hatT_zero]

theorem norm_le_half_of_bufPt {x : Fin n → AddCircle (16 : ℝ)} (hx : d.bufPt x) :
    ‖liftVec 16 x‖ ≤ 1 / 2 := by
  linarith [d.norm_liftVec_of_bufPt hx, d.ρ_add_two_D_lt]

/-- **`B_{g,h}` has graph type `gh` on the buffer**, uniformly (Lemma 8.2). -/
theorem B_buf : GraphTendsto d.bufW (fun i q ↦ d.π i (q.1 * q.2)) (fun i q ↦ (d.BI i q).h)
    d.labW d.labW := by
  refine (d.graphTendsto_buf (fun i ↦ cW i) (fun i ↦ cW i) _ (fun i q ↦ d.rep i (q.1 * q.2))
    fun δ hδ ↦ ?_).congr (funext₂ fun i q ↦ d.χ_rep i _) rfl
  obtain ⟨δ₁, -, hev⟩ := d.eventually_B_params hδ
  filter_upwards [hev] with i ⟨hG, h₁, _, h₃⟩ q y x hx hu
  have := d.BT_inner hG _ _ _ (d.cocycle i q.1 q.2).val_mem (d.rep_add_rep i q.1 q.2)
    (d.BI_ne_zero hG hu) (d.norm_le_half_of_bufPt hx)
  have := d.hatModulus_mono (norm_nonneg _) (h₃ q.1 q.2 _ (by
    linarith [d.norm_le_half_of_bufPt hx]))
  linarith

/-- **`U_g` is local (type `1`) on the buffer.** -/
theorem U_buf : GraphTendsto d.bufW (fun _ (_ : d.G _) ↦ (1 : d.Cp)) (fun i g ↦ (d.UI i g).h)
    d.labW d.labW := by
  refine (d.graphTendsto_buf (fun i ↦ cW i) (fun i ↦ cW i) _ (fun _ _ ↦ 1)
    fun δ hδ ↦ ?_).congr (funext₂ fun _ _ ↦ map_one _) rfl
  filter_upwards [d.tendsto_TU_germ.eventually (gt_mem_nhds hδ), d.eventually_good_germ]
    with i hi hG g y x _ hu
  rw [PadicTail.val_one, hatT_zero]
  exact (d.UI_dist hG hu).trans_lt hi


theorem l2_cW_le_of_bufPt {i : ℕ} {x : (W n i).X} (hx : d.bufW i x) :
    l2 (cW i x) 0 ≤ d.ρ + 2 * d.D := by
  rw [← norm_liftVec_eq]; exact d.norm_liftVec_of_bufPt hx

/-- The second term `U b^*` of `V` lands near `ĥ_g(x)` (via `ĥ_g ĥ_{g⁻¹} = k_{g,g⁻¹}`). -/
theorem V_term₂_dist {i : ℕ} (hG : d.Good (germMesh i)) {g : d.G i} {δ δ₃ : ℝ} (hδ : 0 < δ)
    (hδB' : √n * (d.RA (germMesh i) * mesh 16 (germMesh i)) < 1 / 32)
    (hωRAδ : d.hatModulus (d.RA (germMesh i) * mesh 16 (germMesh i)) < δ / 4)
    (hTU : ((d.TU (germMesh i) : ℝ) + 1) * mesh 16 (germMesh i) < δ / 4) (hδ₃ : δ₃ ≤ δ / 4)
    (hdisp : ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ ≤ 2 →
      ‖d.chartAct (d.cocycle i g g⁻¹).val v - v‖ < δ₃)
    {y x l : (W n i).X} (hx : d.bufW i x) (hU : (d.UI i g).h y l ≠ 0)
    (hb : (d.aI i g⁻¹).f x l ≠ 0) : dist (cW i y) (d.hatT (d.rep i g).val (cW i x)) < δ := by
  have hρ := d.ρ_lt.trans d.ρplus_lt
  have hD := d.D_lt
  have hx2 := d.l2_cW_le_of_bufPt hx
  have e₁ := d.UI_dist hG hU
  have e₂ := d.aI_dist hG hb
  have hl : ‖liftVec 16 (cW i l)‖ ≤ 1 / 2 := by
    rw [norm_liftVec_eq]
    have h₁ := l2_triangle (cW i l) (d.hatT (d.rep i g⁻¹).val (cW i l)) 0
    have h₂ := l2_triangle (d.hatT (d.rep i g⁻¹).val (cW i l)) (cW i x) 0
    have h₃ := d.l2_hatT_le (d.rep i g⁻¹).val_mem (cW i l)
    have h₄ := l2_le_sqrt_mul_dist (d.hatT (d.rep i g⁻¹).val (cW i l)) (cW i x)
    have h₅ : √n * dist (d.hatT (d.rep i g⁻¹).val (cW i l)) (cW i x) ≤
        √n * (d.RA (germMesh i) * mesh 16 (germMesh i)) := by
      rw [dist_comm]; gcongr
    have h₆ := l2_comm (cW i l) (d.hatT (d.rep i g⁻¹).val (cW i l))
    linarith
  have hcomp := d.hatT_hatT_of_le (d.rep i g).val_mem (d.rep i g⁻¹).val_mem
    (d.cocycle i g g⁻¹).val_mem (d.rep_add_rep i g g⁻¹) hl
  rw [d.hatT_rep_one_val i (mul_inv_cancel g)] at hcomp
  set w := toTorus (d.chartAct (d.cocycle i g g⁻¹).val (liftVec 16 (cW i l)))
  have e₃ : dist w (cW i l) < δ₃ :=
    (d.dist_toTorus_chartAct_le _ (cW i l)).trans_lt (hdisp _ (by linarith))
  have e₄ := d.dist_hatT_le_hatModulus (d.rep i g).val_mem e₂
  rw [hcomp] at e₄
  have h₇ := dist_triangle4 (cW i y) (cW i l) w (d.hatT (d.rep i g).val (cW i x))
  have h₈ := dist_comm w (cW i l)
  have h₉ := dist_comm (d.hatT (d.rep i g).val (cW i x)) w
  linarith

/-- The first term `-a φ K` of `V` lands near `ĥ_g(x)` (via `ĥ_{g⁻¹} ĥ_g = k_{g⁻¹,g}`). -/
theorem V_term₁_dist {i : ℕ} (hG : d.Good (germMesh i)) {g : d.G i} {δ δ₁ δ₂ : ℝ}
    (hω₂ : d.hatModulus δ₂ ≤ δ / 2) (hω₁ : d.hatModulus δ₁ ≤ δ₂ / 3)
    (hδB : d.δB (germMesh i) < δ₂ / 3) (hδB' : √n * d.δB (germMesh i) < 1 / 32)
    (hRAδ : d.RA (germMesh i) * mesh 16 (germMesh i) < δ / 2)
    (hη : mesh 16 (germMesh i) < 2 * δ₂ / 3)
    (hdisp : ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ ≤ 2 →
      ‖d.chartAct (d.cocycle i g⁻¹ g).val v - v‖ < δ₁)
    {y x κ l : (W n i).X} (hx : d.bufW i x) (hT : (d.TI i g).h x κ ≠ 0)
    (ha : (d.aI i g).f y l ≠ 0) (hφ : (phiI n i).f l κ ≠ 0) :
    dist (cW i y) (d.hatT (d.rep i g).val (cW i x)) < δ := by
  have hρ := d.ρ_lt.trans d.ρplus_lt
  have hD := d.D_lt
  have hx2 := d.l2_cW_le_of_bufPt hx
  rw [TI_h] at hT
  have hBT := d.BI_ne_zero (q := (g⁻¹, g)) hG hT
  have hl2 := d.BT_l2 hG _ _ _ hBT
  have hκ : ‖liftVec 16 (cW i κ)‖ ≤ 1 / 2 := by
    rw [norm_liftVec_eq]
    have h₁ := l2_triangle (cW i κ) (cW i x) 0
    have h₂ := l2_comm (cW i x) (cW i κ)
    linarith
  have hin := d.BT_inner hG _ _ _ (d.cocycle i g⁻¹ g).val_mem (d.rep_add_rep i g⁻¹ g) hBT hκ
  rw [d.hatT_rep_one_val i (inv_mul_cancel g)] at hin
  have hωd := d.hatModulus_mono (norm_nonneg _) (hdisp _ (by linarith)).le
  have e₁ := d.aI_dist hG ha
  have e₂ := phiW_dist hφ
  have hlx : dist (cW i l) (cW i x) ≤ δ₂ := by
    have h₁ := dist_triangle (cW i l) (cW i κ) (cW i x)
    have h₂ := dist_comm (cW i x) (cW i κ)
    linarith
  have e₃ := d.dist_hatT_le_hatModulus (d.rep i g).val_mem hlx
  have h₄ := dist_triangle (cW i y) (d.hatT (d.rep i g).val (cW i l))
    (d.hatT (d.rep i g).val (cW i x))
  linarith

theorem TI_ne_zero_of {i : ℕ} {g : d.G i} {κ x : (W n i).X} {c : ℚ}
    (h : (-(c • ((d.TI i g).hᵀ * (W n i).sgn))) κ x ≠ 0) : (d.TI i g).h x κ ≠ 0 := by
  intro h0
  apply h
  rw [Matrix.neg_apply, Matrix.smul_apply, sgn, mul_diagonal, transpose_apply, h0, zero_mul, smul_zero, neg_zero]

/-- **`V_g` has graph type `g` on the buffer**, uniformly (l.705): on the inner region the tracks
`ĥ_g ĥ_{g⁻¹} = k_{g,g⁻¹}` and `ĥ_{g⁻¹} ĥ_g = k_{g⁻¹,g}` are `d_i`-small, so both `-a φ K` and
`U b^*` land near `ĥ_g(x)`. -/
theorem V_buf : GraphTendsto d.bufW (fun i g ↦ d.π i g) (fun i g ↦ (d.VI i g).h) d.labW d.labW := by
  refine (d.graphTendsto_buf (fun i ↦ cW i) (fun i ↦ cW i) _ (fun i g ↦ d.rep i g)
    fun δ hδ ↦ ?_).congr (funext₂ fun i g ↦ d.χ_rep i g) rfl
  obtain ⟨δ₂, hδ₂, hω₂⟩ := d.exists_hatModulus_le (half_pos hδ)
  obtain ⟨δ₁, hδ₁, hω₁⟩ := d.exists_hatModulus_le (show 0 < δ₂ / 3 by positivity)
  have hδ₃ : 0 < min δ₁ (δ / 4) := lt_min hδ₁ (by positivity)
  have hB := tendsto_comp_germ d.tendsto_δB
  have hRA := d.tendsto_RA_germ
  have hωRA := d.tendsto_hatModulus (fun i ↦ d.RA_mul_nonneg _) hRA
  filter_upwards [d.eventually_good_germ, hB.eventually (gt_mem_nhds (show (0 : ℝ) < δ₂ / 3 by
      positivity)),
    (hB.const_mul √n).eventually (gt_mem_nhds (by simp : (√n * 0 : ℝ) < 1 / 32)),
    (hRA.const_mul √n).eventually (gt_mem_nhds (by simp : (√n * 0 : ℝ) < 1 / 32)),
    hRA.eventually (gt_mem_nhds (half_pos hδ)),
    hωRA.eventually (gt_mem_nhds (show (0 : ℝ) < δ / 4 by positivity)),
    d.tendsto_TU_germ.eventually (gt_mem_nhds (show (0 : ℝ) < δ / 4 by positivity)),
    tendsto_mesh_germ.eventually (gt_mem_nhds (show (0 : ℝ) < 2 * δ₂ / 3 by positivity)),
    d.eventually_cocycle_chartAct_lt hδ₃]
    with i hG hδB hδB' hRA' hRAδ hωRAδ hTU hη hdisp g y x hx hu
  rw [VI_h, Matrix.add_apply] at hu
  by_cases h1 : (((d.aI i g).f * (phiI n i).f) * (-(((-(-1 : ℚ) ^ (n + 4)) •
      ((d.TI i g).hᵀ * (W n i).sgn))))) y x = 0
  · rw [h1, zero_add] at hu
    obtain ⟨l, hU, hb⟩ := exists_mul_apply_ne_zero hu
    rw [transpose_apply] at hb
    exact d.V_term₂_dist hG hδ hRA' hωRAδ hTU (min_le_right _ _) (hdisp g g⁻¹) hx hU hb
  · obtain ⟨κ, haφ, hK⟩ := exists_mul_apply_ne_zero h1
    obtain ⟨l, ha, hφ⟩ := exists_mul_apply_ne_zero haφ
    exact d.V_term₁_dist hG hω₂ hω₁ hδB hδB' hRAδ hη
      (fun v hv ↦ (hdisp g⁻¹ g v hv).trans_le (min_le_left _ _)) hx (d.TI_ne_zero_of hK) ha hφ

end Buffered

/-! ### The far subcomplexes `F_i` (l.710) -/

section Far

variable [ContinuousVAdd ℤ_[p] M] [LocallyCompactSpace M] [FirstCountableTopology M]

/-- The far cells: closed torus carrier missing `f⁻¹B̄(y, t)` (l.710). -/
def farW (i : ℕ) (q : (W n i).X) : Prop :=
  (torus.geometry 16 (germMesh i) n).carrierFar {x | dist d.yS (d.torusLabel x) ≤ d.t} q.1

theorem isSub_farW (i : ℕ) : (W n i).IsSub (d.farW i) :=
  isSub_fst (Geometry.isSub_carrierFar _ _)

theorem farW_dist {i : ℕ} {q : (W n i).X} (h : d.farW i q) : d.t < dist d.yS (d.seqW.label i q) := by
  have := Geometry.center_notMem_of_carrierFar h
  rw [torus.geometry_center] at this
  exact not_le.mp this

/-- The retained cells are eventually buffered (`t < u`, l.721). -/
theorem near_bufW : ∀ᶠ i in atTop, ∀ q, ¬d.farW i q → d.bufPt (cW i q) := by
  obtain ⟨δ, hδ, hf⟩ := Metric.uniformContinuous_iff.mp d.uniformContinuous_torusLabel
    (d.u - d.t) (by linarith [d.t_lt_u])
  filter_upwards [tendsto_mesh_germ.eventually (gt_mem_nhds (show (0 : ℝ) < δ by linarith))]
    with i hi q hq
  obtain ⟨x, hx, hxK⟩ := Set.not_disjoint_iff.mp hq
  have h₁ := torus.dist_center_le_of_mem 16 (germMesh i) n hx
  have h₂ : dist (d.torusLabel (cW i q)) (d.torusLabel x) < d.u - d.t :=
    hf (by rw [dist_comm]; linarith [mesh_nonneg (germMesh i)])
  have h₃ := dist_triangle d.yS (d.torusLabel x) (d.torusLabel (cW i q))
  have h₄ : dist d.yS (d.torusLabel x) ≤ d.t := hxK
  change dist d.yS (d.torusLabel (cW i q)) ≤ d.u
  linarith [dist_comm (d.torusLabel (cW i q)) (d.torusLabel x)]

end Far

/-! ### `ChainModelData` -/

section Data

variable [ContinuousVAdd ℤ_[p] M] [LocallyCompactSpace M] [FirstCountableTopology M]

theorem seqW_dimLE : d.seqW.DimLE (n + 4) := fun i ↦ torusCP.dimLE (germMesh i) n

/-- **Lemma 8.1** on `W_i`: the controlled strictly symmetric duality `φ_i = torusCP.duality`
(the germ's duality), with `b`, `H`, `H'` all `f`-controlled. -/
def seqWDuality : d.seqW.SymDuality (n + 4) d.seqW_dimLE :=
  let e := torusCP.controlledDuality 16 n germMesh tendsto_germMesh d.torusLabel
    d.continuous_torusLabel
  ControlledSeq.SymDuality.ofSeq (fun i ↦ torusCP.duality (germMesh i) n) e.hom.tendsto
    e.inv.tendsto e.homInv.tendsto e.invHom.tendsto

theorem seqWDuality_hom (i : ℕ) : (d.seqWDuality.hom.f i) = (torusCP.duality (germMesh i) n).hom :=
  rfl

/-- `f`-control of a family in the form of `Prop92.UnifPropTendsto`. -/
theorem unifProp_of_graphTendsto {J : ℕ → Type*} {θ : ∀ i, J i → d.Cp}
    {u : ∀ i, J i → Matrix (W n i).X (W n i).X ℚ}
    (h : GraphTendsto (fun _ _ ↦ True) θ u d.seqW.label d.seqW.label) :
    Tendsto (fun i ↦ ⨆ j, prop (u i j) (d.seqW.label i) (d.seqW.label i)) atTop (𝓝 0) :=
  tendsto_zero_of_le h fun i ↦ iSup_le fun j ↦ by
    have := graphPropOn_le_graphErr (buf := fun _ _ ↦ True) (θ := θ) (u := u)
      (a := d.seqW.label) (b := d.seqW.label) i j
    exact (propOn_true (u := u i j) (source := d.seqW.label i)
      (target := d.seqW.label i)).symm.le.trans this

end Data

/-- **The chain-model data of §8** (Lemmas 8.1–8.2, (8.1)–(8.7)) for the fixed data `d`, on the
germ chain models `D_i = W_i = Tⁿ_{i+2} ⊗ CPcell` (`seqW`, labels `f̂ ∘ lift ∘ centre`), with the
field layout of `HSFormal.Prop92.ChainModelInput` for `cd = d.control`, `π = d.π`
(`(ρ̃, f)`-labels `(ρ i σ, seqW.label i σ)`; the pair `gh = (g, h)` for `B`), plus (8.4) and the
slant homotopies `U_g`. All bounds are uniform in `g, h ∈ G_i`. -/
structure ChainModelData (d : FixedData p n M) [ContinuousVAdd ℤ_[p] M] [LocallyCompactSpace M]
    [FirstCountableTopology M] where
  /-- The `T`-coordinate `ρ̃` of the cells. -/
  ρ : ∀ i, (W n i).X → sphere (0 : EuclideanSpace ℂ (Fin d.m)) 1
  /-- The buffered region. -/
  buf : ∀ i, (W n i).X → Prop
  /-- The far subcomplexes `F_i`. -/
  far : ∀ i, (W n i).X → Prop
  [decFar : ∀ i, DecidablePred (far i)]
  isSub_far : ∀ i, (W n i).IsSub (far i)
  /-- The radius `t` of (7.8). -/
  t : ℝ
  R_lt_t : d.R < t
  far_dist : ∀ i σ, far i σ → t < dist d.yS (d.seqW.label i σ)
  near_buf : ∀ᶠ i in atTop, ∀ σ, ¬far i σ → buf i σ
  d_buf : PropTendstoOn buf (fun i ↦ (W n i).d) (fun i σ ↦ (ρ i σ, d.seqW.label i σ))
    (fun i σ ↦ (ρ i σ, d.seqW.label i σ))
  φ_buf : PropTendstoOn buf (fun i ↦ (d.seqWDuality.hom.f i).f)
    (fun i σ ↦ (ρ i σ, d.seqW.label i σ)) (fun i σ ↦ (ρ i σ, d.seqW.label i σ))
  b_buf : PropTendstoOn buf (fun i ↦ (d.seqWDuality.inv.f i).f)
    (fun i σ ↦ (ρ i σ, d.seqW.label i σ)) (fun i σ ↦ (ρ i σ, d.seqW.label i σ))
  homInv_buf : PropTendstoOn buf (fun i ↦ (d.seqWDuality.homInv.h i).h)
    (fun i σ ↦ (ρ i σ, d.seqW.label i σ)) (fun i σ ↦ (ρ i σ, d.seqW.label i σ))
  invHom_buf : PropTendstoOn buf (fun i ↦ (d.seqWDuality.invHom.h i).h)
    (fun i σ ↦ (ρ i σ, d.seqW.label i σ)) (fun i σ ↦ (ρ i σ, d.seqW.label i σ))
  /-- The chain approximations `a_g` of `ĥ_g × 1`, (8.1)–(8.3). -/
  a : ∀ i, d.G i → Hom (W n i) (W n i)
  a_one : ∀ i, a i 1 = Hom.id (W n i)
  /-- (8.4) `a_g z = z` exactly. -/
  a_z : ∀ i g, (a i g).f *ᵥ torusCP.z (germMesh i) n = torusCP.z (germMesh i) n
  a_f : Tendsto (fun i ↦ ⨆ g, prop (a i g).f (d.seqW.label i) (d.seqW.label i)) atTop (𝓝 0)
  a_buf : GraphTendsto buf (fun i g ↦ d.π i g) (fun i g ↦ (a i g).f)
    (fun i σ ↦ (ρ i σ, d.seqW.label i σ)) (fun i σ ↦ (ρ i σ, d.seqW.label i σ))
  /-- Lemma 8.2, (8.5): `a_g a_h - a_{gh} = dB_{g,h} + B_{g,h}d`. -/
  B : ∀ i (gh : d.G i × d.G i), Htpy ((a i gh.1).comp (a i gh.2)) (a i (gh.1 * gh.2))
  B_f : Tendsto (fun i ↦ ⨆ gh, prop (B i gh).h (d.seqW.label i) (d.seqW.label i)) atTop (𝓝 0)
  B_buf : GraphTendsto buf (fun i gh ↦ d.π i (gh.1 * gh.2)) (fun i gh ↦ (B i gh).h)
    (fun i σ ↦ (ρ i σ, d.seqW.label i σ)) (fun i σ ↦ (ρ i σ, d.seqW.label i σ))
  /-- (8.6): `a_g φ a_g^* - φ = dU_g + U_g δ`. -/
  U : ∀ i (g : d.G i), Htpy (((a i g).comp (d.seqWDuality.hom.f i)).comp
    ((a i g).dual (n + 4) (d.seqW_dimLE i) (d.seqW_dimLE i))) (d.seqWDuality.hom.f i)
  U_f : Tendsto (fun i ↦ ⨆ g, prop (U i g).h (d.seqW.label i) (d.seqW.label i)) atTop (𝓝 0)
  U_buf : GraphTendsto buf (fun _ (_ : d.G _) ↦ (1 : d.Cp)) (fun i g ↦ (U i g).h)
    (fun i σ ↦ (ρ i σ, d.seqW.label i σ)) (fun i σ ↦ (ρ i σ, d.seqW.label i σ))
  /-- (8.7): `a_g φ - φ a_{g⁻¹}^* = dV_g + V_g δ`, `V = -a φ K + U b^*`. -/
  V : ∀ i (g : d.G i), Htpy ((a i g).comp (d.seqWDuality.hom.f i))
    ((d.seqWDuality.hom.f i).comp ((a i g⁻¹).dual (n + 4) (d.seqW_dimLE i) (d.seqW_dimLE i)))
  V_f : Tendsto (fun i ↦ ⨆ g, prop (V i g).h (d.seqW.label i) (d.seqW.label i)) atTop (𝓝 0)
  V_buf : GraphTendsto buf (fun i g ↦ d.π i g) (fun i g ↦ (V i g).h)
    (fun i σ ↦ (ρ i σ, d.seqW.label i σ)) (fun i σ ↦ (ρ i σ, d.seqW.label i σ))

variable [ContinuousVAdd ℤ_[p] M] [LocallyCompactSpace M] [FirstCountableTopology M] [T2Space M]

open scoped Classical in
/-- **The chain-model data exist** (Lemmas 8.1–8.2 on the cubical germ models). -/
def chainModelData : ChainModelData d where
  ρ := d.rhoW
  buf := d.bufW
  far := d.farW
  isSub_far := d.isSub_farW
  t := d.t
  R_lt_t := d.R_lt_t
  far_dist _ _ h := d.farW_dist h
  near_buf := d.near_bufW
  d_buf := d.d_buf
  φ_buf := d.phi_buf
  b_buf := d.inv_buf
  homInv_buf := d.homInv_buf
  invHom_buf := d.invHom_buf
  a := d.aI
  a_one := d.aI_one
  a_z := d.aI_z
  a_f := d.unifProp_of_graphTendsto d.graphTendsto_aI
  a_buf := d.a_buf
  B := d.BI
  B_f := d.unifProp_of_graphTendsto d.graphTendsto_BI
  B_buf := d.B_buf
  U := d.UI
  U_f := d.unifProp_of_graphTendsto d.graphTendsto_UI
  U_buf := d.U_buf
  V := d.VI
  V_f := d.unifProp_of_graphTendsto d.graphTendsto_VI
  V_buf := d.V_buf

/-- The chain models are literally the germ complexes of `HSFormal.manifoldGerm` for `c = f̂`. -/
theorem seqW_label_germ (i : ℕ) (σ : (W n i).X) :
    d.seqW.label i σ = d.fhatS (germCollapse n (torus.center 16 (germMesh i) n σ.1)) :=
  (d.fhatS_germCollapse _).symm

end HSFormal.FixedData
