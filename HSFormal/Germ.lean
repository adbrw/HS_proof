import HSFormal.Assembly
import HSFormal.Cubical.CylinderInvariance
import HSFormal.Cubical.GridSeam

/-!
# The manifold germ `Tⁿ_{m_i} ⊗ CPcell` and its homotopy invariance (cubical modules C5, C7)

The interface `ManifoldGerm` of `HSFormal.Assembly`, realized by the cubical torus model, and the
step `GermHomotopyInvariance` (Lemma 11.1, (11.3)).

* `chartCollapse : Sⁿ → Sⁿ`: `v ↦ v / d(v)` with `d(v) = min 1 ((6 - ‖v‖_∞)/2)`, `∞ ↦ ∞`; the
  identity on the cube `‖v‖_∞ ≤ 4`, `∞` on `‖v‖_∞ ≥ 6`, and it pushes points outwards
  (`‖v‖_∞ ≤ ‖w‖_∞` if `v ↦ w`). Here `‖v‖_∞ = ‖WithLp.ofLp v‖` is the sup norm of the chart
  coordinates.
* `germCollapse n : (ℝ/16ℤ)ⁿ → Sⁿ`: `chartCollapse` of the chart lift `liftVec 16` to
  `[-8, 8)ⁿ`; continuous across the seam (`continuous_comp_liftVec_supNorm`). It equals the chart
  lift on the cube `‖x‖ ≤ 4` (`germCollapse_of_norm_le`; `‖x‖` is the sup norm of the torus,
  `= ‖liftVec x‖_∞`, `norm_ofLp_liftVec`), maps `‖x‖ ≥ 4` into `{‖w‖_∞ ≥ 4} ∪ {∞}`
  (`germCollapse_far`), so control maps that are `∞` on `‖w‖_∞ ≥ 4` see only the lift
  (`comp_germCollapse`); in particular `f̂ ∘ q = FixedData.torusLabel` (`fhatS_germCollapse`).
* `manifoldGerm`: the class in `Lconc_{n+4}(𝒜_1(Sⁿ))` of `W_i = Tⁿ_{m_i} ⊗ CPcell` on
  `(ℝ/16ℤ)ⁿ`, mesh `16/m_i`, `m_i = i + 2` (`germMesh`, `≥ 2` for cell locality, `→ ∞`), the cell
  `σ ⊗ e` labelled by `(c ∘ q)(centre σ)`. The asymptotic category is `cd.A1S` on the nose
  (`scalarHom cd.Cp`, label space `RoundSphere cd.n` with the trivial isometric action), and
  `↑(n + 4) = ↑n + 4 = cd.N` holds by `rfl`, so no relabelling or cast is needed.
* `germHomotopyInvariance : GermHomotopyInvariance manifoldGerm` (from
  `torusCP.cls_eq_of_homotopic`, applied to `c₀ ∘ q ≃ c₁ ∘ q`).
-/

noncomputable section

namespace HSFormal

open Filter Topology OnePoint Metric LTheory Cubical Cubical.BasedComplex

/-! ### The collapse of the chart sphere -/

section ChartCollapse

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem norm_ofLp_le_norm (v : E) : ‖WithLp.ofLp v‖ ≤ ‖v‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 fun i ↦ PiLp.norm_apply_le v i

/-- The radial factor `d(v) = min 1 ((6 - ‖v‖_∞) / 2)`: `1` on `‖v‖_∞ ≤ 4`, `≤ 0` exactly on
`‖v‖_∞ ≥ 6`. -/
def collapseDen (v : E) : ℝ := min 1 ((6 - ‖WithLp.ofLp v‖) / 2)

theorem continuous_collapseDen : Continuous (collapseDen (n := n)) :=
  continuous_const.min ((continuous_const.sub
    (continuous_norm.comp (PiLp.continuous_ofLp 2 _))).div_const 2)

theorem collapseDen_le_one (v : E) : collapseDen v ≤ 1 := min_le_left _ _

theorem collapseDen_of_le {v : E} (hv : ‖WithLp.ofLp v‖ ≤ 4) : collapseDen v = 1 :=
  min_eq_left (by linarith)

theorem collapseDen_pos_iff {v : E} : 0 < collapseDen v ↔ ‖WithLp.ofLp v‖ < 6 := by
  rw [collapseDen, lt_min_iff]
  constructor
  · rintro ⟨-, h⟩; linarith
  · intro h; exact ⟨one_pos, by linarith⟩

/-- **The collapse `Sⁿ → Sⁿ`**: `v ↦ v / d(v)` on `‖v‖_∞ < 6`, `∞` elsewhere. -/
def chartCollapse : C(OnePoint E, OnePoint E) where
  toFun z := z.elim ∞ fun v ↦ divOrInfty (collapseDen v) v
  continuous_toFun := by
    refine continuous_elim (continuous_divOrInfty continuous_collapseDen continuous_id
      fun v hv h0 ↦ ?_) fun s hs ↦ ?_
    · subst h0
      have : 0 < collapseDen (0 : E) := collapseDen_pos_iff.2 (by simp)
      linarith
    · have hK : IsCompact (WithLp.toLp 2 '' closedBall (0 : Fin n → ℝ) 6 : Set E) :=
        (isCompact_closedBall _ _).image (PiLp.continuous_toLp 2 _)
      refine ⟨_, hK.isClosed, hK, fun v hv ↦ ?_⟩
      have h6 : 6 ≤ ‖WithLp.ofLp v‖ := by
        by_contra h
        exact hv ⟨WithLp.ofLp v, mem_closedBall_zero_iff.2 (not_le.1 h).le, rfl⟩
      rw [divOrInfty_of_nonpos (not_lt.1 (mt collapseDen_pos_iff.1 (not_lt.2 h6)))]
      exact mem_of_mem_nhds hs

@[simp]
theorem chartCollapse_infty : chartCollapse (n := n) ∞ = ∞ := rfl

theorem chartCollapse_coe (v : E) :
    chartCollapse (v : OnePoint E) = divOrInfty (collapseDen v) v := rfl

/-- The collapse is the identity on the cube `‖v‖_∞ ≤ 4`. -/
theorem chartCollapse_coe_of_le {v : E} (hv : ‖WithLp.ofLp v‖ ≤ 4) :
    chartCollapse (v : OnePoint E) = v := by
  rw [chartCollapse_coe, collapseDen_of_le hv, divOrInfty_of_pos one_pos, inv_one, one_smul]

/-- The collapse is `∞` on `‖v‖_∞ ≥ 6`. -/
theorem chartCollapse_coe_of_ge {v : E} (hv : 6 ≤ ‖WithLp.ofLp v‖) :
    chartCollapse (v : OnePoint E) = ∞ := by
  rw [chartCollapse_coe, divOrInfty_of_nonpos (not_lt.1 (mt collapseDen_pos_iff.1 (not_lt.2 hv)))]

/-- The collapse pushes points outwards: `v ↦ w` implies `‖v‖_∞ ≤ ‖w‖_∞`. -/
theorem norm_le_of_chartCollapse_eq {v w : E} (h : chartCollapse (v : OnePoint E) = w) :
    ‖WithLp.ofLp v‖ ≤ ‖WithLp.ofLp w‖ := by
  rw [chartCollapse_coe] at h
  rcases lt_or_ge 0 (collapseDen v) with hd | hd
  · rw [divOrInfty_of_pos hd, OnePoint.coe_eq_coe] at h
    subst h
    rw [WithLp.ofLp_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hd.le)]
    exact le_mul_of_one_le_left (norm_nonneg _) (one_le_inv₀ hd |>.2 (collapseDen_le_one v))
  · rw [divOrInfty_of_nonpos hd] at h
    exact absurd h.symm (OnePoint.coe_ne_infty w)

/-- `{‖v‖_∞ ≥ 4}` is mapped into `{‖w‖_∞ ≥ 4} ∪ {∞}`. -/
theorem chartCollapse_far {v : E} (hv : 4 ≤ ‖WithLp.ofLp v‖) :
    chartCollapse (v : OnePoint E) = ∞ ∨
      ∃ w : E, chartCollapse (v : OnePoint E) = w ∧ 4 ≤ ‖WithLp.ofLp w‖ := by
  induction h : chartCollapse (v : OnePoint E) using OnePoint.rec with
  | infty => exact .inl rfl
  | coe w => exact .inr ⟨w, rfl, hv.trans (norm_le_of_chartCollapse_eq h)⟩

/-- A map that is constant on `{‖w‖_∞ ≥ 4} ∪ {∞}` does not see the collapse. -/
theorem comp_chartCollapse {Z : Type*} (c : OnePoint E → Z)
    (hc : ∀ w : E, 4 ≤ ‖WithLp.ofLp w‖ → c w = c ∞) (z : OnePoint E) :
    c (chartCollapse z) = c z := by
  induction z using OnePoint.rec with
  | infty => rfl
  | coe v =>
    rcases le_or_gt ‖WithLp.ofLp v‖ 4 with hv | hv
    · rw [chartCollapse_coe_of_le hv]
    · rw [hc v hv.le]
      rcases chartCollapse_far hv.le with h | ⟨w, h, hw⟩
      · rw [h]
      · rw [h, hc w hw]

end ChartCollapse

/-! ### Chart lifts across the seam, sup-norm version -/

section Lift

variable (L : ℝ) [Fact (0 < L)] {n : ℕ}

/-- The sup norm of the lift is the sup norm on the torus. -/
theorem norm_ofLp_liftVec (x : Fin n → AddCircle L) : ‖WithLp.ofLp (liftVec L x)‖ = ‖x‖ := by
  have h : ∀ i, ‖WithLp.ofLp (liftVec L x) i‖ = ‖x i‖ := fun i ↦ by
    rw [← abs_liftHalf, ← Real.norm_eq_abs]; rfl
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun i ↦ ?_)
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i ↦ ?_)
  · rw [h]; exact norm_le_pi_norm x i
  · rw [← h]; exact norm_le_pi_norm _ i

/-- **Labels across the seam, sup-norm version** of `continuous_comp_liftVec`: a continuous map on
`Sⁿ = OnePoint ℝⁿ` that is constant on `‖v‖_∞ ≥ r`, `r < L/2`, gives a continuous label on
`(ℝ/Lℤ)ⁿ` through the lift. -/
theorem continuous_comp_liftVec_supNorm {Z : Type*} [TopologicalSpace Z]
    {F : OnePoint (EuclideanSpace ℝ (Fin n)) → Z} (hF : Continuous F) {r : ℝ} (hr : r < L / 2)
    (hconst : ∀ v : EuclideanSpace ℝ (Fin n), r ≤ ‖WithLp.ofLp v‖ → F v = F ∞) :
    Continuous fun x ↦ F (liftVec L x : EuclideanSpace ℝ (Fin n)) := by
  have hL : (0 : ℝ) < L := Fact.out
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  rcases lt_or_ge r ‖x‖ with hx | hx
  · have hev : ∀ᶠ y in 𝓝 x, F (liftVec L y : EuclideanSpace ℝ (Fin n)) = F ∞ := by
      filter_upwards [continuous_norm.continuousAt.eventually (lt_mem_nhds hx)] with y hy
      exact hconst _ (by rw [norm_ofLp_liftVec]; exact hy.le)
    exact (continuousAt_const (y := F ∞)).congr (hev.mono fun _ h ↦ h.symm)
  · have hseam : ∀ i, x i ≠ ((-(L / 2) : ℝ) : AddCircle L) := fun i hi ↦ by
      have hnorm : ‖x i‖ = L / 2 := by
        rw [hi, (AddCircle.norm_coe_eq_abs_iff L hL.ne').mpr (by
          rw [abs_neg, abs_of_pos hL, abs_of_pos (by linarith)]), abs_neg,
          abs_of_pos (by linarith)]
      linarith [norm_le_pi_norm x i]
    have h₁ : ∀ i, ContinuousAt (fun y : Fin n → AddCircle L ↦ liftHalf L (y i)) x := fun i ↦
      (continuous_subtype_val.continuousAt.comp
        (AddCircle.continuousAt_equivIco L _ (hseam i))).comp
        (f := fun y : Fin n → AddCircle L ↦ y i) (continuous_apply i).continuousAt
    have h : ContinuousAt (liftVec L) x :=
      (PiLp.continuous_toLp 2 _).continuousAt.comp (continuousAt_pi.mpr h₁)
    exact hF.continuousAt.comp (OnePoint.continuous_coe.continuousAt.comp h)

end Lift

/-! ### The torus-to-sphere collapse `q` -/

section GermCollapse

variable (n : ℕ)

/-- **The collapse `q : (ℝ/16ℤ)ⁿ → Sⁿ`**: the chart lift to `[-8, 8)ⁿ` followed by
`chartCollapse`; the identity of the chart on the cube `‖x‖ ≤ 4`, `∞` on `‖x‖ ≥ 6`. -/
def germCollapse : C(Fin n → AddCircle (16 : ℝ), RoundSphere n) where
  toFun x := RoundSphere.toOnePoint.symm (chartCollapse (liftVec 16 x : OnePoint _))
  continuous_toFun := RoundSphere.toOnePoint.symm.continuous.comp <|
    continuous_comp_liftVec_supNorm 16 chartCollapse.continuous (r := 6) (by norm_num)
      fun _ hv ↦ chartCollapse_coe_of_ge hv

variable {n}

theorem germCollapse_apply (x : Fin n → AddCircle (16 : ℝ)) :
    germCollapse n x = RoundSphere.toOnePoint.symm (chartCollapse (liftVec 16 x : OnePoint _)) :=
  rfl

/-- `q` is the chart lift on the cube `‖x‖ ≤ 4` of the torus. -/
theorem germCollapse_of_norm_le {x : Fin n → AddCircle (16 : ℝ)} (hx : ‖x‖ ≤ 4) :
    germCollapse n x = RoundSphere.toOnePoint.symm (liftVec 16 x : OnePoint _) := by
  rw [germCollapse_apply, chartCollapse_coe_of_le (by rwa [norm_ofLp_liftVec])]

/-- `q = ∞` on `‖x‖ ≥ 6`. -/
theorem germCollapse_of_le_norm {x : Fin n → AddCircle (16 : ℝ)} (hx : 6 ≤ ‖x‖) :
    germCollapse n x = RoundSphere.infty := by
  rw [germCollapse_apply, chartCollapse_coe_of_ge (by rwa [norm_ofLp_liftVec])]; rfl

/-- `q` pushes outwards: `q x = w` implies `‖x‖ ≤ ‖w‖_∞`. -/
theorem norm_le_of_germCollapse_eq {x : Fin n → AddCircle (16 : ℝ)} {w : EuclideanSpace ℝ (Fin n)}
    (h : germCollapse n x = RoundSphere.toOnePoint.symm (w : OnePoint _)) :
    ‖x‖ ≤ ‖WithLp.ofLp w‖ := by
  rw [← norm_ofLp_liftVec 16]
  exact norm_le_of_chartCollapse_eq h

/-- `q x = w` with `‖w‖_∞ ≤ 4` forces `x` into the cube, with lift `w`. -/
theorem liftVec_eq_of_germCollapse_eq {x : Fin n → AddCircle (16 : ℝ)}
    {w : EuclideanSpace ℝ (Fin n)}
    (h : germCollapse n x = RoundSphere.toOnePoint.symm (w : OnePoint _))
    (hw : ‖WithLp.ofLp w‖ ≤ 4) : ‖x‖ ≤ 4 ∧ liftVec 16 x = w := by
  have hx := (norm_le_of_germCollapse_eq h).trans hw
  refine ⟨hx, ?_⟩
  rw [germCollapse_of_norm_le hx] at h
  exact OnePoint.coe_injective (RoundSphere.toOnePoint.symm.injective h)

/-- `q` maps `‖x‖ ≥ 4` into `{‖w‖_∞ ≥ 4} ∪ {∞}`. -/
theorem germCollapse_far {x : Fin n → AddCircle (16 : ℝ)} (hx : 4 ≤ ‖x‖) :
    germCollapse n x = RoundSphere.infty ∨ ∃ w : EuclideanSpace ℝ (Fin n),
      germCollapse n x = RoundSphere.toOnePoint.symm (w : OnePoint _) ∧ 4 ≤ ‖WithLp.ofLp w‖ :=
  chartCollapse_far (by rwa [norm_ofLp_liftVec])

/-- A control map that is constant on `{‖w‖_∞ ≥ 4} ∪ {∞}` sees only the chart lift: `c ∘ q` is
`c ∘ lift`. -/
theorem comp_germCollapse {Z : Type*} (c : RoundSphere n → Z)
    (hc : ∀ w : EuclideanSpace ℝ (Fin n), 4 ≤ ‖WithLp.ofLp w‖ →
      c (RoundSphere.toOnePoint.symm (w : OnePoint _)) = c RoundSphere.infty)
    (x : Fin n → AddCircle (16 : ℝ)) :
    c (germCollapse n x) = c (RoundSphere.toOnePoint.symm (liftVec 16 x : OnePoint _)) :=
  comp_chartCollapse (fun z ↦ c (RoundSphere.toOnePoint.symm z)) hc _

end GermCollapse

/-- `f̂ ∘ q = FixedData.torusLabel`: `f̂ = ∞` on `‖v‖ ≥ 2`, hence on `‖v‖_∞ ≥ 4`. -/
theorem FixedData.fhatS_germCollapse {p : ℕ} [Fact p.Prime] {n : ℕ} {M : Type*}
    [TopologicalSpace M] [AddAction ℤ_[p] M] [ContinuousVAdd ℤ_[p] M] [LocallyCompactSpace M]
    [FirstCountableTopology M] (d : FixedData p n M) (x : Fin n → AddCircle (16 : ℝ)) :
    d.fhatS (germCollapse n x) = d.torusLabel x :=
  comp_germCollapse d.fhatS (fun w hw ↦ by
    change d.fhat w = ∞
    rw [d.fhat_coe, ite_eq_right (not_lt.2 (by linarith [norm_ofLp_le_norm w]))]) x

/-! ### The manifold germ -/

/-- The mesh sequence `m_i = i + 2` of the germ: `≥ 2` (cell locality, `torusCP.local`) and
`→ ∞`. -/
def germMesh (i : ℕ) : ℕ := i + 2

instance (i : ℕ) : NeZero (germMesh i) := ⟨Nat.succ_ne_zero _⟩

theorem two_le_germMesh (i : ℕ) : 2 ≤ germMesh i := Nat.le_add_left 2 i

theorem tendsto_germMesh : Tendsto germMesh atTop atTop :=
  tendsto_add_atTop_nat 2

/-- The germ `W_i = Tⁿ_{m_i} ⊗ CPcell` labelled by `(c ∘ q)(centre σ)` is controlled over `Sⁿ`. -/
theorem germ_isControlledDuality (n : ℕ) (c : C(RoundSphere n, RoundSphere n)) :
    IsControlledDuality (fun i ↦ torusCP.duality (germMesh i) n)
      fun i σ ↦ c (germCollapse n (torus.center 16 (germMesh i) n σ.1)) :=
  (torusCP.isControlledDuality 16 n tendsto_germMesh).comp
    (CompactSpace.uniformContinuous_of_continuous (c.comp (germCollapse n)).continuous)

/-- **The manifold germ** (`ManifoldGerm`): the class in `Lconc_{n+4}(𝒜_1(Sⁿ))` of the cubical
torus model `W_i = Tⁿ_{m_i} ⊗ CPcell` on `(ℝ/16ℤ)ⁿ`, `m_i = i + 2` (mesh `16/m_i`), with the
torus Serre cap tensored with the duality of `CPcell`, the cell `σ ⊗ e` labelled by
`(c ∘ q)(centre σ)`, `q = germCollapse`. -/
def manifoldGerm : ManifoldGerm := fun _ cd c ↦
  Lconc.cls ((germ_isControlledDuality cd.n c).toAsymptotic (scalarHom cd.Cp))

theorem manifoldGerm_def {p : ℕ} (cd : ControlData p) (c : C(RoundSphere cd.n, RoundSphere cd.n)) :
    manifoldGerm cd c =
      Lconc.cls ((germ_isControlledDuality cd.n c).toAsymptotic (scalarHom cd.Cp)) :=
  rfl

/-- **S10: Lemma 11.1 and (11.3)** for the cubical germ: homotopic control maps `c₀ ≃ c₁` give
homotopic labels `c₀ ∘ q ≃ c₁ ∘ q` on the torus, hence equal classes
(`torusCP.cls_eq_of_homotopic`). -/
theorem germHomotopyInvariance : GermHomotopyInvariance manifoldGerm := by
  intro p _ cd c₀ c₁ h
  have := torusCP.cls_eq_of_homotopic (scalarHom cd.Cp) 16 cd.n tendsto_germMesh
    (h.comp (ContinuousMap.Homotopic.refl (germCollapse cd.n)))
  rw [manifoldGerm_def, manifoldGerm_def]
  exact this

/-- The germ of `f̂` for the control data of the fixed data is labelled by
`FixedData.torusLabel ∘ centre` (`f̂ ∘ q = f̂ ∘ lift`). -/
theorem FixedData.manifoldGerm_fhatS {p : ℕ} [Fact p.Prime] {n : ℕ} {M : Type*}
    [TopologicalSpace M] [AddAction ℤ_[p] M] [ContinuousVAdd ℤ_[p] M] [LocallyCompactSpace M]
    [FirstCountableTopology M] (d : FixedData p n M) :
    manifoldGerm d.control d.fhatS =
      Lconc.cls (((torusCP.isControlledDuality 16 n tendsto_germMesh).comp
        (CompactSpace.uniformContinuous_of_continuous d.continuous_torusLabel)).toAsymptotic
          (scalarHom d.Cp)) :=
  IsControlledDuality.cls_toAsymptotic_congr _ _ _
    (funext fun _ ↦ funext fun _ ↦ d.fhatS_germCollapse _)

end HSFormal
