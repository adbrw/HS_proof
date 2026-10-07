import HSFormal.Cubical.Filling
import HSFormal.TailGroups

/-!
# The completed maps `ĥ` on the torus (cubical module C6, part 1)

Manuscript (8.1)–(8.3) (l.596–613) on the torus `(ℝ/16ℤ)ⁿ ⊇ [-8, 8)ⁿ ⊇ B(0, 4)` of the chain
models `W_i = Tⁿ_{m_i} ⊗ CPcell`:

* `FixedData.hatT a`: for `a ∈ ℤ_[p]`, `x ↦ x + θ(|x|)(a x - x)` in chart coordinates of the lift
  (`chartAct a v = φ(a +ᵥ φ⁻¹ v)`, cutoff `θ = 1` on `B(0,1)`, `θ = 0` off `B(0,3/2)`), and the
  identity elsewhere (`hatT_apply`); `hatT 0 = id` (`hatT_zero`).
* Displacement `≤ D` in every coordinate and in `ℓ²` (`dist_hatT_le`, `l2_hatT_le`); on
  `B(0, 1)` it is the action (`liftVec_hatT_of_le_one`).
* (8.2) `f ĥ = f` exactly (`torusLabel_hatT`), using fix 5 of `cubical-review.md`
  (`|ĥ x| ≥ 1 - D > ρ + 2D` off `B(0,1)`).
* **Equicontinuity** of the compact family `{ĥ_a : a ∈ H}` (l.570): one modulus `ω`
  (`hatModulus`) with `dist (ĥ_a x) (ĥ_a y) ≤ ω (dist x y)` and `ω δ → 0` as `δ → 0`, from joint
  continuity on `H × (ℝ/16ℤ)ⁿ` (`continuousOn_hatDisp`).
-/

noncomputable section

set_option linter.unusedSectionVars false

open Filter Metric Topology Set
open HSFormal.Cubical HSFormal.Cubical.BasedComplex

namespace HSFormal.FixedData

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {M : Type*} [TopologicalSpace M] [AddAction ℤ_[p] M]
  (d : FixedData p n M)

/-! ### The cutoff and the chart action -/

/-- The cutoff `θ(t) = clamp(3 - 2t)`: `1` for `t ≤ 1`, `0` for `t ≥ 3/2` (8.1). -/
def cutoff (t : ℝ) : ℝ := max 0 (min 1 (3 - 2 * t))

theorem cutoff_nonneg (t : ℝ) : 0 ≤ cutoff t := le_max_left _ _

theorem cutoff_le_one (t : ℝ) : cutoff t ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem cutoff_of_le_one {t : ℝ} (ht : t ≤ 1) : cutoff t = 1 := by
  rw [cutoff, min_eq_left (by linarith), max_eq_right zero_le_one]

theorem cutoff_of_ge {t : ℝ} (ht : 3 / 2 ≤ t) : cutoff t = 0 := by
  rw [cutoff, max_eq_left (min_le_of_right_le (by linarith))]

theorem continuous_cutoff : Continuous cutoff := by unfold cutoff; fun_prop

/-- `a` acting in chart coordinates: `v ↦ φ(a +ᵥ φ⁻¹ v)`. -/
def chartAct (a : ℤ_[p]) (v : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  d.φ (a +ᵥ d.φ.symm v)

theorem symm_mem_source {v : EuclideanSpace ℝ (Fin n)} (hv : ‖v‖ ≤ 2) : d.φ.symm v ∈ d.φ.source :=
  d.φ.map_target (d.mem_target_of_norm_lt hv (by norm_num))

theorem apply_symm {v : EuclideanSpace ℝ (Fin n)} (hv : ‖v‖ ≤ 2) : d.φ (d.φ.symm v) = v :=
  d.φ.right_inv (d.mem_target_of_norm_lt hv (by norm_num))

theorem vadd_symm_mem_source {a : ℤ_[p]} (ha : a ∈ d.H) {v : EuclideanSpace ℝ (Fin n)}
    (hv : ‖v‖ ≤ 2) : a +ᵥ d.φ.symm v ∈ d.φ.source :=
  d.vadd_mem_source a ha _ (d.symm_mem_source hv) (by rwa [d.apply_symm hv])

/-- Displacement `≤ D` of the chart action on `B̄(0, 2)` (7.1). -/
theorem norm_chartAct_sub_le {a : ℤ_[p]} (ha : a ∈ d.H) {v : EuclideanSpace ℝ (Fin n)}
    (hv : ‖v‖ ≤ 2) : ‖d.chartAct a v - v‖ ≤ d.D := by
  have := d.displacement_le a ha _ (d.symm_mem_source hv) (by rwa [d.apply_symm hv])
  rwa [d.apply_symm hv] at this

theorem chartAct_zero {v : EuclideanSpace ℝ (Fin n)} (hv : ‖v‖ ≤ 2) : d.chartAct 0 v = v := by
  rw [chartAct, zero_vadd, d.apply_symm hv]

/-- `φ⁻¹ (a v) = a +ᵥ φ⁻¹ v`. -/
theorem symm_chartAct {a : ℤ_[p]} (ha : a ∈ d.H) {v : EuclideanSpace ℝ (Fin n)} (hv : ‖v‖ ≤ 2) :
    d.φ.symm (d.chartAct a v) = a +ᵥ d.φ.symm v :=
  d.φ.left_inv (d.vadd_symm_mem_source ha hv)

/-- `b (a v) = (b + a) v`. -/
theorem chartAct_chartAct {a b : ℤ_[p]} (ha : a ∈ d.H) {v : EuclideanSpace ℝ (Fin n)}
    (hv : ‖v‖ ≤ 2) : d.chartAct b (d.chartAct a v) = d.chartAct (b + a) v := by
  rw [chartAct, d.symm_chartAct ha hv, vadd_vadd]; rfl

/-! ### The displacement field and `ĥ` on the torus -/

/-- The displacement `θ(|v|) (a v - v)` of (8.1) on `B(0, 2)`, `0` elsewhere. -/
def disp (a : ℤ_[p]) (v : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  if ‖v‖ < 2 then cutoff ‖v‖ • (d.chartAct a v - v) else 0

theorem norm_disp_le {a : ℤ_[p]} (ha : a ∈ d.H) (v : EuclideanSpace ℝ (Fin n)) :
    ‖d.disp a v‖ ≤ d.D := by
  unfold disp
  split_ifs with hv
  · rw [norm_smul, Real.norm_of_nonneg (cutoff_nonneg _)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (cutoff_le_one _)).trans
      (d.norm_chartAct_sub_le ha hv.le)
  · simpa using d.D_nonneg

theorem disp_of_ge {a : ℤ_[p]} {v : EuclideanSpace ℝ (Fin n)} (hv : 3 / 2 ≤ ‖v‖) :
    d.disp a v = 0 := by
  unfold disp
  split_ifs
  · rw [cutoff_of_ge hv, zero_smul]
  · rfl

theorem add_disp_of_le_one (a : ℤ_[p]) {v : EuclideanSpace ℝ (Fin n)} (hv : ‖v‖ ≤ 1) :
    v + d.disp a v = d.chartAct a v := by
  rw [disp, ite_eq_left (by linarith), cutoff_of_le_one hv, one_smul, add_sub_cancel]

theorem disp_zero (v : EuclideanSpace ℝ (Fin n)) : d.disp 0 v = 0 := by
  unfold disp
  split_ifs with hv
  · rw [d.chartAct_zero hv.le, sub_self, smul_zero]
  · rfl

/-- Coordinatewise projection `ℝⁿ → (ℝ/16ℤ)ⁿ`. -/
def toTorus (w : EuclideanSpace ℝ (Fin n)) : Fin n → AddCircle (16 : ℝ) :=
  fun k ↦ ((w k : ℝ) : AddCircle (16 : ℝ))

/-- **The completed map `ĥ_a`** of (8.1) on the torus: `x + θ(|x|)(a x - x)` in the lifted chart
coordinates. -/
def hatT (a : ℤ_[p]) (x : Fin n → AddCircle (16 : ℝ)) : Fin n → AddCircle (16 : ℝ) :=
  x + toTorus (d.disp a (liftVec 16 x))

theorem hatT_zero (x : Fin n → AddCircle (16 : ℝ)) : d.hatT 0 x = x := by
  ext k; simp [hatT, disp_zero, toTorus]

theorem hatT_of_ge {a : ℤ_[p]} {x : Fin n → AddCircle (16 : ℝ)} (hx : 3 / 2 ≤ ‖liftVec 16 x‖) :
    d.hatT a x = x := by
  ext k; simp [hatT, d.disp_of_ge hx, toTorus]

/-! ### Lifts -/

theorem liftHalf_coe {t : ℝ} (ht : t ∈ Ico (-8 : ℝ) 8) : liftHalf 16 (t : AddCircle (16 : ℝ)) = t := by
  have ht' : t ∈ Ico (-((16 : ℝ) / 2)) (-((16 : ℝ) / 2) + 16) := by
    constructor <;> linarith [ht.1, ht.2]
  rw [liftHalf, AddCircle.equivIco_coe_eq ht']

theorem liftVec_apply (x : Fin n → AddCircle (16 : ℝ)) (k : Fin n) :
    liftVec 16 x k = liftHalf 16 (x k) := rfl

theorem toTorus_liftVec (x : Fin n → AddCircle (16 : ℝ)) : toTorus (liftVec 16 x) = x := by
  ext k; exact coe_liftHalf 16 (x k)

theorem abs_coord_le_norm (w : EuclideanSpace ℝ (Fin n)) (k : Fin n) : |w k| ≤ ‖w‖ := by
  have := PiLp.norm_apply_le w k
  rwa [Real.norm_eq_abs] at this

theorem liftVec_toTorus {w : EuclideanSpace ℝ (Fin n)} (hw : ‖w‖ < 8) :
    liftVec 16 (toTorus w) = w := by
  ext k
  rw [liftVec_apply, toTorus, liftHalf_coe]
  have := abs_coord_le_norm w k
  constructor <;> [linarith [neg_abs_le (w k)]; linarith [le_abs_self (w k)]]

theorem liftVec_add_toTorus {x : Fin n → AddCircle (16 : ℝ)} {w : EuclideanSpace ℝ (Fin n)}
    (h : ‖liftVec 16 x + w‖ < 8) : liftVec 16 (x + toTorus w) = liftVec 16 x + w := by
  ext k
  have e : x k + toTorus w k = ((liftVec 16 x k + w k : ℝ) : AddCircle (16 : ℝ)) := by
    rw [AddCircle.coe_add, liftVec_apply, coe_liftHalf]; rfl
  rw [liftVec_apply, Pi.add_apply, e, liftHalf_coe]
  · rfl
  · have := abs_coord_le_norm (liftVec 16 x + w) k
    simp only [PiLp.add_apply] at this
    constructor <;> [linarith [neg_abs_le (liftVec 16 x k + w k)];
      linarith [le_abs_self (liftVec 16 x k + w k)]]

/-- `ĥ` in lifted chart coordinates. -/
theorem liftVec_hatT {a : ℤ_[p]} (ha : a ∈ d.H) (x : Fin n → AddCircle (16 : ℝ)) :
    liftVec 16 (d.hatT a x) = liftVec 16 x + d.disp a (liftVec 16 x) := by
  by_cases hx : 3 / 2 ≤ ‖liftVec 16 x‖
  · rw [d.hatT_of_ge hx, d.disp_of_ge hx, add_zero]
  · refine liftVec_add_toTorus ?_
    linarith [norm_add_le (liftVec 16 x) (d.disp a (liftVec 16 x)), d.norm_disp_le ha
      (liftVec 16 x), d.D_lt]

/-- On `B(0, 1)`, `ĥ_a` is the action. -/
theorem liftVec_hatT_of_le_one {a : ℤ_[p]} (ha : a ∈ d.H) {x : Fin n → AddCircle (16 : ℝ)}
    (hx : ‖liftVec 16 x‖ ≤ 1) : liftVec 16 (d.hatT a x) = d.chartAct a (liftVec 16 x) := by
  rw [d.liftVec_hatT ha, d.add_disp_of_le_one a hx]

theorem hatT_of_le_one {a : ℤ_[p]} (ha : a ∈ d.H) {x : Fin n → AddCircle (16 : ℝ)}
    (hx : ‖liftVec 16 x‖ ≤ 1) : d.hatT a x = toTorus (d.chartAct a (liftVec 16 x)) := by
  rw [← d.liftVec_hatT_of_le_one ha hx, toTorus_liftVec]


/-! ### Displacement bounds -/

theorem dist_coe_coord_le (t : ℝ) : ‖((t : ℝ) : AddCircle (16 : ℝ))‖ ≤ |t| := by
  rw [← Real.norm_eq_abs]; exact QuotientAddGroup.norm_mk_le_norm

theorem dist_add_toTorus_le (x : Fin n → AddCircle (16 : ℝ)) (w : EuclideanSpace ℝ (Fin n)) :
    dist (x + toTorus w) x ≤ ‖w‖ := by
  refine (dist_pi_le_iff (norm_nonneg _)).mpr fun k ↦ ?_
  rw [Pi.add_apply, dist_eq_norm, add_sub_cancel_left]
  exact (dist_coe_coord_le _).trans (abs_coord_le_norm w k)

/-- `ĥ_a` moves points by at most `D` (sup metric). -/
theorem dist_hatT_le {a : ℤ_[p]} (ha : a ∈ d.H) (x : Fin n → AddCircle (16 : ℝ)) :
    dist (d.hatT a x) x ≤ d.D :=
  (dist_add_toTorus_le x _).trans (d.norm_disp_le ha _)

/-- The `ℓ²` distance on `(ℝ/16ℤ)ⁿ`. -/
def l2 (x y : Fin n → AddCircle (16 : ℝ)) : ℝ :=
  dist (WithLp.toLp 2 x : PiLp 2 fun _ : Fin n ↦ AddCircle (16 : ℝ)) (WithLp.toLp 2 y)

theorem l2_eq (x y : Fin n → AddCircle (16 : ℝ)) : l2 x y = √(∑ k, dist (x k) (y k) ^ 2) := by
  rw [l2, PiLp.dist_eq_of_L2]

theorem l2_triangle (x y z : Fin n → AddCircle (16 : ℝ)) : l2 x z ≤ l2 x y + l2 y z :=
  dist_triangle _ _ _

theorem l2_comm (x y : Fin n → AddCircle (16 : ℝ)) : l2 x y = l2 y x := dist_comm _ _

theorem norm_liftVec_eq (x : Fin n → AddCircle (16 : ℝ)) : ‖liftVec 16 x‖ = l2 x 0 := by
  rw [EuclideanSpace.norm_eq, l2_eq]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Pi.zero_apply, dist_zero_right, Real.norm_eq_abs]
  change |liftHalf 16 (x k)| ^ 2 = _
  rw [abs_liftHalf]

theorem l2_add_toTorus_le (x : Fin n → AddCircle (16 : ℝ)) (w : EuclideanSpace ℝ (Fin n)) :
    l2 (x + toTorus w) x ≤ ‖w‖ := by
  rw [l2_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun k _ ↦ ?_)
  rw [Pi.add_apply, dist_eq_norm, add_sub_cancel_left, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (norm_nonneg _) (dist_coe_coord_le _) 2

/-- `ĥ_a` moves points by at most `D` in `ℓ²`. -/
theorem l2_hatT_le {a : ℤ_[p]} (ha : a ∈ d.H) (x : Fin n → AddCircle (16 : ℝ)) :
    l2 (d.hatT a x) x ≤ d.D :=
  (l2_add_toTorus_le x _).trans (d.norm_disp_le ha _)

theorem l2_le_of_coord_le {x y : Fin n → AddCircle (16 : ℝ)} {a : Fin n → ℝ} {δ : ℝ}
    (hδ : 0 ≤ δ) (h : ∀ k, dist (x k) (y k) ≤ a k + δ) :
    l2 x y ≤ ‖(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))‖ + √n * δ := by
  have e : ‖(WithLp.toLp 2 (fun _ : Fin n ↦ δ) : EuclideanSpace ℝ (Fin n))‖ = √n * δ := by
    rw [EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs, sq_abs, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hδ]
  rw [← e]
  refine le_trans ?_ (norm_add_le _ _)
  rw [l2_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun k _ ↦ ?_)
  simp only [PiLp.add_apply, Real.norm_eq_abs, sq_abs]
  exact pow_le_pow_left₀ dist_nonneg (h k) 2

theorem norm_toLp_le_l2 {x y : Fin n → AddCircle (16 : ℝ)} {a : Fin n → ℝ}
    (h : ∀ k, 0 ≤ a k ∧ a k ≤ dist (x k) (y k)) :
    ‖(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))‖ ≤ l2 x y := by
  rw [l2_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun k _ ↦ ?_)
  simp only [Real.norm_eq_abs, sq_abs]
  exact pow_le_pow_left₀ (h k).1 (h k).2 2

theorem l2_le_sqrt_mul_dist (x y : Fin n → AddCircle (16 : ℝ)) : l2 x y ≤ √n * dist x y := by
  rw [l2_eq, ← Real.sqrt_sq dist_nonneg, ← Real.sqrt_mul (Nat.cast_nonneg _)]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ k, dist (x k) (y k) ^ 2 ≤ ∑ _k : Fin n, dist x y ^ 2 :=
        Finset.sum_le_sum fun k _ ↦ pow_le_pow_left₀ dist_nonneg (dist_le_pi_dist x y k) 2
    _ = n * dist x y ^ 2 := by simp

theorem dist_le_l2 (x y : Fin n → AddCircle (16 : ℝ)) : dist x y ≤ l2 x y := by
  refine (dist_pi_le_iff (by rw [l2]; exact dist_nonneg)).mpr fun k ↦ ?_
  rw [l2_eq]
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun k ↦ dist (x k) (y k) ^ 2) (fun _ _ ↦ sq_nonneg _)
    (Finset.mem_univ k)

/-! ### (8.2): `f ĥ = f` -/

section Label

variable [ContinuousVAdd ℤ_[p] M] [LocallyCompactSpace M] [FirstCountableTopology M]

theorem fhat_eq_chartHomotopyFun (v : EuclideanSpace ℝ (Fin n)) :
    d.fhat v = d.chartHomotopyFun (0, v) := rfl

theorem fhat_eq_infty {v : EuclideanSpace ℝ (Fin n)} (hv : d.ρ + 2 * d.D < ‖v‖) :
    d.fhat v = OnePoint.infty := by
  rw [fhat_eq_chartHomotopyFun]; exact d.chartHomotopyFun_eq_infty hv

theorem fhat_chartAct {a : ℤ_[p]} (ha : a ∈ d.H) {v : EuclideanSpace ℝ (Fin n)} (hv : ‖v‖ ≤ 1) :
    d.fhat (d.chartAct a v) = d.fhat v := by
  have hv2 : ‖v‖ ≤ 2 := by linarith
  have hw : ‖d.chartAct a v‖ < 4 := by
    linarith [norm_sub_norm_le (d.chartAct a v) v, d.norm_chartAct_sub_le ha hv2, d.D_lt]
  rw [d.fhat_coe_of_mem_target (d.mem_target_of_norm_lt le_rfl hw),
    d.fhat_coe_of_mem_target (d.mem_target_of_norm_lt hv2 (by norm_num)), d.symm_chartAct ha hv2,
    d.f_vadd ha]

/-- **(8.2)** `f ĥ = f` exactly, for every `a ∈ H`: on `B(0,1)` by invariance, elsewhere both
points lie outside the nonconstant locus `B(0, ρ + 2D)` (`|ĥ x| ≥ 1 - D > ρ + 2D`). -/
theorem torusLabel_hatT {a : ℤ_[p]} (ha : a ∈ d.H) (x : Fin n → AddCircle (16 : ℝ)) :
    d.torusLabel (d.hatT a x) = d.torusLabel x := by
  have hρ := d.ρ_lt.trans d.ρplus_lt
  have hD := d.D_lt
  have hD0 := d.D_nonneg
  change d.fhat (liftVec 16 (d.hatT a x)) = d.fhat (liftVec 16 x)
  by_cases hx : ‖liftVec 16 x‖ ≤ 1
  · rw [d.liftVec_hatT_of_le_one ha hx, d.fhat_chartAct ha hx]
  · push_neg at hx
    rw [d.liftVec_hatT ha, d.fhat_eq_infty (v := liftVec 16 x) (by linarith),
      d.fhat_eq_infty]
    have h₁ := norm_sub_le (liftVec 16 x + d.disp a (liftVec 16 x)) (d.disp a (liftVec 16 x))
    rw [add_sub_cancel_right] at h₁
    linarith [d.norm_disp_le ha (liftVec 16 x)]

end Label


/-! ### Equicontinuity of the completed family `{ĥ_a : a ∈ H}` -/

theorem continuous_toTorus : Continuous (toTorus (n := n)) :=
  continuous_pi fun k ↦ QuotientAddGroup.continuous_mk.comp ((PiLp.continuous_apply 2 _ k))

theorem norm_liftVec_eq_sqrt (x : Fin n → AddCircle (16 : ℝ)) :
    ‖liftVec 16 x‖ = √(∑ k, ‖x k‖ ^ 2) := by
  rw [norm_liftVec_eq, l2_eq]
  simp

theorem continuous_norm_liftVec : Continuous fun x : Fin n → AddCircle (16 : ℝ) ↦ ‖liftVec 16 x‖ := by
  simp_rw [norm_liftVec_eq_sqrt]
  fun_prop

theorem continuousAt_liftVec {x : Fin n → AddCircle (16 : ℝ)} (hx : ‖liftVec 16 x‖ < 8) :
    ContinuousAt (liftVec 16) x := by
  have hx' : ∀ k, x k ≠ ((-((16 : ℝ) / 2) : ℝ) : AddCircle (16 : ℝ)) := fun k h ↦ by
    have h₁ : |liftHalf 16 (x k)| ≤ ‖liftVec 16 x‖ := abs_coord_le_norm (liftVec 16 x) k
    rw [abs_liftHalf, h, (AddCircle.norm_coe_eq_abs_iff 16 (by norm_num)).mpr (by norm_num)]
      at h₁
    norm_num at h₁
    linarith
  have h₁ : ∀ i, ContinuousAt (fun y : Fin n → AddCircle (16 : ℝ) ↦ liftHalf 16 (y i)) x :=
    fun i ↦ (continuous_subtype_val.continuousAt.comp
      (AddCircle.continuousAt_equivIco 16 _ (hx' i))).comp
        (f := fun y : Fin n → AddCircle (16 : ℝ) ↦ y i) (continuous_apply i).continuousAt
  exact (PiLp.continuous_toLp 2 _).continuousAt.comp (continuousAt_pi.mpr h₁)

theorem toTorus_zero : toTorus (0 : EuclideanSpace ℝ (Fin n)) = 0 := by
  funext k; simp [toTorus]

/-- The displacement field of `ĥ` as a function of `(a, x)`. -/
def hatDisp (q : ℤ_[p] × (Fin n → AddCircle (16 : ℝ))) : Fin n → AddCircle (16 : ℝ) :=
  toTorus (d.disp q.1 (liftVec 16 q.2))

theorem hatT_eq (a : ℤ_[p]) (x : Fin n → AddCircle (16 : ℝ)) : d.hatT a x = x + d.hatDisp (a, x) :=
  rfl

section Equi

variable [ContinuousVAdd ℤ_[p] M]

theorem continuousAt_disp {a : ℤ_[p]} (ha : a ∈ d.H) {v : EuclideanSpace ℝ (Fin n)}
    (h2 : ‖v‖ < 2) : ContinuousAt (fun q : ℤ_[p] × EuclideanSpace ℝ (Fin n) ↦ d.disp q.1 q.2)
      (a, v) := by
  have hvt : v ∈ d.φ.target := d.mem_target_of_norm_lt h2.le (by norm_num)
  have h₀ : ContinuousAt (fun q : ℤ_[p] × EuclideanSpace ℝ (Fin n) ↦ d.φ.symm q.2) (a, v) :=
    ContinuousAt.comp (g := d.φ.symm) (f := Prod.snd) (d.φ.continuousAt_symm hvt)
      continuousAt_snd
  have h₁ : ContinuousAt (fun q : ℤ_[p] × EuclideanSpace ℝ (Fin n) ↦
      q.1 +ᵥ d.φ.symm q.2) (a, v) := continuousAt_fst.vadd h₀
  have h₂ : ContinuousAt (fun q : ℤ_[p] × EuclideanSpace ℝ (Fin n) ↦
      d.φ (q.1 +ᵥ d.φ.symm q.2)) (a, v) :=
    ContinuousAt.comp (g := d.φ) (f := fun q : ℤ_[p] × EuclideanSpace ℝ (Fin n) ↦
      q.1 +ᵥ d.φ.symm q.2) (d.φ.continuousAt (d.vadd_symm_mem_source ha h2.le)) h₁
  have hF : ContinuousAt (fun q : ℤ_[p] × EuclideanSpace ℝ (Fin n) ↦
      cutoff ‖q.2‖ • (d.φ (q.1 +ᵥ d.φ.symm q.2) - q.2)) (a, v) :=
    ((continuous_cutoff.comp (continuous_norm.comp continuous_snd)).continuousAt).smul
      (h₂.sub continuousAt_snd)
  refine hF.congr ?_
  filter_upwards [(continuous_norm.comp continuous_snd).continuousAt.eventually
    (gt_mem_nhds (b := ‖(a, v).2‖) h2)] with q hq
  simp only [Function.comp_apply] at hq
  simp [disp, hq, chartAct]

theorem continuousAt_hatDisp {a : ℤ_[p]} (ha : a ∈ d.H) (x : Fin n → AddCircle (16 : ℝ)) :
    ContinuousAt d.hatDisp (a, x) := by
  have hN := (continuous_norm_liftVec (n := n)).comp continuous_snd
    (X := ℤ_[p] × (Fin n → AddCircle (16 : ℝ)))
  rcases lt_or_ge (3 / 2) ‖liftVec 16 x‖ with h | h
  · have hev : ∀ᶠ q in 𝓝 (a, x), d.hatDisp q = 0 := by
      filter_upwards [hN.continuousAt.eventually (lt_mem_nhds h)] with q hq
      simp [hatDisp, d.disp_of_ge (a := q.1) hq.le, toTorus_zero]
    exact continuousAt_const.congr (hev.mono fun q hq ↦ hq.symm)
  · have h2 : ‖liftVec 16 x‖ < 2 := by linarith
    have hlift : ContinuousAt (fun q : ℤ_[p] × (Fin n → AddCircle (16 : ℝ)) ↦
        (q.1, liftVec 16 q.2)) (a, x) :=
      continuousAt_fst.prodMk ((continuousAt_liftVec (by linarith)).comp continuousAt_snd)
    exact continuous_toTorus.continuousAt.comp
      (ContinuousAt.comp (f := fun q : ℤ_[p] × (Fin n → AddCircle (16 : ℝ)) ↦
        (q.1, liftVec 16 q.2)) (g := fun q ↦ d.disp q.1 q.2) (d.continuousAt_disp ha h2) hlift)

theorem uniformContinuousOn_hatDisp :
    UniformContinuousOn d.hatDisp ((d.H : Set ℤ_[p]) ×ˢ univ) :=
  ((padicPowerSubgroup_isClosed _).isCompact.prod isCompact_univ).uniformContinuousOn_of_continuous
    fun q hq ↦ (d.continuousAt_hatDisp hq.1 q.2).continuousWithinAt

theorem dist_torus_le (x y : Fin n → AddCircle (16 : ℝ)) : dist x y ≤ 8 :=
  (dist_pi_le_iff (by norm_num)).mpr fun k ↦ by
    rw [dist_eq_norm]
    exact (AddCircle.norm_le_half_period 16 (by norm_num)).trans (by norm_num)

/-- **The common modulus `ω` of the compact family `{ĥ_a : a ∈ H}`** (l.544, l.570). -/
def hatModulus (δ : ℝ) : ℝ :=
  sSup ((fun q : ℤ_[p] × (Fin n → AddCircle (16 : ℝ)) × (Fin n → AddCircle (16 : ℝ)) ↦
    dist (d.hatT q.1 q.2.1) (d.hatT q.1 q.2.2)) '' {q | q.1 ∈ d.H ∧ dist q.2.1 q.2.2 ≤ δ})

theorem bddAbove_hatModulus (δ : ℝ) :
    BddAbove ((fun q : ℤ_[p] × (Fin n → AddCircle (16 : ℝ)) × (Fin n → AddCircle (16 : ℝ)) ↦
      dist (d.hatT q.1 q.2.1) (d.hatT q.1 q.2.2)) '' {q | q.1 ∈ d.H ∧ dist q.2.1 q.2.2 ≤ δ}) :=
  ⟨8, by rintro _ ⟨q, -, rfl⟩; exact dist_torus_le _ _⟩

theorem dist_hatT_le_hatModulus {a : ℤ_[p]} (ha : a ∈ d.H) {x y : Fin n → AddCircle (16 : ℝ)}
    {δ : ℝ} (h : dist x y ≤ δ) : dist (d.hatT a x) (d.hatT a y) ≤ d.hatModulus δ :=
  le_csSup (d.bddAbove_hatModulus δ) ⟨(a, x, y), ⟨ha, h⟩, rfl⟩

theorem hatModulus_nonneg {δ : ℝ} (hδ : 0 ≤ δ) : 0 ≤ d.hatModulus δ :=
  dist_nonneg.trans (d.dist_hatT_le_hatModulus (zero_mem d.H) (x := 0) (y := 0)
    (by rwa [dist_self]))

theorem hatModulus_mono {δ δ' : ℝ} (hδ : 0 ≤ δ) (h : δ ≤ δ') : d.hatModulus δ ≤ d.hatModulus δ' :=
  csSup_le_csSup (d.bddAbove_hatModulus δ') ⟨_, ⟨(0, 0, 0), ⟨zero_mem _, by simpa using hδ⟩, rfl⟩⟩
    (image_mono fun _ hq ↦ ⟨hq.1, hq.2.trans h⟩)

theorem hatModulus_le_eight (δ : ℝ) (hδ : 0 ≤ δ) : d.hatModulus δ ≤ 8 :=
  csSup_le ⟨_, ⟨(0, 0, 0), ⟨zero_mem _, by simpa using hδ⟩, rfl⟩⟩ (by
    rintro _ ⟨q, -, rfl⟩; exact dist_torus_le _ _)

/-- **Equicontinuity**: `ω δ → 0` as `δ → 0`, uniformly over `H`. -/
theorem exists_hatModulus_le {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, d.hatModulus δ ≤ ε := by
  obtain ⟨δ₁, hδ₁, h⟩ := Metric.uniformContinuousOn_iff.mp d.uniformContinuousOn_hatDisp (ε / 2)
    (half_pos hε)
  refine ⟨min (δ₁ / 2) (ε / 2), lt_min (half_pos hδ₁) (half_pos hε), ?_⟩
  refine csSup_le ⟨_, ⟨(0, 0, 0), ⟨zero_mem _, by
    simp only [dist_self]; exact (lt_min (half_pos hδ₁) (half_pos hε)).le⟩, rfl⟩⟩ ?_
  rintro _ ⟨⟨a, x, y⟩, ⟨ha, hxy⟩, rfl⟩
  simp only at ha hxy ⊢
  have hlt : dist (a, x) (a, y) < δ₁ := by
    rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
    linarith [min_le_left (δ₁ / 2) (ε / 2)]
  have h₁ := (h (a, x) ⟨ha, trivial⟩ (a, y) ⟨ha, trivial⟩ hlt).le
  rw [d.hatT_eq, d.hatT_eq]
  refine (dist_add_add_le _ _ _ _).trans ?_
  linarith [min_le_right (δ₁ / 2) (ε / 2)]

theorem tendsto_hatModulus {δ : ℕ → ℝ} (h0 : ∀ i, 0 ≤ δ i) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun i ↦ d.hatModulus (δ i)) atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
  obtain ⟨δ₀, hδ₀, hle⟩ := d.exists_hatModulus_le (half_pos hε)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hδ δ₀ hδ₀
  refine ⟨N, fun i hi ↦ ?_⟩
  have h₁ : δ i ≤ δ₀ := by
    have := hN i hi
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (h0 i)] at this
    exact this.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (d.hatModulus_nonneg (h0 i))]
  linarith [d.hatModulus_mono (h0 i) h₁]

end Equi


/-! ### Composition on the inner region, cocycles, lifts and `ρ̃` -/

theorem toTorus_add (v w : EuclideanSpace ℝ (Fin n)) : toTorus (v + w) = toTorus v + toTorus w := by
  funext k; simp [toTorus]

theorem dist_toTorus_le (v w : EuclideanSpace ℝ (Fin n)) :
    dist (toTorus w) (toTorus v) ≤ ‖w - v‖ := by
  have : toTorus w = toTorus v + toTorus (w - v) := by rw [← toTorus_add, add_sub_cancel]
  rw [this]; exact dist_add_toTorus_le _ _

theorem norm_chartAct_le {a : ℤ_[p]} (ha : a ∈ d.H) {v : EuclideanSpace ℝ (Fin n)} (hv : ‖v‖ ≤ 2) :
    ‖d.chartAct a v‖ ≤ ‖v‖ + d.D := by
  have := norm_le_insert' (d.chartAct a v) v
  linarith [d.norm_chartAct_sub_le ha hv, norm_sub_norm_le (d.chartAct a v) v]

theorem hatT_toTorus_of_le_one {a : ℤ_[p]} (ha : a ∈ d.H) {w : EuclideanSpace ℝ (Fin n)}
    (hw : ‖w‖ ≤ 1) : d.hatT a (toTorus w) = toTorus (d.chartAct a w) := by
  rw [d.hatT_of_le_one ha (by rwa [liftVec_toTorus (by linarith)]),
    liftVec_toTorus (by linarith)]

/-- **The track on the inner region** (l.612): for `|x| ≤ 1/2`, `ĥ_a ĥ_b x = ĥ_c (k x)` when
`a + b = c + k` (`k = k_{g,h}` the cocycle). -/
theorem hatT_hatT_of_le {a b c k : ℤ_[p]} (ha : a ∈ d.H) (hb : b ∈ d.H) (hk : k ∈ d.H)
    (habc : a + b = c + k) {x : Fin n → AddCircle (16 : ℝ)} (hx : ‖liftVec 16 x‖ ≤ 1 / 2) :
    d.hatT a (d.hatT b x) = d.hatT c (toTorus (d.chartAct k (liftVec 16 x))) := by
  have hD := d.D_lt
  have hD0 := d.D_nonneg
  have hv2 : ‖liftVec 16 x‖ ≤ 2 := by linarith
  have hb1 : ‖d.chartAct b (liftVec 16 x)‖ ≤ 1 := by linarith [d.norm_chartAct_le hb hv2]
  have hk1 : ‖d.chartAct k (liftVec 16 x)‖ ≤ 1 := by linarith [d.norm_chartAct_le hk hv2]
  have hc : c ∈ d.H := by
    have : c = a + b - k := by rw [habc]; abel
    rw [this]; exact d.H.sub_mem (d.H.add_mem ha hb) hk
  rw [d.hatT_of_le_one hb (by linarith), d.hatT_toTorus_of_le_one ha hb1,
    d.hatT_toTorus_of_le_one hc hk1, d.chartAct_chartAct hb hv2, d.chartAct_chartAct hk hv2, habc]

theorem dist_toTorus_chartAct_le (k : ℤ_[p]) (x : Fin n → AddCircle (16 : ℝ)) :
    dist (toTorus (d.chartAct k (liftVec 16 x))) x ≤ ‖d.chartAct k (liftVec 16 x) - liftVec 16 x‖ := by
  have := dist_toTorus_le (liftVec 16 x) (d.chartAct k (liftVec 16 x))
  rwa [toTorus_liftVec] at this

theorem symm_mem_Q {v : EuclideanSpace ℝ (Fin n)} (hv : ‖v‖ ≤ 2) : d.φ.symm v ∈ d.Q :=
  ⟨(0, d.φ.symm v), ⟨zero_mem _, d.symm_mem_source hv, by
    simp only [mem_preimage, mem_closedBall, dist_zero_right]; rwa [d.apply_symm hv]⟩,
    zero_vadd _ _⟩

/-- `d_i → 0`: the cocycles `k_{g,h} ∈ K_i` move `B̄(0, 2)` uniformly little (l.612). -/
theorem eventually_cocycle_chartAct_lt [ContinuousVAdd ℤ_[p] M] {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∀ g h : d.G i, ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ ≤ 2 →
      ‖d.chartAct (d.cocycle i g h).val v - v‖ < ε := by
  filter_upwards [d.eventually_cocycle_displacement_lt hε] with i hi g h v hv
  have := (hi g h (d.φ.symm v) (d.symm_mem_Q hv)).2
  rwa [PadicTail.smul_def, d.apply_symm hv] at this

/-- Lifts are `1`-Lipschitz coordinatewise near the chart. -/
theorem abs_liftHalf_sub_le {a b : AddCircle (16 : ℝ)} (hb : |liftHalf 16 b| ≤ 6)
    (h : dist a b ≤ 1) : |liftHalf 16 a - liftHalf 16 b| ≤ dist a b := by
  have ha : |liftHalf 16 a| ≤ 8 := by
    rw [abs_liftHalf]; exact (AddCircle.norm_le_half_period 16 (by norm_num)).trans (by norm_num)
  have ha' := abs_le.mp ha
  have hb' := abs_le.mp hb
  have hnorm : ‖((liftHalf 16 a - liftHalf 16 b : ℝ) : AddCircle (16 : ℝ))‖ = dist a b := by
    rw [AddCircle.coe_sub, coe_liftHalf, coe_liftHalf, dist_eq_norm]
  have ht : -14 ≤ liftHalf 16 a - liftHalf 16 b ∧ liftHalf 16 a - liftHalf 16 b ≤ 14 :=
    ⟨by linarith, by linarith⟩
  generalize liftHalf 16 a - liftHalf 16 b = t at hnorm ht ⊢
  have hcoe : ∀ u : ℝ, |u| ≤ 8 → ‖((u : ℝ) : AddCircle (16 : ℝ))‖ = |u| := fun u hu ↦
    (AddCircle.norm_coe_eq_abs_iff 16 (by norm_num)).mpr (by norm_num; linarith)
  rcases le_or_gt |t| 8 with h8 | h8
  · rw [← hnorm, hcoe t h8]
  · exfalso
    rcases lt_abs.mp h8 with h₁ | h₁
    · have e := AddCircle.coe_add_period (16 : ℝ) (t - 16)
      rw [sub_add_cancel] at e
      rw [e, hcoe _ (by rw [abs_le]; constructor <;> linarith),
        abs_of_neg (by linarith)] at hnorm
      linarith
    · have e := AddCircle.coe_add_period (16 : ℝ) t
      rw [← e, hcoe _ (by rw [abs_le]; constructor <;> linarith),
        abs_of_pos (by linarith)] at hnorm
      linarith

theorem norm_liftVec_sub_le {x y : Fin n → AddCircle (16 : ℝ)} (hy : ‖liftVec 16 y‖ ≤ 6)
    (h : dist x y ≤ 1) : ‖liftVec 16 x - liftVec 16 y‖ ≤ √n * dist x y := by
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq dist_nonneg, ← Real.sqrt_mul (Nat.cast_nonneg _)]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ k, ‖(liftVec 16 x - liftVec 16 y) k‖ ^ 2 ≤ ∑ _k : Fin n, dist x y ^ 2 := by
        refine Finset.sum_le_sum fun k _ ↦ ?_
        rw [Real.norm_eq_abs]
        refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
        have hk := dist_le_pi_dist x y k
        exact (abs_liftHalf_sub_le ((abs_coord_le_norm (liftVec 16 y) k).trans hy)
          (hk.trans h)).trans hk
    _ = n * dist x y ^ 2 := by simp

/-- `ρ̃` read in the chart. -/
def rhoChart (v : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℂ (Fin d.m) := d.ρtilde (d.φ.symm v)

/-- (7.7) in the chart: `ρ̃(a v) = χ(a) ρ̃(v)`. -/
theorem rhoChart_chartAct {a : ℤ_[p]} (ha : a ∈ d.H) {v : EuclideanSpace ℝ (Fin n)}
    (hv : ‖v‖ ≤ 2) : d.rhoChart (d.chartAct a v) = (padicChar p d.j a : ℂ) • d.rhoChart v := by
  rw [rhoChart, d.symm_chartAct ha hv, d.ρtilde_vadd a ha]; rfl

end HSFormal.FixedData
