import HSFormal.LTheory.Theorem63
import HSFormal.Germ
import HSFormal.Cubical.PinchCut

/-!
# The cube flag and the reduction of `PinchSignature` to single cuts (cubical module C8)

* `RoundSphere.chartV v`: the chart point of `Sⁿ = OnePoint ℝⁿ` with sup-norm coordinates
  `v : Fin n → ℝ` (the coordinates of `germCollapse`, which is the chart lift on `‖v‖_∞ ≤ 4`).
* `ControlData.cubeRadius`: a radius `0 < r_Q ≤ 1`, chosen from `cd` alone, with the cube
  `‖v‖_∞ ≤ r_Q` inside `{d(y, ·) < R}`.
* **`ControlData.cubeFlag`**: the cube cut flag of the cubical route (simplicial-design §2.5) as a
  `CutFlag` of `Theorem63`, a function of `cd` alone: the first cut `B = Q = [-r_Q, r_Q]ⁿ`,
  `A = Sⁿ ∖ int Q` (so `Z₀ ⊆ A`, `Z₀ ∩ B = ∅`), interface `∂Q`; the `k`-th cut of
  `Y (k+1) = ∂Φ_{k+2}` into the top face `b k = Φ_{k+1}` (the next coordinate `= +r_Q`) and the
  rest `a k`, where `Φ_j` is the face of `Q` with the first `n - j` coordinates `= r_Q`; this is
  the order of `cube.topEmb` (first tensor factor first).  `P`, `Q` are the end points
  `v_{n-1} = ±r_Q` of the edge `Φ₁`.  `cubeFlagChoice : FlagChoice`.
* **`pinchSignature_of_cutSteps`**: `PinchSignature (fibreSignatureOf 𝕃 cubeFlagChoice)
  manifoldGerm` follows from single cut steps of classes `x k` (up to signs `u k`, the `bsign`s of
  Lemma 4.1 and the A/B side sign of `PinchPair.cutBdHtpy`) and the value of `σ_tail` on the last
  class (`pt ⊗ CPcell`, `σ = 1`).
-/

noncomputable section

open Metric Topology CategoryTheory

namespace HSFormal

namespace RoundSphere

variable {n : ℕ}

/-- The chart point with sup-norm coordinates `v`. -/
def chartV (v : Fin n → ℝ) : RoundSphere n :=
  toOnePoint.symm ((WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n)) : OnePoint _)

theorem continuous_chartV : Continuous (chartV (n := n)) :=
  toOnePoint.symm.continuous.comp (OnePoint.continuous_coe.comp (PiLp.continuous_toLp 2 _))

theorem chartV_injective : Function.Injective (chartV (n := n)) := fun v w h ↦ by
  have := OnePoint.coe_injective (toOnePoint.symm.injective h)
  simpa using congrArg WithLp.ofLp this

theorem isOpenMap_chartV : IsOpenMap (chartV (n := n)) :=
  toOnePoint.symm.isOpenMap.comp (OnePoint.isOpenEmbedding_coe.isOpenMap.comp
    (PiLp.homeomorph 2 _).symm.isOpenMap)

theorem isClosed_image_chartV {K : Set (Fin n → ℝ)} {r : ℝ} (hK : IsClosed K)
    (hr : K ⊆ closedBall 0 r) : IsClosed (chartV '' K) :=
  ((isCompact_closedBall 0 r).of_isClosed_subset hK hr).image continuous_chartV |>.isClosed

theorem eq_infty_or_chartV (z : RoundSphere n) : z = infty ∨ ∃ v, chartV v = z := by
  induction h : toOnePoint z using OnePoint.rec with
  | infty => left; exact toOnePoint.injective (by rw [h]; rfl)
  | coe w => right; exact ⟨WithLp.ofLp w, by simp [chartV, ← h]⟩

theorem chartV_ne_infty (v : Fin n → ℝ) : chartV v ≠ infty := fun h ↦
  OnePoint.coe_ne_infty _ (toOnePoint.symm.injective h)

/-- The centre `y` of `ControlData` is the chart origin. -/
theorem dist_y_eq {y : RoundSphere n} (hy : dist y infty = 2) (z : RoundSphere n) :
    dist y z = dist (chartV 0) z := by
  have h0 : dist (chartV (n := n) 0) infty = 2 := by
    simpa [chartV] using dist_zero_infty (n := n)
  rw [dist_eq_norm_amb, dist_eq_norm_amb, amb_eq_neg_northPole hy, amb_eq_neg_northPole h0]

end RoundSphere

open RoundSphere

/-! ### Faces of the sup-norm cube -/

section CubeSets

variable {n : ℕ} (r : ℝ)

/-- The face of the cube `‖v‖_∞ ≤ r` with the first `j` coordinates equal to `r`. -/
def cubeFaceV (j : ℕ) : Set (Fin n → ℝ) := {v | ‖v‖ ≤ r ∧ ∀ i : Fin n, (i : ℕ) < j → v i = r}

/-- Its boundary: one of the remaining coordinates is `±r`. -/
def cubeBdryV (j : ℕ) : Set (Fin n → ℝ) :=
  {v | v ∈ cubeFaceV r j ∧ ∃ i : Fin n, j ≤ (i : ℕ) ∧ |v i| = r}

/-- The rest of the boundary of the face `j`: the bottom of coordinate `j`, or a later coordinate
at `±r`. -/
def cubeRestV (j : ℕ) : Set (Fin n → ℝ) :=
  {v | v ∈ cubeFaceV r j ∧ ((∃ i : Fin n, (i : ℕ) = j ∧ v i = -r) ∨
    ∃ i : Fin n, j < (i : ℕ) ∧ |v i| = r)}

/-- An end point of the last edge `Φ₁`: `v_{n-1} = s`. -/
def cubeEndV (s : ℝ) : Set (Fin n → ℝ) :=
  {v | v ∈ cubeFaceV r (n - 1) ∧ ∃ i : Fin n, (i : ℕ) = n - 1 ∧ v i = s}

variable {r}

theorem cubeFaceV_subset (j : ℕ) : cubeFaceV (n := n) r j ⊆ closedBall 0 r :=
  fun _ hv ↦ mem_closedBall_zero_iff.mpr hv.1

theorem isClosed_cubeFaceV (j : ℕ) : IsClosed (cubeFaceV (n := n) r j) := by
  simp only [cubeFaceV, Set.setOf_and, Set.setOf_forall]
  exact (isClosed_le continuous_norm continuous_const).inter
    (isClosed_iInter fun i ↦ isClosed_iInter fun _ ↦
      isClosed_eq (continuous_apply i) continuous_const)

theorem isClosed_abs_eq (i : Fin n) : IsClosed {v : Fin n → ℝ | |v i| = r} :=
  isClosed_eq (continuous_abs.comp (continuous_apply i)) continuous_const

theorem isClosed_cubeBdryV (j : ℕ) : IsClosed (cubeBdryV (n := n) r j) := by
  simp only [cubeBdryV, Set.setOf_and, Set.setOf_exists, Set.setOf_mem_eq]
  exact (isClosed_cubeFaceV j).inter (isClosed_iUnion_of_finite fun i ↦
    isClosed_const.inter (isClosed_abs_eq i))

theorem isClosed_cubeRestV (j : ℕ) : IsClosed (cubeRestV (n := n) r j) := by
  simp only [cubeRestV, Set.setOf_and, Set.setOf_or, Set.setOf_exists, Set.setOf_mem_eq]
  exact (isClosed_cubeFaceV j).inter ((isClosed_iUnion_of_finite fun i ↦
    isClosed_const.inter (isClosed_eq (continuous_apply i) continuous_const)).union
    (isClosed_iUnion_of_finite fun i ↦ isClosed_const.inter (isClosed_abs_eq i)))

theorem isClosed_cubeEndV (s : ℝ) : IsClosed (cubeEndV (n := n) r s) := by
  simp only [cubeEndV, Set.setOf_and, Set.setOf_exists, Set.setOf_mem_eq]
  exact (isClosed_cubeFaceV _).inter (isClosed_iUnion_of_finite fun i ↦
    isClosed_const.inter (isClosed_eq (continuous_apply i) continuous_const))

/-- A point of sup norm `r > 0` has a coordinate `±r`. -/
theorem exists_abs_eq_of_norm_eq {v : Fin n → ℝ} (hr : 0 < r) (hv : ‖v‖ = r) :
    ∃ i, |v i| = r := by
  by_contra h
  push_neg at h
  have : ‖v‖ < r := (pi_norm_lt_iff hr).mpr fun i ↦
    lt_of_le_of_ne (hv ▸ norm_le_pi_norm v i) (by rw [Real.norm_eq_abs]; exact h i)
  exact this.ne hv

end CubeSets

/-! ### The cube flag fixed by the control data -/

namespace ControlData

variable {p : ℕ} (cd : ControlData p)

theorem exists_cubeRadius : ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
    ∀ v : Fin cd.n → ℝ, ‖v‖ ≤ r → dist cd.y (chartV v) < cd.R := by
  have hc : Continuous fun v : Fin cd.n → ℝ ↦ dist cd.y (chartV v) :=
    continuous_const.dist continuous_chartV
  have h0 : dist cd.y (chartV 0) = 0 := by rw [dist_y_eq cd.dist_y_infty, dist_self]
  obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 hc.continuousAt cd.R (cd.r_pos.trans cd.r_lt_R)
  refine ⟨min (δ / 2) 1, by positivity, min_le_right _ _, fun v hv ↦ ?_⟩
  have := h (x := v) (by
    rw [dist_zero_right]; exact hv.trans_lt ((min_le_left _ _).trans_lt (half_lt_self hδ)))
  rw [h0, Real.dist_eq, sub_zero] at this
  exact (le_abs_self _).trans_lt this

/-- **The radius `r_Q` of the cut cube**, a function of `cd` alone. -/
def cubeRadius : ℝ := Classical.choose cd.exists_cubeRadius

theorem cubeRadius_pos : 0 < cd.cubeRadius := (Classical.choose_spec cd.exists_cubeRadius).1

theorem cubeRadius_le_one : cd.cubeRadius ≤ 1 := (Classical.choose_spec cd.exists_cubeRadius).2.1

theorem dist_lt_of_norm_le {v : Fin cd.n → ℝ} (hv : ‖v‖ ≤ cd.cubeRadius) :
    dist cd.y (chartV v) < cd.R :=
  (Classical.choose_spec cd.exists_cubeRadius).2.2 v hv

/-- The closure of the complement of the open cube. -/
def cubeOut : Set (RoundSphere cd.n) := {z | ∀ v, chartV v = z → cd.cubeRadius ≤ ‖v‖}

theorem isClosed_cubeOut : IsClosed cd.cubeOut := by
  have : cd.cubeOutᶜ = chartV '' ball 0 cd.cubeRadius := by
    ext z
    simp only [cubeOut, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_le, Set.mem_image,
      mem_ball_zero_iff, exists_prop]
    exact ⟨fun ⟨v, hv, h⟩ ↦ ⟨v, h, hv⟩, fun ⟨v, h, hv⟩ ↦ ⟨v, hv, h⟩⟩
  rw [← isOpen_compl_iff, this]
  exact isOpenMap_chartV _ isOpen_ball

theorem image_inter {S T : Set (Fin cd.n → ℝ)} {z : RoundSphere cd.n} (hS : z ∈ chartV '' S)
    (hT : z ∈ chartV '' T) : ∃ v ∈ S ∩ T, chartV v = z := by
  obtain ⟨v, hv, rfl⟩ := hS
  obtain ⟨w, hw, hwv⟩ := hT
  exact ⟨v, ⟨hv, chartV_injective hwv ▸ hw⟩, rfl⟩

/-- **The cube cut flag** (simplicial-design §2.5), fixed by `cd`. -/
def cubeFlag : LTheory.CutFlag cd.Cp (RoundSphere cd.n) cd.Z₀ (cd.n - 1) where
  A := cd.cubeOut
  B := chartV '' cubeFaceV cd.cubeRadius 0
  Y k := chartV '' cubeBdryV cd.cubeRadius (cd.n - 1 - k)
  a k := chartV '' cubeRestV cd.cubeRadius (cd.n - 2 - k)
  b k := chartV '' cubeFaceV cd.cubeRadius (cd.n - 1 - k)
  P := chartV '' cubeEndV cd.cubeRadius cd.cubeRadius
  Q := chartV '' cubeEndV cd.cubeRadius (-cd.cubeRadius)
  hZ := cd.isClosedInv_dist_ge cd.R
  hA := cd.isClosedInv_of_isClosed cd.isClosed_cubeOut
  hB := cd.isClosedInv_of_isClosed
    (isClosed_image_chartV (isClosed_cubeFaceV _) (cubeFaceV_subset _))
  ha k := cd.isClosedInv_of_isClosed (isClosed_image_chartV (isClosed_cubeRestV _)
    fun _ hv ↦ cubeFaceV_subset _ hv.1)
  hb k := cd.isClosedInv_of_isClosed
    (isClosed_image_chartV (isClosed_cubeFaceV _) (cubeFaceV_subset _))
  hP := cd.isClosedInv_of_isClosed (isClosed_image_chartV (isClosed_cubeEndV _)
    fun _ hv ↦ cubeFaceV_subset _ hv.1)
  hQ := cd.isClosedInv_of_isClosed (isClosed_image_chartV (isClosed_cubeEndV _)
    fun _ hv ↦ cubeFaceV_subset _ hv.1)
  cover := Set.eq_univ_of_forall fun z ↦ by
    rcases eq_infty_or_chartV z with rfl | ⟨v, rfl⟩
    · exact .inl fun v hv ↦ (chartV_ne_infty v hv).elim
    · rcases le_or_gt cd.cubeRadius ‖v‖ with h | h
      · exact .inl fun w hw ↦ chartV_injective hw ▸ h
      · exact .inr ⟨v, ⟨h.le, fun i hi ↦ absurd hi (Nat.not_lt_zero _)⟩, rfl⟩
  ZA z hz v hv := by
    by_contra h
    exact absurd hz (not_le.mpr (hv ▸ cd.dist_lt_of_norm_le (not_le.mp h).le))
  ZB := Set.disjoint_left.mpr fun z hz ⟨v, hv, hvz⟩ ↦
    absurd hz (not_le.mpr (hvz ▸ cd.dist_lt_of_norm_le hv.1))
  top z hz := by
    obtain ⟨v, hv, rfl⟩ := hz.2
    have hn : ‖v‖ = cd.cubeRadius := le_antisymm hv.1 (hz.1 v rfl)
    obtain ⟨i, hi⟩ := exists_abs_eq_of_norm_eq cd.cubeRadius_pos hn
    exact ⟨v, ⟨⟨hv.1, fun i hi ↦ absurd hi (by omega)⟩, i, by omega, hi⟩, rfl⟩
  succ k z hz := by
    obtain ⟨v, ⟨hv, i, hi, hvi⟩, rfl⟩ := hz
    have hj : cd.n - 1 - (k + 1) = cd.n - 2 - k := by omega
    rw [hj] at hv hi
    rcases lt_or_eq_of_le hi with hi' | hi'
    · exact .inl ⟨v, ⟨hv, .inr ⟨i, hi', hvi⟩⟩, rfl⟩
    · rcases abs_eq cd.cubeRadius_pos.le |>.mp hvi with h | h
      · refine .inr ⟨v, ⟨hv.1, fun i' hi'' ↦ ?_⟩, rfl⟩
        rcases lt_or_eq_of_le (show (i' : ℕ) ≤ cd.n - 2 - k by omega) with h' | h'
        · exact hv.2 i' h'
        · rwa [show i' = i from Fin.ext (h'.trans hi')]
      · exact .inl ⟨v, ⟨hv, .inl ⟨i, hi'.symm, h⟩⟩, rfl⟩
  inter k z hz := by
    obtain ⟨v, ⟨hrest, hface⟩, rfl⟩ := cd.image_inter hz.1 hz.2
    refine ⟨v, ⟨hface, ?_⟩, rfl⟩
    rcases hrest.2 with ⟨i, hi, hvi⟩ | ⟨i, hi, hvi⟩
    · by_cases hlt : (i : ℕ) < cd.n - 1 - k
      · have := hface.2 i hlt
        have := cd.cubeRadius_pos
        linarith
      · exact ⟨i, by omega, by rw [hvi, abs_neg, abs_of_pos cd.cubeRadius_pos]⟩
    · exact ⟨i, by omega, hvi⟩
  PY := Set.image_mono fun v ⟨hv, i, hi, hvi⟩ ↦
    ⟨by rwa [Nat.sub_zero], i, by omega, by rw [hvi, abs_of_pos cd.cubeRadius_pos]⟩
  QY := Set.image_mono fun v ⟨hv, i, hi, hvi⟩ ↦
    ⟨by rwa [Nat.sub_zero], i, by omega, by rw [hvi, abs_neg, abs_of_pos cd.cubeRadius_pos]⟩
  YPQ z hz := by
    obtain ⟨v, ⟨hv, i, hi, hvi⟩, rfl⟩ := hz
    rw [Nat.sub_zero] at hv hi
    have hi' : (i : ℕ) = cd.n - 1 := by omega
    rcases abs_eq cd.cubeRadius_pos.le |>.mp hvi with h | h
    · exact .inl ⟨v, ⟨hv, i, hi', h⟩, rfl⟩
    · exact .inr ⟨v, ⟨hv, i, hi', h⟩, rfl⟩
  PQ := Set.disjoint_left.mpr fun z hP hQ ↦ by
    obtain ⟨v, ⟨⟨-, i, hi, hvi⟩, ⟨-, i', hi', hvi'⟩⟩, -⟩ := cd.image_inter hP hQ
    have : i = i' := Fin.ext (hi.trans hi'.symm)
    subst this
    have := cd.cubeRadius_pos
    linarith

end ControlData

/-- **The cube flag choice** (simplicial-design §2.5): `cd ↦ cd.cubeFlag`. -/
def cubeFlagChoice : FlagChoice := fun _ cd ↦ cd.cubeFlag

/-! ### `PinchSignature` from single cut steps -/

open LTheory AsymptoticCategory

variable (𝕃 : LowerLTheory)

/-- The class `[𝔪_id] ∈ L_N(ℬ_{1,Z₀}(Sⁿ))` of the germ of the identity control map (labels
`q ∘ centre`, `Germ.lean`) after the exterior quotient. -/
abbrev germClass {p : ℕ} (cd : ControlData p) : 𝕃.L cd.B1S cd.N :=
  𝕃.cls cd.B1S cd.N (Lconc.map cd.proj (manifoldGerm cd (ContinuousMap.id _)))

/-- **The single cut steps of Lemma 11.2 on the cube flag**: classes `x k ∈ L_{k+4}(𝒜_{Y k}(Sⁿ))`
(intended: `[∂Φ_{k+1} ⊗ CPcell]` with the boundary structure `𝒟(cubeTop)` of `PinchFace`), the
exterior cut of the germ class and each hemisphere cut equal to `±` the next class (Lemma 4.1 with
the A/B relation `cutBdHtpy`, the B-pair being the cube pair `⊗ CPcell` by `PinchFlag`/`PinchFace`,
controlled by `PinchControl`), and `σ_tail` of the positive end point (`pt ⊗ CPcell`) a sign tail
(`σ(CPcell) = 1`, `cpSymPoincare_unit_sign₄_one`). -/
structure CubeCutSteps {p : ℕ} (cd : ControlData p) where
  x : ∀ k : ℕ, 𝕃.L (cd.cubeFlag.C (scalarHom cd.Cp) k) ((k : ℤ) + 4)
  u₀ : ℤˣ
  u : ℕ → ℤˣ
  cut : cd.cubeFlag.cut (scalarHom cd.Cp) 𝕃 (((cd.n - 1 : ℕ) : ℤ) + 4)
      (𝕃.castDeg _ cd.N_eq (germClass 𝕃 cd)) = u₀ • x (cd.n - 1)
  mvCut : ∀ k, cd.cubeFlag.mvCut (scalarHom cd.Cp) 𝕃 k ((k : ℤ) + 4)
      (𝕃.castDeg _ (LowerLTheory.natDeg_succ k 4) (x (k + 1))) = u k • x k
  last : IsSignTail (𝕃.σtail (scalarHom cd.Cp)
      (𝕃.map ((supportKaroubiFiltration (scalarHom cd.Cp) cd.cubeFlag.P).incl ≫
        forgetControl (scalarHom cd.Cp) (RoundSphere cd.n)) 4
        (projSep 𝕃 cd.cubeFlag.hP cd.cubeFlag.hQ cd.cubeFlag.PY cd.cubeFlag.QY cd.cubeFlag.YPQ
          cd.cubeFlag.PQ 4 (𝕃.castDeg _ (by simp) (x 0)))))

/-- **`PinchSignature` from the cut steps** (Lemma 11.2, (11.4)–(11.5)): for the fibre signature
of the cube flag, `σ(Δ_1[𝔪_id])` is `±` the value on the last class. -/
theorem pinchSignature_of_cutSteps
    (h : ∀ ⦃p : ℕ⦄ [Fact p.Prime] (cd : ControlData p), Nonempty (CubeCutSteps 𝕃 cd)) :
    PinchSignature (fibreSignatureOf 𝕃 cubeFlagChoice) manifoldGerm := by
  intro p _ cd
  obtain ⟨S⟩ := h cd
  change IsSignTail (𝕃.σtail (scalarHom cd.Cp) (cd.delta1 𝕃 cd.cubeFlag (germClass 𝕃 cd)))
  simp only [ControlData.delta1, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  rw [CutFlag.delta_apply, S.cut, Units.smul_def, map_zsmul,
    𝕃.iterDown_eq_of_steps _ 4 _ S.x S.u S.mvCut, Units.smul_def, map_zsmul, map_zsmul, map_zsmul,
    map_zsmul, map_zsmul, map_zsmul, ← Units.smul_def, ← Units.smul_def]
  exact (S.last.units_smul _).units_smul _

end HSFormal
