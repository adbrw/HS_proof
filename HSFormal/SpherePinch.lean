import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The oriented pinch and the round target sphere (Section 7, L492–524)

The target sphere `Sⁿ` of Section 7 is the one-point compactification `OnePoint ℝⁿ` of
coordinate space.

* `HSFormal.pinch ρ`: the oriented pinch `s_ρ : ℝⁿ → Sⁿ`, `v ↦ v / (ρ - ‖v‖)` on `B(0,ρ)` and `∞`
  outside (L492). It is continuous, and a homeomorphism of `B(0,ρ)` onto `Sⁿ ∖ {∞}`
  (`HSFormal.pinchBallHomeomorph`).
* `HSFormal.pinchMap`: its extension `Sⁿ → Sⁿ` by `∞ ↦ ∞`, and `HSFormal.pinchHomotopy`, an
  explicit homotopy rel `∞` from the identity of `Sⁿ` to it (so the pinch has degree one).
* `HSFormal.roundSphere`: stereographic identification of `Sⁿ` with the unit sphere of `ℝⁿ⁺¹`;
  `HSFormal.roundDist` is the induced round (chordal) metric, for which `s_ρ(0)` and `∞` are
  antipodal at distance `2` (L519).
* `HSFormal.SphereSelfMapSurjective`: the classical non-contractibility of spheres, isolated as an
  explicit hypothesis (degree theory is not available in mathlib).
-/

noncomputable section

open Set Filter Metric Module OnePoint
open Topology
open scoped unitInterval

namespace HSFormal

section DivOrInfty

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `a / d` in the one-point compactification, and `∞` when `d ≤ 0`. -/
def divOrInfty (d : ℝ) (a : E) : OnePoint E :=
  if 0 < d then ((d⁻¹ • a : E) : OnePoint E) else ∞

theorem divOrInfty_of_pos {d : ℝ} (hd : 0 < d) (a : E) :
    divOrInfty d a = ((d⁻¹ • a : E) : OnePoint E) := ite_eq_left hd

theorem divOrInfty_of_nonpos {d : ℝ} (hd : d ≤ 0) (a : E) : divOrInfty d a = ∞ :=
  ite_eq_right hd.not_gt

theorem divOrInfty_eq_infty_iff {d : ℝ} {a : E} : divOrInfty d a = ∞ ↔ d ≤ 0 := by
  rcases lt_or_ge 0 d with hd | hd
  · simp [divOrInfty_of_pos hd, hd.not_ge]
  · simp [divOrInfty_of_nonpos hd, hd]

omit [NormedSpace ℝ E] in
/-- Every neighbourhood of `∞` contains all points of sufficiently large norm. -/
theorem exists_forall_norm_gt_mem {s : Set (OnePoint E)} (hs : s ∈ 𝓝 (∞ : OnePoint E)) :
    ∃ R : ℝ, ∀ w : E, R < ‖w‖ → (w : OnePoint E) ∈ s := by
  obtain ⟨L, ⟨-, hL⟩, hLs⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.1 hs
  obtain ⟨R, hR⟩ := hL.isBounded.subset_closedBall 0
  refine ⟨R, fun w hw => hLs (Or.inl ⟨w, fun hwL => ?_, rfl⟩)⟩
  have := mem_closedBall_zero_iff.1 (hR hwL)
  linarith

theorem continuous_divOrInfty {X : Type*} [TopologicalSpace X] {d : X → ℝ} {a : X → E}
    (hd : Continuous d) (ha : Continuous a) (h : ∀ x, d x ≤ 0 → a x ≠ 0) :
    Continuous fun x => divOrInfty (d x) (a x) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  rcases lt_or_ge 0 (d x) with hx | hx
  · have hev : (fun y => (((d y)⁻¹ • a y : E) : OnePoint E)) =ᶠ[𝓝 x]
        fun y => divOrInfty (d y) (a y) := by
      filter_upwards [hd.continuousAt.eventually (lt_mem_nhds hx)] with y hy
      rw [divOrInfty_of_pos hy]
    exact (OnePoint.continuous_coe.continuousAt.comp
      ((hd.continuousAt.inv₀ hx.ne').smul ha.continuousAt)).congr hev
  · have hax : 0 < ‖a x‖ := norm_pos_iff.2 (h x hx)
    show Tendsto _ (𝓝 x) (𝓝 (divOrInfty (d x) (a x)))
    rw [divOrInfty_of_nonpos hx]
    intro s hs
    rw [Filter.mem_map]
    obtain ⟨R, hR⟩ := exists_forall_norm_gt_mem hs
    set δ := ‖a x‖ / (2 * (|R| + 1)) with hδdef
    have hδ : 0 < δ := by positivity
    have hδR : (|R| + 1) * δ = ‖a x‖ / 2 := by
      rw [hδdef]
      field_simp
    have h1 : ∀ᶠ y in 𝓝 x, ‖a x‖ / 2 < ‖a y‖ :=
      (continuous_norm.comp ha).continuousAt.eventually (lt_mem_nhds (half_lt_self hax))
    have h2 : ∀ᶠ y in 𝓝 x, d y < δ := hd.continuousAt.eventually (gt_mem_nhds (by linarith))
    filter_upwards [h1, h2] with y hy1 hy2
    rcases le_or_gt (d y) 0 with hy | hy
    · rw [mem_preimage, divOrInfty_of_nonpos hy]
      exact mem_of_mem_nhds hs
    · rw [mem_preimage, divOrInfty_of_pos hy]
      apply hR
      rw [norm_smul, norm_inv, Real.norm_of_nonneg hy.le, inv_mul_eq_div, lt_div_iff₀ hy]
      calc R * d y ≤ |R| * d y := mul_le_mul_of_nonneg_right (le_abs_self R) hy.le
        _ ≤ |R| * δ := mul_le_mul_of_nonneg_left hy2.le (abs_nonneg R)
        _ < (|R| + 1) * δ := by nlinarith
        _ < ‖a y‖ := by rw [hδR]; exact hy1

end DivOrInfty

section Extension

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- A continuous family `g : X × Y → OnePoint Z` that tends to `∞` off compact subsets of `Y`,
uniformly in `X`, extends continuously to `X × OnePoint Y` by `∞` at `∞`. -/
theorem continuous_elim_prod {g : X × Y → OnePoint Z} (hg : Continuous g)
    (hinf : ∀ s ∈ 𝓝 (∞ : OnePoint Z), ∃ K : Set Y, IsClosed K ∧ IsCompact K ∧
      ∀ x, ∀ y ∉ K, g (x, y) ∈ s) :
    Continuous fun q : X × OnePoint Y => q.2.elim ∞ fun y => g (q.1, y) := by
  refine continuous_iff_continuousAt.2 fun ⟨x, z⟩ => ?_
  induction z using OnePoint.rec with
  | infty =>
    intro s hs
    obtain ⟨K, hKc, hKk, hK⟩ := hinf s hs
    have hU : (univ : Set X) ×ˢ (((↑) '' K)ᶜ : Set (OnePoint Y)) ∈ 𝓝 (x, (∞ : OnePoint Y)) :=
      prod_mem_nhds univ_mem
        ((isOpen_compl_image_coe.2 ⟨hKc, hKk⟩).mem_nhds infty_notMem_image_coe)
    rw [Filter.mem_map]
    filter_upwards [hU] with q hq
    obtain ⟨x', z'⟩ := q
    induction z' using OnePoint.rec with
    | infty => exact mem_preimage.2 (mem_of_mem_nhds hs)
    | coe y => exact hK x' y fun hy => hq.2 ⟨y, hy, rfl⟩
  | coe y =>
    have hι : IsOpenEmbedding (Prod.map (id : X → X) ((↑) : Y → OnePoint Y)) :=
      IsOpenEmbedding.id.prodMap OnePoint.isOpenEmbedding_coe
    exact (hι.continuousAt_iff (g := fun q : X × OnePoint Y => q.2.elim ∞ fun y => g (q.1, y))
      (x := (x, y))).1 hg.continuousAt

/-- One-variable version of `HSFormal.continuous_elim_prod`. -/
theorem continuous_elim {g : Y → OnePoint Z} (hg : Continuous g)
    (hinf : ∀ s ∈ 𝓝 (∞ : OnePoint Z), ∃ K : Set Y, IsClosed K ∧ IsCompact K ∧
      ∀ y ∉ K, g y ∈ s) :
    Continuous fun z : OnePoint Y => z.elim ∞ g :=
  (continuous_elim_prod (X := Unit) (g := fun q => g q.2) (hg.comp continuous_snd)
    fun s hs => (hinf s hs).imp fun _ hK => ⟨hK.1, hK.2.1, fun _ y hy => hK.2.2 y hy⟩).comp
    (continuous_const.prodMk continuous_id : Continuous fun z : OnePoint Y => ((), z))

end Extension

section Pinch

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The oriented pinch `s_ρ` (L492): `v ↦ v / (ρ - ‖v‖)` on `B(0,ρ)`, and `∞` outside. -/
def pinch (ρ : ℝ) (v : E) : OnePoint E := divOrInfty (ρ - ‖v‖) v

theorem pinch_eq_infty_iff {ρ : ℝ} {v : E} : pinch ρ v = ∞ ↔ ρ ≤ ‖v‖ := by
  rw [pinch, divOrInfty_eq_infty_iff, sub_nonpos]

theorem pinch_of_le {ρ : ℝ} {v : E} (h : ρ ≤ ‖v‖) : pinch ρ v = ∞ := pinch_eq_infty_iff.2 h

theorem pinch_of_lt {ρ : ℝ} {v : E} (h : ‖v‖ < ρ) :
    pinch ρ v = (((ρ - ‖v‖)⁻¹ • v : E) : OnePoint E) :=
  divOrInfty_of_pos (sub_pos.2 h) v

theorem pinch_zero {ρ : ℝ} (hρ : 0 < ρ) : pinch ρ (0 : E) = ((0 : E) : OnePoint E) := by
  rw [pinch_of_lt (by simpa using hρ), smul_zero]

theorem continuous_pinch {ρ : ℝ} (hρ : 0 < ρ) : Continuous (pinch (E := E) ρ) :=
  continuous_divOrInfty (continuous_const.sub continuous_norm) continuous_id fun v hv h0 => by
    simp only [h0, norm_zero, sub_zero] at hv
    linarith

/-- The inverse `w ↦ ρ w / (1 + ‖w‖)` of the pinch on `B(0,ρ)`. -/
def pinchBallInv {ρ : ℝ} (hρ : 0 < ρ) (w : E) : ball (0 : E) ρ :=
  ⟨(ρ / (1 + ‖w‖)) • w, by
    have h1 : 0 < 1 + ‖w‖ := by positivity
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (div_pos hρ h1).le, div_mul_eq_mul_div,
      div_lt_iff₀ h1]
    nlinarith [norm_nonneg w]⟩

theorem pinchBallInv_left {ρ : ℝ} (hρ : 0 < ρ) (v : ball (0 : E) ρ) :
    pinchBallInv hρ ((ρ - ‖(v : E)‖)⁻¹ • (v : E)) = v := by
  obtain ⟨v, hv⟩ := v
  have hpos : 0 < ρ - ‖v‖ := sub_pos.2 (mem_ball_zero_iff.1 hv)
  apply Subtype.ext
  simp only [pinchBallInv]
  rw [norm_smul, norm_inv, Real.norm_of_nonneg hpos.le, smul_smul]
  convert one_smul ℝ v using 2
  field_simp
  ring

theorem pinchBallInv_right {ρ : ℝ} (hρ : 0 < ρ) (w : E) :
    (ρ - ‖(pinchBallInv hρ w : E)‖)⁻¹ • (pinchBallInv hρ w : E) = w := by
  have hpos : 0 < 1 + ‖w‖ := by positivity
  simp only [pinchBallInv]
  rw [norm_smul, Real.norm_of_nonneg (div_pos hρ hpos).le, smul_smul]
  convert one_smul ℝ w using 2
  field_simp
  ring

/-- `s_ρ` is a homeomorphism of `B(0,ρ)` onto `ℝⁿ = Sⁿ ∖ {∞}`, with inverse `w ↦ ρ w / (1 + ‖w‖)`. -/
def pinchBallHomeomorph {ρ : ℝ} (hρ : 0 < ρ) : ball (0 : E) ρ ≃ₜ E where
  toFun v := (ρ - ‖(v : E)‖)⁻¹ • (v : E)
  invFun := pinchBallInv hρ
  left_inv := pinchBallInv_left hρ
  right_inv := pinchBallInv_right hρ
  continuous_toFun := by
    refine Continuous.smul ?_ continuous_subtype_val
    exact (continuous_const.sub (continuous_norm.comp continuous_subtype_val)).inv₀ fun v =>
      (sub_pos.2 (mem_ball_zero_iff.1 v.2)).ne'
  continuous_invFun :=
    ((continuous_const.div (continuous_const.add continuous_norm) fun w =>
      (add_pos_of_pos_of_nonneg one_pos (norm_nonneg w)).ne').smul continuous_id).subtype_mk _

theorem pinch_coe_ball {ρ : ℝ} (hρ : 0 < ρ) (v : ball (0 : E) ρ) :
    pinch ρ (v : E) = ((pinchBallHomeomorph hρ v : E) : OnePoint E) :=
  pinch_of_lt (mem_ball_zero_iff.1 v.2)

/-- The scaling family `v ↦ v / (1 - t (1 - ρ + ‖v‖))`, from the identity (`t = 0`) to `s_ρ`. -/
def pinchHomotopyFun (ρ : ℝ) (q : I × E) : OnePoint E :=
  divOrInfty (1 - (q.1 : ℝ) * (1 - ρ + ‖q.2‖)) q.2

theorem continuous_pinchHomotopyFun {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    Continuous (pinchHomotopyFun (E := E) ρ) := by
  refine continuous_divOrInfty (continuous_const.sub ((continuous_subtype_val.comp
    continuous_fst).mul (continuous_const.add (continuous_norm.comp continuous_snd))))
    continuous_snd fun q hq h0 => ?_
  rw [h0, norm_zero, add_zero] at hq
  nlinarith [q.1.2.1, q.1.2.2]

variable [ProperSpace E]

/-- The pinch on the compactified coordinate space, `∞ ↦ ∞`. -/
def pinchMap {ρ : ℝ} (hρ : 0 < ρ) : C(OnePoint E, OnePoint E) where
  toFun z := z.elim ∞ (pinch ρ)
  continuous_toFun := continuous_elim (continuous_pinch hρ) fun s hs =>
    ⟨closedBall 0 ρ, isClosed_closedBall, isCompact_closedBall 0 ρ, fun y hy => by
      rw [pinch_of_le (by simpa using (not_le.1 fun h => hy (mem_closedBall_zero_iff.2 h)).le)]
      exact mem_of_mem_nhds hs⟩

@[simp]
theorem pinchMap_infty {ρ : ℝ} (hρ : 0 < ρ) : pinchMap (E := E) hρ ∞ = ∞ := rfl

@[simp]
theorem pinchMap_coe {ρ : ℝ} (hρ : 0 < ρ) (v : E) : pinchMap hρ (v : OnePoint E) = pinch ρ v :=
  rfl

/-- The pinch is homotopic rel `∞` to the identity of `Sⁿ`; in particular it has degree one. -/
def pinchHomotopy {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    (ContinuousMap.id (OnePoint E)).HomotopyRel (pinchMap hρ) {∞} where
  toFun q := q.2.elim ∞ fun v => pinchHomotopyFun ρ (q.1, v)
  continuous_toFun := by
    refine continuous_elim_prod (continuous_pinchHomotopyFun hρ hρ1) fun s hs => ?_
    obtain ⟨R, hR⟩ := exists_forall_norm_gt_mem hs
    refine ⟨closedBall 0 R, isClosed_closedBall, isCompact_closedBall 0 R, fun t v hv => ?_⟩
    have hvR : R < ‖v‖ := by simpa using hv
    rcases le_or_gt (1 - (t : ℝ) * (1 - ρ + ‖v‖)) 0 with hd | hd
    · rw [pinchHomotopyFun, divOrInfty_of_nonpos hd]
      exact mem_of_mem_nhds hs
    · rw [pinchHomotopyFun, divOrInfty_of_pos hd]
      apply hR
      have hd1 : 1 - (t : ℝ) * (1 - ρ + ‖v‖) ≤ 1 := by
        nlinarith [t.2.1, norm_nonneg v]
      rw [norm_smul, norm_inv, Real.norm_of_nonneg hd.le, inv_mul_eq_div]
      exact hvR.trans_le (le_div_self (norm_nonneg v) hd hd1)
  map_zero_left z := by
    induction z using OnePoint.rec with
    | infty => rfl
    | coe v => simp [pinchHomotopyFun, divOrInfty_of_pos one_pos]
  map_one_left z := by
    induction z using OnePoint.rec with
    | infty => rfl
    | coe v =>
      show divOrInfty (1 - ((1 : I) : ℝ) * (1 - ρ + ‖v‖)) v = pinch ρ v
      rw [Set.Icc.coe_one, pinch]
      congr 1
      ring
  prop' t z hz := by
    rw [mem_singleton_iff] at hz
    subst hz
    rfl

theorem pinchMap_homotopicRel_id {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    (pinchMap (E := E) hρ).HomotopicRel (ContinuousMap.id _) {∞} :=
  ⟨(pinchHomotopy hρ hρ1).symm⟩

end Pinch

section RoundSphere

/-- The north pole of the unit sphere in `ℝⁿ⁺¹`. -/
def northPole (n : ℕ) : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single 0 1

theorem norm_northPole (n : ℕ) : ‖northPole n‖ = 1 := by simp [northPole]

/-- A linear identification of `ℝⁿ` with the equatorial hyperplane. -/
def hyperplaneEquiv (n : ℕ) :
    EuclideanSpace ℝ (Fin n) ≃L[ℝ] (ℝ ∙ northPole n)ᗮ :=
  haveI : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := ⟨by simp⟩
  (FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq (by
    rw [Submodule.finrank_orthogonal_span_singleton (n := n) (by
      intro h; have := norm_northPole n; rw [h, norm_zero] at this; exact zero_ne_one this)]
    simp)).some

/-- The stereographic identification of `Sⁿ = OnePoint ℝⁿ` with the round unit sphere of `ℝⁿ⁺¹`;
`∞` goes to the north pole and `0` to the south pole. -/
def roundSphere (n : ℕ) :
    OnePoint (EuclideanSpace ℝ (Fin n)) ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  (hyperplaneEquiv n).toHomeomorph.onePointCongr.trans
    (onePointHyperplaneHomeoUnitSphere (norm_northPole n))

theorem roundSphere_infty (n : ℕ) :
    (roundSphere n ∞ : EuclideanSpace ℝ (Fin (n + 1))) = northPole n := rfl

theorem roundSphere_zero (n : ℕ) :
    (roundSphere n ((0 : EuclideanSpace ℝ (Fin n)) : OnePoint (EuclideanSpace ℝ (Fin n))) :
      EuclideanSpace ℝ (Fin (n + 1))) = -northPole n := by
  have h1 : roundSphere n ((0 : EuclideanSpace ℝ (Fin n)) : OnePoint (EuclideanSpace ℝ (Fin n))) =
      stereoInvFun (norm_northPole n) (hyperplaneEquiv n 0) := rfl
  rw [h1, map_zero, stereoInvFun_apply]
  norm_num [smul_smul]

/-- The round (chordal) metric on `Sⁿ`, transported from the unit sphere of `ℝⁿ⁺¹`. -/
def roundDist {n : ℕ} (z z' : OnePoint (EuclideanSpace ℝ (Fin n))) : ℝ :=
  dist (roundSphere n z) (roundSphere n z')

theorem continuous_roundDist {n : ℕ} :
    Continuous fun q : OnePoint (EuclideanSpace ℝ (Fin n)) × OnePoint _ => roundDist q.1 q.2 :=
  ((roundSphere n).continuous.comp continuous_fst).dist
    ((roundSphere n).continuous.comp continuous_snd)

theorem continuous_roundDist_left {n : ℕ} (z₀ : OnePoint (EuclideanSpace ℝ (Fin n))) :
    Continuous fun z => roundDist z₀ z :=
  continuous_const.dist (roundSphere n).continuous

/-- `0` and `∞` are antipodal for the round metric. -/
theorem roundDist_zero_infty (n : ℕ) :
    roundDist ((0 : EuclideanSpace ℝ (Fin n)) : OnePoint (EuclideanSpace ℝ (Fin n))) ∞ = 2 := by
  rw [roundDist, Subtype.dist_eq, roundSphere_zero, roundSphere_infty, dist_eq_norm,
    ← neg_add', norm_neg, ← two_smul ℝ, norm_smul, norm_northPole]
  norm_num

end RoundSphere

/-- **Non-contractibility of spheres** (Brouwer; e.g. [Hat02, §2.2]): a continuous self-map of the
`n`-sphere `Sⁿ = OnePoint ℝⁿ` that is homotopic to the identity is surjective. (A non-surjective
map factors through `Sⁿ ∖ {pt} ≅ ℝⁿ`, hence is nullhomotopic, while the identity of `Sⁿ` is not:
`Hₙ(Sⁿ) ≠ 0` for `n ≥ 1`, and `S⁰` is disconnected.) This is the only consequence of the degree-one
statement of L500 used in Section 7; it is an explicit hypothesis, never an axiom. -/
def SphereSelfMapSurjective : Prop :=
  ∀ (n : ℕ) (g : C(OnePoint (EuclideanSpace ℝ (Fin n)), OnePoint (EuclideanSpace ℝ (Fin n)))),
    g.Homotopic (ContinuousMap.id _) → Function.Surjective g

end HSFormal
