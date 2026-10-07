import HSFormal.Newman.Claims
import HSFormal.WeakInputs

/-!
# N9. Newman's theorem for prime order (Newman blueprint, module N9)

`newmanPrimeOrder_of_degreeEqZeroOfFree : DegreeEqZeroOfFree → NewmanPrimeOrder`: the transfer
vanishing lemma (N7, `HSFormal/Newman/TransferStatement.lean`) implies
`HSFormal.NewmanPrimeOrder` (blueprint §2.7).

* `subsingleton_of_chartedSpace_zero`: a connected manifold modelled on `ℝ⁰` is a point.
* `chartDom φ f q`, `chartConj φ f`: the transport of a periodic `f` to a chart `φ`
  (`chartConj φ f = φ ∘ f ∘ φ⁻¹` on `φ (chartDom φ f q)`, the points whose first `q` iterates
  stay in the chart source).
* `exists_uniform_radius`: the uniform `ε` for `(M, U)`, chosen from one chart ball in `U`
  before `q` and `f`; Claim 1 then gives a nonempty open set of fixed points.
* `isClosed_interior_fixedPoints`: the interior of the fixed point set is closed (Claim 2′ at a
  point of the closure of the non-fixed locus nearest to the centre of a fixed ball).
* `newmanPrimeOrder_of_degreeEqZeroOfFree`: connectedness concludes.
-/

open Set Function Metric Topology Filter

namespace HSFormal.Newman

/-! ### Dimension zero -/

/-- A connected Hausdorff manifold modelled on `ℝ⁰` is a point. -/
theorem subsingleton_of_chartedSpace_zero (M : Type*) [TopologicalSpace M] [T1Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 0)) M] [ConnectedSpace M] : Subsingleton M := by
  refine ⟨fun x y => ?_⟩
  have hsrc : (chartAt (EuclideanSpace ℝ (Fin 0)) x).source = {x} := by
    ext z
    constructor
    · intro hz
      exact (chartAt (EuclideanSpace ℝ (Fin 0)) x).injOn hz (mem_chart_source _ x)
        (Subsingleton.elim _ _)
    · rintro rfl
      exact mem_chart_source _ z
  have hopen : IsOpen ({x} : Set M) := hsrc ▸ (chartAt (EuclideanSpace ℝ (Fin 0)) x).open_source
  rcases isClopen_iff.1 ⟨isClosed_singleton, hopen⟩ with h | h
  · exact absurd h (singleton_nonempty x).ne_empty
  · have : y ∈ ({x} : Set M) := h ▸ mem_univ y
    exact (mem_singleton_iff.1 this).symm

/-! ### Transport of a periodic map to a chart -/

section Transport

variable {M : Type*} [TopologicalSpace M] {H : Type*} [TopologicalSpace H]

/-- The points whose first `q` iterates under `f` lie in the source of `φ`. -/
def chartDom (φ : OpenPartialHomeomorph M H) (f : M → M) (q : ℕ) : Set M :=
  {x | ∀ k < q, f^[k] x ∈ φ.source}

/-- The conjugate `φ ∘ f ∘ φ⁻¹`. -/
def chartConj (φ : OpenPartialHomeomorph M H) (f : M → M) : H → H :=
  fun z => φ (f (φ.symm z))

variable {φ : OpenPartialHomeomorph M H} {f : M → M} {q : ℕ}

lemma isOpen_chartDom (hf : Continuous f) : IsOpen (chartDom φ f q) := by
  have : chartDom φ f q = ⋂ k ∈ Iio q, f^[k] ⁻¹' φ.source := by
    ext x
    simp [chartDom]
  rw [this]
  exact (finite_Iio q).isOpen_biInter fun k _ => φ.open_source.preimage (hf.iterate k)

lemma chartDom_subset (hq : 0 < q) : chartDom φ f q ⊆ φ.source := fun _ hx => hx 0 hq

lemma mapsTo_chartDom (hper : ∀ x, f^[q] x = x) :
    MapsTo f (chartDom φ f q) (chartDom φ f q) := by
  intro x hx k hk
  rw [← iterate_succ_apply]
  rcases Nat.lt_or_ge (k + 1) q with h | h
  · exact hx _ h
  · rw [show k.succ = q by omega, hper x]
    exact hx 0 (by omega)

lemma isOpen_image_chartDom (hf : Continuous f) (hq : 0 < q) : IsOpen (φ '' chartDom φ f q) :=
  φ.isOpen_image_of_subset_source (isOpen_chartDom hf) (chartDom_subset hq)

lemma image_chartDom_subset_target (hq : 0 < q) : φ '' chartDom φ f q ⊆ φ.target := by
  rintro _ ⟨x, hx, rfl⟩
  exact φ.map_source (chartDom_subset hq hx)

lemma symm_mem_chartDom (hq : 0 < q) {z : H} (hz : z ∈ φ '' chartDom φ f q) :
    φ.symm z ∈ chartDom φ f q := by
  obtain ⟨x, hx, rfl⟩ := hz
  rwa [φ.left_inv (chartDom_subset hq hx)]

lemma mapsTo_chartConj (hq : 0 < q) (hper : ∀ x, f^[q] x = x) :
    MapsTo (chartConj φ f) (φ '' chartDom φ f q) (φ '' chartDom φ f q) := fun _ hz =>
  ⟨_, mapsTo_chartDom hper (symm_mem_chartDom hq hz), rfl⟩

lemma chartConj_iterate (hq : 0 < q) (hper : ∀ x, f^[q] x = x) (k : ℕ) {z : H}
    (hz : z ∈ φ '' chartDom φ f q) : (chartConj φ f)^[k] z = φ (f^[k] (φ.symm z)) := by
  induction k generalizing z with
  | zero => exact (φ.right_inv (image_chartDom_subset_target hq hz)).symm
  | succ k ih =>
    rw [iterate_succ_apply, ih (mapsTo_chartConj hq hper hz)]
    change φ (f^[k] (φ.symm (φ (f (φ.symm z))))) = _
    rw [φ.left_inv (chartDom_subset hq (mapsTo_chartDom hper (symm_mem_chartDom hq hz))),
      ← iterate_succ_apply]

lemma chartConj_iterate_self (hq : 0 < q) (hper : ∀ x, f^[q] x = x) {z : H}
    (hz : z ∈ φ '' chartDom φ f q) : (chartConj φ f)^[q] z = z := by
  rw [chartConj_iterate hq hper q hz, hper, φ.right_inv (image_chartDom_subset_target hq hz)]

lemma continuousOn_chartConj (hf : Continuous f) (hq : 0 < q) (hper : ∀ x, f^[q] x = x) :
    ContinuousOn (chartConj φ f) (φ '' chartDom φ f q) := by
  have h1 : ContinuousOn φ.symm (φ '' chartDom φ f q) :=
    φ.continuousOn_symm.mono (image_chartDom_subset_target hq)
  have h2 : ContinuousOn (fun z => f (φ.symm z)) (φ '' chartDom φ f q) :=
    hf.comp_continuousOn h1
  exact φ.continuousOn.comp h2 fun z hz =>
    chartDom_subset hq (mapsTo_chartDom hper (symm_mem_chartDom hq hz))

lemma chartConj_eq_iff (hq : 0 < q) (hper : ∀ x, f^[q] x = x) {z : H}
    (hz : z ∈ φ '' chartDom φ f q) : chartConj φ f z = z ↔ f (φ.symm z) = φ.symm z := by
  have hx := symm_mem_chartDom hq hz
  have hzt := φ.right_inv (image_chartDom_subset_target hq hz)
  constructor
  · intro h
    refine φ.injOn (chartDom_subset hq (mapsTo_chartDom hper hx)) (chartDom_subset hq hx) ?_
    change chartConj φ f z = φ (φ.symm z)
    rw [h, hzt]
  · intro h
    change φ (f (φ.symm z)) = z
    rw [h, hzt]

end Transport

/-! ### The uniform `ε` and Claim 1 -/

section Main

/-- **The uniform `ε`** (§2.7). For a nonempty open `U` there is `ε > 0`, chosen before `q` and
`f`, such that every `f` of prime period `q` moving the points of `U` by less than `ε` along
their orbits fixes a nonempty open set pointwise. -/
theorem exists_uniform_radius (hT : DegreeEqZeroOfFree) {m : ℕ} {M : Type*} [MetricSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M] {U : Set M} (hU : IsOpen U)
    (hne : U.Nonempty) :
    ∃ ε > 0, ∀ q : ℕ, q.Prime → ∀ f : M ≃ₜ M, (∀ x, f^[q] x = x) →
      (∀ k : ℕ, ∀ x ∈ U, dist (f^[k] x) x < ε) → (interior {x | f x = x}).Nonempty := by
  obtain ⟨x₀, hx₀⟩ := hne
  set φ := chartAt (EuclideanSpace ℝ (Fin (m + 1))) x₀ with hφ
  have hsrc : x₀ ∈ φ.source := mem_chart_source _ x₀
  have hUo : IsOpen (φ '' (U ∩ φ.source)) :=
    φ.isOpen_image_of_subset_source (hU.inter φ.open_source) inter_subset_right
  obtain ⟨r₀, hr₀, hr₀U⟩ := Metric.isOpen_iff.1 hUo (φ x₀) ⟨x₀, ⟨hx₀, hsrc⟩, rfl⟩
  have hr : 0 < r₀ / 2 := by positivity
  have hcU : closedBall (φ x₀) (r₀ / 2) ⊆ φ '' (U ∩ φ.source) :=
    (closedBall_subset_ball (by linarith)).trans hr₀U
  generalize r₀ / 2 = r at hr hcU
  have htgt : closedBall (φ x₀) r ⊆ φ.target := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hcU hz
    exact φ.map_source hx.2
  -- the compact `D₁ = φ⁻¹ B̄(c, r) ⊆ U`
  have hD₁c : IsCompact (φ.symm '' closedBall (φ x₀) r) :=
    (isCompact_closedBall _ r).image_of_continuousOn (φ.continuousOn_symm.mono htgt)
  have hD₁U : φ.symm '' closedBall (φ x₀) r ⊆ U ∩ φ.source := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hcU hz
    rwa [φ.left_inv hx.2]
  obtain ⟨δ₁, hδ₁, hδ₁s⟩ :=
    hD₁c.exists_thickening_subset_open φ.open_source (hD₁U.trans inter_subset_right)
  have hunif := hD₁c.uniformContinuousAt_of_continuousAt φ
    (fun x hx => φ.continuousAt (hD₁U hx).2)
    (Metric.dist_mem_uniformity (show (0 : ℝ) < r / 32 by positivity))
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := Metric.mem_uniformity_dist.1 hunif
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun q hq f hfq hsmall => ?_⟩
  have hq0 : 0 < q := hq.pos
  -- transport to the chart
  have hD₁dom : φ.symm '' closedBall (φ x₀) r ⊆ chartDom φ f q := fun x hx k _ =>
    hδ₁s (mem_thickening_iff.2 ⟨x, hx, (hsmall k x (hD₁U hx).1).trans_le (min_le_left _ _)⟩)
  have hballV : closedBall (φ x₀) r ⊆ φ '' chartDom φ f q := fun z hz =>
    ⟨φ.symm z, hD₁dom ⟨z, hz, rfl⟩, φ.right_inv (htgt hz)⟩
  have hsmall' : ∀ z ∈ closedBall (φ x₀) r, ∀ k,
      dist ((chartConj φ f)^[k] z) z ≤ r / 32 := by
    intro z hz k
    rw [chartConj_iterate hq0 hfq k (hballV hz)]
    have hx : φ.symm z ∈ φ.symm '' closedBall (φ x₀) r := ⟨z, hz, rfl⟩
    have hd : dist (φ.symm z) (f^[k] (φ.symm z)) < δ₂ := by
      rw [dist_comm]
      exact (hsmall k _ (hD₁U hx).1).trans_le (min_le_right _ _)
    have h' : dist (φ (φ.symm z)) (φ (f^[k] (φ.symm z))) < r / 32 := hδ₂' hd hx
    rw [φ.right_inv (htgt hz)] at h'
    rw [dist_comm]
    exact h'.le
  have hfixball := fixed_of_small_orbits hT hq (isOpen_image_chartDom f.continuous hq0)
    (mapsTo_chartConj hq0 hfq) (continuousOn_chartConj f.continuous hq0 hfq)
    (fun z hz => chartConj_iterate_self hq0 hfq hz) (by positivity) hballV hsmall'
  -- `f` fixes `φ⁻¹ B(c, r / 2)`
  have hbt : ball (φ x₀) (r / 2) ⊆ closedBall (φ x₀) r :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  refine ⟨x₀, mem_interior.2 ⟨φ.symm '' ball (φ x₀) (r / 2), ?_,
    φ.isOpen_image_symm_of_subset_target isOpen_ball (hbt.trans htgt),
    ⟨φ x₀, mem_ball_self (by positivity), φ.left_inv hsrc⟩⟩⟩
  rintro _ ⟨z, hz, rfl⟩
  exact (chartConj_eq_iff hq0 hfq (hballV (hbt hz))).1 (hfixball z hz)

/-! ### Closedness of the interior of the fixed point set (Claim 2′) -/

/-- The interior of the fixed point set of a homeomorphism of prime period is closed (§2.7). -/
theorem isClosed_interior_fixedPoints (hT : DegreeEqZeroOfFree) {m : ℕ} {M : Type*}
    [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M] {q : ℕ} (hq : q.Prime)
    (f : M ≃ₜ M) (hfq : ∀ x, f^[q] x = x) : IsClosed (interior {x | f x = x}) := by
  have hq0 : 0 < q := hq.pos
  rw [← closure_subset_iff_isClosed]
  intro x₁ hx₁
  by_contra hx₁O
  have hFcl : IsClosed {x | f x = x} := isClosed_eq f.continuous continuous_id
  have hfx₁ : f x₁ = x₁ := by
    have := closure_mono interior_subset hx₁
    rwa [hFcl.closure_eq] at this
  set ψ := chartAt (EuclideanSpace ℝ (Fin (m + 1))) x₁ with hψ
  have hx₁src : x₁ ∈ ψ.source := mem_chart_source _ x₁
  have hx₁dom : x₁ ∈ chartDom ψ f q := fun k _ => by rw [iterate_fixed hfx₁]; exact hx₁src
  have hV : IsOpen (ψ '' chartDom ψ f q) := isOpen_image_chartDom f.continuous hq0
  have hgc : ContinuousOn (chartConj ψ f) (ψ '' chartDom ψ f q) :=
    continuousOn_chartConj f.continuous hq0 hfq
  have hz₁V : ψ x₁ ∈ ψ '' chartDom ψ f q := ⟨x₁, hx₁dom, rfl⟩
  obtain ⟨η, hη, hηV⟩ := Metric.isOpen_iff.1 hV (ψ x₁) hz₁V
  -- a point `x'` of `O = interior (Fix f)` with `ψ x'` within `η / 4` of `ψ x₁`
  have hnhd : chartDom ψ f q ∩ ψ ⁻¹' ball (ψ x₁) (η / 4) ∈ 𝓝 x₁ :=
    inter_mem ((isOpen_chartDom f.continuous).mem_nhds hx₁dom)
      ((ψ.continuousAt hx₁src).preimage_mem_nhds (ball_mem_nhds _ (by positivity)))
  obtain ⟨x', ⟨hx'dom, hx'b⟩, hx'O⟩ := mem_closure_iff_nhds.1 hx₁ _ hnhd
  have hOV : IsOpen (ψ '' (interior {x | f x = x} ∩ chartDom ψ f q)) :=
    ψ.isOpen_image_of_subset_source (isOpen_interior.inter (isOpen_chartDom f.continuous))
      (inter_subset_right.trans (chartDom_subset hq0))
  obtain ⟨t₀, ht₀, ht₀O⟩ := Metric.isOpen_iff.1 hOV (ψ x') ⟨x', ⟨hx'O, hx'dom⟩, rfl⟩
  have ha₀ : dist (ψ x') (ψ x₁) < η / 4 := hx'b
  generalize ψ x' = a₀ at ha₀ ht₀O
  -- `B(a₀, t₀)` is fixed by the conjugate `g`
  have hfixO : ∀ z ∈ ball a₀ t₀, z ∈ ψ '' chartDom ψ f q ∧ chartConj ψ f z = z := by
    intro z hz
    obtain ⟨x, ⟨hxO, hxdom⟩, rfl⟩ := ht₀O hz
    have hzV : ψ x ∈ ψ '' chartDom ψ f q := ⟨x, hxdom, rfl⟩
    refine ⟨hzV, (chartConj_eq_iff hq0 hfq hzV).2 ?_⟩
    rw [ψ.left_inv (chartDom_subset hq0 hxdom)]
    have h2 : x ∈ {x | f x = x} := interior_subset hxO
    exact h2
  -- the non-fixed locus `NF` of `g`, and `ψ x₁ ∈ closure NF`
  have hNFo : IsOpen ((ψ '' chartDom ψ f q) \ {z | chartConj ψ f z = z}) :=
    isOpen_diff_fixedPoints hV hgc
  have hz₁NF : ψ x₁ ∈ closure ((ψ '' chartDom ψ f q) \ {z | chartConj ψ f z = z}) := by
    rw [Metric.mem_closure_iff]
    intro s hs
    have hopen : IsOpen (ψ.symm '' (ball (ψ x₁) s ∩ ψ '' chartDom ψ f q)) :=
      ψ.isOpen_image_symm_of_subset_target (isOpen_ball.inter hV)
        (inter_subset_right.trans (image_chartDom_subset_target hq0))
    have hmem : x₁ ∈ ψ.symm '' (ball (ψ x₁) s ∩ ψ '' chartDom ψ f q) :=
      ⟨ψ x₁, ⟨mem_ball_self hs, hz₁V⟩, ψ.left_inv hx₁src⟩
    have hns : ¬ (ψ.symm '' (ball (ψ x₁) s ∩ ψ '' chartDom ψ f q) ⊆ {x | f x = x}) :=
      fun hsub => hx₁O (mem_interior.2 ⟨_, hsub, hopen, hmem⟩)
    obtain ⟨_, ⟨z, ⟨hzb, hzV⟩, rfl⟩, hnf⟩ := not_subset.1 hns
    exact ⟨z, ⟨hzV, fun hgz => hnf ((chartConj_eq_iff hq0 hfq hzV).1 hgz)⟩, by
      rw [dist_comm]; exact hzb⟩
  generalize hNFdef : (ψ '' chartDom ψ f q) \ {z | chartConj ψ f z = z} = NF at hNFo hz₁NF
  have hNF : ∀ z, z ∈ NF ↔ z ∈ ψ '' chartDom ψ f q ∧ chartConj ψ f z ≠ z := by
    intro z; rw [← hNFdef]; rfl
  -- the point `b` of `closure NF ∩ B̄(a₀, η / 2)` nearest to `a₀`
  have hNc : IsCompact (closure NF ∩ closedBall a₀ (η / 2)) :=
    (isCompact_closedBall a₀ (η / 2)).inter_left isClosed_closure
  have hz₁N : ψ x₁ ∈ closure NF ∩ closedBall a₀ (η / 2) :=
    ⟨hz₁NF, mem_closedBall.2 (by rw [dist_comm]; linarith)⟩
  obtain ⟨b, hbN, hbmin⟩ := hNc.exists_isMinOn ⟨_, hz₁N⟩
    (f := fun z => dist z a₀) (continuous_id.dist continuous_const).continuousOn
  have hrz : dist b a₀ ≤ dist (ψ x₁) a₀ := hbmin hz₁N
  have hrt : t₀ ≤ dist b a₀ := by
    by_contra hlt'
    have hlt := not_le.1 hlt'
    have hdisj : Disjoint (ball a₀ t₀) NF :=
      disjoint_left.2 fun z hz hzNF => ((hNF z).1 hzNF).2 (hfixO z hz).2
    exact disjoint_left.1 (hdisj.closure_right isOpen_ball) (mem_ball.2 hlt) hbN.1
  generalize hrdef : dist b a₀ = r at hrz hrt
  have hr : 0 < r := ht₀.trans_le hrt
  have hballNF : Disjoint (ball a₀ r) NF := by
    refine disjoint_left.2 fun z hz hzNF => ?_
    have hza := mem_ball.1 hz
    have hzN : z ∈ closure NF ∩ closedBall a₀ (η / 2) :=
      ⟨subset_closure hzNF, mem_closedBall.2 (by rw [dist_comm] at ha₀; linarith)⟩
    have h1 : dist b a₀ ≤ dist z a₀ := hbmin hzN
    linarith
  have hcballNF : Disjoint (closedBall a₀ r) NF := by
    rw [← closure_ball a₀ hr.ne']
    exact (hballNF.symm.closure_right hNFo).symm
  have hcballV : closedBall a₀ r ⊆ ψ '' chartDom ψ f q := fun z hz => hηV (mem_ball.2 (by
    have h1 := mem_closedBall.1 hz
    have h2 := dist_triangle z a₀ (ψ x₁)
    have h3 := dist_comm (ψ x₁) a₀
    linarith))
  have hfixball : ∀ z ∈ closedBall a₀ r, chartConj ψ f z = z := fun z hz => by
    by_contra h
    exact disjoint_left.1 hcballNF hz ((hNF z).2 ⟨hcballV hz, h⟩)
  have hb : b ∈ sphere a₀ r := mem_sphere.2 hrdef
  have hacc : ∀ s > 0, ∃ z ∈ ψ '' chartDom ψ f q ∩ ball b s, chartConj ψ f z ≠ z := by
    intro s hs
    obtain ⟨z, hzNF, hzb⟩ := Metric.mem_closure_iff.1 hbN.1 s hs
    obtain ⟨hzV, hgz⟩ := (hNF z).1 hzNF
    exact ⟨z, ⟨hzV, mem_ball.2 (by rw [dist_comm]; exact hzb)⟩, hgz⟩
  exact false_of_fixed_ball_touching hT hq hV (mapsTo_chartConj hq0 hfq) hgc
    (fun z hz => chartConj_iterate_self hq0 hfq hz) hr hcballV hfixball hb hacc

end Main

/-! ### Newman's theorem for prime order -/

/-- **Newman's theorem for prime order**, from the transfer vanishing lemma (N7). -/
theorem newmanPrimeOrder_of_degreeEqZeroOfFree (hT : DegreeEqZeroOfFree) : NewmanPrimeOrder := by
  intro n M _ _ _ _ U hU hUne
  cases n with
  | zero =>
    have := subsingleton_of_chartedSpace_zero M
    exact ⟨1, one_pos, fun _ _ _ _ _ _ => Subsingleton.elim _ _⟩
  | succ m =>
    obtain ⟨ε, hε, hfix⟩ := exists_uniform_radius (m := m) hT hU hUne
    refine ⟨ε, hε, fun q hq f hfq hsmall => ?_⟩
    rcases isClopen_iff.1 ⟨isClosed_interior_fixedPoints (m := m) hT hq f hfq, isOpen_interior⟩
      with h | h
    · exact absurd h (hfix q hq f hfq hsmall).ne_empty
    · intro x
      have h1 : x ∈ interior {x | f x = x} := h ▸ mem_univ x
      have h2 : x ∈ {x | f x = x} := interior_subset h1
      exact h2

end HSFormal.Newman
