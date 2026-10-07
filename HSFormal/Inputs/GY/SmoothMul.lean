import HSFormal.Inputs.GY.LogDeriv
import Mathlib.Analysis.Calculus.FDeriv.Partial

/-!
# Smoothness of the multiplication in exponential coordinates (blueprint C3, §5 H2 steps 5–7)

For `S : LocalExpStructure G E` with `G` a topological group and `E` finite-dimensional, the map
`μ (X, Y) = S.mu X Y = log (exp X * exp Y)` is `C^∞` on a product of balls around `0`:

* `LocalExpStructure.contDiffMu : S.ContDiffMu` (the frozen target of C3 in `GY/Defs.lean`).

Proof (blueprint H2):
* Step 5 (`exists_hasFDerivAt_mu_zero`): `Γ Z = Gop Z⁻¹` (`Gam`) is `C^∞` near `0` and
  `L ↦ μ (Z, L)` has derivative `Γ Z` at `0`: it is a local right inverse of `K ↦ μ (-Z, Z + K)`,
  whose derivative at `0` is the invertible `Gop Z` (C2), so `HasFDerivAt.of_local_left_inverse`
  applies.
* Step 6: `μ (X, Y') = μ (μ (X, Y), μ (-Y, Y'))` gives `∂₂ μ (X, Y) = Γ (μ (X, Y)) ∘ Gop Y`
  (`d2mu X Y`), and `μ (X', Y) = -μ (-Y, -X')` gives `∂₁ μ (X, Y) = d2mu (-Y) (-X)`. Both partials
  are continuous, so `hasStrictFDerivAt_uncurry_coprod` gives the Fréchet derivative
  `D p = (d2mu (-p.2) (-p.1)).coprod (d2mu p.1 p.2)`.
* Step 7: `D` is a `C^∞` expression in `p` and `μ`, so `μ ∈ C^n ⇒ fderiv μ = D ∈ C^n ⇒ μ ∈ C^{n+1}`
  (`contDiffOn_succ_iff_fderiv_of_isOpen`); conclude with `contDiffOn_infty`.

Deviation from the blueprint: the first partial derivative is written `d2mu (-Y) (-X)` (no rewriting
of `μ (-Y, -X)` as `-μ (X, Y)` inside `Γ`), which avoids a second identity in the bootstrap.
-/

noncomputable section

namespace HSFormal.GY

open Filter Topology Metric
open scoped ContDiff

namespace LocalExpStructure

variable {G : Type*} [Group G] [TopologicalSpace G]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (S : LocalExpStructure G E)

/-! ### Algebraic identities for `μ` -/

/-- `exp X * exp Y = exp (μ (X, Y))` and `exp (-Y) * exp Y' = exp (μ (-Y, Y'))` give
`μ (μ (X, Y), μ (-Y, Y')) = μ (X, Y')`. -/
theorem mu_mu_neg {X Y Y' : E} (h₁ : S.exp X * S.exp Y ∈ S.chart.target)
    (h₂ : S.exp (-Y) * S.exp Y' ∈ S.chart.target) :
    S.mu (S.mu X Y) (S.mu (-Y) Y') = S.mu X Y' := by
  rw [S.mu_def (S.mu X Y), S.exp_mu h₁, S.exp_mu h₂, S.mu_def X Y', exp_neg]
  congr 1
  group

/-- `μ (X, Y) = -μ (-Y, -X)` when `exp (-Y) * exp (-X)` is in the chart target and
`-μ (-Y, -X)` in the chart source. -/
theorem mu_eq_neg_mu_neg {X Y : E} (h₁ : S.exp (-Y) * S.exp (-X) ∈ S.chart.target)
    (h₂ : -S.mu (-Y) (-X) ∈ S.chart.source) : S.mu X Y = -S.mu (-Y) (-X) := by
  have h : S.exp (-S.mu (-Y) (-X)) = S.exp X * S.exp Y := by
    rw [exp_neg, S.exp_mu h₁, exp_neg, exp_neg]
    group
  rw [S.mu_def X Y, ← h, S.symm_exp h₂]

theorem continuousAt_mu [IsTopologicalGroup G] {p : E × E}
    (hp : S.exp p.1 * S.exp p.2 ∈ S.chart.target) :
    ContinuousAt (fun q : E × E => S.mu q.1 q.2) p := by
  have hc : Continuous fun q : E × E => S.exp q.1 * S.exp q.2 :=
    (S.continuous_exp.comp continuous_fst).mul (S.continuous_exp.comp continuous_snd)
  show ContinuousAt (fun q : E × E => S.chart.symm (S.exp q.1 * S.exp q.2)) p
  exact ContinuousAt.comp (f := fun q : E × E => S.exp q.1 * S.exp q.2)
    (S.chart.continuousAt_symm hp) hc.continuousAt

/-! ### Step 5: the derivative of `L ↦ μ (Z, L)` at `0` -/

variable [IsTopologicalGroup G] [FiniteDimensional ℝ E]

local instance completeSpaceOfFD'' : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- `Γ Z = (Gop Z)⁻¹` (`Ring.inverse`; it is a genuine inverse for small `Z`). -/
def Gam (Z : E) : E →L[ℝ] E := Ring.inverse (S.Gop Z)

/-- The second partial derivative `∂₂ μ (X, Y) = Γ (μ (X, Y)) ∘ Gop Y`. -/
def d2mu (X Y : E) : E →L[ℝ] E := (S.Gam (S.mu X Y)).comp (S.Gop Y)

theorem exists_isUnit_Gop : ∃ r > 0, ∀ Z : E, ‖Z‖ < r → IsUnit (S.Gop Z) := by
  have h : S.Gop ⁻¹' {x | IsUnit x} ∈ 𝓝 (0 : E) := by
    refine S.continuous_Gop.continuousAt.preimage_mem_nhds ?_
    rw [S.Gop_zero]
    exact Units.isOpen.mem_nhds isUnit_one
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 h
  exact ⟨r, hr, fun Z hZ => hball (mem_ball_zero_iff.2 hZ)⟩

theorem contDiffAt_Gam {Z : E} (hZ : IsUnit (S.Gop Z)) : ContDiffAt ℝ ∞ S.Gam Z := by
  have h := contDiffAt_ringInverse (𝕜 := ℝ) (n := ∞) hZ.unit
  rw [hZ.unit_spec] at h
  exact h.comp Z S.contDiff_Gop.contDiffAt

/-- **Step 5.** There is `ρ₅ > 0` with `ball 0 ρ₅ ⊆ source`, `Γ` smooth on `ball 0 ρ₅`, and
`HasFDerivAt (μ Z) (Γ Z) 0` for `‖Z‖ < ρ₅`. -/
theorem exists_hasFDerivAt_mu_zero : ∃ ρ₅ > 0, ball (0 : E) ρ₅ ⊆ S.chart.source ∧
    ContDiffOn ℝ ∞ S.Gam (ball 0 ρ₅) ∧
    ∀ Z : E, ‖Z‖ < ρ₅ → HasFDerivAt (S.mu Z) (S.Gam Z) 0 := by
  obtain ⟨δ, hδ, K₁, hK₁⟩ := S.c11
  obtain ⟨ρ₂, hρ₂, hG⟩ := S.hasFDerivAt_mu_neg_add
  obtain ⟨ru, hru, hunit⟩ := S.exists_isUnit_Gop
  obtain ⟨rs, hrs, hsrc⟩ := Metric.mem_nhds_iff.1 S.source_mem_nhds
  set r := min (min ρ₂ ru) (min δ rs) with hr_def
  have hr : 0 < r := lt_min (lt_min hρ₂ hru) (lt_min hδ hrs)
  have hrρ₂ : r ≤ ρ₂ := (min_le_left _ _).trans (min_le_left _ _)
  have hrru : r ≤ ru := (min_le_left _ _).trans (min_le_right _ _)
  have hrδ : r ≤ δ := (min_le_right _ _).trans (min_le_left _ _)
  have hrrs : r ≤ rs := (min_le_right _ _).trans (min_le_right _ _)
  have hsub : ball (0 : E) r ⊆ S.chart.source := (ball_subset_ball hrrs).trans hsrc
  refine ⟨r, hr, hsub, fun Z hZ => (S.contDiffAt_Gam (hunit Z ?_)).contDiffWithinAt, fun Z hZ => ?_⟩
  · exact lt_of_lt_of_le (mem_ball_zero_iff.1 hZ) hrru
  have hZsrc : Z ∈ S.chart.source := hsub (mem_ball_zero_iff.2 hZ)
  set u := (hunit Z (hZ.trans_le hrru)).unit with hu
  have hu' : (u : E →L[ℝ] E) = S.Gop Z := (hunit Z (hZ.trans_le hrru)).unit_spec
  set f' : E ≃L[ℝ] E := ContinuousLinearEquiv.unitsEquiv ℝ E u
  have hf' : (f' : E →L[ℝ] E) = S.Gop Z := by rw [← hu']; ext x; rfl
  have hf'symm : (f'.symm : E →L[ℝ] E) = S.Gam Z := by
    rw [Gam, ← hu', Ring.inverse_unit]; ext x; rfl
  set g : E → E := fun L => S.mu Z L - Z with hg_def
  have hg0 : g 0 = 0 := by simp [hg_def, mu_def, S.symm_exp hZsrc]
  have hgc : ContinuousAt g 0 := by
    have hmem : S.exp Z * S.exp 0 ∈ S.chart.target := by
      simpa using S.exp_mem_target hZsrc
    have h1 : ContinuousAt (fun L : E => S.mu Z L) 0 :=
      (S.continuousAt_mu (p := (Z, 0)) hmem).comp (continuousAt_const.prodMk continuousAt_id)
    exact h1.sub continuousAt_const
  have hf : HasFDerivAt (fun K => S.mu (-Z) (Z + K)) (f' : E →L[ℝ] E) (g 0) := by
    rw [hg0, hf']; exact hG Z (hZ.trans_le hrρ₂)
  have hfg : ∀ᶠ L in 𝓝 (0 : E), (fun K => S.mu (-Z) (Z + K)) (g L) = L := by
    filter_upwards [ball_mem_nhds (0 : E) (lt_min hδ hrs)] with L hL
    rw [mem_ball_zero_iff] at hL
    have hLδ : ‖L‖ < δ := hL.trans_le (min_le_left _ _)
    have hLsrc : L ∈ S.chart.source := hsrc (mem_ball_zero_iff.2 (hL.trans_le (min_le_right _ _)))
    have hmem := (hK₁ Z L (hZ.trans_le hrδ) hLδ).1
    simp only [hg_def, add_sub_cancel]
    rw [mu_def, S.exp_mu hmem, exp_neg, inv_mul_cancel_left, S.symm_exp hLsrc]
  have hg := HasFDerivAt.of_local_left_inverse hgc hf hfg
  rw [hf'symm] at hg
  have := hg.add_const Z
  simpa [hg_def] using this

/-! ### Steps 6–7: partial derivatives and the bootstrap -/

/-- The Fréchet derivative of `μ`: `D p = (d2mu (-p.2) (-p.1)).coprod (d2mu p.1 p.2)`. -/
def Dmu (p : E × E) : E × E →L[ℝ] E := (S.d2mu (-p.2) (-p.1)).coprod (S.d2mu p.1 p.2)

omit [IsTopologicalGroup G] [FiniteDimensional ℝ E] in
/-- `A.coprod B = A ∘ fst + B ∘ snd`. -/
theorem coprod_eq_comp_add (A B : E →L[ℝ] E) :
    A.coprod B =
      A.comp (ContinuousLinearMap.fst ℝ E E) + B.comp (ContinuousLinearMap.snd ℝ E E) := by
  ext <;> simp

/-- **C3.** The multiplication `μ (X, Y) = log (exp X * exp Y)` is `C^∞` near `(0, 0)`. -/
theorem contDiffMu : S.ContDiffMu := by
  obtain ⟨δ, hδ, K₁, hK₁⟩ := S.c11
  obtain ⟨ρ₂, hρ₂, hG⟩ := S.hasFDerivAt_mu_neg_add
  obtain ⟨ρ₅, hρ₅, hsrc, hΓsmooth, hΓ⟩ := S.exists_hasFDerivAt_mu_zero
  set c : ℝ := 2 + |K₁| with hc_def
  have hc : 0 < c := by positivity
  set ρ := min (min δ ρ₂) (min 1 (ρ₅ / c)) with hρ_def
  have hρ : 0 < ρ := lt_min (lt_min hδ hρ₂) (lt_min one_pos (div_pos hρ₅ hc))
  have hρδ : ρ ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
  have hρρ₂ : ρ ≤ ρ₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hρ1 : ρ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hρc : ρ * c ≤ ρ₅ := by
    have : ρ ≤ ρ₅ / c := (min_le_right _ _).trans (min_le_right _ _)
    rwa [le_div_iff₀ hc] at this
  set Ω : Set (E × E) := ball (0 : E) ρ ×ˢ ball (0 : E) ρ with hΩ_def
  have hΩ : IsOpen Ω := isOpen_ball.prod isOpen_ball
  have hΩswap : ∀ p ∈ Ω, ((-p.2, -p.1) : E × E) ∈ Ω := by
    rintro ⟨X, Y⟩ ⟨hX, hY⟩
    exact ⟨by simpa using hY, by simpa using hX⟩
  -- (F1) the products stay in the chart target.
  have F1 : ∀ X Y : E, ‖X‖ < ρ → ‖Y‖ < ρ → S.exp X * S.exp Y ∈ S.chart.target :=
    fun X Y hX hY => (hK₁ X Y (hX.trans_le hρδ) (hY.trans_le hρδ)).1
  -- (F2) `μ` maps `Ω` into `ball 0 ρ₅`.
  have F2 : ∀ X Y : E, ‖X‖ < ρ → ‖Y‖ < ρ → ‖S.mu X Y‖ < ρ₅ := by
    intro X Y hX hY
    have h : ‖S.mu X Y - (X + Y)‖ ≤ K₁ * ‖X‖ * ‖Y‖ :=
      (hK₁ X Y (hX.trans_le hρδ) (hY.trans_le hρδ)).2
    have h1 : ‖S.mu X Y‖ ≤ ‖X‖ + ‖Y‖ + K₁ * ‖X‖ * ‖Y‖ := by
      have := norm_add_le (S.mu X Y - (X + Y)) (X + Y)
      rw [sub_add_cancel] at this
      linarith [norm_add_le X Y]
    have h2 : K₁ * ‖X‖ * ‖Y‖ ≤ |K₁| * ρ := by
      have hXY : ‖X‖ * ‖Y‖ ≤ ρ * 1 :=
        mul_le_mul hX.le (hY.le.trans hρ1) (norm_nonneg _) hρ.le
      calc K₁ * ‖X‖ * ‖Y‖ ≤ |K₁| * (‖X‖ * ‖Y‖) := by
            rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self K₁) (by positivity)
        _ ≤ |K₁| * ρ := by rw [mul_one] at hXY; exact mul_le_mul_of_nonneg_left hXY (abs_nonneg _)
    calc ‖S.mu X Y‖ < ρ + ρ + |K₁| * ρ := by linarith
      _ = ρ * c := by rw [hc_def]; ring
      _ ≤ ρ₅ := hρc
  -- (F3) the second partial derivative.
  have F3 : ∀ X Y : E, ‖X‖ < ρ → ‖Y‖ < ρ → HasFDerivAt (S.mu X) (S.d2mu X Y) Y := by
    intro X Y hX hY
    have hshift : HasFDerivAt (S.mu (-Y)) (S.Gop Y) Y := by
      have := (hasFDerivAt_comp_add_left Y).1 (hG Y (hY.trans_le hρρ₂))
      rwa [add_zero] at this
    have hZ : HasFDerivAt (S.mu (S.mu X Y)) (S.Gam (S.mu X Y)) (S.mu (-Y) Y) := by
      rw [S.mu_neg_self]; exact hΓ _ (F2 X Y hX hY)
    have hcomp := hZ.comp Y hshift
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 (hY.trans_le hρδ))] with Y' hY'
    rw [mem_ball_zero_iff] at hY'
    exact (S.mu_mu_neg (F1 X Y hX hY)
      (hK₁ (-Y) Y' (by simpa using hY.trans_le hρδ) hY').1).symm
  -- (F4) the first partial derivative.
  have F4 : ∀ X Y : E, ‖X‖ < ρ → ‖Y‖ < ρ →
      HasFDerivAt (fun X' => S.mu X' Y) (S.d2mu (-Y) (-X)) X := by
    intro X Y hX hY
    have hneg : HasFDerivAt (fun X' : E => -X') (-ContinuousLinearMap.id ℝ E) X :=
      (hasFDerivAt_id X).fun_neg
    have h1 : HasFDerivAt (fun X' => S.mu (-Y) (-X'))
        ((S.d2mu (-Y) (-X)).comp (-ContinuousLinearMap.id ℝ E)) X :=
      (F3 (-Y) (-X) (by simpa using hY) (by simpa using hX)).comp X hneg
    have h2 : HasFDerivAt (fun X' => -S.mu (-Y) (-X'))
        (-((S.d2mu (-Y) (-X)).comp (-ContinuousLinearMap.id ℝ E))) X := h1.fun_neg
    have h' : HasFDerivAt (fun X' => -S.mu (-Y) (-X')) (S.d2mu (-Y) (-X)) X := by
      refine h2.congr_fderiv ?_
      ext v; simp
    refine h'.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hX)] with X' hX'
    rw [mem_ball_zero_iff] at hX'
    refine S.mu_eq_neg_mu_neg (F1 (-Y) (-X') (by simpa using hY) (by simpa using hX')) ?_
    exact hsrc (mem_ball_zero_iff.2 (by
      rw [norm_neg]; exact F2 (-Y) (-X') (by simpa using hY) (by simpa using hX')))
  -- (F5) continuity of `μ` on `Ω`.
  have F5 : ContinuousOn (fun p : E × E => S.mu p.1 p.2) Ω := fun p hp =>
    (S.continuousAt_mu
      (F1 p.1 p.2 (mem_ball_zero_iff.1 hp.1) (mem_ball_zero_iff.1 hp.2))).continuousWithinAt
  have hmaps : Set.MapsTo (fun p : E × E => S.mu p.1 p.2) Ω (ball 0 ρ₅) := fun p hp =>
    mem_ball_zero_iff.2 (F2 p.1 p.2 (mem_ball_zero_iff.1 hp.1) (mem_ball_zero_iff.1 hp.2))
  -- (F6) continuity of the partial derivative on `Ω`.
  have F6 : ContinuousOn (fun p : E × E => S.d2mu p.1 p.2) Ω := by
    have h1 : ContinuousOn (fun p : E × E => S.Gam (S.mu p.1 p.2)) Ω :=
      hΓsmooth.continuousOn.comp F5 hmaps
    have h2 : ContinuousOn (fun p : E × E => S.Gop p.2) Ω :=
      (S.continuous_Gop.comp continuous_snd).continuousOn
    exact h1.clm_comp h2
  have F6' : ∀ p ∈ Ω, ContinuousAt (fun p : E × E => S.d2mu p.1 p.2) p :=
    fun p hp => F6.continuousAt (hΩ.mem_nhds hp)
  -- (F7) the Fréchet derivative.
  have F7 : ∀ p ∈ Ω, HasFDerivAt (fun q : E × E => S.mu q.1 q.2) (S.Dmu p) p := by
    intro p hp
    have hev : ∀ᶠ v in 𝓝 p, v ∈ Ω := hΩ.mem_nhds hp
    have hc1 : ContinuousAt (fun v : E × E => S.d2mu (-v.2) (-v.1)) p := by
      have h := ContinuousAt.comp (g := fun q : E × E => S.d2mu q.1 q.2)
        (f := fun v : E × E => ((-v.2, -v.1) : E × E)) (x := p) (F6' _ (hΩswap p hp))
        (by fun_prop)
      exact h
    have h := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := p) (f := S.mu)
      (f₁ := fun X Y => S.d2mu (-Y) (-X)) (f₂ := S.d2mu)
      (hev.mono fun v hv => F4 v.1 v.2 (mem_ball_zero_iff.1 hv.1) (mem_ball_zero_iff.1 hv.2))
      (hev.mono fun v hv => F3 v.1 v.2 (mem_ball_zero_iff.1 hv.1) (mem_ball_zero_iff.1 hv.2))
      hc1 (F6' p hp)
    exact h.hasFDerivAt
  -- (F8) the bootstrap.
  have hfd : ∀ p ∈ Ω, fderiv ℝ (fun q : E × E => S.mu q.1 q.2) p = S.Dmu p :=
    fun p hp => (F7 p hp).fderiv
  have hdiff : DifferentiableOn ℝ (fun q : E × E => S.mu q.1 q.2) Ω :=
    fun p hp => (F7 p hp).differentiableAt.differentiableWithinAt
  have hboot : ∀ n : ℕ, ContDiffOn ℝ n (fun q : E × E => S.mu q.1 q.2) Ω := by
    intro n
    induction n with
    | zero => exact contDiffOn_zero.2 F5
    | succ n ih =>
      have hn : ((n : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
      have hd2 : ContDiffOn ℝ n (fun p : E × E => S.d2mu p.1 p.2) Ω := by
        have h1 : ContDiffOn ℝ n (fun p : E × E => S.Gam (S.mu p.1 p.2)) Ω :=
          have h := (hΓsmooth.of_le hn).comp ih hmaps
          h
        have h2 : ContDiffOn ℝ n (fun p : E × E => S.Gop p.2) Ω :=
          ((S.contDiff_Gop.comp contDiff_snd).of_le hn).contDiffOn
        have h := h1.clm_comp h2
        exact h
      have hswap : ContDiffOn ℝ n (fun p : E × E => S.d2mu (-p.2) (-p.1)) Ω := by
        have hl : ContDiff ℝ n fun p : E × E => ((-p.2, -p.1) : E × E) :=
          contDiff_snd.neg.prodMk contDiff_fst.neg
        have h := hd2.comp hl.contDiffOn hΩswap
        exact h
      have hD : ContDiffOn ℝ n S.Dmu Ω := by
        have : S.Dmu = fun p : E × E =>
            (S.d2mu (-p.2) (-p.1)).comp (ContinuousLinearMap.fst ℝ E E) +
              (S.d2mu p.1 p.2).comp (ContinuousLinearMap.snd ℝ E E) :=
          funext fun p => coprod_eq_comp_add _ _
        rw [this]
        exact (hswap.clm_comp contDiffOn_const).add (hd2.clm_comp contDiffOn_const)
      rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
      refine ⟨hdiff, fun h => absurd h (WithTop.natCast_ne_top n), ?_⟩
      exact hD.congr hfd
  exact ⟨ρ, hρ, contDiffOn_infty.2 hboot, F1⟩

/-- Blueprint name of `contDiffMu` (C3 `LocalExpStructure.contDiffOn_mu`). -/
theorem contDiffOn_mu : S.ContDiffMu := S.contDiffMu

end LocalExpStructure

end HSFormal.GY
