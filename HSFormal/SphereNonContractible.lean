import HSFormal.SpherePinch
import HSFormal.Brouwer.FixedPoint

/-!
# Non-contractibility of spheres: discharging `SphereSelfMapSurjective`

This module proves `HSFormal.sphereSelfMapSurjective : HSFormal.SphereSelfMapSurjective`, the
classical fact that a continuous self-map of `Sⁿ = OnePoint ℝⁿ` homotopic to the identity is
surjective, from **Brouwer's fixed-point theorem** (`HSFormal.Brouwer.brouwer_fixed_point`, ported
in `HSFormal/Brouwer/` from harfe's MIT-licensed https://github.com/harfe/fixed-point-theorems-lean4,
commit `770940d`; it proves Brouwer for nonempty compact convex sets via a cubical Sperner lemma,
following Kuhn 1960; license text in `HSFormal/Brouwer/LICENSE`).

The argument is the textbook one, carried out on the round unit sphere `𝕊 ⊆ E` of a
finite-dimensional real normed space `E` (we take `E = ℝⁿ⁺¹` and transport along the stereographic
homeomorphism `HSFormal.roundSphere n : OnePoint ℝⁿ ≃ₜ 𝕊`); it is uniform in `n`, including `n = 0`.

* `HSFormal.no_retraction_closedBall_sphere`: there is no retraction of the closed unit ball onto
  the unit sphere (otherwise `y ↦ -r y` would be a fixed-point-free self-map of the ball).
* `HSFormal.false_of_homotopy_id_const_sphere`: the identity of `𝕊` is not homotopic to a
  constant map. A homotopy `F` from `id` to the constant map `q` factors through the quotient map
  `(t, x) ↦ (1 - t) • x` from `I × 𝕊` onto the closed ball, giving a retraction.
* `HSFormal.homotopic_const_of_not_mem_range`: a self-map of `𝕊` missing a point `p` is homotopic
  to the constant map `-p`, via `(t, x) ↦ normalize ((1 - t) • f x - t • p)`.
-/

noncomputable section

open Set Metric
open scoped unitInterval

namespace HSFormal

section RoundSphere

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **No-retraction theorem**: the unit sphere of a finite-dimensional real normed space is not a
retract of the closed unit ball. -/
theorem no_retraction_closedBall_sphere [FiniteDimensional ℝ E]
    (r : C(closedBall (0 : E) 1, sphere (0 : E) 1))
    (hr : ∀ (x : E) (hx : x ∈ sphere (0 : E) 1), (r ⟨x, sphere_subset_closedBall hx⟩ : E) = x) :
    False := by
  let f : C(closedBall (0 : E) 1, closedBall (0 : E) 1) :=
    { toFun := fun y => ⟨-(r y : E), by
        rw [mem_closedBall_zero_iff, norm_neg, ← mem_closedBall_zero_iff]
        exact sphere_subset_closedBall (r y).2⟩
      continuous_toFun := by fun_prop }
  obtain ⟨y, hy⟩ := Brouwer.brouwer_fixed_point (closedBall (0 : E) 1) (convex_closedBall 0 1)
    (isCompact_closedBall 0 1) ⟨0, mem_closedBall_self zero_le_one⟩ f
  have hy' : -(r y : E) = y := congrArg Subtype.val hy
  have hys : (y : E) ∈ sphere (0 : E) 1 := by
    rw [mem_sphere_zero_iff_norm, ← hy', norm_neg, ← mem_sphere_zero_iff_norm]
    exact (r y).2
  have hry : (r y : E) = y := by
    have := hr y hys
    simpa using this
  rw [hry] at hy'
  have h0 : (y : E) = 0 := by
    have : (2 : ℝ) • (y : E) = 0 := by rw [two_smul]; nth_rewrite 1 [← hy']; exact neg_add_cancel _
    exact (smul_eq_zero.mp this).resolve_left two_ne_zero
  rw [mem_sphere_zero_iff_norm, h0, norm_zero] at hys
  exact zero_ne_one hys

/-- The identity of the unit sphere of a finite-dimensional real normed space is not homotopic to a
constant map. -/
theorem false_of_homotopy_id_const_sphere [FiniteDimensional ℝ E] (q : sphere (0 : E) 1)
    (F : ContinuousMap.Homotopy (ContinuousMap.id (sphere (0 : E) 1))
      (ContinuousMap.const (sphere (0 : E) 1) q)) : False := by
  classical
  -- the quotient map `(t, x) ↦ (1 - t) • x` from `I × 𝕊` onto the closed unit ball
  let Φ : I × sphere (0 : E) 1 → closedBall (0 : E) 1 := fun p =>
    ⟨(1 - (p.1 : ℝ)) • (p.2 : E), by
      rw [mem_closedBall_zero_iff, norm_smul, norm_eq_of_mem_sphere p.2, mul_one,
        Real.norm_of_nonneg (sub_nonneg.mpr p.1.2.2)]
      linarith [p.1.2.1]⟩
  have hΦc : Continuous Φ := by fun_prop
  have hΦs : Function.Surjective Φ := by
    rintro ⟨y, hy⟩
    by_cases h0 : y = 0
    · refine ⟨(1, q), ?_⟩
      ext1
      simp [Φ, h0]
    · have hn : 0 < ‖y‖ := norm_pos_iff.mpr h0
      have hle : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.mp hy
      refine ⟨(⟨1 - ‖y‖, by constructor <;> linarith⟩,
        ⟨‖y‖⁻¹ • y, by
          rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']⟩),
        ?_⟩
      ext1
      simp only [Φ, sub_sub_cancel, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  have hΦq : Topology.IsQuotientMap Φ :=
    IsClosedMap.isQuotientMap (hΦc.isClosedMap) hΦc hΦs
  -- the induced retraction
  let r : closedBall (0 : E) 1 → sphere (0 : E) 1 := fun y =>
    if h : (y : E) = 0 then q else
      F (⟨1 - ‖(y : E)‖, by
          have := mem_closedBall_zero_iff.mp y.2
          constructor <;> linarith [norm_nonneg (y : E)]⟩,
        ⟨‖(y : E)‖⁻¹ • (y : E), by
          rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
            inv_mul_cancel₀ (norm_pos_iff.mpr h).ne']⟩)
  have hrΦ : r ∘ Φ = F := by
    funext ⟨t, x⟩
    have hx : ‖(x : E)‖ = 1 := norm_eq_of_mem_sphere x
    by_cases ht : (t : ℝ) = 1
    · have ht' : t = 1 := Subtype.ext ht
      subst ht'
      have h0 : (Φ (1, x) : E) = 0 := by simp [Φ]
      simp only [Function.comp_apply, r, dite_eq_left h0]
      exact (F.apply_one x).symm
    · have hpos : 0 < 1 - (t : ℝ) := sub_pos.mpr (lt_of_le_of_ne t.2.2 ht)
      have hnorm : ‖(Φ (t, x) : E)‖ = 1 - (t : ℝ) := by
        simp only [Φ]
        rw [norm_smul, hx, mul_one, Real.norm_of_nonneg hpos.le]
      have h0 : (Φ (t, x) : E) ≠ 0 := by
        rw [← norm_pos_iff, hnorm]; exact hpos
      simp only [Function.comp_apply, r, dite_eq_right h0]
      congr 1
      ext1
      · simp [hnorm]
      · ext1
        simp only [hnorm]
        simp only [Φ, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
  have hrc : Continuous r := by
    rw [hΦq.continuous_iff, hrΦ]
    exact F.continuous
  refine no_retraction_closedBall_sphere ⟨r, hrc⟩ fun x hx => ?_
  have hx1 : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
  have h0 : x ≠ 0 := by rintro rfl; simp at hx1
  change ((r ⟨x, _⟩ : sphere (0 : E) 1) : E) = x
  simp only [r, dite_eq_right h0, hx1, sub_self, inv_one, one_smul]
  have : F ((0 : I), (⟨x, hx⟩ : sphere (0 : E) 1)) = ⟨x, hx⟩ := F.apply_zero _
  exact congrArg Subtype.val this

/-- A continuous self-map of the unit sphere missing the point `p` is homotopic to the constant map
at the antipode `-p`. -/
theorem homotopic_const_of_not_mem_range (f : C(sphere (0 : E) 1, sphere (0 : E) 1))
    (p : sphere (0 : E) 1) (hp : p ∉ range f) :
    f.Homotopic (ContinuousMap.const _ (-p)) := by
  have hne : ∀ (t : I) (x : sphere (0 : E) 1),
      (1 - (t : ℝ)) • (f x : E) - (t : ℝ) • (p : E) ≠ 0 := by
    intro t x h
    have hfx : ‖(f x : E)‖ = 1 := norm_eq_of_mem_sphere (f x)
    have hp1 : ‖(p : E)‖ = 1 := norm_eq_of_mem_sphere p
    have h1 : (1 - (t : ℝ)) • (f x : E) = (t : ℝ) • (p : E) := sub_eq_zero.mp h
    have h2 : 1 - (t : ℝ) = t := by
      have := congrArg norm h1
      rwa [norm_smul, norm_smul, hfx, hp1, mul_one, mul_one,
        Real.norm_of_nonneg (sub_nonneg.mpr t.2.2), Real.norm_of_nonneg t.2.1] at this
    have ht0 : (t : ℝ) ≠ 0 := by intro h0; rw [h0] at h2; norm_num at h2
    rw [h2] at h1
    exact hp ⟨x, Subtype.ext (smul_right_injective E ht0 h1)⟩
  refine ⟨{
    toFun := fun z => ⟨‖(1 - (z.1 : ℝ)) • (f z.2 : E) - (z.1 : ℝ) • (p : E)‖⁻¹ •
        ((1 - (z.1 : ℝ)) • (f z.2 : E) - (z.1 : ℝ) • (p : E)), by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hne z.1 z.2))]⟩
    continuous_toFun := by
      refine Continuous.subtype_mk ?_ _
      refine Continuous.smul ?_ (by fun_prop)
      exact Continuous.inv₀ (by fun_prop) fun z => norm_ne_zero_iff.mpr (hne z.1 z.2)
    map_zero_left := fun x => by
      ext1
      simp [norm_eq_of_mem_sphere (f x)]
    map_one_left := fun x => by
      ext1
      simp [norm_eq_of_mem_sphere p] }⟩

end RoundSphere

/-- **Non-contractibility of spheres**: a continuous self-map of `Sⁿ = OnePoint ℝⁿ` homotopic to the
identity is surjective. This discharges the explicit hypothesis `HSFormal.SphereSelfMapSurjective`
of Section 7 (via Brouwer's fixed-point theorem). -/
theorem sphereSelfMapSurjective : SphereSelfMapSurjective := by
  intro n g hg p
  by_contra hp
  set e := roundSphere n
  let eC : C(OnePoint (EuclideanSpace ℝ (Fin n)), sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    ⟨e, e.continuous⟩
  let eS : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, OnePoint (EuclideanSpace ℝ (Fin n))) :=
    ⟨e.symm, e.symm.continuous⟩
  let f : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
      sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := eC.comp (g.comp eS)
  have hf : f.Homotopic (ContinuousMap.id _) := by
    have h := (ContinuousMap.Homotopic.refl eC).comp (hg.comp (ContinuousMap.Homotopic.refl eS))
    convert h using 1
    ext1 x
    simp [eC, eS]
  have hmiss : e p ∉ range f := by
    rintro ⟨x, hx⟩
    refine hp ⟨e.symm x, ?_⟩
    have : e (g (e.symm x)) = e p := hx
    exact e.injective this
  have hconst := (hf.symm.trans (homotopic_const_of_not_mem_range f (e p) hmiss))
  exact false_of_homotopy_id_const_sphere _ hconst.some

end HSFormal
