import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Topology.Instances.Shrink
import Mathlib.Algebra.Group.Shrink
import Mathlib.Algebra.Group.Action.TransferInstance
import HSFormal.HilbertSmithNegK

/-!
# Universe-polymorphic forms of the main theorems

`HSFormal.HilbertSmith` and `HSFormal.PadicExclusion` quantify over a manifold and a group in
`Type`. A second-countable Hausdorff space is `Small.{0}` (`small_of_secondCountable`), so a
manifold `M : Type u` and a group `G : Type v` can be replaced by `Shrink.{0} M` and `Shrink.{0} G`
with the transported structures; a `C^∞` Lie group structure on `Shrink.{0} G` pulls back along the
homeomorphic group isomorphism `G ≃ₜ Shrink.{0} G` (`IsLieGroup'.of_equiv`).

* `HSFormal.Universe.hilbertSmith_univ`: the Hilbert–Smith theorem for `M : Type u`, `G : Type v`.
* `HSFormal.padicExclusion`: boundaryless p-adic exclusion, every hypothesis discharged.
* `HSFormal.Universe.padicExclusion_univ`: the same for `M : Type u`.
-/

open scoped Manifold ContDiff Topology

namespace HSFormal.Universe

universe u v w

/-- A second-countable T0 space is `Small.{w}` for every universe `w`. -/
theorem small_of_secondCountable (X : Type u) [TopologicalSpace X] [T0Space X]
    [SecondCountableTopology X] : Small.{w} X := by
  let b := TopologicalSpace.countableBasis X
  have hb : TopologicalSpace.IsTopologicalBasis b := TopologicalSpace.isBasis_countableBasis X
  have : Countable b := (TopologicalSpace.countable_countableBasis X).to_subtype
  let f : X → Set b := fun x => {s | x ∈ (s : Set X)}
  refine small_of_injective (f := f) ?_
  intro x y hxy
  apply Inseparable.eq
  rw [inseparable_iff_forall_isOpen]
  intro s hs
  have key : ∀ {x y : X}, f x = f y → x ∈ s → y ∈ s := by
    intro x y hxy hx
    obtain ⟨t, htb, hxt, hts⟩ := hb.exists_subset_of_mem_open hx hs
    have : (⟨t, htb⟩ : b) ∈ f y := hxy ▸ hxt
    exact hts this
  exact ⟨key hxy, key hxy.symm⟩

section Pullback

variable {H : Type*} [TopologicalSpace H] {X : Type*} {Y : Type*} [TopologicalSpace X]
  [TopologicalSpace Y]

/-- Pull back a charted space structure along a homeomorphism, chart by chart. -/
@[reducible] def pullbackChartedSpace [ChartedSpace H Y] (e : X ≃ₜ Y) : ChartedSpace H X where
  atlas := (fun c => e.toOpenPartialHomeomorph ≫ₕ c) '' atlas H Y
  chartAt x := e.toOpenPartialHomeomorph ≫ₕ chartAt H (e x)
  mem_chart_source x := by simp [mem_chart_source]
  chart_mem_atlas x := ⟨_, chart_mem_atlas H (e x), rfl⟩

theorem pullback_transition (e : X ≃ₜ Y) (c c' : OpenPartialHomeomorph Y H) :
    (e.toOpenPartialHomeomorph ≫ₕ c).symm ≫ₕ (e.toOpenPartialHomeomorph ≫ₕ c') =
      c.symm ≫ₕ c' := by
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc,
    ← OpenPartialHomeomorph.trans_assoc e.toOpenPartialHomeomorph.symm,
    ← Homeomorph.symm_toOpenPartialHomeomorph, ← Homeomorph.trans_toOpenPartialHomeomorph,
    Homeomorph.symm_trans_self, Homeomorph.refl_toOpenPartialHomeomorph,
    OpenPartialHomeomorph.refl_trans]

theorem pullback_hasGroupoid [ChartedSpace H Y] (e : X ≃ₜ Y) (G : StructureGroupoid H)
    [HasGroupoid Y G] : @HasGroupoid H _ X _ (pullbackChartedSpace e) G := by
  let := pullbackChartedSpace (H := H) e
  exact ⟨by
    rintro _ _ ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
    rw [pullback_transition]
    exact HasGroupoid.compatible hc hc'⟩

end Pullback

/-- The `C^∞` Lie group conclusion of `HSFormal.IsLieGroup`, for a group in any universe. -/
def IsLieGroup' (G : Type u) [Group G] [TopologicalSpace G] : Prop :=
  ∃ (d : ℕ) (_ : ChartedSpace (EuclideanSpace ℝ (Fin d)) G),
    LieGroup 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ G

/-- `IsLieGroup'` transfers along a homeomorphic group isomorphism. -/
theorem IsLieGroup'.of_equiv {G : Type u} {G' : Type v} [Group G] [TopologicalSpace G]
    [Group G'] [TopologicalSpace G'] (e : G ≃ₜ G') (he : ∀ x y, e (x * y) = e x * e y)
    (h : IsLieGroup' G') : IsLieGroup' G := by
  obtain ⟨d, cs, hlie⟩ := h
  set E := EuclideanSpace ℝ (Fin d)
  let : ChartedSpace E G := pullbackChartedSpace e
  have : HasGroupoid G (contDiffGroupoid ∞ 𝓘(ℝ, E)) := pullback_hasGroupoid e _
  have : IsManifold 𝓘(ℝ, E) ∞ G := IsManifold.mk' _ _ _
  -- `e` and `e.symm` are smooth: in the pulled-back charts they are the identity.
  have hc : ∀ x : G, chartAt E x = e.toOpenPartialHomeomorph ≫ₕ chartAt E (e x) := fun _ => rfl
  have hE : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e := by
    intro x
    have h1 : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (chartAt E (e x)).symm (chartAt E (e x)).target :=
      contMDiffOn_chart_symm
    have h2 : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (chartAt E x) (chartAt E x).source :=
      contMDiffOn_chart
    have h3 := h1.comp h2 (fun y hy => by
      rw [hc] at hy ⊢
      simp only [OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
        Set.univ_inter, Set.mem_preimage, Homeomorph.toOpenPartialHomeomorph_apply] at hy
      simpa using (chartAt E (e x)).map_source hy)
    refine (h3.congr (fun y hy => ?_)).contMDiffAt ((chartAt E x).open_source.mem_nhds
      (mem_chart_source E x))
    rw [hc] at hy
    simp only [OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
      Set.univ_inter, Set.mem_preimage, Homeomorph.toOpenPartialHomeomorph_apply] at hy
    simp only [Function.comp_apply, hc, OpenPartialHomeomorph.coe_trans,
      Homeomorph.toOpenPartialHomeomorph_apply]
    exact ((chartAt E (e x)).left_inv hy).symm
  have hEs : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e.symm := by
    intro y
    have h1 : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (chartAt E (e.symm y)).symm
        (chartAt E (e.symm y)).target := contMDiffOn_chart_symm
    have h2 : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (chartAt E y) (chartAt E y).source :=
      contMDiffOn_chart
    have hcy : chartAt E (e.symm y) = e.toOpenPartialHomeomorph ≫ₕ chartAt E y := by
      rw [hc, Homeomorph.apply_symm_apply]
    have h3 := h1.comp h2 (fun z hz => by
      show chartAt E y z ∈ (chartAt E (e.symm y)).target
      rw [hcy]
      simpa using (chartAt E y).map_source hz)
    refine (h3.congr (fun z hz => ?_)).contMDiffAt ((chartAt E y).open_source.mem_nhds
      (mem_chart_source E y))
    simp only [Function.comp_apply, hcy, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.coe_trans]
    rw [(chartAt E y).left_inv hz]
    rfl
  let φ : G ≃* G' := MulEquiv.mk' e.toEquiv he
  refine ⟨d, inferInstance, { contMDiff_mul := ?_, contMDiff_inv := ?_ }⟩
  · have : (fun p : G × G => p.1 * p.2) = e.symm ∘ (fun q : G' × G' => q.1 * q.2) ∘
        Prod.map e e := by
      funext p
      simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd]
      rw [← he, Homeomorph.symm_apply_apply]
    rw [this]
    exact hEs.comp (contMDiff_mul 𝓘(ℝ, E) ∞ |>.comp (hE.prodMap hE))
  · have : (fun a : G => a⁻¹) = e.symm ∘ (fun b : G' => b⁻¹) ∘ e := by
      funext a
      have : e a⁻¹ = (e a)⁻¹ := map_inv φ a
      simp only [Function.comp_apply, ← this, Homeomorph.symm_apply_apply]
    rw [this]
    exact hEs.comp ((contMDiff_inv 𝓘(ℝ, E) ∞).comp hE)

/-- The body of `HSFormal.HilbertSmith` with the manifold in `Type u` and the group in `Type v`. -/
def HilbertSmithIn : Prop :=
  ∀ (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ConnectedSpace M]
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [SecondCountableTopology G] [MulAction G M] [ContinuousSMul G M]
    [FaithfulSMul G M], IsLieGroup' G

/-- The Hilbert–Smith statement in `Type` implies it in all universes: a second-countable Hausdorff
space is `Small.{0}`, so `M` and `G` can be replaced by their `Shrink`s. -/
theorem hilbertSmithIn_of_type (h : HilbertSmithIn.{0, 0}) : HilbertSmithIn.{u, v} := by
  intro n M _ _ _ _ _ G _ _ _ _ _ _ _ _ _
  have : Small.{0} M := small_of_secondCountable M
  have : Small.{0} G := small_of_secondCountable G
  let eM : M ≃ₜ Shrink.{0} M := Shrink.homeomorph M
  let eG : G ≃ₜ Shrink.{0} G := Shrink.homeomorph G
  have heG : ∀ x y, eG (x * y) = eG x * eG y := fun x y => equivShrink_mul x y
  let φG : G ≃* Shrink.{0} G := MulEquiv.mk' eG.toEquiv heG
  have hφ : ∀ x, φG x = eG x := fun _ => rfl
  have hφs : ∀ x, φG.symm x = eG.symm x := fun _ => rfl
  -- the manifold `Shrink M`
  have : T2Space (Shrink.{0} M) := eM.t2Space
  have : SecondCountableTopology (Shrink.{0} M) := eM.symm.isInducing.secondCountableTopology
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Shrink.{0} M) := pullbackChartedSpace eM.symm
  have : ConnectedSpace (Shrink.{0} M) := eM.surjective.connectedSpace eM.continuous
  -- the group `Shrink G`
  have : IsTopologicalGroup (Shrink.{0} G) :=
    { continuous_mul := by
        have : (fun p : Shrink.{0} G × Shrink.{0} G => p.1 * p.2) =
            eG ∘ (fun q : G × G => q.1 * q.2) ∘ Prod.map eG.symm eG.symm := by
          funext p
          simp [heG]
        rw [this]
        exact eG.continuous.comp (continuous_mul.comp
          (eG.symm.continuous.prodMap eG.symm.continuous))
      continuous_inv := by
        have : (fun a : Shrink.{0} G => a⁻¹) = eG ∘ (fun b : G => b⁻¹) ∘ eG.symm := by
          funext a
          simp only [Function.comp_apply, ← hφ, ← hφs, map_inv, MulEquiv.apply_symm_apply]
        rw [this]
        exact eG.continuous.comp (continuous_inv.comp eG.symm.continuous) }
  have : LocallyCompactSpace (Shrink.{0} G) := eG.symm.isOpenEmbedding.locallyCompactSpace
  have : T2Space (Shrink.{0} G) := eG.t2Space
  have : SecondCountableTopology (Shrink.{0} G) := eG.symm.isInducing.secondCountableTopology
  -- the action
  let act : MulAction (Shrink.{0} G) (Shrink.{0} M) :=
    { smul := fun g m => eM (eG.symm g • eM.symm m)
      one_smul := fun m => by
        change eM (eG.symm 1 • eM.symm m) = m
        rw [← hφs, map_one, one_smul, Homeomorph.apply_symm_apply]
      mul_smul := fun g h m => by
        change eM (eG.symm (g * h) • eM.symm m) = eM (eG.symm g • eM.symm (eM (eG.symm h • eM.symm m)))
        rw [← hφs, ← hφs, ← hφs, map_mul, mul_smul, Homeomorph.symm_apply_apply] }
  have hsmul : ∀ (g : Shrink.{0} G) (m : Shrink.{0} M), g • m = eM (eG.symm g • eM.symm m) :=
    fun _ _ => rfl
  have : ContinuousSMul (Shrink.{0} G) (Shrink.{0} M) := ⟨by
    have : (fun p : Shrink.{0} G × Shrink.{0} M => p.1 • p.2) =
        eM ∘ (fun q : G × M => q.1 • q.2) ∘ Prod.map eG.symm eM.symm := by
      funext p
      exact hsmul p.1 p.2
    rw [this]
    exact eM.continuous.comp (continuous_smul.comp
      (eG.symm.continuous.prodMap eM.symm.continuous))⟩
  have : FaithfulSMul (Shrink.{0} G) (Shrink.{0} M) := ⟨fun {g₁ g₂} hg => by
    apply eG.symm.injective
    apply eq_of_smul_eq_smul (α := M)
    intro m
    have := hg (eM m)
    rw [hsmul, hsmul, Homeomorph.symm_apply_apply] at this
    exact eM.injective this⟩
  exact IsLieGroup'.of_equiv eG heG (h n (Shrink.{0} M) (Shrink.{0} G))

/-- The body of `HSFormal.PadicExclusion` with the manifold in `Type u`. -/
def PadicExclusionIn : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ConnectedSpace M]
    [AddAction ℤ_[p] M] [ContinuousVAdd ℤ_[p] M], ¬ FaithfulVAdd ℤ_[p] M

/-- p-adic exclusion in `Type` implies it for manifolds in every universe. -/
theorem padicExclusionIn_of_type (h : PadicExclusionIn.{0}) : PadicExclusionIn.{u} := by
  intro p _ n M _ _ _ _ _ _ _ hF
  have : Small.{0} M := small_of_secondCountable M
  let eM : M ≃ₜ Shrink.{0} M := Shrink.homeomorph M
  have : T2Space (Shrink.{0} M) := eM.t2Space
  have : SecondCountableTopology (Shrink.{0} M) := eM.symm.isInducing.secondCountableTopology
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Shrink.{0} M) := pullbackChartedSpace eM.symm
  have : ConnectedSpace (Shrink.{0} M) := eM.surjective.connectedSpace eM.continuous
  let act : AddAction ℤ_[p] (Shrink.{0} M) :=
    { vadd := fun g m => eM (g +ᵥ eM.symm m)
      zero_vadd := fun m => by
        change eM ((0 : ℤ_[p]) +ᵥ eM.symm m) = m
        rw [zero_vadd, Homeomorph.apply_symm_apply]
      add_vadd := fun g h m => by
        change eM ((g + h) +ᵥ eM.symm m) = eM (g +ᵥ eM.symm (eM (h +ᵥ eM.symm m)))
        rw [add_vadd, Homeomorph.symm_apply_apply] }
  have hvadd : ∀ (g : ℤ_[p]) (m : Shrink.{0} M), g +ᵥ m = eM (g +ᵥ eM.symm m) := fun _ _ => rfl
  have : ContinuousVAdd ℤ_[p] (Shrink.{0} M) := ⟨by
    have : (fun q : ℤ_[p] × Shrink.{0} M => q.1 +ᵥ q.2) =
        eM ∘ (fun q : ℤ_[p] × M => q.1 +ᵥ q.2) ∘ Prod.map id eM.symm := by
      funext q
      exact hvadd q.1 q.2
    rw [this]
    exact eM.continuous.comp (continuous_vadd.comp (continuous_id.prodMap eM.symm.continuous))⟩
  refine h p n (Shrink.{0} M) ⟨fun {g₁ g₂} hg => ?_⟩
  apply eq_of_vadd_eq_vadd (P := M)
  intro m
  have := hg (eM m)
  rw [hvadd, hvadd, Homeomorph.symm_apply_apply] at this
  exact eM.injective this

end HSFormal.Universe

namespace HSFormal

open LTheory

/-- **p-adic exclusion** (boundaryless, `HSFormal.PadicExclusion`): `padicExclusion_of_model` with
the model lemmas discharged as in `hilbertSmith_of_model₅`. -/
theorem padicExclusion : PadicExclusion :=
  padicExclusion_of_model liftingPairNullAll liftingClosedSubAll
    (decBijModel_of_unionRel_halfLine (negKAll_of_negKHighAll negKHighAll)
      (fun _ _ _ _ _ N _ ↦ unionRel _ N) (fun _ _ _ _ _ N _ ↦ halfLineSplitKar _ N))
    Newman.newmanPrimeOrder

namespace Universe

universe u v

/-- **The Hilbert–Smith theorem** for a manifold `M : Type u` and a group `G : Type v`. -/
theorem hilbertSmith_univ : HilbertSmithIn.{u, v} :=
  hilbertSmithIn_of_type fun n M _ _ _ _ _ G _ _ _ _ _ _ _ _ _ ↦ hilbertSmith n M G

/-- **p-adic exclusion** for a manifold `M : Type u`. -/
theorem padicExclusion_univ : PadicExclusionIn.{u} :=
  padicExclusionIn_of_type fun p _ n M _ _ _ _ _ _ _ ↦ padicExclusion p n M

end Universe

end HSFormal
