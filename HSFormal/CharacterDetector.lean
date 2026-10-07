import Mathlib.Analysis.Complex.Circle
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.TietzeExtension

/-!
# Character averages and continuous orbit detectors

The measure below is the actual normalized Haar measure on a compact group. Averaging
with a circle character gives a continuous equivariant complex-valued function. A
character trivial on a point stabilizer descends to the compact orbit; Tietze extension
then supplies an averaging input whose average equals one at that point.

These are topological prerequisites for the detector in Section 7 of `fullHS_final.md`.
They do not assume the proposed controlled realization or assert a Hilbert–Smith theorem.
-/

noncomputable section

open Set Filter MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped Topology

namespace HSFormal

section NormalizedHaar

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Haar measure normalized on the whole compact group, rather than on an unspecified
positive compact neighborhood. -/
def normalizedCompactHaar : Measure G :=
  Measure.haarMeasure (⊤ : PositiveCompacts G)

instance normalizedCompactHaar_isHaar : IsHaarMeasure (normalizedCompactHaar G) := by
  unfold normalizedCompactHaar
  infer_instance

instance normalizedCompactHaar_isProbability : IsProbabilityMeasure (normalizedCompactHaar G) := by
  constructor
  simpa only [normalizedCompactHaar, PositiveCompacts.coe_top] using
    (Measure.haarMeasure_self (K₀ := (⊤ : PositiveCompacts G)))

end NormalizedHaar

section Average

variable {G X : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [MetricSpace X] [LocallyCompactSpace X] [MulAction G X] [ContinuousSMul G X]

/-- The character-weighted normalized Haar average. The circle codomain supplies both
the continuous inverse and the unit norm required by the eventual sphere detector. -/
def characterAverage (χ : G →* Circle) (f : X → ℂ) (x : X) : ℂ :=
  ∫ g, (↑((χ g)⁻¹) : ℂ) * f (g • x) ∂normalizedCompactHaar G

omit [LocallyCompactSpace X] in
/-- Continuous inputs are genuinely Bochner integrable against normalized Haar. -/
theorem characterAverage_integrable (χ : G →* Circle) (hχ : Continuous χ)
    (f : C(X, ℂ)) (x : X) :
    Integrable (fun g : G => (↑((χ g)⁻¹) : ℂ) * f (g • x)) (normalizedCompactHaar G) := by
  have hcont : Continuous (fun g : G => (↑((χ g)⁻¹) : ℂ) * f (g • x)) :=
    (continuous_subtype_val.comp hχ.inv).mul
      (f.continuous.comp (continuous_id.smul continuous_const))
  have hi := ContinuousOn.integrableOn_compact
    (μ := normalizedCompactHaar G) (isCompact_univ : IsCompact (univ : Set G))
    hcont.continuousOn
  simpa only [IntegrableOn, Measure.restrict_univ] using hi

omit [T2Space G] in
theorem characterAverage_continuous (χ : G →* Circle) (hχ : Continuous χ)
    (f : C(X, ℂ)) : Continuous (characterAverage χ f) := by
  have hcont : Continuous (fun z : X × G =>
      (↑((χ z.2)⁻¹) : ℂ) * f (z.2 • z.1)) :=
    (continuous_subtype_val.comp (hχ.comp continuous_snd).inv).mul
      (f.continuous.comp (continuous_snd.smul continuous_fst))
  have hint := continuous_parametric_integral_of_continuous
    (f := fun x : X => fun g : G => (↑((χ g)⁻¹) : ℂ) * f (g • x))
    (μ := normalizedCompactHaar G) hcont (isCompact_univ : IsCompact (univ : Set G))
  unfold characterAverage
  simpa only [Measure.restrict_univ] using hint

omit [T2Space G] [MetricSpace X] [LocallyCompactSpace X] [ContinuousSMul G X] in
theorem characterAverage_equivariant (χ : G →* Circle) (f : X → ℂ)
    (h : G) (x : X) :
    characterAverage χ f (h • x) = (χ h : ℂ) * characterAverage χ f x := by
  have hchar (g : G) :
      (χ h : ℂ) * (↑((χ (g * h))⁻¹) : ℂ) = (↑((χ g)⁻¹) : ℂ) := by
    rw [← Circle.coe_mul]
    congr 1
    simp only [map_mul, mul_inv_rev]
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  calc
    characterAverage χ f (h • x) =
        ∫ g, (χ h : ℂ) *
          ((↑((χ (g * h))⁻¹) : ℂ) * f ((g * h) • x)) ∂normalizedCompactHaar G := by
      apply integral_congr_ae
      filter_upwards with g
      simp only [mul_smul]
      rw [← mul_assoc, hchar]
    _ = (χ h : ℂ) *
        (∫ g, (↑((χ (g * h))⁻¹) : ℂ) * f ((g * h) • x) ∂normalizedCompactHaar G) :=
      integral_const_mul _ _
    _ = (χ h : ℂ) * characterAverage χ f x := by
      exact congrArg (fun z : ℂ => (χ h : ℂ) * z)
        (integral_mul_right_eq_self (μ := normalizedCompactHaar G)
          (fun g : G => (↑((χ g)⁻¹) : ℂ) * f (g • x)) h)

omit [T2Space G] [MetricSpace X] [LocallyCompactSpace X] [ContinuousSMul G X] in
/-- Prescribed character values on an orbit force the normalized average to equal one
at its base point. This establishes nonvanishing without a cancellation assumption. -/
theorem characterAverage_eq_one_of_orbit_values (χ : G →* Circle) (f : X → ℂ) (x : X)
    (hf : ∀ g : G, f (g • x) = (χ g : ℂ)) :
    characterAverage χ f x = 1 := by
  have heq : (fun g : G => (↑((χ g)⁻¹) : ℂ) * f (g • x)) = fun _ => (1 : ℂ) := by
    funext g
    rw [hf g, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]
  unfold characterAverage
  rw [heq]
  simp

def characterAverageMap (χ : G →* Circle) (hχ : Continuous χ) (f : C(X, ℂ)) : C(X, ℂ) :=
  ⟨characterAverage χ f, characterAverage_continuous χ hχ f⟩

end Average

section OrbitExtension

variable {G X : Type*} [Group G] [MulAction G X]

/-- Killing the stabilizer is exactly what is needed for character values to be
well-defined on an orbit. -/
theorem character_eq_of_smul_eq (χ : G →* Circle) (x : X)
    (hstab : ∀ g : G, g • x = x → χ g = 1)
    {a b : G} (hab : a • x = b • x) : χ a = χ b := by
  have hfixed : (a⁻¹ * b) • x = x := by
    rw [mul_smul, ← hab, inv_smul_smul]
  have hchar := hstab (a⁻¹ * b) hfixed
  simp only [map_mul, map_inv] at hchar
  exact eq_of_inv_mul_eq_one hchar

variable [TopologicalSpace G] [CompactSpace G] [MetricSpace X] [ContinuousSMul G X]

/-- A continuous character that kills the stabilizer extends from the compact orbit
to a continuous complex-valued function on the metric ambient space. Tietze is applied
through the real product model of the complex numbers. -/
theorem exists_continuous_orbit_character_extension (χ : G →* Circle) (hχ : Continuous χ)
    (x : X) (hstab : ∀ g : G, g • x = x → χ g = 1) :
    ∃ f : C(X, ℂ), ∀ g : G, f (g • x) = (χ g : ℂ) := by
  let O : Set X := range (fun g : G => g • x)
  let q : G → O := fun g => ⟨g • x, ⟨g, rfl⟩⟩
  let phase : O → Circle := fun z => χ (Classical.choose z.2)
  have hphase (g : G) : phase (q g) = χ g := by
    exact character_eq_of_smul_eq χ x hstab (Classical.choose_spec (q g).2)
  have hq : Continuous q :=
    (continuous_id.smul continuous_const).subtype_mk _
  have hsurj : Function.Surjective q := by
    intro z
    obtain ⟨g, hg⟩ := z.2
    exact ⟨g, Subtype.ext hg⟩
  have hquot : Topology.IsQuotientMap q :=
    Topology.IsQuotientMap.of_surjective_continuous hsurj hq
  have hphaseCont : Continuous phase := by
    apply hquot.continuous_iff.mpr
    have heq : phase ∘ q = χ := funext hphase
    rw [heq]
    exact hχ
  have hO : IsClosed O := by
    have hxc : Continuous (fun g : G => g • x) := continuous_id.smul continuous_const
    have hc := (isCompact_univ : IsCompact (univ : Set G)).image hxc
    simpa only [O, image_univ] using hc.isClosed
  let p : C(O, ℂ) := ⟨fun z => (phase z : ℂ), continuous_subtype_val.comp hphaseCont⟩
  letI : TietzeExtension ℂ :=
    TietzeExtension.of_homeo Complex.equivRealProdCLM.toHomeomorph
  obtain ⟨f, hf⟩ := p.exists_restrict_eq hO
  refine ⟨f, fun g => ?_⟩
  have hh := congrArg (fun F : C(O, ℂ) => F (q g)) hf
  exact hh.trans (congrArg (fun z : Circle => (z : ℂ)) (hphase g))

end OrbitExtension

section PointDetector

variable {G X : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [MetricSpace X] [LocallyCompactSpace X] [MulAction G X] [ContinuousSMul G X]

omit [T2Space G] in
/-- A character killing a point's stabilizer has a continuous equivariant detector
equal to one at that point. The orbit-value input is constructed, not assumed. -/
theorem exists_equivariant_character_function_at (χ : G →* Circle) (hχ : Continuous χ)
    (x : X) (hstab : ∀ g : G, g • x = x → χ g = 1) :
    ∃ F : C(X, ℂ), F x = 1 ∧
      ∀ g : G, ∀ y : X, F (g • y) = (χ g : ℂ) * F y := by
  obtain ⟨f, hf⟩ := exists_continuous_orbit_character_extension χ hχ x hstab
  exact ⟨characterAverageMap χ hχ f,
    characterAverage_eq_one_of_orbit_values χ f x hf,
    characterAverage_equivariant χ f⟩

omit [T2Space G] in
/-- A compact carrier whose stabilizers lie in the character kernel has a finite
family of continuous equivariant complex coordinates with no common zero on the
carrier. This is the finite-cover step in the construction of the sphere detector. -/
theorem exists_finite_character_detector (χ : G →* Circle) (hχ : Continuous χ)
    {K : Set X} (hK : IsCompact K)
    (hstab : ∀ x ∈ K, ∀ g : G, g • x = x → χ g = 1) :
    ∃ Fs : Finset C(X, ℂ),
      (∀ F ∈ Fs, ∀ g : G, ∀ y : X, F (g • y) = (χ g : ℂ) * F y) ∧
      ∀ x ∈ K, ∃ F ∈ Fs, F x ≠ 0 := by
  classical
  let E := {F : C(X, ℂ) // ∀ g : G, ∀ y : X, F (g • y) = (χ g : ℂ) * F y}
  let U : E → Set X := fun F => {y | F.1 y ≠ 0}
  have hopen : ∀ F : E, IsOpen (U F) := fun F =>
    isOpen_ne_fun F.1.continuous continuous_const
  have hcover : K ⊆ ⋃ F : E, U F := by
    intro x hx
    obtain ⟨F, hFx, hFeq⟩ := exists_equivariant_character_function_at χ hχ x (hstab x hx)
    refine Set.mem_iUnion.mpr ⟨⟨F, hFeq⟩, ?_⟩
    change F x ≠ 0
    rw [hFx]
    exact one_ne_zero
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U hopen hcover
  refine ⟨s.image Subtype.val, ?_, ?_⟩
  · intro F hF
    obtain ⟨F', _, rfl⟩ := Finset.mem_image.mp hF
    exact F'.2
  · intro x hx
    obtain ⟨F, hFs, hFx⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact ⟨F.1, Finset.mem_image.mpr ⟨F, hFs, rfl⟩, hFx⟩

end PointDetector

end HSFormal
