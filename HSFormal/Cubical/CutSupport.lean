import HSFormal.Cubical.CutStep
import HSFormal.Cubical.CutLift

/-!
# Supports of realized controlled sequences (cubical module C8)

* `ControlledSeq.LabelsNear A S`: the labels of `A` approach `S` uniformly; then every realized
  object `A.obj π r` lies in `𝒜_S(X)` (`isSupported_obj`).
* `inIdeal_hom`: a realized matrix sequence lies in the ideal `I_S` when the labels of the
  endpoints of its nonzero entries approach `S` uniformly (manuscript §2, `inIdeal_map_iff`).
-/

noncomputable section

namespace HSFormal.Cubical

open Filter Matrix CategoryTheory CategoryTheory.Limits HSFormal.LTheory HSFormal.Compression
  Metric AsymptoticCategory AsymptoticObject
open scoped ENNReal Topology Pointwise

namespace BasedComplex.ControlledSeq

variable {X : Type} [PseudoEMetricSpace X]

/-- The labels of `A` approach `S` uniformly. -/
def LabelsNear (A : ControlledSeq X) (S : Set X) : Prop :=
  Tendsto (fun i ↦ ⨆ σ, infEDist (A.label i σ) S) atTop (𝓝 0)

theorem LabelsNear.mono {A : ControlledSeq X} {S T : Set X} (h : A.LabelsNear S) (hST : S ⊆ T) :
    A.LabelsNear T :=
  tendsto_zero_of_le h fun _ ↦ iSup_mono fun _ ↦ infEDist_anti hST

/-- Labels of a restriction. -/
theorem labelsNear_restrict (A : ControlledSeq X) {P : ∀ i, (A.C i).X → Prop}
    [∀ i, DecidablePred (P i)] (hP : ∀ i, (A.C i).IsLocallyClosed (P i)) {S : Set X}
    (h : Tendsto (fun i ↦ ⨆ (σ) (_ : P i σ), infEDist (A.label i σ) S) atTop (𝓝 0)) :
    (A.restrict P hP).LabelsNear S :=
  tendsto_zero_of_le h fun i ↦ iSup_le fun σ ↦
    le_iSup₂_of_le (f := fun σ (_ : P i σ) ↦ infEDist (A.label i σ) S) σ.1 σ.2 le_rfl

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  (π : ∀ i, G i →* H) [MulAction H X] [IsIsometricSMul H X]

theorem isSupported_obj {A : ControlledSeq X} {S : Set X} (hS : ∀ h : H, h • S = S)
    (hA : A.LabelsNear S) (r : ℤ) : (A.obj π r).IsSupported S :=
  tendsto_zero_of_le hA fun i ↦ iSup_le fun b ↦ by
    rw [fullLabel, infEDist_smul_of_invariant hS]
    exact le_iSup (fun σ ↦ infEDist (A.label i σ) S) _

theorem supportProperty_obj {A : ControlledSeq X} {S : Set X} (hS : ∀ h : H, h • S = S)
    (hA : A.LabelsNear S) (r : ℤ) :
    supportProperty S (AsymptoticCategory.functor.obj (A.obj π r)) :=
  isSupported_obj π hS hA r

/-- **Realized matrices in the ideal `I_S`**: the endpoints of the nonzero entries approach `S`. -/
theorem inIdeal_hom {A B : ControlledSeq X} (u : ∀ i, Matrix (B.C i).X (A.C i).X ℚ) (hu)
    (r r' : ℤ) {S : Set X} (hS : ∀ h : H, h • S = S)
    (h : Tendsto (fun i ↦ ⨆ (κ) (σ) (_ : u i κ σ ≠ 0),
      max (infEDist (B.label i κ) S) (infEDist (A.label i σ) S)) atTop (𝓝 0)) :
    InIdeal S (AsymptoticCategory.functor.map (hom (A := A) (B := B) π u hu r r')) := by
  refine (inIdeal_map_iff _).mpr (tendsto_zero_of_le h fun i ↦ endpointDist_le_iff.mpr ?_)
  intro c a hca
  rw [hom_val] at hca
  obtain ⟨-, hne⟩ := sheet_apply_ne_zero hca
  have hle : max (infEDist (B.label i ((cellEquiv (B.C i) r').symm c.1).1) S)
      (infEDist (A.label i ((cellEquiv (A.C i) r).symm a.1).1) S) ≤
      ⨆ (κ) (σ) (_ : u i κ σ ≠ 0), max (infEDist (B.label i κ) S) (infEDist (A.label i σ) S) :=
    le_iSup₂_of_le (f := fun κ σ ↦ ⨆ (_ : u i κ σ ≠ 0),
      max (infEDist (B.label i κ) S) (infEDist (A.label i σ) S)) _ _ (le_iSup_of_le hne le_rfl)
  rw [fullLabel, fullLabel, infEDist_smul_of_invariant hS, infEDist_smul_of_invariant hS]
  exact ⟨(le_max_left _ _).trans hle, (le_max_right _ _).trans hle⟩

end BasedComplex.ControlledSeq

end HSFormal.Cubical
