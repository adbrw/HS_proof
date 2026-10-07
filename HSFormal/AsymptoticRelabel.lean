import HSFormal.AsymptoticSupport
import Mathlib.GroupTheory.GroupAction.SubMulAction

/-!
# Lemma 2.4: relabeling onto a support

For an isometric equivariant embedding `j : Y → X` of a compact nonempty `H`-space, pushing
labels forward along `j` is an equivalence `𝒜_G(Y) ≌ 𝒜_{j(Y)}(X)`.  For a closed invariant
`S ⊆ X` (a `SubMulAction`) and `j` the inclusion, this is manuscript Lemma 2.4.  Essential
surjectivity moves each orbit representative to a nearest point of `j(Y)`; the identity matrix
from old to new labels has propagation at most the support distance.
-/

noncomputable section

namespace HSFormal

open Filter Matrix CategoryTheory CategoryTheory.Limits Metric
open scoped Classical ENNReal Topology

universe u v

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  {π : ∀ i, G i →* H} {X : Type u} [MulAction H X] [PseudoEMetricSpace X]
  {Y : Type v} [MulAction H Y] [PseudoEMetricSpace Y]

theorem prop_one_le {A Z : Type*} [DecidableEq A] [PseudoEMetricSpace Z] (ℓ ℓ' : A → Z)
    {r : ℝ≥0∞} (h : ∀ a, edist (ℓ' a) (ℓ a) ≤ r) : prop (1 : Matrix A A ℚ) ℓ ℓ' ≤ r :=
  prop_le_iff.mpr fun b a hba ↦ by
    obtain rfl : b = a := by
      by_contra hne
      exact hba (one_apply_ne hne)
    exact h b

namespace AsymptoticObject

variable (j : Y → X)

/-- Push-forward of the labels along `j`. -/
def push (M : AsymptoticObject π Y) : AsymptoticObject π X :=
  ⟨M.rank, fun i k ↦ j (M.label i k)⟩

variable {j} (hj : Isometry j) (hjeq : ∀ (h : H) (y : Y), j (h • y) = h • j y)
include hjeq

omit [∀ i, Fintype (G i)] [PseudoEMetricSpace X] [PseudoEMetricSpace Y] in
theorem fullLabel_push (M : AsymptoticObject π Y) (i : ℕ) (b : Fin ((M.push j).rank i) × G i) :
    (M.push j).fullLabel i b = j (M.fullLabel i b) := by
  simp [fullLabel, push, hjeq]

include hj in
omit [∀ i, Fintype (G i)] in
theorem propSeq_push {M N : AsymptoticObject π Y} (f : Family M N) :
    propSeq (M.push j) (N.push j) f = propSeq M N f := by
  funext i
  simp only [propSeq, prop, fullLabel_push hjeq, hj.edist_eq]
  rfl

/-- Uniformly continuous equivariant push-forward preserves (2.1). -/
theorem tendsto_propSeq_push (hj : UniformContinuous j) {M N : AsymptoticObject π Y}
    (f : M ⟶ N) : Tendsto (propSeq (M.push j) (N.push j) f.1) atTop (𝓝 0) := by
  refine ENNReal.tendsto_nhds_zero.mpr fun ε hε ↦ ?_
  obtain ⟨δ, hδ, hjδ⟩ := EMetric.uniformContinuous_iff.mp hj ε hε
  filter_upwards [(tendsto_order.1 (tendsto_propSeq f)).2 δ hδ] with i hi
  refine prop_le_iff.mpr fun c a hca ↦ ?_
  rw [fullLabel_push hjeq, fullLabel_push hjeq]
  exact (hjδ ((edist_le_prop hca).trans_lt hi)).le

/-- Push-forward of controlled families along a uniformly continuous equivariant map; the
matrices are unchanged. -/
def pushFunctor (hj : UniformContinuous j) : AsymptoticObject π Y ⥤ AsymptoticObject π X where
  obj M := M.push j
  map {M N} f := show M.push j ⟶ N.push j from
    ⟨f.1, (⟨equivariant f, tendsto_propSeq_push hjeq hj f⟩ :
      IsControlled (M.push j) (N.push j) f.1)⟩

omit [∀ i, Fintype (G i)] [PseudoEMetricSpace Y] in
theorem isSupported_push (M : AsymptoticObject π Y) : (M.push j).IsSupported (Set.range j) :=
  tendsto_zero_of_forall_eq_zero fun i ↦ le_antisymm (iSup_le fun b ↦ by
    rw [fullLabel_push hjeq]
    exact (infEDist_zero_of_mem (Set.mem_range_self _)).le) bot_le

end AsymptoticObject

open AsymptoticObject

namespace AsymptoticCategory

variable {j : Y → X} (hjeq : ∀ (h : H) (y : Y), j (h • y) = h • j y)

/-- Push-forward `𝒜_G(Y) → 𝒜_G(X)` along a uniformly continuous equivariant map. -/
def pushTail (hj : UniformContinuous j) : AsymptoticCategory π Y ⥤ AsymptoticCategory π X :=
  CategoryTheory.Quotient.lift _ (pushFunctor hjeq hj ⋙ functor) fun _ _ _ _ h ↦
    (functor_map_eq_iff _ _).mpr h

/-- Push-forward preserves duality. -/
theorem pushTail_transpose (hj : UniformContinuous j) {A B : AsymptoticCategory π Y}
    (φ : A ⟶ B) : (pushTail hjeq hj).map (transpose φ) = transpose ((pushTail hjeq hj).map φ) := by
  obtain ⟨f, rfl⟩ := exists_rep φ
  rfl

variable (hj : Isometry j) {T : Set X} (hT : Set.range j = T)

/-- Push-forward into the support category `𝒜_T(X)`, `T = j(Y)`. -/
def relabelFunctor : AsymptoticCategory π Y ⥤ SupportCategory π T :=
  ObjectProperty.lift _ (pushTail hjeq hj.uniformContinuous) fun A ↦ hT ▸ isSupported_push hjeq A.as

/-- **Lemma 2.4 (relabeling onto a support).** For an isometric equivariant embedding of a
compact nonempty `H`-space, `𝒜_G(Y) → 𝒜_{j(Y)}(X)` is an equivalence. -/
theorem relabelFunctor_isEquivalence [IsIsometricSMul H X] [CompactSpace Y] [Nonempty Y] :
    (relabelFunctor (π := π) hjeq hj hT).IsEquivalence := by
  subst hT
  exact { faithful := ⟨fun {A B} φ ψ h ↦ by
    obtain ⟨f, rfl⟩ := exists_rep φ
    obtain ⟨g, rfl⟩ := exists_rep ψ
    have h' := congrArg InducedCategory.Hom.hom h
    change functor.map ((pushFunctor hjeq hj.uniformContinuous).map f) =
      functor.map ((pushFunctor hjeq hj.uniformContinuous).map g) at h'
    rw [functor_map_eq_iff] at h' ⊢
    exact h'⟩
          full := ⟨fun {A B} φ ↦ by
    obtain ⟨f, hf⟩ := exists_rep φ.hom
    refine ⟨functor.map ⟨f.1, ⟨equivariant f, ?_⟩⟩, ?_⟩
    · exact (congrArg (fun s => Tendsto s atTop (𝓝 0))
        (propSeq_push hj hjeq (M := A.as) (N := B.as) f.1)).mp (tendsto_propSeq f)
    · ext1
      exact hf⟩
          essSurj := ⟨fun O ↦ by
    set N := O.obj.as
    have hK : IsCompact (Set.range j) := isCompact_range hj.continuous
    choose z hz hzeq using fun x : X ↦ hK.exists_infEDist_eq_edist (Set.range_nonempty j) x
    choose y hy using hz
    let M : AsymptoticObject π Y := ⟨N.rank, fun i k ↦ y (N.label i k)⟩
    have hbound : ∀ i (b : Fin (N.rank i) × G i),
        edist (N.fullLabel i b) ((M.push j).fullLabel i b) ≤ N.supportDist (Set.range j) i := by
      intro i b
      have : (M.push j).fullLabel i b = π i b.2 • j (y (N.label i b.1)) := rfl
      rw [this, fullLabel, edist_smul_left, hy, ← hzeq, ← fullLabel_one N i b.1]
      exact infEDist_le_supportDist i _
    let u : M.push j ⟶ N := ⟨fun i ↦ (1 : Matrix (Fin (N.rank i) × G i) (Fin (N.rank i) × G i) ℚ),
      ⟨fun _ ↦ IsEquivariant.one, tendsto_zero_of_le O.property fun i ↦
        prop_one_le _ _ fun b ↦ hbound i b⟩⟩
    let w : N ⟶ M.push j := ⟨fun i ↦ (1 : Matrix (Fin (N.rank i) × G i) (Fin (N.rank i) × G i) ℚ),
      ⟨fun _ ↦ IsEquivariant.one, tendsto_zero_of_le O.property fun i ↦
        prop_one_le _ _ fun b ↦ (edist_comm _ _).trans_le (hbound i b)⟩⟩
    refine ⟨functor.obj M, ⟨ObjectProperty.isoMk _ (functor.mapIso
      { hom := u, inv := w, hom_inv_id := ?_, inv_hom_id := ?_ })⟩⟩ <;>
      exact hom_ext fun i ↦ Matrix.one_mul 1⟩ }

/-- **Lemma 2.4** for a closed invariant nonempty `S ⊆ X` (compact `X`): the inclusion
induces an equivalence `𝒜_G(S) ≌ 𝒜_S(X)`. -/
theorem relabelFunctor_subtype_isEquivalence [IsIsometricSMul H X] [CompactSpace X]
    (S : SubMulAction H X) (hS : IsClosed (S : Set X)) [Nonempty S] :
    (relabelFunctor (π := π) (j := ((↑) : S → X)) (fun h y ↦ SubMulAction.val_smul h y)
      (fun _ _ ↦ rfl) Subtype.range_coe).IsEquivalence := by
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp hS.isCompact
  exact relabelFunctor_isEquivalence _ _ _

end AsymptoticCategory

end HSFormal
