import HSFormal.AsymptoticCategory
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Supports in `𝒜_G(X)`: `𝒜_S(X)`, `I_S`, `ℬ_Z(X)` and Lemmas 2.2, 2.3

For `S ⊆ X`, `𝒜_S(X)` is the full subcategory of objects whose labels approach `S`
uniformly, measured with `Metric.infEDist` (so `S = ∅` gives the eventually empty objects).
`I_S` is the ideal of maps factoring through `𝒜_S(X)`; `ℬ_Z(X) = 𝒜(X)/𝒜_Z(X)` is the quotient
by `I_Z`.  We prove the characterization of `I_S` by endpoints of nonzero entries
(manuscript §2, unnumbered), the separation Lemma 2.3, and the excision Lemma 2.2.
-/

noncomputable section

namespace HSFormal

open Filter Matrix CategoryTheory CategoryTheory.Limits Metric
open scoped Classical ENNReal Topology Pointwise

universe u

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)]
  {π : ∀ i, G i →* H} {X : Type u} [MulAction H X] [PseudoEMetricSpace X]

namespace AsymptoticObject

variable (S : Set X) (M : AsymptoticObject π X)

/-- `sup_b d(ℓ_i b, S)` at index `i`. -/
def supportDist (i : ℕ) : ℝ≥0∞ :=
  ⨆ b, infEDist (M.fullLabel i b) S

/-- The distance of the free orbit of `k` from `S`. -/
def orbitDist (i : ℕ) (k : Fin (M.rank i)) : ℝ≥0∞ :=
  ⨆ g, infEDist (M.fullLabel i (k, g)) S

/-- Membership in `𝒜_S(X)`: labels approach `S` uniformly. -/
def IsSupported : Prop :=
  Tendsto (M.supportDist S) atTop (𝓝 0)

/-- The largest endpoint distance from `S` over the nonzero entries at index `i`. -/
def endpointDist (S : Set X) {M N : AsymptoticObject π X} (f : Family M N) (i : ℕ) : ℝ≥0∞ :=
  ⨆ (c) (a) (_ : f i c a ≠ 0), max (infEDist (N.fullLabel i c) S) (infEDist (M.fullLabel i a) S)

variable {S M}

theorem infEDist_le_supportDist (i : ℕ) (b : Fin (M.rank i) × G i) :
    infEDist (M.fullLabel i b) S ≤ M.supportDist S i :=
  le_iSup (fun b ↦ infEDist (M.fullLabel i b) S) b

theorem infEDist_le_orbitDist (i : ℕ) (k : Fin (M.rank i)) (g : G i) :
    infEDist (M.fullLabel i (k, g)) S ≤ M.orbitDist S i k :=
  le_iSup (fun g ↦ infEDist (M.fullLabel i (k, g)) S) g

theorem orbitDist_le_supportDist (i : ℕ) (k : Fin (M.rank i)) :
    M.orbitDist S i k ≤ M.supportDist S i :=
  iSup_le fun g ↦ infEDist_le_supportDist i (k, g)

theorem IsSupported.mono {T : Set X} (hST : S ⊆ T) (hM : M.IsSupported S) : M.IsSupported T :=
  tendsto_zero_of_le hM fun _ ↦ iSup_mono fun _ ↦ infEDist_anti hST

theorem isSupported_zeroObj : (zeroObj : AsymptoticObject π X).IsSupported S :=
  tendsto_zero_of_forall_eq_zero fun i ↦ by
    simp only [supportDist]
    exact le_antisymm (iSup_le fun b ↦ b.1.elim0) bot_le

theorem supportDist_biprodObj_le (N : AsymptoticObject π X) (i : ℕ) :
    (biprodObj M N).supportDist S i ≤ max (M.supportDist S i) (N.supportDist S i) := by
  refine iSup_le fun b ↦ ?_
  obtain ⟨k, g⟩ := b
  refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) k
  · refine le_trans (le_of_eq ?_) ((infEDist_le_supportDist (M := M) i (k, g)).trans
      (le_max_left _ _))
    simp [fullLabel, biprodObj]
  · refine le_trans (le_of_eq ?_) ((infEDist_le_supportDist (M := N) i (k, g)).trans
      (le_max_right _ _))
    simp [fullLabel, biprodObj]

theorem IsSupported.biprodObj {N : AsymptoticObject π X} (hM : M.IsSupported S)
    (hN : N.IsSupported S) : (biprodObj M N).IsSupported S :=
  tendsto_zero_of_le (by simpa using hM.max hN) (supportDist_biprodObj_le N)

theorem endpointDist_le_iff {N : AsymptoticObject π X} {f : Family M N} {i : ℕ} {r : ℝ≥0∞} :
    endpointDist S f i ≤ r ↔ ∀ c a, f i c a ≠ 0 →
      infEDist (N.fullLabel i c) S ≤ r ∧ infEDist (M.fullLabel i a) S ≤ r := by
  simp only [endpointDist, iSup_le_iff, max_le_iff]

theorem endpointDist_le_of_supported {N : AsymptoticObject π X} (f : Family M N) (i : ℕ) :
    endpointDist S f i ≤ max (N.supportDist S i) (M.supportDist S i) :=
  endpointDist_le_iff.mpr fun c a _ ↦
    ⟨(infEDist_le_supportDist i c).trans (le_max_left _ _),
      (infEDist_le_supportDist i a).trans (le_max_right _ _)⟩

variable [∀ i, Fintype (G i)]

/-- A nonzero entry of an equivariant map transports orbit distances by its propagation. -/
theorem orbitDist_target_le {N : AsymptoticObject π X} (f : M ⟶ N) (i : ℕ)
    (c : Fin (N.rank i) × G i) (a : Fin (M.rank i) × G i) (h : f.1 i c a ≠ 0) :
    N.orbitDist S i c.1 ≤ M.orbitDist S i a.1 + propSeq M N f.1 i := by
  refine iSup_le fun g ↦ ?_
  set x := g * c.2⁻¹
  have hc : ((c.1, x * c.2) : Fin (N.rank i) × G i) = (c.1, g) := by simp [x]
  have h' : f.1 i (c.1, x * c.2) (a.1, x * a.2) ≠ 0 := by rwa [equivariant f i x c a]
  rw [← hc]
  calc infEDist (N.fullLabel i (c.1, x * c.2)) S
      ≤ infEDist (M.fullLabel i (a.1, x * a.2)) S +
          edist (N.fullLabel i (c.1, x * c.2)) (M.fullLabel i (a.1, x * a.2)) :=
        infEDist_le_infEDist_add_edist
    _ ≤ M.orbitDist S i a.1 + propSeq M N f.1 i :=
        add_le_add (infEDist_le_orbitDist i a.1 _) (edist_le_prop h')

theorem orbitDist_source_le {N : AsymptoticObject π X} (f : M ⟶ N) (i : ℕ)
    (c : Fin (N.rank i) × G i) (a : Fin (M.rank i) × G i) (h : f.1 i c a ≠ 0) :
    M.orbitDist S i a.1 ≤ N.orbitDist S i c.1 + propSeq M N f.1 i := by
  have h' : (transpose f).1 i a c ≠ 0 := h
  have := orbitDist_target_le (S := S) (transpose f) i a c h'
  simpa [propSeq, prop_transpose] using this

end AsymptoticObject

open AsymptoticObject

variable [∀ i, Fintype (G i)]

namespace AsymptoticCategory

variable (S : Set X)

/-- The object property defining `𝒜_S(X)`. -/
def supportProperty : ObjectProperty (AsymptoticCategory π X) :=
  fun A ↦ A.as.IsSupported S

variable (π) in
/-- The support category `𝒜_S(X)`. -/
abbrev SupportCategory :=
  (supportProperty (π := π) S).FullSubcategory

/-- The ideal `I_S` of maps factoring through an object of `𝒜_S(X)`. -/
def InIdeal {A B : AsymptoticCategory π X} (φ : A ⟶ B) : Prop :=
  ∃ (W : AsymptoticCategory π X) (_ : supportProperty S W) (u : A ⟶ W) (v : W ⟶ B), φ = u ≫ v

variable {S}

theorem supportProperty_functor_obj {M : AsymptoticObject π X} :
    supportProperty S (functor.obj M) ↔ M.IsSupported S := Iff.rfl

/-- For `S = ∅` the support category is the zero category. -/
theorem isZero_of_isSupported_empty {M : AsymptoticObject π X} (hM : M.IsSupported ∅) :
    IsZero (functor.obj M) := by
  refine (IsZero.iff_id_eq_zero _).mpr ?_
  rw [← CategoryTheory.Functor.map_id, ← functor.map_zero M M, functor_map_eq_iff]
  filter_upwards [(tendsto_order.1 hM).2 1 one_pos] with i hi
  ext b
  exfalso
  have := (infEDist_le_supportDist (S := ∅) i (b.1, 1)).trans_lt hi
  simp at this

theorem InIdeal.zero (A B : AsymptoticCategory π X) : InIdeal S (0 : A ⟶ B) :=
  ⟨functor.obj zeroObj, isSupported_zeroObj, 0, 0, by simp⟩

theorem InIdeal.comp_left {A B C : AsymptoticCategory π X} (ψ : A ⟶ B) {φ : B ⟶ C}
    (h : InIdeal S φ) : InIdeal S (ψ ≫ φ) := by
  obtain ⟨W, hW, u, v, rfl⟩ := h
  exact ⟨W, hW, ψ ≫ u, v, by simp⟩

theorem InIdeal.comp_right {A B C : AsymptoticCategory π X} {φ : A ⟶ B} (ψ : B ⟶ C)
    (h : InIdeal S φ) : InIdeal S (φ ≫ ψ) := by
  obtain ⟨W, hW, u, v, rfl⟩ := h
  exact ⟨W, hW, u, v ≫ ψ, by simp⟩

theorem InIdeal.neg {A B : AsymptoticCategory π X} {φ : A ⟶ B} (h : InIdeal S φ) :
    InIdeal S (-φ) := by
  obtain ⟨W, hW, u, v, rfl⟩ := h
  exact ⟨W, hW, u, -v, by simp⟩

theorem InIdeal.smul (c : ℚ) {A B : AsymptoticCategory π X} {φ : A ⟶ B} (h : InIdeal S φ) :
    InIdeal S (c • φ) := by
  obtain ⟨W, hW, u, v, rfl⟩ := h
  exact ⟨W, hW, u, c • v, by simp⟩

theorem InIdeal.add {A B : AsymptoticCategory π X} {φ ψ : A ⟶ B} (hφ : InIdeal S φ)
    (hψ : InIdeal S ψ) : InIdeal S (φ + ψ) := by
  obtain ⟨W, hW, u, v, rfl⟩ := hφ
  obtain ⟨W', hW', u', v', rfl⟩ := hψ
  let b := biprodBicone W W'
  refine ⟨b.pt, IsSupported.biprodObj hW hW', u ≫ b.inl + u' ≫ b.inr,
    b.fst ≫ v + b.snd ≫ v', ?_⟩
  simp [b]

theorem InIdeal.sub {A B : AsymptoticCategory π X} {φ ψ : A ⟶ B} (hφ : InIdeal S φ)
    (hψ : InIdeal S ψ) : InIdeal S (φ - ψ) := by
  simpa [sub_eq_add_neg] using hφ.add hψ.neg

theorem InIdeal.mono {T : Set X} (hST : S ⊆ T) {A B : AsymptoticCategory π X} {φ : A ⟶ B}
    (h : InIdeal S φ) : InIdeal T φ := by
  obtain ⟨W, hW, u, v, rfl⟩ := h
  exact ⟨W, IsSupported.mono hST hW, u, v, rfl⟩

/-- Manuscript §2: a map lies in `I_S` exactly when the endpoints of all its nonzero entries
approach `S` uniformly. -/
theorem inIdeal_map_iff {M N : AsymptoticObject π X} (f : M ⟶ N) :
    InIdeal S (functor.map f) ↔ Tendsto (endpointDist S f.1) atTop (𝓝 0) := by
  constructor
  · rintro ⟨W, hW, u, v, huv⟩
    obtain ⟨u, rfl⟩ := exists_rep u
    obtain ⟨v, rfl⟩ := exists_rep v
    rw [← Functor.map_comp, functor_map_eq_iff] at huv
    refine tendsto_zero_of_eventually_le
      (by simpa using (hW.add (tendsto_propSeq u)).add (tendsto_propSeq v)) ?_
    filter_upwards [huv] with i hi
    refine endpointDist_le_iff.mpr fun c a hca ↦ ?_
    rw [hi, comp_val] at hca
    obtain ⟨w, hvw, huw⟩ := matrix_mul_entry_nonzero_witness _ _ c a hca
    constructor
    · calc infEDist (N.fullLabel i c) S
          ≤ infEDist (W.as.fullLabel i w) S + edist (N.fullLabel i c) (W.as.fullLabel i w) :=
            infEDist_le_infEDist_add_edist
        _ ≤ W.as.supportDist S i + propSeq W.as N v.1 i :=
            add_le_add (infEDist_le_supportDist i w) (edist_le_prop hvw)
        _ ≤ _ := by
            rw [add_assoc]
            exact add_le_add le_rfl le_add_self
    · calc infEDist (M.fullLabel i a) S
          ≤ infEDist (W.as.fullLabel i w) S + edist (M.fullLabel i a) (W.as.fullLabel i w) :=
            infEDist_le_infEDist_add_edist
        _ ≤ W.as.supportDist S i + propSeq M W.as u.1 i := by
            rw [edist_comm]
            exact add_le_add (infEDist_le_supportDist i w) (edist_le_prop huw)
        _ ≤ _ := le_self_add
  · intro hf
    let P : ∀ i, Fin (M.rank i) → Prop := fun i k ↦ ∃ c g, f.1 i c (k, g) ≠ 0
    refine ⟨functor.obj (M.restrict P), ?_, functor.map (M.restrictEmb P).proj,
      functor.map ((M.restrictEmb P).incl ≫ f), ?_⟩
    · refine tendsto_zero_of_le hf fun i ↦ iSup_le fun b ↦ ?_
      obtain ⟨c, g, hcg⟩ := ((M.mem_range_restrictEmb P i _).mp ⟨b.1, rfl⟩)
      set k := (M.restrictEmb P).toFun i b.1
      set x := b.2 * g⁻¹
      have h' : f.1 i (c.1, x * c.2) (k, x * g) ≠ 0 := by rwa [equivariant f i x c (k, g)]
      have hb : (M.restrict P).fullLabel i b = M.fullLabel i (k, x * g) := by
        simp [x, k, fullLabel, (M.restrictEmb P).label_toFun]
      change infEDist ((M.restrict P).fullLabel i b) S ≤ _
      rw [hb]
      exact ((endpointDist_le_iff.mp le_rfl) _ _ h').2
    · rw [← Functor.map_comp, ← Category.assoc, restrict_proj_incl]
      congr 1
      refine hom_ext fun i ↦ ?_
      ext c a
      simp only [comp_val, diagProj_val, mul_diagonal]
      by_cases ha : P i a.1
      · simp [ha]
      · have : f.1 i c a = 0 := by
          by_contra h
          exact ha ⟨c, a.2, h⟩
        simp [ha, this]

variable (S) in
/-- `φ ~ ψ` iff `φ - ψ ∈ I_S`. -/
def idealRel : HomRel (AsymptoticCategory π X) :=
  fun _ _ φ ψ ↦ InIdeal S (φ - ψ)

instance idealRel_congruence : Congruence (idealRel (π := π) S) where
  equivalence := ⟨fun _ ↦ by simpa [idealRel] using InIdeal.zero _ _,
    fun h ↦ by simpa [idealRel] using h.neg, fun h h' ↦ by simpa [idealRel] using h.add h'⟩
  comp_left φ _ _ h := by simpa [idealRel, Preadditive.comp_sub] using h.comp_left φ
  comp_right ψ h := by simpa [idealRel, Preadditive.sub_comp] using h.comp_right ψ

end AsymptoticCategory

open AsymptoticCategory

variable (π) in
/-- The exterior quotient `ℬ_Z(X) = 𝒜(X)/𝒜_Z(X)`, (2.3). -/
abbrev ExteriorCategory (Z : Set X) :=
  CategoryTheory.Quotient (idealRel (π := π) Z)

namespace ExteriorCategory

variable {Z : Set X}

instance preadditive : Preadditive (ExteriorCategory π Z) :=
  Quotient.preadditive _ fun _ _ _ _ _ _ h h' ↦ by
    simpa [idealRel, add_sub_add_comm] using h.add h'

/-- The quotient functor `𝒜(X) → ℬ_Z(X)`. -/
abbrev functor : AsymptoticCategory π X ⥤ ExteriorCategory π Z :=
  Quotient.functor _

instance functor_additive : (functor (π := π) (Z := Z)).Additive :=
  Quotient.functor_additive _ _

instance linear : Linear ℚ (ExteriorCategory π Z) :=
  Quotient.linear ℚ _ fun c _ _ _ _ h ↦ by simpa [idealRel, ← smul_sub] using h.smul c

/-- Manuscript (2.3): every equation in `ℬ_Z(X)` is a factorization of its defect through
`𝒜_Z(X)`. -/
theorem functor_map_eq_iff {A B : AsymptoticCategory π X} (φ ψ : A ⟶ B) :
    (functor (Z := Z)).map φ = functor.map ψ ↔ InIdeal Z (φ - ψ) :=
  Quotient.functor_map_eq_iff _ φ ψ

end ExteriorCategory

namespace AsymptoticCategory

/-! ### Lemma 2.3 (separation) -/

variable {S Z : Set X}

theorem eventually_eq_zero_of_separated (hSZ : 0 < ⨅ (s ∈ S) (z ∈ Z), edist s z)
    {M N : AsymptoticObject π X} (f : M ⟶ N) (hM : M.IsSupported S)
    (hf : Tendsto (endpointDist Z f.1) atTop (𝓝 0)) : ∀ᶠ i in atTop, f.1 i = 0 := by
  set δ := ⨅ (s ∈ S) (z ∈ Z), edist s z
  have hε : 0 < δ / 2 := ENNReal.half_pos hSZ.ne'
  filter_upwards [(tendsto_order.1 hM).2 _ hε, (tendsto_order.1 hf).2 _ hε] with i hMi hfi
  ext c a
  by_contra hca
  obtain ⟨s, hs, hxs⟩ := infEDist_lt_iff.mp ((infEDist_le_supportDist i a).trans_lt hMi)
  obtain ⟨z, hz, hxz⟩ := infEDist_lt_iff.mp
    ((((endpointDist_le_iff.mp le_rfl) c a hca).2).trans_lt hfi)
  have hδ : δ ≤ edist s z := (iInf₂_le s hs).trans (iInf₂_le z hz)
  have : edist s z < δ := by
    calc edist s z ≤ edist s (M.fullLabel i a) + edist (M.fullLabel i a) z := edist_triangle _ _ _
      _ < δ / 2 + δ / 2 := by
          rw [edist_comm] at hxs
          exact ENNReal.add_lt_add hxs hxz
      _ = δ := ENNReal.add_halves δ
  exact (this.trans_le hδ).false

variable (S Z) in
/-- The composite `𝒜_S(X) ⊂ 𝒜(X) → ℬ_Z(X)`. -/
def separationFunctor : SupportCategory π S ⥤ ExteriorCategory π Z :=
  (supportProperty S).ι ⋙ ExteriorCategory.functor

instance separationFunctor_full : (separationFunctor (π := π) S Z).Full where
  map_surjective {_ _} φ := by
    obtain ⟨ψ, rfl⟩ := (ExteriorCategory.functor (Z := Z)).map_surjective φ
    exact ⟨ObjectProperty.homMk ψ, rfl⟩

/-- **Lemma 2.3 (separation).** If `d(S, Z) > 0`, then `𝒜_S(X) → ℬ_Z(X)` is fully faithful. -/
theorem separationFunctor_faithful (hSZ : 0 < ⨅ (s ∈ S) (z ∈ Z), edist s z) :
    (separationFunctor (π := π) S Z).Faithful where
  map_injective {A B} φ ψ h := by
    ext1
    change ExteriorCategory.functor.map φ.hom = ExteriorCategory.functor.map ψ.hom at h
    rw [ExteriorCategory.functor_map_eq_iff] at h
    obtain ⟨f, hf⟩ := exists_rep (φ.hom - ψ.hom)
    rw [← hf, inIdeal_map_iff] at h
    rw [← sub_eq_zero, ← hf, functor_map_eq_zero_iff]
    exact eventually_eq_zero_of_separated hSZ f A.property h

theorem separationFunctor_fullyFaithful (hSZ : 0 < ⨅ (s ∈ S) (z ∈ Z), edist s z) :
    Nonempty (separationFunctor (π := π) S Z).FullyFaithful := by
  haveI := separationFunctor_faithful (π := π) hSZ
  exact ⟨Functor.FullyFaithful.ofFullyFaithful _⟩

end AsymptoticCategory

/-! ### Lemma 2.2 (excision) -/

section Excision

variable [CompactSpace X] {A B : Set X}

/-- The compactness estimate `N_t(A) ∩ N_t(B) ⊆ N_{η(t)}(A ∩ B)` in the proof of Lemma 2.2. -/
theorem exists_pos_infEDist_inter (hA : IsClosed A) (hB : IsClosed B) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x, infEDist x A < δ → infEDist x B < δ → infEDist x (A ∩ B) < ε := by
  set K := {x | ε ≤ infEDist x (A ∩ B)}
  have hK : IsCompact K := (isClosed_le continuous_const continuous_infEDist).isCompact
  rcases K.eq_empty_or_nonempty with hK0 | hKne
  · refine ⟨1, one_pos, fun x _ _ ↦ not_le.mp fun hx ↦ ?_⟩
    have : x ∈ K := hx
    simp [hK0] at this
  obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hKne
    ((continuous_infEDist.max continuous_infEDist).continuousOn)
  refine ⟨max (infEDist x₀ A) (infEDist x₀ B), ?_, fun x hxA hxB ↦ not_le.mp fun hx ↦ ?_⟩
  · refine pos_iff_ne_zero.mpr fun h0 ↦ ?_
    have hx : x₀ ∈ A ∩ B := ⟨(mem_iff_infEDist_zero_of_closed hA).mpr (le_antisymm
      ((le_max_left _ _).trans h0.le) bot_le), (mem_iff_infEDist_zero_of_closed hB).mpr
      (le_antisymm ((le_max_right _ _).trans h0.le) bot_le)⟩
    have hx₀' : ε ≤ infEDist x₀ (A ∩ B) := hx₀
    rw [infEDist_zero_of_mem hx] at hx₀'
    exact hε.ne' (le_antisymm hx₀' bot_le)
  · exact (isMinOn_iff.mp hmin x hx).not_gt (max_lt hxA hxB)

theorem eventually_infEDist_inter_lt (hA : IsClosed A) (hB : IsClosed B) {ε : ℝ≥0∞}
    (hε : 0 < ε) {a b : ℕ → ℝ≥0∞} (ha : Tendsto a atTop (𝓝 0)) (hb : Tendsto b atTop (𝓝 0)) :
    ∀ᶠ i in atTop, ∀ x, infEDist x A ≤ a i → infEDist x B ≤ b i → infEDist x (A ∩ B) < ε := by
  obtain ⟨δ, hδ, h⟩ := exists_pos_infEDist_inter hA hB hε
  filter_upwards [(tendsto_order.1 ha).2 δ hδ, (tendsto_order.1 hb).2 δ hδ] with i hai hbi x hxa hxb
  exact h x (hxa.trans_lt hai) (hxb.trans_lt hbi)

namespace AsymptoticObject

omit [∀ i, Fintype (G i)] in
/-- **Lemma 2.2, first part:** `𝒜_A ∩ 𝒜_B = 𝒜_{A ∩ B}` (objectwise). -/
theorem isSupported_inter_iff (hA : IsClosed A) (hB : IsClosed B) (M : AsymptoticObject π X) :
    M.IsSupported A ∧ M.IsSupported B ↔ M.IsSupported (A ∩ B) := by
  refine ⟨fun ⟨hMA, hMB⟩ ↦ ENNReal.tendsto_nhds_zero.mpr fun ε hε ↦ ?_,
    fun h ↦ ⟨h.mono Set.inter_subset_left, h.mono Set.inter_subset_right⟩⟩
  filter_upwards [eventually_infEDist_inter_lt hA hB hε hMA hMB] with i hi
  exact iSup_le fun b ↦ (hi _ (infEDist_le_supportDist i b) (infEDist_le_supportDist i b)).le

omit [∀ i, Fintype (G i)] in
theorem tendsto_endpointDist_inter (hA : IsClosed A) (hB : IsClosed B)
    {M N : AsymptoticObject π X} (f : Family M N) (hfA : Tendsto (endpointDist A f) atTop (𝓝 0))
    (hfB : Tendsto (endpointDist B f) atTop (𝓝 0)) :
    Tendsto (endpointDist (A ∩ B) f) atTop (𝓝 0) := by
  refine ENNReal.tendsto_nhds_zero.mpr fun ε hε ↦ ?_
  filter_upwards [eventually_infEDist_inter_lt hA hB hε hfA hfB] with i hi
  refine endpointDist_le_iff.mpr fun c a hca ↦ ?_
  have hAi := (endpointDist_le_iff (S := A) (f := f)).mp le_rfl c a hca
  have hBi := (endpointDist_le_iff (S := B) (f := f)).mp le_rfl c a hca
  exact ⟨(hi _ hAi.1 hBi.1).le, (hi _ hAi.2 hBi.2).le⟩

end AsymptoticObject

namespace AsymptoticCategory

/-- **Lemma 2.2, first part** in (2.4): `𝒜_A ∩ 𝒜_B = 𝒜_{A ∩ B}`. -/
theorem supportProperty_inter (hA : IsClosed A) (hB : IsClosed B) :
    supportProperty (π := π) A ⊓ supportProperty B = supportProperty (A ∩ B) := by
  funext T
  exact propext (isSupported_inter_iff hA hB T.as)

variable (π) in
/-- On `𝒜_A(X)`, `φ ~ ψ` iff `φ - ψ ∈ I_Y`. -/
def subIdealRel (A Y : Set X) : HomRel (SupportCategory π A) :=
  fun _ _ φ ψ ↦ idealRel Y φ.hom ψ.hom

instance subIdealRel_congruence (A Y : Set X) : Congruence (subIdealRel π A Y) where
  equivalence := ⟨fun φ ↦ (Congruence.equivalence (r := idealRel (π := π) Y)).refl φ.hom,
    fun h ↦ (Congruence.equivalence (r := idealRel (π := π) Y)).symm h,
    fun h h' ↦ (Congruence.equivalence (r := idealRel (π := π) Y)).trans h h'⟩
  comp_left φ _ _ h := HomRel.comp_left (r := idealRel (π := π) Y) φ.hom h
  comp_right ψ h := HomRel.comp_right (r := idealRel (π := π) Y) ψ.hom h

variable (π) in
/-- The quotient `𝒜_A(X)/𝒜_Y(X)`. -/
abbrev SupportQuotient (A Y : Set X) :=
  CategoryTheory.Quotient (subIdealRel π A Y)

variable (A B) in
/-- The functor `𝒜_A/𝒜_{A ∩ B} → 𝒜(X)/𝒜_B` induced by inclusion. -/
def excisionFunctor : SupportQuotient π A (A ∩ B) ⥤ ExteriorCategory π B :=
  CategoryTheory.Quotient.lift _ ((supportProperty A).ι ⋙ ExteriorCategory.functor) fun _ _ _ _ h ↦
    (ExteriorCategory.functor_map_eq_iff _ _).mpr (InIdeal.mono Set.inter_subset_right h)

omit [PseudoEMetricSpace X] [CompactSpace X] in
theorem smul_mem_iff_of_invariant (hAinv : ∀ h : H, h • A = A) (h : H) (x : X) :
    h • x ∈ A ↔ x ∈ A := by
  conv_lhs => rw [← hAinv h]
  exact Set.smul_mem_smul_set_iff

/-- **Lemma 2.2, second part** of (2.4): for a closed cover `X = A ∪ B` with `A` invariant,
`𝒜_A/𝒜_{A ∩ B} → 𝒜(X)/𝒜_B` is an equivalence. -/
theorem excisionFunctor_isEquivalence (hA : IsClosed A) (hB : IsClosed B)
    (hAinv : ∀ h : H, h • A = A) (hcover : A ∪ B = Set.univ) :
    (excisionFunctor (π := π) A B).IsEquivalence where
  faithful := ⟨fun {P Q} φ ψ h ↦ by
    obtain ⟨φ, rfl⟩ := (CategoryTheory.Quotient.functor _).map_surjective φ
    obtain ⟨ψ, rfl⟩ := (CategoryTheory.Quotient.functor _).map_surjective ψ
    change ExteriorCategory.functor.map φ.hom = ExteriorCategory.functor.map ψ.hom at h
    rw [ExteriorCategory.functor_map_eq_iff] at h
    apply CategoryTheory.Quotient.sound
    change InIdeal (A ∩ B) (φ.hom - ψ.hom)
    obtain ⟨f, hf⟩ := exists_rep (φ.hom - ψ.hom)
    rw [← hf, inIdeal_map_iff] at h ⊢
    refine tendsto_endpointDist_inter hA hB f.1 ?_ h
    exact tendsto_zero_of_le (by simpa using Q.as.property.max P.as.property)
      (endpointDist_le_of_supported f.1)⟩
  full := ⟨fun {_ _} φ ↦ by
    obtain ⟨ψ, rfl⟩ := (ExteriorCategory.functor (Z := B)).map_surjective φ
    exact ⟨(CategoryTheory.Quotient.functor _).map (ObjectProperty.homMk ψ), rfl⟩⟩
  essSurj := ⟨fun T ↦ by
    set N := T.as.as
    let P : ∀ i, Fin (N.rank i) → Prop := fun i k ↦ N.label i k ∈ A
    have hsupp : supportProperty A (functor.obj (N.restrict P)) :=
      tendsto_zero_of_forall_eq_zero fun i ↦
      le_antisymm (iSup_le fun b ↦ (infEDist_zero_of_mem ((smul_mem_iff_of_invariant hAinv _ _).mpr
        ((N.mem_range_restrictEmb P i _).mp ⟨b.1, rfl⟩))).le) bot_le
    let E := ExteriorCategory.functor (π := π) (Z := B)
    refine ⟨⟨⟨functor.obj (N.restrict P), hsupp⟩⟩, ⟨
      { hom := E.map (functor.map (N.restrictEmb P).incl)
        inv := E.map (functor.map (N.restrictEmb P).proj)
        hom_inv_id := by
          change E.map _ ≫ E.map _ = 𝟙 (E.obj (functor.obj (N.restrict P)))
          rw [← Functor.map_comp, ← Functor.map_comp, OrbitEmbedding.incl_proj]
          rfl
        inv_hom_id := ?_ }⟩⟩
    change E.map (functor.map (N.restrictEmb P).proj) ≫ E.map (functor.map (N.restrictEmb P).incl)
      = 𝟙 T
    rw [← Functor.map_comp, ← Functor.map_comp, restrict_proj_incl]
    change E.map _ = E.map (functor.map (𝟙 N))
    rw [ExteriorCategory.functor_map_eq_iff, ← Functor.map_sub, inIdeal_map_iff]
    refine tendsto_zero_of_forall_eq_zero fun i ↦
      le_antisymm (endpointDist_le_iff.mpr fun c a hca ↦ ?_) bot_le
    have hc : c = a ∧ ¬ P i a.1 := by
      by_cases hca' : c = a
      · subst hca'
        by_cases hP : P i c.1
        · simp [hP] at hca
        · exact ⟨rfl, hP⟩
      · simp [diagonal_apply_ne _ hca', one_apply_ne hca'] at hca
    obtain ⟨rfl, hP⟩ := hc
    have hB' : N.fullLabel i c ∈ B := by
      have hx : N.fullLabel i c ∈ A ∪ B := hcover ▸ Set.mem_univ _
      refine hx.resolve_left fun hxA ↦ hP ?_
      exact (smul_mem_iff_of_invariant hAinv _ _).mp hxA
    exact ⟨(infEDist_zero_of_mem hB').le, (infEDist_zero_of_mem hB').le⟩⟩

end AsymptoticCategory

end Excision

end HSFormal
