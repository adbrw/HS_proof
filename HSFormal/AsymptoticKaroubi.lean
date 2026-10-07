import HSFormal.AsymptoticSupport

/-!
# Karoubi filtrations and Lemma 2.1

We state [CP95, Definition 1.27] for a full subcategory `𝒰` of a preadditive category: every
object carries a filtered family of splittings `A = E_α ⊕ A_α` with `E_α ∈ 𝒰`, such that maps
from (to) objects of `𝒰` factor through the inclusion of (projection to) some `E_α`, and the
families of a direct sum `A ⊕ A'` and of the sum splittings are mutually cofinal.  The order
`E_α ⊕ A_α ≤ E_β ⊕ A_β` (`E_α ⊆ E_β`, `A_β ⊆ A_α`) is `e_α e_β = e_β e_α = e_α` on idempotents.

Lemma 2.1: `𝒜_S(X) ⊂ 𝒜(X)` is a Karoubi filtration, by the splittings `E_r M ⊕ U_r M` at null
radii `r`, and these splittings are fixed by transpose duality.
-/

noncomputable section

namespace HSFormal

open Filter Matrix CategoryTheory CategoryTheory.Limits Metric
open scoped Classical ENNReal Topology

universe u

section Abstract

variable {C : Type*} [Category C] [Preadditive C]

/-- A decomposition `A = E ⊕ U`. -/
structure Splitting (A : C) where
  E : C
  U : C
  ιE : E ⟶ A
  πE : A ⟶ E
  ιU : U ⟶ A
  πU : A ⟶ U
  ιE_πE : ιE ≫ πE = 𝟙 E
  ιU_πU : ιU ≫ πU = 𝟙 U
  ιE_πU : ιE ≫ πU = 0
  ιU_πE : ιU ≫ πE = 0
  total : πE ≫ ιE + πU ≫ ιU = 𝟙 A

/-- The idempotent of `A` with image `E`. -/
def Splitting.idem {A : C} (σ : Splitting A) : A ⟶ A :=
  σ.πE ≫ σ.ιE

/-- The order on splittings: `E ⊆ E'` and `U' ⊆ U`. -/
def IdemLE {A : C} (e e' : A ⟶ A) : Prop :=
  e ≫ e' = e ∧ e' ≫ e = e

/-- [CP95, Definition 1.27]: `C` is `𝒰`-filtered, i.e. `𝒰 ⊂ C` is a Karoubi filtration. -/
structure KaroubiFiltration (𝒰 : ObjectProperty C) where
  splittings : ∀ A : C, Set (Splitting A)
  mem : ∀ A, ∀ σ ∈ splittings A, 𝒰 σ.E
  nonempty : ∀ A, (splittings A).Nonempty
  directed : ∀ A, ∀ σ ∈ splittings A, ∀ τ ∈ splittings A,
    ∃ ρ ∈ splittings A, IdemLE σ.idem ρ.idem ∧ IdemLE τ.idem ρ.idem
  factor_to : ∀ {V A : C}, 𝒰 V → ∀ f : V ⟶ A,
    ∃ σ ∈ splittings A, ∃ g : V ⟶ σ.E, f = g ≫ σ.ιE
  factor_from : ∀ {A V : C}, 𝒰 V → ∀ f : A ⟶ V,
    ∃ σ ∈ splittings A, ∃ g : σ.E ⟶ V, f = σ.πE ≫ g
  sum : ∀ {A A' : C} (b : BinaryBicone A A'), b.IsBilimit →
    (∀ σ ∈ splittings b.pt, ∃ α ∈ splittings A, ∃ β ∈ splittings A',
      IdemLE σ.idem (b.fst ≫ α.idem ≫ b.inl + b.snd ≫ β.idem ≫ b.inr)) ∧
    (∀ α ∈ splittings A, ∀ β ∈ splittings A', ∃ σ ∈ splittings b.pt,
      IdemLE (b.fst ≫ α.idem ≫ b.inl + b.snd ≫ β.idem ≫ b.inr) σ.idem)

end Abstract

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  {π : ∀ i, G i →* H} {X : Type u} [MulAction H X] [PseudoEMetricSpace X]

namespace AsymptoticObject

variable (S : Set X)

/-- The orbits at distance at most `r i` from `S`. -/
def nearPred (M : AsymptoticObject π X) (r : ℕ → ℝ≥0∞) : ∀ i, Fin (M.rank i) → Prop :=
  fun i k ↦ M.orbitDist S i k ≤ r i

variable {S}

theorem diagProj_nearPred_mono (M : AsymptoticObject π X) {r s : ℕ → ℝ≥0∞} (h : ∀ i, r i ≤ s i) :
    IdemLE (M.diagProj (M.nearPred S r)) (M.diagProj (M.nearPred S s)) :=
  M.diagProj_comp_diagProj _ _ fun i _ hk ↦ hk.trans (h i)

theorem diagProj_nearPred_supportDist (M : AsymptoticObject π X) :
    M.diagProj (M.nearPred S (M.supportDist S)) = 𝟙 M := by
  rw [← diagProj_true]
  congr
  funext i k
  simpa [nearPred] using orbitDist_le_supportDist i k

/-- Absorption: rows reached from `E_t` by `f` lie in `E_r` when `t + prop f ≤ r`. -/
theorem diagProj_comp_diagProj_of_le {M N : AsymptoticObject π X} (f : M ⟶ N)
    {t r : ℕ → ℝ≥0∞} (h : ∀ i, t i + propSeq M N f.1 i ≤ r i) :
    M.diagProj (M.nearPred S t) ≫ f ≫ N.diagProj (N.nearPred S r) =
      M.diagProj (M.nearPred S t) ≫ f := by
  refine hom_ext fun i ↦ ?_
  simp only [comp_val, diagProj_val]
  ext c a
  simp only [diagonal_mul, mul_diagonal]
  by_cases ha : M.nearPred S t i a.1
  · by_cases hca : f.1 i c a = 0
    · simp [hca]
    · have hc : N.nearPred S r i c.1 :=
        (orbitDist_target_le f i c a hca).trans ((add_le_add ha le_rfl).trans (h i))
      simp [ha, hc]
  · simp [ha]

/-- Absorption: columns reaching `E_t` through `f` lie in `E_r` when `t + prop f ≤ r`. -/
theorem diagProj_comp_diagProj_of_le' {M N : AsymptoticObject π X} (f : M ⟶ N)
    {t r : ℕ → ℝ≥0∞} (h : ∀ i, t i + propSeq M N f.1 i ≤ r i) :
    M.diagProj (M.nearPred S r) ≫ f ≫ N.diagProj (N.nearPred S t) =
      f ≫ N.diagProj (N.nearPred S t) := by
  refine hom_ext fun i ↦ ?_
  simp only [comp_val, diagProj_val]
  ext c a
  simp only [diagonal_mul, mul_diagonal]
  by_cases hc : N.nearPred S t i c.1
  · by_cases hca : f.1 i c a = 0
    · simp [hca]
    · have ha : M.nearPred S r i a.1 :=
        (orbitDist_source_le f i c a hca).trans ((add_le_add hc le_rfl).trans (h i))
      simp [ha, hc]
  · simp [hc]

omit [∀ i, Fintype (G i)] in
theorem isSupported_restrict_nearPred (M : AsymptoticObject π X) {r : ℕ → ℝ≥0∞}
    (hr : Tendsto r atTop (𝓝 0)) : (M.restrict (M.nearPred S r)).IsSupported S := by
  refine tendsto_zero_of_le hr fun i ↦ iSup_le fun b ↦ ?_
  have hb : (M.restrict (M.nearPred S r)).fullLabel i b =
      M.fullLabel i ((M.restrictEmb (M.nearPred S r)).toFun i b.1, b.2) := by
    simp [fullLabel, (M.restrictEmb _).label_toFun]
  rw [hb]
  exact (infEDist_le_orbitDist i _ b.2).trans
    ((M.mem_range_restrictEmb (M.nearPred S r) i _).mp ⟨b.1, rfl⟩)

end AsymptoticObject

open AsymptoticObject

namespace AsymptoticCategory

/-- The splitting of `functor.obj M` by a based summand and its complement. -/
def restrictSplitting (M : AsymptoticObject π X) (P : ∀ i, Fin (M.rank i) → Prop) :
    Splitting (functor.obj M) where
  E := functor.obj (M.restrict P)
  U := functor.obj (M.restrict fun i k ↦ ¬ P i k)
  ιE := functor.map (M.restrictEmb P).incl
  πE := functor.map (M.restrictEmb P).proj
  ιU := functor.map (M.restrictEmb _).incl
  πU := functor.map (M.restrictEmb _).proj
  ιE_πE := by rw [← Functor.map_comp, OrbitEmbedding.incl_proj, CategoryTheory.Functor.map_id]
  ιU_πU := by rw [← Functor.map_comp, OrbitEmbedding.incl_proj, CategoryTheory.Functor.map_id]
  ιE_πU := by rw [← Functor.map_comp, ← Functor.map_zero functor]; congr 1;
                exact (M.restrictBicone P).inl_snd
  ιU_πE := by rw [← Functor.map_comp, ← Functor.map_zero functor]; congr 1;
                exact (M.restrictBicone P).inr_fst
  total := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_add, ← CategoryTheory.Functor.map_id]
    exact congrArg _ (M.restrictBicone_total P)

theorem restrictSplitting_idem (M : AsymptoticObject π X) (P : ∀ i, Fin (M.rank i) → Prop) :
    (restrictSplitting M P).idem = functor.map (M.diagProj P) := by
  rw [Splitting.idem, restrictSplitting, ← Functor.map_comp, restrict_proj_incl]

/-- The splitting `A = E_r A ⊕ U_r A` at radius `r` from `S`. -/
def supportSplitting (S : Set X) (A : AsymptoticCategory π X) (r : ℕ → ℝ≥0∞) : Splitting A :=
  restrictSplitting A.as (A.as.nearPred S r)

variable {S : Set X}

theorem supportSplitting_idem (A : AsymptoticCategory π X) (r : ℕ → ℝ≥0∞) :
    (supportSplitting S A r).idem = functor.map (A.as.diagProj (A.as.nearPred S r)) :=
  restrictSplitting_idem _ _

/-- The splittings are fixed by transpose duality. -/
theorem supportSplitting_transpose (A : AsymptoticCategory π X) (r : ℕ → ℝ≥0∞) :
    transpose (supportSplitting S A r).ιE = (supportSplitting S A r).πE ∧
      transpose (supportSplitting S A r).ιU = (supportSplitting S A r).πU :=
  ⟨rfl, rfl⟩

theorem idem_absorb {A B : AsymptoticCategory π X} (f : A.as ⟶ B.as) {t r : ℕ → ℝ≥0∞}
    (h : ∀ i, t i + propSeq A.as B.as f.1 i ≤ r i) :
    (supportSplitting S A t).idem ≫ functor.map f ≫ (supportSplitting S B r).idem =
      (supportSplitting S A t).idem ≫ functor.map f := by
  simp only [supportSplitting_idem, ← Functor.map_comp]
  exact congrArg _ (diagProj_comp_diagProj_of_le f h)

theorem idem_absorb' {A B : AsymptoticCategory π X} (f : A.as ⟶ B.as) {t r : ℕ → ℝ≥0∞}
    (h : ∀ i, t i + propSeq A.as B.as f.1 i ≤ r i) :
    (supportSplitting S A r).idem ≫ functor.map f ≫ (supportSplitting S B t).idem =
      functor.map f ≫ (supportSplitting S B t).idem := by
  simp only [supportSplitting_idem, ← Functor.map_comp]
  exact congrArg _ (diagProj_comp_diagProj_of_le' f h)

variable (S) in
/-- **Lemma 2.1 (support filtration).** `𝒜_S(X) ⊂ 𝒜(X)` is a Karoubi filtration, with the
splittings `E_r M ⊕ U_r M` over null radii `r`. -/
def supportFiltration : KaroubiFiltration (supportProperty (π := π) S) where
  splittings A := {σ | ∃ r, Tendsto r atTop (𝓝 0) ∧ σ = supportSplitting S A r}
  mem := by
    rintro A _ ⟨r, hr, rfl⟩
    exact A.as.isSupported_restrict_nearPred hr
  nonempty A := ⟨_, 0, tendsto_const_nhds, rfl⟩
  directed := by
    rintro A _ ⟨r, hr, rfl⟩ _ ⟨s, hs, rfl⟩
    refine ⟨_, ⟨r ⊔ s, by simpa [Pi.sup_def] using hr.max hs, rfl⟩, ?_, ?_⟩ <;>
      simp only [supportSplitting_idem, IdemLE, ← Functor.map_comp]
    · exact ⟨congrArg _ (A.as.diagProj_nearPred_mono fun i ↦ le_sup_left).1,
        congrArg _ (A.as.diagProj_nearPred_mono fun i ↦ le_sup_left).2⟩
    · exact ⟨congrArg _ (A.as.diagProj_nearPred_mono fun i ↦ le_sup_right).1,
        congrArg _ (A.as.diagProj_nearPred_mono fun i ↦ le_sup_right).2⟩
  factor_to := by
    intro V A hV φ
    obtain ⟨f, rfl⟩ := exists_rep φ
    set r := fun i ↦ V.as.supportDist S i + propSeq V.as A.as f.1 i
    refine ⟨_, ⟨r, by simpa using hV.add (tendsto_propSeq f), rfl⟩,
      functor.map (f ≫ (A.as.restrictEmb _).proj), ?_⟩
    have h : f ≫ A.as.diagProj (A.as.nearPred S r) = f := by
      have := diagProj_comp_diagProj_of_le (S := S) f (t := V.as.supportDist S) (r := r)
        fun i ↦ le_rfl
      simpa only [diagProj_nearPred_supportDist, Category.id_comp] using this
    change functor.map f = functor.map _ ≫ functor.map (A.as.restrictEmb _).incl
    rw [← Functor.map_comp, Category.assoc, restrict_proj_incl, h]
  factor_from := by
    intro A V hV φ
    obtain ⟨f, rfl⟩ := exists_rep φ
    set r := fun i ↦ V.as.supportDist S i + propSeq A.as V.as f.1 i
    refine ⟨_, ⟨r, by simpa using hV.add (tendsto_propSeq f), rfl⟩,
      functor.map ((A.as.restrictEmb _).incl ≫ f), ?_⟩
    have h : A.as.diagProj (A.as.nearPred S r) ≫ f = f := by
      have := diagProj_comp_diagProj_of_le' (S := S) f (t := V.as.supportDist S) (r := r)
        fun i ↦ le_rfl
      simpa only [diagProj_nearPred_supportDist, Category.comp_id] using this
    change functor.map f = functor.map (A.as.restrictEmb _).proj ≫ functor.map _
    rw [← Functor.map_comp, ← Category.assoc, restrict_proj_incl, h]
  sum := by
    intro A A' b hb
    have htot := IsBilimit.binary_total hb
    obtain ⟨fst, hfst⟩ := exists_rep b.fst
    obtain ⟨snd, hsnd⟩ := exists_rep b.snd
    obtain ⟨inl, hinl⟩ := exists_rep b.inl
    obtain ⟨inr, hinr⟩ := exists_rep b.inr
    set ε : ℕ → ℝ≥0∞ := fun i ↦ max (max (propSeq _ _ fst.1 i) (propSeq _ _ snd.1 i))
      (max (propSeq _ _ inl.1 i) (propSeq _ _ inr.1 i))
    have hε : Tendsto ε atTop (𝓝 0) := by
      simpa using ((tendsto_propSeq fst).max (tendsto_propSeq snd)).max
        ((tendsto_propSeq inl).max (tendsto_propSeq inr))
    have h1 : ∀ i, propSeq _ _ fst.1 i ≤ ε i := fun i ↦ le_max_left _ _ |>.trans (le_max_left _ _)
    have h2 : ∀ i, propSeq _ _ snd.1 i ≤ ε i := fun i ↦ le_max_right _ _ |>.trans (le_max_left _ _)
    have h3 : ∀ i, propSeq _ _ inl.1 i ≤ ε i := fun i ↦ le_max_left _ _ |>.trans (le_max_right _ _)
    have h4 : ∀ i, propSeq _ _ inr.1 i ≤ ε i := fun i ↦ le_max_right _ _ |>.trans (le_max_right _ _)
    constructor
    · rintro _ ⟨t, ht, rfl⟩
      have hr : Tendsto (t + ε) atTop (𝓝 0) := by simpa [Pi.add_def] using ht.add hε
      refine ⟨_, ⟨t + ε, hr, rfl⟩, _, ⟨t + ε, hr, rfl⟩, ?_, ?_⟩
      · have ha := idem_absorb (S := S) (A := b.pt) (B := A) fst (t := t) (r := t + ε)
          fun i ↦ add_le_add le_rfl (h1 i)
        have hb' := idem_absorb (S := S) (A := b.pt) (B := A') snd (t := t) (r := t + ε)
          fun i ↦ add_le_add le_rfl (h2 i)
        rw [hfst] at ha
        rw [hsnd] at hb'
        rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc, ← Category.assoc,
          ← Category.assoc, Category.assoc _ b.fst, Category.assoc _ b.snd, ha, hb',
          Category.assoc, Category.assoc, ← Preadditive.comp_add, htot, Category.comp_id]
      · have ha := idem_absorb' (S := S) (A := A) (B := b.pt) inl (t := t) (r := t + ε)
          fun i ↦ add_le_add le_rfl (h3 i)
        have hb' := idem_absorb' (S := S) (A := A') (B := b.pt) inr (t := t) (r := t + ε)
          fun i ↦ add_le_add le_rfl (h4 i)
        rw [hinl] at ha
        rw [hinr] at hb'
        rw [Preadditive.add_comp, Category.assoc, Category.assoc, Category.assoc,
          Category.assoc, ha, hb', ← Category.assoc, ← Category.assoc, ← Preadditive.add_comp,
          htot, Category.id_comp]
    · rintro _ ⟨r, hr, rfl⟩ _ ⟨r', hr', rfl⟩
      have hs : Tendsto ((r ⊔ r') + ε) atTop (𝓝 0) := by
        simpa [Pi.add_def, Pi.sup_def] using (hr.max hr').add hε
      refine ⟨_, ⟨(r ⊔ r') + ε, hs, rfl⟩, ?_, ?_⟩
      · have ha := idem_absorb (S := S) (A := A) (B := b.pt) inl (t := r) (r := (r ⊔ r') + ε)
          fun i ↦ add_le_add le_sup_left (h3 i)
        have hb' := idem_absorb (S := S) (A := A') (B := b.pt) inr (t := r') (r := (r ⊔ r') + ε)
          fun i ↦ add_le_add le_sup_right (h4 i)
        rw [hinl] at ha
        rw [hinr] at hb'
        rw [Preadditive.add_comp, Category.assoc, Category.assoc, Category.assoc,
          Category.assoc, ha, hb']
      · have ha := idem_absorb' (S := S) (A := b.pt) (B := A) fst (t := r) (r := (r ⊔ r') + ε)
          fun i ↦ add_le_add le_sup_left (h1 i)
        have hb' := idem_absorb' (S := S) (A := b.pt) (B := A') snd (t := r') (r := (r ⊔ r') + ε)
          fun i ↦ add_le_add le_sup_right (h2 i)
        rw [hfst] at ha
        rw [hsnd] at hb'
        rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc, ← Category.assoc,
          ← Category.assoc, ← Category.assoc, ← Category.assoc, Category.assoc _ b.fst,
          Category.assoc _ b.snd, ha, hb']

/-- **Lemma 2.1, duality:** the filtration is fixed by transpose duality. -/
theorem supportFiltration_transpose (A : AsymptoticCategory π X) :
    ∀ σ ∈ (supportFiltration (π := π) S).splittings A,
      transpose σ.ιE = σ.πE ∧ transpose σ.ιU = σ.πU := by
  rintro _ ⟨r, -, rfl⟩
  exact supportSplitting_transpose A r

end AsymptoticCategory

end HSFormal
