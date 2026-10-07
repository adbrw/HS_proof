import HSFormal.Cubical.CutSupport
import HSFormal.LTheory.Theorem63

/-!
# The L-class equations of a cut (cubical module C8, the step of Lemma 11.2)

For a cut `K : SeqCut X` of a controlled Poincaré complex `(W, ψ)` the A-pair (`SeqCut.toSymPair`)
is mapped to `𝒜(X)` (`SeqCut.Xamb`) and the excision isometry R3 is checked on the realized
matrices: the complement `1 - t i` of the A-side and the cap defect `i (cutTop ψ W_A) i^* - ψ` are
carried by the cells off `W_A` (and their `ψ`-neighbours), hence lie in `I_S` as soon as those
cells are labelled near `S` (`SeqCut.r3_hc`, `SeqCut.r3_hcap`).
-/

noncomputable section

namespace HSFormal.Cubical

open Filter Matrix CategoryTheory CategoryTheory.Limits HSFormal.LTheory HSFormal.Compression
  Metric AsymptoticCategory AsymptoticObject
open scoped ENNReal Topology Pointwise

namespace BasedComplex

open ControlledSeq

namespace SeqCut

variable {X : Type} [PseudoEMetricSpace X] (K : SeqCut X)
  {H : Type} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  (π : ∀ i, G i →* H) [MulAction H X] [IsIsometricSMul H X]

/-- The realized inclusion `W_A → W` in `𝒜(X)`. -/
abbrev iAmb : (asymptoticQuotInv π X).mapC (K.WA.toComplex π) ⟶
    (asymptoticQuotInv π X).mapC (K.W.toComplex π) :=
  (asymptoticQuotInv π X).mapH ((K.W.inclSeq K.hA).toComplex π)

/-- Its degreewise retraction. -/
abbrev tAmb (r : ℤ) : AsymptoticCategory.functor.obj (K.W.obj π r) ⟶
    AsymptoticCategory.functor.obj (K.WA.obj π r) :=
  AsymptoticCategory.functor.map ((K.W.splitSeq π K.hA).t r)

theorem r3_ht (r : ℤ) : (K.iAmb π).f r ≫ K.tAmb π r = 𝟙 _ := by
  change AsymptoticCategory.functor.map _ ≫ AsymptoticCategory.functor.map _ = _
  rw [← CategoryTheory.Functor.map_comp, (K.W.splitSeq π K.hA).it, CategoryTheory.Functor.map_id]
  rfl

/-- The complement `1 - t i` is the realized projection onto the cells off `W_A`. -/
theorem r3_hc {S : Set X} (hS : ∀ h : H, h • S = S) (hc : K.WnA.LabelsNear S) (r : ℤ) :
    InIdeal S (𝟙 _ - K.tAmb π r ≫ (K.iAmb π).f r) := by
  have e : 𝟙 _ - K.tAmb π r ≫ (K.iAmb π).f r = AsymptoticCategory.functor.map
      (((K.W.projSeq K.hA).toComplex π).f r ≫ (K.W.splitSeq π K.hA).s r) := by
    have := (K.W.splitSeq π K.hA).total r
    change _ = AsymptoticCategory.functor.map _
    rw [← sub_eq_of_eq_add' this.symm, CategoryTheory.Functor.map_sub,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_comp]
    rfl
  rw [e, Hom.toComplex_f]
  change InIdeal S (AsymptoticCategory.functor.map (hom (A := K.W) (B := K.WnA) π _ _ r r ≫
    hom (A := K.WnA) (B := K.W) π (fun i ↦ (projHom (K.hA i)).fᵀ)
      (K.W.projSeq_transpose_tendsto K.hA) r r))
  erw [hom_comp (A := K.W) (B := K.WnA) (B' := K.W) _ _ _ _ fun i κ σ h hσ ↦ by
    exact ((projHom (K.hA i)).deg0 κ σ h).trans ((add_zero _).trans hσ)]
  refine inIdeal_hom π _ _ r r hS (tendsto_zero_of_le hc fun i ↦ iSup_le fun κ ↦ iSup_le fun σ ↦
    iSup_le fun h ↦ ?_)
  change ((projHom (K.hA i)).fᵀ * (projHom (K.hA i)).f) κ σ ≠ 0 at h
  rw [projHom_transpose_mul_apply] at h
  by_cases hκ : K.SA i κ
  · rw [dif_neg (not_not.mpr hκ)] at h
    exact absurd rfl h
  · rw [dif_pos hκ] at h
    have hκσ : κ = σ := by
      by_contra hne
      exact h (by simp [projHom, hne])
    subst hκσ
    rw [max_self]
    exact le_iSup_of_le (⟨κ, hκ⟩ : (K.WnA.C i).X) le_rfl

/-- The A-pair in `𝒜(X)`. -/
abbrev Xamb (hψ : IsKarEquiv (𝟙 _) (𝟙 _) (dualityMap π K.hW K.ψ))
    (hR : IsKarEquiv (𝟙 _) (𝟙 _) (dualityMap π K.hWB K.ladderR)) :
    SymPair (asymptoticInvCat π X).inv K.N :=
  (K.toSymPair π hψ hR).map (asymptoticQuotInv π X)

/-- The closed complex `(W, ψ)` in `𝒜(X)`. -/
abbrev Wamb (hψ : IsKarEquiv (𝟙 _) (𝟙 _) (dualityMap π K.hW K.ψ)) :
    SymPoincare (asymptoticInvCat π X).inv ((K.N : ℤ) + 1) :=
  (symPoincareOf π K.hW K.ψ K.hψ hψ).map (asymptoticQuotInv π X)

/-- The realized inclusion `W_A → W` from the A-pair to the closed complex. -/
abbrev iX (hψ : IsKarEquiv (𝟙 _) (𝟙 _) (dualityMap π K.hW K.ψ))
    (hR : IsKarEquiv (𝟙 _) (𝟙 _) (dualityMap π K.hWB K.ladderR)) :
    (K.Xamb π hψ hR).D ⟶ (K.Wamb π hψ).C := K.iAmb π

/-- `ψ` as a square matrix. -/
abbrev psiM (i : ℕ) : Matrix (K.W.C i).X (K.W.C i).X ℚ := (K.ψ.f i).f

theorem hom_sub {A B : ControlledSeq X} (u v : ∀ i, Matrix (B.C i).X (A.C i).X ℚ) (hu hv)
    (r r' : ℤ) : hom π (fun i ↦ u i - v i) (hu.sub hv) r r' = hom π u hu r r' - hom π v hv r r' := by
  rw [sub_eq_add_neg, ← neg_one_smul ℚ (hom π v hv r r'), smul_hom, ← hom_add]
  exact hom_congr (funext fun i ↦ by simp [sub_eq_add_neg]) _ _ _ _

/-- The cap defect `i T i^* - ψ` of the A-side on all cells. -/
theorem capDefect_apply (i : ℕ) (κ σ : (K.W.C i).X) :
    ((inclHom (K.hA i)).f * (cutTop (K.hW i) (K.ψ.f i) (K.SA i) *
        ((1 : Matrix {σ // K.SA i σ} {σ // K.SA i σ} ℚ) * (inclHom (K.hA i)).fᵀ)) -
        K.psiM i) κ σ =
      if K.SA i κ ∧ K.SA i σ then 0 else -K.psiM i κ σ := by
  rw [Matrix.one_mul, Matrix.sub_apply, inclHom_mul_apply]
  by_cases hκ : K.SA i κ
  · rw [dif_pos hκ, mul_inclHom_transpose_apply]
    by_cases hσ : K.SA i σ
    · rw [dif_pos hσ, if_pos ⟨hκ, hσ⟩]; simp [cutTop]
    · rw [dif_neg hσ, if_neg fun h ↦ hσ h.2]; ring
  · rw [dif_neg hκ, if_neg fun h ↦ hκ h.1]; ring

attribute [local implicit_reducible] ControlledSeq.restrict ControlledSeq.inclSeq in
/-- **The cap defect lies in `I_S`** when the cells off `W_A` are labelled near `S`. -/
theorem r3_hcap (hψ : IsKarEquiv (𝟙 _) (𝟙 _) (dualityMap π K.hW K.ψ))
    (hR : IsKarEquiv (𝟙 _) (𝟙 _) (dualityMap π K.hWB K.ladderR)) {S : Set X}
    (hS : ∀ h : H, h • S = S) (hc : K.WnA.LabelsNear S) (r : ℤ) :
    InIdeal S ((dualHom (asymptoticInvCat π X).inv ((K.N : ℤ) + 1) (K.iX π hψ hR)).f r ≫
      (K.Xamb π hψ hR).top r ≫ (K.iX π hψ hR).f r - (K.Wamb π hψ).φ.f r) := by
  have e₁ : (dualHom (asymptoticInvCat π X).inv ((K.N : ℤ) + 1) (K.iX π hψ hR)).f r =
      AsymptoticCategory.functor.map (hom (A := K.W) (B := K.WA) π
        (fun i ↦ (inclHom (K.hA i)).fᵀ) (K.W.inclSeq_transpose_tendsto K.hA)
        ((K.N : ℤ) + 1 - r) ((K.N : ℤ) + 1 - r)) := by
    change AsymptoticCategory.functor.map (AsymptoticObject.transpose
      (((K.W.inclSeq K.hA).toComplex π).f ((K.N : ℤ) + 1 - r))) = _
    rw [Hom.toComplex_f, transpose_hom]
    rfl
  have e₂ : (K.Wamb π hψ).φ.f r = AsymptoticCategory.functor.map (hom (A := K.W) (B := K.W) π
      (fun i ↦ K.psiM i) K.ψ.tendsto ((K.N : ℤ) + 1 - r) r) := by
    change AsymptoticCategory.functor.map ((dualityMap π K.hW K.ψ).f r) = _
    rw [dualityMap_f]
    rfl
  have e₃ : (K.Xamb π hψ hR).top r = AsymptoticCategory.functor.map
      (hom (A := K.WA) (B := K.WA) π (fun i ↦ cutTop (K.hW i) (K.ψ.f i) (K.SA i) *
        (1 : Matrix {σ // K.SA i σ} {σ // K.SA i σ} ℚ)) (K.Apair.T_tendsto.mul PropTendsto.one)
        ((K.N : ℤ) + 1 - r) r) := by
    rw [SymPair.map_top]
    change AsymptoticCategory.functor.map (relTop (K.Apair.δφ π) r) = _
    simp only [relTop, HomologicalComplex.XIsoOfEq, eqToIso.hom,
      eqToHom_toComplex_X K.Apair.D (show (K.N : ℤ) + 1 - r = K.N - (r - 1) by ring),
      SeqPair.δφ_hom, SeqPair.topHom]
    change AsymptoticCategory.functor.map (hom (A := K.Apair.D) (B := K.Apair.D) π (fun _ ↦ 1)
      PropTendsto.one ((K.N : ℤ) + 1 - r) ((K.N : ℤ) - (r - 1)) ≫
      hom (A := K.Apair.D) (B := K.Apair.D) π K.Apair.T K.Apair.T_tendsto ((K.N : ℤ) - (r - 1))
        r) = _
    rw [hom_comp (A := K.Apair.D) (B := K.Apair.D) (B' := K.Apair.D) _ _ _ _ fun i κ σ h hσ ↦ by
      obtain rfl := eq_of_one_ne_zero h; omega]
    rfl
  have e₄ : (K.iX π hψ hR).f r = AsymptoticCategory.functor.map
      (hom (A := K.WA) (B := K.W) π (fun i ↦ (inclHom (K.hA i)).f) (K.W.inclSeq K.hA).tendsto
        r r) := rfl
  haveI := AsymptoticCategory.functor_additive (π := π) (X := X)
  have hψt : PropTendsto (fun i ↦ K.psiM i) K.W.label K.W.label := K.ψ.tendsto
  suffices H : InIdeal S (AsymptoticCategory.functor.map (hom (A := K.W) (B := K.WA) π
        (fun i ↦ (inclHom (K.hA i)).fᵀ) (K.W.inclSeq_transpose_tendsto K.hA)
        ((K.N : ℤ) + 1 - r) ((K.N : ℤ) + 1 - r)) ≫
      AsymptoticCategory.functor.map (hom (A := K.WA) (B := K.WA) π
        (fun i ↦ cutTop (K.hW i) (K.ψ.f i) (K.SA i) *
          (1 : Matrix {σ // K.SA i σ} {σ // K.SA i σ} ℚ))
        (K.Apair.T_tendsto.mul PropTendsto.one) ((K.N : ℤ) + 1 - r) r) ≫
      AsymptoticCategory.functor.map (hom (A := K.WA) (B := K.W) π
        (fun i ↦ (inclHom (K.hA i)).f) (K.W.inclSeq K.hA).tendsto r r) -
      AsymptoticCategory.functor.map (hom (A := K.W) (B := K.W) π
        (fun i ↦ K.psiM i) hψt ((K.N : ℤ) + 1 - r) r)) by
    exact (congrArg (InIdeal S)
      (congrArg₂ (· - ·) (congrArg₂ (· ≫ ·) e₁ (congrArg₂ (· ≫ ·) e₃ e₄)) e₂)).mpr H
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_sub,
    hom_comp (A := K.WA) (B := K.WA) (B' := K.W) _ _ _ _ fun i κ σ h hσ ↦ by
      have h' := K.Apair.T_deg i κ σ
        (by simpa using h : cutTop (K.hW i) (K.ψ.f i) (K.SA i) κ σ ≠ 0)
      change ((K.W.C i).deg κ.1 : ℤ) = r
      change ((K.W.C i).deg σ.1 : ℤ) = (K.N : ℤ) + 1 - r at hσ
      change (K.W.C i).deg κ.1 + (K.W.C i).deg σ.1 = K.N + 1 at h'
      omega,
    hom_comp (A := K.W) (B := K.WA) (B' := K.W) _ _ _ _ fun i κ σ h hσ ↦
      ((inclHom (K.hA i)).deg0.transpose0 κ σ h).trans ((add_zero _).trans hσ),
    ← hom_sub]
  refine inIdeal_hom π _ _ _ _ hS (tendsto_zero_of_le (by simpa using hc.add K.ψ.tendsto)
    fun i ↦ iSup_le fun κ ↦ iSup_le fun σ ↦ iSup_le fun h ↦ ?_)
  have hM : ((inclHom (K.hA i)).f * (cutTop (K.hW i) (K.ψ.f i) (K.SA i) *
      ((1 : Matrix {σ // K.SA i σ} {σ // K.SA i σ} ℚ) * (inclHom (K.hA i)).fᵀ)) - K.psiM i) κ σ ≠ 0 := by
    simpa [Matrix.mul_assoc] using h
  rw [capDefect_apply] at hM
  split_ifs at hM with hκσ
  · exact absurd rfl hM
  have hψ0 : (K.ψ.f i).f κ σ ≠ 0 := fun h0 ↦ hM (by simp [psiM, h0])
  have hp := edist_le_prop (source := K.W.label i) (target := K.W.label i) hψ0
  set c := ⨆ τ, infEDist (K.WnA.label i τ) S
  set p := prop (K.ψ.f i).f ((K.W.dual (K.N + 1) K.hW).label i) (K.W.label i)
  have hp' : edist (K.W.label i κ) (K.W.label i σ) ≤ p := hp
  rcases not_and_or.mp hκσ with hκ | hσ
  · have h₁ : infEDist (K.W.label i κ) S ≤ c := le_iSup_of_le (⟨κ, hκ⟩ : (K.WnA.C i).X) le_rfl
    refine max_le (h₁.trans le_self_add) ?_
    calc infEDist (K.W.label i σ) S ≤ infEDist (K.W.label i κ) S + edist (K.W.label i σ)
          (K.W.label i κ) := infEDist_le_infEDist_add_edist
      _ ≤ c + p := add_le_add h₁ (by rw [edist_comm]; exact hp')
  · have h₁ : infEDist (K.W.label i σ) S ≤ c := le_iSup_of_le (⟨σ, hσ⟩ : (K.WnA.C i).X) le_rfl
    refine max_le ?_ (h₁.trans le_self_add)
    calc infEDist (K.W.label i κ) S ≤ infEDist (K.W.label i σ) S + edist (K.W.label i κ)
          (K.W.label i σ) := infEDist_le_infEDist_add_edist
      _ ≤ c + p := add_le_add h₁ hp'

/-! ### The Mayer–Vietoris step -/

/-- Realized objects of a sequence labelled near `S` lie in `𝒜_S`. -/
theorem supp_mapC {A : ControlledSeq X} {S : Set X} (hS : IsClosedInv H S)
    (hA : A.LabelsNear S) (r : ℤ) :
    (supportKaroubiFiltration π S).U (((asymptoticQuotInv π X).mapC (A.toComplex π)).X r) :=
  supportProperty_obj π hS.2 hA r

theorem _root_.HSFormal.LTheory.SymPoincare.lift_neg {A : InvCat} {U : ObjectProperty A}
    [IsAdditiveSub U] {N : ℤ} (P : SymPoincare A.inv N) (h : ∀ r, U (P.C.X r)) :
    P.neg.lift h = (P.lift h).neg := rfl

variable [CompactSpace X] (𝕃 : LowerLTheory)

/-- **The Mayer–Vietoris step of Lemma 11.2** for a cut `K` of a controlled Poincaré complex
`(W, ψ)` supported near `Y'` along the cover `Y' ⊆ a ∪ b`: the hemisphere boundary of `[W]` is
`-bsign` times the class of the next complex `L` (the boundary of the B-side, `bd_isometric`). -/
theorem mvStep (hψ : IsKarEquiv (𝟙 _) (𝟙 _) (dualityMap π K.hW K.ψ))
    (hR : IsKarEquiv (𝟙 _) (𝟙 _) (dualityMap π K.hWB K.ladderR))
    {a b Y Y' : Set X} (ha : IsClosedInv H a) (hb : IsClosedInv H b) (hY : IsClosedInv H Y)
    (hY' : IsClosedInv H Y') (hsucc : Y' ⊆ a ∪ b) (hinter : a ∩ b ⊆ Y)
    (hW : K.W.LabelsNear Y') (hWA : K.WA.LabelsNear a) (hBd : K.Apair.Bd.LabelsNear (a ∩ b))
    (hWnA : K.WnA.LabelsNear b)
    {L : ControlledSeq X} {hL : L.DimLE K.N} {ψL : ControlledSeq.Hom (L.dual K.N hL) L}
    (hψL : ControlledSeq.IsSymm hL ψL) (hPL : IsKarEquiv (𝟙 _) (𝟙 _) (dualityMap π hL ψL))
    (e : ∀ i, CellIso (K.Sig.C i) (L.C i))
    (hl : ∀ i σ, L.label i ((e i).toEquiv σ) = K.W.label i σ.1)
    (hmatch : ∀ i σ τ, (ψL.f i).f ((e i).toEquiv σ) ((e i).toEquiv τ) = (K.bdB i).f σ τ)
    (hLY : L.LabelsNear Y) :
    𝕃.map (supportIncl hinter) K.N (mvBdry41 π 𝕃 ha hb K.N
      (𝕃.map (supportIncl hsucc) ((K.N : ℤ) + 1) (𝕃.cls _ ((K.N : ℤ) + 1)
        (Lconc.cls ((K.Wamb π hψ).lift (supp_mapC π hY' hW)))))) =
      (-𝕃.bsign K.N) • 𝕃.cls _ K.N (Lconc.cls
        (((symPoincareOf π hL ψL hψL hPL).map (asymptoticQuotInv π X)).lift
          (supp_mapC π hY hLY))) := by
  have hp : (K.Xamb π hψ hR).bd.p = 𝟙 _ := by
    change (asymptoticQuotInv π X).mapH (𝟙 _) = _
    exact CategoryTheory.Functor.map_id _ _
  have hpD : (K.Xamb π hψ hR).pD = 𝟙 _ := by
    change (asymptoticQuotInv π X).mapH (𝟙 _) = _
    exact CategoryTheory.Functor.map_id _ _
  have hC : ∀ r, (supportKaroubiFiltration π a).U ((K.Xamb π hψ hR).bd.C.X r) := fun r ↦
    supp_mapC π ha (hBd.mono Set.inter_subset_left) r
  have hD : ∀ r, (supportKaroubiFiltration π a).U ((K.Xamb π hψ hR).D.X r) := fun r ↦
    supp_mapC π ha hWA r
  have hYV : ∀ r, (supportRestrictFiltration π (a ∩ b) a).U
      (((K.Xamb π hψ hR).liftSub hp hpD hC hD).bd.C.X r) := fun r ↦
    supp_mapC π (ha.inter hb) hBd r
  have hP := SymPair.isometric_toQuot_liftSub_sub (K.Xamb π hψ hR) hp hpD hC hD
    (U₂ := (supportKaroubiFiltration π (a ∪ b)).U) (U₃ := (supportKaroubiFiltration π Y').U)
    (fun _ h ↦ IsSupported.mono Set.subset_union_left h) (fun _ h ↦ IsSupported.mono hsucc h)
    (supportKaroubiFiltration π b) (fun _ h ↦ IsSupported.mono Set.subset_union_right h)
    (fun r ↦ (excisionHom π a b).map_mem _ (hYV r)) (K.Wamb π hψ) (supp_mapC π hY' hW)
    (K.iX π hψ hR) (by
      change (asymptoticQuotInv π X).mapH (𝟙 _) = _; exact CategoryTheory.Functor.map_id _ _) (K.tAmb π) (K.r3_ht π) (K.r3_hc π hb.2 hWnA)
    (K.r3_hcap π hψ hR hb.2 hWnA)
  have hcls := mvSystem_bdry_cls (π := π) 𝕃 ⟨a, ha⟩ ⟨b, hb⟩
    ((K.Xamb π hψ hR).liftSub hp hpD hC hD) hYV _ hP
  have hbd := K.bd_isometric π hψ hR hψL hPL e hl hmatch
  have hbd' : SymPoincare.Isometric (K.Xamb π hψ hR).bd
      ((symPoincareOf π hL ψL hψL hPL).map (asymptoticQuotInv π X)).neg := by
    have h2 : SymPoincare.Isometric ((K.toSymPair π hψ hR).bd.map (asymptoticQuotInv π X))
        ((symPoincareOf π hL ψL hψL hPL).neg.map (asymptoticQuotInv π X)) :=
      ⟨hbd.some.map _⟩
    rw [SymPoincare.map_neg] at h2
    exact h2
  have hYY : ∀ r, (supportKaroubiFiltration π Y).U ((K.Xamb π hψ hR).bd.C.X r) := fun r ↦
    supp_mapC π hY (hBd.mono hinter) r
  have hlift : Lconc.cls (A := (supportKaroubiFiltration π Y).sub) (N := K.N)
      ((K.Xamb π hψ hR).bd.lift hYY) = -Lconc.cls (A := (supportKaroubiFiltration π Y).sub)
      (((symPoincareOf π hL ψL hψL hPL).map (asymptoticQuotInv π X)).lift
        (supp_mapC π hY hLY)) := by
    rw [← Lconc.cls_neg]
    exact Lconc.cls_eq_of_isometric (hbd'.lift _ _)
  rw [← 𝕃.cls_map, Lconc.map_cls]
  change 𝕃.map (supportIncl hinter) K.N ((mvSystem π 𝕃).bdry ⟨a, ha⟩ ⟨b, hb⟩ K.N _) = _
  refine (congrArg (𝕃.map (supportIncl hinter) K.N) hcls).trans ?_
  rw [Units.smul_def, map_zsmul, ← 𝕃.cls_map, Lconc.map_cls]
  change 𝕃.bsign K.N • 𝕃.cls (supportKaroubiFiltration π Y).sub K.N
    (Lconc.cls (A := (supportKaroubiFiltration π Y).sub) ((K.Xamb π hψ hR).bd.lift hYY)) = _
  rw [hlift, map_neg, Units.smul_def, Units.smul_def, Units.val_neg, neg_smul, smul_neg]

/-- **The exterior step of Lemma 11.2** (the cut (4.2) of `X = A ∪ B`, `Z ⊆ A`, `Z ∩ B = ∅`): the
exterior cut of the class of `(W, ψ)` in `ℬ_Z` is `-bsign` times the class of `L` (the boundary of
the B-side, `bd_isometric`). -/
theorem extStep (hψ : IsKarEquiv (𝟙 _) (𝟙 _) (dualityMap π K.hW K.ψ))
    (hR : IsKarEquiv (𝟙 _) (𝟙 _) (dualityMap π K.hWB K.ladderR))
    {A B Z Y : Set X} (hA : IsClosedInv H A) (hB : IsClosedInv H B) (hZ : IsClosedInv H Z)
    (hY : IsClosedInv H Y) (hcover : A ∪ B = Set.univ) (hZA : Z ⊆ A) (hZB : Disjoint Z B)
    (htop : A ∩ B ⊆ Y)
    (hWA : K.WA.LabelsNear A) (hBd : K.Apair.Bd.LabelsNear (A ∩ B)) (hWnA : K.WnA.LabelsNear B)
    {L : ControlledSeq X} {hL : L.DimLE K.N} {ψL : ControlledSeq.Hom (L.dual K.N hL) L}
    (hψL : ControlledSeq.IsSymm hL ψL) (hPL : IsKarEquiv (𝟙 _) (𝟙 _) (dualityMap π hL ψL))
    (e : ∀ i, CellIso (K.Sig.C i) (L.C i))
    (hl : ∀ i σ, L.label i ((e i).toEquiv σ) = K.W.label i σ.1)
    (hmatch : ∀ i σ τ, (ψL.f i).f ((e i).toEquiv σ) ((e i).toEquiv τ) = (K.bdB i).f σ τ)
    (hLY : L.LabelsNear Y) :
    𝕃.map (supportIncl htop) K.N (cutBdry 𝕃 hA hB hZ hcover hZA hZB K.N
      (𝕃.cls _ ((K.N : ℤ) + 1)
        (Lconc.cls ((K.Wamb π hψ).map (supportKaroubiFiltration π Z).proj)))) =
      (-𝕃.bsign K.N) • 𝕃.cls _ K.N (Lconc.cls
        (((symPoincareOf π hL ψL hψL hPL).map (asymptoticQuotInv π X)).lift
          (supp_mapC π hY hLY))) := by
  have hp : (K.Xamb π hψ hR).bd.p = 𝟙 _ := by
    change (asymptoticQuotInv π X).mapH (𝟙 _) = _
    exact CategoryTheory.Functor.map_id _ _
  have hpD : (K.Xamb π hψ hR).pD = 𝟙 _ := by
    change (asymptoticQuotInv π X).mapH (𝟙 _) = _
    exact CategoryTheory.Functor.map_id _ _
  have hC : ∀ r, (supportKaroubiFiltration π A).U ((K.Xamb π hψ hR).bd.C.X r) := fun r ↦
    supp_mapC π hA (hBd.mono Set.inter_subset_left) r
  have hD : ∀ r, (supportKaroubiFiltration π A).U ((K.Xamb π hψ hR).D.X r) := fun r ↦
    supp_mapC π hA hWA r
  have hYV : ∀ r, (supportRestrictFiltration π (A ∩ B) A).U
      (((K.Xamb π hψ hR).liftSub hp hpD hC hD).bd.C.X r) := fun r ↦
    supp_mapC π (hA.inter hB) hBd r
  have hBZ : IsClosedInv H (B ∪ Z) := hB.union hZ
  have hQ := SymPair.isometric_toQuot_liftSub (K.Xamb π hψ hR) hp hpD hC hD
    (supportKaroubiFiltration π (B ∪ Z))
    (fun r ↦ IsSupported.mono (Set.inter_subset_right.trans Set.subset_union_left) (hYV r))
    (K.Wamb π hψ) (K.iX π hψ hR) (by
      change (asymptoticQuotInv π X).mapH (𝟙 _) = _; exact CategoryTheory.Functor.map_id _ _) (K.tAmb π) (K.r3_ht π)
    (K.r3_hc π hBZ.2 (hWnA.mono Set.subset_union_left))
    (K.r3_hcap π hψ hR hBZ.2 (hWnA.mono Set.subset_union_left))
  have hWZ : (K.Wamb π hψ).map (supportKaroubiFiltration π (B ∪ Z)).proj =
      ((K.Wamb π hψ).map (supportKaroubiFiltration π Z).proj).map
        (supportFiltrationHom (π := π) (Set.subset_union_right : Z ⊆ B ∪ Z)).quot := rfl
  rw [hWZ] at hQ
  have hcls := cutBdry_cls (π := π) 𝕃 hA hB hZ hcover hZA hZB
    ((K.Xamb π hψ hR).liftSub hp hpD hC hD) hYV _ hQ
  have hbd := K.bd_isometric π hψ hR hψL hPL e hl hmatch
  have hbd' : SymPoincare.Isometric (K.Xamb π hψ hR).bd
      ((symPoincareOf π hL ψL hψL hPL).map (asymptoticQuotInv π X)).neg := by
    have h2 : SymPoincare.Isometric ((K.toSymPair π hψ hR).bd.map (asymptoticQuotInv π X))
        ((symPoincareOf π hL ψL hψL hPL).neg.map (asymptoticQuotInv π X)) :=
      ⟨hbd.some.map _⟩
    rw [SymPoincare.map_neg] at h2
    exact h2
  have hYY : ∀ r, (supportKaroubiFiltration π Y).U ((K.Xamb π hψ hR).bd.C.X r) := fun r ↦
    supp_mapC π hY (hBd.mono htop) r
  have hlift : Lconc.cls (A := (supportKaroubiFiltration π Y).sub) (N := K.N)
      ((K.Xamb π hψ hR).bd.lift hYY) = -Lconc.cls (A := (supportKaroubiFiltration π Y).sub)
      (((symPoincareOf π hL ψL hψL hPL).map (asymptoticQuotInv π X)).lift
        (supp_mapC π hY hLY)) := by
    rw [← Lconc.cls_neg]
    exact Lconc.cls_eq_of_isometric (hbd'.lift _ _)
  refine (congrArg (𝕃.map (supportIncl htop) K.N) hcls).trans ?_
  rw [Units.smul_def, map_zsmul, ← 𝕃.cls_map, Lconc.map_cls]
  change 𝕃.bsign K.N • 𝕃.cls (supportKaroubiFiltration π Y).sub K.N
    (Lconc.cls (A := (supportKaroubiFiltration π Y).sub) ((K.Xamb π hψ hR).bd.lift hYY)) = _
  rw [hlift, map_neg, Units.smul_def, Units.smul_def, Units.val_neg, neg_smul, smul_neg]

end SeqCut

end BasedComplex

end HSFormal.Cubical
