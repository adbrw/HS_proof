import HSFormal.Cubical.CutRealize

/-!
# A single cut of a controlled Poincaré complex (cubical module C8, the step of Lemma 11.2)

A controlled strictly symmetric duality `ψ : W^{N+1-*} → W` (Poincaré in the prequotient) and a
cover `W = W_A ∪ W_B` by subcomplexes for which `ψ` is local in both directions (`SeqCut`).

* The **A-pair** `(W_A, Σ = W_A ∩ W_B)` with top `cutTop ψ W_A` is a controlled based pair
  (`SeqCut.Apair`); its relative cap is the left column `ladderLeft` of the excision ladder up to
  the cell bijection `W_A/Σ ≅ W/W_B`.  By two-out-of-three on the realized ladder
  `0 → (W/W_B)^* → W^* → W_B^* → 0`, `0 → W_A → W → W/W_A → 0` (`isKarEquiv_left`), it is an
  equivalence as soon as `ψ` and the right column `ladderRight` (the B-pair map) are: the A-pair is
  a `SymPair` (`SeqCut.toSymPair`).
* Realized cell isomorphisms (`ControlledSeq.Hom.ofCellIso`) and the dualities of compositions
  (`dualHom_toComplex_comp_dualityMap`).
-/

noncomputable section

namespace HSFormal.Cubical

open Filter Matrix CategoryTheory CategoryTheory.Limits HSFormal.LTheory HSFormal.Compression
open scoped ENNReal Topology

namespace BasedComplex

namespace ControlledSeq

variable {X : Type} [PseudoEMetricSpace X]

/-! ### Realized dualities of compositions -/

section Asymptotic

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  (π : ∀ i, G i →* H) [MulAction H X] [IsIsometricSMul H X] {A B C : ControlledSeq X} {N : ℕ}

theorem dualHom_toComplex_comp_dualityMap (hA : A.DimLE N) (hB : B.DimLE N) (F : Hom A B)
    (φ : Hom (A.dual N hA) C) :
    dualHom (asymptoticObjInvolution π X) N (F.toComplex π) ≫ dualityMap π hA φ =
      dualityMap π hB (φ.comp (F.dual N hA hB)) := by
  rw [dualHom_toComplex _ N hA hB, dualityMap, dualityMap, Category.assoc, Category.assoc,
    Iso.inv_hom_id_assoc, Hom.toComplex_comp]

theorem dualityMap_comp_toComplex (hA : A.DimLE N) (φ : Hom (A.dual N hA) B) (F : Hom B C) :
    dualityMap π hA φ ≫ F.toComplex π = dualityMap π hA (F.comp φ) := by
  rw [dualityMap, dualityMap, Category.assoc, Hom.toComplex_comp]

theorem dualityMap_congr (hA : A.DimLE N) {φ φ' : Hom (A.dual N hA) B}
    (h : ∀ i, (φ.f i).f = (φ'.f i).f) : dualityMap π hA φ = dualityMap π hA φ' := by
  rw [Hom.ext_f fun i ↦ BasedComplex.Hom.ext (h i)]

/-- A controlled duality equivalence realizes to a homotopy equivalence. -/
theorem isKarEquiv_dualityMap (hA : A.DimLE N) (E : HtpyEquiv (A.dual N hA) B) :
    IsKarEquiv (𝟙 _) (𝟙 _) (dualityMap π hA E.hom) := by
  have h := (isKarEquiv_id_iff _).mpr ⟨E.toHomotopyEquiv π, rfl⟩
  exact (IsKarEquiv.of_isIso (dualIso π A N hA).hom).comp h (by simp) (by simp) (by simp)

/-- Strictly inverse controlled chain maps realize to inverse isomorphisms. -/
theorem isIso_toComplex (F : Hom A B) (G : Hom B A) (h₁ : G.comp F = Hom.id A)
    (h₂ : F.comp G = Hom.id B) : IsIso (F.toComplex π) :=
  ⟨G.toComplex π, by rw [← Hom.toComplex_comp, h₁, Hom.toComplex_id],
    by rw [← Hom.toComplex_comp, h₂, Hom.toComplex_id]⟩

end Asymptotic

/-! ### Realized cell isomorphisms -/

variable {A B : ControlledSeq X}

/-- The controlled chain map of termwise cell isomorphisms preserving labels. -/
def Hom.ofCellIso (e : ∀ i, CellIso (A.C i) (B.C i))
    (hl : ∀ i σ, B.label i ((e i).toEquiv σ) = A.label i σ) : Hom A B where
  f i := (e i).hom
  tendsto := PropTendsto.of_label_eq fun i κ σ h ↦ by
    change (if κ = (e i).toEquiv σ then (1 : ℚ) else 0) ≠ 0 at h
    have hκ : κ = (e i).toEquiv σ := by by_contra h'; exact h (if_neg h')
    rw [hκ, hl]

theorem Hom.ofCellIso_f (e : ∀ i, CellIso (A.C i) (B.C i)) (hl) (i : ℕ) :
    ((Hom.ofCellIso e hl).f i).f = (e i).mat := rfl

theorem label_symm (e : ∀ i, CellIso (A.C i) (B.C i))
    (hl : ∀ i σ, B.label i ((e i).toEquiv σ) = A.label i σ) (i : ℕ) (σ : (B.C i).X) :
    A.label i ((e i).symm.toEquiv σ) = B.label i σ := by
  rw [← hl, CellIso.apply_symm_apply]

theorem Hom.ofCellIso_comp (e : ∀ i, CellIso (A.C i) (B.C i)) (hl) :
    (Hom.ofCellIso (fun i ↦ (e i).symm) (label_symm e hl)).comp (Hom.ofCellIso e hl) =
      Hom.id A :=
  Hom.ext_f fun i ↦ BasedComplex.Hom.ext (CellIso.mat_symm_mul_mat (e i))

theorem Hom.ofCellIso_comp' (e : ∀ i, CellIso (A.C i) (B.C i)) (hl) :
    (Hom.ofCellIso e hl).comp (Hom.ofCellIso (fun i ↦ (e i).symm) (label_symm e hl)) =
      Hom.id B :=
  Hom.ext_f fun i ↦ BasedComplex.Hom.ext (CellIso.mat_mul_mat_symm (e i))

section Asymptotic

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  (π : ∀ i, G i →* H) [MulAction H X] [IsIsometricSMul H X]

instance isIso_ofCellIso (e : ∀ i, CellIso (A.C i) (B.C i)) (hl) :
    IsIso ((Hom.ofCellIso e hl).toComplex π) :=
  isIso_toComplex π _ _ (Hom.ofCellIso_comp e hl) (Hom.ofCellIso_comp' e hl)

end Asymptotic

/-- The negative of a controlled chain map. -/
def Hom.neg (F : Hom A B) : Hom A B := ⟨fun i ↦ (F.f i).smul (-1), F.tendsto.smul (-1)⟩

section Asymptotic

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  (π : ∀ i, G i →* H) [MulAction H X] [IsIsometricSMul H X]

theorem Hom.neg_toComplex (F : Hom A B) : F.neg.toComplex π = -F.toComplex π := by
  ext r
  rw [Hom.toComplex_f, HomologicalComplex.neg_f_apply, Hom.toComplex_f, ← neg_one_smul ℚ,
    smul_hom]
  rfl

theorem dualityMap_neg {N : ℕ} (hA : A.DimLE N) (φ : Hom (A.dual N hA) B) :
    dualityMap π hA φ.neg = -dualityMap π hA φ := by
  rw [dualityMap, dualityMap, Hom.neg_toComplex, Preadditive.comp_neg]

variable {N : ℕ}

/-- **The realized Poincaré complex** `(A, φ)` of a controlled strictly symmetric duality map
which is a realized equivalence (no controlled inverse needed). -/
@[simps]
def symPoincareOf (hA : A.DimLE N) (φ : Hom (A.dual N hA) A) (hφ : IsSymm hA φ)
    (hP : IsKarEquiv (𝟙 _) (𝟙 _) (dualityMap π hA φ)) :
    SymPoincare (asymptoticObjInvolution π X) N where
  C := A.toComplex π
  p := 𝟙 _
  p_idem := by simp
  support := SymDuality.supportedIn_id π hA
  φ := dualityMap π hA φ
  φ_kar := by simp
  symm := isStrictSymm_dualityMap hφ
  poincare := by rw [isPoincare_iff, dualHom_id]; exact hP

end Asymptotic

end ControlledSeq

theorem CellIso.mat_transpose {C D : BasedComplex} (e : CellIso C D) : e.matᵀ = e.symm.mat := by
  ext σ ρ
  simp only [transpose_apply, CellIso.mat, of_apply]
  by_cases h : ρ = e.toEquiv σ
  · subst h; simp
  · rw [if_neg h, if_neg]
    rintro rfl
    exact h (e.apply_symm_apply ρ).symm

/-- Conjugation by a permutation matrix. -/
theorem CellIso.conj_apply {C D : BasedComplex} (e : CellIso C D) (M : Matrix C.X C.X ℚ)
    (ρ κ : D.X) : (e.mat * (M * e.matᵀ)) ρ κ = M (e.symm.toEquiv ρ) (e.symm.toEquiv κ) := by
  rw [CellIso.mat_mul_apply, CellIso.mat_transpose]
  have := CellIso.mul_mat_apply e.symm M (e.symm.toEquiv ρ) κ
  rw [this]

/-- The transport `c M c^*` of a duality map along a cell isomorphism. -/
abbrev CellIso.transportHom {C D : BasedComplex} {N : ℕ} (c : CellIso C D) (hC : C.DimLE N)
    (hD : D.DimLE N) (M : Hom (C.dual N hC) C) : Hom (D.dual N hD) D :=
  c.hom.comp (M.comp (c.hom.dual N hC hD))

theorem CellIso.transportHom_apply {C D : BasedComplex} {N : ℕ} (c : CellIso C D)
    (hC : C.DimLE N) (hD : D.DimLE N) (M : Hom (C.dual N hC) C) (σ τ : C.X) :
    (c.transportHom hC hD M).f (c.toEquiv σ) (c.toEquiv τ) = M.f σ τ := by
  change (c.mat * (M.f * c.matᵀ)) _ _ = _
  rw [CellIso.conj_apply, CellIso.symm_apply_apply, CellIso.symm_apply_apply]

theorem CellIso.transportHom_ext {C D : BasedComplex} {N : ℕ} (c : CellIso C D)
    (hC : C.DimLE N) (hD : D.DimLE N) (M : Hom (C.dual N hC) C) (M' : Hom (D.dual N hD) D)
    (h : ∀ σ τ, M'.f (c.toEquiv σ) (c.toEquiv τ) = M.f σ τ) : c.transportHom hC hD M = M' := by
  refine Hom.ext (Matrix.ext fun ρ κ ↦ ?_)
  obtain ⟨σ, rfl⟩ := c.toEquiv.surjective ρ
  obtain ⟨τ, rfl⟩ := c.toEquiv.surjective κ
  rw [transportHom_apply, h]

open ControlledSeq

/-! ### Cuts of controlled dualities -/

theorem IsSub.restrict_pred {C : BasedComplex} {P Q : C.X → Prop} [DecidablePred P]
    (hP : C.IsLocallyClosed P) (hQ : C.IsSub Q) :
    (C.restrict P hP).IsSub fun x ↦ Q x.1 :=
  fun _ _ h hy ↦ hQ _ _ h hy

/-- **A cut** of a controlled `(N+1)`-dimensional strictly symmetric duality `ψ` along a cover
`W = W_A ∪ W_B` by subcomplexes, `ψ` local in both directions, `Σ = W_A ∩ W_B` of dimension
`≤ N`. -/
structure SeqCut (X : Type) [PseudoEMetricSpace X] where
  W : ControlledSeq X
  N : ℕ
  hW : W.DimLE (N + 1)
  ψ : ControlledSeq.Hom (W.dual (N + 1) hW) W
  hψ : ControlledSeq.IsSymm hW ψ
  SA : ∀ i, (W.C i).X → Prop
  SB : ∀ i, (W.C i).X → Prop
  [decA : ∀ i, DecidablePred (SA i)]
  [decB : ∀ i, DecidablePred (SB i)]
  hA : ∀ i, (W.C i).IsSub (SA i)
  hB : ∀ i, (W.C i).IsSub (SB i)
  cover : ∀ i σ, SA i σ ∨ SB i σ
  loc : ∀ i σ τ, (ψ.f i).f σ τ ≠ 0 → ¬SB i τ → SA i σ
  loc' : ∀ i σ τ, (ψ.f i).f σ τ ≠ 0 → ¬SA i τ → SB i σ
  hSig : ∀ i σ, SA i σ → SB i σ → (W.C i).deg σ ≤ N

namespace SeqCut

variable {X : Type} [PseudoEMetricSpace X] (K : SeqCut X)

attribute [instance] SeqCut.decA SeqCut.decB

/-- `W_A`. -/
abbrev WA : ControlledSeq X := K.W.restrict K.SA fun i ↦ (K.hA i).isLocallyClosed

/-- `W/W_B` (the cells off `B`, all in `A`). -/
abbrev WnB : ControlledSeq X :=
  K.W.restrict (fun i σ ↦ ¬K.SB i σ) fun i ↦ (K.hB i).isLocallyClosed_compl

/-- `W_B`. -/
abbrev WB : ControlledSeq X := K.W.restrict K.SB fun i ↦ (K.hB i).isLocallyClosed

/-- `W/W_A`. -/
abbrev WnA : ControlledSeq X :=
  K.W.restrict (fun i σ ↦ ¬K.SA i σ) fun i ↦ (K.hA i).isLocallyClosed_compl

theorem hWnB : K.WnB.DimLE (K.N + 1) := fun i σ ↦ K.hW i σ.1
theorem hWB : K.WB.DimLE (K.N + 1) := fun i σ ↦ K.hW i σ.1

theorem T_deg (i : ℕ) (σ τ : (K.W.C i).X) (h : (K.ψ.f i).f σ τ ≠ 0) :
    (K.W.C i).deg σ + (K.W.C i).deg τ = K.N + 1 := by
  have h₁ := (K.ψ.f i).deg0 σ τ h
  have h₂ := K.hW i τ
  change ((K.W.C i).deg σ : ℤ) = ((K.N + 1 - (K.W.C i).deg τ : ℕ) : ℤ) + 0 at h₁
  omega

/-- **The A-pair** `(W_A, Σ)` with top `cutTop ψ W_A`. -/
@[implicit_reducible] def Apair : SeqPair X where
  D := K.WA
  N := K.N
  hD i σ := K.hW i σ.1
  S i x := K.SB i x.1
  hS i := IsSub.restrict_pred (K.hA i).isLocallyClosed (K.hB i)
  hSN i x hx := K.hSig i x.1 x.2 hx
  T i := cutTop (K.hW i) (K.ψ.f i) (K.SA i)
  T_deg i _ _ h := K.T_deg i _ _ h
  T_symm i σ τ := (isSymm_iff (K.ψ.f i)).mp (K.hψ i) σ.1 τ.1
  T_tendsto := tendsto_zero_of_le K.ψ.tendsto fun i ↦
    prop_submatrix_le (u := (K.ψ.f i).f) (source := K.W.label i) (target := K.W.label i)
      Subtype.val Subtype.val
  supp i _ _ h := cutDefect_ne_zero (K.hA i).isLocallyClosed (K.hB i) (K.cover i) (K.loc i)
    (K.loc' i) h

/-- The left column `C^{N+1-*}(W, W_B) → C(W_A)` of the excision ladder. -/
def ladderL : ControlledSeq.Hom (K.WnB.dual (K.N + 1) K.hWnB) K.WA where
  f i := ladderLeft (K.hW i) (K.ψ.f i) (K.hA i) (K.hB i) (K.loc i)
  tendsto := tendsto_zero_of_le K.ψ.tendsto fun i ↦
    prop_submatrix_le (u := (K.ψ.f i).f) (source := K.W.label i) (target := K.W.label i)
      Subtype.val Subtype.val

/-- The right column (the B-pair map) `C^{N+1-*}(W_B) → C(W/W_A)`. -/
def ladderR : ControlledSeq.Hom (K.WB.dual (K.N + 1) K.hWB) K.WnA where
  f i := ladderRight (K.hW i) (K.ψ.f i) (K.hA i) (K.hB i) (K.loc i)
  tendsto := tendsto_zero_of_le K.ψ.tendsto fun i ↦
    prop_submatrix_le (u := (K.ψ.f i).f) (source := K.W.label i) (target := K.W.label i)
      Subtype.val Subtype.val

/-- The cells of `W/W_B` are the cells of `W_A/Σ`. -/
def relIso (i : ℕ) : CellIso (K.WnB.C i) (K.Apair.Rel.C i) where
  toEquiv :=
    { toFun σ := ⟨⟨σ.1, (K.cover i σ.1).resolve_right σ.2⟩, σ.2⟩
      invFun x := ⟨x.1.1, x.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  deg_eq _ := rfl
  d_eq _ _ := rfl

/-- The realized cell isomorphism `W/W_B ≅ W_A/Σ`. -/
def relIsoHom : ControlledSeq.Hom K.WnB K.Apair.Rel :=
  Hom.ofCellIso K.relIso fun _ _ ↦ rfl

theorem relHom_eq :
    K.Apair.relHom = K.ladderL.comp (K.relIsoHom.dual (K.N + 1) K.hWnB K.Apair.hRel) := by
  refine Hom.ext_f fun i ↦ BasedComplex.Hom.ext (Matrix.ext fun ρ x ↦ ?_)
  simp only [ControlledSeq.Hom.comp, BasedComplex.Hom.comp, mul_apply]
  symm
  refine (Finset.sum_eq_single (⟨x.1.1, x.2⟩ : (K.WnB.C i).X) ?_ ?_).trans ?_
  · intro σ _ hσ
    change _ * (if x = (K.relIso i).toEquiv σ then (1 : ℚ) else 0) = 0
    rw [if_neg, mul_zero]
    rintro rfl
    exact hσ rfl
  · intro h; exact absurd (Finset.mem_univ _) h
  · change _ * (if x = (K.relIso i).toEquiv ⟨x.1.1, x.2⟩ then (1 : ℚ) else 0) = _
    rw [if_pos (by rfl), mul_one]
    rfl

/-- The flat interface `Σ = W_A ∩ W_B`. -/
abbrev Sig : ControlledSeq X :=
  K.W.restrict (fun i σ ↦ K.SA i σ ∧ K.SB i σ) fun i ↦ ((K.hA i).and (K.hB i)).isLocallyClosed

theorem hSigN : K.Sig.DimLE K.N := fun i σ ↦ K.hSig i σ.1 σ.2.1 σ.2.2

theorem hBd' : K.Apair.Bd.DimLE K.N := K.Apair.hBd

/-- The nested cells of the A-pair boundary are the flat interface. -/
def nest (i : ℕ) : CellIso (K.Sig.C i) (K.Apair.Bd.C i) where
  toEquiv :=
    { toFun σ := ⟨⟨σ.1, σ.2.1⟩, σ.2.2⟩
      invFun x := ⟨x.1.1, x.1.2, x.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  deg_eq _ := rfl
  d_eq _ _ := rfl

theorem hsuppA (i : ℕ) : ∀ σ τ : {σ // K.SA i σ},
    cutDefect (K.hW i) (K.ψ.f i) (K.SA i) (K.hA i).isLocallyClosed σ τ ≠ 0 →
      (K.SA i σ.1 ∧ K.SB i σ.1) ∧ (K.SA i τ.1 ∧ K.SB i τ.1) := cutDefect_supp_left (hW := K.hW i) (φ := K.ψ.f i) (K.hA i) (K.hB i)
  (K.cover i) (K.loc i) (K.loc' i)

theorem hsuppB (i : ℕ) : ∀ σ τ : {σ // K.SB i σ},
    cutDefect (K.hW i) (K.ψ.f i) (K.SB i) (K.hB i).isLocallyClosed σ τ ≠ 0 →
      (K.SA i σ.1 ∧ K.SB i σ.1) ∧ (K.SA i τ.1 ∧ K.SB i τ.1) := cutDefect_supp_right (hW := K.hW i) (φ := K.ψ.f i) (K.hA i) (K.hB i)
  (K.cover i) (K.loc i) (K.loc' i)

/-- The A-side boundary structure on the flat interface. -/
abbrev bdA (i : ℕ) : BasedComplex.Hom ((K.Sig.C i).dual K.N (K.hSigN i)) (K.Sig.C i) :=
  cutBdHom (K.hW i) (K.ψ.f i) (K.SA i) (fun σ ↦ K.SA i σ ∧ K.SB i σ) (K.hA i).isLocallyClosed
    (fun _ h ↦ h.1) ((K.hA i).and (K.hB i)) (K.hSigN i) (K.hsuppA i)

/-- **The B-side boundary structure** on the flat interface (the boundary of the B-pair). -/
abbrev bdB (i : ℕ) : BasedComplex.Hom ((K.Sig.C i).dual K.N (K.hSigN i)) (K.Sig.C i) :=
  cutBdHom (K.hW i) (K.ψ.f i) (K.SB i) (fun σ ↦ K.SA i σ ∧ K.SB i σ) (K.hB i).isLocallyClosed
    (fun _ h ↦ h.2) ((K.hA i).and (K.hB i)) (K.hSigN i) (K.hsuppB i)

/-- The two sides have opposite boundary structures up to the homotopy `cutTop ψ Σ`. -/
def bdHtpy (i : ℕ) : BasedComplex.Htpy (K.bdA i) ((K.bdB i).smul (-1)) :=
  cutBdHtpy (K.hW i) (K.ψ.f i) (K.hA i) (K.hB i) (K.hSigN i) (K.cover i) (K.hsuppA i)
    (K.hsuppB i)

theorem bdHom_nest (i : ℕ) (σ τ : (K.Sig.C i).X) :
    (K.Apair.bdHom.f i).f ((K.nest i).toEquiv σ) ((K.nest i).toEquiv τ) = (K.bdA i).f σ τ :=
  rfl

section Asymptotic

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  (π : ∀ i, G i →* H) [MulAction H X] [IsIsometricSMul H X]

/-- **Two-out-of-three on the excision ladder**: if `ψ` and the B-pair map are realized
equivalences, so is the left column. -/
theorem isKarEquiv_ladderL (hψ : IsKarEquiv (𝟙 _) (𝟙 _) (dualityMap π K.hW K.ψ))
    (hR : IsKarEquiv (𝟙 _) (𝟙 _) (dualityMap π K.hWB K.ladderR)) :
    IsKarEquiv (𝟙 _) (𝟙 _) (dualityMap π K.hWnB K.ladderL) := by
  refine isKarEquiv_left (((K.W.splitSeq π K.hB).dual (asymptoticObjInvolution π X)
    ((K.N + 1 : ℕ) : ℤ))) (K.W.splitSeq π K.hA) ?_ ?_ hψ hR
  · rw [dualHom_toComplex_comp_dualityMap π K.hW K.hWnB, dualityMap_comp_toComplex]
    refine dualityMap_congr π _ fun i ↦ ?_
    exact congrArg BasedComplex.Hom.f
      (ladderLeft_comm (K.hW i) (K.ψ.f i) (K.hA i) (K.hB i) (K.loc i)).symm
  · rw [dualHom_toComplex_comp_dualityMap π K.hWB K.hW, dualityMap_comp_toComplex]
    refine dualityMap_congr π _ fun i ↦ ?_
    exact congrArg BasedComplex.Hom.f
      (ladderRight_comm (K.hW i) (K.ψ.f i) (K.hA i) (K.hB i) (K.loc i)).symm

/-- The relative cap of the A-pair is a realized equivalence. -/
theorem isKarEquiv_relHom (hψ : IsKarEquiv (𝟙 _) (𝟙 _) (dualityMap π K.hW K.ψ))
    (hR : IsKarEquiv (𝟙 _) (𝟙 _) (dualityMap π K.hWB K.ladderR)) :
    IsKarEquiv (𝟙 _) (𝟙 _) (dualityMap π K.Apair.hRel K.Apair.relHom) := by
  rw [relHom_eq, ← dualHom_toComplex_comp_dualityMap π K.hWnB K.Apair.hRel]
  haveI : IsIso (K.relIsoHom.toComplex π) := isIso_ofCellIso π _ _
  haveI : IsIso (dualHom (asymptoticObjInvolution π X) ((K.N + 1 : ℕ) : ℤ)
      (K.relIsoHom.toComplex π)) :=
    inferInstanceAs (IsIso (LTheory.dualIso (asymptoticObjInvolution π X) ((K.N + 1 : ℕ) : ℤ)
      (asIso (K.relIsoHom.toComplex π))).hom)
  exact (IsKarEquiv.of_isIso _).comp (K.isKarEquiv_ladderL π hψ hR) (by simp) (by simp) (by simp)

/-- **The A-pair of a cut is a Poincaré pair** (prequotient). -/
def toSymPair (hψ : IsKarEquiv (𝟙 _) (𝟙 _) (dualityMap π K.hW K.ψ))
    (hR : IsKarEquiv (𝟙 _) (𝟙 _) (dualityMap π K.hWB K.ladderR)) :
    SymPair (asymptoticObjInvolution π X) K.N :=
  K.Apair.toSymPair π (K.isKarEquiv_relHom π hψ hR)

theorem prop_mat_eq_zero {C D : BasedComplex} (e : CellIso C D) {a : C.X → X} {b : D.X → X}
    (h : ∀ σ, b (e.toEquiv σ) = a σ) : prop e.mat a b = 0 :=
  le_antisymm (prop_le_iff.mpr fun ρ σ hρσ ↦ by
    have : ρ = e.toEquiv σ := by
      by_contra h'; exact hρσ (by simp [CellIso.mat, h'])
    rw [this, h, edist_self]) bot_le

/-- **The boundary of the A-pair is the negative of the next closed complex**: if a cell
isomorphism `e : Σ ≅ L` carries the B-side boundary structure (the boundary of the B-pair) to a
Poincaré duality `ψ_L` of `L`, then `∂(A-pair) ≃ -(L, ψ_L)` (`cutBdHtpy`). -/
theorem bd_isometric (hψ : IsKarEquiv (𝟙 _) (𝟙 _) (dualityMap π K.hW K.ψ))
    (hR : IsKarEquiv (𝟙 _) (𝟙 _) (dualityMap π K.hWB K.ladderR)) {L : ControlledSeq X}
    {hL : L.DimLE K.N} {ψL : ControlledSeq.Hom (L.dual K.N hL) L} (hψL : ControlledSeq.IsSymm hL ψL)
    (hPL : IsKarEquiv (𝟙 _) (𝟙 _) (dualityMap π hL ψL)) (e : ∀ i, CellIso (K.Sig.C i) (L.C i))
    (hl : ∀ i σ, L.label i ((e i).toEquiv σ) = K.W.label i σ.1)
    (hmatch : ∀ i σ τ, (ψL.f i).f ((e i).toEquiv σ) ((e i).toEquiv τ) = (K.bdB i).f σ τ) :
    SymPoincare.Isometric (K.toSymPair π hψ hR).bd (symPoincareOf π hL ψL hψL hPL).neg := by
  let c : ∀ i, CellIso (K.Apair.Bd.C i) (L.C i) := fun i ↦ (K.nest i).symm.trans (e i)
  have hc : ∀ i x, L.label i ((c i).toEquiv x) = K.Apair.Bd.label i x := fun i x ↦ hl i _
  let F : ControlledSeq.Hom K.Apair.Bd L := Hom.ofCellIso c hc
  let Fi : ControlledSeq.Hom L K.Apair.Bd := Hom.ofCellIso (fun i ↦ (c i).symm) (label_symm c hc)
  -- the transported homotopy
  have h₁ : ∀ i, (e i).transportHom (K.hSigN i) (hL i) (K.bdA i) =
      ((F.comp K.Apair.bdHom).comp (F.dual K.N K.Apair.hBd hL)).f i := fun i ↦ by
    refine CellIso.transportHom_ext _ _ _ _ _ fun σ τ ↦ ?_
    have := (c i).transportHom_apply (K.hBd' i) (hL i) (K.Apair.bdHom.f i) ((K.nest i).toEquiv σ)
      ((K.nest i).toEquiv τ)
    simp only [c, CellIso.trans_apply, CellIso.symm_apply_apply] at this
    rw [← K.bdHom_nest i, ← this, CellIso.transportHom]
    exact congrArg (fun M : BasedComplex.Hom ((L.C i).dual K.N (hL i)) (L.C i) ↦
      M.f ((e i).toEquiv σ) ((e i).toEquiv τ))
      (BasedComplex.Hom.comp_assoc ((c i).hom) (K.Apair.bdHom.f i)
        ((c i).hom.dual K.N (K.hBd' i) (hL i)))
  have h₂ : ∀ i, (e i).transportHom (K.hSigN i) (hL i) ((K.bdB i).smul (-1)) = ψL.neg.f i :=
    fun i ↦ CellIso.transportHom_ext _ _ _ _ _ fun σ τ ↦ by
      change (-1 : ℚ) • (ψL.f i).f _ _ = (-1 : ℚ) • (K.bdB i).f σ τ
      rw [hmatch]
  let Hc : ControlledSeq.Htpy ((F.comp K.Apair.bdHom).comp (F.dual K.N K.Apair.hBd hL))
      ψL.neg :=
    { h := fun i ↦ (((K.bdHtpy i).compRight ((e i).hom.dual K.N (K.hSigN i) (hL i))).compLeft
        (e i).hom).congr (h₁ i) (h₂ i)
      tendsto := by
        refine tendsto_zero_of_le K.ψ.tendsto fun i ↦ ?_
        dsimp only
        rw [Htpy.congr_h, Htpy.compLeft_h, Htpy.compRight_h, Hom.dual_f]
        change prop ((e i).mat * (_ * (e i).matᵀ)) (L.label i) (L.label i) ≤ _
        rw [CellIso.mat_transpose]
        refine prop_mul_le_of_le (b := K.Sig.label i) (prop_mul_le_of_le
          (b := K.Sig.label i) (le_of_eq (prop_mat_eq_zero (e i).symm fun ρ ↦ ?_))
          (prop_submatrix_le (u := (K.ψ.f i).f) (source := K.W.label i)
            (target := K.W.label i) Subtype.val Subtype.val) (by rw [zero_add]))
          (le_of_eq (prop_mat_eq_zero (e i) (hl i))) (by rw [add_zero])
        have := hl i ((e i).symm.toEquiv ρ)
        rw [CellIso.apply_symm_apply] at this
        exact this.symm }
  refine ⟨⟨F.toComplex π, Fi.toComplex π, by simp [symPoincareOf, toSymPair],
    by simp [symPoincareOf, toSymPair],
    Homotopy.ofEq ?_, Homotopy.ofEq ?_, homotopyCongr
      (((Hc.toHomotopy π)).compLeft (dualIso π L K.N hL).hom) ?_ ?_⟩⟩
  · change Hom.toComplex π F ≫ Hom.toComplex π Fi = 𝟙 _
    rw [← Hom.toComplex_comp, Hom.ofCellIso_comp, Hom.toComplex_id]
  · change Hom.toComplex π Fi ≫ Hom.toComplex π F = 𝟙 _
    rw [← Hom.toComplex_comp, Hom.ofCellIso_comp', Hom.toComplex_id]
  · change dualityMap π hL _ = _
    rw [← dualHom_toComplex_comp_dualityMap π K.hBd' hL, ← dualityMap_comp_toComplex]
    rfl
  · change dualityMap π hL _ = _
    rw [dualityMap_neg]
    rfl

end Asymptotic

end SeqCut

end BasedComplex

end HSFormal.Cubical
