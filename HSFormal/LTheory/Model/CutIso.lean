import HSFormal.LTheory.Model.CutHalf
import HSFormal.LTheory.Model.CutIsoGen

/-!
# The cut union is homotopy isometric to `(-1)^N P` (lower L-theory model, module 22)

For an honest free `(N+1)`-dimensional Poincaré complex `P = (C, 1, φ)` over `C_ℤ(A)` and cut
data with `Sec` data, the lower and upper cut pairs `X⁻ = lowerPair`, `X⁺ = upperPair`
(`Model/CutBoundary.lean`, `Model/CutUpper.lean`) glue to `cutUnion = X⁻ ∪ X⁺`.  This file
proves `cutUnion ≃ (-1)^N P`.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression
  homotopyCofiber

noncomputable section

attribute [local implicit_reducible] CZ.CutData.lowerPair CZ.CutData.upperPair
  CZ.CutData.rawUpperPair PairOn.union PairOn.glue PairOn.toPair SymPair.closedOfIsZero
  SymPair.toPairOn CZ.cut CZ.diagSplitting

lemma homotopyCongr_heq {V : Type*} [Category V] [Preadditive V] {C D : ChainComplex V ℤ}
    {f g f' g' : C ⟶ D} (H : Homotopy f g) (hf : f = f') (hg : g = g') :
    HEq (homotopyCongr H hf hg) H := by
  subst hf hg; rfl

/-- A cast of `SymPair.toPairOn` along an equality of boundaries is a given `PairOn` with the
same fields. -/
lemma cast_toPairOn_eq {V : Type*} [Category V] [Preadditive V] [HasBinaryBiproducts V]
    {J : StrictInvolution V} {N : ℤ} (T : SymPair J N) {Q : SymPoincare J N} (h : T.bd = Q)
    (T' : PairOn Q) (hD : T'.D = T.D) (hpD : HEq T'.pD T.pD) (hj : HEq T'.j T.j)
    (hδ : HEq T'.δφ T.δφ) : h ▸ T.toPairOn = T' := by
  cases T
  subst h
  cases T'
  dsimp only at hD hpD hj hδ
  subst hD
  cases hpD
  cases hj
  cases hδ
  rfl

lemma bicone_total' {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C] (X Y : C) :
    (BinaryBiproduct.bicone X Y).snd ≫ (BinaryBiproduct.bicone X Y).inr +
      (BinaryBiproduct.bicone X Y).fst ≫ (BinaryBiproduct.bicone X Y).inl = 𝟙 _ := by
  rw [add_comm]; exact biprod.total

namespace CZ

namespace CutData

variable {A : InvCat} {N : ℤ} {P : SymPoincare A.cz.inv (N + 1)} {D : CutData P}

/-! ### The upper pair as a pair on `-∂` -/

section Upper

variable (S : D.Sec) (hp : P.p = 𝟙 _) (hN : 0 ≤ N)

/-- The common boundary `∂` of the cut pairs. -/
abbrev cutBd : SymPoincare A.cz.inv N := (lowerPair S hp hN).bd

lemma cutBd_φ : (cutBd S hp hN).φ = dualHom A.cz.inv N (truncEquiv S hp hN).f ≫ D.thom.bdφ ≫
    (truncEquiv S hp hN).f := rfl

lemma cutBd_p : (cutBd S hp hN).p = truncIdem S := rfl

lemma upperPair_bd_φ : (upperPair S hp hN).bd.φ = dualHom A.cz.inv N (truncEquiv S hp hN).f ≫
    (-D.thom.bdφ) ≫ (truncEquiv S hp hN).f := rfl

lemma upperPair_δφ_eq : dualHom A.cz.inv N ((truncEquiv S hp hN).g ≫ D.jPlus) ≫
    (dualHom A.cz.inv N (truncEquiv S hp hN).f ≫ (-D.thom.bdφ) ≫ (truncEquiv S hp hN).f) ≫
      (truncEquiv S hp hN).g ≫ D.jPlus =
    dualHom A.cz.inv N ((truncEquiv S hp hN).g ≫ D.jPlus) ≫ (cutBd S hp hN).neg.φ ≫
      (truncEquiv S hp hN).g ≫ D.jPlus := by
  simp [SymPoincare.neg, cutBd_φ]

/-- The relative structure of the upper pair, as a relative structure on `-∂`. -/
def upperOnδφ : Homotopy (dualHom A.cz.inv N ((truncEquiv S hp hN).g ≫ D.jPlus) ≫
    (cutBd S hp hN).neg.φ ≫ (truncEquiv S hp hN).g ≫ D.jPlus) 0 :=
  homotopyCongr (upperPair S hp hN).δφ (upperPair_δφ_eq S hp hN) rfl

lemma relDuality_upperOnδφ :
    relDuality (upperOnδφ S hp hN) = relDuality (upperPair S hp hN).δφ := by
  ext r : 1
  simp only [relDuality_f]
  have h₁ : relTop (upperOnδφ S hp hN) r = relTop (upperPair S hp hN).δφ r := rfl
  have h₂ : (cutBd S hp hN).neg.φ.f r = (upperPair S hp hN).bd.φ.f r := by
    simp [SymPoincare.neg, cutBd_φ, upperPair_bd_φ]
  rw [h₁, h₂]
  rfl

/-- **The upper cut pair as a pair on `-∂`** (no cast: all fields explicit). -/
@[implicit_reducible]
def upperOn : PairOn (cutBd S hp hN).neg where
  D := D.subC
  pD := 𝟙 _
  pD_idem := by simp
  support := (upperPair S hp hN).support
  j := (truncEquiv S hp hN).g ≫ D.jPlus
  j_kar := (upperPair S hp hN).j_kar
  δφ := upperOnδφ S hp hN
  δφ_kar := (upperPair S hp hN).δφ_kar
  symm := (upperPair S hp hN).symm
  poincare := by
    rw [relDuality_upperOnδφ]
    exact (upperPair S hp hN).poincare

/-- The cut union, with the upper pair given by `upperOn`. -/
abbrev cutUnion' : SymPoincare A.cz.inv (N + 1) :=
  (lowerPair S hp hN).toPairOn.union (upperOn S hp hN)

lemma cutUnion_eq : cutUnion S hp hN = cutUnion' S hp hN := by
  rw [cutUnion, SymPair.union, cast_toPairOn_eq (upperPair S hp hN) (upperPair_bd S hp hN)
    (upperOn S hp hN) rfl HEq.rfl HEq.rfl (homotopyCongr_heq _ (upperPair_δφ_eq S hp hN) rfl)]

end Upper

/-! ### The comparison map `X⁻ ∪ X⁺ ⟶ P` -/

section Comparison

variable (S : D.Sec) (hp : P.p = 𝟙 _) (hN : 0 ≤ N)

include hp in
lemma bdJ_φq : D.thom.bdJ ≫ D.φq = coneFst D.thom.φ ≫ D.φq := by
  rw [SymComplex.bdJ, assoc]
  congr 1
  change dualHom A.cz.inv (N + 1) D.pT ≫ D.φq = D.φq
  rw [D.pT_eq_id hp, dualHom_id, id_comp]

/-- The raw gluing null-homotopy `j⁻ φq - j⁺ ι_S ≃ 0` (`glueHomotopy`). -/
def glueHd : Homotopy (D.thom.bdJ ≫ D.φq + D.jPlus ≫ (-D.inclS)) 0 :=
  homotopyCongr (Homotopy.equivSubZero D.glueHomotopy.symm)
    (by rw [bdJ_φq hp, Preadditive.comp_neg, ← sub_eq_add_neg]) rfl

lemma glueHd_hom (i k : ℤ) : (glueHd hp).hom i k = -D.glueHomotopy.hom i k := rfl

/-- The two inclusions `T^{N+1-*} ⊕ S ⟶ C`, `(x, s) ↦ φ q^* x - ι_S s`. -/
def cmpα : Glue.S (lowerPair S hp hN).toPairOn (upperOn S hp hN) ⟶ P.C :=
  sumFst _ ≫ D.φq + sumSnd _ ≫ (-D.inclS)

lemma u_cmpα : Glue.u (σU _) (lowerPair S hp hN).toPairOn (upperOn S hp hN) ≫ cmpα S hp hN =
    (truncEquiv S hp hN).g ≫ (D.thom.bdJ ≫ D.φq + D.jPlus ≫ (-D.inclS)) := by
  simp only [Glue.u, Glue.β, Glue.jY, cmpα, add_comp, comp_add, assoc, sumInl_sumFst_assoc,
    sumInl_sumSnd_assoc, sumInr_sumFst_assoc, sumInr_sumSnd_assoc, zero_comp, comp_zero,
    add_zero, zero_add]
  change truncIdem S ≫ ((truncEquiv S hp hN).g ≫ D.thom.bdJ) ≫ D.φq +
    ((truncEquiv S hp hN).g ≫ D.jPlus) ≫ (-D.inclS) = _
  rw [assoc, (truncEquiv S hp hN).pg_assoc]
  simp only [assoc]

/-- The null-homotopy of `u α` on the truncated boundary. -/
def cmpHd : Homotopy (Glue.u (σU _) (lowerPair S hp hN).toPairOn (upperOn S hp hN) ≫
    cmpα S hp hN) 0 :=
  homotopyCongr ((glueHd hp).compLeft (truncEquiv S hp hN).g) (u_cmpα S hp hN).symm (by simp)

/-- **The comparison map** `X⁻ ∪ X⁺ ⟶ P`: `φ q^*` on `T^{N+1-*}`, `-ι_S` on `S`, the gluing
homotopy on the cone coordinate. -/
def cutCmp : Glue.U (σU _) (lowerPair S hp hN).toPairOn (upperOn S hp hN) ⟶ P.C :=
  desc _ (cmpα S hp hN) (cmpHd S hp hN)

/-- The truncation homotopy `W : g ∂ g^* ≃ ∂φ` on the raw boundary. -/
def cutW : Homotopy (dualHom A.cz.inv N (truncEquiv S hp hN).g ≫ (cutBd S hp hN).φ ≫
    (truncEquiv S hp hN).g) D.thom.bdφ :=
  homotopyCongr ((D.thom.rawBoundaryPair D.pT_support).bdW (truncEquiv S hp hN))
    (by simp [cutBd_φ]) rfl

lemma cutW_hom (i k : ℤ) : (cutW S hp hN).hom i k =
    ((D.thom.rawBoundaryPair D.pT_support).bdW (truncEquiv S hp hN)).hom i k := rfl

lemma upper_bdW_hom (i k : ℤ) : ((D.rawUpperPair hp).bdW (truncEquiv S hp hN)).hom i k =
    -((D.thom.rawBoundaryPair D.pT_support).bdW (truncEquiv S hp hN)).hom i k := by
  simp only [RawPair.bdW, symmHomotopy_hom, RawPair.bdW₀, transposeHomFamily, Pi.smul_apply,
    Pi.add_apply, karHomotopy_hom, homotopyCongr, conjHomotopy_refl_hom]
  simp [rawUpperPair, StrictInvolution.star_add, StrictInvolution.star_neg, smul_add, smul_neg]
  abel

end Comparison

/-! ### The structure is carried to `(-1)^N φ` -/

section Conj

variable (S : D.Sec) (hp : P.p = 𝟙 _) (hN : 0 ≤ N)

lemma claimA_t1 {a b c d : ℤ} (h₁ : a = b) (h₂ : b = c) (h₃ : c = d) {Z : A.cz}
    (Y : P.C.X d ⟶ Z) :
    (P.C.XIsoOfEq h₁).hom ≫ (P.C.XIsoOfEq h₂).hom ≫ (D.σ c).πE ≫ (D.thom.C.XIsoOfEq h₃).hom ≫
      (D.σ d).ιE ≫ Y = (P.C.XIsoOfEq (h₁.trans (h₂.trans h₃))).hom ≫ (D.σ d).πE ≫
        (D.σ d).ιE ≫ Y := by
  subst h₁ h₂ h₃; simp

lemma πE_castT_ιE_cast {b z w : ℤ} (h₂ : b = z) (h₃ : z = w) :
    (D.σ b).πE ≫ (D.thom.C.XIsoOfEq h₂).hom ≫ (D.σ z).ιE ≫ (P.C.XIsoOfEq h₃).hom =
      (P.C.XIsoOfEq (h₂.trans h₃)).hom ≫ (D.σ w).πE ≫ (D.σ w).ιE := by
  subst h₂ h₃; simp

lemma claimA_t2 {a x z w : ℤ} (h₁ : a = x) (h₂ : N + 1 - x = z) (h₃ : z = w) :
    (P.C.XIsoOfEq h₁).hom ≫ (D.σ x).πU ≫ (D.σ x).ιU ≫ A.cz.inv.star (P.φ.f x) ≫
      (D.σ (N + 1 - x)).πE ≫ (D.thom.C.XIsoOfEq h₂).hom ≫ (D.σ z).ιE ≫ (P.C.XIsoOfEq h₃).hom =
    (w * (N + 1 - w)).negOnePow • ((D.σ a).πU ≫ (D.σ a).ιU ≫
      (P.C.XIsoOfEq (by omega : a = N + 1 - w)).hom ≫ P.φ.f w ≫ (D.σ w).πE ≫ (D.σ w).ιE) := by
  rw [πE_castT_ιE_cast h₂ h₃, star_φ_cast_assoc P x w (h₂.trans h₃)]
  subst h₁
  simp

lemma claimA_t3 {a x m w : ℤ} (h₁ : a = x) (h₂ : x = N + 1 - m) (h₃ : m = w) {Z : A.cz}
    (Y : P.C.X w ⟶ Z) :
    (P.C.XIsoOfEq h₁).hom ≫ (D.σ x).πU ≫ (D.σ x).ιU ≫ (P.C.XIsoOfEq h₂).hom ≫ P.φ.f m ≫
      (P.C.XIsoOfEq h₃).hom ≫ Y = (D.σ a).πU ≫ (D.σ a).ιU ≫
        (P.C.XIsoOfEq (by omega : a = N + 1 - w)).hom ≫ P.φ.f w ≫ Y := by
  subst h₁ h₃; simp

/-- **The raw union family of the cut is `(-1)^N φ`**: the three terms are the `E`-columns, the
`(U, E)`-block and the `(U, U)`-block of `φ`. -/
lemma cut_rawFam (r : ℤ) : (N.negOnePow • P.φ).f r =
    (P.C.XIsoOfEq (by omega : N + 1 - r = N - (r - 1))).hom ≫
      rawFam D.thom.bdφ D.thom.bdJ D.jPlus D.φq (-D.inclS) D.thom.bdRel.hom
        (D.deltaPlus hp).hom (glueHd hp) (r - 1) r := by
  simp only [rawFam, glueHd_hom, dualHomotopy_hom, SymComplex.bdRel, Homotopy.ofEq,
    Pi.zero_apply, zero_comp, comp_zero, add_zero]
  rw [D.glueHomotopy_hom (by simp; omega), D.glueHomotopy_hom (by simp),
    D.deltaPlus_hom_of_rel hp (by simp)]
  have hφ : D.thom.bdφ = D.thom.bdSwap := by
    rw [SymComplex.bdφ, D.bdP_eq_id hp, comp_id]
  have hJ : D.thom.bdJ = coneFst D.thom.φ := by
    rw [SymComplex.bdJ, D.thom_p, D.pT_eq_id hp]
    exact (congrArg _ (dualHom_id _ _ _)).trans (comp_id _)
  rw [hφ, hJ]
  simp only [glueHom, topPlus, comp_f, neg_f_apply, dualHom_f, SymComplex.bdSwap_f, jPlus_f, jPlusF,
    SplitCx.fromSub_f, coneFst_f, StrictInvolution.star_neg, StrictInvolution.star_comp,
    StrictInvolution.star_add, StrictInvolution.star_units_smul, Preadditive.neg_comp,
    Preadditive.comp_neg, add_comp, comp_add, assoc, Linear.units_smul_comp,
    Linear.comp_units_smul, neg_neg, star_σ_πU, star_σ_ιU, star_σ_πE, star_σ_ιE,
    SymComplex.star_sndX_swapF_assoc, SymComplex.star_fstX_swapF_assoc, compA, cross,
    SplitCx.cross, BoundaryConstruction.star_XIsoOfEq_hom, inlX_fstX_assoc, inrX_sndX_assoc,
    inlX_sndX_assoc, inrX_fstX_assoc, zero_comp, comp_zero, smul_zero, add_zero, zero_add,
    SplitCx.toQuot_f, dualDesuspIso_hom_f, desuspMap_f]
  rw [claimA_t1, claimA_t2 _ _ _ (w := r), claimA_t3]
  simp only [XIsoOfEq_rfl, Iso.refl_hom, id_comp, HomologicalComplex.units_smul_f_apply]
  have hs₁ : (r - 1 + 1).negOnePow * (N + r).negOnePow = N.negOnePow := by
    rw [← Int.negOnePow_add, Int.negOnePow_eq_iff]
    exact ⟨r, by ring⟩
  have hs₂ : ((r - 1) * N).negOnePow * (r * (N + 1 - r)).negOnePow = N.negOnePow := by
    rw [← Int.negOnePow_add, Int.negOnePow_eq_iff]
    have e : (r - 1) * N + r * (N + 1 - r) - N = 2 * (r * N - N) - r * (r - 1) := by ring
    rw [e]
    exact (even_two_mul _).sub (Int.even_mul_pred_self r)
  have tot (x : ℤ) : (D.σ x).πE ≫ (D.σ x).ιE + (D.σ x).πU ≫ (D.σ x).ιU = 𝟙 _ := (D.σ x).total
  simp only [smul_neg, neg_neg, smul_smul, hs₁, hs₂, ← smul_add]
  congr 1
  have key : (D.σ (N + 1 - r)).πU ≫ (D.σ (N + 1 - r)).ιU ≫ P.φ.f r ≫ (D.σ r).πE ≫ (D.σ r).ιE +
      (D.σ (N + 1 - r)).πU ≫ (D.σ (N + 1 - r)).ιU ≫ P.φ.f r ≫ (D.σ r).πU ≫ (D.σ r).ιU =
      (D.σ (N + 1 - r)).πU ≫ (D.σ (N + 1 - r)).ιU ≫ P.φ.f r := by
    simp only [← comp_add, tot, comp_id]
  rw [add_assoc, key]
  simp only [← assoc, ← add_comp, tot, id_comp]

/-- **The comparison map carries the union structure to `(-1)^N φ`.** -/
def cutConj : Homotopy (dualHom A.cz.inv (N + 1) (cutCmp S hp hN) ≫
    unionφ (lowerPair S hp hN).toPairOn (upperOn S hp hN) ≫ cutCmp S hp hN) (N.negOnePow • P.φ) :=
  pushHomotopy (cutCmp S hp hN) (truncEquiv S hp hN).g (cutW S hp hN) D.thom.bdJ D.jPlus D.φq
    (-D.inclS) D.thom.bdRel.hom (D.deltaPlus hp).hom (glueHd hp)
    (truncEquiv S hp hN).pg rfl rfl (fun _ _ ↦ rfl)
    (fun i k ↦ by
      change ((dualHom A.cz.inv N D.jPlus).f i ≫
        ((D.rawUpperPair hp).bdW (truncEquiv S hp hN)).hom i k ≫ D.jPlus.f k) +
          (D.deltaPlus hp).hom i k = _
      rw [upper_bdW_hom, cutW_hom]
      simp)
    (by simp only [Glue.ιW, cutCmp, assoc]; erw [homotopyCofiber.inr_desc]; simp [cmpα])
    (by simp only [Glue.ιY, cutCmp, assoc]; erw [homotopyCofiber.inr_desc]; simp [cmpα])
    (fun i k ↦ by
      rw [Glue.K'_hom, cutCmp, inrCompHomotopy_hom_desc_hom]
      rfl)
    _ (cut_rawFam hp)

end Conj

/-! ### The comparison map is a Kar equivalence -/

section KarEquiv

variable (S : D.Sec) (hp : P.p = 𝟙 _) (hN : 0 ≤ N)

/-- `D_⁻ ⊕ D_⁺` with its two inclusions. -/
abbrev cutS : ChainComplex A.cz ℤ := Glue.S (lowerPair S hp hN).toPairOn (upperOn S hp hN)

/-- The raw (untruncated) union map `u = (j⁻, j⁺) : ∂T ⟶ T^{N+1-*} ⊕ S`. -/
abbrev rawU : D.thom.bdC ⟶ cutS S hp hN := D.thom.bdJ ≫ sumInl _ + D.jPlus ≫ sumInr _

lemma rawU_cmpα : rawU S hp hN ≫ cmpα S hp hN = D.thom.bdJ ≫ D.φq + D.jPlus ≫ (-D.inclS) := by
  simp [cmpα, add_comp, comp_add]

/-- The raw comparison map `Cone(u) ⟶ C`. -/
def rawCmp : cone (rawU S hp hN) ⟶ P.C :=
  desc _ (cmpα S hp hN) (homotopyCongr (glueHd hp) (rawU_cmpα S hp hN).symm rfl)

lemma g_rawU : (truncEquiv S hp hN).g ≫ rawU S hp hN =
    Glue.u (σU _) (lowerPair S hp hN).toPairOn (upperOn S hp hN) ≫ 𝟙 _ := by
  rw [comp_id]
  simp only [Glue.u, Glue.β, Glue.jY, comp_add]
  change _ = (truncIdem S ≫ (truncEquiv S hp hN).g ≫ D.thom.bdJ) ≫ _ + _
  rw [(truncEquiv S hp hN).pg_assoc,
    show (upperOn S hp hN).j = (truncEquiv S hp hN).g ≫ D.jPlus from rfl]
  simp only [assoc]

lemma cutCmp_eq : cutCmp S hp hN =
    coneMap (truncEquiv S hp hN).g (𝟙 _) (g_rawU S hp hN) ≫ rawCmp S hp hN := by
  ext n : 1
  apply ext_from_X (Glue.u (σU _) (lowerPair S hp hN).toPairOn (upperOn S hp hN)) (n - 1) n
    (by simp)
  · simp [cutCmp, rawCmp, cmpHd]
  · simp [cutCmp, rawCmp]

lemma lowerPair_pD : (lowerPair S hp hN).pD = 𝟙 _ := by
  change dualHom A.cz.inv (N + 1) D.thom.p = 𝟙 _
  rw [D.thom_p, D.pT_eq_id hp]
  exact dualHom_id _ _ _

lemma cut_pS : Glue.pS (lowerPair S hp hN).toPairOn (upperOn S hp hN) = 𝟙 _ := by
  ext r : 1
  change (sumFst _ ≫ (lowerPair S hp hN).pD ≫ sumInl _ + sumSnd _ ≫ 𝟙 _ ≫ sumInr _).f r = _
  rw [lowerPair_pD]
  simp only [Glue.bS, add_f_apply, comp_f, sumFst_f, sumInl_f, sumSnd_f, sumInr_f, id_f,
    BinaryBiproduct.bicone_fst, BinaryBiproduct.bicone_inl, BinaryBiproduct.bicone_snd,
    BinaryBiproduct.bicone_inr, id_comp]
  exact biprod.total

lemma isKarEquiv_coneMap_g : IsKarEquiv (cutUnion' S hp hN).p (𝟙 _)
    (coneMap (truncEquiv S hp hN).g (𝟙 _) (g_rawU S hp hN)) := by
  have hpS := cut_pS S hp hN
  have em : IsKarEquiv (truncIdem S) (𝟙 _) (truncEquiv S hp hN).g := by
    have h := (truncEquiv S hp hN).symm.isKarEquiv
    change IsKarEquiv _ _ (truncEquiv S hp hN).g at h
    have key : ∀ (q g : D.thom.bdC ⟶ D.thom.bdC), q = 𝟙 _ → IsKarEquiv (truncIdem S) q g →
        IsKarEquiv (truncIdem S) (𝟙 _) g := fun _ _ hq h ↦ hq ▸ h
    exact key _ _ (D.bdP_eq_id hp) h
  have h := isKarEquiv_coneMap (j := Glue.u (σU _) (lowerPair S hp hN).toPairOn (upperOn S hp hN))
    (j' := rawU S hp hN) (pB := truncIdem S)
    (pD := Glue.pS (lowerPair S hp hN).toPairOn (upperOn S hp hN)) (pB' := 𝟙 _) (pD' := 𝟙 _)
    (truncIdem_idem S hp hN) (Glue.pS_idem _ _) (by simp) (by simp)
    (by
      have := Glue.u_pS (σU _) (lowerPair S hp hN).toPairOn (upperOn S hp hN)
      rw [hpS, comp_id] at this ⊢
      exact this) (by simp)
    (by simp) (by rw [hpS]; simp) (g_rawU S hp hN) em (by rw [hpS]; exact
      (KarHtpyEquiv.refl (Category.comp_id _)).isKarEquiv)
  rwa [coneMap_id] at h

/-- `ι_S : S ⟶ Cone(u)`. -/
abbrev rawI : D.subC ⟶ cone (rawU S hp hN) :=
  sumInr (Glue.bS (lowerPair S hp hN).toPairOn (upperOn S hp hN)) ≫ inr (rawU S hp hN)

lemma rawU_sumFst : rawU S hp hN ≫ sumFst _ = D.thom.bdJ := by
  simp [rawU, add_comp]

/-- `Cone(u) ⟶ Cone(j⁻)`, forgetting `S`. -/
abbrev rawN : cone (rawU S hp hN) ⟶ cone D.thom.bdJ :=
  coneMap (𝟙 _) (sumFst _) (by rw [id_comp, rawU_sumFst])

/-- The degreewise split sequence `S ⟶ Cone(u) ⟶ Cone(j⁻)`. -/
def rawSplit : DegreewiseSplit (rawI S hp hN) (rawN S hp hN) where
  t n := sndX (rawU S hp hN) n ≫ (sumSnd _).f n
  s n := fstX D.thom.bdJ n (n - 1) (by simp) ≫ inlX (rawU S hp hN) (n - 1) n (by simp) +
    sndX D.thom.bdJ n ≫ (sumInl _).f n ≫ inrX (rawU S hp hN) n
  it n := by simp [Glue.bS]
  sq n := by
    apply ext_from_X D.thom.bdJ (n - 1) n (by simp)
    · simp [inlX_coneMap_f]
    · simp [Glue.bS]
  total n := by
    apply ext_from_X (rawU S hp hN) (n - 1) n (by simp)
    · simp [inlX_coneMap_f]
    · simp only [Glue.bS, comp_add, inrX_sndX_assoc, comp_f, sumInr_f, inr_f, assoc,
        inrX_coneMap_f_assoc, sumFst_f, inrX_fstX_assoc, zero_comp, inrX_sndX_assoc, comp_zero,
        zero_add, comp_id, sumSnd_f, sumInl_f]
      rw [← assoc, ← assoc, ← add_comp]
      erw [bicone_total']
      exact (id_comp _).trans (comp_id _).symm

/-- The degreewise split sequence `S ⟶ C ⟶ T` (with `-ι_S`). -/
def cutSplitNeg : DegreewiseSplit (-D.inclS) D.q where
  t n := -(D.σ n).πU
  s n := (D.σ n).ιE
  it n := by
    simp only [neg_f_apply, Preadditive.neg_comp_neg, SplitCx.fromSub_f]
    exact (D.σ n).ιU_πU
  sq n := (D.σ n).ιE_πE
  total n := by
    simp only [neg_f_apply, Preadditive.neg_comp_neg, SplitCx.fromSub_f, SplitCx.toQuot_f]
    exact (add_comm _ _).trans (D.σ n).total

include hp in
lemma thom_coneIdem : D.thom.coneIdem = 𝟙 _ := by
  ext n : 1
  apply ext_from_X D.thom.bdJ (n - 1) n (by simp)
  · simp [inlX_coneMap_f, D.bdP_eq_id hp]
  · simp [D.pT_eq_id hp]

/-- `Cone(j⁻) ≃ T` via `-π`. -/
def coneπEquiv : HomotopyEquiv (cone D.thom.bdJ) D.thomC where
  hom := -D.thom.coneπ
  inv := -D.thom.coneι
  homotopyHomInvId := homotopyCongr D.thom.coneHomotopy.symm
    (by rw [thom_coneIdem hp, id_comp, Preadditive.neg_comp_neg]) (thom_coneIdem hp)
  homotopyInvHomId := Homotopy.ofEq (by rw [Preadditive.neg_comp_neg, SymComplex.coneι_coneπ]; rfl)

@[reassoc]
lemma ιE_cast_πE' {a b : ℤ} (h : a = b) :
    (D.σ a).ιE ≫ (P.C.XIsoOfEq h).hom ≫ (D.σ b).πE = (D.thomC.XIsoOfEq h).hom := by
  subst h; simp [Splitting.ιE_πE]

lemma rawN_coneπ : rawN S hp hN ≫ (coneπEquiv hp).hom = rawCmp S hp hN ≫ D.q := by
  ext n : 1
  apply ext_from_X (rawU S hp hN) (n - 1) n (by simp)
  · simp [coneπEquiv, rawCmp, glueHd_hom,
      D.glueHomotopy_hom (by simp : (ComplexShape.down ℤ).Rel n (n - 1)), glueHom]
    rw [ιE_cast_πE']
  · have := (D.σ n).ιU_πE
    simp [coneπEquiv, rawCmp, cmpα, Glue.bS]
    erw [this, comp_zero]

/-- The raw comparison `Cone(u) ⟶ C` is a homotopy equivalence (two-out-of-three on the ladder
`S ⟶ Cone(u) ⟶ Cone(j⁻)` over `S ⟶ C ⟶ T`). -/
def rawCmpEquiv : HomotopyEquiv (cone (rawU S hp hN)) P.C :=
  homotopyEquivMiddle (rawSplit S hp hN) cutSplitNeg (HomotopyEquiv.refl _) (coneπEquiv hp)
    (rawCmp S hp hN) (by simp [rawCmp, cmpα, HomotopyEquiv.refl]) (rawN_coneπ S hp hN)

lemma isKarEquiv_rawCmp : IsKarEquiv (𝟙 _) (𝟙 _) (rawCmp S hp hN) :=
  (isKarEquiv_id_iff _).mpr ⟨rawCmpEquiv S hp hN, rfl⟩

/-- **The comparison map is a Kar equivalence** `(X⁻ ∪ X⁺, p_∪) ≃ (C, 1)`. -/
lemma isKarEquiv_cutCmp : IsKarEquiv (cutUnion' S hp hN).p P.p (cutCmp S hp hN) := by
  rw [cutCmp_eq, hp]
  exact (isKarEquiv_coneMap_g S hp hN).comp (isKarEquiv_rawCmp S hp hN)
    (cutUnion' S hp hN).p_idem (by simp) (by simp)

lemma cutCmp_kar : (cutUnion' S hp hN).p ≫ cutCmp S hp hN ≫ P.p = cutCmp S hp hN := by
  obtain ⟨g, hg, ⟨H₁⟩, ⟨H₂⟩⟩ := isKarEquiv_cutCmp S hp hN
  rw [hp, comp_id]
  change Glue.pU (σU _) (lowerPair S hp hN).toPairOn (upperOn S hp hN) ≫ cutCmp S hp hN = _
  rw [cutCmp_eq, ← assoc]
  congr 1
  ext n : 1
  apply ext_from_X (Glue.u (σU _) (lowerPair S hp hN).toPairOn (upperOn S hp hN)) (n - 1) n
    (by simp)
  · have e : (truncIdem S).f (n - 1) ≫ (truncEquiv S hp hN).g.f (n - 1) =
        (truncEquiv S hp hN).g.f (n - 1) := by rw [← comp_f, (truncEquiv S hp hN).pg]
    simp [inlX_coneMap_f, reassoc_of% e]
  · simp [cut_pS S hp hN]

end KarEquiv

/-! ### The cut union is homotopy isometric to `(-1)^N P` -/

section Main

variable (S : D.Sec) (hp : P.p = 𝟙 _) (hN : 0 ≤ N)

lemma nonempty_isometry_of_conj {M : ℤ} {Q R : SymPoincare A.cz.inv M} (f : Q.C ⟶ R.C)
    (hf : Q.p ≫ f ≫ R.p = f) (he : IsKarEquiv Q.p R.p f)
    (H : Homotopy (dualHom A.cz.inv M f ≫ Q.φ ≫ f) R.φ) : Nonempty (Q.HomotopyIsometry R) := by
  obtain ⟨g, hg, ⟨H₁⟩, ⟨H₂⟩⟩ := he
  exact ⟨⟨f, g, hf, hg, H₂, H₁, H⟩⟩

/-- **`cutUnion ≃ (-1)^N P`**, even case. -/
theorem nonempty_cutUnion_isometry_of_even (h : Even N) :
    Nonempty ((cutUnion S hp hN).HomotopyIsometry P) := by
  rw [cutUnion_eq]
  refine nonempty_isometry_of_conj (cutCmp S hp hN) (cutCmp_kar S hp hN)
    (isKarEquiv_cutCmp S hp hN) (homotopyCongr (cutConj S hp hN) rfl ?_)
  rw [Int.negOnePow_even N h, one_smul]

/-- **`cutUnion ≃ (-1)^N P`**, odd case. -/
theorem nonempty_cutUnion_isometry_of_odd (h : Odd N) :
    Nonempty ((cutUnion S hp hN).HomotopyIsometry P.neg) := by
  rw [cutUnion_eq]
  refine nonempty_isometry_of_conj (cutCmp S hp hN) (cutCmp_kar S hp hN)
    (isKarEquiv_cutCmp S hp hN) (homotopyCongr (cutConj S hp hN) rfl ?_)
  rw [Int.negOnePow_odd N h, Units.neg_smul, one_smul]

/-- **The class of the cut union**: `[X⁻ ∪ X⁺] = (-1)^N [P]` in `Lconc (C_ℤ A) (N + 1)`. -/
theorem cls_cutUnion :
    Lconc.cls (cutUnion S hp hN) = ((N.negOnePow : ℤˣ) : ℤ) • Lconc.cls P := by
  rcases Int.even_or_odd N with h | h
  · obtain ⟨e⟩ := nonempty_cutUnion_isometry_of_even S hp hN h
    rw [Lconc.cls_eq_of_isometry e, Int.negOnePow_even N h]
    simp
  · obtain ⟨e⟩ := nonempty_cutUnion_isometry_of_odd S hp hN h
    rw [Lconc.cls_eq_of_isometry e, Int.negOnePow_odd N h, Lconc.cls_neg]
    simp

end Main

end CutData

end CZ

end

end HSFormal.LTheory
