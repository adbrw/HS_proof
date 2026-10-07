import HSFormal.LTheory.Model.UnionRelLadder

/-!
# The U-turn null-cobordism

For pairs `X` on `Q = B ⊕ -B` and `Z` on `-B`, the U-turn `W' = D_X ∪_{C_Q} D_Z` is a
null-cobordism of `(X ∪ (Z ⊕ -Z)) ⊕ -(X ∪ Cyl)` (`UTurn.nullPair`), so that
`[X ∪ (Z ⊕ -Z)] = [X ∪ Cyl]` in `Lconc` (`UTurn.cls_union_uturn`): the class of
`X ∪ (Z ⊕ -Z)` does not depend on `Z`.

The relative duality map is a Kar equivalence:
* with the transposed boundary structure `φᵀ_∂`, by **P2** (`KarSplit.isKarEquiv_relDuality`)
  and the `λ`-ladder (`Model/UnionRelLadder.lean`);
* with the symmetrized structure `φ_∂`, by transport along `φ_∂ ≃ φᵀ_∂` (`UTurn.Wd`), whose
  pushforward `j^* W j` vanishes (`UTurn.jj_Wd_jj`).
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex homotopyCofiber
  HSFormal.Compression

noncomputable section

attribute [local implicit_reducible] PairOn.toPair SymPair.neg SymPair.toPairOn PairOn.union PairOn.glue
  SymPair.closedOfIsZero IsStrictSymm PairOn.sum SymPoincare.HomotopyIsometry.cylinder

universe v u

variable {V : Type u} [Category.{v} V] [Preadditive V] {J : StrictInvolution V} {N : ℤ}

variable [HasBinaryBiproducts V] [HasFiniteBiproducts V] [Linear ℚ V]

namespace UTurn

open Union

variable {B : SymPoincare J N} {b : ∀ r, BinaryBicone (B.C.X r) (B.C.X r)} (Z : PairOn B.neg)
  (X : PairOn (Q b))

/-! ### Idempotents and Kar conditions -/

lemma pSW_idem : pSW Z X ≫ pSW Z X = pSW Z X := by
  ext n : 1
  apply biprod.hom_ext' <;> simp [pSW]

lemma pW_idem : pW Z X ≫ pW Z X = pW Z X := coneMap_idem _ (Q b).p_idem (pSW_idem Z X)

lemma pBc_idem : pBc b Z ≫ pBc b Z = pBc b Z := by
  refine coneMap_idem _ (Q b).p_idem ?_
  ext n : 1
  apply biprod.hom_ext' <;> simp [pSB]

lemma pcX_idem : pcX X ≫ pcX X = pcX X := coneMap_idem _ (Q b).p_idem X.pD_idem

lemma pcZ_idem : pcZ Z ≫ pcZ Z = pcZ Z := coneMap_idem _ B.neg.p_idem Z.pD_idem

lemma iK_kar : X.pD ≫ iK Z X ≫ pK Z X = iK Z X := by
  ext n
  simp [iK, pSK]

lemma qK_kar : pK Z X ≫ qK Z X ≫ pBc b Z = qK Z X := by
  rw [qK, coneMap_comp, coneMap_comp]
  apply coneMap_ext'
  · simp
  · ext n : 1
    apply biprod.hom_ext'
    · simp [pSK]
    · apply biprod.hom_ext' <;> simp [pSK, pSB]

lemma ιZk_kar : Z.pD ≫ ιZk Z X ≫ pW Z X = ιZk Z X := by
  ext n
  simp [ιZk, pSW]

lemma πW_kar : pW Z X ≫ πW Z X ≫ pcX X = πW Z X := by
  rw [πW, coneMap_comp, coneMap_comp]
  apply coneMap_ext'
  · simp
  · ext n : 1
    apply biprod.hom_ext' <;> simp [pSW]

lemma c_kar : pcZ Z ≫ c Z ≫ pBc b Z = c Z := by
  rw [c, coneMap_comp, coneMap_comp]
  apply coneMap_ext'
  · simp [c₀, SymPoincare.neg]
  · ext n : 1
    simp [c₁, pSB]

lemma relDuality_Z_kar :
    dualHom J (N + 1) (pcZ Z) ≫ relDuality Z.δφ ≫ Z.pD = relDuality Z.δφ :=
  relDuality_kar Z.δφ Z.pD_idem _ Z.j_comp_pD B.neg.dualHom_p_comp_φ Z.δφ_kar

lemma relDuality_X_kar :
    dualHom J (N + 1) (pcX X) ≫ relDuality X.δφ ≫ X.pD = relDuality X.δφ :=
  relDuality_kar X.δφ X.pD_idem _ X.j_comp_pD (Q b).dualHom_p_comp_φ X.δφ_kar

lemma lL_kar : dualHom J (N + 1) (pBc b Z) ≫ lL Z ≫ Z.pD = lL Z := by
  have h1 : c Z ≫ pBc b Z = c Z := kar_right (pBc_idem Z) (c_kar Z)
  have h2 : relDuality Z.δφ ≫ Z.pD = relDuality Z.δφ := kar_right Z.pD_idem (relDuality_Z_kar Z)
  simp only [lL, assoc]
  rw [← assoc (dualHom J (N + 1) (pBc b Z)), ← dualHom_comp, h1, h2]

lemma TΨ_kar : dualHom J (N + 1) X.pD ≫ TΨ X ≫ pcX X = TΨ X :=
  transposeHom_kar (relDuality_X_kar X)

/-- `l = c^* Ψ_Z` is a Kar equivalence. -/
lemma isKarEquiv_lL : IsKarEquiv (dualHom J (N + 1) (pBc b Z)) Z.pD (lL Z) :=
  (isKarEquiv_c Z).dualHom.comp Z.poincare (dualHom_idem (pBc_idem Z)) (dualHom_idem (pcZ_idem Z))
    Z.pD_idem

/-- `TΨ_X` is a Kar equivalence. -/
lemma isKarEquiv_TΨ : IsKarEquiv (dualHom J (N + 1) X.pD) (pcX X) (TΨ X) :=
  X.poincare.transposeHom (pcX_idem X) X.pD_idem

/-- **The middle map `λ` is a Kar equivalence** (the `λ`-ladder). -/
theorem isKarEquiv_lamT : IsKarEquiv (dualHom J (N + 1) (pK Z X)) (pW Z X) (lamT Z X) :=
  isKarEquiv_middle (dualHom_idem (pBc_idem Z)) (dualHom_idem (pK_idem Z X))
    (dualHom_idem X.pD_idem) Z.pD_idem (pW_idem Z X) (pcX_idem X) (dualHom_kar (qK_kar Z X))
    (dualHom_kar (iK_kar Z X)) (ιZk_kar Z X) (πW_kar Z X) ((splitK Z X).dual J (N + 1))
    (splitW Z X) (lL_kar Z) (KarSplit.lam_kar _ _ _ (pW_idem Z X) (jj_kar Z X) _ _) (TΨ_kar X)
    (left_square Z X) (right_square Z X) (isKarEquiv_lL Z) (isKarEquiv_TΨ X)

/-! ### P2: Poincaré duality with the transposed structure -/

lemma pK_kK_kar_a : pK Z X ≫ ka Z X ≫ Glue.pU (σ (Q b)) X (uturn b Z) = ka Z X := by
  rw [ka, coneMap_comp, coneMap_comp]
  apply coneMap_ext'
  · simp
  · ext n : 1
    apply biprod.hom_ext'
    · simp [pSK, nka, Glue.pS]
    · apply biprod.hom_ext' <;> simp [pSK, pSB, nka, Glue.pS, mB, inrD, comp_sub, sub_comp]
      all_goals rfl

lemma pK_kK_kar_b : pK Z X ≫ kb Z X ≫ Glue.pU (σ (Q b)) X (cyl b) = kb Z X := by
  rw [kb, coneMap_comp, coneMap_comp]
  apply coneMap_ext'
  · simp [SymPoincare.sum, add_comp, comp_add]
    abel
  · ext n : 1
    apply biprod.hom_ext'
    · simp [pSK, nkb, Glue.pS]
    · apply biprod.hom_ext' <;> simp [pSK, pSB, nkb, Glue.pS, cyl_pD]

lemma inl_bd_p : sumInl (bb Z X) ≫ (bd Z X).p =
    Glue.pU (σ (Q b)) X (uturn b Z) ≫ sumInl (bb Z X) := by
  ext n : 1; exact inl_bd_p_f Z X n

lemma inr_bd_p : sumInr (bb Z X) ≫ (bd Z X).p = Glue.pU (σ (Q b)) X (cyl b) ≫ sumInr (bb Z X) := by
  ext n : 1; exact inr_bd_p_f Z X n

lemma kK_kar : pK Z X ≫ kK Z X ≫ (bd Z X).p = kK Z X := by
  simp (config := {proj := false}) only [kK, add_comp, comp_add, assoc, inl_bd_p, inr_bd_p]
  rw [reassoc_of% (pK_kK_kar_a Z X), reassoc_of% (pK_kK_kar_b Z X)]

lemma dualHom_bd_p_phiD : dualHom J (N + 1) (bd Z X).p ≫ phiD Z X = phiD Z X := by
  have ha : dualHom J (N + 1) (bd Z X).p ≫ dualHom J (N + 1) (sumInl (bb Z X)) =
      dualHom J (N + 1) (sumInl (bb Z X)) ≫
        dualHom J (N + 1) (Glue.pU (σ (Q b)) X (uturn b Z)) := by
    rw [← dualHom_comp, inl_bd_p, dualHom_comp]
  have hb : dualHom J (N + 1) (bd Z X).p ≫ dualHom J (N + 1) (sumInr (bb Z X)) =
      dualHom J (N + 1) (sumInr (bb Z X)) ≫ dualHom J (N + 1) (Glue.pU (σ (Q b)) X (cyl b)) := by
    rw [← dualHom_comp, inr_bd_p, dualHom_comp]
  rw [phiD, comp_sub, reassoc_of% ha, reassoc_of% hb, reassoc_of% (phiT_kar X (uturn b Z)),
    reassoc_of% (phiT_kar X (cyl b))]

/-- **P2 + the `λ`-ladder**: the U-turn is Poincaré for the transposed boundary structure. -/
theorem poincareT : IsKarEquiv (dualHom J (N + 1 + 1) (coneMap (bd Z X).p (pW Z X)
    (comm_of_kar (bd Z X).p_idem (pW_idem Z X) (jj_kar Z X)))) (pW Z X)
    (relDuality (Homotopy.ofEq (jj_phiD_jj Z X))) :=
  (split Z X).isKarEquiv_relDuality (pK_idem Z X) (bd Z X).p_idem (pW_idem Z X) (kK_kar Z X)
    (jj_kar Z X) (phiD Z X) (jj_phiD_jj Z X) _ (dualHom_bd_p_phiD Z X) _ (fun _ _ ↦ rfl)
    (isKarEquiv_lamT Z X)

/-! ### Transport to the symmetrized structure -/

lemma sandL_eq (x y : ℤ) :
    (dualHom J N (fa Z X)).f x ≫ L X (uturn b Z) x y ≫ (fa Z X).f y =
      (dualHom J N (fb Z X)).f x ≫ L X (cyl b) x y ≫ (fb Z X).f y := by
  simp only [L, conjL, Linear.smul_comp, Linear.comp_smul, dualHomotopy_hom, dualHom_f, assoc,
    Linear.comp_units_smul, Linear.units_smul_comp, star_fa_star_K'_assoc, star_fb_star_K'_assoc,
    K'_fa_f, K'_fb_f]

lemma sandUnion (r r' : ℤ) :
    (dualHom J (N + 1) (fa Z X)).f r ≫ (unionPhiTHomotopy X (uturn b Z)).hom r r' ≫
        (fa Z X).f r' =
      (dualHom J (N + 1) (fb Z X)).f r ≫ (unionPhiTHomotopy X (cyl b)).hom r r' ≫
        (fb Z X).f r' := by
  by_cases h : (ComplexShape.down ℤ).Rel r' r
  · rw [unionPhiTHomotopy_hom _ _ _ _ h, unionPhiTHomotopy_hom _ _ _ _ h]
    simp only [dualHom_f, assoc]
    rw [star_f_XIsoOfEq_assoc, star_f_XIsoOfEq_assoc, ← dualHom_f, ← dualHom_f, sandL_eq]
  · rw [Homotopy.zero _ r r' h, Homotopy.zero _ r r' h, zero_comp, comp_zero, zero_comp,
      comp_zero]

/-- `φ_∂ ≃ φᵀ_∂`, blockwise. -/
def Wd : Homotopy (bd Z X).φ (phiD Z X) :=
  homotopyCongr
    ((((unionPhiTHomotopy X (uturn b Z)).compRight (sumInl (bb Z X))).compLeft
        (dualHom J (N + 1) (sumInl (bb Z X)))).add
      ((((unionPhiTHomotopy X (cyl b)).compRight (sumInr (bb Z X))).compLeft
        (dualHom J (N + 1) (sumInr (bb Z X)))).smul (-1 : ℤ)))
    (by simp [SymPoincare.sum, SymPoincare.neg])
    (by simp [phiD, sub_eq_add_neg])

lemma jj_Wd_jj (r r' : ℤ) :
    (dualHom J (N + 1) (jj Z X)).f r ≫ (Wd Z X).hom r r' ≫ (jj Z X).f r' = 0 := by
  have ea : (dualHom J (N + 1) (jj Z X)).f r ≫ (dualHom J (N + 1) (sumInl (bb Z X))).f r =
      (dualHom J (N + 1) (fa Z X)).f r := by rw [← comp_f, ← dualHom_comp, inl_jj]
  have eb : (dualHom J (N + 1) (jj Z X)).f r ≫ (dualHom J (N + 1) (sumInr (bb Z X))).f r =
      (dualHom J (N + 1) (fb Z X)).f r := by rw [← comp_f, ← dualHom_comp, inr_jj]
  simp only [Wd, homotopyCongr_hom, Homotopy.add_hom, Homotopy.compLeft_hom,
    Homotopy.compRight_hom, Homotopy.smul, Pi.add_apply, comp_add, add_comp, assoc,
    Linear.smul_comp, Linear.comp_smul, neg_comp, comp_neg, reassoc_of% ea, reassoc_of% eb,
    inl_jj_f, inr_jj_f, sandUnion, neg_one_smul, add_neg_cancel]

/-- **The U-turn is Poincaré.** -/
theorem poincare : IsKarEquiv (dualHom J (N + 1 + 1) (coneMap (bd Z X).p (pW Z X)
    (comm_of_kar (bd Z X).p_idem (pW_idem Z X) (jj_kar Z X)))) (pW Z X)
    (relDuality (Homotopy.ofEq (jj_bd_jj Z X))) :=
  (poincareT Z X).of_homotopy (transportRelDualityHomotopy (Wd Z X)
    (Homotopy.ofEq (jj_bd_jj Z X)) (Homotopy.ofEq (jj_phiD_jj Z X))
    (fun r r' ↦ by rw [jj_Wd_jj]; simp [Homotopy.ofEq])).symm

lemma pW_support : SupportedIn (pW Z X) 0 (N + 1 + 1) := by
  intro r hr
  rw [coneMap_f _ r (r - 1) (down_rel_pred r), (Q b).support (r - 1) (by omega)]
  simp [pSW, X.support r (by omega), Z.support r (by omega)]

/-- **The U-turn null-cobordism** of `(X ∪ (Z ⊕ -Z)) ⊕ -(X ∪ Cyl)`. -/
def nullPair : SymPair J (N + 1) where
  bd := bd Z X
  D := W' Z X
  pD := pW Z X
  pD_idem := pW_idem Z X
  support := pW_support Z X
  j := jj Z X
  j_kar := jj_kar Z X
  δφ := Homotopy.ofEq (jj_bd_jj Z X)
  δφ_kar r r' := by simp [Homotopy.ofEq]
  symm := by
    rw [IsSymmHomotopy, transposeHomotopy_hom]
    funext a b
    simp [Homotopy.ofEq, transposeHomFamily]
  poincare := poincare Z X

theorem nullCobordant_bd : NullCobordant (bd Z X) := ⟨nullPair Z X, rfl⟩

end UTurn

/-- **The U-turn relation**: `[X ∪ (Z ⊕ -Z)] = [X ∪ Cyl]`; in particular the class of
`X ∪ (Z ⊕ -Z)` does not depend on `Z`. -/
theorem UTurn.cls_union_uturn {A : InvCat} {N : ℤ} {B : SymPoincare A.inv N}
    {b : ∀ r, BinaryBicone (B.C.X r) (B.C.X r)} (Z : PairOn B.neg) (X : PairOn (UTurn.Q b)) :
    Lconc.cls (X.union (UTurn.uturn b Z)) = Lconc.cls (X.union (UTurn.cyl b)) := by
  have h := Lconc.cls_eq_zero (UTurn.nullCobordant_bd Z X)
  rw [UTurn.bd, Lconc.cls_sum, Lconc.cls_neg, ← sub_eq_add_neg, sub_eq_zero] at h
  exact h

/-- The class of `X ∪ (Z ⊕ -Z)` does not depend on `Z`. -/
theorem UTurn.cls_union_uturn_eq {A : InvCat} {N : ℤ} {B : SymPoincare A.inv N}
    {b : ∀ r, BinaryBicone (B.C.X r) (B.C.X r)} (Z Z' : PairOn B.neg) (X : PairOn (UTurn.Q b)) :
    Lconc.cls (X.union (UTurn.uturn b Z)) = Lconc.cls (X.union (UTurn.uturn b Z')) := by
  rw [UTurn.cls_union_uturn, UTurn.cls_union_uturn]

end

end HSFormal.LTheory
