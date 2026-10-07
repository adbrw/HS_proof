import HSFormal.LTheory.Model.LiftingClosedSubAux

/-!
# The trace cobordism of the relative boundary construction on a closed complex

For a closed `(N+1)`-dimensional Poincaré complex `Q` of an `InvCat` `A`, the face
`W = PairData.ofClosedZero Q` (a pair on the zero boundary) and any triad
`T : TriadOn W (PairData.zero zeroP)` (module 10, in **general degrees**: `p_E` supported in
`[0, N + 2]`, no connectivity), the trace `M = Σ⁻¹Cone(Φ_W)` of module 10 is the top of a raw
Poincaré pair

  `j = (i₀', i₁') : Q ⊕ -Z ⟶ M`, relative structure `0` (the triad cycle vanishes on the nose,
  `trace_cycle`),

whose boundary contains the **raw** new face `Z = (Z_D, p_Z, δφ_Z)` (`Z_D` lives in
`[-1, N + 2]`).  This is a `RawPair` (`unionRaw`).

**Poincaré duality** (`isKarEquiv_unionRaw`, Wall's two-out-of-three on a ladder): the dual of
the degreewise split sequence `Cone(i₁') ⟶ Cone(j) ⟶ Cone(Q ⟶ 0)` sits over the split sequence
`Σ⁻¹Cone(Q ⟶ 0) ⟶ M ⟶ E^{N+2-*}` of `M = Σ⁻¹Cone(Φ_W)`, with vertical maps `±φ_Q` (left),
the relative duality `Ψ` of `j` (middle) and `-i_T^*` (right; `i_T : E ≃ Cone(i₁')`,
`isKarEquiv_iT`).  The squares commute on the nose.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression
  homotopyCofiber

noncomputable section

namespace TriadOn

/-- The idempotent `p_Q ⊕ 0` of `Cone(Q ⟶ 0)`. -/
abbrev _root_.HSFormal.LTheory.SymPoincare.zconeIdem {A : InvCat} {N : ℤ} (Q : SymPoincare A.inv N) :
    zcone Q.C ⟶ zcone Q.C :=
  coneMap Q.p (0 : (HomologicalComplex.zero : ChainComplex A ℤ) ⟶ HomologicalComplex.zero)
    (by simp)

lemma _root_.HSFormal.LTheory.SymPoincare.zconeIdem_idem {A : InvCat} {N : ℤ}
    (Q : SymPoincare A.inv N) : Q.zconeIdem ≫ Q.zconeIdem = Q.zconeIdem :=
  coneMap_idem _ Q.p_idem (by simp)

/-- The left vertical map of the ladder, `-(±φ_Q) : (Cone(Q ⟶ 0))^{N+2-*} ⟶ Σ⁻¹Cone(Q ⟶ 0)`. -/
def _root_.HSFormal.LTheory.SymPoincare.zconeDual {A : InvCat} {N : ℤ} (Q : SymPoincare A.inv (N + 1)) :
    dualComplex A.inv (N + 1 + 1) (zcone Q.C) ⟶ desusp (zcone Q.C) :=
  -((zconeDualIso Q.C A.inv (N + 1)).hom ≫ Q.φ ≫ (zconeIso Q.C).hom)

lemma _root_.HSFormal.LTheory.SymPoincare.zconeDual_f {A : InvCat} {N : ℤ}
    (Q : SymPoincare A.inv (N + 1)) (r : ℤ) :
    Q.zconeDual.f r = (r + 1).negOnePow • A.inv.star (inlX (0 : Q.C ⟶ HomologicalComplex.zero) (N + 1 - r)
      (N + 1 + 1 - r) (down_rel_sub (N + 1) r)) ≫ Q.φ.f r ≫
        inlX (0 : Q.C ⟶ HomologicalComplex.zero) r (r + 1) (down_rel_succ r) := by
  simp [SymPoincare.zconeDual, Int.negOnePow_succ]

lemma _root_.HSFormal.LTheory.SymPoincare.zconeDualIso_conj {A : InvCat} {N : ℤ}
    (Q : SymPoincare A.inv (N + 1)) :
    (zconeDualIso Q.C A.inv (N + 1)).hom ≫ dualHom A.inv (N + 1) Q.p ≫
      (zconeDualIso Q.C A.inv (N + 1)).inv = dualHom A.inv (N + 1 + 1) Q.zconeIdem := by
  ext r
  simp only [comp_f, zconeDualIso_hom_f, zconeDualIso_inv_f, zconeDualIsoX_hom, zconeDualIsoX_inv,
    dualHom_f, Linear.units_smul_comp, Linear.comp_units_smul, smul_smul, Int.units_mul_self,
    one_smul, star_coneMap_f _ (N + 1 + 1 - r) (N + 1 - r) (down_rel_sub (N + 1) r), zero_f,
    A.inv.star_zero, zero_comp, comp_zero, add_zero]

lemma _root_.HSFormal.LTheory.SymPoincare.zconeIso_conj {A : InvCat} {N : ℤ}
    (Q : SymPoincare A.inv N) :
    (zconeIso Q.C).inv ≫ Q.p ≫ (zconeIso Q.C).hom = desuspMap Q.zconeIdem := by
  ext r
  simp [coneFst, coneMap_f _ (r + 1) r (down_rel_succ r)]

lemma _root_.HSFormal.LTheory.SymPoincare.isKarEquiv_zconeDual {A : InvCat} {N : ℤ}
    (Q : SymPoincare A.inv (N + 1)) :
    IsKarEquiv (dualHom A.inv (N + 1 + 1) Q.zconeIdem) (desuspMap Q.zconeIdem) Q.zconeDual := by
  have h := ((isPoincare_iff.mp Q.poincare).conjIso
    (zconeDualIso Q.C A.inv (N + 1)).symm).conjIsoRight (zconeIso Q.C)
  simp only [Iso.symm_inv, Iso.symm_hom, Q.zconeDualIso_conj, Q.zconeIso_conj] at h
  exact h.neg.of_eq (by simp [SymPoincare.zconeDual])

lemma _root_.HSFormal.LTheory.SymPoincare.zconeDual_kar {A : InvCat} {N : ℤ}
    (Q : SymPoincare A.inv (N + 1)) :
    dualHom A.inv (N + 1 + 1) Q.zconeIdem ≫ Q.zconeDual ≫ desuspMap Q.zconeIdem = Q.zconeDual := by
  rw [← Q.zconeDualIso_conj, ← Q.zconeIso_conj]
  simp only [SymPoincare.zconeDual, neg_comp, comp_neg, assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id_assoc, SymPoincare.dualHom_p_comp_φ_assoc, SymPoincare.φ_comp_p_assoc]

variable {A : InvCat} {N : ℤ} {Q : SymPoincare A.inv (N + 1)}
  (T : TriadOn (PairData.ofClosedZero Q) (PairData.zero (zeroP (J := A.inv) (N := N))))
  (hW : (PairData.ofClosedZero Q).IsPoincare)

lemma isZero_zeroP_C (r : ℤ) : IsZero ((zeroP (J := A.inv) (N := N)).C.X r) :=
  isZero_zeroP_X r

/-- The raw closed new face `(Z_D, p_Z, δφ_Z)` (supported in `[-1, N + 2]`). -/
abbrev Zr : RawSym A.inv (N + 1) := (T.relBdRaw hW).rawClosed isZero_zeroP_C

/-- The bicones of `Q ⊕ Z`. -/
abbrev bT (r : ℤ) : BinaryBicone (Q.C.X r) (T.ZD.X r) := BinaryBiproduct.bicone _ _

/-- The raw boundary `Q ⊕ -Z` of the trace. -/
abbrev Bu : RawSym A.inv (N + 1) := (RawSym.ofSymPoincare Q).sum (T.Zr hW).neg T.bT

/-- The boundary map `j = (i₀', i₁') : Q ⊕ Z ⟶ M`. -/
@[implicit_reducible]
def jU : sumComplex T.bT ⟶ T.MD := sumFst T.bT ≫ T.i₀' + sumSnd T.bT ≫ T.i₁'

@[reassoc (attr := simp)]
lemma sumInl_jU : sumInl T.bT ≫ T.jU = T.i₀' := by simp [jU]

@[reassoc (attr := simp)]
lemma sumInr_jU : sumInr T.bT ≫ T.jU = T.i₁' := by simp [jU]

lemma Zr_φ_f (r : ℤ) : (T.Zr hW).φ.f r = T.R (N + 1 - r) r (by omega) ≫ T.pZ.f r := by
  simp [RelRawPair.rawClosed, relTop_δφZ]

/-- **The triad cycle of the trace vanishes**: `j (φ_Q ⊕ -φ_Z) j^* = 0`. -/
lemma jU_cycle : dualHom A.inv (N + 1) T.jU ≫ (T.Bu hW).φ ≫ T.jU = 0 := by
  have e₁ : dualHom A.inv (N + 1) T.jU ≫ dualHom A.inv (N + 1) (sumInl T.bT) =
      dualHom A.inv (N + 1) T.i₀' := by rw [← dualHom_comp, sumInl_jU]
  have e₂ : dualHom A.inv (N + 1) T.jU ≫ dualHom A.inv (N + 1) (sumInr T.bT) =
      dualHom A.inv (N + 1) T.i₁' := by rw [← dualHom_comp, sumInr_jU]
  simp only [Bu, RawSym.sum_φ, RawSym.ofSymPoincare_φ, RawSym.neg_φ, comp_add, add_comp, assoc,
    sumInl_jU, sumInr_jU, reassoc_of% e₁, reassoc_of% e₂]
  ext r
  have h := T.trace_cycle (N + 1 - r) r (by omega)
  simp only [XIsoOfEq_rfl, Iso.refl_hom, id_comp, PairData.relTop_ofClosedZero] at h
  simp only [add_f_apply, comp_f, dualHom_f, neg_f_apply, Zr_φ_f, zero_f, neg_comp, comp_neg,
    assoc, h]
  abel

@[reassoc (attr := simp)]
lemma p_i₀' : Q.p ≫ T.i₀' = T.i₀' := T.pD_i₀'

lemma jU_kar : (T.Bu hW).p ≫ T.jU ≫ T.pM = T.jU := by
  simp [Bu, jU, add_comp, comp_add]

/-- The relative structure `0` of the trace. -/
@[implicit_reducible]
def δφU : Homotopy (dualHom A.inv (N + 1) T.jU ≫ (T.Bu hW).φ ≫ T.jU) 0 :=
  Homotopy.ofEq (T.jU_cycle hW)

/-! #### The ladder -/

/-- `Cone(i₁') ⟶ Cone(j)`, induced by `Z ⊂ Q ⊕ Z`. -/
@[implicit_reducible]
def ιU : cone T.i₁' ⟶ cone T.jU := coneMap (sumInr T.bT) (𝟙 T.MD) (by simp)

/-- `Cone(j) ⟶ Cone(Q ⟶ 0)`, induced by `Q ⊕ Z ⟶ Q`. -/
@[implicit_reducible]
def πU : cone T.jU ⟶ zcone Q.C := coneMap (sumFst T.bT) 0 (by simp)

/-- The idempotent `(p_Q ⊕ p_Z) ⊕ p_M` of `Cone(j)`. -/
abbrev eU : cone T.jU ⟶ cone T.jU :=
  coneMap (T.Bu hW).p T.pM (comm_of_kar (T.Bu hW).p_idem T.pM_idem (T.jU_kar hW))

lemma eU_idem : T.eU hW ≫ T.eU hW = T.eU hW := coneMap_idem _ (T.Bu hW).p_idem T.pM_idem

/-- The degreewise split sequence `0 ⟶ Cone(i₁') ⟶ Cone(j) ⟶ Cone(Q ⟶ 0) ⟶ 0`. -/
def splitU : DegreewiseSplit T.ιU T.πU where
  t n := fstX T.jU n (n - 1) (down_rel_pred n) ≫ (T.bT (n - 1)).snd ≫
      inlX T.i₁' (n - 1) n (down_rel_pred n) + sndX T.jU n ≫ inrX T.i₁' n
  s n := fstX (0 : Q.C ⟶ HomologicalComplex.zero) n (n - 1) (down_rel_pred n) ≫
    (T.bT (n - 1)).inl ≫ inlX T.jU (n - 1) n (down_rel_pred n)
  it n := by
    apply ext_from_X T.i₁' (n - 1) n (down_rel_pred n) <;> simp [ιU]
  sq n := by
    apply ext_from_X (0 : Q.C ⟶ HomologicalComplex.zero) (n - 1) n (down_rel_pred n)
    · simp [πU]
    · exact (isZero_zero A).eq_of_src _ _
  total n := by
    apply ext_from_X T.jU (n - 1) n (down_rel_pred n)
    · simp only [ιU, πU, comp_add, add_comp, inlX_fstX_assoc, inlX_sndX_assoc, zero_comp,
        add_zero, assoc, inlX_coneMap_f, sumInr_f, inlX_coneMap_f_assoc, sumFst_f,
        BinaryBiproduct.bicone_fst, BinaryBiproduct.bicone_snd,
        BinaryBiproduct.bicone_inl, BinaryBiproduct.bicone_inr]
      rw [← assoc, ← assoc, ← add_comp, add_comm (biprod.snd ≫ biprod.inr), biprod.total]
      exact (id_comp _).trans (comp_id _).symm
    · simp [ιU, πU]

lemma eMT_ιU : T.eMT ≫ T.ιU = T.ιU ≫ T.eU hW := by
  rw [ιU, coneMap_comp, coneMap_comp]
  exact coneMap_eq_of_eq _ _ (by simp [Bu]) (by simp)

lemma eU_πU : T.eU hW ≫ T.πU = T.πU ≫ Q.zconeIdem := by
  rw [πU, coneMap_comp, coneMap_comp]
  exact coneMap_eq_of_eq _ _ (by simp [Bu]) (by simp)

/-- The top row (before dualizing) as a Kar split sequence. -/
def karSplitU : KarSplit T.eMT (T.eU hW) Q.zconeIdem T.ιU T.πU :=
  KarSplit.ofDegreewise T.splitU T.eMT_idem (T.eU_idem hW) Q.zconeIdem_idem (T.eMT_ιU hW) (T.eU_πU hW)

/-! #### The squares -/

@[reassoc (attr := simp)]
lemma star_biprod_fst_inl (X Y : A) :
    A.inv.star (biprod.fst : X ⊞ Y ⟶ X) ≫ A.inv.star (biprod.inl : X ⟶ X ⊞ Y) = 𝟙 X := by
  rw [← A.inv.star_comp, biprod.inl_fst, A.inv.star_id]

@[reassoc (attr := simp)]
lemma star_biprod_fst_inr (X Y : A) :
    A.inv.star (biprod.fst : X ⊞ Y ⟶ X) ≫ A.inv.star (biprod.inr : Y ⟶ X ⊞ Y) = 0 := by
  rw [← A.inv.star_comp, biprod.inr_fst, A.inv.star_zero]

@[reassoc (attr := simp)]
lemma inl_jU_f (r : ℤ) : (biprod.inl : Q.C.X r ⟶ Q.C.X r ⊞ T.ZD.X r) ≫ T.jU.f r = T.i₀'.f r := by
  simp [jU]

@[reassoc (attr := simp)]
lemma inr_jU_f (r : ℤ) : (biprod.inr : T.ZD.X r ⟶ Q.C.X r ⊞ T.ZD.X r) ≫ T.jU.f r = T.i₁'.f r := by
  simp [jU]

@[reassoc (attr := simp)]
lemma i₀'_f_fstX (r : ℤ) : T.i₀'.f r ≫ fstX T.ΦW (r + 1) r (down_rel_succ r) = 0 := by
  simp

@[reassoc (attr := simp)]
lemma i₁'_f_fstX (r : ℤ) : T.i₁'.f r ≫ fstX T.ΦW (r + 1) r (down_rel_succ r) =
    fstX T.Φ (r + 1) r (down_rel_succ r) ≫ (dualHom A.inv (N + 1 + 1) T.pE).f r := by
  simp [desuspMap_f]

@[reassoc (attr := simp)]
lemma φ_f_p_f (r : ℤ) : Q.φ.f r ≫ Q.p.f r = Q.φ.f r := by
  rw [← comp_f, Q.φ_comp_p]

@[simp]
lemma relTop_δφU (r : ℤ) : relTop (T.δφU hW) r = 0 := by
  simp [relTop, δφU, Homotopy.ofEq]

@[reassoc]
lemma R_fstX (s k : ℤ) (h : s + k = N + 1) :
    T.R s k h ≫ fstX T.Φ (k + 1) k (down_rel_succ k) =
      (k + 1).negOnePow • (A.inv.star (inrX T.Φ (s + 1)) ≫ A.inv.star (inrX T.i₀ (s + 1)) ≫
        (T.E.XIsoOfEq (by omega : s + 1 = N + 1 + 1 - k)).hom) := by
  simp [R]

@[reassoc]
lemma relTop_δφZ_fstX (r : ℤ) : relTop T.δφZ r ≫ fstX T.Φ (r + 1) r (down_rel_succ r) =
    (r + 1).negOnePow • (A.inv.star (inrX T.Φ (N + 1 - r + 1)) ≫
      A.inv.star (inrX T.i₀ (N + 1 - r + 1)) ≫ (T.E.XIsoOfEq (by omega)).hom ≫
        (dualHom A.inv (N + 1 + 1) T.pE).f r) := by
  rw [relTop_δφZ, assoc, desuspMap_f, coneMap_f_fstX, R_fstX_assoc]
  simp only [Linear.units_smul_comp, assoc]

lemma square_leftU : dualHom A.inv (N + 1 + 1) T.πU ≫ relDuality (T.δφU hW) =
    Q.zconeDual ≫ desuspMap (inr T.ΦW) := by
  ext r
  simp [relDuality_f, πU, SymPoincare.zconeDual_f, jU]

lemma iT_ιU_f (r : ℤ) : T.iT.f (N + 1 + 1 - r) ≫ T.ιU.f (N + 1 + 1 - r) =
    T.pE.f _ ≫ (T.E.XIsoOfEq (by omega : N + 1 + 1 - r = N + 1 - r + 1)).hom ≫
      inrX T.i₀ (N + 1 - r + 1) ≫ inrX T.Φ (N + 1 - r + 1) ≫ biprod.inr ≫
        inlX T.jU (N + 1 - r) (N + 1 + 1 - r) (down_rel_sub (N + 1) r) := by
  rw [iT_f, T.ιT_eq _ _ (N + 1 - r) _ (by omega)]
  simp [ιT, ιU]

lemma square_rightU : dualHom A.inv (N + 1 + 1) T.ιU ≫ (-dualHom A.inv (N + 1 + 1) T.iT) =
    relDuality (T.δφU hW) ≫ coneFst T.ΦW := by
  ext r
  have e : (dualHom A.inv (N + 1 + 1) T.ιU ≫ (-dualHom A.inv (N + 1 + 1) T.iT)).f r =
      -A.inv.star (T.iT.f (N + 1 + 1 - r) ≫ T.ιU.f (N + 1 + 1 - r)) := by
    simp [A.inv.star_comp]
  rw [e, T.iT_ιU_f]
  simp [relDuality_f, coneFst, relTop_δφZ_fstX_assoc, A.inv.star_comp, jU]

/-! #### Poincaré duality of the trace pair -/

lemma Bu_p_jU : (T.Bu hW).p ≫ T.jU = T.jU ≫ T.pM :=
  comm_of_kar (T.Bu hW).p_idem T.pM_idem (T.jU_kar hW)

lemma jU_pM : T.jU ≫ T.pM = T.jU := by simp [jU]

/-- **Wall's two-out-of-three for the trace**: the relative duality `Ψ : Cone(j)^{N+2-*} ⟶ M` of
the trace pair `j : Q ⊕ -Z ⟶ M` is a Kar equivalence. -/
theorem isKarEquiv_unionRaw :
    IsKarEquiv (dualHom A.inv (N + 1 + 1) (T.eU hW)) T.pM (relDuality (T.δφU hW)) := by
  have hpE := dualHom_idem (J := A.inv) (N := N + 1 + 1) T.pE_idem
  refine isKarEquiv_middle_of_comm (dualHom_idem Q.zconeIdem_idem) (dualHom_idem (T.eU_idem hW))
    (dualHom_idem T.eMT_idem) (by rw [← desuspMap_comp]; exact congrArg desuspMap Q.zconeIdem_idem)
    T.pM_idem hpE ?_ ?_
    (desuspMap_inr_comm T.ΦW T.ΦW_comm) (coneFst_comm T.ΦW T.ΦW_comm)
    ((T.karSplitU hW).dual A.inv (N + 1 + 1))
    (desuspConeKarSplit T.ΦW (dualHom_idem T.pE_idem) Q.zconeIdem_idem T.ΦW_comm) Q.zconeDual_kar ?_ ?_
    (T.square_leftU hW) (T.square_rightU hW) Q.isKarEquiv_zconeDual T.isKarEquiv_iT.dualHom.neg
  · rw [← dualHom_comp, ← dualHom_comp, T.eU_πU hW]
  · rw [← dualHom_comp, ← dualHom_comp, T.eMT_ιU hW]
  · exact relDuality_kar (T.δφU hW) T.pM_idem (T.Bu_p_jU hW) T.jU_pM
      (T.Bu hW).dualHom_p_comp_φ (fun r r' ↦ by simp [δφU, Homotopy.ofEq])
  · simp only [neg_comp, comp_neg]
    rw [← dualHom_comp, ← dualHom_comp, T.pE_iT, T.iT_eMT]

/-- **The trace pair** `j = (i₀', i₁') : Q ⊕ -Z ⟶ M` with relative structure `0`, a raw Poincaré
pair (its boundary contains the raw new face `Z`). -/
@[implicit_reducible]
def unionRaw : RawPair A.inv (N + 1) where
  C := sumComplex T.bT
  p := (T.Bu hW).p
  p_idem := (T.Bu hW).p_idem
  φ := (T.Bu hW).φ
  φ_kar := (T.Bu hW).φ_kar
  φ_symm := (T.Bu hW).symm
  φ_poincare := (T.Bu hW).poincare
  D := T.MD
  pD := T.pM
  pD_idem := T.pM_idem
  support := T.pM_support
  j := T.jU
  j_kar := T.jU_kar hW
  δφ := T.δφU hW
  δφ_kar r r' := by simp [δφU, Homotopy.ofEq]
  symm := by
    rw [IsSymmHomotopy, transposeHomotopy_hom]
    funext r r'
    simp [δφU, Homotopy.ofEq, transposeHomFamily]
  poincare := T.isKarEquiv_unionRaw hW

@[simp] lemma unionRaw_p : (T.unionRaw hW).p = (T.Bu hW).p := rfl
@[simp] lemma unionRaw_φ : (T.unionRaw hW).φ = (T.Bu hW).φ := rfl

end TriadOn

end

end HSFormal.LTheory
