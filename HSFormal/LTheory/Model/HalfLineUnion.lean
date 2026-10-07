import HSFormal.LTheory.Model.HalfLineCZ
import HSFormal.LTheory.Model.CutSurj

/-!
# The union of the two half-line pairs is the line complex (half-line splitting, part 5)

For `Q : SymPoincare A.inv N`, the negative half-line pair `Y = (CZ.negLine A).pair Q` (on
`Q` placed at `0`) and the negative of the positive half-line pair
`Z = -(CZ.posLine A).pair Q` (on `-(Q at 0)`) glue to `Y ∪ Z ≃ Q ⊗ ℝ = (CZ.lineData A).sym Q`.

* `HalfLineData.aMap`: an embedding `(κE, κV)` of half-line data into line data gives a chain map
  `H.cx C ⟶ L.cx C`; `T_conj` computes the conjugate of the half-line duality `T` by it.
* For `C_ℤ(A)`: `aY = (κ_{≤-1}, κ_{≤0})`, `aZ = (κ_{≥0}, -κ_{≥0})`, and the **partition
  identity** `θ_{1/2,1/2} = aY^* T_Y aY - aZ^* T_Z aZ` (`θs_partition`): on dual vertices
  `(s⁻¹ + 1)/2` splits over the edges `(-∞, -1]`, `[0, ∞)`, on dual edges `(1 + s)/2` likewise.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression
  homotopyCofiber

noncomputable section

attribute [local implicit_reducible] PairOn.toPair SymPair.neg SymPair.toPairOn PairOn.union PairOn.glue
  SymPair.closedOfIsZero CZ.lineData InvFunctor.comp HalfLineData.pair

namespace HalfLineData

/-! ### Embeddings of half-line data into line data -/

section Conj

variable {A B : InvCat} (H : HalfLineData A B) (L : LineData A B) (κE : H.E.F ⟶ L.Δ.F)
  (κV : H.V.F ⟶ L.Δ.F)
  (hκ : ∀ X, κE.app X ≫ L.s.iso.hom.app X - κE.app X = (H.u.app X - H.w.app X) ≫ κV.app X)

include hκ in
lemma aMap_comm (C : ChainComplex A ℤ) :
    (NatTrans.mapHomologicalComplex κE _).app C ≫ L.g C =
      H.g C ≫ (NatTrans.mapHomologicalComplex κV _).app C := by
  ext i
  simp [comp_sub, hκ]

/-- The chain map `H.cx C ⟶ L.cx C` of an embedding `(κE, κV)`. -/
def aMap (C : ChainComplex A ℤ) : H.cx C ⟶ L.cx C :=
  coneMap _ _ (H.aMap_comm L κE κV hκ C)

variable {H L κE κV}

@[reassoc (attr := simp)]
lemma inlX_aMap (C : ChainComplex A ℤ) (i k : ℤ) (hk : (ComplexShape.down ℤ).Rel i k) :
    inlX (H.g C) k i hk ≫ (H.aMap L κE κV hκ C).f i = κE.app (C.X k) ≫ inlX (L.g C) k i hk := by
  simp [aMap]

@[reassoc (attr := simp)]
lemma inrX_aMap (C : ChainComplex A ℤ) (i : ℤ) :
    inrX (H.g C) i ≫ (H.aMap L κE κV hκ C).f i = κV.app (C.X i) ≫ inrX (L.g C) i := by
  simp [aMap]

@[reassoc (attr := simp)]
lemma aMap_fstX (C : ChainComplex A ℤ) (i k : ℤ) (hk : (ComplexShape.down ℤ).Rel i k) :
    (H.aMap L κE κV hκ C).f i ≫ fstX (L.g C) i k hk = fstX (H.g C) i k hk ≫ κE.app (C.X k) := by
  simp [aMap]

@[reassoc (attr := simp)]
lemma aMap_sndX (C : ChainComplex A ℤ) (i : ℤ) :
    (H.aMap L κE κV hκ C).f i ≫ sndX (L.g C) i = sndX (H.g C) i ≫ κV.app (C.X i) := by
  simp [aMap]

@[reassoc]
lemma star_fstX_star_aMap (C : ChainComplex A ℤ) {i k : ℤ} (hk : (ComplexShape.down ℤ).Rel i k) :
    B.inv.star (fstX (L.g C) i k hk) ≫ B.inv.star ((H.aMap L κE κV hκ C).f i) =
      B.inv.star (κE.app (C.X k)) ≫ B.inv.star (fstX (H.g C) i k hk) := by
  rw [← B.inv.star_comp, aMap_fstX, B.inv.star_comp]

@[reassoc]
lemma star_sndX_star_aMap (C : ChainComplex A ℤ) (i : ℤ) :
    B.inv.star (sndX (L.g C) i) ≫ B.inv.star ((H.aMap L κE κV hκ C).f i) =
      B.inv.star (κV.app (C.X i)) ≫ B.inv.star (sndX (H.g C) i) := by
  rw [← B.inv.star_comp, aMap_sndX, B.inv.star_comp]

/-- Naturality of `aMap`. -/
lemma aMap_natural {C D : ChainComplex A ℤ} (f : C ⟶ D) :
    H.map f ≫ H.aMap L κE κV hκ D = H.aMap L κE κV hκ C ≫ L.map f := by
  ext i
  apply ext_from_X (H.g C) (i - 1) i (by simp)
  all_goals simp [InvNat.app_map_assoc, -NatTrans.naturality, -NatTrans.naturality_assoc]

variable (a b : ℚ) (M : ℤ)

/-- **The conjugate of `T` by an embedding**: `a^* T a` has components
`κV^* (a u^* + b w^*) κE` (dual vertices) and `κE^* (a w + b u) κV` (dual edges). -/
lemma T_conj (C : ChainComplex A ℤ) (r : ℤ) :
    B.inv.star ((H.aMap L κE κV hκ C).f (M + 1 - r)) ≫ H.T a b M C r ≫
        (H.aMap L κE κV hκ (dualComplex A.inv M C)).f r =
      B.inv.star (inrX (L.g C) (M + 1 - r)) ≫
        ((L.Δ.mapC C).XIsoOfEq (show M + 1 - r = M - (r - 1) by omega)).hom ≫
          (B.inv.star (κV.app _) ≫ H.cf' a b (C.X (M - (r - 1))) ≫ κE.app _) ≫
            inlX (L.g (dualComplex A.inv M C)) (r - 1) r (by simp) +
      r.negOnePow • (B.inv.star (inlX (L.g C) (M - r) (M + 1 - r) (down_rel_sub M r)) ≫
        (B.inv.star (κE.app _) ≫ H.cf a b (C.X (M - r)) ≫ κV.app _) ≫
          inrX (L.g (dualComplex A.inv M C)) r) := by
  apply cone.ext_star (J := B.inv) (L.g C) _ _ (down_rel_sub M r)
  all_goals apply ext_to_X (L.g (dualComplex A.inv M C)) r (r - 1) (by simp)
  all_goals simp only [T, star_fstX_star_aMap_assoc, star_sndX_star_aMap_assoc]
  all_goals half_simp
  all_goals simp only [aMap_fstX, aMap_sndX]
  all_goals half_simp

/-- The conjugate of the half-line relative structure `δH ≫ H(φ)` by an embedding, in terms
of `T`. -/
lemma conj_δH (hab : a + b = 1) (C : ChainComplex A ℤ) (φ : dualComplex A.inv M C ⟶ C) (r : ℤ) :
    ((L.cx C).XIsoOfEq (by omega : M + 1 - r = M - (r - 1))).hom ≫
        (dualHom B.inv M (H.aMap L κE κV hκ C)).f (r - 1) ≫ (H.δH a b M hab C).hom (r - 1) r ≫
          (H.map φ).f r ≫ (H.aMap L κE κV hκ C).f r =
      B.inv.star ((H.aMap L κE κV hκ C).f (M + 1 - r)) ≫ H.T a b M C r ≫
        (H.aMap L κE κV hκ (dualComplex A.inv M C)).f r ≫ (L.map φ).f r := by
  have e : ((H.cx C).XIsoOfEq (by omega : M + 1 - r = M - (r - 1))).hom ≫
      (H.δH a b M hab C).hom (r - 1) r = H.T a b M C r := H.relTopH_δH a b M hab C r
  rw [dualHom_f, ← star_f_XIsoOfEq_assoc, reassoc_of% e, ← comp_f, aMap_natural, comp_f]

end Conj

end HalfLineData

/-! ### The two half-lines inside the line of `C_ℤ(A)` -/

namespace CZ

variable (A : InvCat)

@[simp] lemma negLine_u_app (X : A) : (negLine A).u.app X =
    (cut ((Δc A).F.obj X) (fun v ↦ v ≤ -1)).ιE ≫ sh X ≫
      (cut ((Δc A).F.obj X) (fun v ↦ v ≤ 0)).πE := rfl

@[simp] lemma negLine_w_app (X : A) : (negLine A).w.app X =
    (cut ((Δc A).F.obj X) (fun v ↦ v ≤ -1)).ιE ≫ 𝟙 _ ≫
      (cut ((Δc A).F.obj X) (fun v ↦ v ≤ 0)).πE := rfl

@[simp] lemma posLine_u_app (X : A) : (posLine A).u.app X = 𝟙 _ := rfl

@[simp] lemma posLine_w_app (X : A) : (posLine A).w.app X =
    (cut ((Δc A).F.obj X) (fun v ↦ 0 ≤ v)).ιE ≫ sh X ≫
      (cut ((Δc A).F.obj X) (fun v ↦ 0 ≤ v)).πE := rfl

variable {A} in
/-- A compression followed by the inclusion is the inclusion followed by the matrix. -/
lemma cutNat_κ (p q : ℤ → Prop) [DecidablePred p] [DecidablePred q]
    (M : ∀ X : A, (Δc A).F.obj X ⟶ (Δc A).F.obj X) (X : A)
    (h : χ X p ≫ M X ≫ χ X q = χ X p ≫ M X) :
    ((cut ((Δc A).F.obj X) p).ιE ≫ M X ≫ (cut ((Δc A).F.obj X) q).πE) ≫
        (cut ((Δc A).F.obj X) q).ιE = (cut ((Δc A).F.obj X) p).ιE ≫ M X := by
  rw [assoc, assoc, πE_ιE, ← ιE_idem_assoc p, h, ιE_idem_assoc]

/-- The edge inclusion of `(-∞, 0]`. -/
abbrev κYE : (negLine A).E.F ⟶ (lineData A).Δ.F := κ A (fun v ↦ v ≤ -1)
/-- The vertex inclusion of `(-∞, 0]`. -/
abbrev κYV : (negLine A).V.F ⟶ (lineData A).Δ.F := κ A (fun v ↦ v ≤ 0)
/-- The edge inclusion of `[0, ∞)`. -/
abbrev κZE : (posLine A).E.F ⟶ (lineData A).Δ.F := κ A (fun v ↦ 0 ≤ v)
/-- The vertex inclusion of `[0, ∞)`, with the sign of the reversed orientation. -/
abbrev κZV : (posLine A).V.F ⟶ (lineData A).Δ.F := -κ A (fun v ↦ 0 ≤ v)

lemma hκY (X : A) : (κYE A).app X ≫ (lineData A).s.iso.hom.app X - (κYE A).app X =
    ((negLine A).u.app X - (negLine A).w.app X) ≫ (κYV A).app X := by
  rw [sub_comp, negLine_u_app, negLine_w_app]
  simp only [κYE, κYV, κ_app]
  rw [cutNat_κ _ _ (fun X ↦ sh X) X (idem_sh_idem X _ _ (fun v hv ↦ by
      omega)),
    cutNat_κ _ _ (fun X ↦ 𝟙 _) X (by
      simp only [id_comp, comp_id]
      rw [idem_idem X _ _ (fun v ↦ v ≤ -1) (fun v ↦ by (try dsimp only); omega)]), comp_id]

lemma hκZ (X : A) : (κZE A).app X ≫ (lineData A).s.iso.hom.app X - (κZE A).app X =
    ((posLine A).u.app X - (posLine A).w.app X) ≫ (κZV A).app X := by
  rw [sub_comp, posLine_u_app, posLine_w_app]
  simp only [κZE, κZV, NatTrans.app_neg, κ_app, comp_neg, id_comp, sub_neg_eq_add]
  rw [cutNat_κ _ _ (fun X ↦ sh X) X (idem_sh_idem X _ _ (fun v hv ↦ by
      omega))]
  exact sub_eq_neg_add _ _

/-! #### Sandwiches of the embeddings -/

section Sandwich

variable {A} (X : A)

lemma starκ (p : ℤ → Prop) [DecidablePred p] :
    (involution : StrictInvolution (Obj A)).star ((κ A p).app X) =
      (cut ((Δc A).F.obj X) p).πE := star_cut_ιE _ p

lemma star_cutMat (p q : ℤ → Prop) [DecidablePred p] [DecidablePred q]
    (M : (Δc A).F.obj X ⟶ (Δc A).F.obj X) :
    (involution : StrictInvolution (Obj A)).star
        ((cut ((Δc A).F.obj X) p).ιE ≫ M ≫ (cut ((Δc A).F.obj X) q).πE) =
      (cut ((Δc A).F.obj X) q).ιE ≫ (involution : StrictInvolution (Obj A)).star M ≫
        (cut ((Δc A).F.obj X) p).πE := by
  rw [StrictInvolution.star_comp, StrictInvolution.star_comp, star_ιE', star_πE', assoc]

lemma star_cutMat0 (p q : ℤ → Prop) [DecidablePred p] [DecidablePred q] :
    (involution : StrictInvolution (Obj A)).star
        ((cut ((Δc A).F.obj X) p).ιE ≫ (cut ((Δc A).F.obj X) q).πE) =
      (cut ((Δc A).F.obj X) q).ιE ≫ (cut ((Δc A).F.obj X) p).πE := by
  rw [StrictInvolution.star_comp, star_ιE', star_πE']

lemma sand2 (r q : ℤ → Prop) [DecidablePred r] [DecidablePred q] (a b : ℚ)
    (M M' : (Δc A).F.obj X ⟶ (Δc A).F.obj X) :
    (cut ((Δc A).F.obj X) r).πE ≫ (a • ((cut ((Δc A).F.obj X) r).ιE ≫ M ≫
      (cut ((Δc A).F.obj X) q).πE) + b • ((cut ((Δc A).F.obj X) r).ιE ≫ M' ≫
      (cut ((Δc A).F.obj X) q).πE)) ≫ (cut ((Δc A).F.obj X) q).ιE =
      a • (χ X r ≫ M ≫ χ X q) + b • (χ X r ≫ M' ≫ χ X q) := by
  simp only [add_comp, comp_add, Linear.smul_comp, Linear.comp_smul, assoc, πE_ιE_assoc]
  rw [πE_ιE]

lemma sand2' (r : ℤ → Prop) [DecidablePred r] (a b : ℚ)
    (M' : (Δc A).F.obj X ⟶ (Δc A).F.obj X) :
    (cut ((Δc A).F.obj X) r).πE ≫ (a • 𝟙 _ + b • ((cut ((Δc A).F.obj X) r).ιE ≫ M' ≫
      (cut ((Δc A).F.obj X) r).πE)) ≫ (cut ((Δc A).F.obj X) r).ιE =
      a • χ X r + b • (χ X r ≫ M' ≫ χ X r) := by
  simp only [add_comp, comp_add, Linear.smul_comp, Linear.comp_smul, assoc, πE_ιE_assoc, id_comp]
  rw [πE_ιE]

lemma sand2'' (r : ℤ → Prop) [DecidablePred r] (a b : ℚ)
    (M' : (Δc A).F.obj X ⟶ (Δc A).F.obj X) :
    (cut ((Δc A).F.obj X) r).πE ≫ (a • ((cut ((Δc A).F.obj X) r).ιE ≫ M' ≫
      (cut ((Δc A).F.obj X) r).πE) + b • 𝟙 _) ≫ (cut ((Δc A).F.obj X) r).ιE =
      a • (χ X r ≫ M' ≫ χ X r) + b • χ X r := by
  simp only [add_comp, comp_add, Linear.smul_comp, Linear.comp_smul, assoc, πE_ιE_assoc, id_comp]
  rw [πE_ιE]

lemma idem_le_add_idem_ge (c : ℤ) :
    χ X (fun v ↦ v ≤ c) + χ X (fun v ↦ c + 1 ≤ v) = 𝟙 _ := by
  rw [idem_add_idem X _ _ (fun _ ↦ True) (fun v ↦ by simp only [iff_true]; omega)
    (fun v ↦ by omega), idem_eq_id X _ (fun _ ↦ trivial)]

/-- The vertex partition `(s⁻¹ + 1)/2 = κ_{≤0}^* (u^* + w^*)/2 κ_{≤-1} + κ_{≥0}^* (1
+ w'^*)/2 κ_{≥0}`,
in explicit coordinates. -/
lemma V1' : (lineData A).cf' (1 / 2) (1 / 2) X =
    A.cz.inv.star (cut ((Δc A).F.obj X) (fun v ↦ v ≤ 0)).ιE ≫
      ((1 / 2 : ℚ) • A.cz.inv.star ((cut ((Δc A).F.obj X) (fun v ↦ v ≤ -1)).ιE ≫ sh X ≫
          (cut ((Δc A).F.obj X) (fun v ↦ v ≤ 0)).πE) +
        (1 / 2 : ℚ) • A.cz.inv.star ((cut ((Δc A).F.obj X) (fun v ↦ v ≤ -1)).ιE ≫ 𝟙 _ ≫
          (cut ((Δc A).F.obj X) (fun v ↦ v ≤ 0)).πE)) ≫
      (cut ((Δc A).F.obj X) (fun v ↦ v ≤ -1)).ιE -
    A.cz.inv.star (-(cut ((Δc A).F.obj X) (fun v ↦ 0 ≤ v)).ιE) ≫
      ((1 / 2 : ℚ) • A.cz.inv.star (𝟙 _) +
        (1 / 2 : ℚ) • A.cz.inv.star ((cut ((Δc A).F.obj X) (fun v ↦ 0 ≤ v)).ιE ≫ sh X ≫
          (cut ((Δc A).F.obj X) (fun v ↦ 0 ≤ v)).πE)) ≫
      (cut ((Δc A).F.obj X) (fun v ↦ 0 ≤ v)).ιE := by
  simp only [StrictInvolution.star_comp, StrictInvolution.star_neg, StrictInvolution.star_id,
    star_ιE', star_πE', star_sh, assoc, neg_comp]
  rw [sand2, sand2']
  rw [idem_shi_idem X _ _ (fun v hv ↦ by omega), id_comp,
    idem_idem X _ _ (fun v ↦ v ≤ -1) (fun v ↦ by (try dsimp only); omega),
    shi_idem, idem_idem_assoc X _ _ (fun v ↦ 0 + 1 ≤ v) (fun v ↦ by (try dsimp only); omega)]
  have e : shi X = χ X (fun v ↦ v ≤ 0) ≫ shi X + χ X (fun v ↦ 0 + 1 ≤ v) ≫ shi X := by
    rw [← add_comp, idem_le_add_idem_ge, id_comp]
  show (1/2 : ℚ) • shi X + (1/2 : ℚ) • 𝟙 _ = _
  conv_lhs => rw [← idem_le_add_idem_ge X (-1), e]
  simp only [smul_add, sub_neg_eq_add, show (-1 : ℤ) + 1 = 0 from rfl]
  abel

/-- The edge partition `(1 + s)/2 = κ_{≤-1}^* (w + u)/2 κ_{≤0} - κ_{≥0}^* (w' + 1)/2 (-κ_{≥0})`,
in explicit coordinates. -/
lemma E1' : (lineData A).cf (1 / 2) (1 / 2) X =
    A.cz.inv.star (cut ((Δc A).F.obj X) (fun v ↦ v ≤ -1)).ιE ≫
      ((1 / 2 : ℚ) • ((cut ((Δc A).F.obj X) (fun v ↦ v ≤ -1)).ιE ≫ 𝟙 _ ≫
          (cut ((Δc A).F.obj X) (fun v ↦ v ≤ 0)).πE) +
        (1 / 2 : ℚ) • ((cut ((Δc A).F.obj X) (fun v ↦ v ≤ -1)).ιE ≫ sh X ≫
          (cut ((Δc A).F.obj X) (fun v ↦ v ≤ 0)).πE)) ≫
      (cut ((Δc A).F.obj X) (fun v ↦ v ≤ 0)).ιE -
    A.cz.inv.star (cut ((Δc A).F.obj X) (fun v ↦ 0 ≤ v)).ιE ≫
      ((1 / 2 : ℚ) • ((cut ((Δc A).F.obj X) (fun v ↦ 0 ≤ v)).ιE ≫ sh X ≫
          (cut ((Δc A).F.obj X) (fun v ↦ 0 ≤ v)).πE) + (1 / 2 : ℚ) • 𝟙 _) ≫
      (-(cut ((Δc A).F.obj X) (fun v ↦ 0 ≤ v)).ιE) := by
  simp only [star_ιE', comp_neg]
  rw [sand2, sand2'']
  rw [idem_sh_idem X _ _ (fun v hv ↦ by omega), id_comp,
    idem_idem X _ _ (fun v ↦ v ≤ -1) (fun v ↦ by (try dsimp only); omega),
    idem_sh_idem X _ _ (fun v hv ↦ by omega)]
  have e : sh X = χ X (fun v ↦ v ≤ -1) ≫ sh X + χ X (fun v ↦ -1 + 1 ≤ v) ≫ sh X := by
    rw [← add_comp, idem_le_add_idem_ge, id_comp]
  show (1/2 : ℚ) • 𝟙 _ + (1/2 : ℚ) • sh X = _
  conv_lhs => rw [← idem_le_add_idem_ge X (-1), e]
  simp only [smul_add, sub_neg_eq_add, show (-1 : ℤ) + 1 = 0 from rfl]
  abel

/-- The vertex partition, in the form of `T_conj`. -/
lemma V1 : (lineData A).cf' (1 / 2) (1 / 2) X =
    A.cz.inv.star ((κYV A).app X) ≫ (negLine A).cf' (1 / 2) (1 / 2) X ≫ (κYE A).app X -
      A.cz.inv.star ((κZV A).app X) ≫ (posLine A).cf' (1 / 2) (1 / 2) X ≫ (κZE A).app X :=
  V1' X

/-- The edge partition, in the form of `T_conj`. -/
lemma E1 : (lineData A).cf (1 / 2) (1 / 2) X =
    A.cz.inv.star ((κYE A).app X) ≫ (negLine A).cf (1 / 2) (1 / 2) X ≫ (κYV A).app X -
      A.cz.inv.star ((κZE A).app X) ≫ (posLine A).cf (1 / 2) (1 / 2) X ≫ (κZV A).app X :=
  E1' X

end Sandwich

/-- The embedding of the negative half-line `(-∞, 0]` into the line. -/
abbrev aY (C : ChainComplex A ℤ) : (negLine A).cx C ⟶ (lineData A).cx C :=
  (negLine A).aMap (lineData A) (κYE A) (κYV A) (hκY A) C

/-- The embedding of the positive half-line `[0, ∞)` into the line (reversed orientation). -/
abbrev aZ (C : ChainComplex A ℤ) : (posLine A).cx C ⟶ (lineData A).cx C :=
  (posLine A).aMap (lineData A) (κZE A) (κZV A) (hκZ A) C

/-- **The partition identity** `θ_{1/2,1/2} = aY^* T_Y aY - aZ^* T_Z aZ`. -/
lemma θs_partition (M : ℤ) (C : ChainComplex A ℤ) (r : ℤ) :
    ((lineData A).θ (1 / 2) (1 / 2) M C).f r =
      A.cz.inv.star ((aY A C).f (M + 1 - r)) ≫ (negLine A).T (1 / 2) (1 / 2) M C r ≫
          (aY A (dualComplex A.inv M C)).f r -
        A.cz.inv.star ((aZ A C).f (M + 1 - r)) ≫ (posLine A).T (1 / 2) (1 / 2) M C r ≫
          (aZ A (dualComplex A.inv M C)).f r := by
  rw [HalfLineData.T_conj, HalfLineData.T_conj, LineData.θ_f, V1, E1]
  simp only [comp_sub, sub_comp, smul_sub, assoc]
  abel


end CZ

namespace CZ

variable (A : InvCat)

/-! ### The comparison map `Y ∪ Z ⟶ L(Q)` -/

lemma β_κ (p : ℤ → Prop) [DecidablePred p] (hp : p 0) (X : A) :
    (βNat A p).app X ≫ (κ A p).app X = (cut ((Δc A).F.obj X) (fun v ↦ v = 0)).ιE := by
  rw [βNat_app, κ_app, cutNat_κ _ _ (fun X ↦ 𝟙 _) X (by
    simp only [id_comp, comp_id]
    exact idem_idem X _ _ (fun v ↦ v = 0) (fun v ↦ ⟨fun h ↦ h.1, fun h ↦ ⟨h,
        by rw [h]; exact hp⟩⟩)),
    comp_id]

/-- The two boundary vertices cancel in the line: `j_Y aY + j_Z aZ = 0`. -/
lemma jC_aY_add (C : ChainComplex A ℤ) :
    (negLine A).jC C ≫ aY A C + (posLine A).jC C ≫ aZ A C = 0 := by
  ext i : 1
  have e : (βNat A (fun v ↦ v ≤ 0)).app (C.X i) ≫ (κYV A).app (C.X i) +
      (βNat A (fun v ↦ 0 ≤ v)).app (C.X i) ≫ (κZV A).app (C.X i) = 0 := by
    simp only [κYV, κZV, NatTrans.app_neg, comp_neg]
    rw [β_κ A (fun v ↦ v ≤ 0) (le_refl 0), β_κ A (fun v ↦ 0 ≤ v) (le_refl 0), add_neg_cancel]
  rw [add_f_apply, comp_f, comp_f, HalfLineData.jC_f, HalfLineData.jC_f, assoc, assoc,
    HalfLineData.inrX_aMap, HalfLineData.inrX_aMap, zero_f]
  exact (by rw [← assoc, ← assoc, ← add_comp]; exact (congrArg (· ≫ _) e).trans (zero_comp))

variable {A} {N : ℤ} (Q : SymPoincare A.inv N)

/-- The negative half-line pair `Y` on `Q` placed at `0`. -/
abbrev pairY : PairOn (Q.map (atZero A)) := (negLine A).pair Q

/-- The positive half-line pair with reversed orientation: `Z` on `-(Q at 0)`. -/
abbrev pairZ : PairOn (Q.map (atZero A)).neg := ((posLine A).pair Q).toPair.neg.toPairOn

lemma pairZ_δφ_hom (r r' : ℤ) :
    (pairZ Q).δφ.hom r r' = -(((posLine A).pair Q).δφ.hom r r') := by
  change (-1 : ℤ) • _ = _
  rw [neg_one_zsmul]
  rfl

/-- The splitting `Q ≅ 0 ⊕ Q` of the union. -/
abbrev σQ : BdSplit (Q.map (atZero A)) zeroP (Q.map (atZero A)) := σU (Q.map (atZero A))

lemma pair_j_aY_add : (pairY Q).j ≫ aY A Q.C + Glue.jY (pairZ Q) ≫ aZ A Q.C = 0 := by
  change ((negLine A).jC Q.C ≫ (negLine A).map Q.p) ≫ aY A Q.C +
    ((posLine A).jC Q.C ≫ (posLine A).map Q.p) ≫ aZ A Q.C = 0
  rw [assoc, assoc, HalfLineData.aMap_natural, HalfLineData.aMap_natural, ← assoc, ← assoc,
    ← add_comp, jC_aY_add, zero_comp]

/-- `α = (aY, aZ) : D_Y ⊕ D_Z ⟶ L(Q)`. -/
def unionα : Glue.S (pairY Q) (pairZ Q) ⟶ (lineData A).cx Q.C :=
  sumFst _ ≫ aY A Q.C + sumSnd _ ≫ aZ A Q.C

lemma u_unionα : Glue.u (σQ Q) (pairY Q) (pairZ Q) ≫ unionα Q = 0 := by
  simp only [Glue.u, Glue.β, Glue.jY, unionα, add_comp, comp_add, assoc, sumInl_sumFst_assoc,
    sumInl_sumSnd_assoc, sumInr_sumFst_assoc, sumInr_sumSnd_assoc, zero_comp, comp_zero, add_zero,
    zero_add]
  change (Q.map (atZero A)).p ≫ (pairY Q).j ≫ aY A Q.C + _ = 0
  rw [← assoc, Glue.p_comp_W_j]
  exact pair_j_aY_add Q

/-- **The comparison map** `F : Y ∪ Z ⟶ L(Q)`: `aY` on `D_Y`, `aZ` on `D_Z`, `0` on the cone
coordinate `Σ(Q at 0)`. -/
def unionF : Glue.U (σQ Q) (pairY Q) (pairZ Q) ⟶ (lineData A).cx Q.C :=
  desc _ (unionα Q) (Homotopy.ofEq (u_unionα Q))

/-- **`F` carries the union structure to `θ_{1/2,1/2} ≫ L(φ)`** (`pushHomotopy` with the
partition identity `θs_partition`). -/
def unionConj : Homotopy (dualHom A.cz.inv (N + 1) (unionF Q) ≫ unionφ (pairY Q) (pairZ Q) ≫
    unionF Q) ((lineData A).sym Q).φ :=
  pushHomotopy (unionF Q) (Q.map (atZero A)).p (Homotopy.ofEq (Q.map (atZero A)).φ_kar)
    (pairY Q).j (pairZ Q).j (aY A Q.C) (aZ A Q.C) (pairY Q).δφ.hom (pairZ Q).δφ.hom
    (Homotopy.ofEq (pair_j_aY_add Q))
    (Q.map (atZero A)).p_idem (Glue.p_comp_W_j (pairY Q)).symm (Glue.p_comp_Y_j (pairZ Q)).symm
    (fun i k ↦ by simp [Homotopy.ofEq]) (fun i k ↦ by simp [Homotopy.ofEq])
    (by simp [Glue.ιW, unionF, unionα]) (by simp [Glue.ιY, unionF, unionα])
    (fun i k ↦ by
      rw [Glue.K'_hom, unionF, inrCompHomotopy_hom_desc_hom]
      simp [Homotopy.ofEq])
    _ (fun r ↦ by
      simp only [rawFam, dualHomotopy_hom, Homotopy.ofEq, Pi.zero_apply,
        StrictInvolution.star_zero, smul_zero, zero_comp, comp_zero, neg_zero, zero_add, comp_add,
        pairZ_δφ_hom, HalfLineData.pair_δφ_hom, neg_comp, comp_neg, assoc]
      rw [HalfLineData.conj_δH, HalfLineData.conj_δH, LineData.sym_φ, comp_f, θs_partition]
      simp only [sub_comp, assoc]
      abel)

end CZ

end

end HSFormal.LTheory
