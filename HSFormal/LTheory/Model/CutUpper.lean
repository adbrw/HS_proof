import HSFormal.LTheory.Model.CutComplement
import HSFormal.LTheory.Model.Cobordism

/-!
# The upper cut pair (lower L-theory model, module 22, part 6)

For an honest free `(N+1)`-dimensional Poincaré complex `P = (C, 1, φ)` over `C_ℤ(A)` and cut
data `D`, the complement of the lower cut pair is the pair `(j⁺ : ∂T ⟶ S)` over the upper
subcomplex `S = C|_{[t_*, ∞)}` (`CutData.jPlus`, `Model/CutComplement.lean`).  This file makes it
a Poincaré pair with boundary `-∂`, so that it glues with the lower pair:

* **Relative structure.** `CutData.deltaPlus : Homotopy (j⁺^* (-∂θ) j⁺) 0` with components
  `(-1)^N ι_U φ π_U : S^{N-i} ⟶ S_{i+1}` (`topPlus`; the restriction of `φ` to `S`),
  `deltaPlus_eq` (the defining identity), `deltaPlus_symm` (symmetric), and
  `relTop_deltaPlus : relTop δφ⁺ = (-1)^N ι_U φ π_U`.
* **Poincaré duality** (`isKarEquiv_relDualityPlus`): `Ψ⁺ : Cone(j⁺)^{N+1-*} ⟶ S` is a homotopy
  equivalence.  Proof: `coneComp : Cone(j⁺) ≅ Cone(φ q^*)`, `(α, c; s) ↦ (α; ι_E c + ι_U s)`
  (a chain map by construction, `homotopyCofiber.desc` of `ι_S inr` with the gluing homotopy
  `glueHomotopy`; an isomorphism degreewise), and the identity
  `TΨ⁺ ≫ coneComp = (-1)^N (cokerToCone ≫ coneMap 1 φ)` (`TΨ_comp_coneComp`), where
  `cokerToCone : S^{N+1-*} ⟶ Cone(q^* : T^{N+1-*} ⟶ C^{N+1-*})` is the inverse of the
  equivalence `coneToCokerEquiv` of the dual split sequence `split₁` and `coneMap 1 φ` is an
  equivalence by the five lemma for cones (`isKarEquiv_coneMap`).  So `TΨ⁺`, hence `Ψ⁺`
  (`transposeHom_transposeHom`), is an equivalence.
* **The upper pair** `upperPair S hp hN`: the raw pair `rawUpperPair` transported along the
  **same** truncation `truncEquiv` as the lower pair, with `upperPair_bd :
  (upperPair S hp hN).bd = (lowerPair S hp hN).bd.neg` (an equality, by `ext_of_φ`), interior `S`
  in the positive half-line (`upperPair_D_posHalf`), and `cutUnion = X⁻ ∪_∂ X⁺`
  (`SymPair.union`), a closed `(N+1)`-dimensional Poincaré complex.

**Signs** (all checked by the proofs).  In the dual coordinates of `BoundaryConstruction`,
`j⁺^* ∂φ₀ j⁺ = (-1)^{N+i} A x^* + (-1)^{iN} x A^*` on `S^{N-i}` (`A = ι_E φ π_U`,
`x = ι_E d π_U`); by `Tφ = φ` both terms carry the sign `(-1)^N` and equal `-d h - h d` for
`h = ι_U φ π_U` (`φ d = δ φ` and `π_U ι_U = 1 - π_E ι_E` absorb the rest).  Hence the null-homotopy
of `j⁺^* (-∂θ) j⁺` is `(-1)^N h`, and the boundary structure of the upper pair must be `-∂θ`
(`PairOn.union X Y` takes `Y` on `B.neg`).  `h` is symmetric because the transposition sign
`(-1)^{(i+1) + (i+1)(N-i-1)}` (`transposeHomFamily`, `bidual`) cancels the symmetry sign
`(-1)^{(i+1)(N-i)}` of `φ`.  In `TΨ_comp_coneComp` the three components carry
`(-1)^{r(N+1-r) + (N+2-r) + (N+1-r)N + 1} = (-1)^{N+r+1}` (the `T^{N+1-*}` part, against
`-(-1)^r` from `cokerToCone`), `-(-1)^{(N+2-r) + (2N+1-r)} = (-1)^N` (the `T` part) and
`(-1)^N` (the `S` part, from `relTop_deltaPlus`), i.e. `(-1)^N` throughout.

The comparison `cutUnion ≃ ±P` (homotopy isometry) is **not** proved here; see
`Model/CutHalf.lean` for the status of `DecBij`.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression
  homotopyCofiber

noncomputable section

namespace CZ

lemma star_cut_πU {B : InvCat} (X : B.cz) (p : ℤ → Prop) [DecidablePred p] :
    B.cz.inv.star (cut X p).πU = (cut X p).ιU := by
  rw [← star_cut_ιU, B.cz.inv.star_star]

variable {A : InvCat} {N : ℤ}

/-- `φ` reindexed as an `N`-dual chain map `C^{N-*} ⟶ Σ⁻¹C`. -/
abbrev φN (P : SymPoincare A.cz.inv (N + 1)) : dualComplex A.cz.inv N P.C ⟶ desusp P.C :=
  (dualDesuspIso A.cz.inv N P.C).hom ≫ desuspMap P.φ

lemma φN_f (P : SymPoincare A.cz.inv (N + 1)) (i : ℤ) : (φN P).f i =
    (P.C.XIsoOfEq (by omega : N - i = N + 1 - (i + 1))).hom ≫ P.φ.f (i + 1) := rfl

/-- `Tφ = φ` in components, for `P`. -/
@[reassoc]
lemma star_φ_cast (P : SymPoincare A.cz.inv (N + 1)) (a s : ℤ) (h : N + 1 - a = s) :
    A.cz.inv.star (P.φ.f a) ≫ (P.C.XIsoOfEq h).hom = (s * (N + 1 - s)).negOnePow •
      ((P.C.XIsoOfEq (by omega : a = N + 1 - s)).hom ≫ P.φ.f s) :=
  P.toSymComplex.star_φ_f_XIsoOfEq a s h

/-- The chain map condition of `φ` with the casts of the `N`-dual indexing. -/
@[reassoc]
lemma φ_d_comm (P : SymPoincare A.cz.inv (N + 1)) (i : ℤ) :
    (P.C.XIsoOfEq (by omega : N - i = N + 1 - (i + 1))).hom ≫ P.φ.f (i + 1) ≫ P.C.d (i + 1) i =
      -(i.negOnePow • A.cz.inv.star (P.C.d (N - (i - 1)) (N - i)) ≫
        (P.C.XIsoOfEq (by omega : N - (i - 1) = N + 1 - (i - 1 + 1))).hom ≫
          P.φ.f (i - 1 + 1) ≫ (P.C.XIsoOfEq (by omega : i - 1 + 1 = i)).hom) := by
  have h := (φN P).comm i (i - 1)
  simp only [comp_f, dualDesuspIso_hom_f, desuspMap_f, desusp_d, dualComplex_d,
    Preadditive.comp_neg, Linear.units_smul_comp, assoc] at h
  have h' := congrArg (· ≫ (P.C.XIsoOfEq (by omega : i - 1 + 1 = i)).hom) h
  simp only [Preadditive.neg_comp, assoc, d_comp_XIsoOfEq_hom, Linear.units_smul_comp] at h'
  rw [← h', neg_neg]

namespace CutData

variable {P : SymPoincare A.cz.inv (N + 1)} (D : CutData P)

@[simp] lemma star_σ_πU (r : ℤ) : (CZ.involution (A := A)).star (D.σ r).πU = (D.σ r).ιU :=
  star_cut_πU _ _

@[simp] lemma star_σ_ιU (r : ℤ) : (CZ.involution (A := A)).star (D.σ r).ιU = (D.σ r).πU :=
  star_cut_ιU _ _

@[simp] lemma star_σ_πE (r : ℤ) : (CZ.involution (A := A)).star (D.σ r).πE = (D.σ r).ιE :=
  star_cut_πE _ _

@[simp] lemma star_σ_ιE (r : ℤ) : (CZ.involution (A := A)).star (D.σ r).ιE = (D.σ r).πE :=
  star_cut_ιE _ _

@[reassoc]
lemma πU_ιU' (r : ℤ) {Z : A.cz} (Y : P.C.X r ⟶ Z) :
    (D.σ r).πU ≫ (D.σ r).ιU ≫ Y = Y - (D.σ r).πE ≫ (D.σ r).ιE ≫ Y := by
  rw [← assoc, D.πU_ιU, sub_comp, id_comp, assoc]

/-- Moving a cast of `T` through `π_E ⋯ ι_E` (cast on the right). -/
lemma πE_thomIso_ιE {a b : ℤ} (h : a = b) {Z : A.cz} (Y : P.C.X b ⟶ Z) :
    (D.σ a).πE ≫ (D.thom.C.XIsoOfEq h).hom ≫ (D.σ b).ιE ≫ Y =
      (D.σ a).πE ≫ (D.σ a).ιE ≫ (P.C.XIsoOfEq h).hom ≫ Y := by
  subst h; simp

/-- Moving a cast of `T` through `π_E ⋯ ι_E` (cast on the left). -/
lemma πE_thomIso_ιE' {a b : ℤ} (h : a = b) {Z : A.cz} (Y : P.C.X b ⟶ Z) :
    (D.σ a).πE ≫ (D.thom.C.XIsoOfEq h).hom ≫ (D.σ b).ιE ≫ Y =
      (P.C.XIsoOfEq h).hom ≫ (D.σ b).πE ≫ (D.σ b).ιE ≫ Y := by
  subst h; simp

lemma star_d_E_cast {i a a' m : ℤ} (b : ℤ) (h : a' = a) (hm : m = i) (h₁ : a' = N + 1 - m)
    (h₂ : m = i) (h₃ : a = N + 1 - i) {Z : A.cz} (Y : P.C.X i ⟶ Z) :
    A.cz.inv.star (P.C.d a' b) ≫ (D.σ a').πE ≫ (D.σ a').ιE ≫ (P.C.XIsoOfEq h₁).hom ≫
      P.φ.f m ≫ (P.C.XIsoOfEq h₂).hom ≫ Y =
    A.cz.inv.star (P.C.d a b) ≫ (D.σ a).πE ≫ (D.σ a).ιE ≫ (P.C.XIsoOfEq h₃).hom ≫
      P.φ.f i ≫ Y := by
  subst h hm; simp

/-! ### The relative structure `δφ⁺` -/

/-- The components `ε ι_U φ π_U : S^{N-i} ⟶ S_{i+1}` of the relative structure. -/
def topPlus (ε : ℤˣ) (i j : ℤ) (hij : (ComplexShape.down ℤ).Rel j i) :
    (dualComplex A.cz.inv N D.subC).X i ⟶ D.subC.X j :=
  ε • ((D.σ (N - i)).ιU ≫ (φN P).f i ≫
    (P.C.XIsoOfEq (by simp only [ComplexShape.down_Rel] at hij; omega : i + 1 = j)).hom ≫
      (D.σ j).πU)

lemma topPlus_succ (ε : ℤˣ) (i : ℤ) (h : (ComplexShape.down ℤ).Rel (i + 1) i) :
    D.topPlus ε i (i + 1) h = ε • ((D.σ (N - i)).ιU ≫ (φN P).f i ≫ (D.σ (i + 1)).πU) := by
  simp [topPlus]

lemma deltaPlus_eq (hp : P.p = 𝟙 _) :
    dualHom A.cz.inv N D.jPlus ≫ (-D.thom.bdφ) ≫ D.jPlus =
      Homotopy.nullHomotopicMap' (D.topPlus N.negOnePow) := by
  ext i : 1
  rw [Homotopy.nullHomotopicMap'_f (k₂ := i + 1) (k₁ := i) (k₀ := i - 1) (by simp) (by simp),
    topPlus_succ]
  simp only [SymComplex.bdφ, D.bdP_eq_id hp, comp_id, Preadditive.neg_comp, Preadditive.comp_neg,
    neg_f_apply, comp_f, dualHom_f, jPlus_f, jPlusF, SymComplex.bdSwap_f,
    StrictInvolution.star_add, StrictInvolution.star_comp, add_comp, comp_add, assoc,
    SymComplex.star_fstX_swapF_assoc, SymComplex.star_sndX_swapF_assoc, Linear.units_smul_comp,
    Linear.comp_units_smul, inrX_fstX_assoc, inrX_sndX_assoc, inlX_fstX_assoc, inlX_sndX_assoc,
    zero_comp, comp_zero, add_zero, zero_add, smul_zero, compA, cross, SplitCx.cross,
    SplitCx.sub_d, dualComplex_d, topPlus, star_σ_πU, star_σ_ιU, star_σ_πE, star_σ_ιE,
    πU_ιU'_assoc, dualDesuspIso_hom_f, desuspMap_f, comp_sub, smul_sub, sub_comp]
  rw [D.πE_thomIso_ιE, D.πE_thomIso_ιE', star_φ_cast_assoc,
    D.star_d_E_cast (N - i) (show N - (i - 1) = N - i + 1 by omega) (show i - 1 + 1 = i by omega)
      (h₃ := by omega),
    φ_d_comm_assoc]
  have e₂ : (i * N).negOnePow * ((i + 1) * (N + 1 - (i + 1))).negOnePow = N.negOnePow := by
    rw [← Int.negOnePow_add, Int.negOnePow_eq_iff,
      show i * N + (i + 1) * (N + 1 - (i + 1)) - N = 2 * (i * N) - i * (i + 1) by ring]
    exact (even_two_mul _).sub (Int.even_mul_succ_self i)
  simp only [Preadditive.neg_comp, Preadditive.comp_neg, Linear.comp_units_smul,
    Linear.units_smul_comp, assoc, smul_smul, smul_neg, e₂, Int.negOnePow_add]
  abel

/-- **The relative structure of the upper pair** `δφ⁺ : j⁺^* (-∂θ) j⁺ ≃ 0`, with components
`(-1)^N ι_U φ π_U` (the restriction of `φ` to `S`). -/
def deltaPlus (hp : P.p = 𝟙 _) :
    Homotopy (dualHom A.cz.inv N D.jPlus ≫ (-D.thom.bdφ) ≫ D.jPlus) 0 :=
  homotopyCongr (Homotopy.nullHomotopy' (D.topPlus N.negOnePow)) (D.deltaPlus_eq hp).symm rfl

lemma deltaPlus_hom_of_rel (hp : P.p = 𝟙 _) {i j : ℤ} (h : (ComplexShape.down ℤ).Rel j i) :
    (D.deltaPlus hp).hom i j = D.topPlus N.negOnePow i j h := dif_pos h

lemma deltaPlus_hom_of_not_rel (hp : P.p = 𝟙 _) {i j : ℤ} (h : ¬ (ComplexShape.down ℤ).Rel j i) :
    (D.deltaPlus hp).hom i j = 0 := dif_neg h

lemma πU_eqToHom {a b : ℤ} (h : a = b) :
    (D.σ a).πU ≫ eqToHom (congrArg D.subC.X h) = (P.C.XIsoOfEq h).hom ≫ (D.σ b).πU := by
  subst h; simp

/-- `δφ⁺` is symmetric. -/
lemma deltaPlus_symm (hp : P.p = 𝟙 _) : IsSymmHomotopy A.cz.inv N (D.deltaPlus hp) := by
  rw [IsSymmHomotopy, transposeHomotopy_hom]
  funext r r'
  simp only [transposeHomFamily]
  by_cases h : (ComplexShape.down ℤ).Rel r' r
  · have h' : (ComplexShape.down ℤ).Rel (N - r) (N - r') := by
      simp only [ComplexShape.down_Rel] at h ⊢; omega
    rw [D.deltaPlus_hom_of_rel hp h', D.deltaPlus_hom_of_rel hp h]
    obtain rfl : r' = r + 1 := by simp only [ComplexShape.down_Rel] at h; omega
    simp only [topPlus, bidual_hom_f, StrictInvolution.star_units_smul, StrictInvolution.star_comp,
      star_σ_πU, star_σ_ιU, φN_f, BoundaryConstruction.star_XIsoOfEq_hom, Linear.units_smul_comp,
      Linear.comp_units_smul, assoc, smul_smul]
    erw [D.πU_eqToHom (sub_sub_cancel N (r + 1))]
    rw [XIsoOfEq_hom_comp_XIsoOfEq_hom_assoc, star_φ_cast_assoc P (N - (r + 1) + 1) (r + 1)]
    simp only [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul,
      XIsoOfEq_hom_comp_XIsoOfEq_hom_assoc, XIsoOfEq_rfl, Iso.refl_hom, id_comp]
    simp only [assoc, XIsoOfEq_hom_comp_XIsoOfEq_hom_assoc]
    congr 1
    rw [← Int.negOnePow_add, ← Int.negOnePow_add, ← Int.negOnePow_add, Int.negOnePow_eq_iff]
    exact ⟨(r + 1) * (N - r), by ring⟩
  · have h' : ¬ (ComplexShape.down ℤ).Rel (N - r) (N - r') := by
      simp only [ComplexShape.down_Rel] at h ⊢; omega
    rw [D.deltaPlus_hom_of_not_rel hp h', D.deltaPlus_hom_of_not_rel hp h]
    simp



/-- The degreewise split sequence `0 ⟶ S ⟶ C ⟶ T ⟶ 0`. -/
@[simps]
def split₀ : DegreewiseSplit D.inclS D.q where
  t r := (D.σ r).πU
  s r := (D.σ r).ιE
  it r := (D.σ r).ιU_πU
  sq r := (D.σ r).ιE_πE
  total r := (add_comm _ _).trans (D.σ r).total

lemma glueHomotopy_hom {i j : ℤ} (h : (ComplexShape.down ℤ).Rel j i) :
    D.glueHomotopy.hom i j = D.glueHom i j h := by
  change (Homotopy.nullHomotopy' D.glueHom).hom i j + 0 = _
  rw [add_zero]
  exact dif_pos h

/-- `φ q^* : T^{N+1-*} ⟶ C`. -/
abbrev φq : dualComplex A.cz.inv (N + 1) D.thomC ⟶ P.C := dualHom A.cz.inv (N + 1) D.q ≫ P.φ

/-- The null-homotopy of `j⁺ ι_S inr : ∂T ⟶ Cone(φ q^*)`: the gluing homotopy followed by the
cone's null-homotopy of `φ q^* inr`. -/
def coneH : Homotopy (D.jPlus ≫ D.inclS ≫ inr D.φq) 0 :=
  (homotopyCongr (f' := D.jPlus ≫ D.inclS ≫ inr D.φq)
      (g' := coneFst D.thom.φ ≫ D.φq ≫ inr D.φq) (D.glueHomotopy.compRight (inr D.φq))
      (by simp only [assoc]) (by simp only [assoc])).trans
    (homotopyCongr (g' := 0) ((inrCompHomotopy D.φq down_exists_rel).compLeft (coneFst D.thom.φ))
      rfl (by simp))

/-- **`Cone(j⁺) ≅ Cone(φ q^*)`**, `(α, c; s) ↦ (α; ι_E c + ι_U s)` (here only the map). -/
def coneComp : cone D.jPlus ⟶ cone D.φq := desc D.jPlus (D.inclS ≫ inr D.φq) D.coneH

lemma inrX_coneComp (r : ℤ) :
    inrX D.jPlus r ≫ D.coneComp.f r = (D.σ r).ιU ≫ inrX D.φq r := by
  have := congrArg (fun f ↦ f.f r) (inr_desc D.jPlus (D.inclS ≫ inr D.φq) D.coneH)
  simpa [coneComp] using this

lemma inlX_coneComp (r : ℤ) :
    inlX D.jPlus (r - 1) r (by simp) ≫ D.coneComp.f r =
      fstX D.thom.φ (r - 1 + 1) (r - 1) (by simp) ≫ inlX D.φq (r - 1) r (by simp) +
        sndX D.thom.φ (r - 1 + 1) ≫ (D.σ (r - 1 + 1)).ιE ≫
          (P.C.XIsoOfEq (by omega : r - 1 + 1 = r)).hom ≫ inrX D.φq r := by
  rw [coneComp, inlX_desc_f]
  simp only [coneH, Homotopy.trans_hom, homotopyCongr, Homotopy.compRight_hom,
    Homotopy.compLeft_hom, Pi.add_apply]
  rw [D.glueHomotopy_hom (by simp), inrCompHomotopy_hom _ _ _ _ (by simp),
    add_comm (D.glueHom (r - 1) r _ ≫ _)]
  simp [glueHom]

/-- The degreewise inverse of `coneComp`: `(α; c) ↦ (α, π_E c; π_U c)`. -/
def coneCompInvF (r : ℤ) : (cone D.φq).X r ⟶ (cone D.jPlus).X r :=
  fstX D.φq r (r - 1) (by simp) ≫ inlX D.thom.φ (r - 1) (r - 1 + 1) (by simp) ≫
      inlX D.jPlus (r - 1) r (by simp) +
    sndX D.φq r ≫ ((D.σ r).πE ≫ (D.thomC.XIsoOfEq (by omega : r = r - 1 + 1)).hom ≫
      inrX D.thom.φ (r - 1 + 1) ≫ inlX D.jPlus (r - 1) r (by simp) + (D.σ r).πU ≫ inrX D.jPlus r)

@[reassoc (attr := simp)] lemma σ_ιU_πE (r : ℤ) : (D.σ r).ιU ≫ (D.σ r).πE = 0 := (D.σ r).ιU_πE
@[reassoc (attr := simp)] lemma σ_ιU_πU (r : ℤ) : (D.σ r).ιU ≫ (D.σ r).πU = 𝟙 _ := (D.σ r).ιU_πU
@[reassoc (attr := simp)] lemma σ_ιE_πE (r : ℤ) : (D.σ r).ιE ≫ (D.σ r).πE = 𝟙 _ := (D.σ r).ιE_πE
@[reassoc (attr := simp)] lemma σ_ιE_πU (r : ℤ) : (D.σ r).ιE ≫ (D.σ r).πU = 0 := (D.σ r).ιE_πU

@[reassoc]
lemma ιE_cast_πE {a b : ℤ} (h : a = b) :
    (D.σ a).ιE ≫ (P.C.XIsoOfEq h).hom ≫ (D.σ b).πE ≫ (D.thomC.XIsoOfEq h.symm).hom = 𝟙 _ := by
  subst h; simp [Splitting.ιE_πE]

@[reassoc]
lemma ιE_cast_πU {a b : ℤ} (h : a = b) :
    (D.σ a).ιE ≫ (P.C.XIsoOfEq h).hom ≫ (D.σ b).πU = 0 := by
  subst h; simp [Splitting.ιE_πU]

@[reassoc]
lemma πE_cast_ιE {a b : ℤ} (h : a = b) :
    (D.σ a).πE ≫ (D.thomC.XIsoOfEq h).hom ≫ (D.σ b).ιE ≫ (P.C.XIsoOfEq h.symm).hom =
      (D.σ a).πE ≫ (D.σ a).ιE := by
  subst h; simp

lemma coneComp_inv (r : ℤ) : D.coneComp.f r ≫ D.coneCompInvF r = 𝟙 _ := by
  apply ext_from_X D.jPlus (r - 1) r (by simp)
  · rw [reassoc_of% D.inlX_coneComp]
    erw [comp_id]
    apply ext_from_X D.thom.φ (r - 1) (r - 1 + 1) (by simp)
    · simp [coneCompInvF]
    · simp [coneCompInvF, D.ιE_cast_πU_assoc, D.ιE_cast_πE_assoc]
  · rw [reassoc_of% D.inrX_coneComp]
    erw [comp_id]
    simp [coneCompInvF]

lemma inv_coneComp (r : ℤ) : D.coneCompInvF r ≫ D.coneComp.f r = 𝟙 _ := by
  apply ext_from_X D.φq (r - 1) r (by simp)
  · simp [coneCompInvF, D.inlX_coneComp]
  · simp [coneCompInvF, D.inlX_coneComp, D.inrX_coneComp, D.πE_cast_ιE_assoc]
    simp only [← assoc, ← add_comp, Splitting.total, id_comp]

@[reassoc]
lemma coneComp_fstX (r : ℤ) :
    D.coneComp.f r ≫ fstX D.φq r (r - 1) (by simp) =
      fstX D.jPlus r (r - 1) (by simp) ≫ fstX D.thom.φ (r - 1 + 1) (r - 1) (by simp) := by
  apply ext_from_X D.jPlus (r - 1) r (by simp)
  · simp [reassoc_of% D.inlX_coneComp]
  · simp [reassoc_of% D.inrX_coneComp]

@[reassoc]
lemma coneComp_sndX (r : ℤ) :
    D.coneComp.f r ≫ sndX D.φq r =
      fstX D.jPlus r (r - 1) (by simp) ≫ sndX D.thom.φ (r - 1 + 1) ≫ (D.σ (r - 1 + 1)).ιE ≫
        (P.C.XIsoOfEq (by omega : r - 1 + 1 = r)).hom + sndX D.jPlus r ≫ (D.σ r).ιU := by
  apply ext_from_X D.jPlus (r - 1) r (by simp)
  · simp [reassoc_of% D.inlX_coneComp]
  · simp [reassoc_of% D.inrX_coneComp]

section Casts

variable {K L : ChainComplex A.cz ℤ} (f : K ⟶ L)

@[reassoc]
lemma cone_inrX_eqToHom {i i' : ℤ} (h : i = i') :
    inrX f i ≫ eqToHom (congrArg (homotopyCofiber f).X h) = (L.XIsoOfEq h).hom ≫ inrX f i' := by
  subst h; simp

@[reassoc]
lemma cone_inlX_eqToHom {k i i' : ℤ} (hk : (ComplexShape.down ℤ).Rel i k) (h : i = i') :
    inlX f k i hk ≫ eqToHom (congrArg (homotopyCofiber f).X h) =
      (K.XIsoOfEq (show k = i' - 1 by simp only [ComplexShape.down_Rel] at hk; omega)).hom ≫
        inlX f (i' - 1) i' (by simp) := by
  subst h
  obtain rfl : k = i - 1 := by simp only [ComplexShape.down_Rel] at hk; omega
  simp

/-- The components of the transposed relative duality map `TΨ : D^{N+1-*} ⟶ Cone(j)`. -/
lemma transposeHom_relDuality_f {B : ChainComplex A.cz ℤ} {j : B ⟶ L}
    {φ : dualComplex A.cz.inv N B ⟶ B} (H : Homotopy (dualHom A.cz.inv N j ≫ φ ≫ j) 0) (r : ℤ) :
    (transposeHom A.cz.inv (N + 1) (relDuality H)).f r = (r * (N + 1 - r)).negOnePow •
      (A.cz.inv.star (relTop H (N + 1 - r)) ≫
          (L.XIsoOfEq (by omega : N + 1 - (N + 1 - r) = r)).hom ≫ inrX j r +
        (N + 1 - r + 1).negOnePow • A.cz.inv.star (j.f (N + 1 - r)) ≫
          A.cz.inv.star (φ.f (N + 1 - r)) ≫
            (B.XIsoOfEq (by omega : N - (N + 1 - r) = r - 1)).hom ≫
              inlX j (r - 1) r (by simp)) := by
  rw [transposeHom_f, relDuality_f]
  simp only [StrictInvolution.star_add, StrictInvolution.star_comp,
    StrictInvolution.star_units_smul, StrictInvolution.star_star, add_comp, assoc,
    Linear.units_smul_comp]
  rw [cone_inrX_eqToHom (h := by omega), cone_inlX_eqToHom (h := by omega)]

end Casts

@[reassoc]
lemma bdC_cast_fstX {a b : ℤ} (h : a = b) :
    (D.thom.bdC.XIsoOfEq h).hom ≫ fstX D.thom.φ (b + 1) b (by simp) =
      fstX D.thom.φ (a + 1) a (by simp) ≫
        ((dualComplex A.cz.inv (N + 1) D.thomC).XIsoOfEq h).hom := by
  subst h; simp

@[reassoc]
lemma bdC_cast_sndX {a b : ℤ} (h : a = b) :
    (D.thom.bdC.XIsoOfEq h).hom ≫ sndX D.thom.φ (b + 1) =
      sndX D.thom.φ (a + 1) ≫ (D.thomC.XIsoOfEq (by omega : a + 1 = b + 1)).hom := by
  subst h; simp

@[reassoc]
lemma star_d_πE_cast {a m : ℤ} (h : a = m) (b : ℤ) :
    A.cz.inv.star (P.C.d a b) ≫ (D.σ a).πE ≫ (D.thomC.XIsoOfEq h).hom =
      A.cz.inv.star (P.C.d m b) ≫ (D.σ m).πE := by
  subst h; simp

lemma star_d_πE_cast₂ {a m c : ℤ} (h : a = c) (h' : c = m) (b : ℤ) :
    A.cz.inv.star (P.C.d a b) ≫ (D.σ a).πE ≫ (D.thom.C.XIsoOfEq h).hom ≫
        (D.thomC.XIsoOfEq h').hom = A.cz.inv.star (P.C.d m b) ≫ (D.σ m).πE := by
  subst h h'; simp

@[reassoc]
lemma πE_cast_ιE_cast {a b c : ℤ} (h : a = b) (h' : b = c) :
    (D.σ a).πE ≫ (D.thomC.XIsoOfEq h).hom ≫ (D.σ b).ιE ≫ (P.C.XIsoOfEq h').hom =
      (P.C.XIsoOfEq (h.trans h')).hom ≫ (D.σ c).πE ≫ (D.σ c).ιE := by
  subst h h'; simp

@[reassoc]
lemma πU_cast {a b : ℤ} (h : a = b) :
    (D.σ a).πU ≫ (D.subC.XIsoOfEq h).hom = (P.C.XIsoOfEq h).hom ≫ (D.σ b).πU := by
  subst h; simp

lemma relTop_deltaPlus_aux {k m a : ℤ} (hm : m = k) (ha : a = N + 1 - k) (h₀ : N + 1 - k = a)
    (h₁ : a = N + 1 - m) (h₂ : m = k) :
    (D.subC.XIsoOfEq h₀).hom ≫ (D.σ a).ιU ≫ (P.C.XIsoOfEq h₁).hom ≫ P.φ.f m ≫
      (P.C.XIsoOfEq h₂).hom ≫ (D.σ k).πU = (D.σ (N + 1 - k)).ιU ≫ P.φ.f k ≫ (D.σ k).πU := by
  subst hm ha; simp

/-- The relative top structure of the upper pair is `(-1)^N ι_U φ π_U`. -/
lemma relTop_deltaPlus (hp : P.p = 𝟙 _) (k : ℤ) :
    relTop (D.deltaPlus hp) k = N.negOnePow • ((D.σ (N + 1 - k)).ιU ≫ P.φ.f k ≫ (D.σ k).πU) := by
  rw [relTop, D.deltaPlus_hom_of_rel hp (by simp), topPlus, Linear.comp_units_smul, φN_f]
  simp only [assoc]
  rw [D.relTop_deltaPlus_aux (by omega) (by omega)]

@[reassoc]
lemma πE_cast₂_ιE_cast {a b b' c : ℤ} (h : a = b) (h₀ : b = b') (h' : b' = c) :
    (D.σ a).πE ≫ (D.thom.C.XIsoOfEq h).hom ≫ (D.thomC.XIsoOfEq h₀).hom ≫ (D.σ b').ιE ≫
      (P.C.XIsoOfEq h').hom = (P.C.XIsoOfEq (h.trans (h₀.trans h'))).hom ≫ (D.σ c).πE ≫
        (D.σ c).ιE := by
  subst h h₀ h'; simp

/-- The dual degreewise split sequence `0 ⟶ T^{N+1-*} ⟶ C^{N+1-*} ⟶ S^{N+1-*} ⟶ 0`. -/
abbrev split₁ := D.split₀.dual A.cz.inv (N + 1)

/-- `Cone(q^*) ⟶ Cone(φ q^*)`, induced by `φ`. -/
abbrev coneφ : cone (dualHom A.cz.inv (N + 1) D.q) ⟶ cone D.φq :=
  coneMap (j := dualHom A.cz.inv (N + 1) D.q) (j' := D.φq) (𝟙 _) P.φ (by simp [φq])

lemma TΨ_comp_coneComp (hp : P.p = 𝟙 _) :
    transposeHom A.cz.inv (N + 1) (relDuality (D.deltaPlus hp)) ≫ D.coneComp =
      N.negOnePow • (cokerToCone D.split₁ ≫ D.coneφ) := by
  ext r : 1
  apply ext_to_X D.φq r (r - 1) (by simp)
  · rw [comp_f, assoc, D.coneComp_fstX, transposeHom_relDuality_f]
    simp only [comp_f, assoc, D.coneComp_fstX, transposeHom_relDuality_f,
      Linear.units_smul_comp, Linear.comp_units_smul, StrictInvolution.star_add,
      StrictInvolution.star_comp, StrictInvolution.star_units_smul, StrictInvolution.star_star,
      add_comp, comp_add, HomologicalComplex.units_smul_f_apply, cokerToCone_f, coneMap_f_fstX,
      sub_comp, cone_inrX_eqToHom_assoc, cone_inlX_eqToHom_assoc, inrX_fstX_assoc,
      inlX_fstX_assoc, zero_comp, comp_zero, smul_zero, zero_add, add_zero,
      neg_f_apply, SymComplex.bdφ, comp_f, D.bdP_eq_id hp, id_f, comp_id, StrictInvolution.star_neg,
      Preadditive.neg_comp, Preadditive.comp_neg, SymComplex.bdSwap_f, SymComplex.star_swapF,
      jPlus_f, jPlusF, cone.star_fstX_inrX_assoc, cone.star_sndX_inrX_assoc,
      cone.star_fstX_inlX_assoc, cone.star_sndX_inlX_assoc]
    rw [D.bdC_cast_fstX]
    simp only [inlX_fstX_assoc, inrX_fstX_assoc, inlX_fstX, inrX_fstX, zero_comp, comp_zero,
      smul_zero, add_zero, comp_id, zero_sub, smul_neg, zero_add, Preadditive.comp_neg,
      Preadditive.neg_comp, DegreewiseSplit.dual_s, DegreewiseSplit.dual_t, split₀_s, split₀_t,
      star_σ_πU, star_σ_ιE, dualComplex_d, cross, SplitCx.cross, StrictInvolution.star_comp, assoc,
      BoundaryConstruction.dualComplex_XIsoOfEq_hom, XIsoOfEq_hom_comp_XIsoOfEq_hom,
      Linear.units_smul_comp, Linear.comp_units_smul]
    rw [D.star_d_πE_cast₂, smul_smul, smul_smul, smul_smul, neg_inj]
    congr 1
    rw [← Int.negOnePow_add, ← Int.negOnePow_add, ← Int.negOnePow_add, Int.negOnePow_eq_iff]
    have key : Even (2 * ((N + 1 - r) * r - r + 1) + (N + 1 - r) * (N + 1 - r - 1)) :=
      (even_two_mul _).add (Int.even_mul_pred_self _)
    convert key using 1
    ring
  · rw [comp_f, assoc, D.coneComp_sndX, transposeHom_relDuality_f]
    simp only [comp_add, Linear.units_smul_comp, add_comp, assoc, inrX_fstX_assoc,
      inrX_sndX_assoc, inlX_fstX_assoc, inlX_sndX_assoc, zero_comp, comp_zero, smul_zero,
      add_zero, zero_add, D.bdC_cast_sndX_assoc, neg_f_apply, SymComplex.bdφ, comp_f,
      D.bdP_eq_id hp, id_f, comp_id, StrictInvolution.star_neg, Preadditive.neg_comp,
      Preadditive.comp_neg, SymComplex.bdSwap_f, SymComplex.star_swapF, jPlus_f, jPlusF,
      StrictInvolution.star_add, StrictInvolution.star_comp, StrictInvolution.star_units_smul,
      cone.star_fstX_inrX_assoc, cone.star_sndX_inrX_assoc, cone.star_fstX_inlX_assoc,
      cone.star_sndX_inlX_assoc, Linear.comp_units_smul, D.relTop_deltaPlus hp, compA,
      star_σ_πU, star_σ_ιU, star_σ_πE, star_σ_ιE, D.πU_cast_assoc,
      HomologicalComplex.units_smul_f_apply, cokerToCone_f, coneMap_f_sndX, sub_comp,
      inrX_sndX, inlX_sndX, DegreewiseSplit.dual_s, split₀_t, smul_neg]
    rw [D.πE_cast₂_ιE_cast]
    simp only [neg_zero, add_zero, sub_zero]
    rw [star_φ_cast_assoc, star_φ_cast_assoc]
    simp only [XIsoOfEq_rfl, Iso.refl_hom, id_comp, Linear.units_smul_comp,
      Linear.comp_units_smul, smul_smul, assoc]
    have c₁ : (r * (N + 1 - r)).negOnePow * ((N + 1 - r + 1).negOnePow *
        ((N + (N + 1 - r)).negOnePow * (r * (N + 1 - r)).negOnePow)) = -N.negOnePow := by
      rw [← Int.negOnePow_succ, ← Int.negOnePow_add, ← Int.negOnePow_add, ← Int.negOnePow_add,
        Int.negOnePow_eq_iff]
      exact ⟨r * (N + 1 - r) + (N + 1 - r), by ring⟩
    have c₂ : (r * (N + 1 - r)).negOnePow * (N.negOnePow * (r * (N + 1 - r)).negOnePow) =
        N.negOnePow := by
      rw [← Int.negOnePow_add, ← Int.negOnePow_add, Int.negOnePow_eq_iff]
      exact ⟨r * (N + 1 - r), by ring⟩
    rw [c₁, c₂, Units.neg_smul, neg_neg, ← smul_add, ← Preadditive.comp_add, ← Preadditive.comp_add,
      (D.σ r).total, comp_id]

instance (r : ℤ) : IsIso (D.coneComp.f r) :=
  ⟨⟨D.coneCompInvF r, D.coneComp_inv r, D.inv_coneComp r⟩⟩

instance : IsIso D.coneComp := HomologicalComplex.Hom.isIso_of_components _

/-- `φ` is an honest homotopy equivalence `C^{N+1-*} ≃ C` (`P.p = 1`). -/
lemma isKarEquiv_φ (hp : P.p = 𝟙 _) : IsKarEquiv (𝟙 _) (𝟙 _) P.φ := by
  have h := P.poincare
  rw [isPoincare_iff, hp, dualHom_id] at h
  exact h

lemma isKarEquiv_coneφ (hp : P.p = 𝟙 _) : IsKarEquiv (𝟙 _) (𝟙 _) D.coneφ := by
  have h := isKarEquiv_coneMap (B := dualComplex A.cz.inv (N + 1) D.thomC)
    (pB := 𝟙 _) (pD := 𝟙 _) (pB' := 𝟙 _) (pD' := 𝟙 _) (j := dualHom A.cz.inv (N + 1) D.q)
    (j' := D.φq) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (m := 𝟙 _) (n := P.φ) (by simp) (by simp) (by simp [φq])
    ⟨𝟙 _, by simp, ⟨Homotopy.ofEq (by simp)⟩, ⟨Homotopy.ofEq (by simp)⟩⟩ (isKarEquiv_φ hp)
  rwa [coneMap_id, coneMap_id] at h

/-- The transposed relative duality map of the upper pair is a homotopy equivalence. -/
lemma isKarEquiv_TΨ (hp : P.p = 𝟙 _) :
    IsKarEquiv (𝟙 _) (𝟙 _) (transposeHom A.cz.inv (N + 1) (relDuality (D.deltaPlus hp))) := by
  obtain ⟨E₂, hE₂⟩ := (isKarEquiv_id_iff _).mp (D.isKarEquiv_coneφ hp)
  let E : HomotopyEquiv (dualComplex A.cz.inv (N + 1) D.subC) (cone D.jPlus) :=
    ((coneToCokerEquiv D.split₁).symm.trans E₂).trans (HomotopyEquiv.ofIso (asIso D.coneComp).symm)
  have hE : E.hom = (cokerToCone D.split₁ ≫ D.coneφ) ≫ inv D.coneComp := by
    simp [E, HomotopyEquiv.trans, HomotopyEquiv.symm, coneToCokerEquiv, hE₂, HomotopyEquiv.ofIso]
  have key : transposeHom A.cz.inv (N + 1) (relDuality (D.deltaPlus hp)) =
      N.negOnePow • E.hom := by
    rw [hE, ← Linear.units_smul_comp, ← D.TΨ_comp_coneComp hp, assoc, IsIso.hom_inv_id, comp_id]
  apply (isKarEquiv_id_iff _).mpr
  rcases Int.units_eq_one_or N.negOnePow with h | h
  · exact ⟨E, by rw [key, h, one_smul]⟩
  · exact ⟨HomotopyEquiv.negHom E, by rw [key, h, Units.neg_smul, one_smul]; rfl⟩

/-- **The upper pair is Poincaré**: its relative duality map `Ψ⁺ : Cone(j⁺)^{N+1-*} ⟶ S` is a
homotopy equivalence. -/
theorem isKarEquiv_relDualityPlus (hp : P.p = 𝟙 _) :
    IsKarEquiv (𝟙 _) (𝟙 _) (relDuality (D.deltaPlus hp)) := by
  have h := (D.isKarEquiv_TΨ hp)
  rw [← dualHom_id A.cz.inv (N + 1)] at h
  have h' := h.transposeHom (by simp) (by simp)
  rwa [transposeHom_transposeHom, dualHom_id] at h'


/-! ### The raw upper pair and its truncation -/

include D in
lemma isZero_subC (hp : P.p = 𝟙 _) {r : ℤ} (hr : r < 0 ∨ N + 1 < r) : IsZero (D.subC.X r) := by
  have h := isZero_X_of_p_eq_id hp hr
  rw [IsZero.iff_id_eq_zero]
  change 𝟙 (D.σ r).U = 0
  rw [← (D.σ r).ιU_πU, h.eq_of_src (D.σ r).πU 0, comp_zero]

/-- **The raw upper pair** `(j⁺ : ∂T ⟶ S, (δφ⁺, -∂θ))`, a Poincaré pair whose boundary lives in
`[-1, N+1]`. -/
def rawUpperPair (hp : P.p = 𝟙 _) : RawPair A.cz.inv N where
  C := D.thom.bdC
  p := D.thom.bdP
  p_idem := D.thom.bdP_idem
  φ := -D.thom.bdφ
  φ_kar := by simp [D.thom.bdφ_kar]
  φ_symm := D.thom.bdφ_symm.neg
  φ_poincare := D.thom.bdφ_poincare.neg
  D := D.subC
  pD := 𝟙 _
  pD_idem := by simp
  support r hr := (D.isZero_subC hp hr).eq_of_src _ _
  j := D.jPlus
  j_kar := by rw [D.bdP_eq_id hp]; simp
  δφ := D.deltaPlus hp
  δφ_kar r r' := by simp
  symm := D.deltaPlus_symm hp
  poincare := by
    have key : ∀ h : D.thom.bdP ≫ D.jPlus = D.jPlus ≫ 𝟙 D.subC,
        coneMap (j := D.jPlus) (j' := D.jPlus) D.thom.bdP (𝟙 D.subC) h = 𝟙 _ := by
      rw [D.bdP_eq_id hp]; intro h; exact coneMap_id _
    rw [key, dualHom_id]
    exact D.isKarEquiv_relDualityPlus hp

variable {D} (S : D.Sec) (hp : P.p = 𝟙 _) (hN : 0 ≤ N)

/-- **The upper cut pair** `X⁺`: the raw upper pair transported along the **same** boundary
truncation as the lower pair, an `(N+1)`-dimensional Poincaré pair over `C_ℤ(A)` with interior
`S` in the positive half-line and boundary `-∂` (`upperPair_bd`). -/
def upperPair : SymPair A.cz.inv N :=
  (D.rawUpperPair hp).transportBd (truncEquiv S hp hN) (truncIdem_idem S hp hN)
    (truncIdem_support S hp hN)

lemma upperPair_D : (upperPair S hp hN).D = D.subC := rfl

lemma upperPair_j : (upperPair S hp hN).j = (truncEquiv S hp hN).g ≫ D.jPlus := rfl

/-- **The upper and lower cut pairs have opposite boundaries**: `∂X⁺ = -∂X⁻`, so they glue
(`SymPair.union`). -/
theorem upperPair_bd : (upperPair S hp hN).bd = (lowerPair S hp hN).bd.neg :=
  SymPoincare.ext_of_φ rfl HEq.rfl (heq_of_eq (by
    simp [upperPair, lowerPair, rawUpperPair, RawPair.transportBd, RawPair.bdTransport,
      SymPoincare.neg]
    rfl))

lemma upperPair_D_posHalf (r : ℤ) : posHalf A ((upperPair S hp hN).D.X r) := D.subC_posHalf r

/-- **The cut union** `X⁻ ∪_∂ X⁺`, a closed `(N+1)`-dimensional Poincaré complex over
`C_ℤ(A)`. -/
def cutUnion : SymPoincare A.cz.inv (N + 1) :=
  SymPair.union (lowerPair S hp hN) (upperPair S hp hN) (upperPair_bd S hp hN)

end CutData

end CZ

end

end HSFormal.LTheory
