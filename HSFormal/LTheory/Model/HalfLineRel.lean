import HSFormal.LTheory.Model.CutIsoGen

/-!
# Relative duality maps with different source and target pairs (half-line splitting, part 1)

Support for `Model/HalfLineData.lean`.  The relative duality map `relDuality` of `Pairs.lean`
is built from a relative boundary `H : Homotopy (j^* φ j) 0` of a single map `j : B ⟶ D`.  The
duality of a half-line pair is the composite of an isomorphism
`Cone(j_C)^{M+1-*} ⟶ D(C^{M-*})` between *different* complexes with `D(φ)`; that isomorphism is
the relative duality map of a *heterogeneous* relative boundary
`H : Homotopy (j^* φ j') 0` for `j : B ⟶ D`, `φ : B^{N-*} ⟶ B'`, `j' : B' ⟶ D'`.

* `relTopH`, `relTopH_comm`, `relDualityH` (a chain map `Cone(j)^{N+1-*} ⟶ D'`),
  `relTopDiffH`, `relDualityHHomotopy`, `relTopDiffHHomotopy`: the heterogeneous versions of
  `relTop`, `relTop_comm`, `relDuality`, `relTopDiff`, `relDualityHomotopy`,
  `relTopDiffHomotopy` (same proofs).
* `relDuality_eq_relDualityH`: a homogeneous relative boundary whose components factor through a
  heterogeneous one has the factored relative duality map.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression
  homotopyCofiber

noncomputable section

universe v u

variable {V : Type u} [Category.{v} V] [Preadditive V] {J : StrictInvolution V} {N : ℤ}

section Hetero

variable {B D B' D' : ChainComplex V ℤ} {j : B ⟶ D} {φ : dualComplex J N B ⟶ B'} {j' : B' ⟶ D'}

/-- The top component `D^{N+1-r} ⟶ D'_r` of a heterogeneous relative boundary. -/
def relTopH (H : Homotopy (dualHom J N j ≫ φ ≫ j') 0) (r : ℤ) : D.X (N + 1 - r) ⟶ D'.X r :=
  (D.XIsoOfEq (by omega : N + 1 - r = N - (r - 1))).hom ≫ H.hom (r - 1) r

lemma relTopH_eq (H : Homotopy (dualHom J N j ≫ φ ≫ j') 0) (s r : ℤ) (h : s + 1 = r) :
    relTopH H r = (D.XIsoOfEq (by omega : N + 1 - r = N - s)).hom ≫ H.hom s r := by
  obtain rfl : s = r - 1 := by omega
  rfl

/-- The heterogeneous relative cycle condition `δφ_r d = δ δφ_{r-1} + j φ_{r-1} j'^*`. -/
lemma relTopH_comm (H : Homotopy (dualHom J N j ≫ φ ≫ j') 0) (r r' : ℤ)
    (h : (ComplexShape.down ℤ).Rel r r') :
    relTopH H r ≫ D'.d r r' = ((dualComplex J (N + 1) D).d r r' ≫ relTopH H r' :
      D.X (N + 1 - r) ⟶ D'.X r') +
      (D.XIsoOfEq (by simp only [ComplexShape.down_Rel] at h; omega : N + 1 - r = N - r')).hom ≫
        (dualHom J N j ≫ φ ≫ j').f r' := by
  obtain rfl : r = r' + 1 := by simp only [ComplexShape.down_Rel] at h; omega
  have hc : H.hom r' (r' + 1) ≫ D'.d (r' + 1) r' = (dualHom J N j ≫ φ ≫ j').f r' -
      (dualComplex J N D).d r' (r' - 1) ≫ H.hom (r' - 1) r' := by
    rw [H.comm r', dNext_eq _ (show (ComplexShape.down ℤ).Rel r' (r' - 1) by simp),
      prevD_eq _ h, zero_f, add_zero]
    abel
  rw [relTopH_eq H r' _ rfl, relTopH_eq H (r' - 1) r' (by omega), assoc, hc]
  simp only [dualComplex_d, comp_sub, Linear.units_smul_comp, Linear.comp_units_smul,
    XIsoOfEq_star_d_assoc D (show N + 1 - r' = N - (r' - 1) by omega)
      (show N + 1 - (r' + 1) = N - r' by omega)]
  rw [Int.negOnePow_succ, Units.neg_smul]
  abel

/-- **A relative boundary from its top components**: a family `T_r : D^{N+1-r} ⟶ D'_r` with
`T_r d = δ T_{r'} + F_{r'}` (the relative cycle condition) is the top family of a
null-homotopy of `F : D^{N-*} ⟶ D'` (`relTopH_homotopyOfTop`). -/
def homotopyOfTop (F : dualComplex J N D ⟶ D') (T : ∀ r, D.X (N + 1 - r) ⟶ D'.X r)
    (hT : ∀ r r' (h : (ComplexShape.down ℤ).Rel r r'), T r ≫ D'.d r r' =
      ((dualComplex J (N + 1) D).d r r' ≫ T r' : D.X (N + 1 - r) ⟶ D'.X r') +
      (D.XIsoOfEq (by simp only [ComplexShape.down_Rel] at h; omega : N + 1 - r = N - r')).hom ≫
        F.f r') : Homotopy F 0 where
  hom i k := if h : (ComplexShape.down ℤ).Rel k i then
      (D.XIsoOfEq (by simp only [ComplexShape.down_Rel] at h; omega : N - i = N + 1 - k)).hom ≫ T k
    else 0
  zero i k h := dif_neg h
  comm i := by
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel i (i - 1) by simp),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (i + 1) i by simp), dif_pos (by simp),
      dif_pos (by simp), zero_f, add_zero]
    have h := hT (i + 1) i (by simp)
    have e : (dualComplex J N D).d i (i - 1) ≫ (D.XIsoOfEq (by omega : N - (i - 1) =
        N + 1 - i)).hom = -((D.XIsoOfEq (by omega : N - i = N + 1 - (i + 1))).hom ≫
          (dualComplex J (N + 1) D).d (i + 1) i) := by
      simp only [dualComplex_d, Linear.units_smul_comp, Linear.comp_units_smul,
        star_d_XIsoOfEq, Int.negOnePow_succ, Units.neg_smul, Preadditive.comp_neg, neg_neg,
        XIsoOfEq_star_d D (show N + 1 - i = N + 1 - i from rfl)
          (show N - i = N + 1 - (i + 1) by omega), XIsoOfEq_rfl, Iso.refl_hom, comp_id]
    rw [← assoc, e, assoc, h]
    simp only [comp_add, Preadditive.neg_comp, assoc, XIsoOfEq_hom_comp_XIsoOfEq_hom_assoc,
      XIsoOfEq_rfl, Iso.refl_hom, id_comp]
    abel

lemma relTopH_homotopyOfTop {j : B ⟶ D} {φ : dualComplex J N B ⟶ B'} {j' : B' ⟶ D'}
    (T : ∀ r, D.X (N + 1 - r) ⟶ D'.X r)
    (hT : ∀ r r' (h : (ComplexShape.down ℤ).Rel r r'), T r ≫ D'.d r r' =
      ((dualComplex J (N + 1) D).d r r' ≫ T r' : D.X (N + 1 - r) ⟶ D'.X r') +
      (D.XIsoOfEq (by simp only [ComplexShape.down_Rel] at h; omega : N + 1 - r = N - r')).hom ≫
        (dualHom J N j ≫ φ ≫ j').f r') (r : ℤ) :
    relTopH (homotopyOfTop _ T hT) r = T r := by
  simp [relTopH, homotopyOfTop]

variable [HasBinaryBiproducts V]

/-- The heterogeneous relative duality map `Cone(j)^{N+1-*} ⟶ D'`,
`(α, β) ↦ δφ_r α + (-1)^{r+1} j' φ_r β`. -/
def relDualityH (H : Homotopy (dualHom J N j ≫ φ ≫ j') 0) :
    dualComplex J (N + 1) (cone j) ⟶ D' where
  f r := J.star (inrX j (N + 1 - r)) ≫ relTopH H r +
    (r + 1).negOnePow • J.star (inlX j (N - r) (N + 1 - r) (down_rel_sub N r)) ≫ φ.f r ≫ j'.f r
  comm' r r' h := by
    have hr : r = r' + 1 := by simp only [ComplexShape.down_Rel] at h; omega
    apply cone.ext_star (J := J) j _ _ (down_rel_sub N r)
    · simp only [dualComplex_d, comp_add, add_comp, assoc, Linear.comp_units_smul,
        Linear.units_smul_comp, cone.star_fstX_inrX_assoc, cone.star_fstX_inlX_assoc, zero_comp,
        zero_add, cone.star_fstX_d_assoc j _ _ _ (show (ComplexShape.down ℤ).Rel (N + 1 - r')
          (N + 1 - r) by simp only [ComplexShape.down_Rel]; omega), neg_comp,
        cone.star_fstX_inlX'_assoc j _ (down_rel_sub N r'), Hom.comm, φ.comm_assoc, comp_zero,
        neg_zero, star_d_XIsoOfEq_assoc]
      subst hr
      simp [Int.negOnePow_succ]
    · simp only [dualComplex_d, comp_add, add_comp, assoc, Linear.comp_units_smul,
        Linear.units_smul_comp, cone.star_sndX_inrX_assoc, cone.star_sndX_inlX_assoc, zero_comp,
        add_zero, cone.star_sndX_d_assoc j _ _ (show (ComplexShape.down ℤ).Rel (N + 1 - r')
          (N + 1 - r) by simp only [ComplexShape.down_Rel]; omega),
        cone.star_fstX_inlX'_assoc j _ (down_rel_sub N r'), cone.star_fstX_inrX_assoc,
        relTopH_comm H r r' h, comp_zero, smul_zero, add_zero, zero_add, comp_f, dualHom_f,
        star_f_XIsoOfEq_assoc]
      subst hr
      simp [Int.negOnePow_succ, smul_smul]

@[simp]
lemma relDualityH_f (H : Homotopy (dualHom J N j ≫ φ ≫ j') 0) (r : ℤ) :
    (relDualityH H).f r = J.star (inrX j (N + 1 - r)) ≫ relTopH H r +
      (r + 1).negOnePow • J.star (inlX j (N - r) (N + 1 - r) (down_rel_sub N r)) ≫ φ.f r ≫
        j'.f r :=
  rfl

end Hetero

/-! ### Changing a heterogeneous relative boundary by a second-order homotopy -/

section RelTopDiffH

variable {B D B' D' : ChainComplex V ℤ} {j : B ⟶ D} {φ : dualComplex J N B ⟶ B'} {j' : B' ⟶ D'}
  (H₁ H₂ : Homotopy (dualHom J N j ≫ φ ≫ j') 0)

/-- The difference of two heterogeneous relative boundaries, a chain map `D^{N+1-*} ⟶ D'`. -/
def relTopDiffH : dualComplex J (N + 1) D ⟶ D' where
  f r := relTopH H₁ r - relTopH H₂ r
  comm' r r' h := by
    rw [sub_comp, relTopH_comm H₁ r r' h, relTopH_comm H₂ r r' h, comp_sub]
    abel

@[simp]
lemma relTopDiffH_f (r : ℤ) : (relTopDiffH H₁ H₂).f r = relTopH H₁ r - relTopH H₂ r := rfl

/-- If `δφ₁ - δφ₂ = dL - Ld` for a degree-two family `L`, then `δφ₁ - δφ₂ ≃ 0`. -/
def relTopDiffHHomotopy (L : ∀ i k, (dualComplex J N D).X i ⟶ D'.X k)
    (hL : ∀ i i₀ i₁ i₂, i₀ + 1 = i → i + 1 = i₁ → i₁ + 1 = i₂ →
      H₁.hom i i₁ - H₂.hom i i₁ = L i i₂ ≫ D'.d i₂ i₁ - (dualComplex J N D).d i i₀ ≫ L i₀ i₁) :
    Homotopy (relTopDiffH H₁ H₂) 0 :=
  homotopyCongr (Homotopy.nullHomotopy' fun r r' _ ↦
    (D.XIsoOfEq (by omega : N + 1 - r = N - (r - 1))).hom ≫ L (r - 1) r') (by
      ext r
      rw [Homotopy.nullHomotopicMap'_f (down_rel_succ r) (down_rel_pred r)]
      have h := hL (r - 1) (r - 1 - 1) r (r + 1) (by omega) (by omega) (by omega)
      have e := XIsoOfEq_star_d (J := J) D (by omega : N + 1 - (r - 1) = N - (r - 1 - 1))
        (by omega : N + 1 - r = N - (r - 1))
      simp only [relTopDiffH_f, relTopH]
      rw [← comp_sub, h]
      simp only [comp_sub, dualComplex_d, Linear.units_smul_comp, Linear.comp_units_smul,
        reassoc_of% e]
      rw [show (r - 1).negOnePow = -r.negOnePow by rw [Int.negOnePow_sub, Int.negOnePow_one]; simp]
      simp only [Units.neg_smul, sub_neg_eq_add, assoc]
      abel) rfl

variable [HasBinaryBiproducts V]

lemma relDualityH_eq_add :
    relDualityH H₁ = relDualityH H₂ + dualHom J (N + 1) (inr j) ≫ relTopDiffH H₁ H₂ := by
  ext r
  simp only [relDualityH_f, add_f_apply, comp_f, dualHom_f, inr_f, relTopDiffH_f, comp_sub]
  abel

/-- Heterogeneous relative boundaries whose difference is null-homotopic have homotopic relative
duality maps. -/
def relDualityHHomotopy (hΔ : Homotopy (relTopDiffH H₁ H₂) 0) :
    Homotopy (relDualityH H₁) (relDualityH H₂) :=
  homotopyCongr ((Homotopy.refl (relDualityH H₂)).add (hΔ.compLeft (dualHom J (N + 1) (inr j))))
    (relDualityH_eq_add H₁ H₂).symm (by simp)

end RelTopDiffH

/-! ### Comparison with homogeneous relative boundaries -/

section Compare

variable [HasBinaryBiproducts V] {B D B' D' : ChainComplex V ℤ} {j : B ⟶ D}
  {φ : dualComplex J N B ⟶ B'} {j' : B' ⟶ D'} (H : Homotopy (dualHom J N j ≫ φ ≫ j') 0)

/-- A homogeneous relative boundary `δφ` on `j₀ : B₀ ⟶ D₀` (structure `φ₀`) whose components
are those of a heterogeneous one conjugated by a strict square `(m, n) : j ⟶ j₀` and followed by
`f : D' ⟶ D₀` has relative duality map `c^* Ψ_H f` for the cone map `c = (m, n)`. -/
lemma relDuality_eq_relDualityH {B₀ D₀ : ChainComplex V ℤ} {j₀ : B₀ ⟶ D₀}
    {φ₀ : dualComplex J N B₀ ⟶ B₀} (δφ : Homotopy (dualHom J N j₀ ≫ φ₀ ≫ j₀) 0)
    (m : B ⟶ B₀) (n : D ⟶ D₀) (hmn : m ≫ j₀ = j ≫ n) (f : D' ⟶ D₀)
    (htop : ∀ r, J.star (n.f (N + 1 - r)) ≫ relTopH H r ≫ f.f r = relTop δφ r)
    (hφ : ∀ r, J.star (m.f (N - r)) ≫ φ.f r ≫ j'.f r ≫ f.f r = φ₀.f r ≫ j₀.f r) :
    relDuality δφ = dualHom J (N + 1) (coneMap m n hmn) ≫ relDualityH H ≫ f := by
  ext r
  simp only [relDuality_f, comp_f, dualHom_f, relDualityH_f, star_coneMap_f hmn _ _
    (down_rel_sub N r), add_comp, comp_add, assoc, cone.star_fstX_inrX_assoc,
    cone.star_fstX_inlX_assoc, cone.star_sndX_inrX_assoc, cone.star_sndX_inlX_assoc,
    Linear.comp_units_smul, Linear.units_smul_comp, zero_comp, comp_zero, add_zero,
    zero_add, htop, hφ]

end Compare

end

end HSFormal.LTheory
