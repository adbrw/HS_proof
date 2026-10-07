import HSFormal.LTheory.Model.UnionRelDouble

/-!
# The transposed union structure

For the union `U = X ∪_B Y` (`PairOn.union`, `X` first), the union structure is the
symmetrization `δφZ = ½(Hns + T Hns)` of `Glue.Hns`.  This file studies the **transposed**
structure `T Hns` (`Union.THns`), a relative boundary on the same map, with top `φᵀ`
(`Union.phiT`, a chain map `U^{N+1-*} ⟶ U`):

* `Union.unionPhiTHomotopy`: `φ_U ≃ φᵀ`, by the second-order homotopy
  `L = ½ K'^* (-φ_B) K'` (as in `Glue.relDualityδφZHomotopy`), with explicit components.
* `Union.phiT_comp_π` (**right square**): `φᵀ` followed by the projection
  `π : U ⟶ Cone(j_X)` (killing `D_Y`) is `ι_W^* ∘ TΨ_X`.
* `Union.star_sndX_phiT` (**reading `D_Y`**): on the `D_Y`-summand, `φᵀ` is `δφ_Y ι_Y`.
* `Union.star_fstX_phiT` (**reading `ΣC`**): on the `ΣC`-summand, `φᵀ` is `± φ_B j_Y ι_Y`.
* `Union.phiT_kar`: `φᵀ` is a Kar morphism.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex homotopyCofiber
  HSFormal.Compression

noncomputable section

attribute [local implicit_reducible] PairOn.toPair SymPair.neg SymPair.toPairOn PairOn.union PairOn.glue
  SymPair.closedOfIsZero IsStrictSymm

universe v u

variable {V : Type u} [Category.{v} V] [Preadditive V] {J : StrictInvolution V} {N : ℤ}

variable [HasBinaryBiproducts V] [HasFiniteBiproducts V]

namespace Union

variable {B : SymPoincare J N} (X : PairOn B) (Y : PairOn B.neg)

@[reassoc]
lemma star_sndX_XIsoOfEq {A' B' : ChainComplex V ℤ} (j : A' ⟶ B') {k k' : ℤ} (h : k = k') :
    J.star (sndX j k) ≫ ((cone j).XIsoOfEq h).hom = (B'.XIsoOfEq h).hom ≫ J.star (sndX j k') := by
  subst h; simp

@[reassoc]
lemma star_fstX_XIsoOfEq {A' B' : ChainComplex V ℤ} (j : A' ⟶ B') {m k k' : ℤ} (h : k = k')
    (hk : (ComplexShape.down ℤ).Rel k m) (hk' : (ComplexShape.down ℤ).Rel k' m) :
    J.star (fstX j k m hk) ≫ ((cone j).XIsoOfEq h).hom = J.star (fstX j k' m hk') := by
  subst h; simp

@[reassoc]
lemma star_sumSnd_XIsoOfEq {C D : ChainComplex V ℤ} (b : ∀ r, BinaryBicone (C.X r) (D.X r))
    {k k' : ℤ} (h : k = k') :
    J.star ((sumSnd b).f k) ≫ ((sumComplex b).XIsoOfEq h).hom =
      (D.XIsoOfEq h).hom ≫ J.star ((sumSnd b).f k') := by
  subst h; simp

lemma isStrictSymm_a' :
    IsStrictSymm J N (dualHom J N (Glue.a' (σ B) X Y) ≫ (zeroP : SymPoincare J N).φ ≫
      Glue.a' (σ B) X Y) := (zeroP : SymPoincare J N).symm.conj _

/-- The transposed union structure `T Hns`, a relative boundary on `a' : 0 ⟶ U`. -/
def THns : Homotopy (dualHom J N (Glue.a' (σ B) X Y) ≫ (zeroP : SymPoincare J N).φ ≫
    Glue.a' (σ B) X Y) 0 :=
  homotopyCongr (transposeHomotopy J N (Glue.Hns (σ B) X Y)) (isStrictSymm_a' X Y)
    transposeHom_zero

lemma THns_hom (a b : ℤ) : (THns X Y).hom a b =
    (Glue.HW (σ B) X Y).hom a b + ((transposeHomotopy J N (Glue.G (σ B) X Y)).hom a b +
      (Glue.HY (σ B) X Y).hom a b) := by
  rw [THns, homotopyCongr_hom, Glue.transposeHomotopy_Hns_hom]

lemma THns_kar (r r' : ℤ) :
    (dualHom J N (Glue.pU (σ B) X Y)).f r ≫ (THns X Y).hom r r' ≫ (Glue.pU (σ B) X Y).f r' =
      (THns X Y).hom r r' := by
  have h := congrFun (congrFun (transposeHomFamily_conjMap (J := J) (N := N)
    (Glue.pU (σ B) X Y) (Glue.Hns (σ B) X Y).hom) r) r'
  have e : (fun i k ↦ (dualHom J N (Glue.pU (σ B) X Y)).f i ≫ (Glue.Hns (σ B) X Y).hom i k ≫
      (Glue.pU (σ B) X Y).f k) = (Glue.Hns (σ B) X Y).hom :=
    funext₂ (Glue.Hns_kar (σ B) X Y)
  rw [e] at h
  simp only [THns, homotopyCongr_hom, transposeHomotopy_hom]
  exact h.symm

variable [Linear ℚ V]

/-- `φ_U - φᵀ = relTop δφZ - relTop (T Hns)`. -/
abbrev diffT : dualComplex J (N + 1) (Glue.U (σ B) X Y) ⟶ Glue.U (σ B) X Y :=
  relTopDiff (Glue.δφZ (σ B) X Y) (THns X Y)

/-- The union structure `φ_U`, typed on `Glue.U`. -/
@[implicit_reducible]
def unionφ : dualComplex J (N + 1) (Glue.U (σ B) X Y) ⟶ Glue.U (σ B) X Y := (X.union Y).φ

/-- The top `φᵀ` of the transposed union structure, a chain map `U^{N+1-*} ⟶ U`. -/
@[implicit_reducible]
def phiT : dualComplex J (N + 1) (Glue.U (σ B) X Y) ⟶ Glue.U (σ B) X Y :=
  unionφ X Y - diffT X Y

@[simp]
lemma phiT_f (r : ℤ) : (phiT X Y).f r = relTop (THns X Y) r := by
  simp [phiT, unionφ, union_φ_f]

/-- The second-order homotopy `L = ½ K'^*(-φ_B)K'`. -/
def L (i k : ℤ) : (dualComplex J N (Glue.U (σ B) X Y)).X i ⟶ (Glue.U (σ B) X Y).X k :=
  (1 / 2 : ℚ) • conjL (-B.φ) (Glue.K' (σ B) X Y) i k

lemma δφZ_sub_THns (i i₀ i₁ i₂ : ℤ) (h₀ : i₀ + 1 = i) (h₁ : i + 1 = i₁) (h₂ : i₁ + 1 = i₂) :
    (Glue.δφZ (σ B) X Y).hom i i₁ - (THns X Y).hom i i₁ =
      L X Y i i₂ ≫ (Glue.U (σ B) X Y).d i₂ i₁ -
        (dualComplex J N (Glue.U (σ B) X Y)).d i i₀ ≫ L X Y i₀ i₁ := by
  have h : (Glue.G (σ B) X Y).hom i i₁ - (transposeHomotopy J N (Glue.G (σ B) X Y)).hom i i₁ =
      conjL (-B.φ) (Glue.K' (σ B) X Y) i i₂ ≫ (Glue.U (σ B) X Y).d i₂ i₁ -
        (dualComplex J N (Glue.U (σ B) X Y)).d i i₀ ≫ conjL (-B.φ) (Glue.K' (σ B) X Y) i₀ i₁ :=
    conjHomotopy_sub_transpose (-B.φ) (Glue.K' (σ B) X Y) B.symm.neg i i₀ i₁ i₂ h₀ h₁ h₂
  rw [δφZ_hom, THns_hom, Glue.Hns_hom, Glue.transposeHomotopy_Hns_hom, L, L, Linear.smul_comp,
    Linear.comp_smul, ← smul_sub, ← h]
  module

/-- `φ_U - φᵀ ≃ 0`. -/
def diffTHomotopy : Homotopy (diffT X Y) 0 :=
  relTopDiffHomotopy _ _ (L X Y) (δφZ_sub_THns X Y)

/-- **`φ_U ≃ φᵀ`**. -/
def unionPhiTHomotopy : Homotopy (X.union Y).φ (phiT X Y) :=
  homotopyCongr ((diffTHomotopy X Y).add (Homotopy.refl (phiT X Y)))
    (by rw [phiT, unionφ, add_sub_cancel]) (zero_add _)

lemma unionPhiTHomotopy_hom (r r' : ℤ) (h : (ComplexShape.down ℤ).Rel r' r) :
    (unionPhiTHomotopy X Y).hom r r' =
      ((Glue.U (σ B) X Y).XIsoOfEq (by omega : N + 1 - r = N - (r - 1))).hom ≫
        L X Y (r - 1) r' := by
  have h' : r + 1 = r' := h
  simp [unionPhiTHomotopy, diffTHomotopy, relTopDiffHomotopy, Homotopy.nullHomotopy'_hom, h']

lemma THns_kar_left (r r' : ℤ) :
    (dualHom J N (Glue.pU (σ B) X Y)).f r ≫ (THns X Y).hom r r' = (THns X Y).hom r r' := by
  conv_lhs => rw [← THns_kar]
  rw [← assoc, ← comp_f, ← dualHom_comp, Glue.pU_idem, THns_kar]

/-- `φᵀ` is a Kar morphism. -/
lemma phiT_kar : dualHom J (N + 1) (Glue.pU (σ B) X Y) ≫ phiT X Y = phiT X Y := by
  ext r
  simp only [comp_f, dualHom_f, phiT_f, relTop]
  rw [star_f_XIsoOfEq_assoc, ← dualHom_f, THns_kar_left]

/-- The projection `π : U ⟶ Cone(j_X)`, `(x, y_X, y_Y) ↦ (x, y_X)`. -/
def π : Glue.U (σ B) X Y ⟶ cone X.j :=
  coneMap B.p (sumFst (Glue.bS X Y) ≫ X.pD) (by simp [Glue.u, β_eq, Glue.jY, add_comp])

@[reassoc (attr := simp)]
lemma ιW_f_sumFst_f (r : ℤ) : (Glue.ιW (σ B) X Y).f r ≫ sndX (Glue.u (σ B) X Y) r ≫
    (sumFst (Glue.bS X Y)).f r = 𝟙 _ := by
  simp

/-- **Right square**: `φᵀ` followed by `π : U ⟶ Cone(j_X)` is `ι_W^* ∘ TΨ_X`. -/
lemma phiT_comp_π : phiT X Y ≫ π X Y =
    dualHom J (N + 1) (Glue.ιW (σ B) X Y) ≫ transposeHom J (N + 1) (relDuality X.δφ) := by
  have hφ : B.φ ≫ B.p = B.φ := B.φ_comp_p
  have hφ' (m : ℤ) : B.φ.f m ≫ B.p.f m = B.φ.f m := by rw [← comp_f, hφ]
  ext r
  have hrel : (ComplexShape.down ℤ).Rel r (r - 1) := down_rel_pred r
  apply ext_to_X X.j r (r - 1) hrel
  · rw [comp_f, assoc, comp_f, assoc, transposeHom_relDuality_f_fstX _ B.symm, π, coneMap_f_fstX]
    simp only [phiT_f, relTop, THns_hom, assoc, add_comp, comp_add, Union.HW_hom, Union.HY_hom,
      Union.TG_hom, Glue.ιW_f_fstX_assoc, Glue.ιY_f_fstX_assoc, comp_zero, zero_comp, zero_add,
      add_zero, neg_neg,
      K'_hom_eq _ _ _ _ hrel, inlX_fstX_assoc, neg_f_apply, neg_comp, Glue.c', comp_f,
      comp_neg, neg_zero, hφ', dualHom_f, Glue.β', β_f, J.star_comp, dualHom_f]
    rw [star_f_XIsoOfEq_assoc (Glue.ιW (σ B) X Y) (by omega : N + 1 - r = N - (r - 1))]
  · rw [comp_f, assoc, comp_f, assoc, transposeHom_relDuality_f_sndX _ X.symm, π, coneMap_f_sndX]
    simp only [phiT_f, relTop, THns_hom, assoc, add_comp, comp_add, Union.HW_hom, Union.HY_hom,
      Union.TG_hom, Glue.ιW_f_sndX_assoc, Glue.ιY_f_sndX_assoc, comp_zero, zero_add, add_zero,
      K'_hom_eq _ _ _ _ hrel, inlX_sndX_assoc, zero_comp, neg_f_apply, neg_comp, Glue.c',
      comp_f, comp_neg, neg_zero, dualHom_f, sumFst_f, BinaryBiproduct.bicone_fst,
      biprod.inl_fst_assoc, biprod.inr_fst_assoc, PairOn.δφ_kar]
    rw [star_f_XIsoOfEq_assoc (Glue.ιW (σ B) X Y) (by omega : N + 1 - r = N - (r - 1)),
      Double.δφ_pD]

/-! ### Reading the `D_Y`- and `ΣC`-summands of `φᵀ` -/

@[reassoc (attr := simp)]
lemma star_snd_star_sndX_star_ιW (m : ℤ) :
    J.star ((sumSnd (Glue.bS X Y)).f m) ≫ J.star (sndX (Glue.u (σ B) X Y) m) ≫
      J.star ((Glue.ιW (σ B) X Y).f m) = 0 := by
  rw [← J.star_comp, ← J.star_comp, assoc, Glue.ιW_f_sndX_assoc]
  simp

@[reassoc (attr := simp)]
lemma star_snd_star_sndX_star_ιY (m : ℤ) :
    J.star ((sumSnd (Glue.bS X Y)).f m) ≫ J.star (sndX (Glue.u (σ B) X Y) m) ≫
      J.star ((Glue.ιY (σ B) X Y).f m) = 𝟙 _ := by
  rw [← J.star_comp, ← J.star_comp, assoc, Glue.ιY_f_sndX_assoc]
  simp

@[reassoc (attr := simp)]
lemma star_snd_star_sndX_star_inlX (a m : ℤ) (h : (ComplexShape.down ℤ).Rel m a) :
    J.star ((sumSnd (Glue.bS X Y)).f m) ≫ J.star (sndX (Glue.u (σ B) X Y) m) ≫
      J.star (inlX (Glue.u (σ B) X Y) a m h) = 0 := by
  rw [cone.star_sndX_inlX, comp_zero]

@[reassoc (attr := simp)]
lemma star_fstX_star_ιW (m a : ℤ) (h : (ComplexShape.down ℤ).Rel m a) :
    J.star (fstX (Glue.u (σ B) X Y) m a h) ≫ J.star ((Glue.ιW (σ B) X Y).f m) = 0 := by
  rw [← J.star_comp, Glue.ιW_f_fstX, J.star_zero]

@[reassoc (attr := simp)]
lemma star_fstX_star_ιY (m a : ℤ) (h : (ComplexShape.down ℤ).Rel m a) :
    J.star (fstX (Glue.u (σ B) X Y) m a h) ≫ J.star ((Glue.ιY (σ B) X Y).f m) = 0 := by
  rw [← J.star_comp, Glue.ιY_f_fstX, J.star_zero]

/-- **Reading `D_Y`**: on the `D_Y`-summand, `φᵀ` is `δφ_Y` followed by `ι_Y`. -/
lemma star_sndX_phiT (r : ℤ) :
    J.star ((sumSnd (Glue.bS X Y)).f (N + 1 - r)) ≫ J.star (sndX (Glue.u (σ B) X Y) (N + 1 - r)) ≫
      (phiT X Y).f r = relTop Y.δφ r ≫ (Glue.ιY (σ B) X Y).f r := by
  have hk : N + 1 - r = N - (r - 1) := by omega
  have h₂ : (ComplexShape.down ℤ).Rel (N - (r - 1)) (N - r) := by simp; omega
  simp only [phiT_f, relTop]
  rw [star_sndX_XIsoOfEq_assoc _ hk, star_sumSnd_XIsoOfEq_assoc _ hk]
  simp only [THns_hom, comp_add, Union.HW_hom, Union.HY_hom, Union.TG_hom, dualHom_f,
    Glue.β', comp_f, J.star_comp, assoc, star_snd_star_sndX_star_ιW_assoc,
    star_snd_star_sndX_star_ιY_assoc, dualHomotopy_hom, K'_hom_eq _ _ _ _ h₂,
    Linear.comp_units_smul, Linear.units_smul_comp, star_snd_star_sndX_star_inlX_assoc,
    zero_comp, smul_zero, zero_add, add_zero, id_comp]

/-- **Reading `ΣC`**: on the `ΣC`-summand, `φᵀ` is `± φ_B j_Y ι_Y`. -/
lemma star_fstX_phiT (r : ℤ) :
    J.star (fstX (Glue.u (σ B) X Y) (N + 1 - r) (N - r) (down_rel_sub N r)) ≫ (phiT X Y).f r =
      r.negOnePow • (B.φ.f r ≫ Y.j.f r ≫ (Glue.ιY (σ B) X Y).f r) := by
  have hk : N + 1 - r = N - (r - 1) := by omega
  have h₂ : (ComplexShape.down ℤ).Rel (N - (r - 1)) (N - r) := by simp; omega
  simp only [phiT_f, relTop]
  rw [star_fstX_XIsoOfEq_assoc _ hk _ h₂]
  simp only [THns_hom, comp_add, Union.HW_hom, Union.HY_hom, Union.TG_hom, dualHom_f,
    Glue.β', comp_f, J.star_comp, assoc, star_fstX_star_ιW_assoc, star_fstX_star_ιY_assoc,
    dualHomotopy_hom, K'_hom_eq _ _ _ _ h₂, Linear.comp_units_smul, Linear.units_smul_comp,
    cone.star_fstX_inlX_assoc, zero_add, add_zero, neg_f_apply, neg_comp, comp_neg, neg_neg,
    Glue.c', Glue.jY_f, sub_add_cancel, zero_comp, neg_zero]

end Union

end

end HSFormal.LTheory
