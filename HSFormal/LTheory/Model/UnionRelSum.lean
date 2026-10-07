import HSFormal.LTheory.Model.UnionRelLadder

/-!
# Unions of direct sums

For pairs `Y` on `B`, `Y₂` on `-B` and `Z` on `-B`, the union of `Y ⊕ Y₂` (a pair on
`Q = B ⊕ -B`) with the U-turn pair `Z ⊕ -Z` (a pair on `-Q`) is strictly isometric to the direct
sum of unions `(Y ∪ Z) ⊕ (Y₂ ∪ -Z)` (`UnionSum.isometry`), by the shuffle
`Cone(C_B ⊕ C_B ⟶ (D_Y ⊕ D_{Y₂}) ⊕ (D_Z ⊕ D_Z)) ≅ Cone(C_B ⟶ D_Y ⊕ D_Z) ⊕ Cone(C_B ⟶ D_{Y₂} ⊕ D_Z)`.
Hence `[(Y ⊕ Y₂) ∪ (Z ⊕ -Z)] = [Y ∪ Z] + [Y₂ ∪ -Z]` (`UnionSum.cls_union_sum`).
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex homotopyCofiber
  HSFormal.Compression

noncomputable section

attribute [local implicit_reducible] PairOn.toPair SymPair.neg SymPair.toPairOn PairOn.union PairOn.glue
  SymPair.closedOfIsZero IsStrictSymm PairOn.sum SymPoincare.HomotopyIsometry.cylinder

universe v u

variable {V : Type u} [Category.{v} V] [Preadditive V] {J : StrictInvolution V} {N : ℤ}

variable [HasBinaryBiproducts V] [HasFiniteBiproducts V]

omit [HasBinaryBiproducts V] [HasFiniteBiproducts V] in
/-- `T(a^* h c) = c^* (T h) a`. -/
lemma transposeHomFamily_conj₂ {C D : ChainComplex V ℤ} (a c : C ⟶ D)
    (h : ∀ i k, (dualComplex J N C).X i ⟶ C.X k) :
    transposeHomFamily J N (C := D) (D := D) (fun i k ↦ (dualHom J N a).f i ≫ h i k ≫ c.f k) =
      fun i k ↦ (dualHom J N c).f i ≫ transposeHomFamily J N h i k ≫ a.f k := by
  funext r r'
  simp only [transposeHomFamily, dualHom_f, J.star_comp, J.star_star, bidual_hom_f,
    Linear.units_smul_comp, Linear.comp_units_smul, assoc, f_comp_eqToHom a (sub_sub_cancel N r')]

namespace UnionSum

open Union UTurn

variable (B : SymPoincare J N) in
/-- The biproduct bicones of `B ⊕ B`. -/
abbrev bQ (r : ℤ) : BinaryBicone (B.C.X r) (B.C.X r) := BinaryBiproduct.bicone _ _

variable {B : SymPoincare J N} (Y : PairOn B) (Y₂ : PairOn B.neg) (Z : PairOn B.neg)

/-- `Y ⊕ Y₂`, a pair on `Q = B ⊕ -B`. -/
abbrev XS : PairOn (Q (bQ B)) := Y.sum Y₂ (bQ B)

/-- The bicones of `D_Y ⊕ D_{Y₂}`. -/
abbrev bY := PairSum.bD Y Y₂

/-- The bicones of `D_Z ⊕ D_Z`. -/
abbrev bZ := PairSum.bD Z (Zn Z)

/-- The gluing map of the union of sums. -/
abbrev uL := Glue.u (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z)

/-- The gluing map of `Y ∪ Z`. -/
abbrev u₁ := Glue.u (σ B) Y Z

/-- The gluing map of `Y₂ ∪ -Z`. -/
abbrev u₂ := Glue.u (σ B.neg) Y₂ (Zn Z)

/-- `π₁ : (D_Y ⊕ D_{Y₂}) ⊕ (D_Z ⊕ D_Z) ⟶ D_Y ⊕ D_Z`. -/
def π₁ : Glue.S (XS Y Y₂) (uturn (bQ B) Z) ⟶ Glue.S Y Z :=
  sumFst (Glue.bS (XS Y Y₂) (uturn (bQ B) Z)) ≫ sumFst (bY Y Y₂) ≫ sumInl (Glue.bS Y Z) +
    sumSnd (Glue.bS (XS Y Y₂) (uturn (bQ B) Z)) ≫ sumFst (bZ Z) ≫ sumInr (Glue.bS Y Z)

/-- `π₂ : (D_Y ⊕ D_{Y₂}) ⊕ (D_Z ⊕ D_Z) ⟶ D_{Y₂} ⊕ D_Z`. -/
def π₂ : Glue.S (XS Y Y₂) (uturn (bQ B) Z) ⟶ Glue.S Y₂ (Zn Z) :=
  sumFst (Glue.bS (XS Y Y₂) (uturn (bQ B) Z)) ≫ sumSnd (bY Y Y₂) ≫ sumInl (Glue.bS Y₂ (Zn Z)) +
    sumSnd (Glue.bS (XS Y Y₂) (uturn (bQ B) Z)) ≫ sumSnd (bZ Z) ≫ sumInr (Glue.bS Y₂ (Zn Z))

/-- `ι₁ : D_Y ⊕ D_Z ⟶ (D_Y ⊕ D_{Y₂}) ⊕ (D_Z ⊕ D_Z)`. -/
def ι₁ : Glue.S Y Z ⟶ Glue.S (XS Y Y₂) (uturn (bQ B) Z) :=
  sumFst (Glue.bS Y Z) ≫ sumInl (bY Y Y₂) ≫ sumInl (Glue.bS (XS Y Y₂) (uturn (bQ B) Z)) +
    sumSnd (Glue.bS Y Z) ≫ sumInl (bZ Z) ≫ sumInr (Glue.bS (XS Y Y₂) (uturn (bQ B) Z))

/-- `ι₂ : D_{Y₂} ⊕ D_Z ⟶ (D_Y ⊕ D_{Y₂}) ⊕ (D_Z ⊕ D_Z)`. -/
def ι₂ : Glue.S Y₂ (Zn Z) ⟶ Glue.S (XS Y Y₂) (uturn (bQ B) Z) :=
  sumFst (Glue.bS Y₂ (Zn Z)) ≫ sumInr (bY Y Y₂) ≫ sumInl (Glue.bS (XS Y Y₂) (uturn (bQ B) Z)) +
    sumSnd (Glue.bS Y₂ (Zn Z)) ≫ sumInr (bZ Z) ≫ sumInr (Glue.bS (XS Y Y₂) (uturn (bQ B) Z))

lemma Qp_fst : (Q (bQ B)).p ≫ sumFst (bQ B) = sumFst (bQ B) ≫ B.p := by simp [SymPoincare.sum]

lemma Qp_snd : (Q (bQ B)).p ≫ sumSnd (bQ B) = sumSnd (bQ B) ≫ B.p := by simp [SymPoincare.sum, SymPoincare.neg]

lemma inl_Qp : sumInl (bQ B) ≫ (Q (bQ B)).p = B.p ≫ sumInl (bQ B) := by simp [SymPoincare.sum]

lemma inr_Qp : sumInr (bQ B) ≫ (Q (bQ B)).p = B.p ≫ sumInr (bQ B) := by simp [SymPoincare.sum, SymPoincare.neg]

lemma comm₁ : sumFst (bQ B) ≫ u₁ Y Z = uL Y Y₂ Z ≫ π₁ Y Y₂ Z := by
  simp only [Glue.u, π₁, Glue.β, comp_add, add_comp, assoc, sumInl_sumFst_assoc,
    sumInl_sumSnd_assoc, sumInr_sumFst_assoc, sumInr_sumSnd_assoc, zero_comp, comp_zero,
    add_zero, zero_add, Glue.jY]
  rw [← assoc (σ B).ιB, ← assoc (σ (Q (bQ B))).ιB]
  simp [Union.σ, BdSplit.ofRight, XS, PairOn.sum, PairSum.j, uturn, add_comp, reassoc_of% (Qp_fst (B := B))]

lemma comm₂ : sumSnd (bQ B) ≫ u₂ Y₂ Z = uL Y Y₂ Z ≫ π₂ Y Y₂ Z := by
  simp only [Glue.u, π₂, Glue.β, comp_add, add_comp, assoc, sumInl_sumFst_assoc,
    sumInl_sumSnd_assoc, sumInr_sumFst_assoc, sumInr_sumSnd_assoc, zero_comp, comp_zero,
    add_zero, zero_add, Glue.jY]
  rw [← assoc (σ B.neg).ιB, ← assoc (σ (Q (bQ B))).ιB]
  simp [Union.σ, BdSplit.ofRight, XS, PairOn.sum, PairSum.j, uturn, add_comp, reassoc_of% (Qp_snd (B := B))]

lemma comm₁' : sumInl (bQ B) ≫ uL Y Y₂ Z = u₁ Y Z ≫ ι₁ Y Y₂ Z := by
  simp only [Glue.u, ι₁, Glue.β, comp_add, add_comp, assoc, sumInl_sumFst_assoc,
    sumInl_sumSnd_assoc, sumInr_sumFst_assoc, sumInr_sumSnd_assoc, zero_comp, comp_zero,
    add_zero, zero_add, Glue.jY]
  simp [Union.σ, BdSplit.ofRight, XS, PairOn.sum, PairSum.j, uturn, add_comp, reassoc_of% (inl_Qp (B := B))]

lemma comm₂' : sumInr (bQ B) ≫ uL Y Y₂ Z = u₂ Y₂ Z ≫ ι₂ Y Y₂ Z := by
  simp only [Glue.u, ι₂, Glue.β, comp_add, add_comp, assoc, sumInl_sumFst_assoc,
    sumInl_sumSnd_assoc, sumInr_sumFst_assoc, sumInr_sumSnd_assoc, zero_comp, comp_zero,
    add_zero, zero_add, Glue.jY]
  simp [Union.σ, BdSplit.ofRight, XS, PairOn.sum, PairSum.j, uturn, add_comp, reassoc_of% (inr_Qp (B := B))]

variable [Linear ℚ V]

/-- `e₁ : (Y ⊕ Y₂) ∪ (Z ⊕ -Z) ⟶ Y ∪ Z`. -/
def e₁ : cone (uL Y Y₂ Z) ⟶ cone (u₁ Y Z) := coneMap (sumFst (bQ B)) (π₁ Y Y₂ Z) (comm₁ Y Y₂ Z)

/-- `e₂ : (Y ⊕ Y₂) ∪ (Z ⊕ -Z) ⟶ Y₂ ∪ -Z`. -/
def e₂ : cone (uL Y Y₂ Z) ⟶ cone (u₂ Y₂ Z) := coneMap (sumSnd (bQ B)) (π₂ Y Y₂ Z) (comm₂ Y Y₂ Z)

/-- `f₁ : Y ∪ Z ⟶ (Y ⊕ Y₂) ∪ (Z ⊕ -Z)`. -/
def f₁ : cone (u₁ Y Z) ⟶ cone (uL Y Y₂ Z) := coneMap (sumInl (bQ B)) (ι₁ Y Y₂ Z) (comm₁' Y Y₂ Z)

/-- `f₂ : Y₂ ∪ -Z ⟶ (Y ⊕ Y₂) ∪ (Z ⊕ -Z)`. -/
def f₂ : cone (u₂ Y₂ Z) ⟶ cone (uL Y Y₂ Z) := coneMap (sumInr (bQ B)) (ι₂ Y Y₂ Z) (comm₂' Y Y₂ Z)

/-- The bicones of `(Y ∪ Z) ⊕ (Y₂ ∪ -Z)`. -/
abbrev c (r : ℤ) : BinaryBicone ((Y.union Z).C.X r) ((Y₂.union (Zn Z)).C.X r) :=
  BinaryBiproduct.bicone _ _

/-- The target `(Y ∪ Z) ⊕ (Y₂ ∪ -Z)`. -/
abbrev Tgt : SymPoincare J (N + 1) := (Y.union Z).sum (Y₂.union (Zn Z)) (c Y Y₂ Z)

/-- **The shuffle** `E = (e₁, e₂)`. -/
def E : ((XS Y Y₂).union (uturn (bQ B) Z)).C ⟶ (Tgt Y Y₂ Z).C :=
  e₁ Y Y₂ Z ≫ sumInl (c Y Y₂ Z) + e₂ Y Y₂ Z ≫ sumInr (c Y Y₂ Z)

/-- The inverse shuffle. -/
def Einv : (Tgt Y Y₂ Z).C ⟶ ((XS Y Y₂).union (uturn (bQ B) Z)).C :=
  sumFst (c Y Y₂ Z) ≫ f₁ Y Y₂ Z + sumSnd (c Y Y₂ Z) ≫ f₂ Y Y₂ Z

lemma πι_total (n : ℤ) :
    (π₁ Y Y₂ Z).f n ≫ (ι₁ Y Y₂ Z).f n + (π₂ Y Y₂ Z).f n ≫ (ι₂ Y Y₂ Z).f n = 𝟙 _ := by
  apply biprod.hom_ext' <;> apply biprod.hom_ext' <;> simp [π₁, π₂, ι₁, ι₂]

@[reassoc (attr := simp)]
lemma ι₁_π₁_f (n : ℤ) : (ι₁ Y Y₂ Z).f n ≫ (π₁ Y Y₂ Z).f n = 𝟙 _ := by
  apply biprod.hom_ext' <;> simp [π₁, ι₁]

@[reassoc (attr := simp)]
lemma ι₁_π₂_f (n : ℤ) : (ι₁ Y Y₂ Z).f n ≫ (π₂ Y Y₂ Z).f n = 0 := by
  apply biprod.hom_ext' <;> simp [π₂, ι₁]

@[reassoc (attr := simp)]
lemma ι₂_π₁_f (n : ℤ) : (ι₂ Y Y₂ Z).f n ≫ (π₁ Y Y₂ Z).f n = 0 := by
  apply biprod.hom_ext' <;> simp [π₁, ι₂]

@[reassoc (attr := simp)]
lemma ι₂_π₂_f (n : ℤ) : (ι₂ Y Y₂ Z).f n ≫ (π₂ Y Y₂ Z).f n = 𝟙 _ := by
  apply biprod.hom_ext' <;> simp [π₂, ι₂]

lemma E_Einv : E Y Y₂ Z ≫ Einv Y Y₂ Z = 𝟙 _ := by
  ext n
  apply ext_from_X (uL Y Y₂ Z) (n - 1) n (down_rel_pred n)
  · simp [E, Einv, e₁, e₂, f₁, f₂]
    rw [← assoc, ← assoc, ← add_comp, biprod.total, id_comp]
    erw [comp_id]
  · simp [E, Einv, e₁, e₂, f₁, f₂]
    rw [← assoc, ← assoc, ← add_comp, πι_total]
    erw [id_comp, comp_id]

lemma Einv_E : Einv Y Y₂ Z ≫ E Y Y₂ Z = 𝟙 _ := by
  ext n : 1
  apply biprod.hom_ext'
  · apply ext_from_X (u₁ Y Z) (n - 1) n (down_rel_pred n)
    · simp [E, Einv, e₁, e₂, f₁, f₂]
    · simp [E, Einv, e₁, e₂, f₁, f₂]
  · apply ext_from_X (u₂ Y₂ Z) (n - 1) n (down_rel_pred n)
    · simp [E, Einv, e₁, e₂, f₁, f₂]
    · simp [E, Einv, e₁, e₂, f₁, f₂]

/-! ### Idempotents -/

lemma π₁_pS : π₁ Y Y₂ Z ≫ Glue.pS Y Z = Glue.pS (XS Y Y₂) (uturn (bQ B) Z) ≫ π₁ Y Y₂ Z := by
  ext n : 1
  apply biprod.hom_ext' <;> apply biprod.hom_ext' <;>
    simp [π₁, Glue.pS, XS, PairOn.sum, PairSum.pD, uturn]

lemma π₂_pS : π₂ Y Y₂ Z ≫ Glue.pS Y₂ (Zn Z) = Glue.pS (XS Y Y₂) (uturn (bQ B) Z) ≫ π₂ Y Y₂ Z := by
  ext n : 1
  apply biprod.hom_ext' <;> apply biprod.hom_ext' <;>
    simp [π₂, Glue.pS, XS, PairOn.sum, PairSum.pD, uturn]

lemma e₁_pU : e₁ Y Y₂ Z ≫ Glue.pU (σ B) Y Z =
    Glue.pU (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z) ≫ e₁ Y Y₂ Z := by
  rw [e₁, coneMap_comp, coneMap_comp]
  exact coneMap_ext' _ _ (Qp_fst (B := B)).symm (π₁_pS Y Y₂ Z)

lemma e₂_pU : e₂ Y Y₂ Z ≫ Glue.pU (σ B.neg) Y₂ (Zn Z) =
    Glue.pU (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z) ≫ e₂ Y Y₂ Z := by
  rw [e₂, coneMap_comp, coneMap_comp]
  exact coneMap_ext' _ _ (Qp_snd (B := B)).symm (π₂_pS Y Y₂ Z)

lemma E_p : E Y Y₂ Z ≫ (Tgt Y Y₂ Z).p = ((XS Y Y₂).union (uturn (bQ B) Z)).p ≫ E Y Y₂ Z := by
  simp only [E, SymPoincare.sum, union_p, add_comp, comp_add, assoc, sumInl_sumFst_assoc,
    sumInl_sumSnd_assoc, sumInr_sumFst_assoc, sumInr_sumSnd_assoc, zero_comp, comp_zero,
    add_zero, zero_add]
  rw [reassoc_of% (e₁_pU Y Y₂ Z), reassoc_of% (e₂_pU Y Y₂ Z)]

/-! ### Pushforwards along `e₁`, `e₂` -/

lemma ιW_e₁ : Glue.ιW (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z) ≫ e₁ Y Y₂ Z =
    sumFst (bY Y Y₂) ≫ Glue.ιW (σ B) Y Z := by
  rw [Glue.ιW, assoc, e₁, Glue.inr_coneMap, ← assoc, Glue.ιW]
  simp [π₁]

lemma ιW_e₂ : Glue.ιW (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z) ≫ e₂ Y Y₂ Z =
    sumSnd (bY Y Y₂) ≫ Glue.ιW (σ B.neg) Y₂ (Zn Z) := by
  rw [Glue.ιW, assoc, e₂, Glue.inr_coneMap, ← assoc, Glue.ιW]
  simp [π₂]

lemma ιY_e₁ : Glue.ιY (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z) ≫ e₁ Y Y₂ Z =
    sumFst (bZ Z) ≫ Glue.ιY (σ B) Y Z := by
  rw [Glue.ιY, assoc, e₁, Glue.inr_coneMap, ← assoc, Glue.ιY]
  simp [π₁]

lemma ιY_e₂ : Glue.ιY (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z) ≫ e₂ Y Y₂ Z =
    sumSnd (bZ Z) ≫ Glue.ιY (σ B.neg) Y₂ (Zn Z) := by
  rw [Glue.ιY, assoc, e₂, Glue.inr_coneMap, ← assoc, Glue.ιY]
  simp [π₂]

lemma K'_e₁ (x y : ℤ) : (Glue.K' (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z)).hom x y ≫
    (e₁ Y Y₂ Z).f y = (sumFst (bQ B)).f x ≫ (Glue.K' (σ B) Y Z).hom x y := by
  by_cases h : (ComplexShape.down ℤ).Rel y x
  · rw [K'_hom_eq _ _ _ _ h, K'_hom_eq _ _ _ _ h, e₁, inlX_coneMap_f]
  · rw [K'_hom_eq_zero _ _ _ _ h, K'_hom_eq_zero _ _ _ _ h, zero_comp, comp_zero]

lemma K'_e₂ (x y : ℤ) : (Glue.K' (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z)).hom x y ≫
    (e₂ Y Y₂ Z).f y = (sumSnd (bQ B)).f x ≫ (Glue.K' (σ B.neg) Y₂ (Zn Z)).hom x y := by
  by_cases h : (ComplexShape.down ℤ).Rel y x
  · rw [K'_hom_eq _ _ _ _ h, K'_hom_eq _ _ _ _ h, e₂, inlX_coneMap_f]
  · rw [K'_hom_eq_zero _ _ _ _ h, K'_hom_eq_zero _ _ _ _ h, zero_comp, comp_zero]

lemma β'_e₁ : Glue.β' (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z) ≫ e₁ Y Y₂ Z =
    sumFst (bQ B) ≫ Glue.β' (σ B) Y Z := by
  rw [Glue.β', assoc, ιW_e₁, Glue.β', β_eq, β_eq, assoc, assoc]
  have hj : (XS Y Y₂).j = PairSum.j Y Y₂ (bQ B) := rfl
  simp (config := {proj := false}) only [hj, ← assoc, PairSum.j_fst, Qp_fst]

lemma β'_e₂ : Glue.β' (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z) ≫ e₂ Y Y₂ Z =
    sumSnd (bQ B) ≫ Glue.β' (σ B.neg) Y₂ (Zn Z) := by
  rw [Glue.β', assoc, ιW_e₂, Glue.β', β_eq, β_eq, assoc, assoc]
  have hj : (XS Y Y₂).j = PairSum.j Y Y₂ (bQ B) := rfl
  simp (config := {proj := false}) only [hj, ← assoc, PairSum.j_snd, Qp_snd]

lemma c'_e₁ : Glue.c' (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z) ≫ e₁ Y Y₂ Z =
    sumFst (bQ B) ≫ Glue.c' (σ B) Y Z := by
  rw [Glue.c', assoc, ιY_e₁, Glue.c', Glue.jY, Glue.jY]
  simp only [uturn, ← assoc, PairSum.j_fst]

lemma c'_e₂ : Glue.c' (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z) ≫ e₂ Y Y₂ Z =
    sumSnd (bQ B) ≫ Glue.c' (σ B.neg) Y₂ (Zn Z) := by
  rw [Glue.c', assoc, ιY_e₂, Glue.c', Glue.jY, Glue.jY]
  simp only [uturn, ← assoc, PairSum.j_snd]

/-! #### Degreewise and dual forms -/

section Forms

variable (m x y : ℤ)

@[reassoc (attr := simp)]
lemma ιW_f_e₁_f : (Glue.ιW (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z)).f m ≫ (e₁ Y Y₂ Z).f m =
    (sumFst (bY Y Y₂)).f m ≫ (Glue.ιW (σ B) Y Z).f m := by rw [← comp_f, ιW_e₁, comp_f]

@[reassoc (attr := simp)]
lemma ιW_f_e₂_f : (Glue.ιW (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z)).f m ≫ (e₂ Y Y₂ Z).f m =
    (sumSnd (bY Y Y₂)).f m ≫ (Glue.ιW (σ B.neg) Y₂ (Zn Z)).f m := by rw [← comp_f, ιW_e₂, comp_f]

@[reassoc (attr := simp)]
lemma ιY_f_e₁_f : (Glue.ιY (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z)).f m ≫ (e₁ Y Y₂ Z).f m =
    (sumFst (bZ Z)).f m ≫ (Glue.ιY (σ B) Y Z).f m := by rw [← comp_f, ιY_e₁, comp_f]

@[reassoc (attr := simp)]
lemma ιY_f_e₂_f : (Glue.ιY (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z)).f m ≫ (e₂ Y Y₂ Z).f m =
    (sumSnd (bZ Z)).f m ≫ (Glue.ιY (σ B.neg) Y₂ (Zn Z)).f m := by rw [← comp_f, ιY_e₂, comp_f]

@[reassoc (attr := simp)]
lemma β'_f_e₁_f : (Glue.β' (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z)).f m ≫ (e₁ Y Y₂ Z).f m =
    (sumFst (bQ B)).f m ≫ (Glue.β' (σ B) Y Z).f m := by rw [← comp_f, β'_e₁, comp_f]

@[reassoc (attr := simp)]
lemma β'_f_e₂_f : (Glue.β' (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z)).f m ≫ (e₂ Y Y₂ Z).f m =
    (sumSnd (bQ B)).f m ≫ (Glue.β' (σ B.neg) Y₂ (Zn Z)).f m := by rw [← comp_f, β'_e₂, comp_f]

@[reassoc (attr := simp)]
lemma c'_f_e₁_f : (Glue.c' (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z)).f m ≫ (e₁ Y Y₂ Z).f m =
    (sumFst (bQ B)).f m ≫ (Glue.c' (σ B) Y Z).f m := by rw [← comp_f, c'_e₁, comp_f]

@[reassoc (attr := simp)]
lemma c'_f_e₂_f : (Glue.c' (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z)).f m ≫ (e₂ Y Y₂ Z).f m =
    (sumSnd (bQ B)).f m ≫ (Glue.c' (σ B.neg) Y₂ (Zn Z)).f m := by rw [← comp_f, c'_e₂, comp_f]

@[reassoc (attr := simp)]
lemma K'_e₁_f : (Glue.K' (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z)).hom x y ≫
    (e₁ Y Y₂ Z).f y = (sumFst (bQ B)).f x ≫ (Glue.K' (σ B) Y Z).hom x y := K'_e₁ Y Y₂ Z x y

@[reassoc (attr := simp)]
lemma K'_e₂_f : (Glue.K' (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z)).hom x y ≫
    (e₂ Y Y₂ Z).f y = (sumSnd (bQ B)).f x ≫ (Glue.K' (σ B.neg) Y₂ (Zn Z)).hom x y :=
  K'_e₂ Y Y₂ Z x y

@[reassoc (attr := simp)]
lemma star_e₁_star_ιW : J.star ((e₁ Y Y₂ Z).f m) ≫
    J.star ((Glue.ιW (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z)).f m) =
      J.star ((Glue.ιW (σ B) Y Z).f m) ≫ J.star ((sumFst (bY Y Y₂)).f m) := by
  rw [← J.star_comp, ← J.star_comp, ιW_f_e₁_f]

@[reassoc (attr := simp)]
lemma star_e₂_star_ιW : J.star ((e₂ Y Y₂ Z).f m) ≫
    J.star ((Glue.ιW (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z)).f m) =
      J.star ((Glue.ιW (σ B.neg) Y₂ (Zn Z)).f m) ≫ J.star ((sumSnd (bY Y Y₂)).f m) := by
  rw [← J.star_comp, ← J.star_comp, ιW_f_e₂_f]

@[reassoc (attr := simp)]
lemma star_e₁_star_ιY : J.star ((e₁ Y Y₂ Z).f m) ≫
    J.star ((Glue.ιY (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z)).f m) =
      J.star ((Glue.ιY (σ B) Y Z).f m) ≫ J.star ((sumFst (bZ Z)).f m) := by
  rw [← J.star_comp, ← J.star_comp, ιY_f_e₁_f]

@[reassoc (attr := simp)]
lemma star_e₂_star_ιY : J.star ((e₂ Y Y₂ Z).f m) ≫
    J.star ((Glue.ιY (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z)).f m) =
      J.star ((Glue.ιY (σ B.neg) Y₂ (Zn Z)).f m) ≫ J.star ((sumSnd (bZ Z)).f m) := by
  rw [← J.star_comp, ← J.star_comp, ιY_f_e₂_f]

@[reassoc (attr := simp)]
lemma star_e₁_star_β' : J.star ((e₁ Y Y₂ Z).f m) ≫
    J.star ((Glue.β' (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z)).f m) =
      J.star ((Glue.β' (σ B) Y Z).f m) ≫ J.star ((sumFst (bQ B)).f m) := by
  rw [← J.star_comp, ← J.star_comp, β'_f_e₁_f]

@[reassoc (attr := simp)]
lemma star_e₂_star_β' : J.star ((e₂ Y Y₂ Z).f m) ≫
    J.star ((Glue.β' (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z)).f m) =
      J.star ((Glue.β' (σ B.neg) Y₂ (Zn Z)).f m) ≫ J.star ((sumSnd (bQ B)).f m) := by
  rw [← J.star_comp, ← J.star_comp, β'_f_e₂_f]

@[reassoc (attr := simp)]
lemma star_e₁_star_c' : J.star ((e₁ Y Y₂ Z).f m) ≫
    J.star ((Glue.c' (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z)).f m) =
      J.star ((Glue.c' (σ B) Y Z).f m) ≫ J.star ((sumFst (bQ B)).f m) := by
  rw [← J.star_comp, ← J.star_comp, c'_f_e₁_f]

@[reassoc (attr := simp)]
lemma star_e₂_star_c' : J.star ((e₂ Y Y₂ Z).f m) ≫
    J.star ((Glue.c' (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z)).f m) =
      J.star ((Glue.c' (σ B.neg) Y₂ (Zn Z)).f m) ≫ J.star ((sumSnd (bQ B)).f m) := by
  rw [← J.star_comp, ← J.star_comp, c'_f_e₂_f]

@[reassoc (attr := simp)]
lemma star_e₁_star_K' : J.star ((e₁ Y Y₂ Z).f y) ≫
    J.star ((Glue.K' (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z)).hom x y) =
      J.star ((Glue.K' (σ B) Y Z).hom x y) ≫ J.star ((sumFst (bQ B)).f x) := by
  rw [← J.star_comp, ← J.star_comp, K'_e₁_f]

@[reassoc (attr := simp)]
lemma star_e₂_star_K' : J.star ((e₂ Y Y₂ Z).f y) ≫
    J.star ((Glue.K' (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z)).hom x y) =
      J.star ((Glue.K' (σ B.neg) Y₂ (Zn Z)).hom x y) ≫ J.star ((sumSnd (bQ B)).f x) := by
  rw [← J.star_comp, ← J.star_comp, K'_e₂_f]

end Forms

/-! ### The blocks of the pushforward of `Hns` -/

lemma Hns₁₁ (a b : ℤ) : (dualHom J N (e₁ Y Y₂ Z)).f a ≫
    (Glue.Hns (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z)).hom a b ≫ (e₁ Y Y₂ Z).f b =
      (Glue.Hns (σ B) Y Z).hom a b := by
  rw [Glue.Hns_hom, Glue.Hns_hom]
  simp only [HW_hom, HY_hom, G_hom, dualHom_f, comp_add, add_comp, assoc, dualHomotopy_hom,
    Linear.comp_units_smul, Linear.units_smul_comp, neg_f_apply, J.star_neg, neg_comp, comp_neg,
    star_e₁_star_ιW_assoc, star_e₁_star_ιY_assoc, star_e₁_star_K'_assoc, star_e₁_star_c'_assoc,
    ιW_f_e₁_f, ιY_f_e₁_f, β'_f_e₁_f, K'_e₁_f]
  simp [XS, PairOn.sum, PairSum.δφ_hom, uturn, SymPoincare.sum]

lemma Hns₁₂ (a b : ℤ) : (dualHom J N (e₁ Y Y₂ Z)).f a ≫
    (Glue.Hns (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z)).hom a b ≫ (e₂ Y Y₂ Z).f b = 0 := by
  rw [Glue.Hns_hom]
  simp only [HW_hom, HY_hom, G_hom, dualHom_f, comp_add, add_comp, assoc, dualHomotopy_hom,
    Linear.comp_units_smul, Linear.units_smul_comp, neg_f_apply, J.star_neg, neg_comp, comp_neg,
    star_e₁_star_ιW_assoc, star_e₁_star_ιY_assoc, star_e₁_star_K'_assoc, star_e₁_star_c'_assoc,
    ιW_f_e₂_f, ιY_f_e₂_f, β'_f_e₂_f, K'_e₂_f]
  simp [XS, PairOn.sum, PairSum.δφ_hom, uturn, SymPoincare.sum]

lemma Hns₂₁ (a b : ℤ) : (dualHom J N (e₂ Y Y₂ Z)).f a ≫
    (Glue.Hns (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z)).hom a b ≫ (e₁ Y Y₂ Z).f b = 0 := by
  rw [Glue.Hns_hom]
  simp only [HW_hom, HY_hom, G_hom, dualHom_f, comp_add, add_comp, assoc, dualHomotopy_hom,
    Linear.comp_units_smul, Linear.units_smul_comp, neg_f_apply, J.star_neg, neg_comp, comp_neg,
    star_e₂_star_ιW_assoc, star_e₂_star_ιY_assoc, star_e₂_star_K'_assoc, star_e₂_star_c'_assoc,
    ιW_f_e₁_f, ιY_f_e₁_f, β'_f_e₁_f, K'_e₁_f]
  simp [XS, PairOn.sum, PairSum.δφ_hom, uturn, SymPoincare.sum]

lemma Hns₂₂ (a b : ℤ) : (dualHom J N (e₂ Y Y₂ Z)).f a ≫
    (Glue.Hns (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z)).hom a b ≫ (e₂ Y Y₂ Z).f b =
      (Glue.Hns (σ B.neg) Y₂ (Zn Z)).hom a b := by
  rw [Glue.Hns_hom, Glue.Hns_hom]
  simp only [HW_hom, HY_hom, G_hom, dualHom_f, comp_add, add_comp, assoc, dualHomotopy_hom,
    Linear.comp_units_smul, Linear.units_smul_comp, neg_f_apply, J.star_neg, neg_comp, comp_neg,
    star_e₂_star_ιW_assoc, star_e₂_star_ιY_assoc, star_e₂_star_K'_assoc, star_e₂_star_c'_assoc,
    ιW_f_e₂_f, ιY_f_e₂_f, β'_f_e₂_f, K'_e₂_f]
  simp [XS, PairOn.sum, PairSum.δφ_hom, uturn, SymPoincare.sum]

/-! ### The blocks of the pushforward of the union structure -/

lemma THns_block {U₁ U₂ : ChainComplex V ℤ} (x : cone (uL Y Y₂ Z) ⟶ U₁)
    (y : cone (uL Y Y₂ Z) ⟶ U₂) (a b : ℤ) :
    (dualHom J N x).f a ≫ (transposeHomotopy J N
      (Glue.Hns (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z))).hom a b ≫ y.f b =
    transposeHomFamily J N (C := U₂) (D := U₁) (fun i k ↦ (dualHom J N y).f i ≫
      (Glue.Hns (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z)).hom i k ≫ x.f k) a b := by
  simp only [transposeHomotopy_hom, transposeHomFamily, dualHom_f, J.star_comp, J.star_star,
    bidual_hom_f, Linear.units_smul_comp, Linear.comp_units_smul, assoc,
    f_comp_eqToHom y (sub_sub_cancel N b)]

omit [HasBinaryBiproducts V] [HasFiniteBiproducts V] [Linear ℚ V] in
lemma transposeHomFamily_zero' {C D : ChainComplex V ℤ} :
    transposeHomFamily J N (C := C) (D := D) (fun _ _ ↦ 0) = fun _ _ ↦ 0 := by
  funext r r'
  simp [transposeHomFamily]

lemma δφZ₁₁ (a b : ℤ) : (dualHom J N (e₁ Y Y₂ Z)).f a ≫
    (Glue.δφZ (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z)).hom a b ≫ (e₁ Y Y₂ Z).f b =
      (Glue.δφZ (σ B) Y Z).hom a b := by
  have e : (fun i k ↦ (dualHom J N (e₁ Y Y₂ Z)).f i ≫
      (Glue.Hns (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z)).hom i k ≫ (e₁ Y Y₂ Z).f k) =
        (Glue.Hns (σ B) Y Z).hom := funext₂ (Hns₁₁ Y Y₂ Z)
  rw [δφZ_hom, δφZ_hom, Linear.smul_comp, Linear.comp_smul, add_comp, comp_add, Hns₁₁,
    THns_block, e, transposeHomotopy_hom]

lemma δφZ₂₂ (a b : ℤ) : (dualHom J N (e₂ Y Y₂ Z)).f a ≫
    (Glue.δφZ (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z)).hom a b ≫ (e₂ Y Y₂ Z).f b =
      (Glue.δφZ (σ B.neg) Y₂ (Zn Z)).hom a b := by
  have e : (fun i k ↦ (dualHom J N (e₂ Y Y₂ Z)).f i ≫
      (Glue.Hns (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z)).hom i k ≫ (e₂ Y Y₂ Z).f k) =
        (Glue.Hns (σ B.neg) Y₂ (Zn Z)).hom := funext₂ (Hns₂₂ Y Y₂ Z)
  rw [δφZ_hom, δφZ_hom, Linear.smul_comp, Linear.comp_smul, add_comp, comp_add, Hns₂₂,
    THns_block, e, transposeHomotopy_hom]

lemma δφZ₁₂ (a b : ℤ) : (dualHom J N (e₁ Y Y₂ Z)).f a ≫
    (Glue.δφZ (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z)).hom a b ≫ (e₂ Y Y₂ Z).f b = 0 := by
  have e : (fun i k ↦ (dualHom J N (e₂ Y Y₂ Z)).f i ≫
      (Glue.Hns (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z)).hom i k ≫ (e₁ Y Y₂ Z).f k) =
        fun _ _ ↦ 0 := funext₂ (Hns₂₁ Y Y₂ Z)
  rw [δφZ_hom, Linear.smul_comp, Linear.comp_smul, add_comp, comp_add, Hns₁₂,
    THns_block, e, transposeHomFamily_zero', zero_add, smul_zero]

lemma δφZ₂₁ (a b : ℤ) : (dualHom J N (e₂ Y Y₂ Z)).f a ≫
    (Glue.δφZ (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z)).hom a b ≫ (e₁ Y Y₂ Z).f b = 0 := by
  have e : (fun i k ↦ (dualHom J N (e₁ Y Y₂ Z)).f i ≫
      (Glue.Hns (σ (Q (bQ B))) (XS Y Y₂) (uturn (bQ B) Z)).hom i k ≫ (e₂ Y Y₂ Z).f k) =
        fun _ _ ↦ 0 := funext₂ (Hns₁₂ Y Y₂ Z)
  rw [δφZ_hom, Linear.smul_comp, Linear.comp_smul, add_comp, comp_add, Hns₂₁,
    THns_block, e, transposeHomFamily_zero', zero_add, smul_zero]

/-! ### The union structures -/

@[reassoc]
lemma φ₁₁ : dualHom J (N + 1) (e₁ Y Y₂ Z) ≫ ((XS Y Y₂).union (uturn (bQ B) Z)).φ ≫
    e₁ Y Y₂ Z = (Y.union Z).φ := by
  ext r
  simp only [comp_f, dualHom_f, union_φ_f, relTop, assoc]
  rw [star_f_XIsoOfEq_assoc, ← dualHom_f, δφZ₁₁]

@[reassoc]
lemma φ₂₂ : dualHom J (N + 1) (e₂ Y Y₂ Z) ≫ ((XS Y Y₂).union (uturn (bQ B) Z)).φ ≫
    e₂ Y Y₂ Z = (Y₂.union (Zn Z)).φ := by
  ext r
  simp only [comp_f, dualHom_f, union_φ_f, relTop, assoc]
  rw [star_f_XIsoOfEq_assoc, ← dualHom_f, δφZ₂₂]

@[reassoc]
lemma φ₁₂ : dualHom J (N + 1) (e₁ Y Y₂ Z) ≫ ((XS Y Y₂).union (uturn (bQ B) Z)).φ ≫
    e₂ Y Y₂ Z = 0 := by
  ext r
  simp only [comp_f, dualHom_f, union_φ_f, relTop, assoc, zero_f]
  rw [star_f_XIsoOfEq_assoc, ← dualHom_f, δφZ₁₂, comp_zero]

@[reassoc]
lemma φ₂₁ : dualHom J (N + 1) (e₂ Y Y₂ Z) ≫ ((XS Y Y₂).union (uturn (bQ B) Z)).φ ≫
    e₁ Y Y₂ Z = 0 := by
  ext r
  simp only [comp_f, dualHom_f, union_φ_f, relTop, assoc, zero_f]
  rw [star_f_XIsoOfEq_assoc, ← dualHom_f, δφZ₂₁, comp_zero]

lemma E_φ : dualHom J (N + 1) (E Y Y₂ Z) ≫ ((XS Y Y₂).union (uturn (bQ B) Z)).φ ≫ E Y Y₂ Z =
    (Tgt Y Y₂ Z).φ := by
  simp only [E, dualHom_add, dualHom_comp, add_comp, comp_add, assoc, φ₁₁_assoc, φ₁₂_assoc,
    φ₂₁_assoc, φ₂₂_assoc, zero_comp, comp_zero, add_zero, zero_add]

/-- **The union of sums is the sum of unions**: `(Y ⊕ Y₂) ∪ (Z ⊕ -Z) ≅ (Y ∪ Z) ⊕ (Y₂ ∪ -Z)`. -/
def isometry : ((XS Y Y₂).union (uturn (bQ B) Z)).HomotopyIsometry (Tgt Y Y₂ Z) :=
  SymPoincare.HomotopyIsometry.ofIso ⟨E Y Y₂ Z, Einv Y Y₂ Z, E_Einv Y Y₂ Z, Einv_E Y Y₂ Z⟩
    (E_p Y Y₂ Z) (E_φ Y Y₂ Z)

end UnionSum

/-- `[(Y ⊕ Y₂) ∪ (Z ⊕ -Z)] = [Y ∪ Z] + [Y₂ ∪ -Z]`. -/
theorem UnionSum.cls_union_sum {A : InvCat} {N : ℤ} {B : SymPoincare A.inv N} (Y : PairOn B)
    (Y₂ Z : PairOn B.neg) :
    Lconc.cls ((UnionSum.XS Y Y₂).union (UTurn.uturn (UnionSum.bQ B) Z)) =
      Lconc.cls (Y.union Z) + Lconc.cls (Y₂.union (UTurn.Zn Z)) := by
  rw [Lconc.cls_eq_of_isometry (UnionSum.isometry Y Y₂ Z), Lconc.cls_sum]

end

end HSFormal.LTheory
