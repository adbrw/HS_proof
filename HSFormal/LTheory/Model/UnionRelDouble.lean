import HSFormal.LTheory.Model.UnionRelCone
import HSFormal.LTheory.Model.Cobordism

/-!
# The double of a Poincaré pair is null-cobordant

For a Poincaré pair `X` with boundary `R`, the **double** `X ∪_R -X` (`PairOn.union X X.neg`)
bounds the `(N+2)`-dimensional pair `X × I`: the boundary map is the fold
`j_D : D_X ∪_C D_X ⟶ D_X`, `(x, y, z) ↦ y - z` (`Double.jD`), which kills the union structure
strictly (`j_D δφ_∪ j_D^* = 0`, so the relative structure is `0`), and is split by the chain maps
`k = (x, y) ↦ (x, y, y) : Cone(j_X) ⟶ D_X ∪ D_X`, `t = (x, y, z) ↦ (x, z)` and `y ↦ (0, y, 0)`.
By `KarSplit.isKarEquiv_relDuality` (P2, G1) its relative duality map is Poincaré because
`λ = t^* φ_∪ j_D` is exactly the relative duality map `Ψ_X` of `X` (`Double.lam_eq`).

* `Union.*`: unfolding lemmas for `PairOn.union` (the union structure is the symmetrization of
  `Glue.Hns`).
* `PairOn.doublePair`, `PairOn.nullCobordant_union_neg` (**the double bounds**),
  `Lconc.cls_union_neg_self`.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex homotopyCofiber
  HSFormal.Compression

noncomputable section

attribute [local implicit_reducible] PairOn.toPair SymPair.neg SymPair.toPairOn PairOn.union PairOn.glue
  SymPair.closedOfIsZero

universe v u

variable {V : Type u} [Category.{v} V] [Preadditive V] {J : StrictInvolution V} {N : ℤ}

variable [HasBinaryBiproducts V] [HasFiniteBiproducts V]

namespace Union

/-- The splitting `B ≅ 0 ⊕ B` used by `PairOn.union`. -/
abbrev σ (B : SymPoincare J N) : BdSplit B zeroP B := BdSplit.ofRight B zeroP rfl

variable {B : SymPoincare J N} (X : PairOn B) (Y : PairOn B.neg)

lemma β_eq : Glue.β (σ B) X = B.p ≫ X.j := rfl

@[reassoc]
lemma β_f (r : ℤ) : (Glue.β (σ B) X).f r = X.j.f r := by
  rw [β_eq, comp_f, PairOn.p_j_f]

@[reassoc (attr := simp)]
lemma K'_hom_eq (a b : ℤ) (h : (ComplexShape.down ℤ).Rel b a) :
    (Glue.K' (σ B) X Y).hom a b = inlX (Glue.u (σ B) X Y) a b h := by
  rw [Glue.K'_hom, inrCompHomotopy_hom _ _ _ _ h]

lemma K'_hom_eq_zero (a b : ℤ) (h : ¬ (ComplexShape.down ℤ).Rel b a) :
    (Glue.K' (σ B) X Y).hom a b = 0 := by
  rw [Glue.K'_hom, inrCompHomotopy_hom_eq_zero _ _ _ _ h]

lemma HW_hom (a b : ℤ) : (Glue.HW (σ B) X Y).hom a b =
    (dualHom J N (Glue.ιW (σ B) X Y)).f a ≫ X.δφ.hom a b ≫ (Glue.ιW (σ B) X Y).f b := by
  simp [Glue.HW]

lemma HY_hom (a b : ℤ) : (Glue.HY (σ B) X Y).hom a b =
    (dualHom J N (Glue.ιY (σ B) X Y)).f a ≫ Y.δφ.hom a b ≫ (Glue.ιY (σ B) X Y).f b := by
  simp [Glue.HY]

lemma G_hom (a b : ℤ) : (Glue.G (σ B) X Y).hom a b =
    (dualHomotopy J N (Glue.K' (σ B) X Y)).hom a b ≫ (-B.φ).f b ≫ (Glue.β' (σ B) X Y).f b +
      (dualHom J N (-Glue.c' (σ B) X Y)).f a ≫ (-B.φ).f a ≫ (Glue.K' (σ B) X Y).hom a b := by
  rw [Glue.G, conjHomotopy_refl_hom]

lemma TG_hom (a b : ℤ) : (transposeHomotopy J N (Glue.G (σ B) X Y)).hom a b =
    (dualHom J N (Glue.β' (σ B) X Y)).f a ≫ (-B.φ).f a ≫ (Glue.K' (σ B) X Y).hom a b +
      (dualHomotopy J N (Glue.K' (σ B) X Y)).hom a b ≫ (-B.φ).f b ≫
        (-Glue.c' (σ B) X Y).f b := by
  rw [Glue.G, transposeHomotopy_conjHomotopy_hom _ _ B.symm.neg]

variable [Linear ℚ V]

lemma union_C : (X.union Y).C = Glue.U (σ B) X Y := rfl

lemma union_p : (X.union Y).p = Glue.pU (σ B) X Y := rfl

lemma union_φ_f (r : ℤ) : (X.union Y).φ.f r = relTop (Glue.δφZ (σ B) X Y) r := rfl

lemma δφZ_hom (a b : ℤ) : (Glue.δφZ (σ B) X Y).hom a b = (1 / 2 : ℚ) •
    ((Glue.Hns (σ B) X Y).hom a b + (transposeHomotopy J N (Glue.Hns (σ B) X Y)).hom a b) := by
  rw [Glue.δφZ, symmHomotopy_hom, ← transposeHomotopy_hom]
  rfl

/-- A sandwich of the union structure equals a common value of the sandwiches of `Hns` and
`T Hns`. -/
lemma sandwich_δφZ {Z₀ Z₁ : V} (a b : ℤ) (P : Z₀ ⟶ (dualComplex J N (Glue.U (σ B) X Y)).X a)
    (Q : (Glue.U (σ B) X Y).X b ⟶ Z₁) (T : Z₀ ⟶ Z₁)
    (h₁ : P ≫ (Glue.Hns (σ B) X Y).hom a b ≫ Q = T)
    (h₂ : P ≫ (transposeHomotopy J N (Glue.Hns (σ B) X Y)).hom a b ≫ Q = T) :
    P ≫ (Glue.δφZ (σ B) X Y).hom a b ≫ Q = T := by
  rw [δφZ_hom, Linear.smul_comp, Linear.comp_smul, add_comp, comp_add, h₁, h₂, ← two_smul ℚ T,
    smul_smul]
  norm_num

end Union

/-! ### The fold map of the double -/

namespace Double

variable {R : SymPoincare J N} (X : PairOn R)

/-- `-X`, a pair on `-R`. -/
abbrev Xn : PairOn R.neg := X.toPair.neg.toPairOn

@[simp] lemma Xn_pD : (Xn X).pD = X.pD := rfl
@[simp] lemma Xn_j : (Xn X).j = X.j := rfl
lemma Xn_δφ_hom (a b : ℤ) : (Xn X).δφ.hom a b = -X.δφ.hom a b := by
  simp [Xn, PairOn.toPair, SymPair.toPairOn]

/-- The interior `D_X ⊕ D_X` of the double. -/
abbrev bS := Glue.bS X (Xn X)

/-- The gluing map `u = (j, j) : C_R ⟶ D_X ⊕ D_X`. -/
abbrev u := Glue.u (Union.σ R) X (Xn X)

/-- The fold `(y, z) ↦ p y - p z`. -/
def fold : Glue.S X (Xn X) ⟶ X.D := sumFst (bS X) ≫ X.pD - sumSnd (bS X) ≫ X.pD

@[reassoc (attr := simp)]
lemma inl_fold : sumInl (bS X) ≫ fold X = X.pD := by simp [fold]

@[reassoc (attr := simp)]
lemma inr_fold : sumInr (bS X) ≫ fold X = -X.pD := by simp [fold]

@[reassoc (attr := simp)]
lemma inl_fold_f (r : ℤ) : (sumInl (bS X)).f r ≫ (fold X).f r = X.pD.f r := by
  rw [← comp_f, inl_fold]

@[reassoc (attr := simp)]
lemma inr_fold_f (r : ℤ) : (sumInr (bS X)).f r ≫ (fold X).f r = -X.pD.f r := by
  rw [← comp_f, inr_fold, neg_f_apply]

lemma u_fold : u X ≫ fold X = 0 := by
  simp only [u, Glue.u, add_comp, assoc, inl_fold, inr_fold, comp_neg, Union.β_eq,
    PairOn.j_comp_pD, Glue.jY, PairOn.p_comp_j, Xn_j]
  simp

/-- The fold `j_D : D_X ∪_C D_X ⟶ D_X`, `(x, y, z) ↦ p y - p z`. -/
def jD : Glue.U (Union.σ R) X (Xn X) ⟶ X.D := desc (u X) (fold X) (Homotopy.ofEq (u_fold X))

@[reassoc (attr := simp)]
lemma inlX_jD (i j : ℤ) (h : (ComplexShape.down ℤ).Rel j i) :
    inlX (u X) i j h ≫ (jD X).f j = 0 := by
  rw [jD, inlX_desc_f _ _ _ _ _ h]
  rfl

@[reassoc (attr := simp)]
lemma inrX_jD (i : ℤ) : inrX (u X) i ≫ (jD X).f i = (fold X).f i := by
  rw [jD, inrX_desc_f]

@[reassoc (attr := simp)]
lemma ιW_jD : Glue.ιW (Union.σ R) X (Xn X) ≫ jD X = X.pD := by
  rw [Glue.ιW, assoc, jD, inr_desc, inl_fold]

@[reassoc (attr := simp)]
lemma ιY_jD : Glue.ιY (Union.σ R) X (Xn X) ≫ jD X = -X.pD := by
  rw [Glue.ιY, assoc, jD, inr_desc, inr_fold]

@[reassoc (attr := simp)]
lemma ιW_f_jD_f (r : ℤ) : (Glue.ιW (Union.σ R) X (Xn X)).f r ≫ (jD X).f r = X.pD.f r := by
  rw [← comp_f, ιW_jD]

@[reassoc (attr := simp)]
lemma ιY_f_jD_f (r : ℤ) : (Glue.ιY (Union.σ R) X (Xn X)).f r ≫ (jD X).f r = -X.pD.f r := by
  rw [← comp_f, ιY_jD, neg_f_apply]

@[reassoc (attr := simp)]
lemma K'_hom_jD (a b : ℤ) : (Glue.K' (Union.σ R) X (Xn X)).hom a b ≫ (jD X).f b = 0 := by
  by_cases h : (ComplexShape.down ℤ).Rel b a
  · rw [Union.K'_hom_eq _ _ _ _ h, inlX_jD]
  · rw [Union.K'_hom_eq_zero _ _ _ _ h, zero_comp]

lemma jD_kar : Glue.pU (Union.σ R) X (Xn X) ≫ jD X ≫ X.pD = jD X := by
  ext r
  apply ext_from_X (u X) (r - 1) r (down_rel_pred r)
  · simp
  · simp only [comp_f, inrX_coneMap_f_assoc, inrX_jD_assoc, inrX_jD]
    apply biprod.hom_ext' <;> simp [Glue.pS, fold, comp_f]

/-! ### The splitting `0 ⟶ Cone(j_X) ⟶ D_X ∪ D_X ⟶ D_X ⟶ 0` -/

/-- The second inclusion, typed on `D_X`. -/
def inr' : X.D ⟶ Glue.S X (Xn X) := sumInr (bS X)

/-- The diagonal `y ↦ (y, y)`. -/
def diag : X.D ⟶ Glue.S X (Xn X) := sumInl (bS X) + inr' X

@[reassoc (attr := simp)]
lemma diag_fst : diag X ≫ sumFst (bS X) = 𝟙 _ := by simp [diag, inr']

@[reassoc (attr := simp)]
lemma diag_snd : diag X ≫ sumSnd (bS X) = 𝟙 _ := by simp [diag, inr']

lemma kD_comm : R.p ≫ u X = X.j ≫ X.pD ≫ diag X := by
  simp [u, Glue.u, Union.β_eq, Glue.jY, comp_add, diag, inr']

/-- `k : Cone(j_X) ⟶ D_X ∪ D_X`, `(x, y) ↦ (x, y, y)`. -/
def kD : cone X.j ⟶ Glue.U (Union.σ R) X (Xn X) :=
  coneMap R.p (X.pD ≫ diag X) (kD_comm X)

lemma tD_comm : R.p ≫ X.j = u X ≫ sumSnd (bS X) ≫ X.pD := by
  simp [u, Glue.u, Glue.jY, add_comp]

/-- `t : D_X ∪ D_X ⟶ Cone(j_X)`, `(x, y, z) ↦ (x, z)`. -/
def tD : Glue.U (Union.σ R) X (Xn X) ⟶ cone X.j :=
  coneMap R.p (sumSnd (bS X) ≫ X.pD) (tD_comm X)

/-- `s : D_X ⟶ D_X ∪ D_X`, `y ↦ (0, y, 0)`. -/
def sD : X.D ⟶ Glue.U (Union.σ R) X (Xn X) := X.pD ≫ Glue.ιW (Union.σ R) X (Xn X)

/-- The Kar degreewise (in fact chain-level) split sequence
`0 ⟶ Cone(j_X) ⟶ D_X ∪ D_X ⟶ D_X ⟶ 0`. -/
def split : KarSplit X.coneIdem (Glue.pU (Union.σ R) X (Xn X)) X.pD (kD X) (jD X) :=
  KarSplit.ofHom (tD X) (sD X)
    (by
      simp only [tD, coneMap_comp]
      exact coneMap_ext' _ _ (by simp) (by ext r : 1; simp [Glue.pS]))
    (by simp [sD, Glue.ιW_pU])
    (by
      simp only [kD, tD, coneMap_comp]
      exact coneMap_ext' _ _ (by simp) (by simp))
    (by simp [sD])
    (by
      ext r
      apply ext_from_X (u X) (r - 1) r (down_rel_pred r)
      · simp [kD, tD, sD]
      · simp only [kD, tD, sD, comp_f, add_f_apply, comp_add, inrX_coneMap_f_assoc,
          inrX_jD_assoc, inrX_coneMap_f]
        apply biprod.hom_ext' <;> simp [Glue.pS, fold, Glue.ιW, diag, inr', comp_add, add_comp,
          sub_comp])

/-! ### The fold kills the union structure; `λ = Ψ_X` -/

@[reassoc (attr := simp)]
lemma star_jD_star_ιW (m : ℤ) : J.star ((jD X).f m) ≫ J.star ((Glue.ιW (Union.σ R) X (Xn X)).f m) =
    J.star (X.pD.f m) := by
  rw [← J.star_comp, ιW_f_jD_f]

@[reassoc (attr := simp)]
lemma star_jD_star_ιY (m : ℤ) : J.star ((jD X).f m) ≫ J.star ((Glue.ιY (Union.σ R) X (Xn X)).f m) =
    -J.star (X.pD.f m) := by
  rw [← J.star_comp, ιY_f_jD_f, J.star_neg]

@[reassoc (attr := simp)]
lemma star_jD_star_K' (a b : ℤ) :
    J.star ((jD X).f a) ≫ J.star ((Glue.K' (Union.σ R) X (Xn X)).hom b a) = 0 := by
  rw [← J.star_comp, K'_hom_jD, J.star_zero]

@[reassoc (attr := simp)]
lemma star_pD_δφ_pD (a b : ℤ) : J.star (X.pD.f (N - a)) ≫ X.δφ.hom a b ≫ X.pD.f b = X.δφ.hom a b := by
  rw [← dualHom_f, X.δφ_kar]

@[reassoc (attr := simp)]
lemma star_pD_δφ (a b : ℤ) : J.star (X.pD.f (N - a)) ≫ X.δφ.hom a b = X.δφ.hom a b := by
  rw [← X.δφ_kar, ← assoc, ← assoc, ← dualHom_f, ← comp_f, ← dualHom_comp, X.pD_idem,
    assoc, X.δφ_kar]

@[reassoc (attr := simp)]
lemma δφ_pD (a b : ℤ) : X.δφ.hom a b ≫ X.pD.f b = X.δφ.hom a b := by
  rw [← X.δφ_kar, assoc, assoc, ← comp_f, X.pD_idem, X.δφ_kar]

lemma sandHns (a b : ℤ) :
    (dualHom J N (jD X)).f a ≫ (Glue.Hns (Union.σ R) X (Xn X)).hom a b ≫ (jD X).f b = 0 := by
  rw [Glue.Hns_hom]
  simp only [Union.HW_hom, Union.HY_hom, Union.G_hom, dualHom_f, comp_add, add_comp, assoc,
    star_jD_star_ιW_assoc, star_jD_star_ιY_assoc, ιW_f_jD_f, ιY_f_jD_f, K'_hom_jD, comp_zero,
    dualHomotopy_hom, Linear.comp_units_smul, Linear.units_smul_comp, star_jD_star_K'_assoc,
    zero_comp, smul_zero, zero_add, add_zero, Xn_δφ_hom, neg_comp, comp_neg, neg_neg,
    star_pD_δφ_pD]
  abel

lemma sandTHns (a b : ℤ) :
    (dualHom J N (jD X)).f a ≫ (transposeHomotopy J N (Glue.Hns (Union.σ R) X (Xn X))).hom a b ≫
      (jD X).f b = 0 := by
  have h := congrFun (congrFun (transposeHomFamily_conjMap (J := J) (N := N) (jD X)
    (Glue.Hns (Union.σ R) X (Xn X)).hom) a) b
  rw [transposeHomotopy_hom, ← h]
  have h0 : (fun i k ↦ (dualHom J N (jD X)).f i ≫ (Glue.Hns (Union.σ R) X (Xn X)).hom i k ≫
      (jD X).f k) = fun _ _ ↦ 0 := funext₂ (sandHns X)
  rw [h0]
  simp [transposeHomFamily]

lemma ιW_tD : Glue.ιW (Union.σ R) X (Xn X) ≫ tD X = 0 := by
  rw [Glue.ιW, assoc, tD, Glue.inr_coneMap, ← assoc, sumInl_sumSnd_assoc, zero_comp, zero_comp]

lemma ιY_tD : Glue.ιY (Union.σ R) X (Xn X) ≫ tD X = X.pD ≫ inr X.j := by
  rw [Glue.ιY, assoc, tD, Glue.inr_coneMap, ← assoc, sumInr_sumSnd_assoc]

@[reassoc (attr := simp)]
lemma star_tD_star_ιW (m : ℤ) :
    J.star ((tD X).f m) ≫ J.star ((Glue.ιW (Union.σ R) X (Xn X)).f m) = 0 := by
  rw [← J.star_comp, ← comp_f, ιW_tD, zero_f, J.star_zero]

@[reassoc (attr := simp)]
lemma star_tD_star_ιY (m : ℤ) :
    J.star ((tD X).f m) ≫ J.star ((Glue.ιY (Union.σ R) X (Xn X)).f m) =
      J.star (inrX X.j m) ≫ J.star (X.pD.f m) := by
  rw [← J.star_comp, ← comp_f, ιY_tD, comp_f, J.star_comp, inr_f]

@[reassoc]
lemma star_tD_star_K' (a b : ℤ) (h : (ComplexShape.down ℤ).Rel a b) :
    J.star ((tD X).f a) ≫ J.star ((Glue.K' (Union.σ R) X (Xn X)).hom b a) =
      J.star (inlX X.j b a h) ≫ J.star (R.p.f b) := by
  rw [← J.star_comp, Union.K'_hom_eq _ _ _ _ h, tD, inlX_coneMap_f, J.star_comp]

@[reassoc (attr := simp)]
lemma β'_f_jD_f (m : ℤ) :
    (Glue.β' (Union.σ R) X (Xn X)).f m ≫ (jD X).f m = X.j.f m := by
  rw [Glue.β', comp_f, assoc, ιW_f_jD_f, Union.β_f, PairOn.j_pD_f]

@[reassoc (attr := simp)]
lemma c'_f_jD_f (m : ℤ) :
    (Glue.c' (Union.σ R) X (Xn X)).f m ≫ (jD X).f m = -X.j.f m := by
  rw [Glue.c', comp_f, assoc, ιY_f_jD_f, Glue.jY_f, Xn_j, comp_neg, PairOn.j_pD_f]

@[reassoc]
lemma star_p_φ (m : ℤ) : J.star (R.p.f (N - m)) ≫ R.φ.f m = R.φ.f m := by
  rw [← dualHom_f, ← comp_f, R.dualHom_p_comp_φ]

lemma sandT_Hns (b : ℤ) (h : (ComplexShape.down ℤ).Rel (N - (b - 1)) (N - b)) :
    J.star ((tD X).f (N - (b - 1))) ≫ (Glue.Hns (Union.σ R) X (Xn X)).hom (b - 1) b ≫
      (jD X).f b = J.star (inrX X.j (N - (b - 1))) ≫ X.δφ.hom (b - 1) b +
        (b + 1).negOnePow • (J.star (inlX X.j (N - b) (N - (b - 1)) h) ≫ R.φ.f b ≫ X.j.f b) := by
  rw [Glue.Hns_hom]
  simp only [Union.HW_hom, Union.HY_hom, Union.G_hom, dualHom_f, comp_add, add_comp, assoc,
    star_tD_star_ιW_assoc, star_tD_star_ιY_assoc, ιY_f_jD_f, K'_hom_jD, comp_zero,
    dualHomotopy_hom, Linear.comp_units_smul, Linear.units_smul_comp,
    star_tD_star_K'_assoc X _ _ h, zero_comp, zero_add, add_zero, Xn_δφ_hom, neg_comp,
    comp_neg, neg_neg, star_pD_δφ_pD, neg_f_apply, β'_f_jD_f, star_p_φ_assoc, sub_add_cancel,
    Int.negOnePow_succ, Units.neg_smul, smul_neg]
  abel

lemma sandT_THns (b : ℤ) (h : (ComplexShape.down ℤ).Rel (N - (b - 1)) (N - b)) :
    J.star ((tD X).f (N - (b - 1))) ≫
      (transposeHomotopy J N (Glue.Hns (Union.σ R) X (Xn X))).hom (b - 1) b ≫
      (jD X).f b = J.star (inrX X.j (N - (b - 1))) ≫ X.δφ.hom (b - 1) b +
        (b + 1).negOnePow • (J.star (inlX X.j (N - b) (N - (b - 1)) h) ≫ R.φ.f b ≫ X.j.f b) := by
  rw [Glue.transposeHomotopy_Hns_hom]
  simp only [Union.HW_hom, Union.HY_hom, Union.TG_hom, dualHom_f, comp_add, add_comp, assoc,
    star_tD_star_ιW_assoc, star_tD_star_ιY_assoc, ιY_f_jD_f, K'_hom_jD, comp_zero,
    dualHomotopy_hom, Linear.comp_units_smul, Linear.units_smul_comp,
    star_tD_star_K'_assoc X _ _ h, zero_comp, zero_add, add_zero, Xn_δφ_hom, neg_comp,
    comp_neg, neg_neg, star_pD_δφ_pD, neg_f_apply, c'_f_jD_f, star_p_φ_assoc, sub_add_cancel,
    Int.negOnePow_succ, Units.neg_smul, smul_neg]
  abel

variable [Linear ℚ V]

lemma jD_union_jD : dualHom J (N + 1) (jD X) ≫ (X.union (Xn X)).φ ≫ jD X = 0 := by
  ext r
  simp only [comp_f, dualHom_f, Union.union_φ_f, relTop, assoc, zero_f]
  rw [star_f_XIsoOfEq_assoc, ← dualHom_f,
    Union.sandwich_δφZ X (Xn X) _ _ _ _ 0 (sandHns X _ _) (sandTHns X _ _), comp_zero]

lemma hc : Glue.pU (Union.σ R) X (Xn X) ≫ jD X = jD X ≫ X.pD :=
  comm_of_kar (Glue.pU_idem _ X (Xn X)) X.pD_idem (jD_kar X)

lemma hi : X.coneIdem ≫ kD X ≫ Glue.pU (Union.σ R) X (Xn X) = kD X := by
  simp only [kD, coneMap_comp]
  exact coneMap_ext' _ _ (by simp) (by simp [diag, inr', Glue.pS, comp_add, add_comp])

/-- `λ = t^* φ_∪ j_D` is the relative duality map of `X`. -/
lemma lam_eq : (split X).lam (J := J) (n := N + 1) (Glue.coneIdem_idem X)
    (Glue.pU_idem _ X (Xn X)) (X.union (Xn X)).φ (jD_union_jD X) = relDuality X.δφ := by
  ext r
  have h : (ComplexShape.down ℤ).Rel (N - (r - 1)) (N - r) := by simp; omega
  have e : (split X).t (N + 1 - r) = (tD X).f (N + 1 - r) := rfl
  simp only [KarSplit.lam_f, e, Union.union_φ_f, relTop, assoc, relDuality_f]
  rw [star_f_XIsoOfEq_assoc,
    Union.sandwich_δφZ X (Xn X) _ _ _ _ _ (sandT_Hns X r h) (sandT_THns X r h), comp_add,
    Glue.XIsoOfEq_star_inrX_assoc, Linear.comp_units_smul,
    Glue.XIsoOfEq_star_inlX_assoc (hk := down_rel_sub N r)]

/-- The null-cobordism `X × I` of the double `X ∪_R -X`: the fold `D_X ∪ D_X ⟶ D_X` with
vanishing relative structure. -/
def doublePair : SymPair J (N + 1) where
  bd := X.union (Xn X)
  D := X.D
  pD := X.pD
  pD_idem := X.pD_idem
  support := X.support.mono le_rfl (by omega)
  j := jD X
  j_kar := jD_kar X
  δφ := Homotopy.ofEq (jD_union_jD X)
  δφ_kar r r' := by simp [Homotopy.ofEq]
  symm := by
    rw [IsSymmHomotopy, transposeHomotopy_hom]
    funext a b
    simp [Homotopy.ofEq, transposeHomFamily]
  poincare := by
    refine (split X).isKarEquiv_relDuality (Glue.coneIdem_idem X) (Glue.pU_idem _ X (Xn X))
      X.pD_idem (hi X) (jD_kar X) (X.union (Xn X)).φ (jD_union_jD X) (hc X)
      (X.union (Xn X)).dualHom_p_comp_φ _ (fun _ _ ↦ rfl) ?_
    rw [lam_eq]
    exact X.poincare

end Double

variable [Linear ℚ V] in
/-- **The double of a Poincaré pair is null-cobordant**: `X ∪_R -X` bounds `X × I`. -/
theorem PairOn.nullCobordant_union_neg {R : SymPoincare J N} (X : PairOn R) :
    NullCobordant (X.union X.toPair.neg.toPairOn) :=
  ⟨Double.doublePair X, rfl⟩

/-- The double has class `0`. -/
theorem Lconc.cls_union_neg_self {A : InvCat} {N : ℤ} {R : SymPoincare A.inv N} (X : PairOn R) :
    Lconc.cls (X.union X.toPair.neg.toPairOn) = 0 :=
  Lconc.cls_eq_zero X.nullCobordant_union_neg

end

end HSFormal.LTheory
