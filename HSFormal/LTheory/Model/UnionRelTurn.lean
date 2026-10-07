import HSFormal.LTheory.Model.UnionRelTrans

/-!
# The U-turn: unions with `Z ⊕ -Z` and with the cylinder are cobordant

For a Poincaré pair `X` with boundary `Q = B ⊕ -B` and a pair `Z` with boundary `-B`, let
`W₀ = Z ⊕ -Z` (a pair on `-Q`, `UTurn.uturn`) and `Cyl = -(B × I)` (the cylinder of the identity of
`B`, also a pair on `-Q`, `UTurn.cyl`).  Then

  `X ∪ W₀ ⊔ -(X ∪ Cyl)` bounds `W' = D_X ∪_{C_Q} D_Z`  (`UTurn.nullCobordant`),

the union of `X × I` with the U-turn `Z × I` (a triad from `Z ⊕ -Z` to `Cyl`) along `Q × I`.  The
boundary map is `f_a ⊕ f_b` with `f_a = 1 ∪ (1, fold)`, `f_b = 1 ∪ (1, j_Z)`; it kills the union
structures exactly (the relative structure is `0`).  It is degreewise split surjective with kernel
`K = Cone(C_Q ⟶ D_X ⊕ D_Z ⊕ C_B)` (`UTurn.split`), so the relative duality map factors through
`λ = t^* φ j : K^{N+1-*} ⟶ W'` (P2, `KarSplit.isKarEquiv_relDuality`), after replacing the union
structures by their transposes (`Union.phiT`, `Union.unionPhiTHomotopy`).  `λ` is a Kar
equivalence by two-out-of-three on the ladder

  `0 ⟶ B'^{N+1-*} ⟶ K^{N+1-*} ⟶ D_X^{N+1-*} ⟶ 0`  over  `0 ⟶ D_Z ⟶ W' ⟶ Cone(j_X) ⟶ 0`

with outer maps `c^* Ψ_Z` (`c : Cone(j_Z) ≃ B' = Cone(C_Q ⟶ D_Z ⊕ C_B)`) and `TΨ_X`.
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

namespace UTurn

open Union

variable {B : SymPoincare J N} (b : ∀ r, BinaryBicone (B.C.X r) (B.C.X r))

/-- `Q = B ⊕ -B`. -/
abbrev Q : SymPoincare J N := B.sum B.neg b

/-! ### The two pairs on `-Q` -/

variable (Z : PairOn B.neg)

/-- `-Z`, a pair on `--B`. -/
abbrev Zn : PairOn B.neg.neg := Z.toPair.neg.toPairOn

/-- `j_Z`, typed on `C_B`. -/
def kZ : B.C ⟶ Z.D := Z.j

lemma sum_neg_φ : (B.neg.sum B.neg.neg b).φ = (Q b).neg.φ := by
  simp [SymPoincare.sum, comp_add, add_comp, neg_add]
  abel

omit [HasFiniteBiproducts V] in
lemma relDuality_congr {C D : ChainComplex V ℤ} {j : C ⟶ D} {φ₁ φ₂ : dualComplex J N C ⟶ C}
    (h : φ₁ = φ₂) (H : Homotopy (dualHom J N j ≫ φ₁ ≫ j) 0)
    (e : dualHom J N j ≫ φ₁ ≫ j = dualHom J N j ≫ φ₂ ≫ j) :
    relDuality (homotopyCongr H e rfl) = relDuality H := by
  subst h; rfl

/-- `W₀ = Z ⊕ -Z` as a pair on `-Q = -(B ⊕ -B)`. -/
@[implicit_reducible]
def uturn : PairOn (Q b).neg where
  D := PairSum.D Z (Zn Z)
  pD := PairSum.pD Z (Zn Z)
  pD_idem := PairSum.pD_idem Z (Zn Z)
  support := PairSum.pD_support Z (Zn Z)
  j := PairSum.j Z (Zn Z) b
  j_kar := PairSum.j_kar Z (Zn Z) b
  δφ := homotopyCongr (PairSum.δφ Z (Zn Z) b) (by rw [sum_neg_φ]) rfl
  δφ_kar := PairSum.δφ_kar Z (Zn Z) b
  symm := PairSum.δφ_symm Z (Zn Z) b
  poincare := (PairSum.poincare Z (Zn Z) b).of_eq (relDuality_congr (sum_neg_φ b) _ _).symm

variable [Linear ℚ V]

/-- The cylinder `-(B × I)` as a pair on `-Q`. -/
abbrev cyl : PairOn (Q b).neg :=
  ((SymPoincare.HomotopyIsometry.refl B).cylinder b).neg.toPairOn

/-- The boundary map `(x, y) ↦ p x + p y` of the cylinder, typed on `C_Q`. -/
def cJ : (Q b).C ⟶ B.C := sumFst b ≫ B.p + sumSnd b ≫ B.p

lemma cyl_j : (cyl b).j = cJ b := rfl

lemma cyl_pD : (cyl b).pD = B.p := rfl

lemma cyl_δφ_hom (a c : ℤ) : (cyl b).δφ.hom a c = 0 := by
  change (-1 : ℤ) • ((SymPoincare.HomotopyIsometry.refl B).cylδφ b).hom a c = 0
  rw [SymPoincare.HomotopyIsometry.cylδφ_hom]
  simp [SymPoincare.HomotopyIsometry.cylHomotopy, symmHomotopy_hom, karHomotopy,
    transposeHomFamily, Homotopy.ofEq, Homotopy.compRight]

/-! ### The unions and the null-cobordism `W' = D_X ∪_{C_Q} D_Z` -/

variable {b} (X : PairOn (Q b))

/-- `U_a = X ∪ (Z ⊕ -Z)`. -/
abbrev Ua : SymPoincare J (N + 1) := X.union (uturn b Z)

/-- `U_b = X ∪ Cyl`. -/
abbrev Ub : SymPoincare J (N + 1) := X.union (cyl b)

/-- The bicones of `D_X ⊕ D_Z`. -/
abbrev bW (r : ℤ) : BinaryBicone (X.D.X r) (Z.D.X r) := BinaryBiproduct.bicone _ _

/-- `D_X ⊕ D_Z`. -/
abbrev SW : ChainComplex V ℤ := sumComplex (bW Z X)

/-- `w = (β, c j_Z) : C_Q ⟶ D_X ⊕ D_Z`. -/
def w : (Q b).C ⟶ SW Z X :=
  Glue.β (σ (Q b)) X ≫ sumInl (bW Z X) + (cJ b ≫ kZ Z) ≫ sumInr (bW Z X)

/-- **The null-cobordism** `W' = Cone(w) = D_X ∪_{C_Q} D_Z`. -/
abbrev W' : ChainComplex V ℤ := cone (w Z X)

/-- The idempotent `p_X ⊕ p_Z` of `D_X ⊕ D_Z`. -/
def pSW : SW Z X ⟶ SW Z X :=
  sumFst (bW Z X) ≫ X.pD ≫ sumInl (bW Z X) + sumSnd (bW Z X) ≫ Z.pD ≫ sumInr (bW Z X)

@[reassoc (attr := simp)]
lemma B_p_kZ : B.p ≫ kZ Z = kZ Z := Z.p_comp_j

@[reassoc (attr := simp)]
lemma kZ_pD : kZ Z ≫ Z.pD = kZ Z := Z.j_comp_pD

@[reassoc (attr := simp)]
lemma B_p_kZ_f (r : ℤ) : B.p.f r ≫ (kZ Z).f r = (kZ Z).f r := by rw [← comp_f, B_p_kZ]

@[reassoc (attr := simp)]
lemma kZ_pD_f (r : ℤ) : (kZ Z).f r ≫ Z.pD.f r = (kZ Z).f r := by rw [← comp_f, kZ_pD]

@[reassoc]
lemma Qp_cJ : (Q b).p ≫ cJ b = cJ b := by
  simp [cJ, SymPoincare.sum, add_comp, comp_add]

lemma w_comm : (Q b).p ≫ w Z X = w Z X ≫ pSW Z X := by
  have h₁ : (Q b).p ≫ Glue.β (σ (Q b)) X = Glue.β (σ (Q b)) X := by
    rw [β_eq, ← assoc, (Q b).p_idem]
  have h₂ : Glue.β (σ (Q b)) X ≫ X.pD = Glue.β (σ (Q b)) X := by rw [β_eq, assoc, X.j_comp_pD]
  rw [w, comp_add, reassoc_of% h₁, assoc (cJ b), Qp_cJ_assoc]
  simp only [comp_add, add_comp, assoc, pSW, sumInl_sumFst_assoc, sumInl_sumSnd_assoc,
    sumInr_sumFst_assoc, sumInr_sumSnd_assoc, zero_comp, comp_zero, add_zero, zero_add,
    reassoc_of% h₁, reassoc_of% h₂, Qp_cJ_assoc, kZ_pD_assoc]

/-- The idempotent of `W'`. -/
abbrev pW : W' Z X ⟶ W' Z X := coneMap (Q b).p (pSW Z X) (w_comm Z X)

/-! ### The boundary map `f_a ⊕ f_b : U_a ⊕ U_b ⟶ W'` -/

/-- The second projection `D_Z ⊕ D_Z ⟶ D_Z`, typed on `D_Z`. -/
def sndD : PairSum.D Z (Zn Z) ⟶ Z.D := sumSnd (PairSum.bD Z (Zn Z))

/-- The fold `(e₁, e₂) ↦ p e₁ + p e₂ : D_Z ⊕ D_Z ⟶ D_Z`. -/
def fold : PairSum.D Z (Zn Z) ⟶ Z.D := (sumFst (PairSum.bD Z (Zn Z)) + sndD Z) ≫ Z.pD

@[reassoc (attr := simp)]
lemma inl_fold : sumInl (PairSum.bD Z (Zn Z)) ≫ fold Z = Z.pD := by
  simp [fold, sndD]

@[reassoc (attr := simp)]
lemma inr_fold : sumInr (PairSum.bD Z (Zn Z)) ≫ fold Z = Z.pD := by
  simp [fold, sndD]

@[reassoc (attr := simp)]
lemma inl_fold_f (r : ℤ) : (sumInl (PairSum.bD Z (Zn Z))).f r ≫ (fold Z).f r = Z.pD.f r := by
  rw [← comp_f, inl_fold]

@[reassoc (attr := simp)]
lemma inr_fold_f (r : ℤ) : (sumInr (PairSum.bD Z (Zn Z))).f r ≫ (fold Z).f r = Z.pD.f r := by
  rw [← comp_f, inr_fold]

lemma j_fold : (uturn b Z).j ≫ fold Z = cJ b ≫ kZ Z := by
  have h : B.p ≫ Z.j = Z.j := Z.p_comp_j
  simp [uturn, PairSum.j, cJ, kZ, add_comp, comp_add, h]

/-- `(y, e₁, e₂) ↦ (p y, fold(e₁, e₂))`. -/
def na : Glue.S X (uturn b Z) ⟶ SW Z X :=
  sumFst (Glue.bS X (uturn b Z)) ≫ X.pD ≫ sumInl (bW Z X) +
    sumSnd (Glue.bS X (uturn b Z)) ≫ fold Z ≫ sumInr (bW Z X)

/-- `(y, c) ↦ (p y, j_Z c)`. -/
def nb : Glue.S X (cyl b) ⟶ SW Z X :=
  sumFst (Glue.bS X (cyl b)) ≫ X.pD ≫ sumInl (bW Z X) +
    sumSnd (Glue.bS X (cyl b)) ≫ kZ Z ≫ sumInr (bW Z X)

lemma β_pD : Glue.β (σ (Q b)) X ≫ X.pD = Glue.β (σ (Q b)) X := by rw [β_eq, assoc, X.j_comp_pD]

lemma Qp_β : (Q b).p ≫ Glue.β (σ (Q b)) X = Glue.β (σ (Q b)) X := by
  rw [β_eq, ← assoc, (Q b).p_idem]

lemma Qp_w : (Q b).p ≫ w Z X =
    Glue.β (σ (Q b)) X ≫ sumInl (bW Z X) + cJ b ≫ kZ Z ≫ sumInr (bW Z X) := by
  rw [w, comp_add, reassoc_of% (Qp_β X), assoc (cJ b), Qp_cJ_assoc]

lemma na_comm : (Q b).p ≫ w Z X = Glue.u (σ (Q b)) X (uturn b Z) ≫ na Z X := by
  rw [Qp_w]
  simp only [Glue.u, na, comp_add, add_comp, assoc, sumInl_sumFst_assoc, sumInl_sumSnd_assoc,
    sumInr_sumFst_assoc, sumInr_sumSnd_assoc, zero_comp, comp_zero, add_zero, zero_add,
    reassoc_of% (Qp_β X), reassoc_of% (β_pD X), Qp_cJ_assoc, Glue.jY]
  rw [← assoc (uturn b Z).j, j_fold, assoc]

lemma nb_comm : (Q b).p ≫ w Z X = Glue.u (σ (Q b)) X (cyl b) ≫ nb Z X := by
  rw [Qp_w]
  simp only [Glue.u, nb, comp_add, add_comp, assoc, sumInl_sumFst_assoc, sumInl_sumSnd_assoc,
    sumInr_sumFst_assoc, sumInr_sumSnd_assoc, zero_comp, comp_zero, add_zero, zero_add,
    reassoc_of% (Qp_β X), reassoc_of% (β_pD X), Qp_cJ_assoc, Glue.jY, cyl_j]

/-- `f_a : X ∪ (Z ⊕ -Z) ⟶ W'`, the identity on `ΣC_Q ⊕ D_X` and the fold on `D_Z ⊕ D_Z`. -/
def fa : Glue.U (σ (Q b)) X (uturn b Z) ⟶ W' Z X := coneMap (Q b).p (na Z X) (na_comm Z X)

/-- `f_b : X ∪ Cyl ⟶ W'`, the identity on `ΣC_Q ⊕ D_X` and `j_Z` on `C_B`. -/
def fb : Glue.U (σ (Q b)) X (cyl b) ⟶ W' Z X := coneMap (Q b).p (nb Z X) (nb_comm Z X)

lemma pS_na : Glue.pS X (uturn b Z) ≫ na Z X ≫ pSW Z X = na Z X := by
  ext r : 1
  apply biprod.hom_ext'
  · simp [Glue.pS, na, pSW]
  · simp only [Glue.pS, na, pSW, comp_f, add_f_apply, comp_add, add_comp, assoc]
    apply biprod.hom_ext' <;>
      simp [uturn, fold, sndD, PairSum.pD, comp_add, add_comp]

lemma pS_nb : Glue.pS X (cyl b) ≫ nb Z X ≫ pSW Z X = nb Z X := by
  ext r : 1
  apply biprod.hom_ext' <;> simp [Glue.pS, nb, pSW, cyl_pD]

lemma fa_kar : Glue.pU (σ (Q b)) X (uturn b Z) ≫ fa Z X ≫ pW Z X = fa Z X := by
  simp only [fa, coneMap_comp]
  exact coneMap_ext' _ _ (by simp) (pS_na Z X)

lemma fb_kar : Glue.pU (σ (Q b)) X (cyl b) ≫ fb Z X ≫ pW Z X = fb Z X := by
  simp only [fb, coneMap_comp]
  exact coneMap_ext' _ _ (by simp) (pS_nb Z X)

/-! #### Pushforwards along `f_a`, `f_b` -/

/-- The common pushforward `p_Q ≫ inlX` of the cone homotopies. -/
def Kw (x y : ℤ) : (Q b).C.X x ⟶ (W' Z X).X y :=
  if h : (ComplexShape.down ℤ).Rel y x then (Q b).p.f x ≫ inlX (w Z X) x y h else 0

lemma K'_fa (x y : ℤ) :
    (Glue.K' (σ (Q b)) X (uturn b Z)).hom x y ≫ (fa Z X).f y = Kw Z X x y := by
  by_cases h : (ComplexShape.down ℤ).Rel y x
  · rw [K'_hom_eq _ _ _ _ h, Kw, dif_pos h, fa, inlX_coneMap_f]
  · rw [K'_hom_eq_zero _ _ _ _ h, Kw, dif_neg h, zero_comp]

lemma K'_fb (x y : ℤ) :
    (Glue.K' (σ (Q b)) X (cyl b)).hom x y ≫ (fb Z X).f y = Kw Z X x y := by
  by_cases h : (ComplexShape.down ℤ).Rel y x
  · rw [K'_hom_eq _ _ _ _ h, Kw, dif_pos h, fb, inlX_coneMap_f]
  · rw [K'_hom_eq_zero _ _ _ _ h, Kw, dif_neg h, zero_comp]

/-- `ι_X : D_X ⟶ W'`. -/
abbrev ιX : X.D ⟶ W' Z X := sumInl (bW Z X) ≫ inr (w Z X)

/-- `ι_Z : D_Z ⟶ W'`. -/
abbrev ιZ : Z.D ⟶ W' Z X := sumInr (bW Z X) ≫ inr (w Z X)

lemma ιW_fa : Glue.ιW (σ (Q b)) X (uturn b Z) ≫ fa Z X = X.pD ≫ ιX Z X := by
  rw [Glue.ιW, assoc, fa, Glue.inr_coneMap, ← assoc, na]
  simp

lemma ιW_fb : Glue.ιW (σ (Q b)) X (cyl b) ≫ fb Z X = X.pD ≫ ιX Z X := by
  rw [Glue.ιW, assoc, fb, Glue.inr_coneMap, ← assoc, nb]
  simp

lemma ιY_fa : Glue.ιY (σ (Q b)) X (uturn b Z) ≫ fa Z X = fold Z ≫ ιZ Z X := by
  rw [Glue.ιY, assoc, fa, Glue.inr_coneMap, ← assoc, na]
  simp

lemma ιY_fb : Glue.ιY (σ (Q b)) X (cyl b) ≫ fb Z X = kZ Z ≫ ιZ Z X := by
  rw [Glue.ιY, assoc, fb, Glue.inr_coneMap, ← assoc, nb]
  simp

lemma β'_fa : Glue.β' (σ (Q b)) X (uturn b Z) ≫ fa Z X = Glue.β (σ (Q b)) X ≫ ιX Z X := by
  rw [Glue.β', assoc, ιW_fa, ← assoc, β_pD]

lemma β'_fb : Glue.β' (σ (Q b)) X (cyl b) ≫ fb Z X = Glue.β (σ (Q b)) X ≫ ιX Z X := by
  rw [Glue.β', assoc, ιW_fb, ← assoc, β_pD]

lemma c'_fa : Glue.c' (σ (Q b)) X (uturn b Z) ≫ fa Z X = cJ b ≫ kZ Z ≫ ιZ Z X := by
  rw [Glue.c', assoc, ιY_fa, Glue.jY, ← assoc, j_fold, assoc]

lemma c'_fb : Glue.c' (σ (Q b)) X (cyl b) ≫ fb Z X = cJ b ≫ kZ Z ≫ ιZ Z X := by
  rw [Glue.c', assoc, ιY_fb, Glue.jY, cyl_j]

@[reassoc (attr := simp)]
lemma star_fold_star_inl (m : ℤ) : J.star ((fold Z).f m) ≫
    J.star ((sumInl (PairSum.bD Z (Zn Z))).f m) = J.star (Z.pD.f m) := by
  rw [← J.star_comp, inl_fold_f]

@[reassoc (attr := simp)]
lemma star_fold_star_inr (m : ℤ) : J.star ((fold Z).f m) ≫
    J.star ((sumInr (PairSum.bD Z (Zn Z))).f m) = J.star (Z.pD.f m) := by
  rw [← J.star_comp, inr_fold_f]

lemma fold_δφ_fold (x y : ℤ) :
    J.star ((fold Z).f (N - x)) ≫ (uturn b Z).δφ.hom x y ≫ (fold Z).f y = 0 := by
  simp only [uturn, homotopyCongr_hom, PairSum.δφ_hom, Homotopy.compLeft_hom,
    Homotopy.compRight_hom, dualHom_f, comp_add, add_comp, assoc, inl_fold_f, inr_fold_f,
    star_fold_star_inl_assoc, star_fold_star_inr_assoc, Double.Xn_δφ_hom, neg_comp, comp_neg,
    Double.star_pD_δφ_pD]
  exact add_neg_cancel _

section Push

variable {U : ChainComplex V ℤ} (f : U ⟶ W' Z X)

end Push

@[reassoc (attr := simp)]
lemma ιW_f_fa_f (m : ℤ) : (Glue.ιW (σ (Q b)) X (uturn b Z)).f m ≫ (fa Z X).f m =
    (X.pD ≫ ιX Z X).f m := by rw [← comp_f, ιW_fa]

@[reassoc (attr := simp)]
lemma ιW_f_fb_f (m : ℤ) : (Glue.ιW (σ (Q b)) X (cyl b)).f m ≫ (fb Z X).f m =
    (X.pD ≫ ιX Z X).f m := by rw [← comp_f, ιW_fb]

@[reassoc (attr := simp)]
lemma star_fa_star_ιW (m : ℤ) : J.star ((fa Z X).f m) ≫ J.star ((Glue.ιW (σ (Q b)) X (uturn b Z)).f m) =
    J.star ((X.pD ≫ ιX Z X).f m) := by rw [← J.star_comp, ιW_f_fa_f]

@[reassoc (attr := simp)]
lemma star_fb_star_ιW (m : ℤ) : J.star ((fb Z X).f m) ≫ J.star ((Glue.ιW (σ (Q b)) X (cyl b)).f m) =
    J.star ((X.pD ≫ ιX Z X).f m) := by rw [← J.star_comp, ιW_f_fb_f]

@[reassoc (attr := simp)]
lemma ιY_f_fa_f (m : ℤ) : (Glue.ιY (σ (Q b)) X (uturn b Z)).f m ≫ (fa Z X).f m =
    (fold Z).f m ≫ (ιZ Z X).f m := by rw [← comp_f, ιY_fa, comp_f]

@[reassoc (attr := simp)]
lemma star_fa_star_ιY (m : ℤ) : J.star ((fa Z X).f m) ≫ J.star ((Glue.ιY (σ (Q b)) X (uturn b Z)).f m) =
    J.star ((ιZ Z X).f m) ≫ J.star ((fold Z).f m) := by rw [← J.star_comp, ιY_f_fa_f, J.star_comp]

@[reassoc (attr := simp)]
lemma K'_fa_f (x y : ℤ) :
    (Glue.K' (σ (Q b)) X (uturn b Z)).hom x y ≫ (fa Z X).f y = Kw Z X x y := K'_fa Z X x y

@[reassoc (attr := simp)]
lemma K'_fb_f (x y : ℤ) :
    (Glue.K' (σ (Q b)) X (cyl b)).hom x y ≫ (fb Z X).f y = Kw Z X x y := K'_fb Z X x y

@[reassoc (attr := simp)]
lemma star_fa_star_K' (x y : ℤ) : J.star ((fa Z X).f y) ≫
    J.star ((Glue.K' (σ (Q b)) X (uturn b Z)).hom x y) = J.star (Kw Z X x y) := by
  rw [← J.star_comp, K'_fa]

@[reassoc (attr := simp)]
lemma star_fb_star_K' (x y : ℤ) : J.star ((fb Z X).f y) ≫
    J.star ((Glue.K' (σ (Q b)) X (cyl b)).hom x y) = J.star (Kw Z X x y) := by
  rw [← J.star_comp, K'_fb]

@[reassoc (attr := simp)]
lemma β'_f_fa_f (m : ℤ) : (Glue.β' (σ (Q b)) X (uturn b Z)).f m ≫ (fa Z X).f m =
    (Glue.β (σ (Q b)) X ≫ ιX Z X).f m := by rw [← comp_f, β'_fa]

@[reassoc (attr := simp)]
lemma β'_f_fb_f (m : ℤ) : (Glue.β' (σ (Q b)) X (cyl b)).f m ≫ (fb Z X).f m =
    (Glue.β (σ (Q b)) X ≫ ιX Z X).f m := by rw [← comp_f, β'_fb]

@[reassoc (attr := simp)]
lemma star_fa_star_c' (m : ℤ) : J.star ((fa Z X).f m) ≫ J.star ((Glue.c' (σ (Q b)) X (uturn b Z)).f m) =
    J.star ((cJ b ≫ kZ Z ≫ ιZ Z X).f m) := by rw [← J.star_comp, ← comp_f, c'_fa]

@[reassoc (attr := simp)]
lemma star_fb_star_c' (m : ℤ) : J.star ((fb Z X).f m) ≫ J.star ((Glue.c' (σ (Q b)) X (cyl b)).f m) =
    J.star ((cJ b ≫ kZ Z ≫ ιZ Z X).f m) := by rw [← J.star_comp, ← comp_f, c'_fb]

/-- The pushforwards of `Hns` along `f_a` and `f_b` agree. -/
lemma sandHns_eq (x y : ℤ) :
    (dualHom J N (fa Z X)).f x ≫ (Glue.Hns (σ (Q b)) X (uturn b Z)).hom x y ≫ (fa Z X).f y =
      (dualHom J N (fb Z X)).f x ≫ (Glue.Hns (σ (Q b)) X (cyl b)).hom x y ≫ (fb Z X).f y := by
  have hY : J.star ((fold Z).f (N - x)) ≫ (uturn b Z).δφ.hom x y ≫ (fold Z).f y ≫
      (ιZ Z X).f y = 0 := by rw [← assoc, ← assoc, assoc _ _ ((fold Z).f y), fold_δφ_fold,
        zero_comp]
  rw [Glue.Hns_hom, Glue.Hns_hom]
  simp only [HW_hom, HY_hom, G_hom, dualHom_f, comp_add, add_comp, assoc, dualHomotopy_hom,
    Linear.comp_units_smul, Linear.units_smul_comp, neg_f_apply, J.star_neg, neg_comp, comp_neg,
    star_fa_star_ιW_assoc, star_fb_star_ιW_assoc, ιW_f_fa_f, ιW_f_fb_f, star_fa_star_ιY_assoc,
    ιY_f_fa_f, hY, cyl_δφ_hom, zero_comp, comp_zero, star_fa_star_K'_assoc,
    star_fb_star_K'_assoc, β'_f_fa_f, β'_f_fb_f, K'_fa_f, K'_fb_f, star_fa_star_c'_assoc,
    star_fb_star_c'_assoc]

lemma sandTHns_eq (x y : ℤ) :
    (dualHom J N (fa Z X)).f x ≫
        (transposeHomotopy J N (Glue.Hns (σ (Q b)) X (uturn b Z))).hom x y ≫ (fa Z X).f y =
      (dualHom J N (fb Z X)).f x ≫
        (transposeHomotopy J N (Glue.Hns (σ (Q b)) X (cyl b))).hom x y ≫ (fb Z X).f y := by
  have ha := congrFun (congrFun (transposeHomFamily_conjMap (J := J) (N := N) (fa Z X)
    (Glue.Hns (σ (Q b)) X (uturn b Z)).hom) x) y
  have hb := congrFun (congrFun (transposeHomFamily_conjMap (J := J) (N := N) (fb Z X)
    (Glue.Hns (σ (Q b)) X (cyl b)).hom) x) y
  have e : (fun i k ↦ (dualHom J N (fa Z X)).f i ≫ (Glue.Hns (σ (Q b)) X (uturn b Z)).hom i k ≫
      (fa Z X).f k) = fun i k ↦ (dualHom J N (fb Z X)).f i ≫
        (Glue.Hns (σ (Q b)) X (cyl b)).hom i k ≫ (fb Z X).f k := funext₂ (sandHns_eq Z X)
  rw [transposeHomotopy_hom, transposeHomotopy_hom, ← ha, ← hb, e]

variable [Linear ℚ V]

lemma sandδφZ_eq (x y : ℤ) :
    (dualHom J N (fa Z X)).f x ≫ (Glue.δφZ (σ (Q b)) X (uturn b Z)).hom x y ≫ (fa Z X).f y =
      (dualHom J N (fb Z X)).f x ≫ (Glue.δφZ (σ (Q b)) X (cyl b)).hom x y ≫ (fb Z X).f y := by
  rw [δφZ_hom, δφZ_hom, Linear.smul_comp, Linear.comp_smul, Linear.smul_comp, Linear.comp_smul,
    add_comp, comp_add, add_comp, comp_add, sandHns_eq, sandTHns_eq]

lemma sandTH_eq (x y : ℤ) :
    (dualHom J N (fa Z X)).f x ≫ (THns X (uturn b Z)).hom x y ≫ (fa Z X).f y =
      (dualHom J N (fb Z X)).f x ≫ (THns X (cyl b)).hom x y ≫ (fb Z X).f y := by
  simp only [THns, homotopyCongr_hom]
  exact sandTHns_eq Z X x y

lemma fa_union_fa : dualHom J (N + 1) (fa Z X) ≫ (Ua Z X).φ ≫ fa Z X =
    dualHom J (N + 1) (fb Z X) ≫ (Ub X).φ ≫ fb Z X := by
  ext r
  simp only [comp_f, dualHom_f, union_φ_f, relTop, assoc]
  rw [star_f_XIsoOfEq_assoc, star_f_XIsoOfEq_assoc, ← dualHom_f, ← dualHom_f, sandδφZ_eq]

lemma fa_phiT_fa : dualHom J (N + 1) (fa Z X) ≫ phiT X (uturn b Z) ≫ fa Z X =
    dualHom J (N + 1) (fb Z X) ≫ phiT X (cyl b) ≫ fb Z X := by
  ext r
  simp only [comp_f, dualHom_f, phiT_f, relTop, assoc]
  rw [star_f_XIsoOfEq_assoc, star_f_XIsoOfEq_assoc, ← dualHom_f, ← dualHom_f, sandTH_eq]

/-- The bicones of `U_a ⊕ U_b`. -/
abbrev bb (r : ℤ) : BinaryBicone ((Ua Z X).C.X r) ((Ub X).neg.C.X r) := BinaryBiproduct.bicone _ _

/-- **The boundary** `∂W' = U_a ⊕ -U_b`. -/
abbrev bd : SymPoincare J (N + 1) := (Ua Z X).sum (Ub X).neg (bb Z X)

/-- **The boundary map** `j = f_a ⊕ f_b : U_a ⊕ U_b ⟶ W'`. -/
def jj : (bd Z X).C ⟶ W' Z X := sumFst (bb Z X) ≫ fa Z X + sumSnd (bb Z X) ≫ fb Z X

@[reassoc (attr := simp)]
lemma inl_jj : sumInl (bb Z X) ≫ jj Z X = fa Z X := by simp [jj]

@[reassoc (attr := simp)]
lemma inr_jj : sumInr (bb Z X) ≫ jj Z X = fb Z X := by simp [jj]

lemma jj_kar : (bd Z X).p ≫ jj Z X ≫ pW Z X = jj Z X := by
  have ha := fa_kar Z X
  have hb := fb_kar Z X
  simp only [SymPoincare.sum, jj, comp_add, add_comp, assoc, sumInl_sumFst_assoc,
    sumInl_sumSnd_assoc, sumInr_sumFst_assoc, sumInr_sumSnd_assoc, zero_comp, comp_zero,
    add_zero, zero_add]
  rw [show (Ua Z X).p ≫ fa Z X ≫ pW Z X = fa Z X from ha,
    show (Ub X).neg.p ≫ fb Z X ≫ pW Z X = fb Z X from hb]

/-- **The union structures cancel**: `j φ_∂ j^* = 0`. -/
lemma jj_bd_jj : dualHom J (N + 1) (jj Z X) ≫ (bd Z X).φ ≫ jj Z X = 0 := by
  have h := fa_union_fa Z X
  simp only [SymPoincare.sum, SymPoincare.neg, comp_add, add_comp, assoc, inl_jj, inr_jj,
    neg_comp, comp_neg]
  rw [← assoc (dualHom J (N + 1) (jj Z X)), ← dualHom_comp, inl_jj,
    ← assoc (dualHom J (N + 1) (jj Z X)), ← dualHom_comp, inr_jj, ← sub_eq_add_neg]
  exact sub_eq_zero.mpr h

/-- The transposed boundary structure `φᵀ_a ⊕ -φᵀ_b`. -/
def phiD : dualComplex J (N + 1) (bd Z X).C ⟶ (bd Z X).C :=
  dualHom J (N + 1) (sumInl (bb Z X)) ≫ phiT X (uturn b Z) ≫ sumInl (bb Z X) -
    dualHom J (N + 1) (sumInr (bb Z X)) ≫ phiT X (cyl b) ≫ sumInr (bb Z X)

lemma jj_phiD_jj : dualHom J (N + 1) (jj Z X) ≫ phiD Z X ≫ jj Z X = 0 := by
  have h := fa_phiT_fa Z X
  simp only [phiD, sub_comp, comp_sub, assoc, inl_jj, inr_jj]
  rw [← assoc (dualHom J (N + 1) (jj Z X)), ← dualHom_comp, inl_jj,
    ← assoc (dualHom J (N + 1) (jj Z X)), ← dualHom_comp, inr_jj]
  exact sub_eq_zero.mpr h

end UTurn

end

end HSFormal.LTheory
