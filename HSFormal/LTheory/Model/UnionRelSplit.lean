import HSFormal.LTheory.Model.UnionRelTurn

/-!
# The U-turn: the kernel of the boundary map

The boundary map `j = f_a ⊕ f_b : U_a ⊕ U_b ⟶ W'` of `Model/UnionRelTurn.lean` is degreewise split
surjective (`UTurn.split`), with kernel

  `K = Cone(v : C_Q ⟶ D_X ⊕ (D_Z ⊕ C_B))`,  `v = (β, (j_Z ∘ pr₁, c))`,

included by `k(x, y, e, c) = ((x, y, (e, j_Z c - e)), (-x, -y, -c))`; the degreewise retraction is
`t(a, b) = (-x_b, -y_b, -e₂ - j_Z c_b, -c_b)` and the section `s(x, y, e) = ((x, y, (e, 0)), 0)`.
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

/-! ### The kernel `K` -/

/-- The bicones of `D_Z ⊕ C_B`. -/
abbrev bB (r : ℤ) : BinaryBicone (Z.D.X r) (B.C.X r) := BinaryBiproduct.bicone _ _

/-- `D_Z ⊕ C_B`. -/
abbrev SB : ChainComplex V ℤ := sumComplex (bB Z)

/-- The bicones of `D_X ⊕ (D_Z ⊕ C_B)`. -/
abbrev bK (r : ℤ) : BinaryBicone (X.D.X r) ((SB Z).X r) := BinaryBiproduct.bicone _ _

/-- `D_X ⊕ (D_Z ⊕ C_B)`. -/
abbrev SK : ChainComplex V ℤ := sumComplex (bK Z X)

variable (b) in
/-- The first projection `C_Q ⟶ C_B`. -/
def fstQ : (Q b).C ⟶ B.C := sumFst b

variable (b) in
/-- `v_B = (j_Z ∘ pr₁, c) : C_Q ⟶ D_Z ⊕ C_B`. -/
def vB : (Q b).C ⟶ SB Z := (fstQ b ≫ kZ Z) ≫ sumInl (bB Z) + cJ b ≫ sumInr (bB Z)

/-- `v = (β, v_B) : C_Q ⟶ D_X ⊕ (D_Z ⊕ C_B)`. -/
def v : (Q b).C ⟶ SK Z X := Glue.β (σ (Q b)) X ≫ sumInl (bK Z X) + vB b Z ≫ sumInr (bK Z X)

/-- **The kernel** `K = Cone(v)`. -/
abbrev K : ChainComplex V ℤ := cone (v Z X)

/-- The idempotent `p_Z ⊕ p_B` of `D_Z ⊕ C_B`. -/
def pSB : SB Z ⟶ SB Z :=
  sumFst (bB Z) ≫ Z.pD ≫ sumInl (bB Z) + sumSnd (bB Z) ≫ B.p ≫ sumInr (bB Z)

/-- The idempotent of `D_X ⊕ (D_Z ⊕ C_B)`. -/
def pSK : SK Z X ⟶ SK Z X :=
  sumFst (bK Z X) ≫ X.pD ≫ sumInl (bK Z X) + sumSnd (bK Z X) ≫ pSB Z ≫ sumInr (bK Z X)

lemma Qp_fst : (Q b).p ≫ fstQ b = fstQ b ≫ B.p := by simp [SymPoincare.sum, fstQ]

@[reassoc]
lemma vB_comm : (Q b).p ≫ vB b Z = vB b Z ≫ pSB Z := by
  simp (config := {proj := false}) only [vB, pSB, comp_add, add_comp, assoc, sumInl_sumFst_assoc, sumInl_sumSnd_assoc,
    sumInr_sumFst_assoc, sumInr_sumSnd_assoc, zero_comp, comp_zero, add_zero, zero_add,
    Qp_cJ_assoc, kZ_pD_assoc]
  rw [← assoc (Q b).p, Qp_fst, assoc, B_p_kZ_assoc]
  simp [cJ, add_comp]

lemma v_comm : (Q b).p ≫ v Z X = v Z X ≫ pSK Z X := by
  simp (config := {proj := false}) only [v, pSK, comp_add, add_comp, assoc, sumInl_sumFst_assoc, sumInl_sumSnd_assoc,
    sumInr_sumFst_assoc, sumInr_sumSnd_assoc, zero_comp, comp_zero, add_zero, zero_add,
    reassoc_of% (Qp_β X), reassoc_of% (β_pD X)]
  rw [vB_comm_assoc]

/-- The idempotent of `K`. -/
abbrev pK : K Z X ⟶ K Z X := coneMap (Q b).p (pSK Z X) (v_comm Z X)

@[reassoc (attr := simp)]
lemma biprod_inl_fold_f (n : ℤ) : (biprod.inl : Z.D.X n ⟶ _) ≫ (fold Z).f n = Z.pD.f n :=
  inl_fold_f Z n

@[reassoc (attr := simp)]
lemma biprod_inr_fold_f (n : ℤ) : (biprod.inr : (Zn Z).D.X n ⟶ _) ≫ (fold Z).f n = Z.pD.f n :=
  inr_fold_f Z n

/-! ### The inclusion `k : K ⟶ U_a ⊕ U_b` -/

/-- The second inclusion `D_Z ⟶ D_Z ⊕ D_Z`, typed on `D_Z`. -/
def inrD : Z.D ⟶ PairSum.D Z (Zn Z) := sumInr (PairSum.bD Z (Zn Z))

@[reassoc (attr := simp)]
lemma inrD_fold : inrD Z ≫ fold Z = Z.pD := inr_fold Z

/-- `m_B : (e, c) ↦ (e, j_Z c - e) : D_Z ⊕ C_B ⟶ D_Z ⊕ D_Z`. -/
def mB : SB Z ⟶ PairSum.D Z (Zn Z) :=
  sumFst (bB Z) ≫ Z.pD ≫ (sumInl (PairSum.bD Z (Zn Z)) - inrD Z) + sumSnd (bB Z) ≫ kZ Z ≫ inrD Z

/-- `(y, e, c) ↦ (y, (e, j_Z c - e))`. -/
def nka : SK Z X ⟶ Glue.S X (uturn b Z) :=
  sumFst (bK Z X) ≫ X.pD ≫ sumInl (Glue.bS X (uturn b Z)) +
    sumSnd (bK Z X) ≫ mB Z ≫ sumInr (Glue.bS X (uturn b Z))

/-- `(y, e, c) ↦ -(y, c)`. -/
def nkb : SK Z X ⟶ Glue.S X (cyl b) :=
  -(sumFst (bK Z X) ≫ X.pD ≫ sumInl (Glue.bS X (cyl b)) +
    sumSnd (bK Z X) ≫ sumSnd (bB Z) ≫ B.p ≫ sumInr (Glue.bS X (cyl b)))

lemma Qp_uj : (Q b).p ≫ (uturn b Z).j = (uturn b Z).j := (uturn b Z).p_comp_j

@[reassoc]
lemma cJ_Bp : cJ b ≫ B.p = cJ b := by simp [cJ, add_comp]

lemma vB_mB : vB b Z ≫ mB Z = (uturn b Z).j := by
  have h : B.p ≫ Z.j = Z.j := Z.p_comp_j
  simp [vB, mB, uturn, PairSum.j, inrD, cJ, fstQ, comp_add, add_comp, comp_sub, kZ,
    reassoc_of% h]
  abel

lemma hka : (Q b).p ≫ Glue.u (σ (Q b)) X (uturn b Z) = v Z X ≫ nka Z X := by
  simp (config := {proj := false}) only [Glue.u, v, nka, comp_add, add_comp, assoc, sumInl_sumFst_assoc, sumInl_sumSnd_assoc,
    sumInr_sumFst_assoc, sumInr_sumSnd_assoc, zero_comp, comp_zero, add_zero, zero_add,
    reassoc_of% (Qp_β X), reassoc_of% (β_pD X), Glue.jY]
  rw [← assoc (Q b).p, Qp_uj, ← assoc (vB b Z), vB_mB]

lemma hkb : (-(Q b).p) ≫ Glue.u (σ (Q b)) X (cyl b) = v Z X ≫ nkb Z X := by
  simp (config := {proj := false}) only [Glue.u, v, nkb, comp_add, add_comp, assoc, sumInl_sumFst_assoc, sumInl_sumSnd_assoc,
    sumInr_sumFst_assoc, sumInr_sumSnd_assoc, zero_comp, comp_zero, add_zero, zero_add,
    reassoc_of% (β_pD X), Glue.jY, neg_comp, comp_neg, cyl_j]
  rw [← assoc (Q b).p, Qp_β, ← assoc (Q b).p, Qp_cJ]
  simp [vB, add_comp, cJ_Bp_assoc]
  abel

/-- `k_a : K ⟶ U_a`. -/
def ka : K Z X ⟶ Glue.U (σ (Q b)) X (uturn b Z) := coneMap (Q b).p (nka Z X) (hka Z X)

/-- `k_b : K ⟶ U_b`. -/
def kb : K Z X ⟶ Glue.U (σ (Q b)) X (cyl b) := coneMap (-(Q b).p) (nkb Z X) (hkb Z X)

/-- **The kernel inclusion** `k = (k_a, k_b) : K ⟶ U_a ⊕ U_b`. -/
def kK : K Z X ⟶ (bd Z X).C := ka Z X ≫ sumInl (bb Z X) + kb Z X ≫ sumInr (bb Z X)

/-! ### The degreewise retraction `t` and section `s` -/

/-- `u_a`, the gluing map of `U_a`. -/
abbrev ua := Glue.u (σ (Q b)) X (uturn b Z)

/-- `u_b`, the gluing map of `U_b`. -/
abbrev ub := Glue.u (σ (Q b)) X (cyl b)

/-- `t_a : U_a ⟶ K`, `(x, y, (e₁, e₂)) ↦ (0, 0, -e₂, 0)`. -/
def ta (n : ℤ) : (Glue.U (σ (Q b)) X (uturn b Z)).X n ⟶ (K Z X).X n :=
  -(sndX (ua Z X) n ≫ (sumSnd (Glue.bS X (uturn b Z))).f n ≫ (sndD Z).f n ≫ Z.pD.f n ≫
    (sumInl (bB Z)).f n ≫ (sumInr (bK Z X)).f n ≫ inrX (v Z X) n)

/-- `t_b : U_b ⟶ K`, `(x, y, c) ↦ -(x, y, j_Z c, c)`. -/
def tb (n : ℤ) : (Glue.U (σ (Q b)) X (cyl b)).X n ⟶ (K Z X).X n :=
  -(fstX (ub X) n (n - 1) (down_rel_pred n) ≫ (Q b).p.f (n - 1) ≫
      inlX (v Z X) (n - 1) n (down_rel_pred n)) -
    sndX (ub X) n ≫ (sumFst (Glue.bS X (cyl b))).f n ≫ X.pD.f n ≫ (sumInl (bK Z X)).f n ≫
      inrX (v Z X) n -
    sndX (ub X) n ≫ (sumSnd (Glue.bS X (cyl b))).f n ≫ B.p.f n ≫
      ((kZ Z).f n ≫ (sumInl (bB Z)).f n + (sumInr (bB Z)).f n) ≫ (sumInr (bK Z X)).f n ≫
        inrX (v Z X) n

/-- **The degreewise retraction** `t : U_a ⊕ U_b ⟶ K`. -/
def tS (n : ℤ) : (bd Z X).C.X n ⟶ (K Z X).X n :=
  (sumFst (bb Z X)).f n ≫ ta Z X n + (sumSnd (bb Z X)).f n ≫ tb Z X n

/-- `s_a : W' ⟶ U_a`, `(x, y, e) ↦ (x, y, (e, 0))`. -/
def sW (n : ℤ) : (W' Z X).X n ⟶ (Glue.U (σ (Q b)) X (uturn b Z)).X n :=
  fstX (w Z X) n (n - 1) (down_rel_pred n) ≫ (Q b).p.f (n - 1) ≫
      inlX (ua Z X) (n - 1) n (down_rel_pred n) +
    sndX (w Z X) n ≫ (sumFst (bW Z X)).f n ≫ X.pD.f n ≫
      (sumInl (Glue.bS X (uturn b Z))).f n ≫ inrX (ua Z X) n +
    sndX (w Z X) n ≫ (sumSnd (bW Z X)).f n ≫ Z.pD.f n ≫ (sumInl (PairSum.bD Z (Zn Z))).f n ≫
      (sumInr (Glue.bS X (uturn b Z))).f n ≫ inrX (ua Z X) n

/-- **The degreewise section** `s : W' ⟶ U_a ⊕ U_b`. -/
def sS (n : ℤ) : (W' Z X).X n ⟶ (bd Z X).C.X n := sW Z X n ≫ (sumInl (bb Z X)).f n

lemma sq (n : ℤ) : sS Z X n ≫ (jj Z X).f n = (pW Z X).f n := by
  have e : (sumInl (bb Z X)).f n ≫ (jj Z X).f n = (fa Z X).f n := by rw [← comp_f, inl_jj]
  rw [sS, assoc, e]
  apply ext_from_X (w Z X) (n - 1) n (down_rel_pred n)
  · simp [sW, fa]
  · simp only [sW, fa, comp_add, inrX_sndX_assoc, inrX_fstX_assoc, zero_comp, zero_add, assoc,
      inrX_coneMap_f, inrX_coneMap_f_assoc]
    apply biprod.hom_ext' <;> simp [na, pSW]

@[reassoc (attr := simp)]
lemma Qp_f_idem (n : ℤ) : (Q b).p.f n ≫ (Q b).p.f n = (Q b).p.f n := by
  rw [← comp_f, (Q b).p_idem]

lemma it (n : ℤ) : (kK Z X).f n ≫ tS Z X n = (pK Z X).f n := by
  simp only [kK, tS, add_f_apply, comp_f, add_comp, comp_add, assoc, sumInl_f_sumFst_f_assoc,
    sumInl_f_sumSnd_f_assoc, sumInr_f_sumFst_f_assoc, sumInr_f_sumSnd_f_assoc, zero_comp,
    comp_zero, add_zero, zero_add]
  apply ext_from_X (v Z X) (n - 1) n (down_rel_pred n)
  · simp [ka, kb, ta, tb]
    abel
  · simp only [ka, kb, ta, tb, comp_add, inrX_coneMap_f_assoc, assoc, comp_neg, comp_sub,
      inrX_coneMap_f]
    apply biprod.hom_ext'
    · simp [nka, nkb, pSK]
    · apply biprod.hom_ext' <;> simp [nka, nkb, pSK, pSB, mB, inrD, sndD]

@[reassoc (attr := simp)]
lemma inl_bd_p_f (n : ℤ) : (sumInl (bb Z X)).f n ≫ (bd Z X).p.f n =
    (Glue.pU (σ (Q b)) X (uturn b Z)).f n ≫ (sumInl (bb Z X)).f n := by
  simp [SymPoincare.sum, add_comp, comp_add, union_p]

@[reassoc (attr := simp)]
lemma inr_bd_p_f (n : ℤ) : (sumInr (bb Z X)).f n ≫ (bd Z X).p.f n =
    (Glue.pU (σ (Q b)) X (cyl b)).f n ≫ (sumInr (bb Z X)).f n := by
  simp [SymPoincare.sum, SymPoincare.neg, add_comp, comp_add, union_p]

@[reassoc (attr := simp)]
lemma uturn_pD_sndD_f (n : ℤ) : (uturn b Z).pD.f n ≫ (sndD Z).f n = (sndD Z).f n ≫ Z.pD.f n := by
  simp [uturn, sndD, PairSum.pD, add_comp]

@[reassoc (attr := simp)]
lemma inlD_uturn_pD_f (n : ℤ) : (sumInl (PairSum.bD Z (Zn Z))).f n ≫ (uturn b Z).pD.f n =
    Z.pD.f n ≫ (sumInl (PairSum.bD Z (Zn Z))).f n := by
  simp [uturn, PairSum.pD, comp_add]

@[reassoc (attr := simp)]
lemma biprod_inl_uturn_pD_f (n : ℤ) : (biprod.inl : Z.D.X n ⟶ _) ≫ (uturn b Z).pD.f n =
    Z.pD.f n ≫ biprod.inl :=
  inlD_uturn_pD_f Z n

@[reassoc (attr := simp)]
lemma biprod_inr_uturn_pD_f (n : ℤ) : (biprod.inr : (Zn Z).D.X n ⟶ _) ≫ (uturn b Z).pD.f n =
    Z.pD.f n ≫ biprod.inr := by
  simp [uturn, PairSum.pD, comp_add]
  rfl

lemma ta_kar (n : ℤ) : (Glue.pU (σ (Q b)) X (uturn b Z)).f n ≫ ta Z X n ≫ (pK Z X).f n =
    ta Z X n := by
  simp [ta, Glue.pS, pSK, pSB, add_comp, comp_add]

lemma tb_kar (n : ℤ) : (Glue.pU (σ (Q b)) X (cyl b)).f n ≫ tb Z X n ≫ (pK Z X).f n =
    tb Z X n := by
  simp [tb, Glue.pS, pSK, pSB, cyl_pD, add_comp, comp_add]

lemma t_kar (n : ℤ) : (bd Z X).p.f n ≫ tS Z X n ≫ (pK Z X).f n = tS Z X n := by
  refine biprod.hom_ext' _ _ ?_ ?_
  · change (sumInl (bb Z X)).f n ≫ _ = (sumInl (bb Z X)).f n ≫ _
    simp only [tS, inl_bd_p_f_assoc, comp_add, sumInl_f_sumFst_f_assoc, sumInl_f_sumSnd_f_assoc,
      zero_comp, add_zero, add_comp, assoc, comp_zero]
    exact ta_kar Z X n
  · change (sumInr (bb Z X)).f n ≫ _ = (sumInr (bb Z X)).f n ≫ _
    simp only [tS, inr_bd_p_f_assoc, comp_add, sumInr_f_sumFst_f_assoc, sumInr_f_sumSnd_f_assoc,
      zero_comp, zero_add, add_comp, assoc, comp_zero]
    exact tb_kar Z X n

lemma sW_kar (n : ℤ) : (pW Z X).f n ≫ sW Z X n ≫ (Glue.pU (σ (Q b)) X (uturn b Z)).f n =
    sW Z X n := by
  simp [sW, pSW, Glue.pS, add_comp, comp_add]

lemma s_kar (n : ℤ) : (pW Z X).f n ≫ sS Z X n ≫ (bd Z X).p.f n = sS Z X n := by
  simp (config := {proj := false}) only [sS, assoc, inl_bd_p_f]
  rw [← assoc, ← assoc, assoc _ (sW Z X n), sW_kar]

lemma totA (n : ℤ) : ta Z X n ≫ (ka Z X).f n + (fa Z X).f n ≫ sW Z X n =
    (Glue.pU (σ (Q b)) X (uturn b Z)).f n := by
  apply ext_from_X (ua Z X) (n - 1) n (down_rel_pred n)
  · simp [ta, ka, fa, sW]
  · simp only [ta, ka, fa, sW, comp_add, inrX_coneMap_f_assoc, assoc, comp_neg, add_comp,
      inrX_coneMap_f, neg_comp, inrX_sndX_assoc, inrX_fstX_assoc, zero_comp, zero_add]
    apply biprod.hom_ext'
    · simp [nka, na, Glue.pS]
    · apply biprod.hom_ext' <;> simp [nka, na, Glue.pS, mB, inrD, sndD, fold] <;> rfl

lemma totB (n : ℤ) : ta Z X n ≫ (kb Z X).f n = 0 := by
  simp [ta, kb, nkb]

lemma totC (n : ℤ) : tb Z X n ≫ (ka Z X).f n + (fb Z X).f n ≫ sW Z X n = 0 := by
  apply ext_from_X (ub X) (n - 1) n (down_rel_pred n)
  · simp [tb, ka, fb, sW]
  · simp only [tb, ka, fb, sW, comp_add, inrX_coneMap_f_assoc, assoc, comp_neg, add_comp,
      inrX_coneMap_f, neg_comp, inrX_sndX_assoc, inrX_fstX_assoc, zero_comp, zero_add, comp_sub,
      sub_comp]
    apply biprod.hom_ext' <;> simp [nka, nb, Glue.pS, mB, inrD, sndD]

lemma totD (n : ℤ) : tb Z X n ≫ (kb Z X).f n = (Glue.pU (σ (Q b)) X (cyl b)).f n := by
  apply ext_from_X (ub X) (n - 1) n (down_rel_pred n)
  · simp [tb, kb]
    abel
  · simp only [tb, kb, comp_add, inrX_coneMap_f_assoc, assoc, comp_neg, add_comp,
      inrX_coneMap_f, neg_comp, inrX_sndX_assoc, inrX_fstX_assoc, zero_comp, zero_add, comp_sub,
      sub_comp]
    apply biprod.hom_ext' <;> simp [nkb, Glue.pS, cyl_pD]

@[reassoc (attr := simp)]
lemma inl_jj_f (n : ℤ) : (sumInl (bb Z X)).f n ≫ (jj Z X).f n = (fa Z X).f n := by
  rw [← comp_f, inl_jj]

@[reassoc (attr := simp)]
lemma inr_jj_f (n : ℤ) : (sumInr (bb Z X)).f n ≫ (jj Z X).f n = (fb Z X).f n := by
  rw [← comp_f, inr_jj]

lemma total (n : ℤ) : tS Z X n ≫ (kK Z X).f n + (jj Z X).f n ≫ sS Z X n = (bd Z X).p.f n := by
  refine biprod.hom_ext' _ _ ?_ ?_
  · change (sumInl (bb Z X)).f n ≫ _ = (sumInl (bb Z X)).f n ≫ _
    have e : (sumInl (bb Z X)).f n ≫ (tS Z X n ≫ (kK Z X).f n + (jj Z X).f n ≫ sS Z X n) =
        (ta Z X n ≫ (ka Z X).f n + (fa Z X).f n ≫ sW Z X n) ≫ (sumInl (bb Z X)).f n +
          (ta Z X n ≫ (kb Z X).f n) ≫ (sumInr (bb Z X)).f n := by
      simp only [tS, sS, kK, comp_add, add_comp, assoc, sumInl_f_sumFst_f_assoc,
        sumInl_f_sumSnd_f_assoc, zero_comp, add_zero, add_f_apply, comp_f, inl_jj_f_assoc]
      abel
    rw [e, totA, totB, zero_comp, add_zero, inl_bd_p_f]
  · change (sumInr (bb Z X)).f n ≫ _ = (sumInr (bb Z X)).f n ≫ _
    have e : (sumInr (bb Z X)).f n ≫ (tS Z X n ≫ (kK Z X).f n + (jj Z X).f n ≫ sS Z X n) =
        (tb Z X n ≫ (ka Z X).f n + (fb Z X).f n ≫ sW Z X n) ≫ (sumInl (bb Z X)).f n +
          (tb Z X n ≫ (kb Z X).f n) ≫ (sumInr (bb Z X)).f n := by
      simp only [tS, sS, kK, comp_add, add_comp, assoc, sumInr_f_sumFst_f_assoc,
        sumInr_f_sumSnd_f_assoc, zero_comp, zero_add, add_f_apply, comp_f, inr_jj_f_assoc]
      abel
    rw [e, totC, totD, zero_comp, zero_add, inr_bd_p_f]

/-- **The U-turn kernel sequence** `0 → K → U_a ⊕ U_b → W' → 0`, Kar degreewise split. -/
def split : KarSplit (pK Z X) (bd Z X).p (pW Z X) (kK Z X) (jj Z X) where
  t := tS Z X
  s := sS Z X
  t_kar := t_kar Z X
  s_kar := s_kar Z X
  it := it Z X
  sq := sq Z X
  total := total Z X

end UTurn

end

end HSFormal.LTheory
