import HSFormal.LTheory.Model.UnionRelSplit

/-!
# The U-turn: the two rows of the `λ`-ladder

For the U-turn null-cobordism `W' = Cone(w)` of `Model/UnionRelTurn.lean` with kernel
`K = Cone(v)` (`Model/UnionRelSplit.lean`):

* `UTurn.splitK`: the Kar degreewise split sequence `0 → D_X → K → B' → 0`, `B' = Cone(v_B)`;
* `UTurn.splitW`: the Kar degreewise split sequence `0 → D_Z → W' → Cone(j_X) → 0`;
* `UTurn.isKarEquiv_c`: the comparison `c : Cone(j_Z) ⟶ B'`, `c = ((1, -1), (1, 0))`, is a Kar
  homotopy equivalence (inverse `c' = (-pr₂, pr₁ - j_Z pr₂)`).
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

section StarBiprod

variable {A A' : V}

@[reassoc (attr := simp)]
lemma star_biprod_fst_inl : J.star (biprod.fst : A ⊞ A' ⟶ A) ≫ J.star biprod.inl = 𝟙 _ := by
  rw [← J.star_comp, biprod.inl_fst, J.star_id]

@[reassoc (attr := simp)]
lemma star_biprod_fst_inr : J.star (biprod.fst : A ⊞ A' ⟶ A) ≫ J.star biprod.inr = 0 := by
  rw [← J.star_comp, biprod.inr_fst, J.star_zero]

@[reassoc (attr := simp)]
lemma star_biprod_snd_inl : J.star (biprod.snd : A ⊞ A' ⟶ A') ≫ J.star biprod.inl = 0 := by
  rw [← J.star_comp, biprod.inl_snd, J.star_zero]

@[reassoc (attr := simp)]
lemma star_biprod_snd_inr : J.star (biprod.snd : A ⊞ A' ⟶ A') ≫ J.star biprod.inr = 𝟙 _ := by
  rw [← J.star_comp, biprod.inr_snd, J.star_id]

@[reassoc]
lemma star_comp_star {A₁ A₂ A₃ : V} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) :
    J.star g ≫ J.star f = J.star (f ≫ g) := (J.star_comp f g).symm

/-- Maps out of a biproduct are determined on the dual summands `fst^*`, `snd^*`. -/
lemma biprod_ext_star {T : V} {f g : A ⊞ A' ⟶ T}
    (h₁ : J.star biprod.fst ≫ f = J.star biprod.fst ≫ g)
    (h₂ : J.star biprod.snd ≫ f = J.star biprod.snd ≫ g) : f = g := by
  have e (x : A ⊞ A' ⟶ T) : x = J.star biprod.inl ≫ J.star biprod.fst ≫ x +
      J.star biprod.inr ≫ J.star biprod.snd ≫ x := by
    rw [← assoc, ← assoc, ← J.star_comp, ← J.star_comp, ← add_comp, ← J.star_add,
      biprod.total, J.star_id, id_comp]
  rw [e f, e g, h₁, h₂]

end StarBiprod

namespace UTurn

open Union

variable {B : SymPoincare J N} {b : ∀ r, BinaryBicone (B.C.X r) (B.C.X r)} (Z : PairOn B.neg)
  (X : PairOn (Q b))

/-! ### `0 → D_X → K → B' → 0` -/

variable (b) in
/-- `B' = Cone(v_B)`. -/
abbrev Bc : ChainComplex V ℤ := cone (vB b Z)

variable (b) in
/-- The idempotent of `B'`. -/
abbrev pBc : Bc b Z ⟶ Bc b Z := coneMap (Q b).p (pSB Z) (vB_comm Z)

/-- `D_X ⟶ K`. -/
def iK : X.D ⟶ K Z X := X.pD ≫ sumInl (bK Z X) ≫ inr (v Z X)

lemma v_sumSnd : v Z X ≫ sumSnd (bK Z X) = vB b Z := by simp [v, add_comp]

lemma qK_comm : (Q b).p ≫ vB b Z = v Z X ≫ sumSnd (bK Z X) ≫ pSB Z := by
  rw [← assoc, v_sumSnd, vB_comm]

/-- `K ⟶ B'`. -/
def qK : K Z X ⟶ Bc b Z := coneMap (Q b).p (sumSnd (bK Z X) ≫ pSB Z) (qK_comm Z X)

/-- The retraction `K ⟶ D_X`. -/
def tK (n : ℤ) : (K Z X).X n ⟶ X.D.X n :=
  sndX (v Z X) n ≫ (sumFst (bK Z X)).f n ≫ X.pD.f n

/-- The section `B' ⟶ K`. -/
def sK (n : ℤ) : (Bc b Z).X n ⟶ (K Z X).X n :=
  fstX (vB b Z) n (n - 1) (down_rel_pred n) ≫ (Q b).p.f (n - 1) ≫
      inlX (v Z X) (n - 1) n (down_rel_pred n) +
    sndX (vB b Z) n ≫ (pSB Z).f n ≫ (sumInr (bK Z X)).f n ≫ inrX (v Z X) n

@[reassoc (attr := simp)]
lemma pSB_idem_f (n : ℤ) : (pSB Z).f n ≫ (pSB Z).f n = (pSB Z).f n := by
  apply biprod.hom_ext' <;> simp [pSB]

/-- **The kernel sequence** `0 → D_X → K → B' → 0`. -/
def splitK : KarSplit X.pD (pK Z X) (pBc b Z) (iK Z X) (qK Z X) where
  t := tK Z X
  s := sK Z X
  t_kar n := by simp [tK, pSK]
  s_kar n := by
    apply ext_from_X (vB b Z) (n - 1) n (down_rel_pred n)
    · simp [sK]
    · simp [sK, pSK]
  it n := by simp [iK, tK]
  sq n := by
    apply ext_from_X (vB b Z) (n - 1) n (down_rel_pred n)
    · simp [sK, qK]
    · simp [sK, qK]
  total n := by
    apply ext_from_X (v Z X) (n - 1) n (down_rel_pred n)
    · simp [tK, iK, qK, sK]
    · simp only [tK, iK, qK, sK, comp_f, comp_add, add_comp, assoc, inrX_sndX_assoc,
        inrX_coneMap_f_assoc, inrX_coneMap_f, inrX_fstX_assoc, zero_comp, zero_add]
      apply biprod.hom_ext' <;> simp [pSK]

/-! ### `0 → D_Z → W' → Cone(j_X) → 0` -/

/-- The idempotent of `Cone(j_X)`. -/
abbrev pcX : cone X.j ⟶ cone X.j :=
  coneMap (Q b).p X.pD (comm_of_kar (Q b).p_idem X.pD_idem X.j_kar)

/-- `D_Z ⟶ W'`. -/
def ιZk : Z.D ⟶ W' Z X := Z.pD ≫ ιZ Z X

lemma πW_comm : (Q b).p ≫ X.j = w Z X ≫ sumFst (bW Z X) ≫ X.pD := by
  have h : (Q b).p ≫ X.j = X.j := X.p_comp_j
  simp [w, add_comp, β_eq, h, X.j_comp_pD]

/-- `W' ⟶ Cone(j_X)`. -/
def πW : W' Z X ⟶ cone X.j := coneMap (Q b).p (sumFst (bW Z X) ≫ X.pD) (πW_comm Z X)

/-- The retraction `W' ⟶ D_Z`. -/
def tW (n : ℤ) : (W' Z X).X n ⟶ Z.D.X n := sndX (w Z X) n ≫ (sumSnd (bW Z X)).f n ≫ Z.pD.f n

/-- The section `Cone(j_X) ⟶ W'`. -/
def sWc (n : ℤ) : (cone X.j).X n ⟶ (W' Z X).X n :=
  fstX X.j n (n - 1) (down_rel_pred n) ≫ (Q b).p.f (n - 1) ≫
      inlX (w Z X) (n - 1) n (down_rel_pred n) +
    sndX X.j n ≫ X.pD.f n ≫ (sumInl (bW Z X)).f n ≫ inrX (w Z X) n

/-- **The `D_Z`-sequence** `0 → D_Z → W' → Cone(j_X) → 0`. -/
def splitW : KarSplit Z.pD (pW Z X) (pcX X) (ιZk Z X) (πW Z X) where
  t := tW Z X
  s := sWc Z X
  t_kar n := by simp [tW, pSW]
  s_kar n := by
    apply ext_from_X X.j (n - 1) n (down_rel_pred n)
    · simp [sWc]
    · simp [sWc, pSW]
  it n := by simp [ιZk, tW]
  sq n := by
    apply ext_from_X X.j (n - 1) n (down_rel_pred n)
    · simp [sWc, πW]
    · simp [sWc, πW]
  total n := by
    apply ext_from_X (w Z X) (n - 1) n (down_rel_pred n)
    · simp [tW, ιZk, πW, sWc]
    · simp only [tW, ιZk, πW, sWc, comp_f, comp_add, add_comp, assoc, inrX_sndX_assoc,
        inrX_coneMap_f_assoc, inrX_coneMap_f, inrX_fstX_assoc, zero_comp, zero_add]
      apply biprod.hom_ext' <;> simp [pSW]

/-! ### The comparison `c : Cone(j_Z) ⟶ B'` -/

variable (b) in
/-- `c₀ = (1, -1) : C_B ⟶ C_Q`. -/
def c₀ : B.C ⟶ (Q b).C := (sumInl b - sumInr b) ≫ (Q b).p

/-- `c₁ = (1, 0) : D_Z ⟶ D_Z ⊕ C_B`. -/
def c₁ : Z.D ⟶ SB Z := Z.pD ≫ sumInl (bB Z)

lemma c_comm : c₀ b ≫ vB b Z = Z.j ≫ c₁ Z := by
  have h : B.p ≫ Z.j = Z.j := Z.p_comp_j
  rw [c₀, assoc, vB_comm, ← assoc]
  simp [vB, fstQ, cJ, kZ, pSB, c₁, add_comp, comp_add, sub_comp, comp_sub, Z.j_comp_pD,
    reassoc_of% h]

/-- **The comparison** `c : Cone(j_Z) ⟶ B'`. -/
def c : cone Z.j ⟶ Bc b Z := coneMap (c₀ b) (c₁ Z) (c_comm Z)

variable (b) in
/-- `c'₀ = -pr₂ : C_Q ⟶ C_B`. -/
def c'₀ : (Q b).C ⟶ B.C := -(sumSnd b ≫ B.p)

/-- `c'₁ = pr₁ - j_Z pr₂ : D_Z ⊕ C_B ⟶ D_Z`. -/
def c'₁ : SB Z ⟶ Z.D := sumFst (bB Z) ≫ Z.pD - sumSnd (bB Z) ≫ kZ Z

lemma c'_comm : c'₀ b ≫ Z.j = vB b Z ≫ c'₁ Z := by
  have h : B.p ≫ Z.j = Z.j := Z.p_comp_j
  simp [vB, fstQ, cJ, kZ, c'₀, c'₁, add_comp, comp_add, sub_comp, comp_sub, Z.j_comp_pD,
    reassoc_of% h, h]

/-- The inverse comparison `c' : B' ⟶ Cone(j_Z)`. -/
def c' : Bc b Z ⟶ cone Z.j := coneMap (c'₀ b) (c'₁ Z) (c'_comm Z)

/-- The idempotent of `Cone(j_Z)`. -/
abbrev pcZ : cone Z.j ⟶ cone Z.j :=
  coneMap B.neg.p Z.pD (comm_of_kar B.neg.p_idem Z.pD_idem Z.j_kar)

lemma c_c' : c Z (b := b) ≫ c' Z = pcZ Z := by
  rw [c, c', coneMap_comp]
  apply coneMap_ext'
  · simp [c₀, c'₀, SymPoincare.sum, SymPoincare.neg, sub_comp, add_comp, comp_add]
  · simp [c₁, c'₁, comp_sub]

lemma c'_kar : pBc b Z ≫ c' Z ≫ pcZ Z = c' Z := by
  rw [c', coneMap_comp, coneMap_comp]
  apply coneMap_ext'
  · simp [c'₀, SymPoincare.sum, SymPoincare.neg, add_comp, comp_add]
  · ext n : 1
    apply biprod.hom_ext' <;> simp [c'₁, pSB, comp_sub, sub_comp]

@[reassoc (attr := simp)]
lemma vB_f_fst (m : ℤ) : (vB b Z).f m ≫ (biprod.fst : (SB Z).X m ⟶ _) =
    (sumFst b).f m ≫ (kZ Z).f m := by
  simp [vB, fstQ, add_comp]

@[reassoc (attr := simp)]
lemma vB_f_snd (m : ℤ) : (vB b Z).f m ≫ (biprod.snd : (SB Z).X m ⟶ _) =
    (sumFst b).f m ≫ B.p.f m + (sumSnd b).f m ≫ B.p.f m := by
  simp [vB, cJ, add_comp]

@[reassoc (attr := simp)]
lemma inl_vB_f (m : ℤ) : (b m).inl ≫ (vB b Z).f m =
    (kZ Z).f m ≫ (biprod.inl : _ ⟶ (SB Z).X m) + B.p.f m ≫ biprod.inr := by
  simp [vB, fstQ, cJ, add_comp, comp_add]

variable (b) in
/-- The null-homotopy `(x, e, c) ↦ ((c, 0), 0)` of `p - c c'`. -/
def hB (a a' : ℤ) (h : (ComplexShape.down ℤ).Rel a' a) : (Bc b Z).X a ⟶ (Bc b Z).X a' :=
  sndX (vB b Z) a ≫ (sumSnd (bB Z)).f a ≫ B.p.f a ≫ (sumInl b).f a ≫ inlX (vB b Z) a a' h

lemma c'_c_add (n : ℤ) : (c' Z ≫ c Z).f n + (Homotopy.nullHomotopicMap' (hB b Z)).f n =
    (pBc b Z).f n := by
  rw [Homotopy.nullHomotopicMap'_f (down_rel_succ n) (down_rel_pred n)]
  apply ext_from_X (vB b Z) (n - 1) n (down_rel_pred n)
  · simp [c, c', hB, homotopyCofiber_d,
      inlX_d_assoc (vB b Z) n (n - 1) (n - 1 - 1) (down_rel_pred n) (down_rel_pred (n - 1)),
      c₀, c'₀, SymPoincare.sum, add_comp, comp_add, sub_comp, comp_sub]
    abel
  · simp [c, c', hB, homotopyCofiber_d,
      inlX_d (vB b Z) (n + 1) n (n - 1) (down_rel_succ n) (down_rel_pred n),
      c₁, c'₁, pSB, add_comp, comp_add, sub_comp, comp_sub]
    abel

/-- `c' c ≃ p_{B'}`. -/
def c'cHomotopy : Homotopy (c' Z ≫ c Z) (pBc b Z) :=
  (homotopyCongr ((Homotopy.refl (c' Z ≫ c Z)).add (Homotopy.nullHomotopy' (hB b Z)))
    (by ext n; exact c'_c_add Z n) (add_zero _)).symm

/-- **`c : Cone(j_Z) ⟶ B'` is a Kar equivalence.** -/
lemma isKarEquiv_c : IsKarEquiv (pcZ Z) (pBc b Z) (c Z) :=
  ⟨c' Z, c'_kar Z, ⟨c'cHomotopy Z⟩, ⟨Homotopy.ofEq (c_c' Z)⟩⟩

/-! ### The middle map `λ = t^* φᵀ_∂ j : K^{N+1-*} ⟶ W'` -/

lemma pSK_idem : pSK Z X ≫ pSK Z X = pSK Z X := by
  ext n : 1
  apply biprod.hom_ext'
  · simp [pSK]
  · apply biprod.hom_ext' <;> simp [pSK, pSB]

lemma pK_idem : pK Z X ≫ pK Z X = pK Z X := coneMap_idem _ (Q b).p_idem (pSK_idem Z X)

/-- **The middle map** `λ = t^* φᵀ_∂ j : K^{N+1-*} ⟶ W'`. -/
def lamT : dualComplex J (N + 1) (K Z X) ⟶ W' Z X :=
  (split Z X).lam (pK_idem Z X) (bd Z X).p_idem (phiD Z X) (jj_phiD_jj Z X)

lemma lamT_f (r : ℤ) : (lamT Z X).f r =
    J.star (tS Z X (N + 1 - r)) ≫ (phiD Z X).f r ≫ (jj Z X).f r := rfl

/-! #### The retraction `t` followed by `q_K` -/

lemma tS_qK_fstX (n k : ℤ) (h : (ComplexShape.down ℤ).Rel n k) :
    tS Z X n ≫ (qK Z X).f n ≫ fstX (vB b Z) n k h =
      -((sumSnd (bb Z X)).f n ≫ fstX (ub X) n k h ≫ (Q b).p.f k) := by
  obtain rfl : k = n - 1 := by simp at h; omega
  simp [tS, ta, tb, qK]
  abel

lemma tS_qK_sndX_fst (n : ℤ) :
    tS Z X n ≫ (qK Z X).f n ≫ sndX (vB b Z) n ≫ (biprod.fst : (SB Z).X n ⟶ _) =
      -((sumFst (bb Z X)).f n ≫ sndX (ua Z X) n ≫ (sumSnd (Glue.bS X (uturn b Z))).f n ≫
        (sndD Z).f n ≫ Z.pD.f n) -
      (sumSnd (bb Z X)).f n ≫ sndX (ub X) n ≫ (sumSnd (Glue.bS X (cyl b))).f n ≫ B.p.f n ≫
        (kZ Z).f n := by
  simp [tS, ta, tb, qK, pSB, comp_add, add_comp]
  abel

lemma tS_qK_sndX_snd (n : ℤ) :
    tS Z X n ≫ (qK Z X).f n ≫ sndX (vB b Z) n ≫ (biprod.snd : (SB Z).X n ⟶ _) =
      -((sumSnd (bb Z X)).f n ≫ sndX (ub X) n ≫ (sumSnd (Glue.bS X (cyl b))).f n ≫ B.p.f n) := by
  simp [tS, ta, tb, qK, pSB, comp_add, add_comp]

/-! #### Reading `φᵀ_∂` -/

lemma star_fst_phiD_jj (r : ℤ) :
    J.star ((sumFst (bb Z X)).f (N + 1 - r)) ≫ (phiD Z X).f r ≫ (jj Z X).f r =
      (phiT X (uturn b Z)).f r ≫ (fa Z X).f r := by
  simp only [phiD, sub_f_apply, comp_f, dualHom_f, sub_comp, comp_sub, assoc, inl_jj_f, inr_jj_f,
    star_sumFst_sumInl_assoc, star_sumFst_sumInr_assoc, zero_comp, sub_zero, id_comp]

lemma star_snd_phiD_jj (r : ℤ) :
    J.star ((sumSnd (bb Z X)).f (N + 1 - r)) ≫ (phiD Z X).f r ≫ (jj Z X).f r =
      -((phiT X (cyl b)).f r ≫ (fb Z X).f r) := by
  simp only [phiD, sub_f_apply, comp_f, dualHom_f, sub_comp, comp_sub, assoc, inl_jj_f, inr_jj_f,
    star_sumSnd_sumInl_assoc, star_sumSnd_sumInr_assoc, zero_comp, zero_sub, id_comp]

@[reassoc]
lemma star_sndD_relTop_fold (r : ℤ) :
    J.star ((sndD Z).f (N + 1 - r)) ≫ relTop (uturn b Z).δφ r ≫ (fold Z).f r =
      -relTop Z.δφ r := by
  simp only [relTop, assoc]
  erw [star_f_XIsoOfEq_assoc (sndD Z) (by omega : N + 1 - r = N - (r - 1))]
  simp [uturn, PairSum.δφ_hom, sndD, Double.Xn_δφ_hom, Double.δφ_pD]

@[reassoc]
lemma star_sndX_phiT_fa (r : ℤ) :
    J.star ((sumSnd (Glue.bS X (uturn b Z))).f (N + 1 - r)) ≫
      J.star (sndX (ua Z X) (N + 1 - r)) ≫ (phiT X (uturn b Z)).f r ≫ (fa Z X).f r =
        relTop (uturn b Z).δφ r ≫ (fold Z).f r ≫ (ιZ Z X).f r := by
  rw [reassoc_of% (star_sndX_phiT X (uturn b Z) r), ιY_f_fa_f]

@[reassoc]
lemma star_sndX_phiT_cyl (r : ℤ) :
    J.star ((sumSnd (Glue.bS X (cyl b))).f (N + 1 - r)) ≫
      J.star (sndX (ub X) (N + 1 - r)) ≫ (phiT X (cyl b)).f r = 0 := by
  rw [star_sndX_phiT X (cyl b) r]
  simp [relTop, cyl_δφ_hom]

@[reassoc]
lemma star_fstX_phiT_fb (r : ℤ) :
    J.star (fstX (ub X) (N + 1 - r) (N - r) (down_rel_sub N r)) ≫ (phiT X (cyl b)).f r ≫
      (fb Z X).f r = r.negOnePow • ((Q b).φ.f r ≫ (cJ b).f r ≫ (kZ Z).f r ≫ (ιZ Z X).f r) := by
  rw [reassoc_of% (star_fstX_phiT X (cyl b) r)]
  have h : (Glue.ιY (σ (Q b)) X (cyl b)).f r ≫ (fb Z X).f r = (kZ Z).f r ≫ (ιZ Z X).f r := by
    rw [← comp_f, ιY_fb, comp_f]
  simp [Linear.units_smul_comp, h, cyl_j]

lemma Qφ_cJ (r : ℤ) : (Q b).φ.f r ≫ (cJ b).f r =
    (J.star ((sumInl b).f (N - r)) - J.star ((sumInr b).f (N - r))) ≫ B.φ.f r := by
  have hφ (m : ℤ) : B.φ.f m ≫ B.p.f m = B.φ.f m := by rw [← comp_f, B.φ_comp_p]
  simp [SymPoincare.sum, cJ, add_comp, comp_add, sub_comp, hφ]
  abel

/-! #### The left square -/

@[reassoc (attr := simp)]
lemma c₁_f_fst (n : ℤ) : (c₁ Z).f n ≫ (biprod.fst : (SB Z).X n ⟶ _) = Z.pD.f n := by simp [c₁]

@[reassoc (attr := simp)]
lemma c₁_f_snd (n : ℤ) : (c₁ Z).f n ≫ (biprod.snd : (SB Z).X n ⟶ _) = 0 := by simp [c₁]

lemma relTop_pD (r : ℤ) : relTop Z.δφ r ≫ Z.pD.f r = relTop Z.δφ r := by
  simp only [relTop, assoc, Double.δφ_pD]

/-- The left map `l = c^* Ψ_Z : B'^{N+1-*} ⟶ D_Z`. -/
def lL : dualComplex J (N + 1) (Bc b Z) ⟶ Z.D := dualHom J (N + 1) (c Z) ≫ relDuality Z.δφ

lemma left_square : dualHom J (N + 1) (qK Z X) ≫ lamT Z X = lL Z ≫ ιZk Z X := by
  ext r
  have hr : (ComplexShape.down ℤ).Rel (N + 1 - r) (N - r) := down_rel_sub N r
  simp only [comp_f, dualHom_f, lamT_f, lL, assoc]
  apply cone.ext_star (J := J) (vB b Z) (N + 1 - r) (N - r) hr
  · rw [star_comp_star_assoc, star_comp_star_assoc, tS_qK_fstX Z X _ _ hr,
      star_comp_star_assoc, c, coneMap_f_fstX, J.star_neg, neg_comp, J.star_comp, J.star_comp,
      assoc, assoc, star_snd_phiD_jj, comp_neg, comp_neg, neg_neg, star_fstX_phiT_fb,
      J.star_comp, assoc, relDuality_f]
    simp only [add_comp, comp_add, assoc, cone.star_fstX_inrX_assoc, cone.star_fstX_inlX_assoc,
      Linear.comp_units_smul, Linear.units_smul_comp, zero_comp, zero_add, comp_zero,
      reassoc_of% (Qφ_cJ (b := b))]
    have e : J.star ((c₀ b).f (N - r)) = J.star ((Q b).p.f (N - r)) ≫
        (J.star ((sumInl b).f (N - r)) - J.star ((sumInr b).f (N - r))) := by
      rw [c₀, comp_f, J.star_comp, sub_f_apply, J.star_sub]
    have hj : Z.j.f r ≫ Z.pD.f r = Z.j.f r := by rw [← comp_f, Z.j_comp_pD]
    rw [e]
    simp only [ιZk, SymPoincare.neg, comp_f, neg_f_apply, Int.negOnePow_succ, kZ,
      Units.neg_smul, neg_comp, comp_neg, smul_neg, neg_neg, assoc, reassoc_of% hj]
  · apply biprod_ext_star (J := J)
    · simp only [star_comp_star_assoc, assoc]
      rw [tS_qK_sndX_fst, c, coneMap_f_sndX_assoc, c₁_f_fst]
      simp only [J.star_sub, J.star_neg, J.star_comp, sub_comp, neg_comp, assoc,
        star_fst_phiD_jj, star_snd_phiD_jj, comp_neg, star_sndX_phiT_fa,
        star_sndX_phiT_cyl_assoc, star_sndD_relTop_fold_assoc, zero_comp, comp_zero, neg_zero,
        sub_zero, neg_neg, relDuality_f, add_comp, comp_add, cone.star_sndX_inrX_assoc,
        cone.star_sndX_inlX_assoc, Linear.comp_units_smul, Linear.units_smul_comp, smul_zero,
        add_zero, ιZk, comp_f, reassoc_of% (relTop_pD Z r)]
    · simp only [star_comp_star_assoc, assoc]
      rw [tS_qK_sndX_snd, c, coneMap_f_sndX_assoc, c₁_f_snd]
      simp only [J.star_sub, J.star_neg, J.star_comp, sub_comp, neg_comp, assoc,
        star_fst_phiD_jj, star_snd_phiD_jj, comp_neg, star_sndX_phiT_cyl_assoc, zero_comp,
        comp_zero, neg_zero, J.star_zero]

/-! #### The right square -/

/-- The right map `TΨ_X : D_X^{N+1-*} ⟶ Cone(j_X)`. -/
abbrev TΨ : dualComplex J (N + 1) X.D ⟶ cone X.j := transposeHom J (N + 1) (relDuality X.δφ)

lemma fa_πW : fa Z X ≫ πW Z X = π X (uturn b Z) := by
  rw [fa, πW, π, coneMap_comp]
  apply coneMap_ext'
  · exact (Q b).p_idem
  · simp [na, add_comp]

lemma fb_πW : fb Z X ≫ πW Z X = π X (cyl b) := by
  rw [fb, πW, π, coneMap_comp]
  apply coneMap_ext'
  · exact (Q b).p_idem
  · simp [nb, add_comp]

lemma phiD_jj_πW : phiD Z X ≫ jj Z X ≫ πW Z X =
    dualHom J (N + 1) (Glue.ιW (σ (Q b)) X (uturn b Z) ≫ sumInl (bb Z X) -
      Glue.ιW (σ (Q b)) X (cyl b) ≫ sumInr (bb Z X)) ≫ TΨ X := by
  simp only [phiD, sub_comp, assoc, inl_jj_assoc, inr_jj_assoc, fa_πW, fb_πW, phiT_comp_π,
    sub_eq_add_neg, dualHom_add, dualHom_neg, dualHom_comp, add_comp, neg_comp]

lemma ιW_tS (m : ℤ) : (Glue.ιW (σ (Q b)) X (uturn b Z) ≫ sumInl (bb Z X) -
    Glue.ιW (σ (Q b)) X (cyl b) ≫ sumInr (bb Z X)).f m ≫ tS Z X m = (iK Z X).f m := by
  simp [tS, ta, tb, iK, sub_comp, Glue.ιW]

lemma right_square : dualHom J (N + 1) (iK Z X) ≫ TΨ X = lamT Z X ≫ πW Z X := by
  ext r
  simp only [comp_f, lamT_f, dualHom_f, assoc]
  rw [← comp_f (jj Z X) (πW Z X), ← comp_f (phiD Z X), phiD_jj_πW, comp_f, dualHom_f,
    star_comp_star_assoc, ιW_tS]

end UTurn

end

end HSFormal.LTheory
