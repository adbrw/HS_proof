import HSFormal.LTheory.Model.Glue
import HSFormal.LTheory.ConcreteL

/-!
# Sums, unions and transitivity of cobordism; `Lconc` is the cobordism group

* `PairOn.sum`, `NullCobordant.sum`: direct sums of Poincaré pairs (R2 on the split ladder).
* `NullCobordant.of_sum` (**cancellation**, by gluing along `B`): `A ⊕ B` and `-B`
  null-cobordant ⇒ `A` null-cobordant; `NullCobordant.of_isometry` (cylinder + cancellation).
* `PairOn.union`/`SymPair.union`: the **closed union** `D ∪_C D'` of pairs with boundaries
  `(C, φ)` and `(C, -φ)`, a closed `(N+1)`-dimensional Poincaré complex (gluing with `A = 0`
  and `SymPair.closedOfIsZero`).
* `cobordant_equivalence`: **cobordism is an equivalence relation** (transitivity:
  `(P ⊕ -Q) ⊕ (-R ⊕ Q) ≃ (P ⊕ -R) ⊕ (-Q ⊕ Q)` and cancellation).
* `CobGroup.Cls`: the cobordism group; `Lconc.cls_eq_cls_iff`: `cls P = cls Q ↔ Cobordant P Q`,
  `Lconc.cls_eq_zero_iff`, `Lconc.equivCob : Lconc A N ≃+ CobGroup.Cls A N`.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex homotopyCofiber
  HSFormal.Compression

noncomputable section

universe v u

variable {V : Type u} [Category.{v} V] [Preadditive V] {J : StrictInvolution V} {N : ℤ}

/-- A Kar split sequence given by chain maps `t`, `s`. -/
def KarSplit.ofHom {K M Q : ChainComplex V ℤ} {eK : K ⟶ K} {eM : M ⟶ M} {eQ : Q ⟶ Q}
    {i : K ⟶ M} {q : M ⟶ Q} (t : M ⟶ K) (s : Q ⟶ M) (t_kar : eM ≫ t ≫ eK = t)
    (s_kar : eQ ≫ s ≫ eM = s) (it : i ≫ t = eK) (sq : s ≫ q = eQ) (total : t ≫ i + q ≫ s = eM) :
    KarSplit eK eM eQ i q where
  t n := t.f n
  s n := s.f n
  t_kar n := by rw [← comp_f, ← comp_f, t_kar]
  s_kar n := by rw [← comp_f, ← comp_f, s_kar]
  it n := by rw [← comp_f, it]
  sq n := by rw [← comp_f, sq]
  total n := by rw [← comp_f, ← comp_f, ← add_f_apply, total]

section StarSum

variable {C D : ChainComplex V ℤ} (c : ∀ r, BinaryBicone (C.X r) (D.X r)) (k : ℤ)

@[reassoc (attr := simp)]
lemma star_sumFst_sumInl : J.star ((sumFst c).f k) ≫ J.star ((sumInl c).f k) = 𝟙 _ := by
  rw [← J.star_comp, ← comp_f, sumInl_sumFst, id_f, J.star_id]

@[reassoc (attr := simp)]
lemma star_sumFst_sumInr : J.star ((sumFst c).f k) ≫ J.star ((sumInr c).f k) = 0 := by
  rw [← J.star_comp, ← comp_f, sumInr_sumFst, zero_f, J.star_zero]

@[reassoc (attr := simp)]
lemma star_sumSnd_sumInl : J.star ((sumSnd c).f k) ≫ J.star ((sumInl c).f k) = 0 := by
  rw [← J.star_comp, ← comp_f, sumInl_sumSnd, zero_f, J.star_zero]

@[reassoc (attr := simp)]
lemma star_sumSnd_sumInr : J.star ((sumSnd c).f k) ≫ J.star ((sumInr c).f k) = 𝟙 _ := by
  rw [← J.star_comp, ← comp_f, sumInr_sumSnd, id_f, J.star_id]

@[reassoc (attr := simp)]
lemma sumInl_f_sumFst_f : (sumInl c).f k ≫ (sumFst c).f k = 𝟙 _ := by
  rw [← comp_f, sumInl_sumFst, id_f]

@[reassoc (attr := simp)]
lemma sumInl_f_sumSnd_f : (sumInl c).f k ≫ (sumSnd c).f k = 0 := by
  rw [← comp_f, sumInl_sumSnd, zero_f]

@[reassoc (attr := simp)]
lemma sumInr_f_sumFst_f : (sumInr c).f k ≫ (sumFst c).f k = 0 := by
  rw [← comp_f, sumInr_sumFst, zero_f]

@[reassoc (attr := simp)]
lemma sumInr_f_sumSnd_f : (sumInr c).f k ≫ (sumSnd c).f k = 𝟙 _ := by
  rw [← comp_f, sumInr_sumSnd, id_f]

end StarSum

variable [HasBinaryBiproducts V]

lemma coneMap_ext' {B' D' B'' D'' : ChainComplex V ℤ} {j : B' ⟶ D'} {j' : B'' ⟶ D''}
    {m m' : B' ⟶ B''} {n n' : D' ⟶ D''} (h : m ≫ j' = j ≫ n) (h' : m' ≫ j' = j ≫ n')
    (hm : m = m') (hn : n = n') : coneMap m n h = coneMap m' n' h' := by
  subst hm hn; rfl

namespace PairOn

variable {P : SymPoincare J N} (T : PairOn P)

@[reassoc (attr := simp)]
lemma j_comp_pD : T.j ≫ T.pD = T.j := T.toPair.j_comp_pD

@[reassoc (attr := simp)]
lemma p_comp_j : P.p ≫ T.j = T.j := T.toPair.p_comp_j

@[reassoc (attr := simp)]
lemma pD_idem' : T.pD ≫ T.pD = T.pD := T.pD_idem

end PairOn

/-! ### Direct sums of Poincaré pairs -/

namespace PairSum

variable {P Q : SymPoincare J N} (X : PairOn P) (Z : PairOn Q)
  (b : ∀ r, BinaryBicone (P.C.X r) (Q.C.X r))

/-- The bicones of `D_X ⊕ D_Z`. -/
abbrev bD (r : ℤ) : BinaryBicone (X.D.X r) (Z.D.X r) := BinaryBiproduct.bicone _ _

/-- `D_X ⊕ D_Z`. -/
abbrev D : ChainComplex V ℤ := sumComplex (bD X Z)

/-- The idempotent `p_X ⊕ p_Z`. -/
def pD : D X Z ⟶ D X Z :=
  sumFst (bD X Z) ≫ X.pD ≫ sumInl (bD X Z) + sumSnd (bD X Z) ≫ Z.pD ≫ sumInr (bD X Z)

/-- `j_X ⊕ j_Z`. -/
def j : (P.sum Q b).C ⟶ D X Z :=
  sumFst b ≫ X.j ≫ sumInl (bD X Z) + sumSnd b ≫ Z.j ≫ sumInr (bD X Z)

@[reassoc (attr := simp)]
lemma inl_j : sumInl b ≫ j X Z b = X.j ≫ sumInl (bD X Z) := by simp [j]

@[reassoc (attr := simp)]
lemma inr_j : sumInr b ≫ j X Z b = Z.j ≫ sumInr (bD X Z) := by simp [j]

@[reassoc (attr := simp)]
lemma j_fst : j X Z b ≫ sumFst (bD X Z) = sumFst b ≫ X.j := by simp [j]

@[reassoc (attr := simp)]
lemma j_snd : j X Z b ≫ sumSnd (bD X Z) = sumSnd b ≫ Z.j := by simp [j]

@[reassoc]
lemma inl_pD : sumInl (bD X Z) ≫ pD X Z = X.pD ≫ sumInl (bD X Z) := by simp [pD]

@[reassoc]
lemma inr_pD : sumInr (bD X Z) ≫ pD X Z = Z.pD ≫ sumInr (bD X Z) := by simp [pD]

lemma pD_idem : pD X Z ≫ pD X Z = pD X Z := by
  simp [pD, add_comp, comp_add]

lemma j_kar : (P.sum Q b).p ≫ j X Z b ≫ pD X Z = j X Z b := by
  simp [j, pD, add_comp, comp_add]

@[reassoc (attr := simp)]
lemma inl_j_f (r : ℤ) : (sumInl b).f r ≫ (j X Z b).f r = X.j.f r ≫ (sumInl (bD X Z)).f r := by
  rw [← comp_f, inl_j, comp_f]

@[reassoc (attr := simp)]
lemma inr_j_f (r : ℤ) : (sumInr b).f r ≫ (j X Z b).f r = Z.j.f r ≫ (sumInr (bD X Z)).f r := by
  rw [← comp_f, inr_j, comp_f]

variable {X Z b} in
lemma δφ_eq : dualHom J N (sumInl (bD X Z)) ≫ (dualHom J N X.j ≫ P.φ ≫ X.j) ≫ sumInl (bD X Z) +
    dualHom J N (sumInr (bD X Z)) ≫ (dualHom J N Z.j ≫ Q.φ ≫ Z.j) ≫ sumInr (bD X Z) =
      dualHom J N (j X Z b) ≫ (P.sum Q b).φ ≫ j X Z b := by
  simp only [SymPoincare.sum_φ, comp_add, add_comp, assoc, inl_j, inr_j]
  simp only [← assoc, ← dualHom_comp, inl_j, inr_j]

/-- The relative boundary `δφ_X ⊕ δφ_Z` of the sum. -/
def δφ : Homotopy (dualHom J N (j X Z b) ≫ (P.sum Q b).φ ≫ j X Z b) 0 :=
  homotopyCongr (((X.δφ.compRight (sumInl (bD X Z))).compLeft (dualHom J N (sumInl (bD X Z)))).add
    ((Z.δφ.compRight (sumInr (bD X Z))).compLeft (dualHom J N (sumInr (bD X Z))))) δφ_eq
    (by simp)

lemma δφ_hom (r r' : ℤ) : (δφ X Z b).hom r r' =
    ((X.δφ.compRight (sumInl (bD X Z))).compLeft (dualHom J N (sumInl (bD X Z)))).hom r r' +
      ((Z.δφ.compRight (sumInr (bD X Z))).compLeft (dualHom J N (sumInr (bD X Z)))).hom r r' := by
  simp [δφ]

lemma δφ_kar (r r' : ℤ) :
    (dualHom J N (pD X Z)).f r ≫ (δφ X Z b).hom r r' ≫ (pD X Z).f r' = (δφ X Z b).hom r r' := by
  rw [δφ_hom, add_comp, comp_add, kar_conjMap _ (inl_pD X Z) _ X.δφ_kar,
    kar_conjMap _ (inr_pD X Z) _ Z.δφ_kar]

lemma δφ_symm : IsSymmHomotopy J N (δφ X Z b) := by
  have h₁ := X.symm.conjMap (sumInl (bD X Z))
  have h₂ := Z.symm.conjMap (sumInr (bD X Z))
  rw [IsSymmHomotopy, transposeHomotopy_hom] at h₁ h₂ ⊢
  have e : (δφ X Z b).hom = _ + _ := funext₂ (δφ_hom X Z b)
  rw [e, transposeHomFamily_add, h₁, h₂]

lemma pD_support : SupportedIn (pD X Z) 0 (N + 1) := by
  intro r hr
  simp [pD, X.support r hr, Z.support r hr]

/-- The idempotent of `Cone(j_X ⊕ j_Z)`. -/
abbrev cS : cone (j X Z b) ⟶ cone (j X Z b) :=
  coneMap (P.sum Q b).p (pD X Z) (comm_of_kar (P.sum Q b).p_idem (pD_idem X Z) (j_kar X Z b))

/-- `Cone(j_Z) ⟶ Cone(j)`. -/
def i₀ : cone Z.j ⟶ cone (j X Z b) :=
  coneMap (j := Z.j) (j' := j X Z b) (sumInr b) (sumInr (bD X Z)) (inr_j X Z b)

/-- `Cone(j) ⟶ Cone(j_X)`. -/
def q₀ : cone (j X Z b) ⟶ cone X.j :=
  coneMap (j := j X Z b) (j' := X.j) (sumFst b) (sumFst (bD X Z)) (j_fst X Z b).symm

/-- The degreewise split sequence `0 ⟶ Cone(j_Z) ⟶ Cone(j) ⟶ Cone(j_X) ⟶ 0`. -/
def splitTop : KarSplit Z.coneIdem (cS X Z b) X.coneIdem (i₀ X Z b) (q₀ X Z b) :=
  KarSplit.ofHom
    (coneMap (j := j X Z b) (j' := Z.j) (sumSnd b) (sumSnd (bD X Z)) (j_snd X Z b).symm ≫
      Z.coneIdem)
    (X.coneIdem ≫ coneMap (j := X.j) (j' := j X Z b) (sumInl b) (sumInl (bD X Z)) (inl_j X Z b))
    (by simp only [coneMap_comp]; exact coneMap_ext' _ _ (by simp) (by simp [pD]))
    (by simp only [coneMap_comp]; exact coneMap_ext' _ _ (by simp) (by simp [pD]))
    (by simp only [i₀, coneMap_comp]; exact coneMap_ext' _ _ (by simp) (by simp))
    (by simp only [q₀, coneMap_comp]; exact coneMap_ext' _ _ (by simp) (by simp))
    (by
      simp only [i₀, q₀, coneMap_comp, ← coneMap_add]
      exact coneMap_ext' _ _ (by simp <;> abel) (by simp [pD] <;> abel))

/-- The degreewise split sequence `0 ⟶ D_X ⟶ D ⟶ D_Z ⟶ 0`. -/
def splitBot : KarSplit X.pD (pD X Z) Z.pD (sumInl (bD X Z)) (sumSnd (bD X Z)) :=
  KarSplit.ofHom (sumFst (bD X Z) ≫ X.pD) (Z.pD ≫ sumInr (bD X Z)) (by simp [pD])
    (by simp [pD]) (by simp) (by simp) (by simp [pD])

@[reassoc (attr := simp)]
lemma star_q₀_inrX (k : ℤ) : J.star ((q₀ X Z b).f k) ≫ J.star (inrX (j X Z b) k) =
    J.star (inrX X.j k) ≫ J.star ((sumFst (bD X Z)).f k) := by
  rw [← J.star_comp, q₀, inrX_coneMap_f, J.star_comp]

@[reassoc (attr := simp)]
lemma star_q₀_inlX (m k : ℤ) (h : (ComplexShape.down ℤ).Rel k m) :
    J.star ((q₀ X Z b).f k) ≫ J.star (inlX (j X Z b) m k h) =
      J.star (inlX X.j m k h) ≫ J.star ((sumFst b).f m) := by
  rw [← J.star_comp, q₀, inlX_coneMap_f, J.star_comp]

@[reassoc (attr := simp)]
lemma star_i₀_inrX (k : ℤ) : J.star ((i₀ X Z b).f k) ≫ J.star (inrX Z.j k) =
    J.star (inrX (j X Z b) k) ≫ J.star ((sumInr (bD X Z)).f k) := by
  rw [← J.star_comp, i₀, inrX_coneMap_f, J.star_comp]

@[reassoc (attr := simp)]
lemma star_i₀_inlX (m k : ℤ) (h : (ComplexShape.down ℤ).Rel k m) :
    J.star ((i₀ X Z b).f k) ≫ J.star (inlX Z.j m k h) =
      J.star (inlX (j X Z b) m k h) ≫ J.star ((sumInr b).f m) := by
  rw [← J.star_comp, i₀, inlX_coneMap_f, J.star_comp]

lemma square_left : dualHom J (N + 1) (q₀ X Z b) ≫ relDuality (δφ X Z b) =
    relDuality X.δφ ≫ sumInl (bD X Z) := by
  ext r : 1
  have hk : N + 1 - r = N - (r - 1) := by omega
  simp only [comp_f, dualHom_f, relDuality_f, comp_add, add_comp, assoc, Linear.comp_units_smul,
    Linear.units_smul_comp, star_q₀_inrX_assoc, star_q₀_inlX_assoc, relTop, δφ_hom]
  simp only [star_f_XIsoOfEq_assoc (sumFst (bD X Z)) hk, Homotopy.compLeft_hom,
    Homotopy.compRight_hom, dualHom_f, SymPoincare.sum_φ, add_f_apply, comp_f, add_comp, comp_add,
    assoc, star_sumFst_sumInl_assoc, star_sumFst_sumInr_assoc, inl_j_f, inr_j_f, zero_comp,
    comp_zero, add_zero]

@[reassoc (attr := simp)]
lemma j_snd_f (r : ℤ) : (j X Z b).f r ≫ (sumSnd (bD X Z)).f r = (sumSnd b).f r ≫ Z.j.f r := by
  rw [← comp_f, j_snd, comp_f]

lemma square_right : dualHom J (N + 1) (i₀ X Z b) ≫ relDuality Z.δφ =
    relDuality (δφ X Z b) ≫ sumSnd (bD X Z) := by
  ext r
  have hk : N + 1 - r = N - (r - 1) := by omega
  simp only [comp_f, dualHom_f, relDuality_f, comp_add, add_comp, assoc, Linear.comp_units_smul,
    Linear.units_smul_comp, star_i₀_inrX_assoc, star_i₀_inlX_assoc, relTop, δφ_hom,
    star_f_XIsoOfEq_assoc (sumInr (bD X Z)) hk, Homotopy.compLeft_hom,
    Homotopy.compRight_hom, SymPoincare.sum_φ, add_f_apply, j_snd_f, sumInl_f_sumSnd_f_assoc,
    sumInr_f_sumSnd_f_assoc, sumInl_f_sumSnd_f, sumInr_f_sumSnd_f, comp_zero, zero_comp, comp_id,
    smul_add, smul_zero, zero_add]

lemma i₀_comm : Z.coneIdem ≫ i₀ X Z b = i₀ X Z b ≫ cS X Z b := by
  simp only [i₀, coneMap_comp]; exact coneMap_ext' _ _ (by simp) (by simp [pD])

lemma q₀_comm : cS X Z b ≫ q₀ X Z b = q₀ X Z b ≫ X.coneIdem := by
  simp only [q₀, coneMap_comp]; exact coneMap_ext' _ _ (by simp) (by simp [pD])

variable [HasFiniteBiproducts V]

/-- The sum of pairs is Poincaré: R2 on `0 ⟶ Cone(j_X)^* ⟶ Cone(j)^* ⟶ Cone(j_Z)^* ⟶ 0` over
`0 ⟶ D_X ⟶ D_X ⊕ D_Z ⟶ D_Z ⟶ 0`. -/
theorem poincare :
    IsKarEquiv (dualHom J (N + 1) (cS X Z b)) (pD X Z) (relDuality (δφ X Z b)) := by
  have hcX := Glue.coneIdem_idem X
  have hcZ := Glue.coneIdem_idem Z
  have hcS : cS X Z b ≫ cS X Z b = cS X Z b := coneMap_idem _ (P.sum Q b).p_idem (pD_idem X Z)
  refine isKarEquiv_middle_of_comm (dualHom_idem hcX) (dualHom_idem hcS) (dualHom_idem hcZ)
    X.pD_idem (pD_idem X Z) Z.pD_idem ?_ ?_ (inl_pD X Z).symm ?_
    ((splitTop X Z b).dual J (N + 1)) (splitBot X Z)
    (relDuality_kar X.δφ X.pD_idem _ X.j_comp_pD P.dualHom_p_comp_φ X.δφ_kar)
    (relDuality_kar (δφ X Z b) (pD_idem X Z) _ ?_ (P.sum Q b).dualHom_p_comp_φ (δφ_kar X Z b))
    (relDuality_kar Z.δφ Z.pD_idem _ Z.j_comp_pD Q.dualHom_p_comp_φ Z.δφ_kar)
    (square_left X Z b) (square_right X Z b) X.poincare Z.poincare
  · rw [← dualHom_comp, ← dualHom_comp, q₀_comm]
  · rw [← dualHom_comp, ← dualHom_comp, i₀_comm]
  · simp [pD]
  · exact kar_right (pD_idem X Z) (j_kar X Z b)

end PairSum

variable [HasFiniteBiproducts V]

/-- **The direct sum of Poincaré pairs** `(j_X ⊕ j_Z : P ⊕ Q ⟶ D_X ⊕ D_Z, δφ_X ⊕ δφ_Z)`. -/
def PairOn.sum {P Q : SymPoincare J N} (X : PairOn P) (Z : PairOn Q)
    (b : ∀ r, BinaryBicone (P.C.X r) (Q.C.X r)) : PairOn (P.sum Q b) where
  D := PairSum.D X Z
  pD := PairSum.pD X Z
  pD_idem := PairSum.pD_idem X Z
  support := PairSum.pD_support X Z
  j := PairSum.j X Z b
  j_kar := PairSum.j_kar X Z b
  δφ := PairSum.δφ X Z b
  δφ_kar := PairSum.δφ_kar X Z b
  symm := PairSum.δφ_symm X Z b
  poincare := PairSum.poincare X Z b

/-- Sums of null-cobordant complexes (along any bicones) are null-cobordant. -/
theorem NullCobordant.sum {P Q : SymPoincare J N} (hP : NullCobordant P) (hQ : NullCobordant Q)
    (b : ∀ r, BinaryBicone (P.C.X r) (Q.C.X r)) : NullCobordant (P.sum Q b) := by
  obtain ⟨X⟩ := nullCobordant_iff_nonempty_pairOn.1 hP
  obtain ⟨Z⟩ := nullCobordant_iff_nonempty_pairOn.1 hQ
  exact nullCobordant_iff_nonempty_pairOn.2 ⟨X.sum Z b⟩

/-! ### Cancellation and the closed union -/

omit [HasBinaryBiproducts V] [HasFiniteBiproducts V] in
/-- The splitting `A ⊕ B ≅ A ⊕ B` of a sum (along any bicones). -/
def BdSplit.ofSum (A B : SymPoincare J N) (b : ∀ r, BinaryBicone (A.C.X r) (B.C.X r)) :
    BdSplit (A.sum B b) A B where
  ιA := A.p ≫ sumInl b
  ιB := B.p ≫ sumInr b
  πA := sumFst b ≫ A.p
  πB := sumSnd b ≫ B.p
  ιA_kar := by simp
  ιB_kar := by simp
  πA_kar := by simp [add_comp]
  πB_kar := by simp [add_comp]
  ιA_πA := by simp
  ιB_πB := by simp
  ιA_πB := by simp
  ιB_πA := by simp
  total := by simp
  φ_eq := by simp

variable [Linear ℚ V]

/-- **Cancellation** (gluing along `B`): if `A ⊕ B` and `-B` are null-cobordant, so is `A`. -/
theorem NullCobordant.of_sum {A B : SymPoincare J N} {b : ∀ r, BinaryBicone (A.C.X r) (B.C.X r)}
    (h : NullCobordant (A.sum B b)) (h' : NullCobordant B.neg) : NullCobordant A := by
  obtain ⟨W⟩ := nullCobordant_iff_nonempty_pairOn.1 h
  obtain ⟨Y⟩ := nullCobordant_iff_nonempty_pairOn.1 h'
  exact nullCobordant_iff_nonempty_pairOn.2 ⟨W.glue (BdSplit.ofSum A B b) Y⟩

omit [HasBinaryBiproducts V] [Linear ℚ V] in
/-- The Poincaré complex `0` on the zero complex. -/
abbrev zeroP : SymPoincare J N := SymPoincare.zero HomologicalComplex.zero

omit [HasBinaryBiproducts V] [Linear ℚ V] in
lemma isZero_zeroP_X (r : ℤ) : IsZero ((zeroP (J := J) (N := N)).C.X r) := isZero_zero V

omit [HasBinaryBiproducts V] [HasFiniteBiproducts V] [Linear ℚ V] in
/-- The splitting `B ≅ 0 ⊕ B`. -/
def BdSplit.ofRight (B Z : SymPoincare J N) (hZ : Z.p = 0) : BdSplit B Z B where
  ιA := 0
  ιB := B.p
  πA := 0
  πB := B.p
  ιA_kar := by simp
  ιB_kar := by simp
  πA_kar := by simp
  πB_kar := by simp
  ιA_πA := by simp [hZ]
  ιB_πB := by simp
  ιA_πB := by simp
  ιB_πA := by simp
  total := by simp
  φ_eq := by simp

/-- **The union of two Poincaré pairs along their common boundary** (Ran80I §3): for pairs
`(f : C ⟶ D, (δφ, φ))` and `(f' : C ⟶ D', (δφ', -φ))`, the closed `(N+1)`-dimensional Poincaré
complex `D ∪_C D' = Cone((f, f') : C ⟶ D ⊕ D')` with the (symmetrized) union structure
`δφ ∪_φ δφ'`. -/
def PairOn.union {B : SymPoincare J N} (X : PairOn B) (Y : PairOn B.neg) : SymPoincare J (N + 1) :=
  (X.glue (BdSplit.ofRight B zeroP rfl) Y).toPair.closedOfIsZero isZero_zeroP_X

lemma PairOn.union_C {B : SymPoincare J N} (X : PairOn B) (Y : PairOn B.neg) :
    (X.union Y).C = cone (Glue.u (BdSplit.ofRight B zeroP rfl) X Y) := rfl

/-- The union `D ∪_C D'` of two pairs with boundaries `(C, φ)` and `(C, -φ)`. -/
def SymPair.union (X Y : SymPair J N) (h : Y.bd = X.bd.neg) : SymPoincare J (N + 1) :=
  X.toPairOn.union (h ▸ Y.toPairOn)

/-- Null-cobordance is invariant under homotopy isometries (cylinder + cancellation). -/
theorem NullCobordant.of_isometry {P Q : SymPoincare J N} (e : P.HomotopyIsometry Q)
    (h : NullCobordant P) : NullCobordant Q :=
  NullCobordant.of_sum (e.symm.nullCobordant_sum_neg fun _ ↦ BinaryBiproduct.bicone _ _)
    (by rwa [SymPoincare.neg_neg])

/-! ### Strict isometries rearranging sums -/

namespace SymPoincare

omit [HasBinaryBiproducts V] [HasFiniteBiproducts V] [Linear ℚ V]

variable (P Q R S : SymPoincare J N)

/-- `P ⊕ Q ≃ Q ⊕ P`. -/
def sumComm (b : ∀ r, BinaryBicone (P.C.X r) (Q.C.X r))
    (b' : ∀ r, BinaryBicone (Q.C.X r) (P.C.X r)) : (P.sum Q b).HomotopyIsometry (Q.sum P b') := by
  refine .ofEq (sumFst b ≫ P.p ≫ sumInr b' + sumSnd b ≫ Q.p ≫ sumInl b')
    (sumFst b' ≫ Q.p ≫ sumInr b + sumSnd b' ≫ P.p ≫ sumInl b) ?_ ?_ ?_ ?_ ?_ <;>
    simp [add_comp, comp_add] <;> abel

/-- `(P ⊕ Q) ⊕ R ≃ P ⊕ (Q ⊕ R)`. -/
def sumAssoc (b : ∀ r, BinaryBicone (P.C.X r) (Q.C.X r))
    (c : ∀ r, BinaryBicone ((P.sum Q b).C.X r) (R.C.X r))
    (b' : ∀ r, BinaryBicone (Q.C.X r) (R.C.X r))
    (c' : ∀ r, BinaryBicone (P.C.X r) ((Q.sum R b').C.X r)) :
    ((P.sum Q b).sum R c).HomotopyIsometry (P.sum (Q.sum R b') c') := by
  refine .ofEq (sumFst c ≫ sumFst b ≫ P.p ≫ sumInl c' +
      sumFst c ≫ sumSnd b ≫ Q.p ≫ sumInl b' ≫ sumInr c' + sumSnd c ≫ R.p ≫ sumInr b' ≫ sumInr c')
    (sumFst c' ≫ P.p ≫ sumInl b ≫ sumInl c + sumSnd c' ≫ sumFst b' ≫ Q.p ≫ sumInr b ≫ sumInl c +
      sumSnd c' ≫ sumSnd b' ≫ R.p ≫ sumInr c) ?_ ?_ ?_ ?_ ?_ <;>
    simp [add_comp, comp_add] <;> abel

/-- `P ⊕ 0 ≃ P` for a complex `Z` with `p_Z = 0`. -/
def sumZero (Z : SymPoincare J N) (hZ : Z.p = 0) (b : ∀ r, BinaryBicone (P.C.X r) (Z.C.X r)) :
    (P.sum Z b).HomotopyIsometry P := by
  have hφ : Z.φ = 0 := by rw [← Z.φ_comp_p, hZ, comp_zero]
  refine .ofEq (sumFst b ≫ P.p) (P.p ≫ sumInl b) ?_ ?_ ?_ ?_ ?_ <;>
    simp [hZ, hφ]

/-- `-(P ⊕ Q) ≃ -P ⊕ -Q`. -/
def negSum (b : ∀ r, BinaryBicone (P.C.X r) (Q.C.X r))
    (b' : ∀ r, BinaryBicone (P.neg.C.X r) (Q.neg.C.X r)) :
    (P.sum Q b).neg.HomotopyIsometry (P.neg.sum Q.neg b') := by
  refine .ofEq (sumFst b ≫ P.p ≫ sumInl b' + sumSnd b ≫ Q.p ≫ sumInr b')
    (sumFst b' ≫ P.p ≫ sumInl b + sumSnd b' ≫ Q.p ≫ sumInr b) ?_ ?_ ?_ ?_ ?_ <;>
    simp [add_comp, comp_add]

/-- `-(P ⊕ -Q) ≃ Q ⊕ -P`. -/
def negSumSwap (b : ∀ r, BinaryBicone (P.C.X r) (Q.neg.C.X r))
    (b' : ∀ r, BinaryBicone (Q.C.X r) (P.neg.C.X r)) :
    (P.sum Q.neg b).neg.HomotopyIsometry (Q.sum P.neg b') := by
  refine .ofEq (sumFst b ≫ P.p ≫ sumInr b' + sumSnd b ≫ Q.p ≫ sumInl b')
    (sumFst b' ≫ Q.p ≫ sumInr b + sumSnd b' ≫ P.p ≫ sumInl b) ?_ ?_ ?_ ?_ ?_ <;>
    simp [add_comp, comp_add] <;> abel

/-- The interchange `(P ⊕ Q) ⊕ (R ⊕ S) ≃ (P ⊕ R) ⊕ (Q ⊕ S)`. -/
def sumInterchange (b₁ : ∀ r, BinaryBicone (P.C.X r) (Q.C.X r))
    (b₂ : ∀ r, BinaryBicone (R.C.X r) (S.C.X r))
    (c : ∀ r, BinaryBicone ((P.sum Q b₁).C.X r) ((R.sum S b₂).C.X r))
    (b₃ : ∀ r, BinaryBicone (P.C.X r) (R.C.X r)) (b₄ : ∀ r, BinaryBicone (Q.C.X r) (S.C.X r))
    (c' : ∀ r, BinaryBicone ((P.sum R b₃).C.X r) ((Q.sum S b₄).C.X r)) :
    ((P.sum Q b₁).sum (R.sum S b₂) c).HomotopyIsometry ((P.sum R b₃).sum (Q.sum S b₄) c') := by
  refine .ofEq (sumFst c ≫ sumFst b₁ ≫ P.p ≫ sumInl b₃ ≫ sumInl c' +
      sumFst c ≫ sumSnd b₁ ≫ Q.p ≫ sumInl b₄ ≫ sumInr c' +
      sumSnd c ≫ sumFst b₂ ≫ R.p ≫ sumInr b₃ ≫ sumInl c' +
      sumSnd c ≫ sumSnd b₂ ≫ S.p ≫ sumInr b₄ ≫ sumInr c')
    (sumFst c' ≫ sumFst b₃ ≫ P.p ≫ sumInl b₁ ≫ sumInl c +
      sumSnd c' ≫ sumFst b₄ ≫ Q.p ≫ sumInr b₁ ≫ sumInl c +
      sumFst c' ≫ sumSnd b₃ ≫ R.p ≫ sumInl b₂ ≫ sumInr c +
      sumSnd c' ≫ sumSnd b₄ ≫ S.p ≫ sumInr b₂ ≫ sumInr c) ?_ ?_ ?_ ?_ ?_ <;>
    simp [add_comp, comp_add] <;> abel

/-- `(-Q ⊕ Q)^- ≃ Q ⊕ -Q`. -/
def negSumNeg (b : ∀ r, BinaryBicone (Q.neg.C.X r) (Q.C.X r))
    (b' : ∀ r, BinaryBicone (Q.C.X r) (Q.neg.C.X r)) :
    (Q.neg.sum Q b).neg.HomotopyIsometry (Q.sum Q.neg b') := by
  refine .ofEq (sumFst b ≫ Q.p ≫ sumInl b' + sumSnd b ≫ Q.p ≫ sumInr b')
    (sumFst b' ≫ Q.p ≫ sumInl b + sumSnd b' ≫ Q.p ≫ sumInr b) ?_ ?_ ?_ ?_ ?_ <;>
    simp [add_comp, comp_add]

/-- `(P ⊕ -P') ⊕ (Q ⊕ -Q') ≃ (P ⊕ Q) ⊕ -(P' ⊕ Q')`. -/
def sumInterchangeNeg (P' Q' : SymPoincare J N) (b₁ : ∀ r, BinaryBicone (P.C.X r) (P'.neg.C.X r))
    (b₂ : ∀ r, BinaryBicone (Q.C.X r) (Q'.neg.C.X r))
    (c : ∀ r, BinaryBicone ((P.sum P'.neg b₁).C.X r) ((Q.sum Q'.neg b₂).C.X r))
    (b₃ : ∀ r, BinaryBicone (P.C.X r) (Q.C.X r)) (b₄ : ∀ r, BinaryBicone (P'.C.X r) (Q'.C.X r))
    (c' : ∀ r, BinaryBicone ((P.sum Q b₃).C.X r) ((P'.sum Q' b₄).neg.C.X r)) :
    ((P.sum P'.neg b₁).sum (Q.sum Q'.neg b₂) c).HomotopyIsometry
      ((P.sum Q b₃).sum (P'.sum Q' b₄).neg c') := by
  refine .ofEq (sumFst c ≫ sumFst b₁ ≫ P.p ≫ sumInl b₃ ≫ sumInl c' +
      sumFst c ≫ sumSnd b₁ ≫ P'.p ≫ sumInl b₄ ≫ sumInr c' +
      sumSnd c ≫ sumFst b₂ ≫ Q.p ≫ sumInr b₃ ≫ sumInl c' +
      sumSnd c ≫ sumSnd b₂ ≫ Q'.p ≫ sumInr b₄ ≫ sumInr c')
    (sumFst c' ≫ sumFst b₃ ≫ P.p ≫ sumInl b₁ ≫ sumInl c +
      sumSnd c' ≫ sumFst b₄ ≫ P'.p ≫ sumInr b₁ ≫ sumInl c +
      sumFst c' ≫ sumSnd b₃ ≫ Q.p ≫ sumInl b₂ ≫ sumInr c +
      sumSnd c' ≫ sumSnd b₄ ≫ Q'.p ≫ sumInr b₂ ≫ sumInr c) ?_ ?_ ?_ ?_ ?_ <;>
    simp [add_comp, comp_add] <;> abel

end SymPoincare

/-! ### Cobordism is an equivalence relation -/

section CobordismRel

open SymPoincare

/-- Chosen bicones `X_r ⊞ Y_r`. -/
abbrev bb (P Q : SymPoincare J N) (r : ℤ) : BinaryBicone (P.C.X r) (Q.C.X r) :=
  BinaryBiproduct.bicone _ _

variable (hU : ∀ X Y : V, Nonempty (UnitaryBicone J X Y))
include hU

/-- Cobordism can be tested along any bicones. -/
theorem cobordant_iff {P Q : SymPoincare J N} (b : ∀ r, BinaryBicone (P.C.X r) (Q.neg.C.X r)) :
    Cobordant P Q ↔ NullCobordant (P.sum Q.neg b) := by
  constructor
  · rintro ⟨u, hu⟩
    exact hu.of_isometry (sumIsometry P Q.neg _ b)
  · intro h
    let u : ∀ r, UnitaryBicone J (P.C.X r) (Q.C.X r) := fun r ↦ (hU _ _).some
    exact ⟨u, h.of_isometry (sumIsometry P Q.neg b _)⟩

theorem cobordant_refl' (P : SymPoincare J N) : Cobordant P P :=
  (cobordant_iff hU (bb P P.neg)).2 (nullCobordant_sum_neg_self P _)

theorem Cobordant.symm' {P Q : SymPoincare J N} (h : Cobordant P Q) : Cobordant Q P :=
  (cobordant_iff hU (bb Q P.neg)).2
    (((cobordant_iff hU (bb P Q.neg)).1 h).neg.of_isometry (negSumSwap P Q _ _))

/-- **Transitivity of cobordism** (gluing two cobordisms along `Q`): `(P ⊕ -Q) ⊕ (-R ⊕ Q) ≃
(P ⊕ -R) ⊕ (-Q ⊕ Q)`, and the second summand is cancelled by `Q ⊕ -Q`. -/
theorem Cobordant.trans' {P Q R : SymPoincare J N} (h₁ : Cobordant P Q) (h₂ : Cobordant Q R) :
    Cobordant P R := by
  have h₁' := (cobordant_iff hU (bb P Q.neg)).1 h₁
  have h₂' := ((cobordant_iff hU (bb Q R.neg)).1 h₂).of_isometry (sumComm Q R.neg _ (bb _ _))
  have h₃ := (h₁'.sum h₂' (bb _ _)).of_isometry
    (sumInterchange P Q.neg R.neg Q _ _ _ (bb _ _) (bb _ _) (bb _ _))
  have h₄ : NullCobordant (Q.neg.sum Q (bb _ _)).neg :=
    (nullCobordant_sum_neg_self Q (bb _ _)).of_isometry (negSumNeg Q (bb _ _) (bb _ _)).symm
  exact (cobordant_iff hU (bb P R.neg)).2 (h₃.of_sum h₄)

/-- **Cobordism is an equivalence relation.** -/
theorem cobordant_equivalence : Equivalence (Cobordant (J := J) (N := N)) :=
  ⟨cobordant_refl' hU, fun h ↦ h.symm' hU, fun h₁ h₂ ↦ h₁.trans' hU h₂⟩

end CobordismRel

/-! ### `Lconc` is the cobordism group -/

namespace CobGroup

open SymPoincare

variable (A : InvCat) (N : ℤ)

/-- The cobordism relation as a setoid. -/
def setoid : Setoid (SymPoincare A.inv N) := ⟨Cobordant, cobordant_equivalence A.unitary⟩

/-- Cobordism classes of `N`-dimensional Poincaré complexes in `Kar A`. -/
def Cls : Type := Quotient (setoid A N)

variable {A N}

/-- The class of a complex. -/
def mk (P : SymPoincare A.inv N) : Cls A N := Quotient.mk (setoid A N) P

lemma mk_eq_mk {P Q : SymPoincare A.inv N} : mk P = mk Q ↔ Cobordant P Q := Quotient.eq

lemma add_compat {P P' Q Q' : SymPoincare A.inv N} (h : Cobordant P P') (h' : Cobordant Q Q') :
    Cobordant (P.sum Q (bb P Q)) (P'.sum Q' (bb P' Q')) :=
  (cobordant_iff A.unitary (bb _ _)).2
    ((((cobordant_iff A.unitary (bb P P'.neg)).1 h).sum
      ((cobordant_iff A.unitary (bb Q Q'.neg)).1 h') (bb _ _)).of_isometry
        (sumInterchangeNeg P Q P' Q' _ _ _ (bb _ _) (bb _ _) (bb _ _)))

lemma neg_compat {P Q : SymPoincare A.inv N} (h : Cobordant P Q) : Cobordant P.neg Q.neg :=
  (cobordant_iff A.unitary (bb _ _)).2
    (((cobordant_iff A.unitary (bb P Q.neg)).1 h).neg.of_isometry (negSum P Q.neg _ _))

instance : Zero (Cls A N) := ⟨mk zeroP⟩

instance : Add (Cls A N) :=
  ⟨Quotient.map₂ (fun P Q ↦ P.sum Q (bb P Q)) (fun _ _ h _ _ h' ↦ add_compat h h')⟩

instance : Neg (Cls A N) := ⟨Quotient.map SymPoincare.neg (fun _ _ h ↦ neg_compat h)⟩

lemma mk_add (P Q : SymPoincare A.inv N) : mk P + mk Q = mk (P.sum Q (bb P Q)) := rfl

lemma mk_neg (P : SymPoincare A.inv N) : -mk P = mk P.neg := rfl

lemma mk_eq_of_isometry {P Q : SymPoincare A.inv N} (e : P.HomotopyIsometry Q) : mk P = mk Q :=
  Quotient.sound (e.cobordant fun _ ↦ (A.unitary _ _).some)

lemma mk_eq_zero {P : SymPoincare A.inv N} (h : NullCobordant P) : mk P = 0 :=
  Quotient.sound ((cobordant_iff A.unitary (bb _ _)).2
    (h.of_isometry (sumZero P zeroP.neg rfl _).symm))

/-- **The cobordism group**: cobordism classes under direct sum. -/
instance : AddCommGroup (Cls A N) where
  add_assoc := by
    rintro ⟨P⟩ ⟨Q⟩ ⟨R⟩
    exact mk_eq_of_isometry (sumAssoc P Q R _ _ _ _)
  zero_add := by
    rintro ⟨P⟩
    exact mk_eq_of_isometry ((sumComm _ _ _ (bb _ _)).trans (sumZero P zeroP rfl _))
  add_zero := by
    rintro ⟨P⟩
    exact mk_eq_of_isometry (sumZero P zeroP rfl _)
  add_comm := by
    rintro ⟨P⟩ ⟨Q⟩
    exact mk_eq_of_isometry (sumComm P Q _ _)
  neg_add_cancel := by
    rintro ⟨P⟩
    exact mk_eq_zero ((nullCobordant_sum_neg_self P (bb _ _)).of_isometry (sumComm _ _ _ _))
  nsmul := nsmulRec
  zsmul := zsmulRec

end CobGroup

namespace Lconc

open CobGroup

variable {A : InvCat} {N : ℤ}

/-- The comparison map `Lconc A N ⟶ cobordism group`. -/
def toCob : Lconc A N →+ Cls A N :=
  lift CobGroup.mk (fun P Q _ ↦ mk_eq_of_isometry (P.sumIsometry Q _ (bb P Q)))
    (fun _ hP ↦ mk_eq_zero hP)

@[simp]
lemma toCob_cls (P : SymPoincare A.inv N) : toCob (cls P) = CobGroup.mk P := lift_cls _ _ _ P

/-- **`Lconc` is literally the cobordism group**: two complexes have the same class iff they
are cobordant (transitivity of cobordism makes the relations of `Lconc` coincide with
cobordism). -/
theorem cls_eq_cls_iff {P Q : SymPoincare A.inv N} : cls P = cls Q ↔ Cobordant P Q :=
  ⟨fun h ↦ mk_eq_mk.1 (by simpa using congrArg toCob h), cls_eq_of_cobordant⟩

/-- A complex has class zero iff it is null-cobordant. -/
theorem cls_eq_zero_iff {P : SymPoincare A.inv N} : cls P = 0 ↔ NullCobordant P := by
  refine ⟨fun h ↦ ?_, cls_eq_zero⟩
  rw [← cls_eq_zero_of_p_eq_zero (P := zeroP) rfl, cls_eq_cls_iff,
    cobordant_iff A.unitary (bb _ _)] at h
  exact h.of_isometry (SymPoincare.sumZero P zeroP.neg rfl _)

/-- `Lconc A N` is isomorphic to the cobordism group. -/
def equivCob : Lconc A N ≃+ Cls A N :=
  AddEquiv.ofBijective toCob ⟨fun x y h ↦ by
    obtain ⟨P, rfl⟩ := cls_surjective x
    obtain ⟨Q, rfl⟩ := cls_surjective y
    simp only [toCob_cls] at h
    exact cls_eq_of_cobordant (mk_eq_mk.1 h), fun x ↦ by
    obtain ⟨P⟩ := x
    exact ⟨cls P, toCob_cls P⟩⟩

end Lconc

end

end HSFormal.LTheory
