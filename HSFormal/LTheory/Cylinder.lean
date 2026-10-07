import HSFormal.LTheory.Pairs

/-!
# The algebraic cylinder (L-theory module M2)

For a homotopy isometry `e = (f, g) : (C, φ) ≃ (C', φ')`, the pair
`j = (f, 1) : C ⊕ C' ⟶ C'` with boundary `(C, φ) ⊕ (C', -φ')` and relative structure the
symmetrized Kar homotopy `δφ : f φ f^* ≃ φ'` is a Poincaré pair [Ran89, 3.10]: on the
boundary summand `ι`, `Ψ ι = -φ f` (`bdInc_comp_relDuality`), and `ι p_C^*` is a Kar homotopy
inverse of
`λ = (-1)^r inlX^* k^*` for the kernel inclusion `k = (p, -f) : C ⟶ C ⊕ C'`, the cone homotopy
being `h(x, c) = (0, x)`.  Hence homotopy-isometric complexes are cobordant and `P ⊕ -P` is
null-cobordant.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression

noncomputable section

universe v u

variable {V : Type u} [Category.{v} V] [Preadditive V] {J : StrictInvolution V} {N : ℤ}

section KarSymm

variable {C : ChainComplex V ℤ}

/-- Ranicki's `T` commutes with Kar compression: `T(q^* h q) = q^* (T h) q`. -/
lemma transposeHomFamily_conj (q : C ⟶ C) (h : ∀ i k, (dualComplex J N C).X i ⟶ C.X k) :
    transposeHomFamily J N (fun i k ↦ (dualHom J N q).f i ≫ h i k ≫ q.f k) =
      fun i k ↦ (dualHom J N q).f i ≫ transposeHomFamily J N h i k ≫ q.f k := by
  funext r r'
  simp only [transposeHomFamily, dualHom_f, J.star_comp, J.star_star, bidual_hom_f,
    Linear.units_smul_comp, Linear.comp_units_smul, assoc, f_comp_eqToHom q (sub_sub_cancel N r')]

variable [Linear ℚ V]

/-- Symmetrizing a Kar homotopy gives a Kar homotopy. -/
lemma kar_symmHomotopy_hom {q : C ⟶ C} (hq : q ≫ q = q) {φ φ' : dualComplex J N C ⟶ C}
    (hφ : IsStrictSymm J N φ) (hφ' : IsStrictSymm J N φ') (H : Homotopy φ φ')
    (hH : ∀ r r', (dualHom J N q).f r ≫ H.hom r r' ≫ q.f r' = H.hom r r') (r r' : ℤ) :
    (dualHom J N q).f r ≫ (symmHomotopy hφ hφ' H).hom r r' ≫ q.f r' =
      (symmHomotopy hφ hφ' H).hom r r' := by
  have e : H.hom = fun i k ↦ (dualHom J N q).f i ≫ H.hom i k ≫ q.f k :=
    funext₂ fun i k ↦ (hH i k).symm
  have hq' (i : ℤ) : q.f i ≫ q.f i = q.f i := by rw [← comp_f, hq]
  have hq'' (i : ℤ) : (dualHom J N q).f i ≫ (dualHom J N q).f i = (dualHom J N q).f i := by
    rw [← comp_f, ← dualHom_comp, hq]
  rw [symmHomotopy_hom, e, transposeHomFamily_conj]
  simp only [Pi.smul_apply, Pi.add_apply, Linear.comp_smul, Linear.smul_comp, comp_add, add_comp,
    assoc, hq', reassoc_of% (hq'' r)]

end KarSymm

namespace SymPoincare.HomotopyIsometry

variable {P Q : SymPoincare J N} (e : HomotopyIsometry P Q)
  (b : ∀ r, BinaryBicone (P.C.X r) (Q.C.X r))

/-- The boundary map `j = (f, 1) : C ⊕ C' ⟶ C'` of the cylinder. -/
def cylJ : (P.sum Q.neg b).C ⟶ Q.C := sumFst b ≫ e.f + sumSnd b ≫ Q.p

@[reassoc (attr := simp)]
lemma sumInl_cylJ : sumInl b ≫ e.cylJ b = e.f := by simp [cylJ]

@[reassoc (attr := simp)]
lemma sumInr_cylJ : sumInr b ≫ e.cylJ b = Q.p := by simp [cylJ]

lemma cylJ_kar : (P.sum Q.neg b).p ≫ e.cylJ b ≫ Q.p = e.cylJ b := by
  simp [cylJ, add_comp]

@[reassoc (attr := simp)]
lemma dualHom_cylJ_dualHom_sumInl :
    dualHom J N (e.cylJ b) ≫ dualHom J N (sumInl b) = dualHom J N e.f := by
  rw [← dualHom_comp, sumInl_cylJ]

@[reassoc (attr := simp)]
lemma dualHom_cylJ_dualHom_sumInr :
    dualHom J N (e.cylJ b) ≫ dualHom J N (sumInr b) = dualHom J N Q.p := by
  rw [← dualHom_comp, sumInr_cylJ]

lemma dualHom_cylJ_conj : dualHom J N (e.cylJ b) ≫ (P.sum Q.neg b).φ ≫ e.cylJ b =
    dualHom J N e.f ≫ P.φ ≫ e.f + -Q.φ := by
  simp [comp_add, add_comp]

/-- The kernel inclusion `k = (p, -f) : C ⟶ C ⊕ C'` of `j = (f, 1)`. -/
def cylKer : P.C ⟶ (P.sum Q.neg b).C := P.p ≫ sumInl b - e.f ≫ sumInr b

@[reassoc (attr := simp)]
lemma cylKer_cylJ : e.cylKer b ≫ e.cylJ b = 0 := by simp [cylKer, sub_comp]

@[reassoc (attr := simp)]
lemma dualHom_sumFst_p_dualHom_sumInl :
    dualHom J N (sumFst b ≫ P.p) ≫ dualHom J N (sumInl b) = dualHom J N P.p := by
  rw [← dualHom_comp, sumInl_sumFst_assoc]

@[reassoc (attr := simp)]
lemma dualHom_sumFst_p_dualHom_sumInr :
    dualHom J N (sumFst b ≫ P.p) ≫ dualHom J N (sumInr b) = 0 := by
  rw [← dualHom_comp, sumInr_sumFst_assoc, zero_comp, dualHom_zero]

variable [Linear ℚ V]

/-- The symmetrized Kar homotopy `f φ f^* ≃ φ'`. -/
def cylHomotopy : Homotopy (dualHom J N e.f ≫ P.φ ≫ e.f) Q.φ :=
  symmHomotopy (P.symm.conj e.f) Q.symm (karHomotopy (p := dualHom J N Q.p) (q := Q.p) e.conj
    (by simp only [assoc, e.f_comp_p]; rw [← assoc, ← dualHom_comp, e.f_comp_p]) Q.φ_kar)

lemma cylHomotopy_kar (r r' : ℤ) :
    (dualHom J N Q.p).f r ≫ e.cylHomotopy.hom r r' ≫ Q.p.f r' = e.cylHomotopy.hom r r' := by
  refine kar_symmHomotopy_hom Q.p_idem _ _ _ (fun r r' ↦ ?_) r r'
  have h₁ (i : ℤ) : Q.p.f i ≫ Q.p.f i = Q.p.f i := by rw [← comp_f, Q.p_idem]
  have h₂ : J.star (Q.p.f (N - r)) ≫ J.star (Q.p.f (N - r)) = J.star (Q.p.f (N - r)) := by
    rw [← J.star_comp, h₁]
  simp [h₁, reassoc_of% h₂]

/-- The relative structure `δφ` of the cylinder: `j (φ ⊕ -φ') j^* = f φ f^* - φ' ≃ 0`. -/
def cylδφ : Homotopy (dualHom J N (e.cylJ b) ≫ (P.sum Q.neg b).φ ≫ e.cylJ b) 0 :=
  homotopyCongr (e.cylHomotopy.add (Homotopy.refl (-Q.φ))) (e.dualHom_cylJ_conj b).symm (by simp)

@[simp]
lemma cylδφ_hom (r r' : ℤ) : (e.cylδφ b).hom r r' = e.cylHomotopy.hom r r' := by
  simp [cylδφ]

lemma dualHom_pD_comp_cylδφ_hom (r r' : ℤ) :
    (dualHom J N Q.p).f r ≫ (e.cylδφ b).hom r r' = (e.cylδφ b).hom r r' := by
  rw [cylδφ_hom]
  conv_lhs => rw [← e.cylHomotopy_kar r r']
  rw [← assoc, ← comp_f, ← dualHom_comp, Q.p_idem, e.cylHomotopy_kar]

variable [HasBinaryBiproducts V]

lemma cyl_poincare (h : (P.sum Q.neg b).p ≫ e.cylJ b = e.cylJ b ≫ Q.p) :
    IsKarEquiv (dualHom J (N + 1) (coneMap _ _ h)) Q.p (relDuality (e.cylδφ b)) := by
  have hpP : dualHom J N P.p ≫ dualHom J N P.p = dualHom J N P.p := by
    rw [← dualHom_comp, P.p_idem]
  have hpJ : dualHom J (N + 1) (coneMap _ _ h) ≫ dualHom J (N + 1) (coneMap _ _ h) =
      dualHom J (N + 1) (coneMap _ _ h) := by
    rw [← dualHom_comp, coneMap_idem h (P.sum Q.neg b).p_idem Q.p_idem]
  have hH := coneHomotopy (Q.p ≫ sumInr b) h
    (by simp [cylKer] : ((sumFst b ≫ P.p) ≫ e.cylKer b) ≫ e.cylJ b = e.cylJ b ≫ 0)
    (by simp [cylKer, cylJ, comp_sub]; abel) (by simp)
  have hs : dualHom J N P.p ≫
      (dualHom J N (sumFst b ≫ P.p) ≫ bdInc (J := J) (N := N) (e.cylJ b)) ≫
        dualHom J (N + 1) (coneMap _ _ h) = dualHom J N (sumFst b ≫ P.p) ≫ bdInc (e.cylJ b) := by
    simp only [assoc]
    rw [bdInc_comp_dualHom_coneMap]
    simp only [← assoc, ← dualHom_comp]
    congr 2
    simp [add_comp]
  have hπ : IsKarEquiv (dualHom J (N + 1) (coneMap _ _ h)) (dualHom J N P.p)
      (coneDualFst (e.cylJ b) (e.cylKer b) (e.cylKer_cylJ b)) := by
    refine ⟨_, hs, ⟨Homotopy.ofEq ?_⟩, ⟨homotopyCongr (dualHomotopy J (N + 1) hH).symm
      (coneDualFst_comp_bdInc _ _ _ _).symm rfl⟩⟩
    rw [assoc, bdInc_comp_coneDualFst, ← dualHom_comp]
    simp [cylKer]
  have hP : IsKarEquiv (dualHom J N P.p) P.p P.φ := P.poincare
  have hφf : IsKarEquiv (dualHom J N P.p) Q.p (P.φ ≫ e.f) :=
    hP.comp ⟨e.g, e.g_kar, ⟨e.gf⟩, ⟨e.fg⟩⟩ hpP P.p_idem Q.p_idem
  refine (hπ.comp hφf.neg hpJ hpP Q.p_idem).of_homotopy ?_
  have hsΨ : (dualHom J N (sumFst b ≫ P.p) ≫ bdInc (e.cylJ b)) ≫ relDuality (e.cylδφ b) =
      -(P.φ ≫ e.f) := by
    simp [comp_add]
  rw [← hsΨ]
  exact homotopyCongr (((homotopyCongr (dualHomotopy J (N + 1) hH) rfl
    (coneDualFst_comp_bdInc _ _ (e.cylKer_cylJ b) _).symm).symm.compRight
      (relDuality (e.cylδφ b))))
    (by simp only [assoc]) (dualHom_coneMap_comp_relDuality h _ (P.sum Q.neg b).dualHom_p_comp_φ
      (e.dualHom_pD_comp_cylδφ_hom b))

omit [HasBinaryBiproducts V] in
lemma isSymmHomotopy_cylδφ : IsSymmHomotopy J N (e.cylδφ b) := by
  have hs : IsSymmHomotopy J N e.cylHomotopy := isSymmHomotopy_symmHomotopy _ _ _
  rw [IsSymmHomotopy, transposeHomotopy_hom] at hs ⊢
  rwa [show (e.cylδφ b).hom = e.cylHomotopy.hom from funext₂ (e.cylδφ_hom b)]

/-- The algebraic cylinder of a homotopy isometry `e = (f, g) : P ≃ Q`: the Poincaré pair
`((f, 1) : P ⊕ -Q ⟶ Q, (δφ, φ ⊕ -φ'))` with `δφ : f φ f^* ≃ φ'` [Ran89, 3.10]. -/
@[simps]
def cylinder : SymPair J N where
  bd := P.sum Q.neg b
  D := Q.C
  pD := Q.p
  pD_idem := Q.p_idem
  support := Q.support.mono le_rfl (by omega)
  j := e.cylJ b
  j_kar := e.cylJ_kar b
  δφ := e.cylδφ b
  δφ_kar r r' := by rw [cylδφ_hom, e.cylHomotopy_kar]
  symm := e.isSymmHomotopy_cylδφ b
  poincare := e.cyl_poincare b _

include e in
/-- Homotopy-isometric complexes are cobordant: `P ⊕ -Q` bounds the cylinder. -/
theorem nullCobordant_sum_neg : NullCobordant (P.sum Q.neg b) :=
  ⟨e.cylinder b, rfl⟩

include e in
theorem cobordant (b : ∀ r, UnitaryBicone J (P.C.X r) (Q.C.X r)) : Cobordant P Q :=
  ⟨b, e.nullCobordant_sum_neg _⟩

end SymPoincare.HomotopyIsometry

namespace SymPoincare

variable [Linear ℚ V] [HasBinaryBiproducts V]

/-- `P ⊕ -P` is null-cobordant (the cylinder of the identity). -/
theorem nullCobordant_sum_neg_self (P : SymPoincare J N)
    (b : ∀ r, BinaryBicone (P.C.X r) (P.C.X r)) :
    NullCobordant (P.sum P.neg b) :=
  (HomotopyIsometry.refl P).nullCobordant_sum_neg b

/-- `P` is cobordant to itself. -/
theorem cobordant_refl (P : SymPoincare J N) (b : ∀ r, UnitaryBicone J (P.C.X r) (P.C.X r)) :
    Cobordant P P :=
  (HomotopyIsometry.refl P).cobordant b

theorem Isometric.cobordant {P Q : SymPoincare J N} (h : Isometric P Q)
    (b : ∀ r, UnitaryBicone J (P.C.X r) (Q.C.X r)) : Cobordant P Q :=
  h.some.cobordant b

end SymPoincare

end

end HSFormal.LTheory
