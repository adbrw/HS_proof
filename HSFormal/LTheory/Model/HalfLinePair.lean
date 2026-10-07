import HSFormal.LTheory.Model.HalfLineData

/-!
# The half-line Poincaré pair (half-line splitting, part 3)

For half-line data `H` (`Model/HalfLineData.lean`) and an `N`-dimensional Poincaré complex
`Q = (C, p, φ)` over `A`, `H.pair Q : PairOn (Q.map H.O)` is the `(N+1)`-dimensional Poincaré pair
`(j : OC ⟶ H.cx C, (δφ, φ_O))` with

* `j = j_C ∘ H(p)` (the boundary vertex), `p_D = H(p)`;
* `δφ` with top components `T_{1/2,1/2} ≫ H(φ)` (`δφ = δH ≫ H(φ)`), strictly symmetric by the
  transposition law `T_transpose` (`T_{a,b}^t = T_{b,a}`), naturality and `Tφ = φ`;
* Poincaré duality: `Ψ = c^* (Θ_{1/2,1/2} ≫ H(φ))` (`relDuality_pair`) for the strict Kar
  isomorphism `c = (p, H(p)) : Cone(j_C) ⟶ Cone(j)`, and `Θ_{1/2,1/2} ≃ Θ_{1,0}` is an isomorphism
  (`ΘIso`), natural in `C`.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression
  homotopyCofiber

noncomputable section

/-! ### Symmetric relative boundaries from their top components -/

section SymmTop

universe v u

variable {V : Type u} [Category.{v} V] [Preadditive V] {J : StrictInvolution V} {N : ℤ}
  {B D : ChainComplex V ℤ} {j : B ⟶ D} {φ : dualComplex J N B ⟶ B}

lemma homotopy_hom_XIsoOfEq_right {K L : ChainComplex V ℤ} {f g : K ⟶ L} (H : Homotopy f g)
    (a : ℤ) {b b' : ℤ} (h : b = b') : H.hom a b ≫ (L.XIsoOfEq h).hom = H.hom a b' := by
  subst h; simp

/-- A relative boundary whose top components are `(N+1)`-transpose-invariant is symmetric. -/
lemma isSymmHomotopy_of_relTop (H : Homotopy (dualHom J N j ≫ φ ≫ j) 0)
    (h : ∀ r, J.star (relTop H (N + 1 - r)) ≫ (bidual J (N + 1) D).hom.f r = relTop H r) :
    IsSymmHomotopy J N H := by
  rw [IsSymmHomotopy, transposeHomotopy_hom]
  funext r r'
  by_cases hr : (ComplexShape.down ℤ).Rel r' r
  · obtain rfl : r' = r + 1 := by simp only [ComplexShape.down_Rel] at hr; omega
    have h₁ := h (r + 1)
    rw [relTop_eq H r (r + 1) rfl, relTop_eq H (N - (r + 1)) (N + 1 - (r + 1)) (by omega),
      ← homotopy_hom_XIsoOfEq_right H (N - (r + 1)) (show N - r = N + 1 - (r + 1) by omega)] at h₁
    simp only [J.star_comp, star_XIsoOfEq_hom, bidual_hom_f, assoc] at h₁
    rw [transposeHomFamily, bidual_hom_f]
    rw [← cancel_epi (D.XIsoOfEq (show N + 1 - (r + 1) = N - r by omega)).hom, ← h₁]
    simp only [Linear.comp_units_smul, smul_smul, XIsoOfEq_inv_eq,
      ← Int.negOnePow_add]
    congr 1
    · exact negOnePow_eq_of_eq 0 (by ring)
    · simp [XIsoOfEq]
  · rw [transposeHomFamily, H.zero r r' hr, H.zero (N - r') (N - r)
      (by simp only [ComplexShape.down_Rel] at hr ⊢; omega)]
    simp

end SymmTop

namespace HalfLineData

variable {A B : InvCat} (H : HalfLineData A B) (a b : ℚ) (M : ℤ)

/-- **The transposition law of `T`**: `T_{a,b}^t = T_{b,a}` (the analogue of
`LineData.θ_transpose`). -/
lemma T_transpose (C : ChainComplex A ℤ) (r : ℤ) :
    B.inv.star (H.T a b M C (M + 1 - r)) ≫ (bidual B.inv (M + 1) (H.cx C)).hom.f r =
      H.T b a M (dualComplex A.inv M C) r ≫ (H.map (bidual A.inv M C).hom).f r := by
  apply cone.ext_star (J := B.inv) (H.g (dualComplex A.inv M C)) _ _ (down_rel_sub M r)
  all_goals apply ext_to_X (H.g C) r (r - 1) (by simp)
  all_goals simp only [T, bidual_hom_f, B.inv.star_add, B.inv.star_comp,
    B.inv.star_units_smul, B.inv.star_star, star_rat_smul, Linear.units_smul_comp,
    Linear.comp_units_smul, assoc, add_comp, Linear.smul_comp]
  all_goals simp (disch := down_rel) only [inrX_eqToHom'_assoc, inlX_eqToHom'_assoc,
    InvFunctor.mapC_dual_XIsoOfEq']
  all_goals half_simp
  · rw [show (r * (M + 1 - r)).negOnePow = r.negOnePow * (r * (M - r)).negOnePow by
      rw [← Int.negOnePow_add]; congr 1; ring]
    simp only [mul_smul]
    abel
  · have e : (r * (M + 1 - r)).negOnePow * (M + 1 - r).negOnePow =
        ((r - 1) * (M - (r - 1))).negOnePow := by
      rw [← Int.negOnePow_add]; exact negOnePow_eq_of_eq (M + 1 - r) (by ring)
    simp only [smul_smul, e]
    abel

/-- Naturality of the homotopy `δH`. -/
lemma δH_hom_natural (hab : a + b = 1) {C D : ChainComplex A ℤ} (f : C ⟶ D) (r r' : ℤ) :
    (dualHom B.inv M (H.map f)).f r ≫ (H.δH a b M hab C).hom r r' =
      (H.δH a b M hab D).hom r r' ≫ (H.map (dualHom A.inv M f)).f r' := by
  simp only [δH, homotopyOfTop, dualHom_f]
  split_ifs with h
  · rw [star_f_XIsoOfEq_assoc, T_natural, assoc]
  · simp

/-- `H(f)` is a Kar equivalence if `f` is. -/
lemma isKarEquiv_map {C D : ChainComplex A ℤ} {e : C ⟶ C} {e' : D ⟶ D} {f : C ⟶ D}
    (h : IsKarEquiv e e' f) : IsKarEquiv (H.map e) (H.map e') (H.map f) := by
  obtain ⟨g, hg, ⟨H₁⟩, ⟨H₂⟩⟩ := h
  exact ⟨H.map g, by rw [← map_comp, ← map_comp, hg],
    ⟨homotopyCongr (H.htpy H₁) (map_comp _ _ _) rfl⟩,
    ⟨homotopyCongr (H.htpy H₂) (map_comp _ _ _) rfl⟩⟩

/-! ### The half-line pair -/

variable {N : ℤ} (Q : SymPoincare A.inv N)

lemma half_add_half : (1 / 2 : ℚ) + 1 / 2 = 1 := by norm_num

/-- The relative structure on the honest boundary vertex `j_C`. -/
def δφ₀ : Homotopy (dualHom B.inv N (H.jC Q.C) ≫ (Q.map H.O).φ ≫ H.jC Q.C) 0 :=
  homotopyCongr ((H.δH (1 / 2) (1 / 2) N half_add_half Q.C).compRight (H.map Q.φ))
    (by
      rw [bdF, assoc, assoc, ← H.jC_natural Q.φ, SymPoincare.map_φ, InvFunctor.mapDual_eq,
        assoc])
    (by simp)

/-- The boundary inclusion of the pair, `j = j_C ∘ H(p)`. -/
abbrev jP : (Q.map H.O).C ⟶ H.cx Q.C := H.jC Q.C ≫ H.map Q.p

lemma jC_map_p : H.jC Q.C ≫ H.map Q.p = H.O.mapH Q.p ≫ H.jC Q.C := (H.jC_natural Q.p).symm

lemma conj_jP : dualHom B.inv N (H.jP Q) ≫ (Q.map H.O).φ ≫ H.jP Q =
    dualHom B.inv N (H.jC Q.C) ≫ (Q.map H.O).φ ≫ H.jC Q.C := by
  rw [jP, jC_map_p, dualHom_comp, assoc, ← assoc (Q.map H.O).φ]
  have := (Q.map H.O).φ_kar
  simp only [SymPoincare.map_p] at this
  rw [← assoc (dualHom B.inv N (H.O.mapH Q.p)), ← assoc (dualHom B.inv N (H.O.mapH Q.p)),
    assoc (dualHom B.inv N (H.O.mapH Q.p)), this]

/-- **The relative structure of the half-line pair**, `δφ = δH ≫ H(φ)`. -/
def δφ : Homotopy (dualHom B.inv N (H.jP Q) ≫ (Q.map H.O).φ ≫ H.jP Q) 0 :=
  homotopyCongr (H.δφ₀ Q) (H.conj_jP Q).symm rfl

lemma δφ_hom (r r' : ℤ) :
    (H.δφ Q).hom r r' = (H.δH (1 / 2) (1 / 2) N half_add_half Q.C).hom r r' ≫
        (H.map Q.φ).f r' := rfl

lemma relTop_δφ (r : ℤ) :
    relTop (H.δφ Q) r = H.T (1 / 2) (1 / 2) N Q.C r ≫ (H.map Q.φ).f r := by
  rw [← relTopH_δH H (1 / 2) (1 / 2) N half_add_half Q.C r]
  simp only [relTop, relTopH, δφ_hom, assoc]

lemma δφ_kar (r r' : ℤ) : (dualHom B.inv N (H.map Q.p)).f r ≫ (H.δφ Q).hom r r' ≫
    (H.map Q.p).f r' = (H.δφ Q).hom r r' := by
  rw [δφ_hom]
  simp only [assoc]
  rw [reassoc_of% (H.δH_hom_natural (1 / 2) (1 / 2) N half_add_half Q.p r r'), ← comp_f,
    ← comp_f, ← map_comp, ← map_comp, Q.φ_kar]

lemma δφ_symm : IsSymmHomotopy B.inv N (H.δφ Q) := by
  refine isSymmHomotopy_of_relTop _ fun r ↦ ?_
  rw [relTop_δφ, relTop_δφ, B.inv.star_comp, assoc, T_transpose, ← assoc, T_natural, assoc,
    ← comp_f, ← map_comp, ← transposeHom, Q.transposeHom_φ]

/-! ### Poincaré duality of the half-line pair -/

lemma Op_jP : H.O.mapH Q.p ≫ H.jP Q = H.jC Q.C ≫ H.map Q.p := by
  rw [jP, ← assoc, ← jC_map_p, assoc, ← map_comp, Q.p_idem]

lemma Op_jC : H.O.mapH Q.p ≫ H.jC Q.C = H.jP Q ≫ H.map Q.p := by
  rw [jP, assoc, ← map_comp, Q.p_idem, jC_map_p]

/-- The idempotent `(p, H(p))` of `Cone(j_C)`. -/
abbrev coneIdemC : cone (H.jC Q.C) ⟶ cone (H.jC Q.C) :=
  coneMap (H.O.mapH Q.p) (H.map Q.p) (H.jC_natural Q.p)

/-- The idempotent `(p, H(p))` of `Cone(j)` (the Kar idempotent of the pair's cone). -/
abbrev coneIdemP : cone (H.jP Q) ⟶ cone (H.jP Q) :=
  coneMap (H.O.mapH Q.p) (H.map Q.p) (comm_of_kar (Q.map H.O).p_idem
    (by rw [← map_comp, Q.p_idem]) (by rw [← assoc, Op_jP, assoc, ← map_comp, Q.p_idem]))

lemma Op_idem : H.O.mapH Q.p ≫ H.O.mapH Q.p = H.O.mapH Q.p := by
  rw [← Functor.map_comp, Q.p_idem]

lemma mapp_idem : H.map Q.p ≫ H.map Q.p = H.map Q.p := by rw [← map_comp, Q.p_idem]

lemma coneIdemC_idem : H.coneIdemC Q ≫ H.coneIdemC Q = H.coneIdemC Q :=
  coneMap_idem _ (H.Op_idem Q) (H.mapp_idem Q)

lemma coneIdemP_idem : H.coneIdemP Q ≫ H.coneIdemP Q = H.coneIdemP Q :=
  coneMap_idem _ (H.Op_idem Q) (H.mapp_idem Q)

/-- The strict Kar isomorphism `Cone(j_C) ⟶ Cone(j)`. -/
abbrev coneCP : cone (H.jC Q.C) ⟶ cone (H.jP Q) := coneMap (H.O.mapH Q.p) (H.map Q.p) (H.Op_jP Q)

/-- Its inverse `Cone(j) ⟶ Cone(j_C)`. -/
abbrev conePC : cone (H.jP Q) ⟶ cone (H.jC Q.C) := coneMap (H.O.mapH Q.p) (H.map Q.p) (H.Op_jC Q)

lemma isKarEquiv_coneCP : IsKarEquiv (H.coneIdemC Q) (H.coneIdemP Q) (H.coneCP Q) := by
  refine ⟨H.conePC Q, ?_, ⟨Homotopy.ofEq ?_⟩, ⟨Homotopy.ofEq ?_⟩⟩
  · simp only [coneMap_comp, H.Op_idem, H.mapp_idem]
  · simp only [coneMap_comp, H.Op_idem, H.mapp_idem]
  · simp only [coneMap_comp, H.Op_idem, H.mapp_idem]

/-- **The relative duality map of the half-line pair**: `Ψ = c^* (Θ_{1/2,1/2} ≫ H(φ))`. -/
lemma relDuality_pair : relDuality (H.δφ Q) = dualHom B.inv (N + 1) (H.coneCP Q) ≫
    H.Θ (1 / 2) (1 / 2) N half_add_half Q.C ≫ H.map Q.φ := by
  refine relDuality_eq_relDualityH (H.δH (1 / 2) (1 / 2) N half_add_half Q.C) (H.δφ Q)
    (H.O.mapH Q.p) (H.map Q.p) (H.Op_jP Q) (H.map Q.φ) (fun r ↦ ?_) (fun r ↦ ?_)
  · rw [relTopH_δH, relTop_δφ, T_natural_assoc, ← comp_f, ← map_comp,
      SymPoincare.dualHom_p_comp_φ]
  · have h₁ : A.inv.star (Q.p.f (N - r)) ≫ Q.φ.f r = Q.φ.f r := by
      rw [← dualHom_f, ← comp_f, Q.dualHom_p_comp_φ]
    have h₂ : Q.φ.f r ≫ Q.p.f r = Q.φ.f r := by rw [← comp_f, Q.φ_comp_p]
    simp only [InvFunctor.mapDualIso_inv_f, jC_f, assoc, inrX_map,
      Functor.mapHomologicalComplex_map_f, SymPoincare.map_φ, InvFunctor.mapDual_f, comp_f]
    erw [id_comp]
    rw [← InvNat.app_star_map_assoc, ← H.V.map_star, ← Functor.map_comp_assoc, h₁,
      ← InvNat.app_map_assoc, ← Functor.map_comp_assoc, h₂]

lemma isKarEquiv_Θ1 : IsKarEquiv (dualHom B.inv (N + 1) (H.coneIdemC Q))
    (H.map (dualHom A.inv N Q.p)) (H.Θ 1 0 N one_add_zero Q.C) := by
  have hn := H.Θ_natural 1 0 N one_add_zero Q.p
  have hinv : (H.ΘIso N Q.C).inv ≫ dualHom B.inv (N + 1) (H.coneIdemC Q) =
      H.map (dualHom A.inv N Q.p) ≫ (H.ΘIso N Q.C).inv := by
    rw [Iso.inv_comp_eq, ← assoc, Iso.eq_comp_inv, ΘIso_hom]
    exact hn
  have hp : H.map (dualHom A.inv N Q.p) ≫ H.map (dualHom A.inv N Q.p) =
      H.map (dualHom A.inv N Q.p) := by rw [← map_comp, ← dualHom_comp, Q.p_idem]
  refine ⟨H.map (dualHom A.inv N Q.p) ≫ (H.ΘIso N Q.C).inv, ?_, ⟨Homotopy.ofEq ?_⟩,
    ⟨Homotopy.ofEq ?_⟩⟩
  · rw [assoc, hinv, reassoc_of% hp, reassoc_of% hp]
  · rw [assoc, ← ΘIso_hom, Iso.inv_hom_id, comp_id]
  · rw [← assoc, ← hn, assoc, ← ΘIso_hom, Iso.hom_inv_id, comp_id]

lemma isKarEquiv_Θs : IsKarEquiv (dualHom B.inv (N + 1) (H.coneIdemC Q))
    (H.map (dualHom A.inv N Q.p)) (H.Θ (1 / 2) (1 / 2) N half_add_half Q.C) :=
  (H.isKarEquiv_Θ1 Q).of_homotopy (H.ΘHtpy (1 / 2) (1 / 2) N half_add_half Q.C).symm

lemma poincare_pair :
    IsKarEquiv (dualHom B.inv (N + 1) (H.coneIdemP Q)) (H.map Q.p) (relDuality (H.δφ Q)) := by
  have hp' : H.map (dualHom A.inv N Q.p) ≫ H.map (dualHom A.inv N Q.p) =
      H.map (dualHom A.inv N Q.p) := by rw [← map_comp, ← dualHom_comp, Q.p_idem]
  rw [relDuality_pair]
  exact (H.isKarEquiv_coneCP Q).dualHom.comp ((H.isKarEquiv_Θs Q).comp
    (H.isKarEquiv_map Q.poincare) (dualHom_idem (H.coneIdemC_idem Q)) hp' (H.mapp_idem Q))
    (dualHom_idem (H.coneIdemP_idem Q)) (dualHom_idem (H.coneIdemC_idem Q)) (H.mapp_idem Q)

/-- **The half-line Poincaré pair** of `Q`, with boundary `Q` placed at the boundary point. -/
def pair : PairOn (Q.map H.O) where
  D := H.cx Q.C
  pD := H.map Q.p
  pD_idem := H.mapp_idem Q
  support := by simpa using H.map_supportedIn Q.support
  j := H.jP Q
  j_kar := by
    change H.O.mapH Q.p ≫ H.jP Q ≫ H.map Q.p = H.jP Q
    rw [← assoc, Op_jP, assoc, ← map_comp, Q.p_idem]
  δφ := H.δφ Q
  δφ_kar := H.δφ_kar Q
  symm := H.δφ_symm Q
  poincare := H.poincare_pair Q

@[simp] lemma pair_D : (H.pair Q).D = H.cx Q.C := rfl
@[simp] lemma pair_pD : (H.pair Q).pD = H.map Q.p := rfl
@[simp] lemma pair_j : (H.pair Q).j = H.jC Q.C ≫ H.map Q.p := rfl
lemma pair_δφ_hom (r r' : ℤ) : (H.pair Q).δφ.hom r r' =
    (H.δH (1 / 2) (1 / 2) N half_add_half Q.C).hom r r' ≫ (H.map Q.φ).f r' := rfl

end HalfLineData

end

end HSFormal.LTheory
