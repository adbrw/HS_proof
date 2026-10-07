import HSFormal.LTheory.BoundaryPoincare
import HSFormal.LTheory.LocalizationSupport

/-!
# Lifting Poincaré pairs to full subcategories (cubical module C8, support categories)

The cut steps of Lemma 11.2 need Poincaré pairs over the support categories `𝒜_A(X)`, the full
subcategories of `𝒜(X)` of objects supported in `A`; the pairs are built in `𝒜(X)`.  Here a
pair with identity idempotents all of whose objects lie in a full additive subcategory `U` is
lifted to `U` (`SymPair.liftSub`): the relative duality map is reflected along the inclusion
through the cone comparison of `SymPair.map`.  Homotopy isometries lift as well
(`SymPoincare.HomotopyIsometry.lift`).
-/

noncomputable section

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression
  homotopyCofiber

universe u

variable {A : InvCat} {U : ObjectProperty A} [IsAdditiveSub U]

local notation "ι" => (A.subIncl U : A.sub U ⟶ A)

/-- The inclusion of a full subcategory reflects homotopy equivalences. -/
def homotopyEquivLift {K L : ChainComplex U.FullSubcategory ℤ}
    (e : HomotopyEquiv ((U.ι.mapHomologicalComplex _).obj K) ((U.ι.mapHomologicalComplex _).obj L)) :
    HomotopyEquiv K L where
  hom := liftHom e.hom
  inv := liftHom e.inv
  homotopyHomInvId := liftHomotopy (homotopyCongr e.homotopyHomInvId rfl rfl)
  homotopyInvHomId := liftHomotopy (homotopyCongr e.homotopyInvHomId rfl rfl)

omit [IsAdditiveSub U] in
theorem isKarEquiv_of_map {K L : ChainComplex U.FullSubcategory ℤ} (f : K ⟶ L)
    (h : IsKarEquiv (𝟙 _) (𝟙 _) ((U.ι.mapHomologicalComplex _).map f)) :
    IsKarEquiv (𝟙 K) (𝟙 L) f := by
  obtain ⟨e, he⟩ := (isKarEquiv_id_iff _).mp h
  refine (isKarEquiv_id_iff _).mpr ⟨homotopyEquivLift e, ?_⟩
  ext r
  exact congrArg (fun g ↦ g.f r) he

variable {N : ℤ}

/-- **Lifting a Poincaré pair** with identity idempotents whose objects all lie in `U`. -/
def SymPair.liftSub (X : SymPair A.inv N) (hp : X.bd.p = 𝟙 _) (hpD : X.pD = 𝟙 _)
    (hC : ∀ r, U (X.bd.C.X r)) (hD : ∀ r, U (X.D.X r)) : SymPair (A.sub U).inv N where
  bd := X.bd.lift hC
  D := liftComplex U X.D hD
  pD := 𝟙 _
  pD_idem := by simp
  support r hr := ObjectProperty.hom_ext _ (by
    have := X.support r hr
    rw [hpD] at this
    exact this)
  j := liftHom (K := liftComplex U X.bd.C hC) (L := liftComplex U X.D hD) X.j
  j_kar := by
    ext r
    apply ObjectProperty.hom_ext
    simp only [SymPoincare.lift, hp, comp_f, liftHom_f, id_f, Category.comp_id]
    change 𝟙 _ ≫ X.j.f r = X.j.f r
    exact Category.id_comp _
  δφ := liftHomotopy (homotopyCongr X.δφ rfl rfl)
  δφ_kar r r' := ObjectProperty.hom_ext _ (by
    have := X.δφ_kar r r'
    rw [hpD, dualHom_id] at this
    simpa using this)
  symm := by
    have hs := X.symm
    rw [IsSymmHomotopy, transposeHomotopy_hom] at hs ⊢
    funext r r'
    have h := congrFun (congrFun hs r) r'
    refine ObjectProperty.hom_ext _ ?_
    simp only [transposeHomFamily] at h ⊢
    erw [ObjectProperty.units_smul_hom, ObjectProperty.FullSubcategory.comp_hom, bidual_hom_f,
      ObjectProperty.units_smul_hom, ObjectProperty.eqToHom_hom]
    simp only [bidual_hom_f] at h
    exact h
  poincare := by
    have hp' : (X.bd.lift hC).p = 𝟙 _ := by
      ext r
      change X.bd.p.f r = 𝟙 (X.bd.C.X r)
      rw [hp]; rfl
    simp only [hp']
    erw [coneMap_id, dualHom_id]
    apply isKarEquiv_of_map
    have hX := X.poincare
    simp only [hp, hpD, coneMap_id, dualHom_id] at hX
    have e₂ := (A.subIncl U).dualHom_coneComparison_comp_relDuality
      (liftHomotopy (homotopyCongr X.δφ rfl rfl) :
        Homotopy (dualHom (A.sub U).inv N (liftHom (K := liftComplex U X.bd.C hC)
          (L := liftComplex U X.D hD) X.j) ≫ (X.bd.lift hC).φ ≫
            liftHom (K := liftComplex U X.bd.C hC) (L := liftComplex U X.D hD) X.j) 0)
    have e₃ : (A.subIncl U).mapRel (liftHomotopy (homotopyCongr X.δφ rfl rfl) :
        Homotopy (dualHom (A.sub U).inv N (liftHom (K := liftComplex U X.bd.C hC)
          (L := liftComplex U X.D hD) X.j) ≫ (X.bd.lift hC).φ ≫
            liftHom (K := liftComplex U X.bd.C hC) (L := liftComplex U X.D hD) X.j) 0) =
        X.δφ := by
      ext r r'
      erw [InvFunctor.mapRel_hom]
      rfl
    rw [e₃] at e₂
    have e₅ : (A.subIncl U).mapH (relDuality (liftHomotopy (homotopyCongr X.δφ rfl rfl) :
        Homotopy (dualHom (A.sub U).inv N (liftHom (K := liftComplex U X.bd.C hC)
          (L := liftComplex U X.D hD) X.j) ≫ (X.bd.lift hC).φ ≫
            liftHom (K := liftComplex U X.bd.C hC) (L := liftComplex U X.D hD) X.j) 0)) =
        ((A.subIncl U).mapDualIso (N + 1) _).hom ≫
          dualHom A.inv (N + 1) ((A.subIncl U).coneComparison _) ≫ relDuality X.δφ := by
      erw [e₂, InvFunctor.mapDual_eq, Iso.hom_inv_id_assoc]
    change IsKarEquiv _ _ ((A.subIncl U).mapH _)
    erw [e₅]
    haveI : IsIso (dualHom A.inv (N + 1) ((A.subIncl U).coneComparison (liftHom
        (K := liftComplex U X.bd.C hC) (L := liftComplex U X.D hD) X.j))) :=
      inferInstanceAs (IsIso (LTheory.dualIso A.inv (N + 1)
        (asIso ((A.subIncl U).coneComparison _))).hom)
    exact (@IsKarEquiv.of_isIso _ _ _ _ _ _ (Iso.isIso_hom _)).comp
      ((IsKarEquiv.of_isIso _).comp hX (Category.id_comp _)
      (Category.id_comp _) (Category.id_comp _)) (Category.id_comp _) (Category.id_comp _)
      (Category.id_comp _)

variable (X : SymPair A.inv N) (hp : X.bd.p = 𝟙 _) (hpD : X.pD = 𝟙 _)
  (hC : ∀ r, U (X.bd.C.X r)) (hD : ∀ r, U (X.D.X r))

@[simp] theorem SymPair.liftSub_bd : (X.liftSub hp hpD hC hD).bd = X.bd.lift hC := rfl
@[simp] theorem SymPair.liftSub_pD : (X.liftSub hp hpD hC hD).pD = 𝟙 _ := rfl

theorem SymPair.liftSub_top (r : ℤ) : ((X.liftSub hp hpD hC hD).top r).hom = X.top r := by
  simp only [SymPair.top, relTop, SymPair.liftSub, XIsoOfEq, eqToIso.hom]
  erw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.eqToHom_hom]
  · rfl
  · exact congrArg _ (by omega)

theorem SymPair.liftSub_map_top (r : ℤ) :
    ((X.liftSub hp hpD hC hD).map (A.subIncl U)).top r = X.top r := by
  rw [SymPair.map_top]
  exact X.liftSub_top hp hpD hC hD r

/-- **R3 for a lifted pair** (exterior form): the excision isometry of `isometric_toQuot_of_split`
for the image in `A` of a pair lifted to `U`. -/
theorem SymPair.isometric_toQuot_liftSub (F : KaroubiFiltration A)
    (hU : ∀ r, F.U (((X.liftSub hp hpD hC hD).map (A.subIncl U)).bd.C.X r))
    (P : SymPoincare A.inv (N + 1)) (i : X.D ⟶ P.C) (hP : P.p = 𝟙 _)
    (t : ∀ r, P.C.X r ⟶ X.D.X r) (ht : ∀ r, i.f r ≫ t r = 𝟙 _)
    (hc : ∀ r, FactorsThrough F.U (𝟙 _ - t r ≫ i.f r))
    (hcap : ∀ r, FactorsThrough F.U ((dualHom A.inv (N + 1) i).f r ≫ X.top r ≫ i.f r - P.φ.f r)) :
    SymPoincare.Isometric (((X.liftSub hp hpD hC hD).map (A.subIncl U)).toQuot F hU)
      (P.map F.proj) := by
  refine SymPair.isometric_toQuot_of_split F _ hU P i ?_ hP t ht hc fun r ↦ ?_
  · ext r; rfl
  · rw [SymPair.liftSub_map_top]
    exact hcap r

/-- **R3 for a lifted pair inside a full subcategory** (Mayer–Vietoris form): pair lifted to
`U₁ ⊆ U₂`, closed complex lifted to `U₃ ⊆ U₂`, the filtration `F` restricted to `U₂`; all
hypotheses in `A`. -/
theorem SymPair.isometric_toQuot_liftSub_sub {U₂ U₃ : ObjectProperty A} [IsAdditiveSub U₂]
    [U₂.IsStableUnderRetracts] [IsAdditiveSub U₃] (h₁₂ : ∀ x, U x → U₂ x)
    (h₃₂ : ∀ x, U₃ x → U₂ x) (F : KaroubiFiltration A) (hF : ∀ x, F.U x → U₂ x)
    (hU : ∀ r, (F.restrict U₂).U
      (((X.liftSub hp hpD hC hD).map (A.subMap h₁₂)).bd.C.X r))
    (P : SymPoincare A.inv (N + 1)) (hP₃ : ∀ r, U₃ (P.C.X r)) (i : X.D ⟶ P.C) (hP : P.p = 𝟙 _)
    (t : ∀ r, P.C.X r ⟶ X.D.X r) (ht : ∀ r, i.f r ≫ t r = 𝟙 _)
    (hc : ∀ r, FactorsThrough F.U (𝟙 _ - t r ≫ i.f r))
    (hcap : ∀ r, FactorsThrough F.U ((dualHom A.inv (N + 1) i).f r ≫ X.top r ≫ i.f r - P.φ.f r)) :
    SymPoincare.Isometric (((X.liftSub hp hpD hC hD).map (A.subMap h₁₂)).toQuot (F.restrict U₂) hU)
      (((P.lift hP₃).map (A.subMap h₃₂)).map (F.restrict U₂).proj) := by
  refine SymPair.isometric_toQuot_of_split (F.restrict U₂) _ hU _
    (liftHom (K := ((X.liftSub hp hpD hC hD).map (A.subMap h₁₂)).D)
      (L := ((P.lift hP₃).map (A.subMap h₃₂)).C) i) ?_ ?_ (fun r ↦ ObjectProperty.homMk (t r))
    (fun r ↦ ObjectProperty.hom_ext _ (ht r)) (fun r ↦ ?_) (fun r ↦ ?_)
  · ext r; rfl
  · ext r
    apply ObjectProperty.hom_ext
    change P.p.f r = 𝟙 _
    rw [hP]; rfl
  · rw [KaroubiFiltration.factorsThrough_restrict_iff F hF]
    exact hc r
  · rw [KaroubiFiltration.factorsThrough_restrict_iff F hF]
    refine (congrArg (FactorsThrough F.U) ?_).mpr (hcap r)
    have hT : (((X.liftSub hp hpD hC hD).map (A.subMap h₁₂)).top r).hom = X.top r := by
      rw [SymPair.map_top]; exact X.liftSub_top hp hpD hC hD r
    change (dualHom A.inv (N + 1) i).f r ≫
      (((X.liftSub hp hpD hC hD).map (A.subMap h₁₂)).top r).hom ≫ i.f r - P.φ.f r = _
    rw [hT]
    rfl

namespace SymPoincare

variable {P Q : SymPoincare A.inv N} (hP : ∀ r, U (P.C.X r)) (hQ : ∀ r, U (Q.C.X r))

/-- Homotopy isometries lift to full subcategories. -/
def HomotopyIsometry.lift (e : HomotopyIsometry P Q) : HomotopyIsometry (P.lift hP) (Q.lift hQ) where
  f := liftHom (K := liftComplex U P.C hP) (L := liftComplex U Q.C hQ) e.f
  g := liftHom (K := liftComplex U Q.C hQ) (L := liftComplex U P.C hP) e.g
  f_kar := by ext r; exact congrArg (fun g ↦ g.f r) e.f_kar
  g_kar := by ext r; exact congrArg (fun g ↦ g.f r) e.g_kar
  fg := liftHomotopy (homotopyCongr e.fg rfl rfl)
  gf := liftHomotopy (homotopyCongr e.gf rfl rfl)
  conj := liftHomotopy (homotopyCongr e.conj rfl rfl)

omit [IsAdditiveSub U] in
theorem Isometric.lift (h : Isometric P Q) : Isometric (P.lift hP) (Q.lift hQ) :=
  ⟨h.some.lift hP hQ⟩

end SymPoincare

end HSFormal.LTheory
