import HSFormal.LTheory.SymmetricComplex

/-!
# Functoriality and homotopy isometries of symmetric Poincaré complexes (L-theory module M1)

Duality-preserving functors `InvFunctor` and the image `SymPoincare.map` of a Poincaré complex,
and homotopy isometries `(C, φ) ≃ (C', φ')` (the hypothesis of [Ran89, 3.10]): Kar-homotopy
equivalences `f` with `f φ f^* ≃ φ'`.  Homotopy isometry is an equivalence relation, compatible
with negation and functors; direct sums commute with functors up to isometry.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression

noncomputable section

universe v v' v'' u u' u''

variable {V : Type u} [Category.{v} V] [Preadditive V] (J : StrictInvolution V) (N : ℤ)

section InvFunctor

variable {W : Type u'} [Category.{v'} W] [Preadditive W] {W' : Type u''} [Category.{v''} W']
  [Preadditive W']

/-- A strictly duality-preserving additive functor between categories with object-fixing strict
involutions. -/
structure InvFunctor (J' : StrictInvolution W) where
  F : V ⥤ W
  [additive : F.Additive]
  map_star : ∀ {X Y : V} (f : X ⟶ Y), F.map (J.star f) = J'.star (F.map f)

attribute [instance] InvFunctor.additive

namespace InvFunctor

variable {J N} {J' : StrictInvolution W} {J'' : StrictInvolution W'}

variable (J) in
/-- The identity functor. -/
@[simps]
def id : InvFunctor J J where
  F := 𝟭 V
  map_star _ := rfl

/-- Composition of duality-preserving functors. -/
@[simps]
def comp (Φ : InvFunctor J J') (Ψ : InvFunctor J' J'') : InvFunctor J J'' where
  F := Φ.F ⋙ Ψ.F
  map_star f := by simp [Φ.map_star, Ψ.map_star]

variable (Φ : InvFunctor J J')

/-- The image of a complex. -/
abbrev mapC (C : ChainComplex V ℤ) : ChainComplex W ℤ :=
  (Φ.F.mapHomologicalComplex _).obj C

/-- The image of a chain map. -/
abbrev mapH {C D : ChainComplex V ℤ} (f : C ⟶ D) : Φ.mapC C ⟶ Φ.mapC D :=
  (Φ.F.mapHomologicalComplex _).map f

variable (N)

/-- `F(C^{N-*}) = (FC)^{N-*}`, with identity components. -/
def mapDualIso (C : ChainComplex V ℤ) : Φ.mapC (dualComplex J N C) ≅ dualComplex J' N (Φ.mapC C) :=
  Hom.isoOfComponents (fun _ ↦ Iso.refl _) (fun r r' _ ↦ by simp [Φ.map_star])

@[simp]
lemma mapDualIso_hom_f (C : ChainComplex V ℤ) (r : ℤ) : (Φ.mapDualIso N C).hom.f r = 𝟙 _ := rfl

@[simp]
lemma mapDualIso_inv_f (C : ChainComplex V ℤ) (r : ℤ) : (Φ.mapDualIso N C).inv.f r = 𝟙 _ := rfl

variable {N}

/-- `F φ : (FC)^{N-*} ⟶ FD` for `φ : C^{N-*} ⟶ D`, componentwise `F φ_r`. -/
@[simps]
def mapDual {C D : ChainComplex V ℤ} (φ : dualComplex J N C ⟶ D) :
    dualComplex J' N (Φ.mapC C) ⟶ Φ.mapC D where
  f r := Φ.F.map (φ.f r)
  comm' r r' h := by simpa using ((Φ.mapDualIso N C).inv ≫ Φ.mapH φ).comm r r'

/-- `F ψ : FC ⟶ (FD)^{N-*}` for `ψ : C ⟶ D^{N-*}`, componentwise `F ψ_r`. -/
@[simps]
def mapToDual {C D : ChainComplex V ℤ} (ψ : C ⟶ dualComplex J N D) :
    Φ.mapC C ⟶ dualComplex J' N (Φ.mapC D) where
  f r := Φ.F.map (ψ.f r)
  comm' r r' h := by simpa using (Φ.mapH ψ ≫ (Φ.mapDualIso N D).hom).comm r r'

variable {C D : ChainComplex V ℤ}

lemma mapDual_eq (φ : dualComplex J N C ⟶ D) :
    Φ.mapDual φ = (Φ.mapDualIso N C).inv ≫ Φ.mapH φ := by
  ext; simp

lemma mapToDual_eq (ψ : C ⟶ dualComplex J N D) :
    Φ.mapToDual ψ = Φ.mapH ψ ≫ (Φ.mapDualIso N D).hom := by
  ext; simp

lemma dualHom_mapH (f : C ⟶ D) :
    dualHom J' N (Φ.mapH f) = (Φ.mapDualIso N D).inv ≫ Φ.mapH (dualHom J N f) ≫
      (Φ.mapDualIso N C).hom := by
  ext; simp [Φ.map_star]

lemma transposeHom_mapDual (φ : dualComplex J N C ⟶ D) :
    transposeHom J' N (Φ.mapDual φ) = Φ.mapDual (transposeHom J N φ) := by
  ext r; simp [transposeHom_f, Φ.map_star, eqToHom_map]

end InvFunctor

namespace SymPoincare

variable {J N} {J' : StrictInvolution W} (Φ : InvFunctor J J')

/-- The image `F(C, φ) = (FC, Fφ)` of a Poincaré complex under a duality-preserving functor. -/
@[simps, reducible]
def map (P : SymPoincare J N) : SymPoincare J' N where
  C := Φ.mapC P.C
  p := Φ.mapH P.p
  p_idem := by rw [← Functor.map_comp, P.p_idem]
  support r hr := by simp [P.support r hr]
  φ := Φ.mapDual P.φ
  φ_kar := by
    rw [Φ.mapDual_eq, Φ.dualHom_mapH]
    simp only [assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, P.φ_kar]
  symm := by rw [IsStrictSymm, Φ.transposeHom_mapDual, P.symm]
  poincare := by
    obtain ⟨ψ, hψ, ⟨H₁⟩, ⟨H₂⟩⟩ := P.poincare
    refine ⟨Φ.mapToDual ψ, ?_, ⟨homotopyCongr (Φ.F.mapHomotopy H₁) ?_ rfl⟩,
      ⟨homotopyCongr (((Φ.F.mapHomotopy H₂).compLeft (Φ.mapDualIso N P.C).inv).compRight
        (Φ.mapDualIso N P.C).hom) ?_ ?_⟩⟩
    · rw [Φ.mapToDual_eq, Φ.dualHom_mapH]
      simp only [assoc, Iso.hom_inv_id_assoc]
      rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, assoc, hψ]
    · rw [Φ.mapToDual_eq, Φ.mapDual_eq]
      simp only [assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp]
    · rw [Φ.mapToDual_eq, Φ.mapDual_eq]
      simp only [assoc, ← Functor.map_comp_assoc]
    · rw [Φ.dualHom_mapH, assoc]

@[simp]
lemma map_id (P : SymPoincare J N) : P.map (InvFunctor.id J) = P := rfl

lemma map_comp {J'' : StrictInvolution W'}
    (Ψ : InvFunctor J' J'') (P : SymPoincare J N) : P.map (Φ.comp Ψ) = (P.map Φ).map Ψ := rfl

@[simp]
lemma map_neg (P : SymPoincare J N) : P.neg.map Φ = (P.map Φ).neg := by
  cases P
  simp only [map, neg]
  congr 1
  ext; simp

end SymPoincare

end InvFunctor

section Isometry

variable {J N} {W : Type u'} [Category.{v'} W] [Preadditive W] {J' : StrictInvolution W}

/-- Conjugation `f φ f^*` respects homotopies in both arguments. -/
def conjHomotopy {C C' : ChainComplex V ℤ} {f f' : C ⟶ C'} {φ φ' : dualComplex J N C ⟶ C}
    (Hf : Homotopy f f') (Hφ : Homotopy φ φ') :
    Homotopy (dualHom J N f ≫ φ ≫ f) (dualHom J N f' ≫ φ' ≫ f') :=
  (dualHomotopy J N Hf).comp (Hφ.comp Hf)

namespace SymPoincare

/-- A homotopy isometry `(C, p, φ) ≃ (C', p', φ')`, the hypothesis of [Ran89, 3.10]: a homotopy
equivalence `f : (C, p) ⟶ (C', p')` in `Kar V` with `f φ f^* ≃ φ'`.  By `exists_symm_homotopy`
the last homotopy may be taken symmetric over `ℚ`, so this is Ranicki's `f^%(φ) = φ' ∈ Q^N(C')`. -/
structure HomotopyIsometry (P Q : SymPoincare J N) where
  f : P.C ⟶ Q.C
  g : Q.C ⟶ P.C
  f_kar : P.p ≫ f ≫ Q.p = f
  g_kar : Q.p ≫ g ≫ P.p = g
  fg : Homotopy (f ≫ g) P.p
  gf : Homotopy (g ≫ f) Q.p
  conj : Homotopy (dualHom J N f ≫ P.φ ≫ f) Q.φ

namespace HomotopyIsometry

variable {P Q R : SymPoincare J N} (e : HomotopyIsometry P Q)

@[reassoc (attr := simp)]
lemma p_comp_f : P.p ≫ e.f = e.f := by rw [← e.f_kar]; simp

@[reassoc (attr := simp)]
lemma f_comp_p : e.f ≫ Q.p = e.f := by rw [← e.f_kar]; simp

@[reassoc (attr := simp)]
lemma p_comp_g : Q.p ≫ e.g = e.g := by rw [← e.g_kar]; simp

@[reassoc (attr := simp)]
lemma g_comp_p : e.g ≫ P.p = e.g := by rw [← e.g_kar]; simp

/-- The identity isometry. -/
@[simps]
def refl (P : SymPoincare J N) : HomotopyIsometry P P where
  f := P.p
  g := P.p
  f_kar := by simp
  g_kar := by simp
  fg := Homotopy.ofEq P.p_idem
  gf := Homotopy.ofEq P.p_idem
  conj := Homotopy.ofEq P.φ_kar

/-- The inverse isometry: `g φ' g^* ≃ (gf) φ (gf)^* ≃ φ`. -/
@[simps]
def symm : HomotopyIsometry Q P where
  f := e.g
  g := e.f
  f_kar := e.g_kar
  g_kar := e.f_kar
  fg := e.gf
  gf := e.fg
  conj := (conjHomotopy (Homotopy.refl e.g) e.conj.symm).trans
    (homotopyCongr (conjHomotopy e.fg (Homotopy.refl P.φ)) (by simp) P.φ_kar)

/-- Composition of isometries. -/
@[simps]
def trans (e' : HomotopyIsometry Q R) : HomotopyIsometry P R where
  f := e.f ≫ e'.f
  g := e'.g ≫ e.g
  f_kar := by simp
  g_kar := by simp
  fg := (homotopyCongr ((Homotopy.refl e.f).comp (e'.fg.comp (Homotopy.refl e.g))) (by simp)
    (by simp)).trans e.fg
  gf := (homotopyCongr ((Homotopy.refl e'.g).comp (e.gf.comp (Homotopy.refl e'.f))) (by simp)
    (by simp)).trans e'.gf
  conj := (homotopyCongr (conjHomotopy (Homotopy.refl e'.f) e.conj) (by simp) rfl).trans e'.conj

/-- A strict isomorphism `e : C ≅ C'` with `e p = p' e` and `e φ e^* = φ'`. -/
def ofIso (e : P.C ≅ Q.C) (hp : e.hom ≫ Q.p = P.p ≫ e.hom)
    (hφ : dualHom J N e.hom ≫ P.φ ≫ e.hom = Q.φ) : HomotopyIsometry P Q :=
  have hinv : e.inv ≫ P.p = Q.p ≫ e.inv := by
    rw [← cancel_epi e.hom, e.hom_inv_id_assoc, reassoc_of% hp, e.hom_inv_id, comp_id]
  { f := P.p ≫ e.hom
    g := Q.p ≫ e.inv
    f_kar := by simp [hp]
    g_kar := by simp [hinv]
    fg := Homotopy.ofEq (by simp [reassoc_of% hp])
    gf := Homotopy.ofEq (by simp [reassoc_of% hinv])
    conj := Homotopy.ofEq (by simp [hφ]) }

/-- An isometry `P ≃ Q` gives `-P ≃ -Q`. -/
@[simps]
def neg : HomotopyIsometry P.neg Q.neg where
  f := e.f
  g := e.g
  f_kar := e.f_kar
  g_kar := e.g_kar
  fg := e.fg
  gf := e.gf
  conj := homotopyCongr (e.conj.smul (-1 : ℤ)) (by simp) (by simp)

/-- The image of an isometry under a duality-preserving functor. -/
@[simps]
def map (Φ : InvFunctor J J') : HomotopyIsometry (P.map Φ) (Q.map Φ) where
  f := Φ.mapH e.f
  g := Φ.mapH e.g
  f_kar := by simp only [map_p, ← Functor.map_comp, e.f_kar]
  g_kar := by simp only [map_p, ← Functor.map_comp, e.g_kar]
  fg := homotopyCongr (Φ.F.mapHomotopy e.fg) (Functor.map_comp _ _ _) rfl
  gf := homotopyCongr (Φ.F.mapHomotopy e.gf) (Functor.map_comp _ _ _) rfl
  conj := homotopyCongr ((Φ.F.mapHomotopy e.conj).compLeft (Φ.mapDualIso N Q.C).inv)
    (by rw [Φ.dualHom_mapH, map_φ, Φ.mapDual_eq]; simp) (by rw [map_φ, Φ.mapDual_eq])

end HomotopyIsometry

/-- `P` and `Q` are homotopy isometric. -/
def Isometric (P Q : SymPoincare J N) : Prop :=
  Nonempty (HomotopyIsometry P Q)

theorem isometric_equivalence : Equivalence (Isometric (J := J) (N := N)) :=
  ⟨fun P ↦ ⟨.refl P⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ ↦ ⟨e.trans e'⟩⟩

/-- Functors commute with direct sums up to a strict isometry. -/
def mapSum (Φ : InvFunctor J J') (P Q : SymPoincare J N)
    (b : ∀ r, BinaryBicone (P.C.X r) (Q.C.X r)) :
    HomotopyIsometry ((P.sum Q b).map Φ)
      ((P.map Φ).sum (Q.map Φ) fun r ↦ Φ.F.mapBinaryBicone (b r)) :=
  .ofIso (Hom.isoOfComponents (fun _ ↦ Iso.refl _) (fun r r' _ ↦ by
      simp [sum]; erw [Category.id_comp, Category.comp_id]; rfl))
    (by ext; simp [sum]; repeat erw [Category.id_comp]
        repeat erw [Category.comp_id]
        rfl)
    (by ext; simp [sum, Φ.map_star]; erw [J'.star_id]; repeat erw [Category.id_comp]
        repeat erw [Category.comp_id]
        rfl)

end SymPoincare

/-- The image of a unitary bicone under a duality-preserving functor. -/
@[simps toBinaryBicone]
def UnitaryBicone.map (Φ : InvFunctor J J') {X Y : V} (b : UnitaryBicone J X Y) :
    UnitaryBicone J' (Φ.F.obj X) (Φ.F.obj Y) where
  toBinaryBicone := Φ.F.mapBinaryBicone b.toBinaryBicone
  isBilimit := isBinaryBilimitOfTotal _ (by
    have : Φ.F.map b.fst ≫ Φ.F.map b.inl + Φ.F.map b.snd ≫ Φ.F.map b.inr = 𝟙 (Φ.F.obj b.pt) := by
      rw [← Φ.F.map_comp, ← Φ.F.map_comp, ← Φ.F.map_add, IsBilimit.binary_total b.isBilimit,
        Φ.F.map_id]
    exact this)
  star_inl := (Φ.map_star b.inl).symm.trans (congrArg Φ.F.map b.star_inl)
  star_inr := (Φ.map_star b.inr).symm.trans (congrArg Φ.F.map b.star_inr)

end Isometry

end

end HSFormal.LTheory
