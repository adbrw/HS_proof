import HSFormal.LTheory.Model.LinePairs
import HSFormal.LTheory.Model.CZFiltration

/-!
# Naturality of the line construction (lower L-theory model, module 5)

A morphism of line data `h : L ⟶ L'` over duality-preserving functors `Φ : A ⟶ A'`,
`Ψ : B ⟶ B'` is a unitary natural isomorphism `η : Δ ≫ Ψ ≅ Φ ≫ Δ'` intertwining the shifts.
The comparison `h.cmp C : (ΦC) ⊗ ℝ ≅ Ψ(C ⊗ ℝ)` (`η⁻¹` on both cone summands followed by the
cone comparison of `Ψ`) intertwines `θ` (`map_θ`) and the line homotopies (`cmp_htpy`), so
`(ΦP) ⊗ ℝ ≃ Ψ(P ⊗ ℝ)` (`symMapIsometry`) and the transfer is natural (`transfer_map`).

**Signs.**  For a pair `X` whose boundary is killed by `Φ`, closing up `Ψ(X ⊗ ℝ)` gives
`-((ΦX closed up) ⊗ ℝ)` (`pairClosedIsometry`; the sign `t_N = -1` comes from `htpy_relTop`),
while `(X ⊗ ℝ).bd = X.bd ⊗ ℝ` on the nose (`s_N = +1`).

For `C_ℤ`, `CZ.lineHom Φ` has `Ψ = CZ.map Φ` and `η = 1`, whence `Lconc.tensorLine_map`; for a
Karoubi filtration `F`, `CZ.pair_toQuot`/`CZ.cls_pair_toQuot`:
`[(X ⊗ ℝ)/C_ℤ(U)] = -[(X/U) ⊗ ℝ]` under `C_ℤ(A)/C_ℤ(U) ≅ C_ℤ(A/U)`.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression
  homotopyCofiber

noncomputable section

attribute [local implicit_reducible] SymPair.closedOfIsZero SymPair.map LineData.pair

/-! ### Additive functors and cones -/

section FunctorCone

variable {V W : Type*} [Category V] [Preadditive V] [HasBinaryBiproducts V] [Category W]
  [Preadditive W] [HasBinaryBiproducts W] (F : V ⥤ W) [F.Additive]
  {K L' : ChainComplex V ℤ} (φ : K ⟶ L')

lemma ext_from_functor_cone {i k : ℤ} (h : (ComplexShape.down ℤ).Rel i k) {Z : W}
    {f g : F.obj ((homotopyCofiber φ).X i) ⟶ Z}
    (h₁ : F.map (inlX φ k i h) ≫ f = F.map (inlX φ k i h) ≫ g)
    (h₂ : F.map (inrX φ i) ≫ f = F.map (inrX φ i) ≫ g) : f = g := by
  have e (x : F.obj ((homotopyCofiber φ).X i) ⟶ Z) : x = F.map (fstX φ i k h) ≫
      F.map (inlX φ k i h) ≫ x + F.map (sndX φ i) ≫ F.map (inrX φ i) ≫ x := by
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, ← add_comp, ← Functor.map_add,
      ← cone.id_X]
    simp
  rw [e f, e g, h₁, h₂]

lemma ext_to_functor_cone {i k : ℤ} (h : (ComplexShape.down ℤ).Rel i k) {Z : W}
    {f g : Z ⟶ F.obj ((homotopyCofiber φ).X i)}
    (h₁ : f ≫ F.map (fstX φ i k h) = g ≫ F.map (fstX φ i k h))
    (h₂ : f ≫ F.map (sndX φ i) = g ≫ F.map (sndX φ i)) : f = g := by
  have e (x : Z ⟶ F.obj ((homotopyCofiber φ).X i)) : x = x ≫ F.map (fstX φ i k h) ≫
      F.map (inlX φ k i h) + x ≫ F.map (sndX φ i) ≫ F.map (inrX φ i) := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← comp_add, ← Functor.map_add, ← cone.id_X]
    simp
  rw [e f, e g, reassoc_of% h₁, reassoc_of% h₂]

variable (J : StrictInvolution V)

/-- Maps out of `F(Cone_i)` are determined by `F(fstX^*)`, `F(sndX^*)`. -/
lemma ext_from_functor_cone_star {i k : ℤ} (h : (ComplexShape.down ℤ).Rel i k) {Z : W}
    {f g : F.obj ((homotopyCofiber φ).X i) ⟶ Z}
    (h₁ : F.map (J.star (fstX φ i k h)) ≫ f = F.map (J.star (fstX φ i k h)) ≫ g)
    (h₂ : F.map (J.star (sndX φ i)) ≫ f = F.map (J.star (sndX φ i)) ≫ g) : f = g := by
  have e (x : F.obj ((homotopyCofiber φ).X i) ⟶ Z) : x = F.map (J.star (inlX φ k i h)) ≫
      F.map (J.star (fstX φ i k h)) ≫ x + F.map (J.star (inrX φ i)) ≫
        F.map (J.star (sndX φ i)) ≫ x := by
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, ← add_comp, ← Functor.map_add,
      ← J.star_comp, ← J.star_comp, ← J.star_add, ← cone.id_X]
    simp
  rw [e f, e g, h₁, h₂]

end FunctorCone

section ConeComparison

variable {V W : Type*} [Category V] [Preadditive V] [HasBinaryBiproducts V] [Category W]
  [Preadditive W] [HasBinaryBiproducts W] {J : StrictInvolution V} {J' : StrictInvolution W}
  (Ψ : InvFunctor J J') {K L' : ChainComplex V ℤ} (φ : K ⟶ L')

@[reassoc (attr := simp)]
lemma coneComparison_f_map_fstX {i k : ℤ} (hk : (ComplexShape.down ℤ).Rel i k) :
    (Ψ.coneComparison φ).f i ≫ Ψ.F.map (fstX φ i k hk) = fstX (Ψ.mapH φ) i k hk := by
  apply ext_from_X (Ψ.mapH φ) k i hk <;>
    simp [← Functor.map_comp]

@[reassoc (attr := simp)]
lemma coneComparison_f_map_sndX (i : ℤ) :
    (Ψ.coneComparison φ).f i ≫ Ψ.F.map (sndX φ i) = sndX (Ψ.mapH φ) i := by
  apply ext_from_X (Ψ.mapH φ) (i - 1) i (by simp) <;>
    simp [← Functor.map_comp]

end ConeComparison

/-! ### Morphisms of line data -/

namespace LineData

variable {A B A' B' : InvCat}

/-- A morphism of line data over `Φ : A ⟶ A'`, `Ψ : B ⟶ B'`: a unitary natural isomorphism
`η : Δ ≫ Ψ ≅ Φ ≫ Δ'` intertwining the shifts. -/
structure Hom (L : LineData A B) (L' : LineData A' B') where
  /-- The functor on coefficients. -/
  Φ : A ⟶ A'
  /-- The functor on the line categories. -/
  Ψ : B ⟶ B'
  /-- The comparison of the line functors. -/
  η : InvCat.UnitaryIso (L.Δ ≫ Ψ) (Φ ≫ L'.Δ)
  s_comm : ∀ X, Ψ.F.map (L.s.iso.hom.app X) ≫ η.iso.hom.app X =
    η.iso.hom.app X ≫ L'.s.iso.hom.app (Φ.F.obj X)

namespace Hom

variable {L : LineData A B} {L' : LineData A' B'} (h : Hom L L')

/-- `η`. -/
abbrev ηh (X : A) : h.Ψ.F.obj (L.Δ.F.obj X) ⟶ L'.Δ.F.obj (h.Φ.F.obj X) := h.η.iso.hom.app X

/-- `η⁻¹`. -/
abbrev ηi (X : A) : L'.Δ.F.obj (h.Φ.F.obj X) ⟶ h.Ψ.F.obj (L.Δ.F.obj X) := h.η.iso.inv.app X

@[reassoc (attr := simp)]
lemma ηh_ηi (X : A) : h.ηh X ≫ h.ηi X = 𝟙 _ := h.η.iso.hom_inv_id_app X

@[reassoc (attr := simp)]
lemma ηi_ηh (X : A) : h.ηi X ≫ h.ηh X = 𝟙 _ := h.η.iso.inv_hom_id_app X

/-- `s_comm` with the objects of `ηh` (`Ψ(ΔX)`, `Δ'(ΦX)`): on v4.35 rewriting with `s_comm` does
not match these, since `(Δ ≫ Ψ).F.obj X` is not reducibly `Ψ.F.obj (Δ.F.obj X)`. -/
@[reassoc]
lemma s_comm' (X : A) : h.Ψ.F.map (L.s.iso.hom.app X) ≫ h.ηh X =
    h.ηh X ≫ L'.s.iso.hom.app (h.Φ.F.obj X) := h.s_comm X

instance (X : A) : IsIso (h.ηh X) := ⟨⟨h.ηi X, h.ηh_ηi X, h.ηi_ηh X⟩⟩

instance (X : A) : IsIso (h.ηi X) := ⟨⟨h.ηh X, h.ηi_ηh X, h.ηh_ηi X⟩⟩

@[simp]
lemma star_ηh (X : A) : B'.inv.star (h.ηh X) = h.ηi X := h.η.star_hom X

@[simp]
lemma star_ηi (X : A) : B'.inv.star (h.ηi X) = h.ηh X := h.η.star_inv X

@[reassoc]
lemma ηi_map {X Y : A} (f : X ⟶ Y) :
    h.ηi X ≫ h.Ψ.F.map (L.Δ.F.map f) = L'.Δ.F.map (h.Φ.F.map f) ≫ h.ηi Y :=
  (h.η.iso.inv.naturality f).symm

@[reassoc]
lemma map_ηh {X Y : A} (f : X ⟶ Y) :
    h.Ψ.F.map (L.Δ.F.map f) ≫ h.ηh Y = h.ηh X ≫ L'.Δ.F.map (h.Φ.F.map f) :=
  h.η.iso.hom.naturality f

@[reassoc]
lemma ηi_s_hom (X : A) :
    h.ηi X ≫ h.Ψ.F.map (L.s.iso.hom.app X) = L'.s.iso.hom.app (h.Φ.F.obj X) ≫ h.ηi X := by
  rw [← cancel_mono (h.ηh X), assoc, h.s_comm', ηi_ηh_assoc, assoc, ηi_ηh, comp_id]

@[reassoc]
lemma ηi_s_inv (X : A) :
    h.ηi X ≫ h.Ψ.F.map (L.s.iso.inv.app X) = L'.s.iso.inv.app (h.Φ.F.obj X) ≫ h.ηi X := by
  rw [← cancel_epi (L'.s.iso.hom.app (h.Φ.F.obj X)), ← ηi_s_hom_assoc, ← Functor.map_comp,
    s_hom_inv, CategoryTheory.Functor.map_id, comp_id, s_hom_inv_assoc]

variable (C : ChainComplex A ℤ)

/-- `η⁻¹ : Δ'(ΦC) ⟶ Ψ(ΔC)`. -/
@[simps]
def ηC : L'.Δ.mapC (h.Φ.mapC C) ⟶ h.Ψ.mapC (L.Δ.mapC C) where
  f i := h.ηi (C.X i)
  comm' i j _ := by
    simp only [InvFunctor.mapC, Functor.mapHomologicalComplex_obj_d]
    exact h.ηi_map (C.d i j)

/-- `η : Ψ(ΔC) ⟶ Δ'(ΦC)`. -/
@[simps]
def ηC' : h.Ψ.mapC (L.Δ.mapC C) ⟶ L'.Δ.mapC (h.Φ.mapC C) where
  f i := h.ηh (C.X i)
  comm' i j _ := by
    simp only [InvFunctor.mapC, Functor.mapHomologicalComplex_obj_d]
    exact (h.map_ηh (C.d i j)).symm

lemma ηC_comp_g : h.ηC C ≫ h.Ψ.mapH (L.g C) = L'.g (h.Φ.mapC C) ≫ h.ηC C := by
  ext i
  simp [Functor.map_sub, ηi_s_hom, sub_comp, comp_sub]

lemma ηC'_comp_g : h.ηC' C ≫ L'.g (h.Φ.mapC C) = h.Ψ.mapH (L.g C) ≫ h.ηC' C := by
  ext i
  simp [Functor.map_sub, h.s_comm', sub_comp, comp_sub]

/-- **The comparison** `(ΦC) ⊗ ℝ ⟶ Ψ(C ⊗ ℝ)`. -/
def cmp : L'.cx (h.Φ.mapC C) ⟶ h.Ψ.mapC (L.cx C) :=
  coneMap (h.ηC C) (h.ηC C) (h.ηC_comp_g C) ≫ h.Ψ.coneComparison (L.g C)

instance : IsIso (h.cmp C) := by
  have : IsIso (coneMap (h.ηC C) (h.ηC C) (h.ηC_comp_g C)) :=
    ⟨coneMap (h.ηC' C) (h.ηC' C) (h.ηC'_comp_g C), by
      rw [coneMap_comp, ← coneMap_id]; congr 1 <;> ext <;> simp, by
      rw [coneMap_comp, ← coneMap_id]; congr 1 <;> ext <;> simp⟩
  rw [cmp]; infer_instance

variable {C}

@[reassoc (attr := simp)]
lemma inlX_cmp {i k : ℤ} (hk : (ComplexShape.down ℤ).Rel i k) :
    inlX (L'.g (h.Φ.mapC C)) k i hk ≫ (h.cmp C).f i =
      h.ηi (C.X k) ≫ h.Ψ.F.map (inlX (L.g C) k i hk) := by
  simp [cmp]

@[reassoc (attr := simp)]
lemma inrX_cmp (i : ℤ) :
    inrX (L'.g (h.Φ.mapC C)) i ≫ (h.cmp C).f i = h.ηi (C.X i) ≫ h.Ψ.F.map (inrX (L.g C) i) := by
  simp [cmp]

@[reassoc (attr := simp)]
lemma cmp_map_fstX {i k : ℤ} (hk : (ComplexShape.down ℤ).Rel i k) :
    (h.cmp C).f i ≫ h.Ψ.F.map (fstX (L.g C) i k hk) =
      fstX (L'.g (h.Φ.mapC C)) i k hk ≫ h.ηi (C.X k) := by
  simp [cmp]

@[reassoc (attr := simp)]
lemma cmp_map_sndX (i : ℤ) :
    (h.cmp C).f i ≫ h.Ψ.F.map (sndX (L.g C) i) = sndX (L'.g (h.Φ.mapC C)) i ≫ h.ηi (C.X i) := by
  simp [cmp]

/-- Naturality of the comparison. -/
lemma cmp_natural {D : ChainComplex A ℤ} (f : C ⟶ D) :
    h.cmp C ≫ h.Ψ.mapH (L.map f) = L'.map (h.Φ.mapH f) ≫ h.cmp D := by
  ext i
  apply ext_from_X (L'.g (h.Φ.mapC C)) (i - 1) i (by simp)
  all_goals apply ext_to_functor_cone h.Ψ.F (L.g D) (k := i - 1) (by simp)
  all_goals simp [← Functor.map_comp, ηi_map_assoc]
  all_goals exact h.ηi_map _

section Theta

lemma _root_.HSFormal.LTheory.InvFunctor.map_rat_smul' {X Y : B} (q : ℚ) (f : X ⟶ Y) :
    h.Ψ.F.map (q • f) = q • h.Ψ.F.map f :=
  map_rat_smul (h.Ψ.F.mapAddHom : (X ⟶ Y) →+ _) q f

lemma map_rat_smul {X Y : B} (q : ℚ) (f : X ⟶ Y) : h.Ψ.F.map (q • f) = q • h.Ψ.F.map f :=
  _root_.map_rat_smul (h.Ψ.F.mapAddHom : (X ⟶ Y) →+ _) q f

@[reassoc]
lemma ηh_s_hom (X : A) :
    h.ηh X ≫ L'.s.iso.hom.app (h.Φ.F.obj X) = h.Ψ.F.map (L.s.iso.hom.app X) ≫ h.ηh X :=
  (h.s_comm X).symm

@[reassoc]
lemma ηh_s_inv (X : A) :
    h.ηh X ≫ L'.s.iso.inv.app (h.Φ.F.obj X) = h.Ψ.F.map (L.s.iso.inv.app X) ≫ h.ηh X := by
  have := h.ηi_s_inv X
  rw [← cancel_epi (h.ηi X), ηi_ηh_assoc, reassoc_of% this, ηi_ηh, comp_id]

@[reassoc]
lemma ηh_map {X Y : A} (f : X ⟶ Y) :
    h.ηh X ≫ L'.Δ.F.map (h.Φ.F.map f) = h.Ψ.F.map (L.Δ.F.map f) ≫ h.ηh Y :=
  (h.map_ηh f).symm

lemma mapC_XIsoOfEq_hom' {V W : Type*} [Category V] [Preadditive V] [Category W]
    [Preadditive W] (F : V ⥤ W) [F.Additive] (C : ChainComplex V ℤ) {a b : ℤ} (hab : a = b) :
    (((F.mapHomologicalComplex _).obj C).XIsoOfEq hab).hom = F.map (C.XIsoOfEq hab).hom := by
  subst hab; simp

@[reassoc]
lemma star_map_fstX_star_cmp (C : ChainComplex A ℤ) {i k : ℤ}
    (hk : (ComplexShape.down ℤ).Rel i k) :
    h.Ψ.F.map (B.inv.star (fstX (L.g C) i k hk)) ≫ B'.inv.star ((h.cmp C).f i) =
      h.ηh (C.X k) ≫ B'.inv.star (fstX (L'.g (h.Φ.mapC C)) i k hk) := by
  rw [h.Ψ.map_star, ← B'.inv.star_comp, cmp_map_fstX, B'.inv.star_comp, star_ηi]

@[reassoc]
lemma star_map_sndX_star_cmp (C : ChainComplex A ℤ) (i : ℤ) :
    h.Ψ.F.map (B.inv.star (sndX (L.g C) i)) ≫ B'.inv.star ((h.cmp C).f i) =
      h.ηh (C.X i) ≫ B'.inv.star (sndX (L'.g (h.Φ.mapC C)) i) := by
  rw [h.Ψ.map_star, ← B'.inv.star_comp, cmp_map_sndX, B'.inv.star_comp, star_ηi]

/-- `Ψ` carries `θ` to `θ'`. -/
lemma map_θ (a b : ℚ) (M : ℤ) (C : ChainComplex A ℤ) :
    h.Ψ.mapDual (L.θ a b M C) = dualHom B'.inv (M + 1) (h.cmp C) ≫ L'.θ a b M (h.Φ.mapC C) ≫
      L'.map (h.Φ.mapDualIso M C).inv ≫ h.cmp (dualComplex A.inv M C) := by
  ext r
  apply ext_from_functor_cone_star h.Ψ.F (L.g C) B.inv (down_rel_sub M r) <;>
    apply ext_to_functor_cone h.Ψ.F (L.g (dualComplex A.inv M C)) (k := r - 1) (by simp)
  all_goals simp only [InvFunctor.mapDual_f, comp_f, dualHom_f, θ_f, assoc,
    star_map_fstX_star_cmp_assoc, star_map_sndX_star_cmp_assoc, cmp_map_fstX, cmp_map_sndX,
    ← Functor.map_comp]
  all_goals line_simp
  all_goals simp only [Functor.map_add, Functor.map_neg, Functor.map_zero, Functor.map_units_smul,
    map_rat_smul, Functor.map_comp, comp_add, add_comp, assoc, Linear.comp_smul,
    Linear.smul_comp, Linear.comp_units_smul, Linear.units_smul_comp, comp_zero, zero_comp,
    add_zero, zero_add, ηh_s_hom_assoc, ηh_s_inv_assoc, ηh_map_assoc, ηh_s_hom, ηh_s_inv,
    ηh_map, mapC_XIsoOfEq_hom, mapC_XIsoOfEq_hom', InvFunctor.mapC, ηh_ηi_assoc, ηh_ηi,
    CategoryTheory.Functor.map_id, id_comp, comp_id, InvFunctor.mapDualIso_inv_f, cmp_map_fstX,
    cmp_map_sndX, inrX_map_assoc, inlX_map_assoc, Functor.mapHomologicalComplex_map_f]
  all_goals dsimp only [dualComplex_X, Functor.mapHomologicalComplex_obj_X]
  all_goals simp only [CategoryTheory.Functor.map_id, id_comp, ηh_s_hom_assoc, ηh_s_inv_assoc,
    ηh_ηi, comp_id]
  all_goals abel

end Theta

end Hom

lemma _root_.HSFormal.LTheory.InvFunctor.mapDual_comp_mapH {V W : Type*} [Category V] [Preadditive V]
    [Category W] [Preadditive W] {J : StrictInvolution V} {J' : StrictInvolution W}
    (Φ : InvFunctor J J') {N : ℤ} {C D E : ChainComplex V ℤ} (φ : dualComplex J N C ⟶ D)
    (g : D ⟶ E) : Φ.mapDual (φ ≫ g) = Φ.mapDual φ ≫ Φ.mapH g := by
  ext; simp

namespace Hom

variable {L : LineData A B} {L' : LineData A' B'} (h : Hom L L') {N : ℤ}

/-- **Naturality of `P ⊗ ℝ`**: `(ΦP) ⊗ ℝ ≃ Ψ(P ⊗ ℝ)`. -/
def symMapIsometry (P : SymPoincare A.inv N) :
    (L'.sym (P.map h.Φ)).HomotopyIsometry ((L.sym P).map h.Ψ) :=
  .ofIso (asIso (h.cmp P.C)) (by simpa using h.cmp_natural P.p) (by
    simp only [asIso_hom, sym_φ, SymPoincare.map_φ, InvFunctor.mapDual_comp_mapH, map_θ, assoc]
    rw [h.cmp_natural, ← map_comp_assoc, ← InvFunctor.mapDual_eq])

lemma cls_sym_map (P : SymPoincare A.inv N) :
    Lconc.cls (L'.sym (P.map h.Φ)) = Lconc.cls ((L.sym P).map h.Ψ) :=
  Lconc.cls_eq_of_isometry (h.symMapIsometry P)

/-- The transfer commutes with a morphism of line data. -/
lemma transfer_map (x : Lconc A N) :
    L'.transfer N (Lconc.map h.Φ x) = Lconc.map h.Ψ (L.transfer N x) := by
  obtain ⟨P, rfl⟩ := Lconc.cls_surjective x
  simp [h.cls_sym_map]

end Hom

end LineData

/-! ### Line pairs with vanishing boundary -/

namespace LineData

variable {A B : InvCat} (L : LineData A B)

/-- **The sign `t_N = -1`**: on a relative top `T = δφ_{*-1,*}`, the line structure of the pair
is minus the line structure of the closed complex. -/
lemma htpy_relTop {N : ℤ} {D : ChainComplex A ℤ} {f g : dualComplex A.inv N D ⟶ D}
    (H : Homotopy f g) (T : dualComplex A.inv (N + 1) D ⟶ D)
    (hT : ∀ r, T.f r = (D.XIsoOfEq (show N + 1 - r = N - (r - 1) by omega)).hom ≫ H.hom (r - 1) r)
    (r : ℤ) :
    ((L.cx D).XIsoOfEq (show N + 1 + 1 - r = N + 1 - (r - 1) by omega)).hom ≫
        (L.θs N D).f (r - 1) ≫ (L.htpy H).hom (r - 1) r =
      -((L.θs (N + 1) D).f r ≫ (L.map T).f r) := by
  apply cone.ext_star (J := B.inv) (L.g D) _ _ (down_rel_sub (N + 1) r) <;>
    apply ext_to_X (L.g D) r (r - 1) (by simp)
  all_goals simp only [θ_f, hT]
  all_goals pair_simp
  all_goals simp only [hT, XIsoOfEq_hom_comp_XIsoOfEq_hom_assoc]
  all_goals abel

end LineData

lemma isZero_cone_X {V : Type*} [Category V] [Preadditive V] [HasBinaryBiproducts V]
    {K L' : ChainComplex V ℤ} (φ : K ⟶ L') {i : ℤ} (hK : IsZero (K.X (i - 1)))
    (hL : IsZero (L'.X i)) : IsZero ((homotopyCofiber φ).X i) := by
  rw [IsZero.iff_id_eq_zero, cone.id_X φ i (i - 1) (by simp), hK.eq_of_tgt (fstX φ i (i - 1) _) 0,
    hL.eq_of_tgt (sndX φ i) 0, zero_comp, zero_comp, add_zero]

namespace LineData.Hom

variable {A B A' B' : InvCat} {L : LineData A B} {L' : LineData A' B'} (h : Hom L L')

lemma cmp_htpy {C D : ChainComplex A ℤ} {f g : C ⟶ D} (H : Homotopy f g) (i i' : ℤ) :
    (h.cmp C).f i ≫ h.Ψ.F.map ((L.htpy H).hom i i') =
      (L'.htpy (h.Φ.F.mapHomotopy H)).hom i i' ≫ (h.cmp D).f i' := by
  by_cases hi : (ComplexShape.down ℤ).Rel i' i
  · rw [htpy_hom_of_rel _ _ hi, htpy_hom_of_rel _ _ hi]
    apply ext_from_X (L'.g (h.Φ.mapC C)) (i - 1) i (by simp)
    all_goals apply ext_to_functor_cone h.Ψ.F (L.g D) (k := i' - 1) (by simp)
    all_goals simp [← Functor.map_comp, ηi_map_assoc]
    all_goals first | exact h.ηi_map _ |
      simp only [mapC_XIsoOfEq_hom, Functor.map_comp, ηi_map_assoc]
  · rw [htpy_hom_eq_zero _ _ hi, htpy_hom_eq_zero _ _ hi, Functor.map_zero, comp_zero, zero_comp]

@[reassoc]
lemma map_XIsoOfEq_star_cmp (D : ChainComplex A ℤ) {a a' : ℤ} (hh : a = a') :
    h.Ψ.F.map ((L.cx D).XIsoOfEq hh).hom ≫ B'.inv.star ((h.cmp D).f a') =
      B'.inv.star ((h.cmp D).f a) ≫ ((L'.cx (h.Φ.mapC D)).XIsoOfEq hh).hom := by
  subst hh; simp

@[reassoc]
lemma map_mapDualIso_inv_htpy {N : ℤ} {D : ChainComplex A ℤ} {f g : dualComplex A.inv N D ⟶ D}
    (H : Homotopy f g) (i i' : ℤ) :
    (L'.map (h.Φ.mapDualIso N D).inv).f i ≫ (L'.htpy (h.Φ.F.mapHomotopy H)).hom i i' =
      (L'.htpy (homotopyCongr ((h.Φ.F.mapHomotopy H).compLeft (h.Φ.mapDualIso N D).inv)
        (h.Φ.mapDual_eq f).symm (h.Φ.mapDual_eq g).symm)).hom i i' := by
  have := L'.htpy_comp_hom (h.Φ.F.mapHomotopy H) (h.Φ.mapDualIso N D).inv (𝟙 _) i i'
  rw [map_id, id_f] at this
  erw [comp_id] at this
  rw [this]
  exact congrFun (congrFun (L'.htpy_hom_congr (by ext; simp)) i) i'

lemma isZero_pair_bd {N : ℤ} (X : SymPair A.inv N)
    (hZ : ∀ r, IsZero (h.Φ.F.obj (X.bd.C.X r))) (r : ℤ) :
    IsZero (h.Ψ.F.obj ((L.pair X).bd.C.X r)) :=
  (isZero_cone_X (L'.g (h.Φ.mapC X.bd.C)) (L'.Δ.F.map_isZero (hZ (r - 1)))
    (L'.Δ.F.map_isZero (hZ r))).of_iso
      ((HomologicalComplex.eval _ _ r).mapIso (asIso (h.cmp X.bd.C))).symm

/-- **Line pairs with vanishing boundary** (the sign `t_N = -1`): if `Φ` kills the boundary of
`X`, then `Ψ(X ⊗ ℝ)` closed up is isometric to `-((ΦX closed up) ⊗ ℝ)`. -/
def pairClosedIsometry {N : ℤ} (X : SymPair A.inv N)
    (hZ : ∀ r, IsZero (h.Φ.F.obj (X.bd.C.X r))) :
    ((L'.sym (X.toClosed h.Φ hZ)).neg).HomotopyIsometry
      ((L.pair X).toClosed h.Ψ (h.isZero_pair_bd X hZ)) :=
  .ofIso (show L'.cx (h.Φ.mapC X.D) ≅ h.Ψ.mapC (L.cx X.D) from asIso (h.cmp X.D))
    (h.cmp_natural X.pD) (by
    ext r
    have e₁ := congrArg (fun φ ↦ φ.f (r - 1)) (h.map_θ (1 / 2) (1 / 2) N X.D)
    simp only [InvFunctor.mapDual_f, comp_f, dualHom_f] at e₁
    have e₂ := L'.htpy_relTop (X.map h.Φ).δφ (X.toClosed h.Φ hZ).φ (fun _ ↦ rfl) r
    simp only [comp_f, asIso_hom, SymPoincare.neg_φ, sym_φ, neg_comp, comp_neg, neg_f_apply,
      dualHom_f, SymPair.toClosed_φ_f]
    change _ = h.Ψ.F.map (((L.cx X.D).XIsoOfEq _).hom ≫ (L.θs N X.D).f (r - 1) ≫
      (L.htpy X.δφ).hom (r - 1) r)
    dsimp only [θs] at e₁ e₂ ⊢
    rw [Functor.map_comp, Functor.map_comp, e₁]
    simp only [assoc]
    rw [h.cmp_htpy, map_XIsoOfEq_star_cmp_assoc, map_mapDualIso_inv_htpy_assoc,
      congrFun (congrFun (L'.htpy_hom_congr (H' := (X.map h.Φ).δφ)
        (by ext; simp <;> exact Category.id_comp _)) _) _]
    erw [reassoc_of% e₂]
    simp only [neg_comp, comp_neg, assoc]
    rfl)

end LineData.Hom

/-! ### The line data morphisms of `C_ℤ` -/

namespace CZ

variable {A A' : InvCat} (Φ : A ⟶ A')

/-- `C_ℤ(Φ)` as a morphism of line data `C_ℤ(A) ⟶ C_ℤ(A')` (with `η = 1`). -/
def lineHom : LineData.Hom (lineData A) (lineData A') where
  Φ := Φ
  Ψ := CZ.map Φ
  η :=
    { iso := NatIso.ofComponents (fun X ↦ Iso.refl ((CZ.map Φ).F.obj ((const A).F.obj X)))
        fun {X Y} f ↦ by
          erw [comp_id, id_comp]
          exact map_diag Φ _
      star_hom := fun X ↦ involution.star_id _ }
  s_comm X := by
    dsimp only [NatIso.ofComponents_hom_app, Iso.refl_hom]
    erw [comp_id, id_comp]
    ext w v
    rw [map_map_apply, lineData_s_hom, shift_apply, lineData_s_hom, shift_apply]
    split_ifs <;> simp

@[simp] lemma lineHom_Φ : (lineHom Φ).Φ = Φ := rfl

@[simp] lemma lineHom_Ψ : (lineHom Φ).Ψ = CZ.map Φ := rfl

end CZ

/-- **Naturality of the transition map** in duality-preserving functors. -/
lemma Lconc.tensorLine_map {A A' : InvCat} (Φ : A ⟶ A') {N : ℤ} (x : Lconc A N) :
    Lconc.tensorLine A' N (Lconc.map Φ x) = Lconc.map (CZ.map Φ) (Lconc.tensorLine A N x) :=
  (CZ.lineHom Φ).transfer_map x

/-! ### Line pairs and quotients of `C_ℤ` -/

lemma cone_X_mem {V : Type*} [Category V] [Preadditive V] [HasBinaryBiproducts V]
    (U : ObjectProperty V) [IsAdditiveSub U] {K L' : ChainComplex V ℤ} (φ : K ⟶ L') {i : ℤ}
    (hK : U (K.X (i - 1))) (hL : U (L'.X i)) : U ((homotopyCofiber φ).X i) := by
  have hi : (ComplexShape.down ℤ).Rel i (i - 1) := by simp
  let b : BinaryBicone (K.X (i - 1)) (L'.X i) :=
    { pt := (homotopyCofiber φ).X i
      fst := fstX φ i (i - 1) hi
      snd := sndX φ i
      inl := inlX φ (i - 1) i hi
      inr := inrX φ i
      inl_fst := by simp
      inl_snd := by simp
      inr_fst := by simp
      inr_snd := by simp }
  exact IsAdditiveSub.biprod_mem b (isBinaryBilimitOfTotal _ (cone.id_X φ i (i - 1) hi).symm)
    hK hL

namespace CZ

variable {A : InvCat} (F : KaroubiFiltration A) {N : ℤ}

/-- The boundary of `X ⊗ ℝ` lies in `C_ℤ(U)` when the boundary of `X` lies in `U`. -/
lemma pair_bd_mem (X : SymPair A.inv N) (hU : ∀ r, F.U (X.bd.C.X r)) (r : ℤ) :
    F.cz.U (((lineData A).pair X).bd.C.X r) :=
  cone_X_mem F.cz.U _ (fun _ ↦ hU (r - 1)) (fun _ ↦ hU r)

/-- **`(X ⊗ ℝ)/U ≃ -((X/U) ⊗ ℝ)`** under `C_ℤ(A)/C_ℤ(U) ≅ C_ℤ(A/U)`: the boundary sign of
`X ⊗ ℝ` is `s_N = +1` (`LineData.pair_bd`, by definition) and the quotient sign is `t_N = -1`. -/
theorem pair_toQuot (X : SymPair A.inv N) (hU : ∀ r, F.U (X.bd.C.X r)) :
    SymPoincare.Isometric ((((lineData A).pair X).toQuot F.cz (pair_bd_mem F X hU)).map
      F.czQuotIso.hom) (((lineData F.quot).sym (X.toQuot F hU)).neg) := by
  rw [SymPair.toQuot, SymPair.toClosed_map ((lineData A).pair X) F.cz.proj _ F.czQuotIso.hom
    ((lineHom F.proj).isZero_pair_bd X fun r ↦ F.isZero_proj_obj (hU r) :)]
  exact ⟨((lineHom F.proj).pairClosedIsometry X fun r ↦ F.isZero_proj_obj (hU r)).symm⟩

/-- `t_N = -1` on classes: `[(X ⊗ ℝ)/U] = -[(X/U) ⊗ ℝ]`. -/
theorem cls_pair_toQuot (X : SymPair A.inv N) (hU : ∀ r, F.U (X.bd.C.X r)) :
    Lconc.cls ((((lineData A).pair X).toQuot F.cz (pair_bd_mem F X hU)).map F.czQuotIso.hom) =
      -Lconc.tensorLine F.quot (N + 1) (Lconc.cls (X.toQuot F hU)) := by
  rw [Lconc.cls_eq_of_isometric (pair_toQuot F X hU), Lconc.cls_neg, Lconc.tensorLine_cls]

end CZ

end

end HSFormal.LTheory
