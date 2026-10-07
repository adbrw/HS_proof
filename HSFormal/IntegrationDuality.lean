import HSFormal.GraphType
import HSFormal.TensorTriviality
import HSFormal.LTheory.KaroubiFiltration

/-!
# Duality-preserving structure of the asymptotic categories

Glue between `AsymptoticCategory`, `AsymptoticSupport`, `AsymptoticRelabel`, `GraphType`,
`TensorTriviality` (strict involutions on `𝒜_G(X)`, `𝒜_S(X)`, `ℬ_Z(X)`, `𝒜_A/𝒜_Y`, with
transpose-closure of `I_S`) and `LTheory.KaroubiFiltration` (`InvCat`s, where the same involutions
appear definitionally: `asymptoticInvolution_eq`, `exteriorInvCat_inv`).

* Lifts of additive and linear functors through quotients; zero objects and biproducts of
  quotients; the quotient of an `InvCat`.  `𝒜_A/𝒜_Y` has finite biproducts and is an `InvCat`
  (`supportQuotientInvCat`).
* The free-sheet functor `ℬ_{1,Z}(X) → ℬ_{G,Z}(X)` (l.849) is additive, `ℚ`-linear and strictly
  duality-preserving (`ExteriorCategory.freeSheetInv`); it is induced by a map of support
  filtrations (`freeSheetFiltrationHom`).
* Lemma 2.2(ii) (`excisionInv`, `excisionInvCatHom`) and Lemma 2.4 (`relabelInv`) are additive,
  `ℚ`-linear and strictly duality-preserving; uniformly continuous push-forward too
  (`pushTailInv`).
* `𝒜_S(X)` is replete (`supportProperty_of_iso`, from `IsAdditiveSub` in `KaroubiFiltration`).
-/

noncomputable section

namespace HSFormal

open Filter Matrix CategoryTheory CategoryTheory.Limits Metric LTheory Compression
open scoped Classical ENNReal Topology Pointwise

universe u v

/-! ### Generic quotients -/

namespace QuotientLift

variable {C : Type*} [Category C] [Preadditive C] {D : Type*} [Category D] [Preadditive D]
  {r : HomRel C} [Preadditive (CategoryTheory.Quotient r)]
  [(Quotient.functor r).Additive]

theorem additive (F : C ⥤ D) [F.Additive] (h : ∀ (x y : C) (f₁ f₂ : x ⟶ y), r f₁ f₂ →
    F.map f₁ = F.map f₂) : (CategoryTheory.Quotient.lift r F h).Additive where
  map_add {_ _ φ ψ} := by
    obtain ⟨f, rfl⟩ := (Quotient.functor r).map_surjective φ
    obtain ⟨g, rfl⟩ := (Quotient.functor r).map_surjective ψ
    rw [← Functor.map_add, Quotient.lift_map_functor_map, Quotient.lift_map_functor_map,
      Quotient.lift_map_functor_map, F.map_add]

omit [(Quotient.functor r).Additive] in
theorem linear (R : Type*) [Semiring R] [Linear R C] [Linear R D]
    [Linear R (CategoryTheory.Quotient r)]
    [(Quotient.functor r).Linear R] (F : C ⥤ D) [F.Linear R]
    (h : ∀ (x y : C) (f₁ f₂ : x ⟶ y), r f₁ f₂ → F.map f₁ = F.map f₂) :
    (CategoryTheory.Quotient.lift r F h).Linear R where
  map_smul {_ _} φ c := by
    obtain ⟨f, rfl⟩ := (Quotient.functor r).map_surjective φ
    rw [← Functor.map_smul, Quotient.lift_map_functor_map, Quotient.lift_map_functor_map,
      F.map_smul]

theorem hasZeroObject [HasZeroObject C] : HasZeroObject (CategoryTheory.Quotient r) :=
  ⟨⟨_, (Quotient.functor r).map_isZero (isZero_zero C)⟩⟩

theorem hasBinaryBiproducts [HasBinaryBiproducts C] :
    HasBinaryBiproducts (CategoryTheory.Quotient r) :=
  ⟨fun X Y ↦ HasBinaryBiproduct.mk ⟨(Quotient.functor r).mapBinaryBicone
    (BinaryBiproduct.bicone X.as Y.as), isBilimitMap _ (BinaryBiproduct.isBilimit _ _)⟩⟩

theorem hasFiniteBiproducts [HasZeroObject C] [HasBinaryBiproducts C] :
    HasFiniteBiproducts (CategoryTheory.Quotient r) :=
  haveI := hasZeroObject (r := r)
  haveI := hasBinaryBiproducts (r := r)
  hasFiniteBiproducts_of_binary

/-- The involution of `C/r` induced by a strict involution of `C` preserving `r`. -/
def involution [Congruence r] (J : StrictInvolution C)
    (hJ : ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), r f g → r (J.star f) (J.star g)) :
    StrictInvolution (CategoryTheory.Quotient r) where
  star φ := Quot.liftOn φ (fun f ↦ (Quotient.functor r).map (J.star f)) fun f g h ↦ by
    rw [HomRel.compClosure_eq_self] at h
    exact CategoryTheory.Quotient.sound _ (hJ f g h)
  star_comp := by
    rintro _ _ _ ⟨f⟩ ⟨g⟩
    exact congrArg (Quotient.functor r).map (J.star_comp f g)
  star_id X := congrArg (Quotient.functor r).map (J.star_id X.as)
  star_add {_ _} φ ψ := by
    obtain ⟨f, rfl⟩ := (Quotient.functor r).map_surjective φ
    obtain ⟨g, rfl⟩ := (Quotient.functor r).map_surjective ψ
    rw [← Functor.map_add]
    exact (congrArg (Quotient.functor r).map (J.star_add f g)).trans (Functor.map_add _)
  star_star := by
    rintro _ _ ⟨f⟩
    exact congrArg (Quotient.functor r).map (J.star_star f)

/-- The quotient of an `InvCat` by a congruence compatible with `+`, `•` and duality. -/
def invCat (A : InvCat) (r : HomRel A) [Congruence r]
    (hadd : ∀ ⦃X Y : A⦄ (f₁ f₂ g₁ g₂ : X ⟶ Y), r f₁ f₂ → r g₁ g₂ → r (f₁ + g₁) (f₂ + g₂))
    (hsmul : ∀ (c : ℚ) ⦃X Y : A⦄ (f₁ f₂ : X ⟶ Y), r f₁ f₂ → r (c • f₁) (c • f₂))
    (hstar : ∀ ⦃X Y : A⦄ (f g : X ⟶ Y), r f g → r (A.inv.star f) (A.inv.star g)) : InvCat :=
  letI := Quotient.preadditive r hadd
  haveI : (Quotient.functor r).Additive := Quotient.functor_additive r hadd
  letI := Quotient.linear ℚ r hsmul
  haveI := hasFiniteBiproducts (r := r)
  { carrier := CategoryTheory.Quotient r
    inv := involution A.inv hstar
    unitary X Y := by
      obtain ⟨b⟩ := A.unitary X.as Y.as
      exact ⟨{ toBinaryBicone := (Quotient.functor r).mapBinaryBicone b.toBinaryBicone
               isBilimit := isBilimitMap _ b.isBilimit
               star_inl := congrArg (Quotient.functor r).map b.star_inl
               star_inr := congrArg (Quotient.functor r).map b.star_inr }⟩ }

end QuotientLift

/-! ### Exterior quotients: `ℚ`-linearity and the `InvCat` structure -/

namespace ExteriorCategory

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  {π : ∀ i, G i →* H} {X : Type u} [MulAction H X] [PseudoEMetricSpace X] {Z : Set X}

instance functor_linear : (functor (π := π) (Z := Z)).Linear ℚ :=
  Quotient.linear_functor ℚ _ fun c _ _ _ _ h ↦ by
    simpa [AsymptoticCategory.idealRel, ← smul_sub] using h.smul c

end ExteriorCategory

theorem asymptoticInvolution_eq {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)]
    [∀ i, Fintype (G i)] (π : ∀ i, G i →* H) (X : Type) [MulAction H X] [PseudoEMetricSpace X] :
    asymptoticInvolution π X = AsymptoticCategory.involution π X :=
  rfl

theorem exteriorInvCat_inv {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)]
    [∀ i, Fintype (G i)] (π : ∀ i, G i →* H) {X : Type} [MulAction H X] [PseudoEMetricSpace X]
    (Z : Set X) : (exteriorInvCat π Z).inv = ExteriorCategory.involution π Z :=
  rfl

theorem supportKaroubiFiltration_sub_inv {H : Type*} [Group H] {G : ℕ → Type}
    [∀ i, Group (G i)] [∀ i, Fintype (G i)] (π : ∀ i, G i →* H) {X : Type} [MulAction H X]
    [PseudoEMetricSpace X] (S : Set X) :
    (supportKaroubiFiltration π S).sub.inv = AsymptoticCategory.supportInvolution π S :=
  rfl

/-! ### The free-sheet functor `ℬ_{1,Z}(X) → ℬ_{G,Z}(X)` (l.849) -/

section FreeSheet

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  {π : ∀ i, G i →* H} {X : Type u} [MulAction H X] [PseudoEMetricSpace X] [IsIsometricSMul H X]

namespace AsymptoticObject

instance freeSheet_additive : (freeSheet (X := X) π).Additive where
  map_add {_ _ f g} := hom_ext fun i ↦ by
    change sheet (1 : G i) (scalarMatrix π (f + g).1 i) =
      sheet (1 : G i) (scalarMatrix π f.1 i) + sheet (1 : G i) (scalarMatrix π g.1 i)
    rw [← sheet_add]
    rfl

instance freeSheet_linear : (freeSheet (X := X) π).Linear ℚ where
  map_smul f c := hom_ext fun i ↦ by
    change sheet (1 : G i) (scalarMatrix π (c • f).1 i) = c • sheet (1 : G i) (scalarMatrix π f.1 i)
    rw [← sheet_smul]
    rfl

end AsymptoticObject

namespace AsymptoticCategory

instance freeSheet_linear : (freeSheet (X := X) π).Linear ℚ :=
  QuotientLift.linear ℚ _ _

/-- The free-sheet functor `𝒜_1(X) → 𝒜_G(X)` is strictly duality-preserving. -/
def freeSheetInv : InvFunctor (involution (scalarHom H) X) (involution π X) where
  F := freeSheet π
  map_star := freeSheet_map_transpose

end AsymptoticCategory

namespace ExteriorCategory

variable {Z : Set X} (hZ : ∀ h : H, h • Z = Z)

instance freeSheet_additive : (freeSheet π hZ).Additive :=
  QuotientLift.additive _ _

instance freeSheet_linear : (freeSheet π hZ).Linear ℚ :=
  QuotientLift.linear ℚ _ _

theorem freeSheet_map_functor_map {A B : AsymptoticCategory (scalarHom H) X} (φ : A ⟶ B) :
    (freeSheet π hZ).map (functor.map φ) = functor.map ((AsymptoticCategory.freeSheet π).map φ) :=
  rfl

/-- The free-sheet functor commutes strictly with transpose duality. -/
theorem freeSheet_map_transpose {A B : ExteriorCategory (scalarHom H) Z} (φ : A ⟶ B) :
    (freeSheet π hZ).map (transpose φ) = transpose ((freeSheet π hZ).map φ) := by
  obtain ⟨f, rfl⟩ := functor.map_surjective φ
  exact congrArg functor.map (AsymptoticCategory.freeSheet_map_transpose f)

/-- **Free sheets** `ℬ_{1,Z}(X) → ℬ_{G,Z}(X)` as a strictly duality-preserving additive functor;
it transports chain complexes, homotopies and Poincaré complexes (`InvFunctor.mapC`, …). -/
def freeSheetInv : InvFunctor (involution (scalarHom H) Z) (involution π Z) where
  F := freeSheet π hZ
  map_star := freeSheet_map_transpose hZ

end ExteriorCategory

end FreeSheet

section FreeSheetFiltration

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  {π : ∀ i, G i →* H} {X : Type} [MulAction H X] [PseudoEMetricSpace X] [IsIsometricSMul H X]
  {Z : Set X}

/-- Free sheets as a map of support filtrations `(𝒜_{1,Z} ⊂ 𝒜_1) → (𝒜_{G,Z} ⊂ 𝒜_G)`. -/
def freeSheetFiltrationHom (hZ : ∀ h : H, h • Z = Z) :
    FiltrationHom (supportKaroubiFiltration (scalarHom H) Z) (supportKaroubiFiltration π Z) :=
  ⟨AsymptoticCategory.freeSheetInv, fun _ hA ↦
    (AsymptoticObject.isSupported_freeSheetObj_iff hZ).mpr hA⟩

/-- The induced map of exterior quotients is `ExteriorCategory.freeSheet`. -/
theorem freeSheetFiltrationHom_quot (hZ : ∀ h : H, h • Z = Z) :
    (freeSheetFiltrationHom (π := π) hZ).quot.F = ExteriorCategory.freeSheet π hZ :=
  rfl

end FreeSheetFiltration

/-! ### Duality and additivity of push-forward, relabeling (Lemma 2.4), `𝒜_A/𝒜_Y` and excision
(Lemma 2.2) -/

section Relabel

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  {π : ∀ i, G i →* H} {X : Type u} [MulAction H X] [PseudoEMetricSpace X]
  {Y : Type v} [MulAction H Y] [PseudoEMetricSpace Y] {j : Y → X}
  (hjeq : ∀ (h : H) (y : Y), j (h • y) = h • j y)

instance AsymptoticObject.pushFunctor_additive (hj : UniformContinuous j) :
    (AsymptoticObject.pushFunctor (π := π) hjeq hj).Additive where
  map_add := rfl

instance AsymptoticObject.pushFunctor_linear (hj : UniformContinuous j) :
    (AsymptoticObject.pushFunctor (π := π) hjeq hj).Linear ℚ where
  map_smul _ _ := rfl

namespace AsymptoticCategory

instance pushTail_additive (hj : UniformContinuous j) : (pushTail (π := π) hjeq hj).Additive :=
  QuotientLift.additive _ _

instance pushTail_linear (hj : UniformContinuous j) : (pushTail (π := π) hjeq hj).Linear ℚ :=
  QuotientLift.linear ℚ _ _

/-- Uniformly continuous equivariant push-forward preserves duality (l.70). -/
def pushTailInv (hj : UniformContinuous j) : InvFunctor (involution π Y) (involution π X) where
  F := pushTail hjeq hj
  map_star := pushTail_transpose hjeq hj

variable (hj : Isometry j) {T : Set X} (hT : Set.range j = T)

instance relabelFunctor_additive : (relabelFunctor (π := π) hjeq hj hT).Additive where
  map_add := by
    intros
    ext1
    exact (pushTail hjeq hj.uniformContinuous).map_add

instance relabelFunctor_linear : (relabelFunctor (π := π) hjeq hj hT).Linear ℚ where
  map_smul _ _ := by
    ext1
    exact (pushTail hjeq hj.uniformContinuous).map_smul _ _

/-- **Lemma 2.4** is duality-preserving: `𝒜_G(Y) → 𝒜_{j(Y)}(X)` as an `InvFunctor`. -/
def relabelInv : InvFunctor (involution π Y) (supportInvolution π T) where
  F := relabelFunctor hjeq hj hT
  map_star f := by
    ext1
    exact pushTail_transpose hjeq hj.uniformContinuous f

end AsymptoticCategory

end Relabel

section SupportQuotient

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  {π : ∀ i, G i →* H} {X : Type} [MulAction H X] [PseudoEMetricSpace X]

namespace AsymptoticCategory

variable {S A Y B : Set X}

/-- `𝒜_S(X)` is replete: membership is closed under isomorphisms of `𝒜(X)`. -/
theorem supportProperty_of_iso {P Q : AsymptoticCategory π X} (e : P ≅ Q)
    (hP : supportProperty S P) : supportProperty S Q :=
  (supportProperty S).prop_of_iso e hP

example : (supportProperty (π := π) S).IsClosedUnderIsomorphisms := inferInstance

instance SupportQuotient.hasZeroObject : HasZeroObject (SupportQuotient π A Y) :=
  QuotientLift.hasZeroObject

instance SupportQuotient.hasBinaryBiproducts : HasBinaryBiproducts (SupportQuotient π A Y) :=
  QuotientLift.hasBinaryBiproducts

instance SupportQuotient.hasFiniteBiproducts : HasFiniteBiproducts (SupportQuotient π A Y) :=
  QuotientLift.hasFiniteBiproducts

variable (π A Y) in
/-- `𝒜_A/𝒜_Y` as an `InvCat`: the quotient of the `InvCat` `𝒜_A(X)` by `I_Y`. -/
def supportQuotientInvCat : InvCat :=
  haveI : Congruence (C := (supportKaroubiFiltration π A).sub) (subIdealRel π A Y) :=
    subIdealRel_congruence A Y
  QuotientLift.invCat (supportKaroubiFiltration π A).sub (subIdealRel π A Y) subIdealRel_add
    subIdealRel_smul fun _ _ _ _ h ↦
      (congrArg (InIdeal Y) (transpose_sub _ _)).mp (inIdeal_transpose h)

theorem supportQuotientInvCat_carrier :
    (supportQuotientInvCat π A Y).carrier = SupportQuotient π A Y :=
  rfl

theorem supportQuotientInvCat_inv :
    (supportQuotientInvCat π A Y).inv = SupportQuotient.involution π A Y :=
  rfl

instance excisionFunctor_additive : (excisionFunctor (π := π) A B).Additive :=
  QuotientLift.additive _ _

instance excisionFunctor_linear : (excisionFunctor (π := π) A B).Linear ℚ :=
  QuotientLift.linear ℚ _ _

variable (A B) in
/-- **Lemma 2.2(ii)** is duality-preserving: `𝒜_A/𝒜_{A ∩ B} → 𝒜(X)/𝒜_B` as an `InvFunctor`. -/
def excisionInv :
    InvFunctor (SupportQuotient.involution π A (A ∩ B)) (ExteriorCategory.involution π B) where
  F := excisionFunctor A B
  map_star φ := by
    obtain ⟨f, rfl⟩ := SupportQuotient.functor.map_surjective φ
    rfl

variable (π A B) in
/-- Excision as a morphism of `InvCat`s `𝒜_A/𝒜_{A ∩ B} → ℬ_B(X)`. -/
def excisionInvCatHom : supportQuotientInvCat π A (A ∩ B) ⟶ exteriorInvCat π B :=
  excisionInv A B

end AsymptoticCategory

end SupportQuotient

/-! ### Duality-preserving equivalences -/

namespace UnitaryInverse

variable {V : Type*} [Category V] [Preadditive V] {W : Type*} [Category W] [Preadditive W]
  {J : StrictInvolution V} {J' : StrictInvolution W} (Φ : InvFunctor J J')

/-- Every object is unitarily isomorphic to an image of `Φ`. -/
def UnitarilyEssSurj : Prop :=
  ∀ Y : W, ∃ (X : V) (e : Φ.F.obj X ≅ Y), J'.star e.hom = e.inv

variable {Φ} (h : UnitarilyEssSurj Φ)

/-- The chosen preimage. -/
def obj (Y : W) : V := (h Y).choose

/-- The chosen unitary isomorphism. -/
def iso (Y : W) : Φ.F.obj (obj h Y) ≅ Y := (h Y).choose_spec.choose

theorem star_iso_hom (Y : W) : J'.star (iso h Y).hom = (iso h Y).inv :=
  (h Y).choose_spec.choose_spec

theorem star_iso_inv (Y : W) : J'.star (iso h Y).inv = (iso h Y).hom := by
  rw [← star_iso_hom, J'.star_star]

variable [Φ.F.Full] [Φ.F.Faithful]

/-- The inverse functor of a fully faithful, unitarily essentially surjective `Φ`. -/
@[reducible]
def functor : W ⥤ V where
  obj := obj h
  map g := Φ.F.preimage ((iso h _).hom ≫ g ≫ (iso h _).inv)
  map_id _ := Φ.F.map_injective (by simp)
  map_comp _ _ := Φ.F.map_injective (by simp)

theorem map_functor_map {Y Y' : W} (g : Y ⟶ Y') :
    Φ.F.map ((functor h).map g) = (iso h Y).hom ≫ g ≫ (iso h Y').inv :=
  Φ.F.map_preimage _

/-- The strictly duality-preserving inverse. -/
def inv : InvFunctor J' J where
  F := functor h
  additive := ⟨fun {_ _ _ _} ↦ Φ.F.map_injective (by
    simp only [Φ.F.map_add, map_functor_map, Functor.map_preimage, Preadditive.add_comp,
      Preadditive.comp_add])⟩
  map_star g := Φ.F.map_injective (by
    rw [Φ.map_star, map_functor_map, map_functor_map, J'.star_comp, J'.star_comp, star_iso_hom,
      star_iso_inv, Category.assoc])

/-- `Ψ ⋙ Φ ≅ 𝟭`. -/
def counitIso : functor h ⋙ Φ.F ≅ 𝟭 W :=
  NatIso.ofComponents (iso h) fun g ↦ by simp [map_functor_map]

theorem counitIso_star (Y : W) : J'.star ((counitIso h).hom.app Y) = (counitIso h).inv.app Y :=
  star_iso_hom h Y

/-- `Φ ⋙ Ψ ≅ 𝟭`. -/
def unitIso : Φ.F ⋙ functor h ≅ 𝟭 V :=
  NatIso.ofComponents (fun X ↦ Φ.F.preimageIso (iso h (Φ.F.obj X))) fun f ↦
    Φ.F.map_injective (by simp [map_functor_map])

theorem unitIso_star (X : V) : J.star ((unitIso h).hom.app X) = (unitIso h).inv.app X :=
  Φ.F.map_injective (by simp [unitIso, Φ.map_star, star_iso_hom])

/-- In `InvCat`: a fully faithful, unitarily essentially surjective morphism is an equivalence
up to unitary natural isomorphisms (so it induces isomorphisms on `L`-groups). -/
theorem invCat_equiv {A B : InvCat} {Φ : InvFunctor A.inv B.inv} [Φ.F.Full] [Φ.F.Faithful]
    (h : UnitarilyEssSurj Φ) :
    ∃ Ψ : B ⟶ A, Nonempty (InvCat.UnitaryIso ((Φ : A ⟶ B) ≫ Ψ) (𝟙 A)) ∧
      Nonempty (InvCat.UnitaryIso (Ψ ≫ (Φ : A ⟶ B)) (𝟙 B)) :=
  ⟨inv h, ⟨⟨unitIso h, unitIso_star h⟩⟩, ⟨⟨counitIso h, counitIso_star h⟩⟩⟩

end UnitaryInverse

section Equivalences

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  {π : ∀ i, G i →* H} {X : Type} [MulAction H X] [PseudoEMetricSpace X]

open AsymptoticObject

namespace AsymptoticCategory

variable {A B : Set X}

/-- The splitting of Lemma 2.2(ii) is unitary. -/
theorem excisionInv_unitarilyEssSurj (hAinv : ∀ h : H, h • A = A) (hcover : A ∪ B = Set.univ) :
    UnitaryInverse.UnitarilyEssSurj (excisionInv (π := π) A B) := fun T ↦ by
  set N := T.as.as
  let P : ∀ i, Fin (N.rank i) → Prop := fun i k ↦ N.label i k ∈ A
  have hsupp : supportProperty A (functor.obj (N.restrict P)) :=
    tendsto_zero_of_forall_eq_zero fun i ↦
    le_antisymm (iSup_le fun b ↦ (infEDist_zero_of_mem ((smul_mem_iff_of_invariant hAinv _ _).mpr
      ((N.mem_range_restrictEmb P i _).mp ⟨b.1, rfl⟩))).le) bot_le
  let E := ExteriorCategory.functor (π := π) (Z := B)
  refine ⟨⟨⟨functor.obj (N.restrict P), hsupp⟩⟩,
    { hom := E.map (functor.map (N.restrictEmb P).incl)
      inv := E.map (functor.map (N.restrictEmb P).proj)
      hom_inv_id := ?_
      inv_hom_id := ?_ }, rfl⟩
  · erw [← Functor.map_comp, ← Functor.map_comp, OrbitEmbedding.incl_proj]
    rfl
  erw [← Functor.map_comp, ← Functor.map_comp, restrict_proj_incl]
  change E.map _ = E.map (functor.map (𝟙 N))
  rw [ExteriorCategory.functor_map_eq_iff, ← Functor.map_sub, inIdeal_map_iff]
  refine tendsto_zero_of_forall_eq_zero fun i ↦
    le_antisymm (endpointDist_le_iff.mpr fun c a hca ↦ ?_) bot_le
  have hc : c = a ∧ ¬ P i a.1 := by
    by_cases hca' : c = a
    · subst hca'
      by_cases hP : P i c.1
      · simp [hP] at hca
      · exact ⟨rfl, hP⟩
    · simp [diagonal_apply_ne _ hca', one_apply_ne hca'] at hca
  obtain ⟨rfl, hP⟩ := hc
  have hB' : N.fullLabel i c ∈ B := by
    have hx : N.fullLabel i c ∈ A ∪ B := hcover ▸ Set.mem_univ _
    exact hx.resolve_left fun hxA ↦ hP ((smul_mem_iff_of_invariant hAinv _ _).mp hxA)
  exact ⟨(infEDist_zero_of_mem hB').le, (infEDist_zero_of_mem hB').le⟩

/-- **Lemma 2.2(ii) with duality**: excision has a duality-preserving inverse up to unitary
natural isomorphisms. -/
theorem excisionInvCatHom_equiv [CompactSpace X] (hA : IsClosed A) (hB : IsClosed B)
    (hAinv : ∀ h : H, h • A = A) (hcover : A ∪ B = Set.univ) :
    ∃ Ψ : exteriorInvCat π B ⟶ supportQuotientInvCat π A (A ∩ B),
      Nonempty (InvCat.UnitaryIso (excisionInvCatHom π A B ≫ Ψ) (𝟙 _)) ∧
        Nonempty (InvCat.UnitaryIso (Ψ ≫ excisionInvCatHom π A B) (𝟙 _)) :=
  haveI := excisionFunctor_isEquivalence (π := π) hA hB hAinv hcover
  haveI hFull : (excisionInv (π := π) A B).F.Full := inferInstanceAs (excisionFunctor A B).Full
  haveI hFaith : (excisionInv (π := π) A B).F.Faithful :=
    inferInstanceAs (excisionFunctor A B).Faithful
  @UnitaryInverse.invCat_equiv (supportQuotientInvCat π A (A ∩ B)) (exteriorInvCat π B)
    (excisionInv A B) hFull hFaith (excisionInv_unitarilyEssSurj hAinv hcover)

variable {Y : Type} [MulAction H Y] [PseudoEMetricSpace Y] {j : Y → X}
  (hjeq : ∀ (h : H) (y : Y), j (h • y) = h • j y) (hj : Isometry j) {T : Set X}
  (hT : Set.range j = T)

/-- The relabeling of Lemma 2.4 is unitary. -/
theorem relabelInv_unitarilyEssSurj [IsIsometricSMul H X] [CompactSpace Y] [Nonempty Y] :
    UnitaryInverse.UnitarilyEssSurj (relabelInv (π := π) hjeq hj hT) := by
  subst hT
  intro O
  set N := O.obj.as
  have hK : IsCompact (Set.range j) := isCompact_range hj.continuous
  choose z hz hzeq using fun x : X ↦ hK.exists_infEDist_eq_edist (Set.range_nonempty j) x
  choose y hy using hz
  let M : AsymptoticObject π Y := ⟨N.rank, fun i k ↦ y (N.label i k)⟩
  have hbound : ∀ i (b : Fin (N.rank i) × G i),
      edist (N.fullLabel i b) ((M.push j).fullLabel i b) ≤ N.supportDist (Set.range j) i := by
    intro i b
    have : (M.push j).fullLabel i b = π i b.2 • j (y (N.label i b.1)) := rfl
    rw [this, fullLabel, edist_smul_left, hy, ← hzeq, ← fullLabel_one N i b.1]
    exact infEDist_le_supportDist i _
  let u : M.push j ⟶ N := ⟨fun i ↦ (1 : Matrix (Fin (N.rank i) × G i) (Fin (N.rank i) × G i) ℚ),
    ⟨fun _ ↦ IsEquivariant.one, tendsto_zero_of_le O.property fun i ↦
      prop_one_le _ _ fun b ↦ hbound i b⟩⟩
  let w : N ⟶ M.push j := ⟨fun i ↦ (1 : Matrix (Fin (N.rank i) × G i) (Fin (N.rank i) × G i) ℚ),
    ⟨fun _ ↦ IsEquivariant.one, tendsto_zero_of_le O.property fun i ↦
      prop_one_le _ _ fun b ↦ (edist_comm _ _).trans_le (hbound i b)⟩⟩
  refine ⟨functor.obj M, ObjectProperty.isoMk _ (functor.mapIso
    { hom := u, inv := w, hom_inv_id := ?_, inv_hom_id := ?_ }), ?_⟩
  · exact hom_ext fun i ↦ Matrix.one_mul 1
  · exact hom_ext fun i ↦ Matrix.one_mul 1
  · ext1
    exact congrArg functor.map (hom_ext fun _ ↦ Matrix.transpose_one)

/-- Lemma 2.4 as a morphism of `InvCat`s `𝒜_G(Y) → 𝒜_{j(Y)}(X)`. -/
def relabelInvCatHom : asymptoticInvCat π Y ⟶ (supportKaroubiFiltration π T).sub :=
  relabelInv hjeq hj hT

/-- **Lemma 2.4 with duality**: relabeling has a duality-preserving inverse up to unitary
natural isomorphisms. -/
theorem relabelInvCatHom_equiv [IsIsometricSMul H X] [CompactSpace Y] [Nonempty Y] :
    ∃ Ψ : (supportKaroubiFiltration π T).sub ⟶ asymptoticInvCat π Y,
      Nonempty (InvCat.UnitaryIso (relabelInvCatHom hjeq hj hT ≫ Ψ) (𝟙 _)) ∧
        Nonempty (InvCat.UnitaryIso (Ψ ≫ relabelInvCatHom hjeq hj hT) (𝟙 _)) :=
  haveI := relabelFunctor_isEquivalence (π := π) hjeq hj hT
  haveI hFull : (relabelInv (π := π) hjeq hj hT).F.Full :=
    inferInstanceAs (relabelFunctor hjeq hj hT).Full
  haveI hFaith : (relabelInv (π := π) hjeq hj hT).F.Faithful :=
    inferInstanceAs (relabelFunctor hjeq hj hT).Faithful
  @UnitaryInverse.invCat_equiv (asymptoticInvCat π Y) (supportKaroubiFiltration π T).sub
    (relabelInv hjeq hj hT) hFull hFaith (relabelInv_unitarilyEssSurj hjeq hj hT)

end AsymptoticCategory

end Equivalences

end HSFormal
