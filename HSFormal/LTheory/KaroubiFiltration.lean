import HSFormal.LTheory.Isometry
import HSFormal.AsymptoticKaroubi
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
import Mathlib.CategoryTheory.ObjectProperty.Retract
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!
# Additive categories with involution and Karoubi filtrations (L-theory module M4)

`InvCat`: small `ℚ`-linear additive categories with an object-fixing strict involution in which
every pair of objects has a unitary biproduct; morphisms are strictly duality-preserving additive
functors (`InvFunctor`).  `UnitaryIso` and `IsFinSum` are the unitary natural isomorphisms and
finite unitary sums of functors.

`KaroubiFiltration A` is [CP95, Definition 1.27] (`HSFormal.KaroubiFiltration`, axioms (i)–(iv))
for an additive, replete subcategory `U` invariant under the involution, with self-dual
splittings.  The factorization ideal `FactorsThrough U` defines the quotient `F.quot = A/U`
([CP95, p. 738]); `F.sub` is the full subcategory.  Both are `InvCat`s with the induced
involutions.  `FiltrationHom` are functors of pairs, with induced functors on `sub` and `quot`.

`F.restrict V` restricts a filtration to a retract-closed additive subcategory `V`.

Instances: `asymptoticInvCat π X` (`𝒜_G(X)`), its support filtrations
`supportKaroubiFiltration π S` (Lemma 2.1), `𝒜_Y ⊂ 𝒜_A` (`supportRestrictFiltration`) with the
map of filtrations to `𝒜_B ⊂ 𝒜` for `Y ⊆ B`, and the exterior quotient `exteriorInvCat π Z`,
whose carrier is `ExteriorCategory π Z = ℬ_Z(X)`.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HSFormal.Compression

noncomputable section

universe v u

section Ideal

variable {V : Type u} [Category.{v} V] [Preadditive V] (U : ObjectProperty V)

lemma hasFiniteBiproducts_of_binary [HasBinaryBiproducts V] [HasZeroObject V] :
    HasFiniteBiproducts V := by
  haveI : HasFiniteProducts V := hasFiniteProducts_of_has_binary_and_terminal
  exact HasFiniteBiproducts.of_hasFiniteProducts

/-- `f` lies in the factorization ideal `I_U`: it factors through an object of `U`. -/
def FactorsThrough {X Y : V} (f : X ⟶ Y) : Prop :=
  ∃ (W : V) (_ : U W) (u : X ⟶ W) (v : W ⟶ Y), f = u ≫ v

/-- `U` is a full additive replete subcategory. -/
class IsAdditiveSub : Prop extends U.IsClosedUnderIsomorphisms, U.ContainsZero where
  biprod_mem : ∀ {X Y : V} (b : BinaryBicone X Y), b.IsBilimit → U X → U Y → U b.pt

variable {U}

namespace FactorsThrough

variable {X Y Z : V} {f g : X ⟶ Y}

omit [Preadditive V] in
lemma comp_left (h : X ⟶ Y) {g : Y ⟶ Z} (hg : FactorsThrough U g) : FactorsThrough U (h ≫ g) := by
  obtain ⟨W, hW, u, v, rfl⟩ := hg
  exact ⟨W, hW, h ≫ u, v, by simp⟩

omit [Preadditive V] in
lemma comp_right (hf : FactorsThrough U f) (h : Y ⟶ Z) : FactorsThrough U (f ≫ h) := by
  obtain ⟨W, hW, u, v, rfl⟩ := hf
  exact ⟨W, hW, u, v ≫ h, by simp⟩

omit [Preadditive V] in
lemma of_mem {W : V} (hW : U W) (u : X ⟶ W) (v : W ⟶ Y) : FactorsThrough U (u ≫ v) :=
  ⟨W, hW, u, v, rfl⟩

lemma zero [U.ContainsZero] : FactorsThrough U (0 : X ⟶ Y) := by
  obtain ⟨W, -, hW⟩ := U.exists_prop_of_containsZero
  exact ⟨W, hW, 0, 0, by simp⟩

lemma neg (hf : FactorsThrough U f) : FactorsThrough U (-f) := by
  obtain ⟨W, hW, u, v, rfl⟩ := hf
  exact ⟨W, hW, u, -v, by simp⟩

lemma smul {R : Type*} [Semiring R] [Linear R V] (r : R) (hf : FactorsThrough U f) :
    FactorsThrough U (r • f) := by
  obtain ⟨W, hW, u, v, rfl⟩ := hf
  exact ⟨W, hW, u, r • v, by simp⟩

lemma add [IsAdditiveSub U] [HasBinaryBiproducts V] (hf : FactorsThrough U f)
    (hg : FactorsThrough U g) : FactorsThrough U (f + g) := by
  obtain ⟨W, hW, u, v, rfl⟩ := hf
  obtain ⟨W', hW', u', v', rfl⟩ := hg
  exact ⟨_, IsAdditiveSub.biprod_mem _ (BinaryBiproduct.isBilimit W W') hW hW',
    u ≫ biprod.inl + u' ≫ biprod.inr, biprod.fst ≫ v + biprod.snd ≫ v', by simp⟩

lemma sub [IsAdditiveSub U] [HasBinaryBiproducts V] (hf : FactorsThrough U f)
    (hg : FactorsThrough U g) : FactorsThrough U (f - g) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

lemma star (J : StrictInvolution V) (hf : FactorsThrough U f) : FactorsThrough U (J.star f) := by
  obtain ⟨W, hW, u, v, rfl⟩ := hf
  exact ⟨W, hW, J.star v, J.star u, J.star_comp u v⟩

omit [Preadditive V] in
lemma map {W : Type*} [Category W] [Preadditive W] {U' : ObjectProperty W} (Φ : V ⥤ W)
    (hΦ : ∀ X, U X → U' (Φ.obj X)) (hf : FactorsThrough U f) :
    FactorsThrough U' (Φ.map f) := by
  obtain ⟨W, hW, u, v, rfl⟩ := hf
  exact ⟨_, hΦ W hW, Φ.map u, Φ.map v, Φ.map_comp u v⟩

end FactorsThrough

variable (U)

/-- `f ~ g` iff `f - g ∈ I_U`. -/
def factorRel : HomRel V :=
  fun _ _ f g ↦ FactorsThrough U (f - g)

variable [IsAdditiveSub U] [HasBinaryBiproducts V]

instance factorRel_congruence : Congruence (factorRel U) where
  equivalence := ⟨fun _ ↦ by simpa [factorRel] using FactorsThrough.zero,
    fun h ↦ by simpa [factorRel] using h.neg, fun h h' ↦ by simpa [factorRel] using h.add h'⟩
  comp_left f _ _ h := by simpa [factorRel, comp_sub] using h.comp_left f
  comp_right g h := by simpa [factorRel, sub_comp] using h.comp_right g

/-- The quotient `V/U` of [CP95, p. 738]. -/
abbrev QuotCat := CategoryTheory.Quotient (factorRel U)

instance : Preadditive (QuotCat U) :=
  Quotient.preadditive _ fun _ _ _ _ _ _ h h' ↦ by
    simpa [factorRel, add_sub_add_comm] using h.add h'

instance : (Quotient.functor (factorRel U)).Additive :=
  Quotient.functor_additive _ _

instance [Linear ℚ V] : Linear ℚ (QuotCat U) :=
  Quotient.linear ℚ _ fun c _ _ _ _ h ↦ by simpa [factorRel, ← smul_sub] using h.smul c

instance [Linear ℚ V] : (Quotient.functor (factorRel U)).Linear ℚ :=
  Quotient.linear_functor ℚ _ fun c _ _ _ _ h ↦ by simpa [factorRel, ← smul_sub] using h.smul c

variable {U} in
theorem quot_map_eq_iff {X Y : V} (f g : X ⟶ Y) :
    (Quotient.functor (factorRel U)).map f = (Quotient.functor (factorRel U)).map g ↔
      FactorsThrough U (f - g) :=
  Quotient.functor_map_eq_iff _ f g

/-- An additive functor sends bilimit binary bicones to bilimit binary bicones. -/
def isBilimitMap {W : Type*} [Category W] [Preadditive W] (Φ : V ⥤ W) [Φ.Additive] {X Y : V}
    {b : BinaryBicone X Y} (hb : b.IsBilimit) : (Φ.mapBinaryBicone b).IsBilimit :=
  isBinaryBilimitOfTotal _ <| by
    have := congrArg Φ.map (IsBilimit.binary_total hb)
    rw [Φ.map_add, Φ.map_comp, Φ.map_comp, Φ.map_id] at this
    exact this

instance : HasZeroObject (QuotCat U) := by
  obtain ⟨Z, hZ, -⟩ := U.exists_prop_of_containsZero
  exact ⟨⟨_, (Quotient.functor (factorRel U)).map_isZero hZ⟩⟩

instance : HasBinaryBiproducts (QuotCat U) :=
  ⟨fun X Y ↦ HasBinaryBiproduct.mk ⟨(Quotient.functor (factorRel U)).mapBinaryBicone
    (BinaryBiproduct.bicone X.as Y.as), isBilimitMap _ (BinaryBiproduct.isBilimit _ _)⟩⟩

instance : HasFiniteBiproducts (QuotCat U) := hasFiniteBiproducts_of_binary

/-- The full subcategory of an additive subcategory is additive. -/
instance : HasZeroObject U.FullSubcategory := by
  obtain ⟨Z, hZ, hU⟩ := U.exists_prop_of_containsZero
  refine ⟨⟨⟨Z, hU⟩, (IsZero.iff_id_eq_zero _).mpr (ObjectProperty.hom_ext _ ?_)⟩⟩
  exact hZ.eq_of_src _ _

/-- A bicone in `V` on objects of `U` with vertex in `U`, as a bicone in `U`. -/
@[simps]
def subBicone {X Y : U.FullSubcategory} (b : BinaryBicone X.obj Y.obj) (h : U b.pt) :
    BinaryBicone X Y where
  pt := ⟨b.pt, h⟩
  fst := ObjectProperty.homMk b.fst
  snd := ObjectProperty.homMk b.snd
  inl := ObjectProperty.homMk b.inl
  inr := ObjectProperty.homMk b.inr
  inl_fst := ObjectProperty.hom_ext _ b.inl_fst
  inl_snd := ObjectProperty.hom_ext _ b.inl_snd
  inr_fst := ObjectProperty.hom_ext _ b.inr_fst
  inr_snd := ObjectProperty.hom_ext _ b.inr_snd

/-- A lifted bilimit bicone is a bilimit bicone. -/
def subBicone_isBilimit {X Y : U.FullSubcategory} {b : BinaryBicone X.obj Y.obj} (hb : b.IsBilimit)
    (h : U b.pt) : (subBicone U b h).IsBilimit :=
  isBinaryBilimitOfTotal _ (ObjectProperty.hom_ext _ (IsBilimit.binary_total hb))

instance : HasBinaryBiproducts U.FullSubcategory :=
  ⟨fun X Y ↦ HasBinaryBiproduct.mk ⟨_, subBicone_isBilimit U (BinaryBiproduct.isBilimit X.obj Y.obj)
    (IsAdditiveSub.biprod_mem _ (BinaryBiproduct.isBilimit _ _) X.2 Y.2)⟩⟩

instance : HasFiniteBiproducts U.FullSubcategory := hasFiniteBiproducts_of_binary

end Ideal

section Involution

variable {V : Type u} [Category.{v} V] [Preadditive V] (J : StrictInvolution V)
  (U : ObjectProperty V)

/-- The restricted involution on `U`. -/
@[simps]
def subInvolution : StrictInvolution U.FullSubcategory where
  star f := ObjectProperty.homMk (J.star f.hom)
  star_comp f g := ObjectProperty.hom_ext _ (J.star_comp f.hom g.hom)
  star_id X := ObjectProperty.hom_ext _ (J.star_id X.obj)
  star_add f g := ObjectProperty.hom_ext _ (J.star_add f.hom g.hom)
  star_star f := ObjectProperty.hom_ext _ (J.star_star f.hom)

variable [IsAdditiveSub U] [HasBinaryBiproducts V]

/-- The induced involution on `V/U`; well defined since `I_U` is `*`-invariant. -/
def quotInvolution : StrictInvolution (QuotCat U) where
  star f := Quot.liftOn f (fun f ↦ (Quotient.functor (factorRel U)).map (J.star f))
    fun f g h ↦ by
      rw [HomRel.compClosure_eq_self] at h
      exact CategoryTheory.Quotient.sound _ (by simpa [factorRel] using h.star J)
  star_comp := by
    rintro _ _ _ ⟨f⟩ ⟨g⟩
    exact congrArg (Quotient.functor _).map (J.star_comp f g)
  star_id X := congrArg (Quotient.functor _).map (J.star_id X.as)
  star_add := by
    rintro _ _ ⟨f⟩ ⟨g⟩
    exact congrArg (Quotient.functor _).map (J.star_add f g)
  star_star := by
    rintro _ _ ⟨f⟩
    exact congrArg (Quotient.functor _).map (J.star_star f)

@[simp]
lemma quotInvolution_star_map {X Y : V} (f : X ⟶ Y) :
    (quotInvolution J U).star ((Quotient.functor (factorRel U)).map f) =
      (Quotient.functor (factorRel U)).map (J.star f) := rfl

end Involution

lemma InvFunctor.ext {V : Type u} [Category.{v} V] [Preadditive V] {W : Type*} [Category W]
    [Preadditive W] {J : StrictInvolution V} {J' : StrictInvolution W} {Φ Ψ : InvFunctor J J'}
    (h : Φ.F = Ψ.F) : Φ = Ψ := by
  cases Φ; cases Ψ; subst h; rfl

/-- A small `ℚ`-linear additive category with an object-fixing strict involution in which every
pair of objects has a unitary biproduct. -/
structure InvCat : Type 1 where
  carrier : Type
  [cat : SmallCategory carrier]
  [preadd : Preadditive carrier]
  [lin : Linear ℚ carrier]
  [biprod : HasFiniteBiproducts carrier]
  inv : StrictInvolution carrier
  unitary : ∀ X Y : carrier, Nonempty (UnitaryBicone inv X Y)

namespace InvCat

attribute [instance] cat preadd lin biprod

instance : CoeSort InvCat Type := ⟨carrier⟩

instance (A : InvCat) : HasBinaryBiproducts A := hasBinaryBiproducts_of_finite_biproducts _

/-- Morphisms are strictly duality-preserving additive functors. -/
instance : LargeCategory InvCat where
  Hom A B := InvFunctor A.inv B.inv
  id A := InvFunctor.id A.inv
  comp Φ Ψ := Φ.comp Ψ
  id_comp _ := InvFunctor.ext (Functor.id_comp _)
  comp_id _ := InvFunctor.ext (Functor.comp_id _)
  assoc _ _ _ := InvFunctor.ext (Functor.assoc _ _ _)

variable {A B C : InvCat}

@[simp] lemma id_F (A : InvCat) : (𝟙 A : InvFunctor A.inv A.inv).F = 𝟭 A := rfl

@[simp] lemma comp_F (Φ : A ⟶ B) (Ψ : B ⟶ C) :
    (Φ ≫ Ψ : InvFunctor A.inv C.inv).F = (Φ : InvFunctor A.inv B.inv).F ⋙ Ψ.F := rfl

lemma hom_ext {Φ Ψ : A ⟶ B} (h : Φ.F = Ψ.F) : Φ = Ψ := InvFunctor.ext h

/-- A unitary natural isomorphism: `η^* = η⁻¹`. -/
structure UnitaryIso (Φ Ψ : A ⟶ B) where
  iso : Φ.F ≅ Ψ.F
  star_hom : ∀ X, B.inv.star (iso.hom.app X) = iso.inv.app X

namespace UnitaryIso

variable {Φ Ψ Θ : A ⟶ B}

lemma star_inv (e : UnitaryIso Φ Ψ) (X : A) : B.inv.star (e.iso.inv.app X) = e.iso.hom.app X := by
  rw [← e.star_hom, B.inv.star_star]

/-- The identity. -/
@[simps]
def refl (Φ : A ⟶ B) : UnitaryIso Φ Φ := ⟨Iso.refl _, fun _ ↦ B.inv.star_id _⟩

/-- The inverse. -/
@[simps]
def symm (e : UnitaryIso Φ Ψ) : UnitaryIso Ψ Φ := ⟨e.iso.symm, e.star_inv⟩

/-- The composite. -/
@[simps]
def trans (e : UnitaryIso Φ Ψ) (e' : UnitaryIso Ψ Θ) : UnitaryIso Φ Θ :=
  ⟨e.iso ≪≫ e'.iso, fun X ↦ by simp [B.inv.star_comp, e.star_hom, e'.star_hom]⟩

end UnitaryIso

/-- `S` is the finite unitary sum of the functors `Φ i`: pointwise, the `inc i` and their duals
form a biproduct. -/
structure IsFinSum {ι : Type*} [Fintype ι] (Φ : ι → (A ⟶ B)) (S : A ⟶ B) where
  inc : ∀ i, (Φ i).F ⟶ S.F
  inc_star_self : ∀ i X, (inc i).app X ≫ B.inv.star ((inc i).app X) = 𝟙 _
  inc_star_ne : ∀ i j, i ≠ j → ∀ X, (inc i).app X ≫ B.inv.star ((inc j).app X) = 0
  total : ∀ X, ∑ i, B.inv.star ((inc i).app X) ≫ (inc i).app X = 𝟙 _

namespace IsFinSum

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : ι → (A ⟶ B)} {S : A ⟶ B}

/-- The pointwise biproduct bicone. -/
@[simps]
def bicone (h : IsFinSum Φ S) (X : A) : Bicone fun i ↦ ((Φ i).F).obj X where
  pt := (S.F).obj X
  π i := B.inv.star ((h.inc i).app X)
  ι i := (h.inc i).app X
  ι_π i j := by
    split_ifs with hij
    · subst hij; simpa using h.inc_star_self i X
    · exact h.inc_star_ne i j hij X

/-- Each pointwise bicone is a biproduct. -/
def isBilimit (h : IsFinSum Φ S) (X : A) : (h.bicone X).IsBilimit :=
  isBilimitOfTotal _ (h.total X)

end IsFinSum

section SubQuot

variable (A) (U : ObjectProperty A) [IsAdditiveSub U]

/-- The full subcategory `U` with the restricted involution. -/
@[implicit_reducible] def sub : InvCat where
  carrier := U.FullSubcategory
  inv := subInvolution A.inv U
  unitary X Y := by
    obtain ⟨b⟩ := A.unitary X.obj Y.obj
    have h := IsAdditiveSub.biprod_mem _ b.isBilimit X.2 Y.2
    exact ⟨{ toBinaryBicone := subBicone U b.toBinaryBicone h
             isBilimit := subBicone_isBilimit U b.isBilimit h
             star_inl := ObjectProperty.hom_ext _ b.star_inl
             star_inr := ObjectProperty.hom_ext _ b.star_inr }⟩

/-- The quotient `A/U` by the factorization ideal, with the induced involution. -/
@[implicit_reducible] def quotient : InvCat where
  carrier := QuotCat U
  inv := quotInvolution A.inv U
  unitary X Y := by
    obtain ⟨b⟩ := A.unitary X.as Y.as
    exact ⟨{ toBinaryBicone := (Quotient.functor _).mapBinaryBicone b.toBinaryBicone
             isBilimit := isBilimitMap _ b.isBilimit
             star_inl := congrArg (Quotient.functor _).map b.star_inl
             star_inr := congrArg (Quotient.functor _).map b.star_inr }⟩

/-- The inclusion `U ⊂ A`. -/
@[simps!, implicit_reducible]
def subIncl : A.sub U ⟶ A where
  F := U.ι
  additive := inferInstanceAs U.ι.Additive
  map_star _ := rfl

/-- The projection `A → A/U`. -/
@[simps!, implicit_reducible]
def quotProj : A ⟶ A.quotient U where
  F := Quotient.functor (factorRel U)
  additive := inferInstanceAs (Quotient.functor (factorRel U)).Additive
  map_star _ := rfl

end SubQuot

end InvCat

/-- [CP95, Definition 1.27] on an `InvCat`, compatible with the involution.  `U` is a full
additive replete subcategory; `filt` gives the families of splittings `X = E_α ⊕ X_α` with
`E_α ∈ U` and axioms (i) filtered poset, (ii)–(iii) factorization, (iv) sum
(`HSFormal.KaroubiFiltration`); every splitting is self-dual.  The object-fixing involution
preserves `U`, the hypothesis of [CP95, Theorem 4.2]. -/
structure KaroubiFiltration (A : InvCat) where
  U : ObjectProperty A
  [additive : IsAdditiveSub U]
  filt : HSFormal.KaroubiFiltration U
  star_ιE : ∀ X, ∀ σ ∈ filt.splittings X, A.inv.star σ.ιE = σ.πE
  star_ιU : ∀ X, ∀ σ ∈ filt.splittings X, A.inv.star σ.ιU = σ.πU

namespace KaroubiFiltration

attribute [instance] additive

variable {A B C : InvCat} (F : KaroubiFiltration A)

/-- The subcategory `U`. -/
abbrev sub : InvCat := A.sub F.U

/-- The quotient `A/U`. -/
abbrev quot : InvCat := A.quotient F.U

/-- The inclusion `U → A`. -/
abbrev incl : F.sub ⟶ A := A.subIncl F.U

/-- The projection `A → A/U`. -/
abbrev proj : A ⟶ F.quot := A.quotProj F.U

variable {F} {X Y : A} {σ : Splitting X}

lemma star_πE (hσ : σ ∈ F.filt.splittings X) : A.inv.star σ.πE = σ.ιE := by
  rw [← F.star_ιE X σ hσ, A.inv.star_star]

lemma star_πU (hσ : σ ∈ F.filt.splittings X) : A.inv.star σ.πU = σ.ιU := by
  rw [← F.star_ιU X σ hσ, A.inv.star_star]

lemma star_idem (hσ : σ ∈ F.filt.splittings X) : A.inv.star σ.idem = σ.idem := by
  rw [Splitting.idem, A.inv.star_comp, F.star_ιE X σ hσ, star_πE hσ]

variable (F)

/-- Axiom (iii): `I_U` is the set of maps factoring through some `X → E_α`. -/
theorem factorsThrough_iff_source (f : X ⟶ Y) :
    FactorsThrough F.U f ↔ ∃ σ ∈ F.filt.splittings X, ∃ g : σ.E ⟶ Y, f = σ.πE ≫ g := by
  constructor
  · rintro ⟨W, hW, u, v, rfl⟩
    obtain ⟨σ, hσ, g, rfl⟩ := F.filt.factor_from hW u
    exact ⟨σ, hσ, g ≫ v, by simp⟩
  · rintro ⟨σ, hσ, g, rfl⟩
    exact FactorsThrough.of_mem (F.filt.mem X σ hσ) _ _

/-- Axiom (ii): `I_U` is the set of maps factoring through some `E_α → Y`. -/
theorem factorsThrough_iff_target (f : X ⟶ Y) :
    FactorsThrough F.U f ↔ ∃ σ ∈ F.filt.splittings Y, ∃ g : X ⟶ σ.E, f = g ≫ σ.ιE := by
  constructor
  · rintro ⟨W, hW, u, v, rfl⟩
    obtain ⟨σ, hσ, g, rfl⟩ := F.filt.factor_to hW v
    exact ⟨σ, hσ, u ≫ g, by simp⟩
  · rintro ⟨σ, hσ, g, rfl⟩
    exact FactorsThrough.of_mem (F.filt.mem Y σ hσ) _ _

theorem proj_map_eq_iff (f g : X ⟶ Y) :
    F.proj.F.map f = F.proj.F.map g ↔ FactorsThrough F.U (f - g) :=
  quot_map_eq_iff f g

end KaroubiFiltration

/-- A morphism of filtered `InvCat`s: a duality-preserving functor with `Φ(U) ⊆ U'`. -/
structure FiltrationHom {A B : InvCat} (F : KaroubiFiltration A) (F' : KaroubiFiltration B) where
  toHom : A ⟶ B
  map_mem : ∀ X, F.U X → F'.U (toHom.F.obj X)

namespace FiltrationHom

variable {A B C : InvCat} {F : KaroubiFiltration A} {F' : KaroubiFiltration B}
  {F'' : KaroubiFiltration C} (Φ : FiltrationHom F F')

/-- The restriction `U → U'`. -/
def sub : F.sub ⟶ F'.sub where
  F := F'.U.lift (F.U.ι ⋙ Φ.toHom.F) fun X ↦ Φ.map_mem _ X.2
  additive := { map_add := ObjectProperty.hom_ext _ (Φ.toHom.F).map_add }
  map_star f := ObjectProperty.hom_ext _ (Φ.toHom.map_star f.hom)

/-- The induced functor `A/U → B/U'`. -/
def quot : F.quot ⟶ F'.quot where
  F := CategoryTheory.Quotient.lift (factorRel F.U) (Φ.toHom.F ⋙ Quotient.functor _)
    fun _ _ f g (h : FactorsThrough F.U (f - g)) ↦
      (quot_map_eq_iff _ _).mpr (by simpa using h.map (Φ.toHom.F) Φ.map_mem)
  additive := ⟨by
    rintro _ _ ⟨f⟩ ⟨g⟩
    exact congrArg (Quotient.functor _).map (Φ.toHom.F).map_add⟩
  map_star := by
    rintro _ _ ⟨f⟩
    exact congrArg (Quotient.functor _).map (Φ.toHom.map_star f)

theorem incl_comp : F.incl ≫ Φ.toHom = Φ.sub ≫ F'.incl := rfl

theorem comp_proj : Φ.toHom ≫ F'.proj = F.proj ≫ Φ.quot := rfl

variable (F) in
/-- The identity. -/
@[simps]
def id : FiltrationHom F F := ⟨𝟙 A, fun _ h ↦ h⟩

/-- The composite. -/
@[simps]
def comp (Ψ : FiltrationHom F' F'') : FiltrationHom F F'' :=
  ⟨Φ.toHom ≫ Ψ.toHom, fun X h ↦ Ψ.map_mem _ (Φ.map_mem X h)⟩

@[simp] theorem id_sub : (id F).sub = 𝟙 F.sub := rfl

@[simp] theorem comp_sub (Ψ : FiltrationHom F' F'') : (Φ.comp Ψ).sub = Φ.sub ≫ Ψ.sub := rfl

@[simp] theorem id_quot : (id F).quot = 𝟙 F.quot :=
  InvCat.hom_ext (CategoryTheory.Quotient.lift_unique' _ _ _ rfl)

@[simp] theorem comp_quot (Ψ : FiltrationHom F' F'') : (Φ.comp Ψ).quot = Φ.quot ≫ Ψ.quot :=
  InvCat.hom_ext (CategoryTheory.Quotient.lift_unique' _ _ _ rfl)

end FiltrationHom

namespace KaroubiFiltration

variable {A : InvCat} (F : KaroubiFiltration A) (V : ObjectProperty A) [IsAdditiveSub V]
  [V.IsStableUnderRetracts]

/-- A splitting of an object of a retract-closed `V` is a splitting in `V`. -/
@[simps]
def liftSplitting {X : V.FullSubcategory} (σ : Splitting X.obj) : Splitting X where
  E := ⟨σ.E, V.prop_of_retract ⟨σ.ιE, σ.πE, σ.ιE_πE⟩ X.2⟩
  U := ⟨σ.U, V.prop_of_retract ⟨σ.ιU, σ.πU, σ.ιU_πU⟩ X.2⟩
  ιE := ObjectProperty.homMk σ.ιE
  πE := ObjectProperty.homMk σ.πE
  ιU := ObjectProperty.homMk σ.ιU
  πU := ObjectProperty.homMk σ.πU
  ιE_πE := ObjectProperty.hom_ext _ σ.ιE_πE
  ιU_πU := ObjectProperty.hom_ext _ σ.ιU_πU
  ιE_πU := ObjectProperty.hom_ext _ σ.ιE_πU
  ιU_πE := ObjectProperty.hom_ext _ σ.ιU_πE
  total := ObjectProperty.hom_ext _ σ.total

omit [IsAdditiveSub V] [V.IsStableUnderRetracts] in
lemma idemLE_iff {X : V.FullSubcategory} {e e' : X ⟶ X} : IdemLE e e' ↔ IdemLE e.hom e'.hom :=
  ⟨fun h ↦ ⟨congrArg (·.hom) h.1, congrArg (·.hom) h.2⟩,
    fun h ↦ ⟨ObjectProperty.hom_ext _ h.1, ObjectProperty.hom_ext _ h.2⟩⟩

/-- The restriction of `F` to a retract-closed additive subcategory `V`: `U ∩ V ⊂ V`. -/
def restrict : KaroubiFiltration (A.sub V) where
  U X := F.U X.obj
  additive :=
    { of_iso := fun e h ↦ F.U.prop_of_iso (V.ι.mapIso e) h
      exists_zero := by
        obtain ⟨Z, hZ, hU⟩ := F.U.exists_prop_of_containsZero
        refine ⟨⟨Z, V.prop_of_isZero hZ⟩, (IsZero.iff_id_eq_zero _).mpr
          (ObjectProperty.hom_ext _ (hZ.eq_of_src _ _)), hU⟩
      biprod_mem := fun b hb hX hY ↦ IsAdditiveSub.biprod_mem _ (isBilimitMap V.ι hb) hX hY }
  filt :=
    { splittings X := liftSplitting V '' F.filt.splittings X.obj
      mem := by
        rintro X _ ⟨σ, hσ, rfl⟩
        exact F.filt.mem _ σ hσ
      nonempty X := (F.filt.nonempty X.obj).image _
      directed := by
        rintro X _ ⟨σ, hσ, rfl⟩ _ ⟨τ, hτ, rfl⟩
        obtain ⟨ρ, hρ, h₁, h₂⟩ := F.filt.directed _ σ hσ τ hτ
        exact ⟨_, ⟨ρ, hρ, rfl⟩, (idemLE_iff V).mpr h₁, (idemLE_iff V).mpr h₂⟩
      factor_to := by
        intro W X hW f
        obtain ⟨σ, hσ, g, hg⟩ := F.filt.factor_to hW f.hom
        exact ⟨_, ⟨σ, hσ, rfl⟩, ObjectProperty.homMk g, ObjectProperty.hom_ext _ hg⟩
      factor_from := by
        intro X W hW f
        obtain ⟨σ, hσ, g, hg⟩ := F.filt.factor_from hW f.hom
        exact ⟨_, ⟨σ, hσ, rfl⟩, ObjectProperty.homMk g, ObjectProperty.hom_ext _ hg⟩
      sum := by
        intro X Y b hb
        obtain ⟨h₁, h₂⟩ := F.filt.sum _ (isBilimitMap V.ι hb)
        constructor
        · rintro _ ⟨σ, hσ, rfl⟩
          obtain ⟨α, hα, β, hβ, h⟩ := h₁ σ hσ
          exact ⟨_, ⟨α, hα, rfl⟩, _, ⟨β, hβ, rfl⟩, (idemLE_iff V).mpr h⟩
        · rintro _ ⟨α, hα, rfl⟩ _ ⟨β, hβ, rfl⟩
          obtain ⟨σ, hσ, h⟩ := h₂ α hα β hβ
          exact ⟨_, ⟨σ, hσ, rfl⟩, (idemLE_iff V).mpr h⟩ }
  star_ιE := by
    rintro X _ ⟨σ, hσ, rfl⟩
    exact ObjectProperty.hom_ext _ (F.star_ιE _ σ hσ)
  star_ιU := by
    rintro X _ ⟨σ, hσ, rfl⟩
    exact ObjectProperty.hom_ext _ (F.star_ιU _ σ hσ)

/-- The inclusion `(V ∩ U ⊂ V) → (U ⊂ A)`. -/
@[simps]
def restrictHom : FiltrationHom (F.restrict V) F := ⟨A.subIncl V, fun _ h ↦ h⟩

/-- For `U ⊆ V`, the subcategory of the restriction is strictly isomorphic to `U`. -/
def restrictSubIso (h : ∀ X, F.U X → V X) : (F.restrict V).sub ≅ F.sub where
  hom :=
    { F := F.U.lift ((F.restrict V).U.ι ⋙ V.ι) fun Z ↦ Z.2
      additive := ⟨ObjectProperty.hom_ext _ rfl⟩
      map_star _ := ObjectProperty.hom_ext _ rfl }
  inv :=
    { F := (F.restrict V).U.lift (V.lift F.U.ι fun Z ↦ h _ Z.2) fun Z ↦ Z.2
      additive := ⟨ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ rfl)⟩
      map_star _ := ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ rfl) }
  hom_inv_id := rfl
  inv_hom_id := rfl

end KaroubiFiltration

section Asymptotic

open Filter Topology AsymptoticCategory AsymptoticObject

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  {π : ∀ i, G i →* H} {X : Type} [MulAction H X] [PseudoEMetricSpace X]

variable (π X) in
/-- Transpose duality on `𝒜_G(X)`. -/
@[simps, implicit_reducible]
def asymptoticInvolution : StrictInvolution (AsymptoticCategory π X) where
  star := transpose
  star_comp := transpose_comp
  star_id := transpose_id
  star_add := transpose_add
  star_star := transpose_transpose

variable (π X) in
/-- `𝒜_G(X)` as an `InvCat`: based direct sums are unitary. -/
@[implicit_reducible] def asymptoticInvCat : InvCat where
  carrier := AsymptoticCategory π X
  inv := asymptoticInvolution π X
  unitary A B := ⟨{ toBinaryBicone := biprodBicone A B
                    isBilimit := isBinaryBilimitOfTotal _ (biprodBicone_total A B)
                    star_inl := rfl
                    star_inr := rfl }⟩

variable {S : Set X}

open scoped Classical in
/-- `A ∈ 𝒜_S(X)` iff `𝟙_A ∈ I_S`. -/
theorem supportProperty_iff_inIdeal_id {A : AsymptoticCategory π X} :
    supportProperty S A ↔ InIdeal S (𝟙 A) := by
  refine ⟨fun h ↦ ⟨A, h, 𝟙 A, 𝟙 A, by simp⟩, fun h ↦ ?_⟩
  have h₁ : InIdeal S (functor.map (𝟙 A.as)) := by
    rw [CategoryTheory.Functor.map_id]
    exact h
  have h' := (inIdeal_map_iff (𝟙 A.as)).mp h₁
  refine tendsto_zero_of_le h' fun i ↦ iSup_le fun b ↦ ?_
  have hb : (𝟙 A.as : A.as ⟶ A.as).1 i b b ≠ 0 := by
    change (1 : Matrix (Fin (A.as.rank i) × G i) (Fin (A.as.rank i) × G i) ℚ) b b ≠ 0
    simp
  exact ((endpointDist_le_iff.mp le_rfl) b b hb).1

instance (S : Set X) : IsAdditiveSub (supportProperty (π := π) S) where
  of_iso e hA := supportProperty_iff_inIdeal_id.mpr ⟨_, hA, e.inv, e.hom, e.inv_hom_id.symm⟩
  exists_zero := ⟨functor.obj zeroObj, functor.map_isZero isZero_zeroObj, isSupported_zeroObj⟩
  biprod_mem b hb hA hB := supportProperty_iff_inIdeal_id.mpr <| by
    rw [← IsBilimit.binary_total hb]
    exact InIdeal.add ⟨_, hA, _, _, rfl⟩ ⟨_, hB, _, _, rfl⟩

variable (π) in
/-- **Lemma 2.1** as a duality-compatible [CP95, 1.27] filtration: `𝒜_S(X) ⊂ 𝒜_G(X)`. -/
def supportKaroubiFiltration (S : Set X) : KaroubiFiltration (asymptoticInvCat π X) where
  U := supportProperty S
  additive := inferInstanceAs (IsAdditiveSub (supportProperty (π := π) S))
  filt := supportFiltration S
  star_ιE A σ hσ := (supportFiltration_transpose A σ hσ).1
  star_ιU A σ hσ := (supportFiltration_transpose A σ hσ).2

theorem supportKaroubiFiltration_sub_carrier :
    (supportKaroubiFiltration π S).sub.carrier = SupportCategory π S := rfl

/-- Smaller supports: `𝒜_S ⊂ 𝒜_T` for `S ⊆ T`. -/
def supportFiltrationHom {S T : Set X} (h : S ⊆ T) :
    FiltrationHom (supportKaroubiFiltration π S) (supportKaroubiFiltration π T) :=
  ⟨𝟙 _, fun _ hA ↦ IsSupported.mono h hA⟩

instance (S : Set X) : (supportKaroubiFiltration π S).U.IsStableUnderRetracts :=
  ⟨fun e h ↦ supportProperty_iff_inIdeal_id.mpr ⟨_, h, e.i, e.r, e.retract.symm⟩⟩

variable (π) in
/-- The support filtration `𝒜_Y ⊂ 𝒜_A` of the support category `𝒜_A`. -/
def supportRestrictFiltration (Y A : Set X) :
    KaroubiFiltration (supportKaroubiFiltration π A).sub :=
  (supportKaroubiFiltration π Y).restrict (supportKaroubiFiltration π A).U

/-- The map of filtrations `(𝒜_Y ⊂ 𝒜_A) → (𝒜_B ⊂ 𝒜)` for `Y ⊆ B`. -/
def supportRestrictHom {Y A B : Set X} (h : Y ⊆ B) :
    FiltrationHom (supportRestrictFiltration π Y A) (supportKaroubiFiltration π B) :=
  (KaroubiFiltration.restrictHom _ _).comp (supportFiltrationHom h)

/-- For `Y ⊆ A`, the subcategory `𝒜_Y` of `𝒜_A` is strictly isomorphic to `𝒜_Y`. -/
def supportRestrictSubIso {Y A : Set X} (h : Y ⊆ A) :
    (supportRestrictFiltration π Y A).sub ≅ (supportKaroubiFiltration π Y).sub :=
  KaroubiFiltration.restrictSubIso _ _ fun _ hZ ↦ IsSupported.mono h hZ

variable (π) in
/-- The exterior quotient `ℬ_Z(X) = 𝒜_G(X)/𝒜_Z(X)` as an `InvCat`. -/
abbrev exteriorInvCat (Z : Set X) : InvCat := (supportKaroubiFiltration π Z).quot

theorem exteriorInvCat_carrier (Z : Set X) : (exteriorInvCat π Z).carrier = ExteriorCategory π Z :=
  rfl

theorem exteriorInvCat_proj (Z : Set X) :
    (supportKaroubiFiltration π Z).proj.F = ExteriorCategory.functor := rfl

theorem exteriorInvCat_star {Z : Set X} {A B : AsymptoticCategory π X} (φ : A ⟶ B) :
    (exteriorInvCat π Z).inv.star (ExteriorCategory.functor.map φ) =
      ExteriorCategory.functor.map (transpose φ) := rfl

end Asymptotic

end

end HSFormal.LTheory
