import HSFormal.LTheory.Model.NegK.KarSwindle
import Mathlib.CategoryTheory.Idempotents.Biproducts

/-!
# Stable isomorphism of Kar objects (NegKHigh, module N2)

`blueprint/negK-high.md` §2 "Stable isomorphism", §7 row N2.

For an additive category `V` (preadditive with finite biproducts) and `P Q : Karoubi V`,
`StablyIso P Q` means `P ⊞ F ≅ Q ⊞ F'` for objects `F, F'` of `V` ("free" Kar objects
`toKaroubi V`).  This is equality of classes in `K₀(Kar V) / im K₀(V)`.

* `StablyIso` is an equivalence relation (`refl`, `symm`, `trans`), compatible with `⊞`
  (`StablyIso.biprod`), implied by isomorphisms (`of_iso`) and by Kar isomorphisms of raw
  idempotents (`of_karIso`, `Wall.KarIso`), and preserved by additive functors
  (`StablyIso.map`, along `karoubiMap Φ : Karoubi V ⥤ Karoubi W`).
* Free objects are stably zero (`toKaroubi_stablyIso_zero`) and may be added or cancelled
  (`biprod_free`, `stablyIso_biprod_free_iff`).
* `stablyIso_zero_iff`: `P ∼ 0` iff `KarStablyFree P.p F F'` for some `F, F'` (`NegK.lean`);
  absorbed objects (`KarAbsorbs`) are `∼ 0` (`of_karAbsorbs`).
* `karoubiBiconeIso`: for any bicone `b` on `X, Y`, the Kar object
  `(b.pt, b.fst p b.inl + b.snd q b.inr)` (`biconeKar`) is the Karoubi biproduct of `(X, p)` and
  `(Y, q)`; in particular a splitting decomposes Kar objects commuting with it
  (`Splitting.bicone`).
* `StablyIso.of_biprod_complement`: `P ⊞ (Q.X, 1 - Q.p) ∼ 0` implies `P ∼ Q`.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive Idempotents

noncomputable section

universe v u v' u'

section

variable {V : Type u} [Category.{v} V] [Preadditive V] [HasFiniteBiproducts V]

/-- Binary biproducts in `Karoubi V`. -/
instance karoubi_hasBinaryBiproducts : HasBinaryBiproducts (Karoubi V) :=
  hasBinaryBiproducts_of_finite_biproducts _

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

open ZeroObject

/-- **Stable isomorphism** of Kar objects: `P ⊞ F ≅ Q ⊞ F'` in `Karoubi V` for objects `F, F'` of
`V`. -/
def StablyIso (P Q : Karoubi V) : Prop :=
  ∃ F F' : V, Nonempty (P ⊞ (toKaroubi V).obj F ≅ Q ⊞ (toKaroubi V).obj F')

/-- `toKaroubi` preserves binary biproducts. -/
def toKaroubiBiprodIso (F G : V) :
    (toKaroubi V).obj (F ⊞ G) ≅ (toKaroubi V).obj F ⊞ (toKaroubi V).obj G :=
  have := preservesBinaryBiproducts_of_preservesBiproducts (toKaroubi V)
  (toKaroubi V).mapBiprod F G

lemma isZero_toKaroubi_zero : IsZero ((toKaroubi V).obj 0) :=
  (toKaroubi V).map_isZero (isZero_zero V)

/-- `(A ⊞ B) ⊞ C ≅ (A ⊞ C) ⊞ B`. -/
def biprodSwap {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C] (A B E : C) :
    (A ⊞ B) ⊞ E ≅ (A ⊞ E) ⊞ B :=
  biprod.associator A B E ≪≫ biprod.mapIso (Iso.refl A) (biprod.braiding B E) ≪≫
    (biprod.associator A E B).symm

namespace StablyIso

variable {P Q R P' Q' : Karoubi V}

lemma of_iso (e : P ≅ Q) : StablyIso P Q :=
  ⟨0, 0, ⟨biprod.mapIso e (Iso.refl _)⟩⟩

@[refl]
lemma refl (P : Karoubi V) : StablyIso P P := of_iso (Iso.refl P)

@[symm]
lemma symm (h : StablyIso P Q) : StablyIso Q P :=
  let ⟨F, F', ⟨e⟩⟩ := h
  ⟨F', F, ⟨e.symm⟩⟩

@[trans]
lemma trans (h₁ : StablyIso P Q) (h₂ : StablyIso Q R) : StablyIso P R := by
  obtain ⟨F, F', ⟨e₁⟩⟩ := h₁
  obtain ⟨G, G', ⟨e₂⟩⟩ := h₂
  refine ⟨F ⊞ G, G' ⊞ F', ⟨?_⟩⟩
  exact biprod.mapIso (Iso.refl P) (toKaroubiBiprodIso F G) ≪≫
    (biprod.associator _ _ _).symm ≪≫ biprod.mapIso e₁ (Iso.refl _) ≪≫
    biprodSwap _ _ _ ≪≫ biprod.mapIso e₂ (Iso.refl _) ≪≫ biprod.associator _ _ _ ≪≫
    biprod.mapIso (Iso.refl R) (toKaroubiBiprodIso G' F').symm

lemma biprod_right (h : StablyIso P Q) (R : Karoubi V) : StablyIso (P ⊞ R) (Q ⊞ R) := by
  obtain ⟨F, F', ⟨e⟩⟩ := h
  exact ⟨F, F', ⟨biprodSwap _ _ _ ≪≫ biprod.mapIso e (Iso.refl R) ≪≫ biprodSwap _ _ _⟩⟩

lemma biprod_left (R : Karoubi V) (h : StablyIso P Q) : StablyIso (R ⊞ P) (R ⊞ Q) :=
  ((of_iso (biprod.braiding R P)).trans (h.biprod_right R)).trans
    (of_iso (biprod.braiding Q R))

/-- `∼` is compatible with `⊞`. -/
lemma biprod (h₁ : StablyIso P Q) (h₂ : StablyIso P' Q') : StablyIso (P ⊞ P') (Q ⊞ Q') :=
  (h₁.biprod_right P').trans (biprod_left Q h₂)

lemma biprod_comm (P Q : Karoubi V) : StablyIso (P ⊞ Q) (Q ⊞ P) :=
  of_iso (biprod.braiding P Q)

lemma biprod_assoc (P Q R : Karoubi V) : StablyIso ((P ⊞ Q) ⊞ R) (P ⊞ (Q ⊞ R)) :=
  of_iso (biprod.associator P Q R)

/-- Adding a free summand does not change the stable class. -/
lemma biprod_free (P : Karoubi V) (F : V) : StablyIso (P ⊞ (toKaroubi V).obj F) P :=
  ⟨0, F, ⟨(isoBiprodZero isZero_toKaroubi_zero).symm⟩⟩

lemma zero_biprod (P : Karoubi V) : StablyIso (0 ⊞ P) P :=
  of_iso (isoZeroBiprod (isZero_zero _)).symm

lemma biprod_zero (P : Karoubi V) : StablyIso (P ⊞ 0) P :=
  of_iso (isoBiprodZero (isZero_zero _)).symm

lemma stablyIso_biprod_free_iff (F : V) :
    StablyIso (P ⊞ (toKaroubi V).obj F) Q ↔ StablyIso P Q :=
  ⟨fun h ↦ (biprod_free P F).symm.trans h, fun h ↦ (biprod_free P F).trans h⟩

lemma of_isZero {P Q : Karoubi V} (hP : IsZero P) (hQ : IsZero Q) : StablyIso P Q :=
  of_iso (hP.iso hQ)

end StablyIso

/-- Free objects are stably zero. -/
lemma toKaroubi_stablyIso_zero (F : V) : StablyIso ((toKaroubi V).obj F) 0 :=
  (StablyIso.zero_biprod _).symm.trans (StablyIso.biprod_free 0 F)

/-- **Stably zero = stably free** (`KarStablyFree`, `NegK.lean`). -/
theorem stablyIso_zero_iff (P : Karoubi V) :
    StablyIso P 0 ↔ ∃ F F' : V, KarStablyFree P.p F F' := by
  constructor
  · rintro ⟨F, F', ⟨e⟩⟩
    exact ⟨F, F', (karStablyFree_iff P F F').mpr ⟨e ≪≫ (isoZeroBiprod (isZero_zero _)).symm⟩⟩
  · rintro ⟨F, F', h⟩
    obtain ⟨e⟩ := (karStablyFree_iff P F F').mp h
    exact ⟨F, F', ⟨e ≪≫ isoZeroBiprod (isZero_zero _)⟩⟩

/-- Absorbed Kar objects are stably zero. -/
lemma StablyIso.of_karAbsorbs {P : Karoubi V} {F : V} (h : KarAbsorbs P.p F) : StablyIso P 0 :=
  (stablyIso_zero_iff P).mpr ⟨F, F, h⟩

/-- Stably zero objects are stably isomorphic to every free object. -/
lemma stablyIso_zero_iff_free (P : Karoubi V) (F : V) :
    StablyIso P 0 ↔ StablyIso P ((toKaroubi V).obj F) :=
  ⟨fun h ↦ h.trans (toKaroubi_stablyIso_zero F).symm,
    fun h ↦ h.trans (toKaroubi_stablyIso_zero F)⟩

/-! ### Kar isomorphisms and bicones -/

/-- A Kar isomorphism of raw idempotents is an isomorphism in `Karoubi V`. -/
@[simps]
def karoubiIsoOfKarIso {X Y : V} {p : X ⟶ X} {q : Y ⟶ Y} (hp : p ≫ p = p) (hq : q ≫ q = q)
    (α : Wall.KarIso p q) : (⟨X, p, hp⟩ : Karoubi V) ≅ ⟨Y, q, hq⟩ where
  hom := ⟨α.hom, by simp⟩
  inv := ⟨α.inv, by simp⟩
  hom_inv_id := by ext; exact α.hom_inv
  inv_hom_id := by ext; exact α.inv_hom

lemma StablyIso.of_karIso {X Y : V} {p : X ⟶ X} {q : Y ⟶ Y} (hp : p ≫ p = p) (hq : q ≫ q = q)
    (α : Wall.KarIso p q) : StablyIso ⟨X, p, hp⟩ ⟨Y, q, hq⟩ :=
  of_iso (karoubiIsoOfKarIso hp hq α)

section Bicone

variable {X Y : V} (b : BinaryBicone X Y) {p : X ⟶ X} {q : Y ⟶ Y} (hp : p ≫ p = p)
  (hq : q ≫ q = q)

omit [HasFiniteBiproducts V] in
include hp hq in
lemma bicone_idem : (b.fst ≫ p ≫ b.inl + b.snd ≫ q ≫ b.inr) ≫
    (b.fst ≫ p ≫ b.inl + b.snd ≫ q ≫ b.inr) = b.fst ≫ p ≫ b.inl + b.snd ≫ q ≫ b.inr := by
  simp [add_comp, comp_add, reassoc_of% hp, reassoc_of% hq]

/-- The Kar object `(b.pt, b.fst ≫ p ≫ b.inl + b.snd ≫ q ≫ b.inr)` of a bicone. -/
@[simps, implicit_reducible]
def biconeKar : Karoubi V := ⟨b.pt, _, bicone_idem b hp hq⟩

/-- The bicone in `Karoubi V` exhibiting `biconeKar` as a sum of `(X, p)` and `(Y, q)`. -/
@[simps]
def biconeKarBicone : BinaryBicone (⟨X, p, hp⟩ : Karoubi V) ⟨Y, q, hq⟩ where
  pt := biconeKar b hp hq
  fst := ⟨b.fst ≫ p, by rw [biconeKar_p]; simp [add_comp, hp]⟩
  snd := ⟨b.snd ≫ q, by rw [biconeKar_p]; simp [add_comp, hq]⟩
  inl := ⟨p ≫ b.inl, by rw [biconeKar_p]; simp [comp_add, reassoc_of% hp]⟩
  inr := ⟨q ≫ b.inr, by rw [biconeKar_p]; simp [comp_add, reassoc_of% hq]⟩
  inl_fst := by ext; simp [hp]
  inl_snd := by ext; simp
  inr_fst := by ext; simp
  inr_snd := by ext; simp [hq]

omit [HasFiniteBiproducts V] in
lemma biconeKarBicone_total :
    (biconeKarBicone b hp hq).fst ≫ (biconeKarBicone b hp hq).inl +
      (biconeKarBicone b hp hq).snd ≫ (biconeKarBicone b hp hq).inr = 𝟙 _ := by
  ext
  change (b.fst ≫ p) ≫ (p ≫ b.inl) + (b.snd ≫ q) ≫ (q ≫ b.inr) = b.fst ≫ p ≫ b.inl + b.snd ≫ q ≫ b.inr
  simp [reassoc_of% hp, reassoc_of% hq]

/-- **Sums along bicones**: `(b.pt, b.fst p b.inl + b.snd q b.inr) ≅ (X, p) ⊞ (Y, q)` in
`Karoubi V`, for any bicone `b` (no totality is needed: the idempotent cuts out the sum). -/
def karoubiBiconeIso : biconeKar b hp hq ≅ (⟨X, p, hp⟩ : Karoubi V) ⊞ ⟨Y, q, hq⟩ :=
  biprod.uniqueUpToIso _ _ (isBinaryBilimitOfTotal _ (biconeKarBicone_total b hp hq))

lemma StablyIso.biconeKar_iff {P : Karoubi V} :
    StablyIso (biconeKar b hp hq) P ↔ StablyIso ((⟨X, p, hp⟩ : Karoubi V) ⊞ ⟨Y, q, hq⟩) P :=
  ⟨(of_iso (karoubiBiconeIso b hp hq)).symm.trans, (of_iso (karoubiBiconeIso b hp hq)).trans⟩

end Bicone

/-- The bicone of a splitting `Q = E ⊕ U` (`pt = Q`). -/
@[simps]
def _root_.HSFormal.Splitting.bicone {Q : V} (σ : Splitting Q) : BinaryBicone σ.E σ.U where
  pt := Q
  fst := σ.πE
  snd := σ.πU
  inl := σ.ιE
  inr := σ.ιU
  inl_fst := σ.ιE_πE
  inl_snd := σ.ιE_πU
  inr_fst := σ.ιU_πE
  inr_snd := σ.ιU_πU

/-- `(X, p) ⊞ (X, 1 - p) ≅ X`, so `P ⊞ P.complement` is free. -/
lemma StablyIso.biprod_complement (P : Karoubi V) :
    StablyIso (P ⊞ P.complement) ((toKaroubi V).obj P.X) :=
  of_iso P.decomposition

/-- **Cancellation**: if `P ⊞ (Q.X, 1 - Q.p)` is stably zero, then `P ∼ Q`. -/
lemma StablyIso.of_biprod_complement {P Q : Karoubi V} (h : StablyIso (P ⊞ Q.complement) 0) :
    StablyIso P Q :=
  ((((((biprod_free P Q.X).symm.trans (biprod_left P (biprod_complement Q).symm)).trans
    (biprod_left P (biprod_comm Q Q.complement))).trans
      (biprod_assoc P Q.complement Q).symm).trans (h.biprod_right Q)).trans (zero_biprod Q))

/-! ### Additive functors -/

section Map

variable {W : Type u'} [Category.{v'} W] [Preadditive W] [HasFiniteBiproducts W]

/-- The extension `Kar Φ : Karoubi V ⥤ Karoubi W` of a functor `Φ : V ⥤ W`. -/
@[simps, implicit_reducible]
def karoubiMap (Φ : V ⥤ W) : Karoubi V ⥤ Karoubi W where
  obj P := ⟨Φ.obj P.X, Φ.map P.p, by rw [← Φ.map_comp, P.idem]⟩
  map {P Q} f := ⟨Φ.map f.f, by
    change Φ.map P.p ≫ Φ.map f.f ≫ Φ.map Q.p = _
    rw [← Φ.map_comp, ← Φ.map_comp, f.comm]⟩
  map_id P := by ext; simp
  map_comp f g := by ext; simp

instance (Φ : V ⥤ W) [Φ.Additive] : (karoubiMap Φ).Additive where
  map_add {_ _ f g} := by ext; exact Φ.map_add

/-- `Kar Φ` maps free objects to free objects. -/
def karoubiMapToKaroubiIso (Φ : V ⥤ W) (F : V) :
    (karoubiMap Φ).obj ((toKaroubi V).obj F) ≅ (toKaroubi W).obj (Φ.obj F) where
  hom := ⟨𝟙 _, by change Φ.map (𝟙 F) ≫ 𝟙 _ ≫ 𝟙 _ = _; simp⟩
  inv := ⟨𝟙 _, by change 𝟙 _ ≫ 𝟙 _ ≫ Φ.map (𝟙 F) = _; simp⟩
  hom_inv_id := by ext; change 𝟙 _ ≫ 𝟙 _ = Φ.map (𝟙 F); simp
  inv_hom_id := by ext; simp

/-- **Additive functors preserve stable isomorphism.** -/
lemma StablyIso.map (Φ : V ⥤ W) [Φ.Additive] {P Q : Karoubi V} (h : StablyIso P Q) :
    StablyIso ((karoubiMap Φ).obj P) ((karoubiMap Φ).obj Q) := by
  have := preservesBinaryBiproducts_of_preservesBiproducts (karoubiMap Φ)
  obtain ⟨F, F', ⟨e⟩⟩ := h
  exact ⟨Φ.obj F, Φ.obj F', ⟨biprod.mapIso (Iso.refl _) (karoubiMapToKaroubiIso Φ F).symm ≪≫
    ((karoubiMap Φ).mapBiprod _ _).symm ≪≫ (karoubiMap Φ).mapIso e ≪≫ (karoubiMap Φ).mapBiprod _ _ ≪≫
    biprod.mapIso (Iso.refl _) (karoubiMapToKaroubiIso Φ F')⟩⟩

/-- A functor isomorphic to the identity preserves stable classes (e.g. reindexings of `C_ℤ`
at bounded distance, lifted by `Lpow.mapNatIso`). -/
lemma StablyIso.karoubiMap_of_iso {Φ : V ⥤ V} (η : Φ ≅ 𝟭 V) (P : Karoubi V) :
    StablyIso ((karoubiMap Φ).obj P) P := by
  have hΦ : Φ.map P.p ≫ Φ.map P.p = Φ.map P.p := by rw [← Φ.map_comp, P.idem]
  have nat : Φ.map P.p ≫ η.hom.app P.X = η.hom.app P.X ≫ P.p := η.hom.naturality P.p
  refine StablyIso.of_karIso (X := Φ.obj P.X) hΦ P.idem (CZ.karIsoOfFactor hΦ P.idem
    (η.hom.app P.X ≫ P.p) (P.p ≫ η.inv.app P.X) ?_ ?_)
  · rw [assoc, P.idem_assoc, ← reassoc_of% nat, Iso.hom_inv_id_app, comp_id]
  · rw [assoc, Iso.inv_hom_id_app_assoc, P.idem]

/-- `StablyIso.map` for raw idempotents. -/
lemma StablyIso.map' (Φ : V ⥤ W) [Φ.Additive] {X Y : V} {p : X ⟶ X} {q : Y ⟶ Y}
    (hp : p ≫ p = p) (hq : q ≫ q = q) (h : StablyIso ⟨X, p, hp⟩ ⟨Y, q, hq⟩) :
    StablyIso (⟨Φ.obj X, Φ.map p, by rw [← Φ.map_comp, hp]⟩ : Karoubi W)
      ⟨Φ.obj Y, Φ.map q, by rw [← Φ.map_comp, hq]⟩ :=
  h.map Φ

end Map

end

end

end HSFormal.LTheory
