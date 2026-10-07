import HSFormal.ControlledLinear
import Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Combinatorics.Quiver.Symmetric

/-!
# Transpose duality for the scalar controlled category

Matrix transpose preserves null propagation, reverses composition, and is an
involution. It gives an additive rational-linear equivalence from the opposite
category, including after quotienting by exact eventual equality.

This constructs the duality of based scalar matrix families. Duality of chain
complexes, Poincaré structures, support quotients, and L-theory are separate.
-/

noncomputable section

namespace HSFormal.ControlledObject

open Filter Matrix CategoryTheory Opposite

universe u

variable {X : Type u} [PseudoMetricSpace X]

theorem nullControlled_transpose (A B : ControlledObject X) (f : Family A B)
    (hf : NullControlled A B f) :
    NullControlled B A (fun i ↦ (f i).transpose) := by
  obtain ⟨ε, hεnonneg, hε, hfbound⟩ := hf
  refine ⟨ε, hεnonneg, hε, ?_⟩
  intro i
  exact hasPropagationLE_transpose (f i) (A.label i) (B.label i) (ε i) (hfbound i)

/-- Transpose with its actual null-control proof. -/
def controlledTranspose {A B : ControlledObject X} (f : A ⟶ B) : B ⟶ A :=
  ⟨fun i ↦ (f.val i).transpose, nullControlled_transpose A B f.val f.property⟩

@[simp]
theorem transpose_family {A B : ControlledObject X} (f : A ⟶ B) (i : ℕ) :
    (controlledTranspose f).val i = (f.val i).transpose := rfl

@[simp]
theorem controlledTranspose_transpose {A B : ControlledObject X} (f : A ⟶ B) :
    controlledTranspose (controlledTranspose f) = f := by
  apply Subtype.ext
  funext i
  exact Matrix.transpose_transpose (f.val i)

@[simp]
theorem controlledTranspose_id (A : ControlledObject X) :
    controlledTranspose (𝟙 A) = 𝟙 A := by
  apply Subtype.ext
  funext i
  exact Matrix.transpose_one

@[simp]
theorem controlledTranspose_comp {A B C : ControlledObject X}
    (f : A ⟶ B) (g : B ⟶ C) :
    controlledTranspose (f ≫ g) = controlledTranspose g ≫ controlledTranspose f := by
  apply Subtype.ext
  funext i
  exact Matrix.transpose_mul (g.val i) (f.val i)

@[simp]
theorem controlledTranspose_add {A B : ControlledObject X} (f g : A ⟶ B) :
    controlledTranspose (f + g) = controlledTranspose f + controlledTranspose g := by
  apply Subtype.ext
  funext i
  exact Matrix.transpose_add (f.val i) (g.val i)

@[simp]
theorem controlledTranspose_smul {A B : ControlledObject X} (c : ℚ) (f : A ⟶ B) :
    controlledTranspose (c • f) = c • controlledTranspose f := by
  apply Subtype.ext
  funext i
  exact Matrix.transpose_smul c (f.val i)

@[simp]
theorem controlledTranspose_scale {A B : ControlledObject X}
    (c : ℕ → ℚ) (f : A ⟶ B) :
    controlledTranspose (controlledScale c f) = controlledScale c (controlledTranspose f) := by
  apply Subtype.ext
  funext i
  exact Matrix.transpose_smul (c i) (f.val i)

instance controlledObjectInvolutiveReverse : Quiver.HasInvolutiveReverse (ControlledObject X) where
  reverse' := controlledTranspose
  inv' := controlledTranspose_transpose

/-- The opposite-category functor has the original metric-labelled object as its dual. -/
def transposeFunctor : (ControlledObject X)ᵒᵖ ⥤ ControlledObject X where
  obj := Opposite.unop
  map f := controlledTranspose f.unop
  map_id A := by simp
  map_comp f g := by simp

instance transposeFunctor_additive : (transposeFunctor (X := X)).Additive where
  map_add := by
    intro A B f g
    exact controlledTranspose_add f.unop g.unop

instance controlledObjectOppositeHomModule (A B : (ControlledObject X)ᵒᵖ) :
    Module ℚ (A ⟶ B) := AddEquiv.module ℚ { opEquiv A B with map_add' := fun _ _ => rfl }

@[simp]
theorem controlledObject_unop_smul {A B : (ControlledObject X)ᵒᵖ} (c : ℚ) (f : A ⟶ B) :
    (c • f).unop = c • f.unop := rfl

instance controlledObjectOppositeLinear : CategoryTheory.Linear ℚ (ControlledObject X)ᵒᵖ where
  smul_comp A B C c f g := by
    apply Quiver.Hom.unop_inj
    exact CategoryTheory.Linear.comp_smul _ _ _ g.unop c f.unop
  comp_smul A B C f c g := by
    apply Quiver.Hom.unop_inj
    exact CategoryTheory.Linear.smul_comp _ _ _ c g.unop f.unop

instance transposeFunctor_linear : (transposeFunctor (X := X)).Linear ℚ := inferInstance

/-- Transpose is an equivalence, with the same transpose supplying its inverse. -/
def transposeEquivalence : (ControlledObject X)ᵒᵖ ≌ ControlledObject X where
  functor := transposeFunctor
  inverse := (transposeFunctor (X := X)).rightOp
  unitIso := NatIso.ofComponents (fun A ↦ Iso.refl A) (by
    intro A B f
    apply Quiver.Hom.unop_inj
    simp [transposeFunctor])
  counitIso := NatIso.ofComponents (fun A ↦ Iso.refl A) (by
    intro A B f
    simp [transposeFunctor])
  functor_unitIso_comp A := by simp [transposeFunctor, NatIso.ofComponents]

instance transposeEquivalence_inverse_additive :
    (transposeEquivalence (X := X)).inverse.Additive :=
  inferInstanceAs ((transposeFunctor (X := X)).rightOp.Additive)

instance transposeEquivalence_inverse_linear :
    (transposeEquivalence (X := X)).inverse.Linear ℚ := inferInstance

theorem eventualEquality_transpose {A B : ControlledObject X} {f g : A ⟶ B}
    (h : eventualEquality f g) :
    eventualEquality (controlledTranspose f) (controlledTranspose g) := by
  filter_upwards [h] with i hi
  exact congrArg Matrix.transpose hi

/-- Exact eventual equality, including its congruence closure, respects transpose. -/
def tailTranspose {A B : TailCategory X} (f : A ⟶ B) : B ⟶ A :=
  Quot.liftOn f (fun g ↦ Quot.mk _ (controlledTranspose g)) (by
    intro g h hgh
    apply Quot.sound
    rw [HomRel.compClosure_eq_self] at hgh ⊢
    exact eventualEquality_transpose hgh)

@[simp]
theorem tailTranspose_map {A B : ControlledObject X} (f : A ⟶ B) :
    tailTranspose ((tailFunctor (X := X)).map f) =
      (tailFunctor (X := X)).map (controlledTranspose f) := rfl

@[simp]
theorem tailTranspose_transpose {A B : TailCategory X} (f : A ⟶ B) :
    tailTranspose (tailTranspose f) = f := by
  obtain ⟨f, rfl⟩ := (CategoryTheory.Quotient.functor (eventualEquality (X := X))).map_surjective f
  change tailTranspose (tailTranspose ((tailFunctor (X := X)).map f)) =
    (tailFunctor (X := X)).map f
  rw [tailTranspose_map, tailTranspose_map, controlledTranspose_transpose]

@[simp]
theorem tailTranspose_id (A : TailCategory X) :
    tailTranspose (𝟙 A) = 𝟙 A := by
  change tailTranspose ((tailFunctor (X := X)).map (𝟙 A.as)) =
    (tailFunctor (X := X)).map (𝟙 A.as)
  rw [tailTranspose_map, controlledTranspose_id]

@[simp]
theorem tailTranspose_comp {A B C : TailCategory X} (f : A ⟶ B) (g : B ⟶ C) :
    tailTranspose (f ≫ g) = tailTranspose g ≫ tailTranspose f := by
  obtain ⟨f, rfl⟩ := (CategoryTheory.Quotient.functor (eventualEquality (X := X))).map_surjective f
  obtain ⟨g, rfl⟩ := (CategoryTheory.Quotient.functor (eventualEquality (X := X))).map_surjective g
  change tailTranspose ((tailFunctor (X := X)).map f ≫ (tailFunctor (X := X)).map g) =
    tailTranspose ((tailFunctor (X := X)).map g) ≫ tailTranspose ((tailFunctor (X := X)).map f)
  rw [← Functor.map_comp, tailTranspose_map, controlledTranspose_comp, Functor.map_comp,
    tailTranspose_map, tailTranspose_map]

@[simp]
theorem tailTranspose_add {A B : TailCategory X} (f g : A ⟶ B) :
    tailTranspose (f + g) = tailTranspose f + tailTranspose g := by
  obtain ⟨f, rfl⟩ := (CategoryTheory.Quotient.functor (eventualEquality (X := X))).map_surjective f
  obtain ⟨g, rfl⟩ := (CategoryTheory.Quotient.functor (eventualEquality (X := X))).map_surjective g
  change tailTranspose ((tailFunctor (X := X)).map f + (tailFunctor (X := X)).map g) =
    tailTranspose ((tailFunctor (X := X)).map f) + tailTranspose ((tailFunctor (X := X)).map g)
  rw [← Functor.map_add, tailTranspose_map, controlledTranspose_add, Functor.map_add,
    tailTranspose_map, tailTranspose_map]

@[simp]
theorem tailTranspose_smul {A B : TailCategory X} (c : ℚ) (f : A ⟶ B) :
    tailTranspose (c • f) = c • tailTranspose f := by
  obtain ⟨f, rfl⟩ := (CategoryTheory.Quotient.functor (eventualEquality (X := X))).map_surjective f
  change tailTranspose (c • (tailFunctor (X := X)).map f) =
    c • tailTranspose ((tailFunctor (X := X)).map f)
  rw [← Functor.map_smul, tailTranspose_map, controlledTranspose_smul, Functor.map_smul,
    tailTranspose_map]

instance tailCategoryInvolutiveReverse : Quiver.HasInvolutiveReverse (TailCategory X) where
  reverse' := tailTranspose
  inv' := tailTranspose_transpose

def tailTransposeFunctor : (TailCategory X)ᵒᵖ ⥤ TailCategory X where
  obj := Opposite.unop
  map f := tailTranspose f.unop
  map_id A := by simp
  map_comp f g := by simp

instance tailTransposeFunctor_additive : (tailTransposeFunctor (X := X)).Additive where
  map_add := by
    intro A B f g
    exact tailTranspose_add f.unop g.unop

instance tailCategoryOppositeHomModule (A B : (TailCategory X)ᵒᵖ) :
    Module ℚ (A ⟶ B) := AddEquiv.module ℚ { opEquiv A B with map_add' := fun _ _ => rfl }

@[simp]
theorem tailCategory_unop_smul {A B : (TailCategory X)ᵒᵖ} (c : ℚ) (f : A ⟶ B) :
    (c • f).unop = c • f.unop := rfl

instance tailCategoryOppositeLinear : CategoryTheory.Linear ℚ (TailCategory X)ᵒᵖ where
  smul_comp A B C c f g := by
    apply Quiver.Hom.unop_inj
    exact CategoryTheory.Linear.comp_smul _ _ _ g.unop c f.unop
  comp_smul A B C f c g := by
    apply Quiver.Hom.unop_inj
    exact CategoryTheory.Linear.smul_comp _ _ _ c g.unop f.unop

instance tailTransposeFunctor_linear : (tailTransposeFunctor (X := X)).Linear ℚ := inferInstance

def tailTransposeEquivalence : (TailCategory X)ᵒᵖ ≌ TailCategory X where
  functor := tailTransposeFunctor
  inverse := (tailTransposeFunctor (X := X)).rightOp
  unitIso := NatIso.ofComponents (fun A ↦ Iso.refl A) (by
    intro A B f
    apply Quiver.Hom.unop_inj
    simp [tailTransposeFunctor])
  counitIso := NatIso.ofComponents (fun A ↦ Iso.refl A) (by
    intro A B f
    simp [tailTransposeFunctor])
  functor_unitIso_comp A := by simp [tailTransposeFunctor, NatIso.ofComponents]

instance tailTransposeEquivalence_inverse_additive :
    (tailTransposeEquivalence (X := X)).inverse.Additive :=
  inferInstanceAs ((tailTransposeFunctor (X := X)).rightOp.Additive)

instance tailTransposeEquivalence_inverse_linear :
    (tailTransposeEquivalence (X := X)).inverse.Linear ℚ := inferInstance

/-- The checked eventual quotient commutes with the actual duality functors. -/
def tailFunctorTransposeIso :
    transposeFunctor ⋙ (tailFunctor (X := X)) ≅
      (tailFunctor (X := X)).op ⋙ tailTransposeFunctor :=
  NatIso.ofComponents (fun A ↦ Iso.refl _) (by
    intro A B f
    simp [transposeFunctor, tailTransposeFunctor])

end HSFormal.ControlledObject
