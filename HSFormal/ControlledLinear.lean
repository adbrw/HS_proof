import HSFormal.ControlledCategory
import Mathlib.CategoryTheory.Quotient.Linear

/-!
# Rational linearity of the scalar controlled category

Rational matrix scaling is compatible with composition and eventual equality.
The existing quotient construction therefore gives rational modules on tail
morphism groups and a rational-linear quotient functor. Coefficients have no
size bounds. Equivariant labels, support ideals, duality, and L-theory are still
separate constructions.
-/

noncomputable section

namespace HSFormal.ControlledObject

open Filter Matrix CategoryTheory

universe u

variable {X : Type u} [PseudoMetricSpace X]

instance controlledObjectLinear : CategoryTheory.Linear ℚ (ControlledObject X) where
  homModule A B := inferInstanceAs (Module ℚ (Hom A B))
  smul_comp A B C c f g := by
    apply Subtype.ext
    funext i
    exact Matrix.mul_smul (g.val i) c (f.val i)
  comp_smul A B C f c g := by
    apply Subtype.ext
    funext i
    exact Matrix.smul_mul c (g.val i) (f.val i)

theorem eventualEquality_smul {A B : ControlledObject X}
    (c : ℚ) {f g : A ⟶ B} (h : eventualEquality f g) :
    eventualEquality (c • f) (c • g) := by
  filter_upwards [h] with i hi
  exact congrArg (fun M ↦ c • M) hi

instance tailCategoryLinear : CategoryTheory.Linear ℚ (TailCategory X) := by
  letI : (CategoryTheory.Quotient.functor (eventualEquality (X := X))).Additive :=
    tailFunctor_additive (X := X)
  exact CategoryTheory.Quotient.linear ℚ (eventualEquality (X := X))
    (fun c {_ _} f g h ↦ eventualEquality_smul c h)

instance tailFunctor_linear : (tailFunctor (X := X)).Linear ℚ :=
  inferInstance

@[simp]
theorem tailFunctor_map_smul {A B : ControlledObject X} (c : ℚ) (f : A ⟶ B) :
    (tailFunctor (X := X)).map (c • f) = c • (tailFunctor (X := X)).map f := by
  exact (tailFunctor (X := X)).map_smul c f

end HSFormal.ControlledObject
