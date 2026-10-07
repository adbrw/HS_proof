import HSFormal.ControlledMatrices
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.CategoryTheory.Quotient.Preadditive

/-!
# A scalar category of asymptotically controlled rational matrices

Objects have a finite labelled basis at every index, with no uniform rank
bound. Morphisms admit nonnegative propagation bounds tending to zero.
The category is preadditive, and its tail quotient identifies exactly matrix
families that agree at every sufficiently large index.

This is the scalar metric-label model of manuscript Section 2. Equivariant free
bases, support ideals, duality, Karoubi filtrations, finite biproducts, and
Poincaré/L-theory constructions are not asserted here.
-/

noncomputable section

namespace HSFormal

open Filter Matrix CategoryTheory
open scoped Classical

universe u

/-- A small based model allowing the rank to vary without bound. -/
structure ControlledObject (X : Type u) where
  rank : ℕ → ℕ
  label : ∀ i, Fin (rank i) → X

namespace ControlledObject

variable {X : Type u} [PseudoMetricSpace X]

/-- Rectangular matrix families, with target rows and source columns. -/
abbrev Family (A B : ControlledObject X) : Type :=
  ∀ i, Matrix (Fin (B.rank i)) (Fin (A.rank i)) ℚ

/-- Honest null control, with a nonnegative bound at every index. -/
def NullControlled (A B : ControlledObject X) (f : Family A B) : Prop :=
  ∃ ε : ℕ → ℝ, (∀ i, 0 ≤ ε i) ∧ Tendsto ε atTop (nhds 0) ∧
    ∀ i, HasPropagationLE (f i) (A.label i) (B.label i) (ε i)

theorem nullControlled_zero (A B : ControlledObject X) :
    NullControlled A B 0 := by
  refine ⟨fun _ ↦ 0, fun _ ↦ le_rfl, tendsto_const_nhds, ?_⟩
  intro i b a hba
  exact (hba rfl).elim

theorem nullControlled_id (A : ControlledObject X) :
    NullControlled A A (fun i ↦ (1 : Matrix (Fin (A.rank i)) (Fin (A.rank i)) ℚ)) := by
  refine ⟨fun _ ↦ 0, fun _ ↦ le_rfl, tendsto_const_nhds, ?_⟩
  intro i
  simp [HasPropagationLE, MatrixSupportedBy, Matrix.one_apply]

theorem nullControlled_add (A B : ControlledObject X) (f g : Family A B)
    (hf : NullControlled A B f) (hg : NullControlled A B g) :
    NullControlled A B (f + g) := by
  obtain ⟨ε, hεnonneg, hε, hfbound⟩ := hf
  obtain ⟨δ, hδnonneg, hδ, hgbound⟩ := hg
  refine ⟨fun i ↦ max (ε i) (δ i), ?_, ?_, ?_⟩
  · intro i
    exact (hεnonneg i).trans (le_max_left _ _)
  · simpa using hε.max hδ
  · intro i
    exact hasPropagationLE_add (f i) (g i) (A.label i) (B.label i)
      (ε i) (δ i) (hfbound i) (hgbound i)

theorem nullControlled_neg (A B : ControlledObject X) (f : Family A B)
    (hf : NullControlled A B f) : NullControlled A B (-f) := by
  obtain ⟨ε, hεnonneg, hε, hfbound⟩ := hf
  refine ⟨ε, hεnonneg, hε, ?_⟩
  intro i b a hba
  change -(f i b a) ≠ 0 at hba
  exact hfbound i b a (neg_ne_zero.mp hba)

/-- Arbitrary rational coefficient sequences preserve the same null bound. This
includes the varying normalization factors of manuscript Lemma 5.2. -/
theorem nullControlled_scale (A B : ControlledObject X) (c : ℕ → ℚ) (f : Family A B)
    (hf : NullControlled A B f) :
    NullControlled A B (fun i ↦ c i • f i) := by
  obtain ⟨ε, hεnonneg, hε, hfbound⟩ := hf
  refine ⟨ε, hεnonneg, hε, ?_⟩
  intro i b a hba
  change c i * f i b a ≠ 0 at hba
  exact hfbound i b a (right_ne_zero_of_mul hba)

/-- Rational coefficients do not enlarge matrix support. -/
theorem nullControlled_smul (A B : ControlledObject X) (c : ℚ) (f : Family A B)
    (hf : NullControlled A B f) : NullControlled A B (c • f) := by
  exact nullControlled_scale A B (fun _ ↦ c) f hf

theorem nullControlled_comp (A B C : ControlledObject X)
    (f : Family A B) (g : Family B C)
    (hf : NullControlled A B f) (hg : NullControlled B C g) :
    NullControlled A C (fun i ↦ g i * f i) := by
  obtain ⟨ε, hεnonneg, hε, hfbound⟩ := hf
  obtain ⟨δ, hδnonneg, hδ, hgbound⟩ := hg
  refine ⟨fun i ↦ ε i + δ i, ?_, ?_, ?_⟩
  · intro i
    exact add_nonneg (hεnonneg i) (hδnonneg i)
  · simpa using hε.add hδ
  · intro i
    exact hasPropagationLE_mul (f i) (g i) (A.label i) (B.label i) (C.label i)
      (ε i) (δ i) (hfbound i) (hgbound i)

/-- The controlled families form an actual rational submodule. -/
def homSubmodule (A B : ControlledObject X) : Submodule ℚ (Family A B) where
  carrier := {f | NullControlled A B f}
  zero_mem' := nullControlled_zero A B
  add_mem' := by
    intro f g hf hg
    exact nullControlled_add A B f g hf hg
  smul_mem' := by
    intro c f hf
    exact nullControlled_smul A B c f hf

abbrev Hom (A B : ControlledObject X) : Type := homSubmodule A B

/-- Scaling with unrestricted coefficients that may vary with the index. -/
def controlledScale {A B : ControlledObject X} (c : ℕ → ℚ) (f : Hom A B) : Hom A B :=
  ⟨fun i ↦ c i • f.val i, nullControlled_scale A B c f.val f.property⟩

def controlledId (A : ControlledObject X) : Hom A A :=
  ⟨fun _ ↦ 1, nullControlled_id A⟩

def controlledComp {A B C : ControlledObject X} (f : Hom A B) (g : Hom B C) : Hom A C :=
  ⟨fun i ↦ g.val i * f.val i, nullControlled_comp A B C f.val g.val f.property g.property⟩

instance controlledObjectCategory : Category.{0} (ControlledObject X) where
  Hom := Hom
  id := controlledId
  comp := controlledComp
  id_comp f := by
    apply Subtype.ext
    funext i
    exact Matrix.mul_one (f.val i)
  comp_id f := by
    apply Subtype.ext
    funext i
    exact Matrix.one_mul (f.val i)
  assoc f g h := by
    apply Subtype.ext
    funext i
    exact (Matrix.mul_assoc (h.val i) (g.val i) (f.val i)).symm

instance controlledObjectPreadditive : Preadditive (ControlledObject X) where
  homGroup A B := inferInstanceAs (AddCommGroup (Hom A B))
  add_comp A B C f f' g := by
    apply Subtype.ext
    funext i
    exact Matrix.mul_add (g.val i) (f.val i) (f'.val i)
  comp_add A B C f g g' := by
    apply Subtype.ext
    funext i
    exact Matrix.add_mul (g.val i) (g'.val i) (f.val i)

/-- The prequotient hom groups retain their rational module structure. -/
instance controlledObjectHomModule (A B : ControlledObject X) : Module ℚ (A ⟶ B) :=
  inferInstanceAs (Module ℚ (Hom A B))

@[simp]
theorem id_family (A : ControlledObject X) (i : ℕ) :
    (𝟙 A : A ⟶ A).val i = (1 : Matrix (Fin (A.rank i)) (Fin (A.rank i)) ℚ) := rfl

@[simp]
theorem comp_family {A B C : ControlledObject X} (f : A ⟶ B) (g : B ⟶ C) (i : ℕ) :
    (f ≫ g).val i = g.val i * f.val i := rfl

@[simp]
theorem add_family {A B : ControlledObject X} (f g : A ⟶ B) (i : ℕ) :
    (f + g).val i = f.val i + g.val i := rfl

@[simp]
theorem neg_family {A B : ControlledObject X} (f : A ⟶ B) (i : ℕ) :
    (-f).val i = -(f.val i) := rfl

@[simp]
theorem scale_family {A B : ControlledObject X} (c : ℕ → ℚ) (f : A ⟶ B) (i : ℕ) :
    (controlledScale c f).val i = c i • f.val i := rfl

/-- The manuscript's eventual exact equality relation on controlled families. -/
def eventualEquality : HomRel (ControlledObject X) :=
  fun _ _ f g ↦ ∀ᶠ i in atTop, f.val i = g.val i

theorem eventualEquality_refl {A B : ControlledObject X} (f : A ⟶ B) :
    eventualEquality f f := Eventually.of_forall fun _ ↦ rfl

theorem eventualEquality_symm {A B : ControlledObject X} {f g : A ⟶ B}
    (h : eventualEquality f g) : eventualEquality g f := by
  exact h.mono (fun _ hi ↦ hi.symm)

theorem eventualEquality_trans {A B : ControlledObject X} {f g h : A ⟶ B}
    (hfg : eventualEquality f g) (hgh : eventualEquality g h) :
    eventualEquality f h := by
  filter_upwards [hfg, hgh] with i hi hj
  exact hi.trans hj

theorem eventualEquality_comp_left {A B C : ControlledObject X}
    (f : A ⟶ B) {g g' : B ⟶ C} (h : eventualEquality g g') :
    eventualEquality (f ≫ g) (f ≫ g') := by
  filter_upwards [h] with i hi
  exact congrArg (fun M ↦ M * f.val i) hi

theorem eventualEquality_comp_right {A B C : ControlledObject X}
    {f f' : A ⟶ B} (g : B ⟶ C) (h : eventualEquality f f') :
    eventualEquality (f ≫ g) (f' ≫ g) := by
  filter_upwards [h] with i hi
  exact congrArg (fun M ↦ g.val i * M) hi

theorem eventualEquality_add {A B : ControlledObject X}
    (f₁ f₂ g₁ g₂ : A ⟶ B) (hf : eventualEquality f₁ f₂) (hg : eventualEquality g₁ g₂) :
    eventualEquality (f₁ + g₁) (f₂ + g₂) := by
  filter_upwards [hf, hg] with i hi hj
  exact congrArg₂ (fun M N ↦ M + N) hi hj

theorem eventualEquality_scale {A B : ControlledObject X}
    (c : ℕ → ℚ) {f g : A ⟶ B} (h : eventualEquality f g) :
    eventualEquality (controlledScale c f) (controlledScale c g) := by
  filter_upwards [h] with i hi
  exact congrArg (fun M ↦ c i • M) hi

instance eventualEqualityCongruence : Congruence (eventualEquality (X := X)) where
  equivalence :=
    ⟨eventualEquality_refl, eventualEquality_symm, eventualEquality_trans⟩
  comp_left := eventualEquality_comp_left
  comp_right := eventualEquality_comp_right

/-- A genuine quotient category, with no extra generated identifications. -/
abbrev TailCategory (X : Type u) [PseudoMetricSpace X] :=
  CategoryTheory.Quotient (eventualEquality (X := X))

instance tailCategoryPreadditive : Preadditive (TailCategory X) :=
  CategoryTheory.Quotient.preadditive (eventualEquality (X := X))
    (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦ eventualEquality_add f₁ f₂ g₁ g₂ hf hg)

def tailFunctor : ControlledObject X ⥤ TailCategory X :=
  CategoryTheory.Quotient.functor (eventualEquality (X := X))

instance tailFunctor_additive : (tailFunctor (X := X)).Additive :=
  CategoryTheory.Quotient.functor_additive (eventualEquality (X := X))
    (fun {_ _} f₁ f₂ g₁ g₂ hf hg ↦ eventualEquality_add f₁ f₂ g₁ g₂ hf hg)

/-- The crucial exactness check: equality in the quotient is precisely eventual
entrywise equality of the whole finite matrices. -/
theorem tailFunctor_map_eq_iff {A B : ControlledObject X} (f g : A ⟶ B) :
    (tailFunctor (X := X)).map f = (tailFunctor (X := X)).map g ↔
      ∀ᶠ i in atTop, f.val i = g.val i := by
  exact CategoryTheory.Quotient.functor_map_eq_iff (eventualEquality (X := X)) f g

end ControlledObject

end HSFormal
