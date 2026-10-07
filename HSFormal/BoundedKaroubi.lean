import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.CategoryTheory.Idempotents.HomologicalComplex
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Homotopy idempotent completeness of `K^b(P)` (manuscript §1, input 2)

`BalmerSchlichting` states [BS01, Thm 2.8] for the split exact structure in the form used by
the manuscript (l. 27–28, Lemma 5.1): if an additive category `P` is idempotent complete, so is
the bounded homotopy category `K^b(P)`. It is recorded as a `Prop`, not proved.

What is proved here is the strict case: an idempotent of `K^b(P)` represented by a chain map
`e` with `e ≫ e = e` on the nose splits in `K^b(P)` (degreewise splitting). The content of
[BS01] is the passage from `e ≫ e ≃ e` to a strict idempotent; the graph idempotent of §5 is
idempotent only up to homotopy, so the strict case does not cover Lemma 5.1.

The proof of [BS01, 2.8] uses: the triangulated structure on the idempotent completion
[BS01, Thm 1.5] and the Thomason–Landsburg `K₀` criterion (Lemma 2.2), an Eilenberg swindle
`⨁_k T^{2k}` on bounded-below complexes (Lemma 2.4), and kernel truncations of acyclic tails
(Lemma 2.6). None of these is in Mathlib, which also lacks `K⁺(P)` and `K₀` of triangulated
categories.
-/

namespace HSFormal

open CategoryTheory Category Limits Idempotents

universe v u

variable (P : Type u) [Category.{v} P] [Preadditive P]

/-- A chain complex is bounded if it vanishes outside a finite range of degrees. -/
def IsBoundedComplex {P : Type u} [Category.{v} P] [Preadditive P] (K : ChainComplex P ℤ) : Prop :=
  ∃ n : ℕ, ∀ i : ℤ, (n : ℤ) < |i| → IsZero (K.X i)

/-- The objects of `K(P)` represented by bounded complexes. -/
def boundedProperty : ObjectProperty (HomotopyCategory P (ComplexShape.down ℤ)) :=
  fun K ↦ IsBoundedComplex K.as

/-- The bounded homotopy category `K^b(P)`. -/
abbrev BoundedHomotopyCategory := (boundedProperty P).FullSubcategory

/-- [BS01, Theorem 2.8] for the split exact structure: if an additive category is idempotent
complete, then so is its bounded homotopy category. -/
def BalmerSchlichting : Prop :=
  ∀ (P : Type u) [Category.{v} P] [Preadditive P] [HasFiniteBiproducts P]
    [IsIdempotentComplete P], IsIdempotentComplete (BoundedHomotopyCategory P)

variable {P}

/-- Strict idempotents of bounded complexes split in `K^b(P)` when `P` is idempotent complete. -/
theorem BoundedHomotopyCategory.strictIdempotent_splits [IsIdempotentComplete P]
    (X : BoundedHomotopyCategory P) (e : X.obj.as ⟶ X.obj.as) (he : e ≫ e = e) :
    ∃ (Y : BoundedHomotopyCategory P) (i : Y ⟶ X) (p : X ⟶ Y),
      i ≫ p = 𝟙 Y ∧ p ≫ i = ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map e) := by
  obtain ⟨Y, i, p, hip, hpi⟩ := IsIdempotentComplete.idempotents_split _ e he
  obtain ⟨n, hn⟩ := X.property
  have hY : IsBoundedComplex Y := ⟨n, fun k hk ↦ by
    rw [IsZero.iff_id_eq_zero, ← HomologicalComplex.id_f, ← hip, HomologicalComplex.comp_f,
      (hn k hk).eq_of_src (p.f k) 0, comp_zero]⟩
  refine ⟨⟨(HomotopyCategory.quotient _ _).obj Y, hY⟩,
    ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map i),
    ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map p), ?_, ?_⟩
  · ext
    change (HomotopyCategory.quotient _ _).map i ≫ (HomotopyCategory.quotient _ _).map p = 𝟙 _
    rw [← Functor.map_comp, hip, CategoryTheory.Functor.map_id]
  · ext
    change (HomotopyCategory.quotient _ _).map p ≫ (HomotopyCategory.quotient _ _).map i =
      (HomotopyCategory.quotient _ _).map e
    rw [← Functor.map_comp, hpi]

end HSFormal
