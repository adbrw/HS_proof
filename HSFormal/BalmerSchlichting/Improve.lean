import HSFormal.BalmerSchlichting.SplitCone

/-!
# Improving a homotopy idempotent

For `h : e ≫ e ≃ e`, the chain map `e' = 2e² - e` is homotopic to `e`, and
`h' = e²h + 2ehe + he² - h` is a homotopy `e' ≫ e' ≃ e'`. If `h_{l+2} = 0`, then
`h'_{l+1} ≫ e' - e' ≫ h'_{l+1}` factors through the differential `X_{l+1} ⟶ X_l`. This is the polynomial identity
`(p(y) - p(x)) ((x + y)² - 1) = ((y² - y) - (x² - x)) Q(x, y)` with `p(t) = 2t² - t` and
`Q = 2x² + 4xy + 2y² + x + y - 1`.
-/

namespace HSFormal.HomotopyIdempotent

open CategoryTheory Category Limits Preadditive

universe v u

variable {P : Type u} [Category.{v} P] [Preadditive P]

/-- `Σ Q_{ab} a^a ≫ φ ≫ b^b` for `Q = 2x² + 4xy + 2y² + x + y - 1`. -/
def qsum {A B : P} (a : A ⟶ A) (b : B ⟶ B) (φ : A ⟶ B) : A ⟶ B :=
  a ≫ a ≫ φ + a ≫ a ≫ φ + a ≫ φ ≫ b + a ≫ φ ≫ b + a ≫ φ ≫ b + a ≫ φ ≫ b + φ ≫ b ≫ b +
    φ ≫ b ≫ b + a ≫ φ + φ ≫ b - φ

lemma qsum_comp_left {A A' B : P} (a : A ⟶ A) (a' : A' ⟶ A') (b : B ⟶ B) (d : A ⟶ A')
    (ψ : A' ⟶ B) (hd : a ≫ d = d ≫ a') : qsum a b (d ≫ ψ) = d ≫ qsum a' b ψ := by
  simp only [qsum, comp_add, comp_sub, reassoc_of% hd, assoc]

lemma qsum_neg {A B : P} (a : A ⟶ A) (b : B ⟶ B) (φ : A ⟶ B) :
    qsum a b (-φ) = -qsum a b φ := by
  simp only [qsum, comp_neg, neg_comp]
  abel

@[simp]
lemma qsum_zero {A B : P} (a : A ⟶ A) (b : B ⟶ B) : qsum a b 0 = 0 := by
  simp [qsum]

variable {X : ChainComplex P ℤ} (e : X ⟶ X)

/-- The chain map `2e² - e`. -/
def improve : X ⟶ X := e ≫ e + e ≫ e - e

lemma improve_f (n : ℤ) : (improve e).f n = e.f n ≫ e.f n + e.f n ≫ e.f n - e.f n := by
  simp [improve]

variable {e} (h : Homotopy (e ≫ e) e)

/-- The homotopy `e²h + 2ehe + he² - h : improve e ≫ improve e ≃ improve e`. -/
def improveHomotopy : Homotopy (improve e ≫ improve e) (improve e) :=
  Homotopy.congrSub ((h.compLeft (e ≫ e)).add (((h.compLeft e).compRight e).add
    (((h.compLeft e).compRight e).add ((h.compRight (e ≫ e)).add h.symm)))) (by
      simp only [improve, add_comp, comp_add, sub_comp, comp_sub, assoc]
      abel)

lemma improveHomotopy_hom (i j : ℤ) : (improveHomotopy h).hom i j =
    e.f i ≫ e.f i ≫ h.hom i j + e.f i ≫ h.hom i j ≫ e.f j + e.f i ≫ h.hom i j ≫ e.f j +
      h.hom i j ≫ e.f j ≫ e.f j - h.hom i j := by
  simp only [improveHomotopy, Homotopy.congrSub_hom, Homotopy.add_hom, Homotopy.compLeft_hom,
    Homotopy.compRight_hom, Homotopy.symm_hom, HomologicalComplex.comp_f, assoc]
  abel

lemma improveHomotopy_hom_eq_zero (i j : ℤ) (h0 : h.hom i j = 0) :
    (improveHomotopy h).hom i j = 0 := by
  simp [improveHomotopy_hom, h0]

include h in
lemma quotient_map_improve : (HomotopyCategory.quotient P _).map (improve e) =
    (HomotopyCategory.quotient P _).map e := by
  have := HomotopyCategory.eq_of_homotopy _ _ h
  simp only [improve, Functor.map_add, Functor.map_sub, this]
  abel

/-- The factor `Y` with `h'_{l+1} ≫ e' - e' ≫ h'_{l+1} = d ≫ Y`. -/
def improveY (l : ℤ) : ∀ i j, X.X i ⟶ X.X (j + 1) := fun i j ↦
  -qsum (e.f i) (e.f (j + 1)) (h.hom i (l + 1) ≫ h.hom (l + 1) (j + 1))

lemma improveY_eq_zero (l i j : ℤ) (hij : i ≠ l ∨ j ≠ l + 1) : improveY h l i j = 0 := by
  rcases hij with hi | hj
  · rw [improveY, h.zero i (l + 1) (by simp; omega)]
    simp
  · rw [improveY, h.zero (l + 1) (j + 1) (by simp; omega)]
    simp

lemma improveY_eq_zero_of_hom (l i j : ℤ) (h0 : h.hom i (l + 1) = 0) : improveY h l i j = 0 := by
  simp [improveY, h0]

lemma improve_comm (l : ℤ) (hh : h.hom (l + 1 + 1) (l + 1 + 1 + 1) = 0) :
    (improveHomotopy h).hom (l + 1) (l + 1 + 1) ≫ (improve e).f (l + 1 + 1) -
      (improve e).f (l + 1) ≫ (improveHomotopy h).hom (l + 1) (l + 1 + 1) =
        X.d (l + 1) l ≫ improveY h l l (l + 1) := by
  have r₁ := comm_succ h l
  have r₂ := comm_succ h (l + 1)
  rw [hh, zero_comp, add_zero] at r₂
  simp only [HomologicalComplex.comp_f] at r₁ r₂
  have step₁ : (improveHomotopy h).hom (l + 1) (l + 1 + 1) ≫ (improve e).f (l + 1 + 1) -
      (improve e).f (l + 1) ≫ (improveHomotopy h).hom (l + 1) (l + 1 + 1) =
        qsum (e.f (l + 1)) (e.f (l + 1 + 1))
          (h.hom (l + 1) (l + 1 + 1) ≫ (e.f (l + 1 + 1) ≫ e.f (l + 1 + 1) - e.f (l + 1 + 1)) -
            (e.f (l + 1) ≫ e.f (l + 1) - e.f (l + 1)) ≫ h.hom (l + 1) (l + 1 + 1)) := by
    simp only [improveHomotopy_hom, improve_f, qsum, add_comp, comp_add, sub_comp, comp_sub, assoc]
    abel
  have step₂ : h.hom (l + 1) (l + 1 + 1) ≫ (e.f (l + 1 + 1) ≫ e.f (l + 1 + 1) - e.f (l + 1 + 1)) -
      (e.f (l + 1) ≫ e.f (l + 1) - e.f (l + 1)) ≫ h.hom (l + 1) (l + 1 + 1) =
        X.d (l + 1) l ≫ (-(h.hom l (l + 1) ≫ h.hom (l + 1) (l + 1 + 1))) := by
    rw [r₁, r₂]
    simp only [add_sub_cancel_right, add_comp, assoc, comp_neg]
    abel
  rw [step₁, step₂, qsum_comp_left _ (e.f l) _ _ _ (e.comm (l + 1) l), qsum_neg, improveY]

end HSFormal.HomotopyIdempotent
