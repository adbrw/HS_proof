import HSFormal.LTheory.Model.UnionRelNull
import HSFormal.LTheory.Model.UnionRelSum
import HSFormal.LTheory.Model.UnionRelStatement

/-!
# The union relation (R)

**Relation (R)** of the concrete lower L-theory model (`UnionRel`, stated in
`Model/UnionRelStatement.lean`): for Poincaré pairs `Y`, `Y'` with boundary `B` and `Z` with
boundary `-B`,

  `[Y ∪ Z] - [Y' ∪ Z] = [Y ∪ -Y']`  in `Lconc A (N + 1)`.

Proof:
* (**U-turn**, `UTurn.cls_union_uturn_eq`, `Model/UnionRelNull.lean`) for a pair `X` on
  `B ⊕ -B`, the class `[X ∪ (Z ⊕ -Z)]` does not depend on `Z`: the U-turn
  `D_X ∪_{C_{B ⊕ B}} D_Z` is a null-cobordism of `(X ∪ (Z ⊕ -Z)) ⊕ -(X ∪ (B × I))`;
* (**sums**, `UnionSum.cls_union_sum`, `Model/UnionRelSum.lean`)
  `[(Y ⊕ Y₂) ∪ (Z ⊕ -Z)] = [Y ∪ Z] + [Y₂ ∪ -Z]`;
* (**doubles**, `Lconc.cls_union_neg_self`, `Model/UnionRelDouble.lean`) `[X ∪ -X] = 0`.

Hence `[Y ∪ Z] + [Y₂ ∪ -Z]` does not depend on `Z` (`unionRel_key`); with `Y₂ = -Y'` and
`Z := -Y'` this gives `[Y' ∪ Z] + [-Y' ∪ -Z] = 0` and `[Y ∪ Z] + [-Y' ∪ -Z] = [Y ∪ -Y']`.
-/

namespace HSFormal.LTheory

open CategoryTheory

noncomputable section

attribute [local implicit_reducible] PairOn.toPair SymPair.neg SymPair.toPairOn PairOn.union PairOn.glue
  SymPair.closedOfIsZero IsStrictSymm PairOn.sum SymPoincare.HomotopyIsometry.cylinder

variable {A : InvCat} {N : ℤ} {B : SymPoincare A.inv N}

/-- `[Y ∪ Z] + [Y₂ ∪ -Z]` does not depend on `Z`. -/
theorem unionRel_key (Y : PairOn B) (Y₂ Z Z' : PairOn B.neg) :
    Lconc.cls (Y.union Z) + Lconc.cls (Y₂.union (UTurn.Zn Z)) =
      Lconc.cls (Y.union Z') + Lconc.cls (Y₂.union (UTurn.Zn Z')) := by
  rw [← UnionSum.cls_union_sum, ← UnionSum.cls_union_sum]
  exact UTurn.cls_union_uturn_eq Z Z' (UnionSum.XS Y Y₂)

/-- **Relation (R) for pairs on a fixed boundary**: `[Y ∪ Z] - [Y' ∪ Z] = [Y ∪ -Y']`. -/
theorem PairOn.unionRel (Y Y' : PairOn B) (Z : PairOn B.neg) :
    Lconc.cls (Y.union Z) - Lconc.cls (Y'.union Z) =
      Lconc.cls (Y.union Y'.toPair.neg.toPairOn) := by
  have h₁ := unionRel_key Y' Y'.toPair.neg.toPairOn Z Y'.toPair.neg.toPairOn
  have h₂ := unionRel_key Y Y'.toPair.neg.toPairOn Z Y'.toPair.neg.toPairOn
  have d₁ : Lconc.cls (Y'.union Y'.toPair.neg.toPairOn) = 0 := Lconc.cls_union_neg_self Y'
  have d₂ : Lconc.cls (Y'.toPair.neg.toPairOn.union (UTurn.Zn Y'.toPair.neg.toPairOn)) = 0 :=
    Lconc.cls_union_neg_self _
  rw [d₁, d₂, add_zero] at h₁
  rw [d₂, add_zero] at h₂
  rw [eq_sub_of_add_eq h₂, eq_neg_of_add_eq_zero_left h₁]
  abel

/-- **Relation (R)** (`UnionRel`): for `(N+1)`-dimensional Poincaré pairs `Y`, `Y'`, `Z` over `A`
with `∂Z = -∂Y = -∂Y'`, `[Y ∪ Z] - [Y' ∪ Z] = [Y ∪ -Y']` in `Lconc A (N + 1)`. -/
theorem unionRel (A : InvCat) (N : ℤ) : UnionRel A N := by
  intro Y Y' Z hYZ hY'Z hYY'
  rcases Y with ⟨bY, _, _, _, _, _, _, _, _, _, _⟩
  rcases Y' with ⟨bY', _, _, _, _, _, _, _, _, _, _⟩
  rcases Z with ⟨bZ, _, _, _, _, _, _, _, _, _, _⟩
  dsimp only at hYZ hY'Z hYY'
  subst hYZ
  have hB : bY' = bY := by
    rw [← SymPoincare.neg_neg bY', ← SymPoincare.neg_neg bY]
    exact congrArg SymPoincare.neg hY'Z.symm
  subst hB
  exact PairOn.unionRel _ _ _

end

end HSFormal.LTheory
