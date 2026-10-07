import HSFormal.LTheory.Model.CutInj
import HSFormal.LTheory.Model.Instance
import HSFormal.LTheory.Model.NegK.LevelOne

/-!
# `DecBijModel` from relation (R) and the half-line splitting (lower L-theory model, module 22)

Assembly: under `NegK`, every transition `tensorLine` in degrees `N ≥ 0` is injective
(`NegK.tensorLine_injective_kar`, from `HalfLineSplitKar` alone) and surjective
(`NegK.tensorLine_surjective_kar`, from `UnionRel` and `HalfLineSplitKar`), so
`Lmodel.cls_bijective_of_nonneg` gives the decoration bijection; for the point categories
`finSuppFreeQG G T` this is `DecBijModel`.
-/

namespace HSFormal.LTheory

noncomputable section

/-- **The decoration map is bijective** (`Lconc → Lmodel`, `n ≥ 0`) for an `InvCat` with `NegK`,
given relation (R) and the half-line splitting at every level `k` and degree `N ≥ 0`. -/
theorem Lmodel.cls_bijective_of_negK {A : InvCat} (hK : NegK A) {n : ℤ} (hn : 0 ≤ n)
    (hR : ∀ (k : ℕ) (N : ℤ), 0 ≤ N → UnionRel (A.czIter k).cz N)
    (hL : ∀ (k : ℕ) (N : ℤ), 0 ≤ N → HalfLineSplitKar (A.czIter k) N) :
    Function.Bijective (Lmodel.cls A n) :=
  Lmodel.cls_bijective_of_nonneg hn fun k N hN ↦
    hK.tensorLine_bijective_kar k hN (hR k N hN) (hL k N hN)

/-- **`DecBijModel`** from `NegKAll`, relation (R) and the half-line splitting for the point
categories `finSuppFreeQG G T` at every level and degree `N ≥ 0`. -/
theorem decBijModel_of_unionRel_halfLine (hK : NegKAll)
    (hR : ∀ (G : ℕ → Type) [∀ i, Group (G i)] [∀ i, Fintype (G i)] (T : Set ℕ) (k : ℕ) (N : ℤ),
      0 ≤ N → UnionRel ((finSuppFreeQG G T).czIter k).cz N)
    (hL : ∀ (G : ℕ → Type) [∀ i, Group (G i)] [∀ i, Fintype (G i)] (T : Set ℕ) (k : ℕ) (N : ℤ),
      0 ≤ N → HalfLineSplitKar ((finSuppFreeQG G T).czIter k) N) :
    DecBijModel := fun G _ _ T _ hn ↦
  Lmodel.cls_bijective_of_negK (hK G T) hn (hR G T) (hL G T)

end

end HSFormal.LTheory
