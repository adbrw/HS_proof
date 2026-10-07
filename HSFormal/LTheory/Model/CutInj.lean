import HSFormal.LTheory.Model.CutInjQuot

/-!
# Injectivity of the line transitions (lower L-theory model, module 22)

**Route** (germs at `-∞`, no relative cut of the null-cobordism is needed).  Let `Q` be an
`N`-dimensional Poincaré complex over `A = C_ℤ^{∘k}(B)` with `tensorLine [Q] = 0`.
1. The half-line splitting (`HalfLineSplitKar`) gives pairs `Y` on `Q` placed at `0` (interior in
   the negative half-line) and `Z` on `-(Q at 0)` (interior in the positive half-line) with
   `[Y ∪ Z] = ±tensorLine [Q] = 0`, so `Y ∪ Z` is null-cobordant (`Lconc.cls_eq_zero_iff`), and by
   the relative Wall trick under `NegK` it bounds a pair `W` with **free** interior
   (`NegK.exists_free_nullCobordism` at level `k + 1`).
2. Push `W` along the lower germ functor `lowGerm : C_ℤ(A) ⟶ C_ℤ(A)/C_ℤ^{bdd}(A)`
   (`X ↦ X|_{(-∞, 0)}`, `CutInjQuot`): `W⁻` is a pair of the quotient with free interior
   (`lowGerm` maps `1` to `1`) and boundary `(Y ∪ Z)⁻`.
3. `(Y ∪ Z)⁻ ≃ Y/C_ℤ^{bdd}` (`unionGermIso`, `negGermIso`): the germ kills the bounded boundary
   `Q at 0` and the positive-half-line interior of `Z`, and on the negative half-line it is the
   projection modulo bounded objects.  Retarget `W⁻` along this isometry
   (`PairOn.retargetIso`): `Y/C_ℤ^{bdd}` bounds a free pair of `C_ℤ(A)/C_ℤ^{bdd}(A)`.
4. The relative boundary construction (module 10, `TriadOn.nullCobordant_lift_of_quotPair` for the
   bounded Karoubi filtration) then makes the boundary `Q at 0` of `Y` null-cobordant over
   `C_ℤ^{bdd}(A) ≃ A`, i.e. `[Q] = 0` (`Lconc.czBddEquiv`).

Relation (R) (`UnionRel`) is **not** needed for injectivity.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression

noncomputable section

namespace CZ

variable {A : InvCat}

/-- **The germ at `-∞` of a union over a bounded boundary**: for pairs `X` on `B` (interior in
the negative half-line) and `Y` on `-B` (interior in the positive half-line) with `B` bounded,
`(X ∪ Y)⁻ ≃ X/C_ℤ^{bdd}(A)` in `C_ℤ(A)/C_ℤ^{bdd}(A)`. -/
def unionGermQuotIso {N : ℤ} {B : SymPoincare A.cz.inv N} (hB : ∀ r, bdd A (B.C.X r))
    (X : PairOn B) (Y : PairOn B.neg) (hX : ∀ r, negHalf A (X.D.X r))
    (hY : ∀ r, posHalf A (Y.D.X r)) :
    ((X.union Y).map (lowGerm A)).HomotopyIsometry (X.toPair.toQuot (bddF A) hB) :=
  (unionGermIso X Y hB hY).trans (negGermIso X.toPair hB hX)

/-- **Cutting a free null-cobordism of a union at `0`**: if `X ∪ Y` (`X` on a bounded `B` with
interior in the negative half-line, `Y` on `-B` with interior in the positive half-line) bounds a
pair `W` with free interior, then `B` is null-cobordant over the bounded category
`C_ℤ^{bdd}(A)`. -/
theorem nullCobordant_lift_of_union_bound {N : ℤ} (hN : 0 ≤ N) {B : SymPoincare A.cz.inv N}
    (hB : ∀ r, bdd A (B.C.X r)) (X : PairOn B) (Y : PairOn B.neg)
    (hX : ∀ r, negHalf A (X.D.X r)) (hY : ∀ r, posHalf A (Y.D.X r))
    (W : SymPair A.cz.inv (N + 1)) (hW : W.bd = X.union Y)
    (hfree : ∀ r, 0 ≤ r → r ≤ N + 1 + 1 → W.pD.f r = 𝟙 _) :
    NullCobordant (B.lift (U := bdd A) hB) := by
  have e : Nonempty ((W.map (lowGerm A)).bd.HomotopyIsometry (X.toPair.toQuot (bddF A) hB)) := by
    rw [show (W.map (lowGerm A)).bd = W.bd.map (lowGerm A) from rfl, hW]
    exact ⟨unionGermQuotIso hB X Y hX hY⟩
  obtain ⟨e⟩ := e
  let Y' : PairOn (X.toPair.toQuot (bddF A) hB) := (W.map (lowGerm A)).toPairOn.retargetIso e
  refine TriadOn.nullCobordant_lift_of_quotPair (F := bddF A) (W := PairData.ofPairOn X) hB
    (PairData.isPoincare_ofPairOn X) Y' (fun r h₀ h₁ ↦ ?_) (by omega)
  change (lowGerm A).F.map (W.pD.f r) = 𝟙 _
  rw [hfree r h₀ h₁, CategoryTheory.Functor.map_id]

end CZ

/-- **Injectivity of the line transitions** (the injectivity half of `dec_bij`, lower L-theory
module 22): under `NegK B`, for every level `k ≥ 0` and every `N ≥ 0`, if the line complexes
over `C_ℤ^{∘k}(B)` split into half-lines (`HalfLineSplitKar`), then
`tensorLine : Lconc (C_ℤ^{∘k} B) N → Lconc (C_ℤ^{∘k+1} B) (N + 1)` is injective. -/
theorem NegK.tensorLine_injective_kar {B : InvCat} (hK : NegK B) (k : ℕ) {N : ℤ} (hN : 0 ≤ N)
    (hL : HalfLineSplitKar (B.czIter k) N) :
    Function.Injective (Lconc.tensorLine (B.czIter k) N) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨Q, rfl⟩ := Lconc.cls_surjective x
  obtain ⟨Y, Z, hY, hZ, hYZ⟩ := hL Q
  have h₀ : Lconc.cls (Y.union Z) = 0 := by
    rcases hYZ with h | h <;> simp [h, hx]
  obtain ⟨W, hW, hfree⟩ :=
    hK.exists_free_nullCobordism (k := k + 1) (by omega) (N := N + 1) (by omega)
      (Lconc.cls_eq_zero_iff.1 h₀)
  have hnc := CZ.nullCobordant_lift_of_union_bound hN (CZ.bdd_atZero_X Q) Y Z hY hZ W hW hfree
  have h₁ : (Lconc.czBddEquiv (B.czIter k) N).symm (Lconc.cls Q) = 0 := by
    rw [Lconc.czBddEquiv_symm_apply, Lconc.map_cls]
    exact Lconc.cls_eq_zero hnc
  exact (AddEquiv.map_eq_zero_iff _).1 h₁

/-- **`tensorLine` is bijective** in degrees `N ≥ 0` under `NegK`, given relation (R) and the
half-line splitting (surjectivity: `NegK.tensorLine_surjective_kar`). -/
theorem NegK.tensorLine_bijective_kar {B : InvCat} (hK : NegK B) (k : ℕ) {N : ℤ} (hN : 0 ≤ N)
    (hR : UnionRel (B.czIter k).cz N) (hL : HalfLineSplitKar (B.czIter k) N) :
    Function.Bijective (Lconc.tensorLine (B.czIter k) N) :=
  ⟨hK.tensorLine_injective_kar k hN hL, hK.tensorLine_surjective_kar k hN hR hL⟩

end

end HSFormal.LTheory
