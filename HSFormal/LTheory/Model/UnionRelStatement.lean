import HSFormal.LTheory.Model.Cobordism

/-!
# Statement of the union relation (R) (lower L-theory model, module 22)

Relation (R) of `blueprint/lower-L-construction.md` §3.2: for Poincaré pairs `Y`, `Y'` with the
same boundary `B` and a pair `Z` with boundary `-B`,

  `[Y ∪ Z] - [Y' ∪ Z] = [Y ∪ -Y']`  in `Lconc A (N + 1)`.

Only the **statement** is recorded here (as a `Prop`), so that the surjectivity half of
`DecBij` (`Model/CutLine.lean`) can take it as an explicit hypothesis while it is proved
elsewhere.  The equalities of boundaries are explicit hypotheses (all three are `Prop`s, so any
proofs may be supplied; they are mutually consistent: `Y'.neg.bd = Y'.bd.neg` by definition).
-/

namespace HSFormal.LTheory

noncomputable section

/-- **Relation (R)**: for `(N+1)`-dimensional Poincaré pairs `Y`, `Y'`, `Z` over `A` with
`∂Z = -∂Y = -∂Y'`, `[Y ∪ Z] - [Y' ∪ Z] = [Y ∪ -Y']` in `Lconc A (N + 1)`. -/
def UnionRel (A : InvCat) (N : ℤ) : Prop :=
  ∀ (Y Y' Z : SymPair A.inv N) (hYZ : Z.bd = Y.bd.neg) (hY'Z : Z.bd = Y'.bd.neg)
    (hYY' : Y'.neg.bd = Y.bd.neg),
    Lconc.cls (SymPair.union Y Z hYZ) - Lconc.cls (SymPair.union Y' Z hY'Z) =
      Lconc.cls (SymPair.union Y Y'.neg hYY')

end

end HSFormal.LTheory
