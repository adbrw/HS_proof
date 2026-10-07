import HSFormal.LTheory.Model.NegK.High.Periodize

/-!
# Theorem B: the statement (NegKHigh, controlled Bass splitting)

`blueprint/negK-high.md` §3.1.

**Theorem B.**  Let `Y` be an `InvCat`, `l ≥ 0`, `X` an object of `L^l(C_ℤ Y)` and `p` an
idempotent on `X`.  Then there is a Kar object `E` of `L^{l+1} Y = L^l(L Y)` with
`(X, p) ∼ Π(E)` in `Karoubi (L^l(C_ℤ Y))`, where `Π = L^l(Π_Y)` periodizes the newest Laurent
variable into the `C_ℤ` coordinate (`CZ.periodize`).

The witness of the proof is the blueprint's explicit symbol: with `h = χ_{s ≥ 0}`, `q = 1 - p`,
`b` a propagation bound of `p` and `W = [-2b, 2b]`,
`E = (X_W, χ_W (h + (w - 1)·phq + (w⁻¹ - 1)·qhp) χ_W)` (collapsed along `W`).  The statement
records only its existence, which is all the induction (`V(m, l) ⇐ V(m - 1, l + 1)`, §5) uses.

`stablyIso_zero_of_theoremB`: with Theorem B, stable freeness in `L^{l+1} Y` gives stable freeness
in `L^l(C_ℤ Y)` (the induction step).
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive Idempotents

noncomputable section

/-- **Theorem B (controlled Bass splitting)**, `blueprint/negK-high.md` §3.1: every Kar object
`(X, p)` of `L^l(C_ℤ Y)` is stably isomorphic to the periodization `Π(E)` of a Kar object `E` of
`L^{l+1} Y`. -/
def TheoremBStatement : Prop :=
  ∀ (Y : InvCat) (l : ℕ) (X : Lpow l (Y.cz : AddCat)) (p : (Lpow l (Y.cz : AddCat)).Mor X X)
    (hp : p ≫ p = p), ∃ E : Karoubi (Lpow (l + 1) (Y : AddCat)).carrier,
      StablyIso (⟨X, p, hp⟩ : Karoubi (Lpow l (Y.cz : AddCat)).carrier)
        ((karoubiMap (Lpow.map l (CZ.periodize Y))).obj E)

open ZeroObject in
/-- `Π` maps stably zero Kar objects to stably zero ones. -/
lemma stablyIso_zero_periodize {Y : InvCat} {l : ℕ}
    {E : Karoubi (Lpow (l + 1) (Y : AddCat)).carrier} (hE : StablyIso E 0) :
    StablyIso ((karoubiMap (Lpow.map l (CZ.periodize Y))).obj E) 0 :=
  (hE.map (Lpow.map l (CZ.periodize Y))).trans
    (StablyIso.of_isZero (Functor.map_isZero _ (isZero_zero _)) (isZero_zero _))

open ZeroObject in
/-- **The induction step** (`blueprint/negK-high.md` §5): under Theorem B, if every Kar object of
`L^{l+1} Y` produced by Theorem B is stably zero, so is `(X, p)`. -/
lemma stablyIso_zero_of_theoremB (hB : TheoremBStatement) {Y : InvCat} {l : ℕ}
    (hV : ∀ E : Karoubi (Lpow (l + 1) (Y : AddCat)).carrier, StablyIso E 0)
    {X : Lpow l (Y.cz : AddCat)} (p : (Lpow l (Y.cz : AddCat)).Mor X X) (hp : p ≫ p = p) :
    StablyIso (⟨X, p, hp⟩ : Karoubi (Lpow l (Y.cz : AddCat)).carrier) 0 :=
  let ⟨E, hE⟩ := hB Y l X p hp
  hE.trans (stablyIso_zero_periodize (hV E))

end

end HSFormal.LTheory
