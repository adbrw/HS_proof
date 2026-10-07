import HSFormal.LTheory.Model.NegK.High.Laurent
import HSFormal.LTheory.Model.NegK.High.StablyIso
import HSFormal.LTheory.Interface

/-!
# Theorem R, Karoubi form: the statement (NegKHigh module N13, `RegKarStatement`)

`blueprint/negK-high.md` §4 "Kar form (dictionary)", §5 (base `m = 1`, step 2), §7 (`reg_faces`).

For `B = finSuppFreeQG G T` (any `G`, any `T ⊆ ℕ`, possibly infinite) and every `l`, every Kar
object `E` of `L^{l+1} B = L^l (L B)` satisfies `E ⊞ ι⁺Q₁ ∼ ι⁺Q₀` for Kar objects `Q₀, Q₁` of the
faces category `L^l (L⁺ B)`, where `ι⁺ = L^l (LaurentPos.incl B) : L^l (L⁺ B) ⥤ L^l (L B)`
extends the inclusion `L⁺ B ⥤ L B` in the **innermost** variable (the variable that Theorem B's
`Π` periodizes and Lemma F kills).

The proof (`RegKar.lean`) identifies hom-sets fibrewise with matrices over
`lpRing (l + 1) (ℚ[Gᵢ])` (resp. `lpRing l (ℚ[Gᵢ][X])` for the faces, with `ι⁺ ↦ faceMap`) and
transfers `theoremR_matrix` (`RegMatrix.lean`); it gives in fact a Karoubi isomorphism.
-/

namespace HSFormal.LTheory

open CategoryTheory Limits Idempotents

/-- **Theorem R, Karoubi form** (`reg_faces` of the blueprint): for every `G`, `T`, `l` and every
Kar object `E` of `L^{l+1} B`, `B = finSuppFreeQG G T`, there are Kar objects `Q₀, Q₁` of
`L^l (L⁺ B)` with `E ⊞ ι⁺ Q₁ ∼ ι⁺ Q₀` (`StablyIso`), `ι⁺ = Lpow.map l (LaurentPos.incl B)`. -/
def RegKarStatement : Prop :=
  ∀ (G : ℕ → Type) [∀ i, Group (G i)] [∀ i, Fintype (G i)] (T : Set ℕ) (l : ℕ)
    (E : Karoubi (Lpow (l + 1) (finSuppFreeQG G T : AddCat)).carrier),
    ∃ Q₀ Q₁ : Karoubi (Lpow l (LaurentPos (finSuppFreeQG G T : AddCat))).carrier,
      StablyIso (E ⊞ (karoubiMap (Lpow.map l (LaurentPos.incl (finSuppFreeQG G T : AddCat)))).obj Q₁)
        ((karoubiMap (Lpow.map l (LaurentPos.incl (finSuppFreeQG G T : AddCat)))).obj Q₀)

end HSFormal.LTheory
