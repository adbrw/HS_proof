import HSFormal.LTheory.Model.NegK.KarDiag
import HSFormal.LTheory.Model.NegK.LevelOne

/-!
# `NegK` at level `1`, unconditionally

Theorem A (`KarDiag.karDiag`, the two-flag bounded splitting over the semisimple rings `ℚ[Gᵢ]`)
discharges the hypothesis of `negK_levelOne`. The remaining classical input is `NegKHighAll`
(`K₋ₖ(ℚ[G]) = 0` for `k ≥ 2`, in the iterated bounded form; [Bass68], [PW85], [Ran92, 11.2]).
-/

namespace HSFormal.LTheory

variable {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]

theorem negKOne_finSuppFreeQG (T : Set ℕ) : NegKOne (finSuppFreeQG G T) :=
  negK_levelOne KarDiag.karDiag T

theorem negKAll_of_negKHighAll (hH : NegKHighAll) : NegKAll :=
  negKAll_of_high KarDiag.karDiag hH

end HSFormal.LTheory
