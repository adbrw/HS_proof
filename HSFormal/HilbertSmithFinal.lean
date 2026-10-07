import HSFormal.HilbertSmithModel
import HSFormal.Inputs.GY.NSSIsLie
import HSFormal.Inputs.Lemma7
import HSFormal.Newman.Newman

/-!
# The Hilbert–Smith theorem from the concrete model, with the published inputs proved

`hilbertSmith_of_model'` (`HSFormal/HilbertSmithModel.lean`) with the three published inputs
discharged by their proofs on the v4.35 port:
* Gleason–Yamabe (`NSSIsLie`): `GY.nssIsLie` (`HSFormal/Inputs/GY/NSSIsLie.lean`);
* [Tao11, Lemma 7] (`CompactTorsionFreeContainsPadic`): `Lemma7.compactTorsionFreeContainsPadic`
  (`HSFormal/Inputs/Lemma7.lean`);
* Newman's theorem for prime order (`NewmanPrimeOrder`): `Newman.newmanPrimeOrder`
  (`HSFormal/Newman/Newman.lean`).

In `hilbertSmith_of_model_final` the remaining hypotheses are the two L-theory statements
`LTheory.LiftingClosedSubAll` (`HSFormal/LTheory/Model/Exact.lean`) and `LTheory.DecBijModel`
(`HSFormal/LTheory/Model/Instance.lean`); in `hilbertSmith_of_halfLine` (from
`hilbertSmith_of_model₄`) they are `LTheory.NegKHighAll` and the half-line splitting
`LTheory.HalfLineSplitKar`; in `hilbertSmith_of_negKHigh` (from `hilbertSmith_of_model₅`, every
model lemma proved) the only remaining hypothesis is `LTheory.NegKHighAll`.
-/

namespace HSFormal

/-- **The Hilbert–Smith theorem from the concrete model**: the only remaining hypotheses are the
L-theory statements `LiftingClosedSubAll` and `DecBijModel` about the colimit model. -/
theorem hilbertSmith_of_model_final (hA : LTheory.LiftingClosedSubAll)
    (hD : LTheory.DecBijModel) :
    HilbertSmith ∧ HilbertSmithWithBoundary ∧ PadicExclusionWithBoundary :=
  hilbertSmith_of_model' hA hD GY.nssIsLie Lemma7.compactTorsionFreeContainsPadic
    Newman.newmanPrimeOrder

/-- **The Hilbert–Smith theorem from the model, with (L2) and the union relation proved**
(`hilbertSmith_of_model₄`): the remaining hypotheses are `NegK` at levels `k ≥ 2`
(`LTheory.NegKHighAll`) and the half-line splitting `LTheory.HalfLineSplitKar` of the iterated
bounded categories of `⊕_{i ∈ T} Free(ℚ[Gᵢ])`. -/
theorem hilbertSmith_of_halfLine (hK : LTheory.NegKHighAll)
    (hL : ∀ (G : ℕ → Type) [∀ i, Group (G i)] [∀ i, Fintype (G i)] (T : Set ℕ) (k : ℕ) (N : ℤ),
      0 ≤ N → LTheory.HalfLineSplitKar ((LTheory.finSuppFreeQG G T).czIter k) N) :
    HilbertSmith ∧ HilbertSmithWithBoundary ∧ PadicExclusionWithBoundary :=
  hilbertSmith_of_model₄ hK hL GY.nssIsLie Lemma7.compactTorsionFreeContainsPadic
    Newman.newmanPrimeOrder

/-- **The Hilbert–Smith theorem from the model, with every model lemma proved**
(`hilbertSmith_of_model₅`): the only remaining hypothesis is `NegK` at levels `k ≥ 2`
(`LTheory.NegKHighAll`). -/
theorem hilbertSmith_of_negKHigh (hK : LTheory.NegKHighAll) :
    HilbertSmith ∧ HilbertSmithWithBoundary ∧ PadicExclusionWithBoundary :=
  hilbertSmith_of_model₅ hK GY.nssIsLie Lemma7.compactTorsionFreeContainsPadic
    Newman.newmanPrimeOrder

end HSFormal
