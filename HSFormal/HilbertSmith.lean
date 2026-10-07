import HSFormal.MainWeak
import HSFormal.MainPinch
import HSFormal.Cubical.CubeCutSteps
import HSFormal.Inputs.Lemma7
import HSFormal.Inputs.GY.NSSIsLie
import HSFormal.Newman.Newman

/-!
The Hilbert–Smith theorem of the manuscript, with every step of its proof formalized.
The remaining hypotheses are published inputs:
* `NSSIsLie` (Gleason–Yamabe), `CompactTorsionFreeContainsPadic` (Tao 2011, Lemma 7) and
  `NewmanPrimeOrder` (Newman's theorem for prime order; Pardon 2018), or in the second form
  `CompactNonLieContainsPadic` (Lee 1997) and `UniformNewman` instead of the last two;
* a lower L-theory `𝕃 : LowerLTheory` (Carlsson–Pedersen localization, Ranicki decorations).
-/

namespace HSFormal

open LTheory

theorem padicExclusion_of_inputs (𝕃 : LowerLTheory) (hNew : NewmanPrimeOrder) : PadicExclusion :=
  padicExclusion_of_pinchSignature' 𝕃 cubeFlagChoice hNew (pinchSignature 𝕃)

theorem hilbertSmith_of_inputs (𝕃 : LowerLTheory) (hNSS : NSSIsLie)
    (hT : CompactTorsionFreeContainsPadic) (hNew : NewmanPrimeOrder) :
    HilbertSmith ∧ HilbertSmithWithBoundary ∧ PadicExclusionWithBoundary :=
  hilbertSmith_of_pinchSignature' 𝕃 cubeFlagChoice hNSS hT hNew (pinchSignature 𝕃)

theorem hilbertSmith_of_inputs_lee (𝕃 : LowerLTheory) (hNSS : NSSIsLie)
    (hLee : CompactNonLieContainsPadic) (hNew : UniformNewman) :
    HilbertSmith ∧ HilbertSmithWithBoundary ∧ PadicExclusionWithBoundary :=
  hilbertSmith_of_pinchSignature 𝕃 cubeFlagChoice hNSS hLee hNew (pinchSignature 𝕃)

/-- The first form with Tao's Lemma 7 (`CompactTorsionFreeContainsPadic`) discharged by the proof
in `HSFormal.Inputs.Lemma7`. -/
theorem hilbertSmith_of_inputs₂ (𝕃 : LowerLTheory) (hNSS : NSSIsLie) (hNew : NewmanPrimeOrder) :
    HilbertSmith ∧ HilbertSmithWithBoundary ∧ PadicExclusionWithBoundary :=
  hilbertSmith_of_inputs 𝕃 hNSS Lemma7.compactTorsionFreeContainsPadic hNew

/-- **The Hilbert–Smith theorem from a lower L-theory**: the published inputs Gleason–Yamabe
(`GY.nssIsLie`), [Tao11, Lemma 7] (`Lemma7.compactTorsionFreeContainsPadic`) and Newman's
theorem for prime order (`Newman.newmanPrimeOrder`) are discharged by their proofs, so the only
remaining hypothesis is `𝕃 : LowerLTheory`. -/
theorem hilbertSmith_of_lowerL (𝕃 : LowerLTheory) :
    HilbertSmith ∧ HilbertSmithWithBoundary ∧ PadicExclusionWithBoundary :=
  hilbertSmith_of_inputs 𝕃 GY.nssIsLie Lemma7.compactTorsionFreeContainsPadic
    Newman.newmanPrimeOrder

end HSFormal
