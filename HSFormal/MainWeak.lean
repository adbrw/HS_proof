import HSFormal.MainPinch
import HSFormal.MontgomeryPrime

/-!
# Main theorem with weakened published inputs

`hilbertSmith_of_pinchSignature'` is `hilbertSmith_of_pinchSignature` with
`CompactNonLieContainsPadic` [Lee97, Thm 3.1] replaced by `CompactTorsionFreeContainsPadic`
[Tao11, Lemma 7] (a statement about compact groups only) and `UniformNewman` [Pa18] replaced by
`NewmanPrimeOrder` (prime-order cyclic groups, implied by `UniformNewman`, see
`newmanPrimeOrder_of_uniformNewman`). Remaining hypotheses: `NSSIsLie`, these two, the lower
L-theory interface `𝕃`, and `PinchSignature` (§11, Lemma 11.2).
-/

namespace HSFormal

open LTheory

theorem padicExclusion_of_pinchSignature' (𝕃 : LowerLTheory) (F : FlagChoice)
    (hNew : NewmanPrimeOrder) (hpinch : PinchSignature (fibreSignatureOf 𝕃 F) manifoldGerm) :
    PadicExclusion :=
  padicExclusion_of_fine_steps' (pointwisePeriodicIsPeriodic_of_newmanPrimeOrder hNew)
    (fibreSignatureOf 𝕃 F) manifoldGerm Prop92.classConstruction'_manifoldGerm
    inducedClass.toWeak (transferDivisibility_of 𝕃 F) germHomotopyInvariance hpinch

theorem hilbertSmith_of_pinchSignature' (𝕃 : LowerLTheory) (F : FlagChoice) (hNSS : NSSIsLie)
    (hT : CompactTorsionFreeContainsPadic) (hNew : NewmanPrimeOrder)
    (hpinch : PinchSignature (fibreSignatureOf 𝕃 F) manifoldGerm) :
    HilbertSmith ∧ HilbertSmithWithBoundary ∧ PadicExclusionWithBoundary :=
  hilbertSmith_all_of_padicExclusion' hNSS hT hNew <|
    padicExclusion_of_pinchSignature' 𝕃 F hNew hpinch

end HSFormal
