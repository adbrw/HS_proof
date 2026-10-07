import HSFormal.Main
import HSFormal.Prop92

/-!
Remaining hypotheses of the Hilbert–Smith theorem: the published inputs `NSSIsLie`, `CompactNonLieContainsPadic`,
`UniformNewman`, the lower L-theory interface `𝕃`, and `PinchSignature` (§11, Lemma 11.2).
-/

namespace HSFormal

open LTheory

theorem padicExclusion_of_pinchSignature (𝕃 : LowerLTheory) (F : FlagChoice) (hNew : UniformNewman)
    (hpinch : PinchSignature (fibreSignatureOf 𝕃 F) manifoldGerm) : PadicExclusion :=
  padicExclusion_of_remaining 𝕃 F hNew Prop92.classConstruction'_manifoldGerm hpinch

theorem hilbertSmith_of_pinchSignature (𝕃 : LowerLTheory) (F : FlagChoice) (hNSS : NSSIsLie)
    (hLee : CompactNonLieContainsPadic) (hNew : UniformNewman)
    (hpinch : PinchSignature (fibreSignatureOf 𝕃 F) manifoldGerm) :
    HilbertSmith ∧ HilbertSmithWithBoundary ∧ PadicExclusionWithBoundary :=
  hilbertSmith_of_remaining 𝕃 F hNSS hLee hNew Prop92.classConstruction'_manifoldGerm hpinch

end HSFormal
