import HSFormal.InducedClass
import HSFormal.Germ
import HSFormal.LTheory.Theorem63

/-!
# Main theorem: Hilbert–Smith from the remaining hypotheses

Remaining hypotheses of `hilbertSmith_of_remaining` (`padicExclusion_of_remaining` uses only
`UniformNewman`, `𝕃` and the two open steps):

* Published inputs:
  * `NSSIsLie`: Gleason–Yamabe, Montgomery–Zippin [Gol10, §8];
  * `CompactNonLieContainsPadic`: Lee [Lee97, Thm 3.1];
  * `UniformNewman`: uniform Newman theorem [Pa18, Theorem (Newman)].
* `𝕃 : LTheory.LowerLTheory`: the ultimate lower L-groups `L^{⟨-∞⟩}` with their published
  properties [CP95, Definition 4.16], [Ran92, §17] (audited satisfiable).
* Open steps:
  * `ClassConstruction' manifoldGerm`: §§7–9, Proposition 9.2;
  * `PinchSignature (fibreSignatureOf 𝕃 F) manifoldGerm`, for a cut-flag choice `F`: §11,
    Lemma 11.2, (11.4)–(11.5).
-/

namespace HSFormal

open LTheory

/-- `padicExclusion_of_fine_steps` with the existential class construction `ClassConstruction'`. -/
theorem padicExclusion_of_fine_steps' (hMon : PointwisePeriodicIsPeriodic) (σ : FibreSignature)
    (germ : ManifoldGerm) (hcons : ClassConstruction' germ) (hind : InducedClassWeak)
    (htrans : TransferDivisibility σ) (hhtpy : GermHomotopyInvariance germ)
    (hpinch : PinchSignature σ germ) : PadicExclusion :=
  padicExclusion_of_steps' hMon σ germ hcons (cruxStar_of_steps hind htrans)
    (scalarSignatureOne_of_steps hhtpy hpinch)

theorem padicExclusion_of_remaining (𝕃 : LowerLTheory) (F : FlagChoice) (hNew : UniformNewman)
    (hcons : ClassConstruction' manifoldGerm)
    (hpinch : PinchSignature (fibreSignatureOf 𝕃 F) manifoldGerm) : PadicExclusion :=
  padicExclusion_of_fine_steps' (pointwisePeriodicIsPeriodic_of_uniformNewman hNew)
    (fibreSignatureOf 𝕃 F) manifoldGerm hcons inducedClass.toWeak (transferDivisibility_of 𝕃 F)
    germHomotopyInvariance hpinch

theorem hilbertSmith_of_remaining (𝕃 : LowerLTheory) (F : FlagChoice) (hNSS : NSSIsLie)
    (hLee : CompactNonLieContainsPadic) (hNew : UniformNewman)
    (hcons : ClassConstruction' manifoldGerm)
    (hpinch : PinchSignature (fibreSignatureOf 𝕃 F) manifoldGerm) :
    HilbertSmith ∧ HilbertSmithWithBoundary ∧ PadicExclusionWithBoundary :=
  hilbertSmith_all_of_padicExclusion hNSS hLee hNew <|
    padicExclusion_of_remaining 𝕃 F hNew hcons hpinch

end HSFormal
