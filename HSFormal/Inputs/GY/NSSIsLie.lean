import HSFormal.Inputs.GY.WeakGleason
import HSFormal.Inputs.GY.Gleason
import HSFormal.Inputs.GY.ExpChart
import HSFormal.Inputs.GY.SmoothMul
import HSFormal.Inputs.GY.LieStructure

/-!
# The Gleason–Yamabe theorem: `HSFormal.NSSIsLie` (final assembly)

A locally compact Hausdorff group with no small subgroups is a Lie group:

1. A4 `nonempty_weakGleasonNorm`: NSS ⇒ a weak Gleason norm;
2. A5 `WeakGleasonNorm.nonempty_gleasonNorm`: weak Gleason norm ⇒ Gleason norm;
3. B5 `GleasonNorm.exists_localExpStructure`: Gleason norm ⇒ a `LocalExpStructure` on `ℝ^d`;
4. C3 `LocalExpStructure.contDiffMu`: the group law is `C^∞` in exponential coordinates;
5. C4 `LocalExpStructure.isLieGroup`: hence `IsLieGroup G`.

`SecondCountableTopology G` (part of the statement `NSSIsLie`) is not used.
-/

namespace HSFormal.GY

/-- **Gleason–Yamabe**: no small subgroups implies Lie (`HSFormal.NSSIsLie`). -/
theorem nssIsLie : HSFormal.NSSIsLie := by
  intro G _ _ _ _ _ _ hNSS
  obtain ⟨𝒩⟩ := nonempty_weakGleasonNorm hNSS
  obtain ⟨𝒢⟩ := 𝒩.nonempty_gleasonNorm
  obtain ⟨d, ⟨S⟩⟩ := 𝒢.exists_localExpStructure
  exact S.isLieGroup S.contDiffMu

end HSFormal.GY
