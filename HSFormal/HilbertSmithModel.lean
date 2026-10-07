import HSFormal.HilbertSmith
import HSFormal.LTheory.Model.Instance
import HSFormal.LTheory.Model.LiftingPairNull
import HSFormal.LTheory.Model.CutInjDecBij
import HSFormal.LTheory.Model.NegK.Final
import HSFormal.LTheory.Model.LiftingClosedSub
import HSFormal.LTheory.Model.UnionRel
import HSFormal.LTheory.Model.HalfLineSplit

/-!
# The Hilbert–Smith theorem with the concrete lower L-theory model

`HSFormal/HilbertSmith.lean` proves the theorem from an abstract `𝕃 : LowerLTheory`; here `𝕃` is
the colimit model `LTheory.lowerLModel hL hA hD` (`HSFormal/LTheory/Model/Instance.lean`,
`L := Lmodel`), so the L-theory input is reduced to three precisely stated lemmas about the
model.  This is the Lean v4.27 branch, where the published inputs are still hypotheses.

**Remaining hypotheses, and where each is being proved.**
* L-theory (`blueprint/lower-L-construction.md` §4):
  * `LTheory.LiftingPairNullAll` (`HSFormal/LTheory/Model/Bdry.lean`): (L2), uniqueness of
    lifting pairs in null-cobordism form — **proved** (`liftingPairNullAll`,
    `HSFormal/LTheory/Model/LiftingPairNull.lean`), discharged in `hilbertSmith_of_model'`;
  * `LTheory.LiftingClosedSubAll` (`HSFormal/LTheory/Model/Exact.lean`): (L2) for closed
    lifting pairs — module 17;
  * `LTheory.DecBijModel` (`HSFormal/LTheory/Model/Instance.lean`): bijectivity of the
    decoration map for `⊕_{i ∈ T} Free(ℚ[Gᵢ])` in degrees `n ≥ 0` — module 22 (`DecBij`), from
    `NegK` (`HSFormal/LTheory/Model/NegK.lean`).
* Published inputs, proved on the v4.35 port (with TauCeti; not compiled on this branch):
  * `NSSIsLie` (Gleason–Yamabe): `HSFormal.GY.nssIsLie`, `HSFormal/Inputs/GY/NSSIsLie.lean`;
  * `CompactTorsionFreeContainsPadic` ([Tao11, Lemma 7]):
    `HSFormal.Lemma7.compactTorsionFreeContainsPadic`, `HSFormal/Inputs/Lemma7.lean`;
  * `NewmanPrimeOrder` (Newman's theorem for prime order): `HSFormal.Newman.newmanPrimeOrder`,
    `HSFormal/Newman/Newman.lean`.
-/

namespace HSFormal

open LTheory

/-- `p`-adic exclusion from the model: the remaining hypotheses are the three L-theory lemmas
(modules 17, 22) and Newman's theorem for prime order. -/
theorem padicExclusion_of_model (hL : LiftingPairNullAll) (hA : LiftingClosedSubAll)
    (hD : DecBijModel) (hNew : NewmanPrimeOrder) : PadicExclusion :=
  padicExclusion_of_inputs (lowerLModel hL hA hD) hNew

/-- **The Hilbert–Smith theorem from the model**: the remaining hypotheses are the three
L-theory lemmas (modules 17, 22) and the published inputs Gleason–Yamabe, [Tao11, Lemma 7] and
Newman's theorem for prime order (proved on the v4.35 port). -/
theorem hilbertSmith_of_model (hL : LiftingPairNullAll) (hA : LiftingClosedSubAll)
    (hD : DecBijModel) (hNSS : NSSIsLie) (hT : CompactTorsionFreeContainsPadic)
    (hNew : NewmanPrimeOrder) :
    HilbertSmith ∧ HilbertSmithWithBoundary ∧ PadicExclusionWithBoundary :=
  hilbertSmith_of_inputs (lowerLModel hL hA hD) hNSS hT hNew

/-- `hilbertSmith_of_model` with (L2) for lifting pairs discharged (`liftingPairNullAll`). -/
theorem hilbertSmith_of_model' (hA : LiftingClosedSubAll) (hD : DecBijModel) (hNSS : NSSIsLie)
    (hT : CompactTorsionFreeContainsPadic) (hNew : NewmanPrimeOrder) :
    HilbertSmith ∧ HilbertSmithWithBoundary ∧ PadicExclusionWithBoundary :=
  hilbertSmith_of_model liftingPairNullAll hA hD hNSS hT hNew

/-- `hilbertSmith_of_model'` with `DecBijModel` reduced to its inputs: `NegK` at levels `k ≥ 2`
(`NegKHighAll`; level 1 is proved, `NegK/Final.lean`), the union relation (R) and the half-line
splitting (`Model/CutInjDecBij.lean`, `Model/CutSurj.lean`). -/
theorem hilbertSmith_of_model'' (hA : LiftingClosedSubAll) (hK : NegKHighAll)
    (hR : ∀ (G : ℕ → Type) [∀ i, Group (G i)] [∀ i, Fintype (G i)] (T : Set ℕ) (k : ℕ) (N : ℤ),
      0 ≤ N → UnionRel ((finSuppFreeQG G T).czIter k).cz N)
    (hL : ∀ (G : ℕ → Type) [∀ i, Group (G i)] [∀ i, Fintype (G i)] (T : Set ℕ) (k : ℕ) (N : ℤ),
      0 ≤ N → HalfLineSplitKar ((finSuppFreeQG G T).czIter k) N)
    (hNSS : NSSIsLie) (hT : CompactTorsionFreeContainsPadic) (hNew : NewmanPrimeOrder) :
    HilbertSmith ∧ HilbertSmithWithBoundary ∧ PadicExclusionWithBoundary :=
  hilbertSmith_of_model' hA (decBijModel_of_unionRel_halfLine (negKAll_of_negKHighAll hK) hR hL)
    hNSS hT hNew

/-- **The Hilbert–Smith theorem from the model with both (L2) lemmas proved** (`liftingPairNullAll`,
`liftingClosedSubAll`). Remaining: `NegK` at levels `k ≥ 2` (classical: `K₋ₖ(ℚ[G]) = 0`), the
union relation (R) and the half-line splitting (in progress), and the published inputs (proved on
the v4.35 port). -/
theorem hilbertSmith_of_model''' (hK : NegKHighAll)
    (hR : ∀ (G : ℕ → Type) [∀ i, Group (G i)] [∀ i, Fintype (G i)] (T : Set ℕ) (k : ℕ) (N : ℤ),
      0 ≤ N → UnionRel ((finSuppFreeQG G T).czIter k).cz N)
    (hL : ∀ (G : ℕ → Type) [∀ i, Group (G i)] [∀ i, Fintype (G i)] (T : Set ℕ) (k : ℕ) (N : ℤ),
      0 ≤ N → HalfLineSplitKar ((finSuppFreeQG G T).czIter k) N)
    (hNSS : NSSIsLie) (hT : CompactTorsionFreeContainsPadic) (hNew : NewmanPrimeOrder) :
    HilbertSmith ∧ HilbertSmithWithBoundary ∧ PadicExclusionWithBoundary :=
  hilbertSmith_of_model'' liftingClosedSubAll hK hR hL hNSS hT hNew

/-- The Hilbert–Smith theorem from the model with (L2) and the union relation (R) proved
(`unionRel`). Remaining: `NegK` at levels `k ≥ 2`, the half-line splitting, and the published
inputs (proved on the v4.35 port). -/
theorem hilbertSmith_of_model₄ (hK : NegKHighAll)
    (hL : ∀ (G : ℕ → Type) [∀ i, Group (G i)] [∀ i, Fintype (G i)] (T : Set ℕ) (k : ℕ) (N : ℤ),
      0 ≤ N → HalfLineSplitKar ((finSuppFreeQG G T).czIter k) N)
    (hNSS : NSSIsLie) (hT : CompactTorsionFreeContainsPadic) (hNew : NewmanPrimeOrder) :
    HilbertSmith ∧ HilbertSmithWithBoundary ∧ PadicExclusionWithBoundary :=
  hilbertSmith_of_model''' hK (fun _ _ _ _ k N _ ↦ unionRel _ N) hL hNSS hT hNew

/-- **The Hilbert–Smith theorem from the concrete lower L-theory model, with every model lemma
proved** (`liftingPairNullAll`, `liftingClosedSubAll`, `unionRel`, `halfLineSplitKar`, `NegK` at
level 1). Remaining: `NegKHighAll` (classical: `K₋ₖ(ℚ[G]) = 0` for `k ≥ 2`, being formalized on
the v4.35 port) and the published inputs (proved on the v4.35 port). -/
theorem hilbertSmith_of_model₅ (hK : NegKHighAll) (hNSS : NSSIsLie)
    (hT : CompactTorsionFreeContainsPadic) (hNew : NewmanPrimeOrder) :
    HilbertSmith ∧ HilbertSmithWithBoundary ∧ PadicExclusionWithBoundary :=
  hilbertSmith_of_model₄ hK (fun _ _ _ _ k N _ ↦ halfLineSplitKar _ N) hNSS hT hNew

end HSFormal
