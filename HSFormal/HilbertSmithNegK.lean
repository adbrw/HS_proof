import HSFormal.HilbertSmithFinal
import HSFormal.LTheory.Model.NegK.High.Induction
import HSFormal.LTheory.Model.NegK.High.RegKar
import HSFormal.LTheory.Model.NegK.High.BassSplitting

/-!
# The Hilbert–Smith theorem

`NegKHighAll` (`K₋ₖ(ℚ[G]) = 0` for `k ≥ 2`, in the iterated bounded-category form used by the
concrete lower L-theory model) is proved by the induction `negKHighAll_of`
(`NegK/High/Induction.lean`) from the controlled Bass splitting `theoremB`
(`NegK/High/BassSplitting.lean`) and Theorem R in Karoubi form `Reg.regKarStatement`
(`NegK/High/RegKar.lean`); see `blueprint/negK-high.md`. With it, `hilbertSmith_of_negKHigh`
(`HilbertSmithFinal.lean`) has no hypotheses left.
-/

namespace HSFormal

open LTheory

theorem negKHighAll : NegKHighAll :=
  negKHighAll_of theoremB Reg.regKarStatement

theorem hilbertSmith_of_theoremB (hB : TheoremBStatement) :
    HilbertSmith ∧ HilbertSmithWithBoundary ∧ PadicExclusionWithBoundary :=
  hilbertSmith_of_negKHigh (negKHighAll_of hB Reg.regKarStatement)

/-- **The Hilbert–Smith theorem**, with boundary and `p`-adic exclusion forms
(statements in `HSFormal/Statement.lean`). -/
theorem hilbertSmith_all :
    HilbertSmith ∧ HilbertSmithWithBoundary ∧ PadicExclusionWithBoundary :=
  hilbertSmith_of_negKHigh negKHighAll

/-- **The Hilbert–Smith conjecture**: a locally compact group acting continuously and effectively
on a connected topological manifold is a Lie group (`HSFormal.HilbertSmith`). -/
theorem hilbertSmith : HilbertSmith :=
  hilbertSmith_all.1

end HSFormal
