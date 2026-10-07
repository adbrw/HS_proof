import HSFormal.Newman.Degree
import HSFormal.Newman.OrbitQuotient

/-!
# N7 statement: transfer vanishing (frozen)

`DegreeEqZeroOfFree` is the statement of the blueprint's hardest lemma
(`newman.md` §2.4, §5), adjusted to the real N5 (`degree`, `ldeg`) and N6 (`injOn_iterate`) APIs,
with coefficients `ZMod p`. It is proved as `HSFormal.Newman.degreeEqZeroOfFree` in
`HSFormal/Newman/Transfer.lean`; the theorem form `HSFormal.Newman.degree_eq_zero_of_free` has
the same binders in the same order. This file exists so that N8 can be written against the
statement independently of the proof.
-/

namespace HSFormal.Newman

/-- **Transfer vanishing** (blueprint §2.4, the hardest lemma), as a proposition: the degree of a
`⟨g⟩`-invariant map over a value whose fibre is acted on freely by the prime-order `g` is `0` in
`ZMod p`, provided every iterate `g^[j]`, `0 < j < p`, has local degree `1` everywhere. -/
def DegreeEqZeroOfFree : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] {m : ℕ} {W : Set (EuclideanSpace ℝ (Fin (m + 1)))} (hW : IsOpen W)
    {g : EuclideanSpace ℝ (Fin (m + 1)) → EuclideanSpace ℝ (Fin (m + 1))}
    (hgW : Set.MapsTo g W W) (hgc : ContinuousOn g W) (hper : ∀ w ∈ W, g^[p] w = w),
    (∀ w ∈ W, g w ≠ w) →
    (∀ j, 0 < j → j < p → ∀ w (hw : w ∈ W),
      ldeg (ZMod p) hW (g^[j]) (hgc.iterate hgW j) (injOn_iterate hgW hper j) w hw = 1) →
    ∀ {A : EuclideanSpace ℝ (Fin (m + 1)) → EuclideanSpace ℝ (Fin (m + 1))}
      (hA : ContinuousOn A W), (∀ w ∈ W, A (g w) = A w) →
    ∀ {y : EuclideanSpace ℝ (Fin (m + 1))} (hK : IsCompact {w : W | A w = y}),
      degree (ZMod p) hW A hA y hK = 0

end HSFormal.Newman
