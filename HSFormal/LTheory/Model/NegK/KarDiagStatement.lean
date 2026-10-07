import HSFormal.LTheory.Model.CZFunctor
import HSFormal.LTheory.Interface

/-!
# Theorem A (two-flag bounded splitting): the statement

`blueprint/negK-proof.md` §2.4.  Let `B = finSuppFreeQG G T` (any `G`, any `T ⊆ ℕ`, in particular
infinite `T`), `X ∈ C_ℤ(B)` and `p : X ⟶ X` an idempotent of propagation `≤ b`.  Then `(X, p)` is
Kar-isomorphic to a **diagonal** idempotent `CZ.diag d` on some `Q ∈ C_ℤ(B)` (each `d v` an
idempotent of `B`), i.e. to an object of `C_ℤ(Kar B)`, through maps of propagation `≤ b`
(`α : X ⟶ Q`) and `≤ 2b` (`β : Q ⟶ X`).

The proof (`Model/NegK/KarDiag.lean`, `karDiag`) takes `Q_v = ⊞_{w ∈ [v - 2b, v]} X_w` (the
chosen unitary partial sums `CZ.Tower`); the statement only asserts existence of `Q`.

The four Kar conditions `p ≫ α = α`, `α ≫ diag d = α`, `diag d ≫ β = β`, `β ≫ p = β` are part of
the statement, so that `α, β` directly form a `Wall.KarIso p (CZ.diag d)`.  (They also follow
from `α ≫ β = p` and `β ≫ α = diag d` after replacing `α, β` by `α ≫ diag d`, `diag d ≫ β`,
which does not change the propagation bounds since `diag d` has propagation `0`.)
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive

/-- **Theorem A** (`blueprint/negK-proof.md` §2.4, two-flag bounded splitting).  For every
idempotent `p` of propagation `≤ b` on `X ∈ C_ℤ(finSuppFreeQG G T)` there are `Q ∈ C_ℤ(B)`,
idempotents `d v` on `Q_v`, and `α : X ⟶ Q` (propagation `≤ b`), `β : Q ⟶ X` (propagation
`≤ 2b`) with `α ≫ β = p`, `β ≫ α = CZ.diag d`, and the Kar conditions
`p ≫ α = α`, `α ≫ diag d = α`, `diag d ≫ β = β`, `β ≫ p = β`; i.e. `(α, β)` is a Kar
isomorphism `(X, p) ≅ (Q, diag d)` (`Wall.KarIso`). -/
def KarDiagStatement : Prop :=
  ∀ (G : ℕ → Type) [∀ i, Group (G i)] [∀ i, Fintype (G i)] (T : Set ℕ)
    (X : (finSuppFreeQG G T).cz) (p : X ⟶ X), p ≫ p = p → ∀ b : ℕ, CZ.PropLE p.1 b →
    ∃ (Q : (finSuppFreeQG G T).cz) (d : ∀ v, Q.obj v ⟶ Q.obj v) (α : X ⟶ Q) (β : Q ⟶ X),
      (∀ v, d v ≫ d v = d v) ∧ α ≫ β = p ∧ β ≫ α = CZ.diag d ∧
      p ≫ α = α ∧ α ≫ CZ.diag d = α ∧ CZ.diag d ≫ β = β ∧ β ≫ p = β ∧
      CZ.PropLE α.1 b ∧ CZ.PropLE β.1 (2 * b)

end HSFormal.LTheory
