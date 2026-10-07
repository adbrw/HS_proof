import HSFormal.LTheory.Model.Bdry
import HSFormal.LTheory.Model.BoundaryConstructionRel
import HSFormal.LTheory.Model.CutIsoGen

/-!
# (L2): lifting pairs of null-cobordant complexes have null-cobordant boundaries

`blueprint/lower-L-construction.md` §3.2 "(L2) Relative lifting": proof of the hypothesis
`LiftingPairNullAll` of `Model/Bdry.lean` (`liftingPairNullAll`).

## Proof

Let `D` be a closed `(N+1)`-complex over `C_ℤ^{∘k}(A/U)` with `0 ≤ N + 1`, null-cobordant, and
`P` a lifting pair at level `k + 1` of `D ⊗ ℝ`, i.e. a Poincaré pair `X = P.X` over
`F_{k+1} = C_ℤ^{∘(k+1)} F` with boundary in `U_{k+1}` and an isometry
`P.iso : X.toQuot ≃ (D ⊗ ℝ)` (transported along `czIterQuotIso`).

1. A null-cobordism `Y : PairOn D` (`nullCobordant_iff_nonempty_pairOn`) gives the line pair
   `Y ⊗ ℝ` (`LineData.pair`) with boundary `D ⊗ ℝ` **on the nose** and interior the line complex
   `(Y_D, p) ⊗ ℝ`; the relative e-trick `SymPair.freeLineD` replaces the interior by its free
   model (identity idempotent, supported in `[0, N + 3]`), keeping the boundary
   (`LineData.freePairOn`).  So the free-ification happens already at level `k + 1`: no extra
   transition is needed, because the null-cobordism being made free is that of `D` (over
   `C_ℤ^{∘k}`), not one of `X.toQuot`.
2. Transport along the strict isomorphism `(czIterQuotIso (k+1)).inv` (`SymPair.map`; the
   idempotent stays `1`), then retarget along `P.iso.symm` (`PairOn.retargetIso`, CutIsoGen; the
   interior is unchanged): a null-cobordism of `X.toQuot`, free on `[0, N + 3]`.
3. With the face `W = PairData.ofPairOn X.toPairOn` (so `quotBd W = X.toQuot` definitionally),
   module 10's `TriadOn.nullCobordant_lift_of_quotPair` gives `NullCobordant (X.bd.lift)`, i.e.
   `NullCobordant P.bd` (`LiftingPair.nullCobordant_bd`), hence `P.bdCls = 0`
   (`Lconc.cls_eq_zero`) and `ofDeg (bdClsAt P) = 0`.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex

noncomputable section

attribute [local implicit_reducible] KaroubiFiltration.czIter InvCat.czIter SymPair.map

namespace LineData

variable {A B : InvCat} (L : LineData A B) {N : ℤ} {D : SymPoincare A.inv N}

/-- **A free null-cobordism of `D ⊗ ℝ`**: for a null-cobordism `Y` of `D`, the line pair
`Y ⊗ ℝ` with its interior made free (`SymPair.freeLineD`); its boundary is `D ⊗ ℝ` on the
nose and its interior idempotent is the identity. -/
def freePairOn (Y : PairOn D) : PairOn (L.sym D) :=
  ((L.pair Y.toPair).freeLineD L Y.pD_idem Y.support
    (KarHtpyEquiv.refl (L.pair Y.toPair).pD_idem)).toPairOn

@[simp]
lemma freePairOn_pD (Y : PairOn D) : (L.freePairOn Y).pD = 𝟙 _ := rfl

end LineData

namespace KaroubiFiltration

variable {A : InvCat} {F : KaroubiFiltration A}

/-- **(L2) for a single lifting pair**: if the target `D'` of a lifting pair `P` bounds a
Poincaré pair `Y` over `Kar(A/U)` whose interior is free on `[0, N + 2]`, then the boundary of
`P` is null-cobordant over `Kar(U)`.  The face is `W = P.X` itself (so `W/U = P.X.toQuot`), `Y`
is retargeted along `P.iso` to a null-cobordism of `W/U`, and module 10
(`TriadOn.nullCobordant_lift_of_quotPair`) does the rest. -/
theorem LiftingPair.nullCobordant_bd {N : ℤ} {D' : SymPoincare F.quot.inv (N + 1)}
    (P : F.LiftingPair D') (Y : PairOn D')
    (hpY : ∀ r, 0 ≤ r → r ≤ N + 1 + 1 → Y.pD.f r = 𝟙 _) (hN : 0 ≤ N + 1) :
    NullCobordant P.bd :=
  TriadOn.nullCobordant_lift_of_quotPair (F := F) (W := PairData.ofPairOn P.X.toPairOn) P.mem
    (PairData.isPoincare_ofPairOn _) (Y.retargetIso P.iso.symm) hpY hN

/-- **(L2)** (`LiftingPairNull`) for every Karoubi filtration. -/
theorem liftingPairNull (F : KaroubiFiltration A) : F.LiftingPairNull := by
  intro k N D hN hD P n h
  obtain ⟨Y⟩ := nullCobordant_iff_nonempty_pairOn.1 hD
  let L := CZ.lineData (F.quot.czIter k)
  let Φ := (F.czIterQuotIso (k + 1)).inv
  let Z : PairOn ((L.sym D).map Φ) := ((L.freePairOn Y).toPair.map Φ).toPairOn
  have hbd : NullCobordant (LiftingPair.bd P) :=
    LiftingPair.nullCobordant_bd P Z (fun r _ _ ↦ by
      dsimp [Z, SymPair.toPairOn]; simp
      exact congrArg (fun f ↦ HomologicalComplex.Hom.f f r)
        ((Φ.F.mapHomologicalComplex (ComplexShape.down ℤ)).map_id _)) (by omega)
  have h0 : LiftingPair.bdCls P = 0 := Lconc.cls_eq_zero hbd
  simp [LiftingPairAt.bdClsAt, h0]

end KaroubiFiltration

/-- **(L2) for all Karoubi filtrations**: the hypothesis `LiftingPairNullAll` of the model's
boundary map holds. -/
theorem liftingPairNullAll : LiftingPairNullAll := fun _ F ↦ F.liftingPairNull

end

end HSFormal.LTheory
