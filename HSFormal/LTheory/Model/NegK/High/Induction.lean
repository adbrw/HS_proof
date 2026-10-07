import HSFormal.LTheory.Model.NegK.High.BassStatement
import HSFormal.LTheory.Model.NegK.High.RegKarStatement
import HSFormal.LTheory.Model.NegK.Final

/-!
# The final induction (NegKHigh, module N14)

`blueprint/negK-high.md` §5 ("Assembly"), §7 row N14; review `negK-high-review.md` §2.

For an additive category `D`, `VStab D` says that every Kar object of `D` is stably free, and
`VInd B m l := VStab (L^l (czIter m B))` is the blueprint's `V(m, l)`.  For
`B = finSuppFreeQG G T` (all `G`, all `T`, including infinite `T`):

* **Step** (`vInd_succ`, any `InvCat` `B`): Theorem B with `Y = czIter m B` gives
  `V(m + 1, l) ⇐ V(m, l + 1)`.  The new Laurent variable goes outside the remaining `czIter`:
  `L^l (C_ℤ (czIter m B)) ↝ L^{l+1} (czIter m B)`, and `czIter (m + 1) B = (czIter m B).cz` and
  `L^{l+1} = L^l ∘ L` hold by `rfl`.
* **Base** (`vInd_one`): `V(1, l)` from Theorem B (`(X, p) ∼ Π(E)`), Theorem R in Kar form
  (`E ⊞ ι⁺Q₁ ∼ ι⁺Q₀`), additivity of `Π`, and Lemma F (`Π(ι⁺Q) ∼ 0`,
  `CZ.Lpow.stablyIso_zero_periodize_pos`).
* **End** (`negKHighStablyFree_of`): `V(k, 0)` for `k ≥ 2` is literally the `k`-th clause of
  `NegKHighStablyFree (finSuppFreeQG G T)` (`L^0 D = D` with the same instances, by `rfl`).

**Main result**: `negKHighAll_of : TheoremBStatement → RegKarStatement → NegKHighAll`, and with
`NegK/Final.lean` (Theorem A at level `1`) `negKAll_of : … → NegKAll`.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive Idempotents ZeroObject

noncomputable section

universe v u

/-! ### The predicate `V(m, l)` -/

/-- **`VStab D`**: every Kar object `(M, e)` of the additive category `D` is stably free,
`(M, e) ⊕ F ≅ F'` for objects `F, F'` of `D` (`blueprint/negK-high.md` §5). -/
def VStab (D : AddCat.{v, u}) : Prop :=
  ∀ (M : D.carrier) (e : D.Mor M M), e ≫ e = e → ∃ F F' : D.carrier, KarStablyFree e F F'

/-- `VStab D` in terms of `StablyIso`: every Kar object of `D` is stably zero. -/
lemma vStab_iff (D : AddCat.{v, u}) : VStab D ↔ ∀ P : Karoubi D.carrier, StablyIso P 0 :=
  ⟨fun h P ↦ (stablyIso_zero_iff P).mpr (h P.X P.p P.idem),
    fun h M e he ↦ (stablyIso_zero_iff ⟨M, e, he⟩).mp (h _)⟩

/-- **`V(m, l)`** (`blueprint/negK-high.md` §5): every Kar object of `L^l (czIter m B)` is
stably free. -/
def VInd (B : InvCat) (m l : ℕ) : Prop :=
  VStab (Lpow l (B.czIter m : AddCat))

lemma vInd_iff (B : InvCat) (m l : ℕ) :
    VInd B m l ↔ ∀ P : Karoubi (Lpow l (B.czIter m : AddCat)).carrier, StablyIso P 0 :=
  vStab_iff _

/-- At `l = 0`, `V(k, 0)` is literally the `k`-th clause of `NegKHighStablyFree`. -/
lemma negKHighStablyFree_iff_vInd (B : InvCat) :
    NegKHighStablyFree B ↔ ∀ k, 2 ≤ k → VInd B k 0 :=
  Iff.rfl

/-! ### The step `V(m + 1, l) ⇐ V(m, l + 1)` (Theorem B) -/

/-- **The induction step** (`blueprint/negK-high.md` §5, step `m + 1`), for every `InvCat` `B`:
Theorem B with `Y = czIter m B` cuts the outermost `C_ℤ` coordinate,
`(X, p) ∼ Π(E)` with `E` a Kar object of `L^l (L (czIter m B)) = L^{l+1} (czIter m B)`;
`V(m, l + 1)` gives `E ∼ 0`, hence `Π(E) ∼ 0`. -/
theorem vInd_succ (hB : TheoremBStatement) (B : InvCat) (m l : ℕ) (h : VInd B m (l + 1)) :
    VInd B (m + 1) l :=
  (vInd_iff B (m + 1) l).mpr fun P ↦
    stablyIso_zero_of_theoremB hB (Y := B.czIter m) ((vInd_iff B m (l + 1)).mp h) P.p P.idem

/-! ### The base `V(1, l)` (Theorem B, Theorem R, Lemma F) -/

/-- **Lemma F** in `karoubiMap` form: `Π(ι⁺ Q)` is stably zero in `Karoubi (L^l (C_ℤ Y))` for
every Kar object `Q` of the faces category `L^l (L⁺ Y)`. -/
lemma stablyIso_zero_periodize_incl {Y : InvCat} {l : ℕ}
    (Q : Karoubi (Lpow l (LaurentPos (Y : AddCat))).carrier) :
    StablyIso ((karoubiMap (Lpow.map l (CZ.periodize Y))).obj
      ((karoubiMap (Lpow.map l (LaurentPos.incl (Y : AddCat)))).obj Q)) 0 :=
  CZ.Lpow.stablyIso_zero_periodize_pos Q.idem

section Base

variable {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]

/-- **The base `V(1, l)`** (`blueprint/negK-high.md` §5, base `m = 1`), `B = finSuppFreeQG G T`:
1. Theorem B (`Y = B`): `(X, p) ∼ Π(E)` with `E` a Kar object of `L^{l+1} B`;
2. Theorem R (Kar form, `n = l + 1`): `E ⊞ ι⁺Q₁ ∼ ι⁺Q₀`;
3. `Π` is additive: `Π(E) ⊞ Πι⁺Q₁ ≅ Π(E ⊞ ι⁺Q₁) ∼ Πι⁺Q₀`;
4. Lemma F: `Πι⁺Q₀ ∼ 0` and `Πι⁺Q₁ ∼ 0`; hence `Π(E) ∼ 0` and `(X, p) ∼ 0`. -/
theorem vInd_one (hB : TheoremBStatement) (hR : RegKarStatement) (T : Set ℕ) (l : ℕ) :
    VInd (finSuppFreeQG G T) 1 l := by
  refine (vInd_iff _ 1 l).mpr fun P ↦ ?_
  obtain ⟨E, hE⟩ := hB (finSuppFreeQG G T) l P.X P.p P.idem
  obtain ⟨Q₀, Q₁, hQ⟩ := hR G T l E
  let Per := karoubiMap (Lpow.map l (CZ.periodize (finSuppFreeQG G T)))
  let ιp := karoubiMap (Lpow.map l (LaurentPos.incl (finSuppFreeQG G T : AddCat)))
  have := preservesBinaryBiproducts_of_preservesBiproducts Per
  have h₁ : StablyIso (Per.obj (E ⊞ ιp.obj Q₁)) (Per.obj (ιp.obj Q₀)) :=
    hQ.map (Lpow.map l (CZ.periodize (finSuppFreeQG G T)))
  have h₂ : StablyIso (Per.obj E) 0 :=
    (StablyIso.biprod_zero _).symm.trans <|
      (StablyIso.biprod_left _ (stablyIso_zero_periodize_incl Q₁).symm).trans <|
        (StablyIso.of_iso (Per.mapBiprod E (ιp.obj Q₁)).symm).trans <|
          h₁.trans (stablyIso_zero_periodize_incl Q₀)
  exact hE.trans h₂

/-! ### The induction on `m` and the end -/

/-- **`V(m, l)` for all `m ≥ 1` and all `l`** (`blueprint/negK-high.md` §5): induction on `m`
with `l` generalized, `V(m + 1, l) ⇐ V(m, l + 1)`, so
`V(k, 0) ⇐ V(k - 1, 1) ⇐ … ⇐ V(1, k - 1)`. -/
theorem vInd_of_one_le (hB : TheoremBStatement) (hR : RegKarStatement) (T : Set ℕ) {m : ℕ}
    (hm : 1 ≤ m) (l : ℕ) : VInd (finSuppFreeQG G T) m l := by
  induction m, hm using Nat.le_induction generalizing l with
  | base => exact vInd_one hB hR T l
  | succ m _ ih => exact vInd_succ hB _ m l (ih (l + 1))

/-- **`NegKHighStablyFree (finSuppFreeQG G T)`**: `V(k, 0)` for `k ≥ 2`. -/
theorem negKHighStablyFree_of (hB : TheoremBStatement) (hR : RegKarStatement) (T : Set ℕ) :
    NegKHighStablyFree (finSuppFreeQG G T) :=
  (negKHighStablyFree_iff_vInd _).mpr fun _ hk ↦ vInd_of_one_le hB hR T (by omega) 0

end Base

/-- **`NegKHighAll` from Theorem B and Theorem R** (`blueprint/negK-high.md` §5, "End"):
`K₋ₖ(ℚ[Gᵢ]) = 0` for `k ≥ 2` in the iterated bounded form, for all `G` and all `T`. -/
theorem negKHighAll_of (hB : TheoremBStatement) (hR : RegKarStatement) : NegKHighAll :=
  negKHighAll_iff_stablyFree.mpr fun _ _ _ T ↦ negKHighStablyFree_of hB hR T

/-- With Theorem A (`NegK/Final.lean`): the full `NegKAll` input of module 22. -/
theorem negKAll_of (hB : TheoremBStatement) (hR : RegKarStatement) : NegKAll :=
  negKAll_of_negKHighAll (negKHighAll_of hB hR)

end

end HSFormal.LTheory
