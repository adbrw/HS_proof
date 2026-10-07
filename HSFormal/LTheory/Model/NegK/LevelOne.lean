import HSFormal.LTheory.Model.NegK.KarSwindle
import HSFormal.LTheory.Model.NegK.KarDiagStatement

/-!
# `NegK` at level `1`, and the split `NegK = NegKHigh + level 1` (NegK, module 7)

`blueprint/negK-proof.md` §2.4 "Corollary (k = 1)", §5 row 7 and §8 "Decision".

* `NegKOne B`: level `k = 1` of `NegK B` (every object of `Kar C_ℤ(B)` is absorbed by a free
  object).  `NegKHigh B`: the same statement as `NegK B` restricted to `k ≥ 2`.
* `NegK.of_high : NegKHigh B → NegKOne B → NegK B` (and `NegK.iff_high`); `NegKStablyFree.of_high`
  is the form consumed by the Wall trick (`Model/Wall.lean`).
* `NegK.iff_stablyFree`, `negKHigh_iff_stablyFree`: for every `InvCat` `B`, the absorbing and
  the stably-free forms are equivalent at every level `k ≥ 1`.
* `negKOne_of_karDiagonalizable`: level `1` holds for every `InvCat` `B` whose idempotents on
  `C_ℤ(B)` are Kar-isomorphic to diagonal ones (`CZ.KarDiagonalizable`, Lemma D of
  `KarSwindle.lean`).
* **`negK_levelOne`**: under Theorem A (`KarDiagStatement`, `Model/NegK/KarDiagStatement.lean`),
  `NegKOne (finSuppFreeQG G T)` for all `G`, `T` (including infinite `T`).
* `negK_of_high`, `negKAll_of_high`: `NegK (finSuppFreeQG G T)` from Theorem A and `NegKHigh`.

**Stably free vs. absorbing.**  `NegKHighStablyFree B` (`(M, e) ⊕ F ≅ F'`, `k ≥ 2`) is equivalent
to `NegKHigh B` (`negKHigh_iff_stablyFree`, from `karAbsorbs_of_karStablyFree`: free objects of
`C_ℤ(A)` are absorbed by Lemma D, so `P ⊕ F ≅ F'` gives `P ⊕ (G ⊞ G') ≅ G ⊞ G'` for
`F ⊕ G ≅ G`, `F' ⊕ G' ≅ G'`).  So the remaining trusted input may be taken in the weaker
stably-free form, which is `K₋ₖ(B) = 0` for `k ≥ 2` literally (`[P] = [F'] - [F]` with
`[F] = [F'] = 0` by the swindle).

**Downstream wiring (module 22, `DecBij`).**  `lowerLModel` (`Model/Instance.lean`) takes
`hD : DecBijModel`; module 22 is to prove `DecBijModel` from `NegKAll`, i.e.
`∀ G T, NegK (finSuppFreeQG G T)`, through the Wall trick (`NegK.stablyFree`,
`NegKStablyFree.stablyFreeObjects`).  With this file it suffices to assume
`NegKHighAll := ∀ G T, NegKHigh (finSuppFreeQG G T)` (or the equivalent
`NegKHighStablyFreeAll`, `negKHighAll_iff_stablyFree`) together with Theorem A
(`KarDiagStatement`, being proved in `Model/NegK/KarDiag.lean`):
`negKAll_of_high : KarDiagStatement → NegKHighAll → NegKAll`.  Once
`KarDiagStatement` is proved, the hypothesis of `lowerLModel` becomes
`hK : NegKHighAll` (`blueprint/negK-proof.md` §8, step 2), i.e. "`K₋ₖ(ℚGᵢ) = 0` for `k ≥ 2` in
iterated bounded form".
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive

noncomputable section

/-! ### Splitting `NegK` by level -/

/-- Level `k = 1` of `NegK B`: every object `(M, e)` of `Kar C_ℤ(B)` is absorbed by a free
object, `(M, e) ⊕ F ≅ F`. -/
def NegKOne (B : InvCat) : Prop :=
  ∀ (M : B.czIter 1) (e : M ⟶ M), e ≫ e = e → ∃ F : B.czIter 1, KarAbsorbs e F

/-- **`NegKHigh`**: the statement of `NegK B` restricted to the levels `k ≥ 2`,
`K₋ₖ(B) = K₀(Kar C_ℤ^{∘k} B) = 0` for `k ≥ 2`. -/
def NegKHigh (B : InvCat) : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ (M : B.czIter k) (e : M ⟶ M), e ≫ e = e →
    ∃ F : B.czIter k, KarAbsorbs e F

/-- The stably-free form of `NegKHigh` (`(M, e) ⊕ F ≅ F'`), equivalent to it
(`negKHigh_iff_stablyFree`). -/
def NegKHighStablyFree (B : InvCat) : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ (M : B.czIter k) (e : M ⟶ M), e ≫ e = e →
    ∃ F F' : B.czIter k, KarStablyFree e F F'

/-- `NegK` from its levels `k ≥ 2` and its level `1`. -/
theorem NegK.of_high {B : InvCat} (hH : NegKHigh B) (h₁ : NegKOne B) : NegK B := fun k hk ↦ by
  rcases Nat.lt_or_ge k 2 with h | h
  · obtain rfl : k = 1 := by omega
    exact h₁
  · exact hH k h

/-- `NegK B` is exactly `NegKHigh B` together with level `1`. -/
theorem NegK.iff_high {B : InvCat} : NegK B ↔ NegKHigh B ∧ NegKOne B :=
  ⟨fun h ↦ ⟨fun k hk ↦ h k (by omega), h 1 le_rfl⟩, fun h ↦ NegK.of_high h.1 h.2⟩

/-- The form consumed by the Wall trick (`NegKStablyFree.stablyFreeObjects`). -/
theorem NegKStablyFree.of_high {B : InvCat} (hH : NegKHigh B) (h₁ : NegKOne B) :
    NegKStablyFree B :=
  (NegK.of_high hH h₁).stablyFree

/-! ### Stably free vs. absorbing -/

/-- At every level `k ≥ 1`, stably free Kar objects are absorbed: `(M, e) ⊕ F ≅ F'` gives
`(M, e) ⊕ H ≅ H` for a free `H` (Lemma D for free objects, `KarSwindle.lean`). -/
theorem exists_karAbsorbs_of_karStablyFree_czIter {B : InvCat} {k : ℕ} (hk : 1 ≤ k)
    {M F F' : B.czIter k} {e : M ⟶ M} (he : e ≫ e = e) (h : KarStablyFree e F F') :
    ∃ H : B.czIter k, KarAbsorbs e H := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact CZ.exists_karAbsorbs_of_karStablyFree (B := B.czIter k) he h

/-- **`NegK` is equivalent to its stably-free form** (the equivalence stated in `NegK.lean`). -/
theorem NegK.iff_stablyFree {B : InvCat} : NegK B ↔ NegKStablyFree B :=
  ⟨NegK.stablyFree, fun h k hk M e he ↦
    let ⟨_, _, hF⟩ := h k hk M e he
    exists_karAbsorbs_of_karStablyFree_czIter hk he hF⟩

/-- `NegKHigh` is equivalent to its stably-free form. -/
theorem negKHigh_iff_stablyFree {B : InvCat} : NegKHigh B ↔ NegKHighStablyFree B :=
  ⟨fun h k hk M e he ↦ let ⟨F, hF⟩ := h k hk M e he; ⟨F, F, hF⟩, fun h k hk M e he ↦
    let ⟨_, _, hF⟩ := h k hk M e he
    exists_karAbsorbs_of_karStablyFree_czIter (by omega) he hF⟩

/-! ### Level `1` from Theorem A -/

/-- Level `1` for every Kar-diagonalizable `B` (Lemma D, `KarSwindle.lean`). -/
theorem negKOne_of_karDiagonalizable {B : InvCat} (hB : CZ.KarDiagonalizable B) : NegKOne B :=
  fun M e he ↦ CZ.karAbsorbs_of_karDiagonalizable hB M e he

variable {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]

/-- Theorem A makes `finSuppFreeQG G T` Kar-diagonalizable: `(α, β)` is the Kar isomorphism. -/
theorem CZ.karDiagonalizable_of_karDiagStatement (hA : KarDiagStatement) (T : Set ℕ) :
    CZ.KarDiagonalizable (finSuppFreeQG G T) := fun X p hp ↦ by
  obtain ⟨b, hb⟩ := CZ.exists_propLE p
  obtain ⟨Q, d, α, β, hd, hαβ, hβα, hpα, hαd, hdβ, hβp, -, -⟩ := hA G T X p hp b hb
  exact ⟨Q, d, hd, ⟨⟨α, β, hpα, hαd, hdβ, hβp, hαβ, hβα⟩⟩⟩

/-- **`NegK` at level `1`** (`blueprint/negK-proof.md` §2.4, Corollary): under Theorem A, every
object of `Kar C_ℤ(finSuppFreeQG G T)` is absorbed by a free object, for all `G` and all
`T ⊆ ℕ`. -/
theorem negK_levelOne (hA : KarDiagStatement) (T : Set ℕ) : NegKOne (finSuppFreeQG G T) :=
  negKOne_of_karDiagonalizable (CZ.karDiagonalizable_of_karDiagStatement hA T)

/-- `NegK (finSuppFreeQG G T)` from Theorem A and the levels `k ≥ 2`. -/
theorem negK_of_high (hA : KarDiagStatement) {T : Set ℕ} (hH : NegKHigh (finSuppFreeQG G T)) :
    NegK (finSuppFreeQG G T) :=
  NegK.of_high hH (negK_levelOne hA T)

/-! ### Downstream wiring (module 22) -/

/-- The `NegK` input of module 22 (`DecBij`): `NegK (finSuppFreeQG G T)` for all `G`, `T`. -/
def NegKAll : Prop :=
  ∀ (G : ℕ → Type) [∀ i, Group (G i)] [∀ i, Fintype (G i)] (T : Set ℕ),
    NegK (finSuppFreeQG G T)

/-- **What module 22 needs** once Theorem A is proved: `NegKHigh (finSuppFreeQG G T)` for all
`G`, `T` (`blueprint/negK-proof.md` §8, step 2: `lowerLModel` takes
`hK : ∀ G T, NegKHigh (finSuppFreeQG G T)`). -/
def NegKHighAll : Prop :=
  ∀ (G : ℕ → Type) [∀ i, Group (G i)] [∀ i, Fintype (G i)] (T : Set ℕ),
    NegKHigh (finSuppFreeQG G T)

/-- **The reduction of the `NegK` input to `k ≥ 2`**: Theorem A and `NegKHighAll` give the
full `NegKAll` consumed by module 22. -/
theorem negKAll_of_high (hA : KarDiagStatement) (hH : NegKHighAll) : NegKAll :=
  fun G _ _ T ↦ negK_of_high hA (hH G T)

/-- `NegKHighAll` in the (equivalent, a priori weaker) stably-free form. -/
def NegKHighStablyFreeAll : Prop :=
  ∀ (G : ℕ → Type) [∀ i, Group (G i)] [∀ i, Fintype (G i)] (T : Set ℕ),
    NegKHighStablyFree (finSuppFreeQG G T)

lemma negKHighAll_iff_stablyFree : NegKHighAll ↔ NegKHighStablyFreeAll :=
  ⟨fun h G _ _ T ↦ negKHigh_iff_stablyFree.mp (h G T),
    fun h G _ _ T ↦ negKHigh_iff_stablyFree.mpr (h G T)⟩

/-- The reduction with the stably-free form of the input. -/
theorem negKAll_of_highStablyFree (hA : KarDiagStatement) (hH : NegKHighStablyFreeAll) :
    NegKAll :=
  negKAll_of_high hA (negKHighAll_iff_stablyFree.mpr hH)

/-- The stably-free form consumed by the Wall trick, for all `G`, `T`. -/
theorem negKStablyFreeAll_of_high (hA : KarDiagStatement) (hH : NegKHighAll)
    (G : ℕ → Type) [∀ i, Group (G i)] [∀ i, Fintype (G i)] (T : Set ℕ) :
    NegKStablyFree (finSuppFreeQG G T) :=
  (negKAll_of_high hA hH G T).stablyFree

end

end HSFormal.LTheory
