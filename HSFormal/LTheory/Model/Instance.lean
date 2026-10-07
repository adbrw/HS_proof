import HSFormal.LTheory.Interface
import HSFormal.LTheory.Model.Exact

/-!
# The colimit model as a `LowerLTheory` (lower L-theory model, module 23)

`blueprint/lower-L-construction.md` §4 row 23.

`lowerLModel hL hA hD : LowerLTheory` has `L := Lmodel`, the colimit
`Lmodel A n = colim_k Lconc (C_ℤ^{∘k} A) (n + k)` along `− ⊗ ℝ` (`Model/Colim.lean`), and fills
every field of the interface (`Interface.lean`) from a committed lemma of the model:

| field | lemma |
|---|---|
| `map`, `map_id`, `map_comp`, `map_unitaryIso`, `map_finSum` (H4) | `Lmodel.map`, `Lmodel.map_id`, `Lmodel.map_comp`, `Lmodel.map_unitaryIso`, `Lmodel.map_finSum` |
| `cls`, `cls_map` (H3) | `Lmodel.cls`, `Lmodel.cls_map` |
| `bdry`, `bdry_natural` (H1) | `Lmodel.bdryAll`, `Lmodel.bdryAll_natural` (from `hL`) |
| `exact_A` (H1) | `Lmodel.exactAll_A` (from `hA`) |
| `exact_Q`, `exact_U` (H1) | `Lmodel.exactAll_Q`, `Lmodel.exactAll_U` (from `hL`) |
| `bsign`, `bdry_pair` (H2) | `Lmodel.bsign` (`≡ 1`), `Lmodel.bdryAll_pair` (from `hL`) |
| `dec_bij` (H5) | `hD : DecBijModel` |

**Remaining hypotheses** (each a precisely stated `Prop` about the model, being proved elsewhere):
* `LiftingPairNullAll` (`Model/Bdry.lean`): (L2), uniqueness of lifting pairs in null-cobordism
  form, for every Karoubi filtration — module 17 (`LiftingPairUnique`).
* `LiftingClosedSubAll` (`Model/Exact.lean`): (L2) for closed lifting pairs (`Y = 0`), for every
  Karoubi filtration — module 17.
* `DecBijModel` (below): the field `dec_bij` verbatim for `L := Lmodel` — module 22 (`DecBij`),
  from `NegK` (`Model/NegK.lean`), the Wall trick (`Model/Wall.lean`) and
  `Lmodel.cls_bijective_of_nonneg`.
-/

namespace HSFormal.LTheory

open CategoryTheory

noncomputable section

/-- **H5 for the model**: the interface field `dec_bij` verbatim with `cls := Lmodel.cls`.
For `⊕_{i ∈ T} Free(ℚ[Gᵢ])` with `Gᵢ` finite and `n ≥ 0`, the decoration map
`Lconc → Lmodel` is bijective.  To be proved in module 22 (`DecBij`) from `NegK` via
`Lmodel.cls_bijective_of_nonneg`. -/
def DecBijModel : Prop :=
  ∀ (G : ℕ → Type) [∀ i, Group (G i)] [∀ i, Fintype (G i)] (T : Set ℕ) (n : ℤ),
    0 ≤ n → Function.Bijective (Lmodel.cls (finSuppFreeQG G T) n)

/-- **The colimit model of lower L-theory** as a `LowerLTheory`, given (L2) for all Karoubi
filtrations (`hL`, `hA`; module 17) and the decoration isomorphism (`hD`; module 22). -/
def lowerLModel (hL : LiftingPairNullAll) (hA : LiftingClosedSubAll) (hD : DecBijModel) :
    LowerLTheory where
  L := Lmodel
  grp := fun A n ↦ inferInstanceAs (AddCommGroup (Lmodel A n))
  map Φ n := Lmodel.map Φ n
  map_id A n := Lmodel.map_id A n
  map_comp Φ Ψ n := Lmodel.map_comp Φ Ψ n
  map_unitaryIso e n := Lmodel.map_unitaryIso e n
  map_finSum h n := Lmodel.map_finSum h n
  cls A N := Lmodel.cls A N
  cls_map Φ N x := Lmodel.cls_map Φ N x
  bdry F n := Lmodel.bdryAll hL F n
  exact_A F n := Lmodel.exactAll_A hA F n
  exact_Q F n := Lmodel.exactAll_Q hL F n
  exact_U F n := Lmodel.exactAll_U hL F n
  bdry_natural Φ n := Lmodel.bdryAll_natural hL Φ n
  bsign := Lmodel.bsign
  bdry_pair F := Lmodel.bdryAll_pair hL F
  dec_bij G _ _ T n hn := hD G T n hn

section Sanity

variable (hL : LiftingPairNullAll) (hA : LiftingClosedSubAll) (hD : DecBijModel)

/-- The groups of `lowerLModel` are the colimit groups `Lmodel`. -/
@[simp]
lemma lowerLModel_L : (lowerLModel hL hA hD).L = Lmodel := rfl

@[simp]
lemma lowerLModel_map {A B : InvCat} (Φ : A ⟶ B) (n : ℤ) :
    (lowerLModel hL hA hD).map Φ n = Lmodel.map Φ n := rfl

@[simp]
lemma lowerLModel_cls (A : InvCat) (N : ℤ) :
    (lowerLModel hL hA hD).cls A N = Lmodel.cls A N := rfl

@[simp]
lemma lowerLModel_bdry {A : InvCat} (F : KaroubiFiltration A) (n : ℤ) :
    (lowerLModel hL hA hD).bdry F n = Lmodel.bdry F (hL A F) n := rfl

/-- The universal sign of the model is `+1`. -/
@[simp]
lemma lowerLModel_bsign (N : ℤ) : (lowerLModel hL hA hD).bsign N = 1 := rfl

end Sanity

end

end HSFormal.LTheory
