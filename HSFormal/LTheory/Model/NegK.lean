import HSFormal.LTheory.Model.CZFunctor
import Mathlib.CategoryTheory.Idempotents.Biproducts

/-!
# `NegK`: vanishing of `K₋ₖ(B)` for `k ≥ 1` (input of lower-L modules 21–23)

`blueprint/lower-L-construction.md` §3.2 "H5 from NegK" and `blueprint/negK.md` §1.

* `KarStablyFree e F F'`: `(M, e) ⊕ F ≅ F'` in the Karoubi envelope, in the Kar convention of
  `SymPoincare` (objects are pairs `(X, e)`, morphisms `f` with `e f e' = f`), with `⊕` the
  biproduct `M ⊞ F` of the underlying category carrying the idempotent `e ⊞ 1`.
  `KarAbsorbs e F := KarStablyFree e F F`.
* `NegK B`: for every `k ≥ 1`, every object of `Kar (C_ℤ^{∘k} B)` is absorbed by a free object:
  `P ⊕ F ≅ F`.  `negK_iff_karoubi` restates it verbatim in mathlib's Karoubi envelope:
  `∀ k ≥ 1, ∀ P : Karoubi (B.czIter k), ∃ F, P ⊞ F ≅ F`.
* `NegKStablyFree B`: the form `P ⊕ F ≅ F'` of `negK.md` §1 (`NegKAt`); `NegK.stablyFree`.
  The Wall trick (`Model/Wall.lean`) only needs this weaker form.

**Faithfulness.**  In the Grothendieck group of the split-exact category `Kar A`, `[P] = 0` iff
`P ⊕ Q ≅ Q` for some `Q`; adding the complement `Q' = (X, 1 - q)` of `Q = (X, q)` gives
`P ⊕ (X, 1) ≅ (X, 1)`.  So `NegK B` is exactly `K₀(Kar C_ℤ^{∘k} B) = 0` for all `k ≥ 1`, which is
`K₋ₖ(B) = 0` for `k ≥ 1` by [PW85]/[Ped84] applied one `C_ℤ` at a time (`negK.md` §2.2(a)).
`NegKStablyFree B` says that `[P]` lies in the image of `K₀(C_ℤ^{∘k} B)`; that image is `0` by the
Eilenberg swindle in `C_ℤ` (`X ⊕ Σ ≅ Σ`, `Σ = ⊞_{n ≥ 0} tⁿX` on each half line), so for `k ≥ 1`
the two forms are equivalent (not formalized: only `NegK → NegKStablyFree` is used).
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive Idempotents

noncomputable section

universe v u

section KarStable

variable {V : Type u} [Category.{v} V] [Preadditive V] [HasBinaryBiproducts V]

/-- `(M, e) ⊕ F ≅ F'` in the Karoubi envelope `Kar V`: Kar-morphisms
`u : (M ⊞ F, e ⊞ 1) ⟶ (F', 1)` and `v` back with `u v = e ⊞ 1` and `v u = 1` (the Kar conditions
`(e ⊞ 1) u = u` and `v (e ⊞ 1) = v` follow). -/
def KarStablyFree {M : V} (e : M ⟶ M) (F F' : V) : Prop :=
  ∃ (u : M ⊞ F ⟶ F') (v : F' ⟶ M ⊞ F), u ≫ v = biprod.map e (𝟙 F) ∧ v ≫ u = 𝟙 F'

/-- `(M, e) ⊕ F ≅ F` in `Kar V`: the free object `F` absorbs `(M, e)`. -/
def KarAbsorbs {M : V} (e : M ⟶ M) (F : V) : Prop :=
  KarStablyFree e F F

end KarStable

/-- **`NegK`** (`blueprint/lower-L-construction.md` §3.2): for every `k ≥ 1` and every object
`P = (M, e)` of `Kar (C_ℤ^{∘k} B)` there is a free object `F` (an object of `C_ℤ^{∘k} B`) with
`P ⊕ F ≅ F`, i.e. `K₀(Kar C_ℤ^{∘k} B) = K₋ₖ(B) = 0`.  Level `k = 0` is excluded (it is false
for `ℚ[G]`, `G ≠ 1`, `negK.md` §2.1). -/
def NegK (B : InvCat) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ (M : B.czIter k) (e : M ⟶ M), e ≫ e = e →
    ∃ F : B.czIter k, KarAbsorbs e F

/-- The stably-free form of `negK.md` §1 (`NegKAt`): `P ⊕ F ≅ F'` with free `F`, `F'`. -/
def NegKStablyFree (B : InvCat) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ (M : B.czIter k) (e : M ⟶ M), e ≫ e = e →
    ∃ F F' : B.czIter k, KarStablyFree e F F'

lemma NegK.stablyFree {B : InvCat} (h : NegK B) : NegKStablyFree B := fun k hk M e he ↦
  let ⟨F, hF⟩ := h k hk M e he
  ⟨F, F, hF⟩

/-! ### The same statement in mathlib's Karoubi envelope -/

section Karoubi

variable {V : Type u} [Category.{v} V] [Preadditive V] [HasBinaryBiproducts V]
  [HasFiniteBiproducts V]

/-- Binary biproducts of `Karoubi V` (from mathlib's finite biproducts). -/
local instance : HasBinaryBiproducts (Karoubi V) := hasBinaryBiproducts_of_finite_biproducts _

/-- The explicit sum `(P.X ⊞ F, P.p ⊞ 1)` of `P` and the free object `F` in `Karoubi V`. -/
@[simps]
def karSumBicone (P : Karoubi V) (F : V) : BinaryBicone P ((toKaroubi V).obj F) where
  pt := ⟨P.X ⊞ F, biprod.map P.p (𝟙 F), by ext <;> simp⟩
  fst := ⟨biprod.fst ≫ P.p, by simp⟩
  snd := ⟨biprod.snd, by simp⟩
  inl := ⟨P.p ≫ biprod.inl, by simp⟩
  inr := ⟨biprod.inr, by simp⟩
  inl_fst := by ext; simp
  inl_snd := by ext; simp
  inr_fst := by ext; simp
  inr_snd := by ext; simp

/-- `karSumBicone` is a biproduct in `Karoubi V`. -/
def karSumBiconeIsBilimit (P : Karoubi V) (F : V) : (karSumBicone P F).IsBilimit :=
  isBinaryBilimitOfTotal _ (by
    ext
    change (biprod.fst ≫ P.p) ≫ P.p ≫ biprod.inl + biprod.snd ≫ biprod.inr =
      biprod.map P.p (𝟙 F)
    rw [Category.assoc, P.idem_assoc, biprod.map_eq, Category.id_comp]
    rfl)

/-- `KarStablyFree` is `P ⊞ F ≅ F'` in mathlib's `Karoubi V`. -/
theorem karStablyFree_iff (P : Karoubi V) (F F' : V) :
    KarStablyFree P.p F F' ↔ Nonempty (P ⊞ (toKaroubi V).obj F ≅ (toKaroubi V).obj F') := by
  let i₀ := biprod.uniqueUpToIso _ _ (karSumBiconeIsBilimit P F)
  constructor
  · rintro ⟨u, v, huv, hvu⟩
    have hu : biprod.map P.p (𝟙 F) ≫ u = u := by rw [← huv, assoc, hvu, comp_id]
    have hv : v ≫ biprod.map P.p (𝟙 F) = v := by rw [← huv, ← assoc, hvu, id_comp]
    exact ⟨i₀.symm ≪≫
      { hom := ⟨u, by change biprod.map P.p (𝟙 F) ≫ u ≫ 𝟙 F' = u; rw [Category.comp_id, hu]⟩
        inv := ⟨v, by change 𝟙 F' ≫ v ≫ biprod.map P.p (𝟙 F) = v; rw [Category.id_comp, hv]⟩
        hom_inv_id := by ext; exact huv
        inv_hom_id := by ext; exact hvu }⟩
  · rintro ⟨i⟩
    let j := i₀ ≪≫ i
    refine ⟨j.hom.f, j.inv.f, ?_, ?_⟩
    · erw [← Karoubi.comp_f, j.hom_inv_id, Karoubi.id_f]; rfl
    · erw [← Karoubi.comp_f, j.inv_hom_id, Karoubi.id_f]; rfl

/-- **`NegK` in mathlib's Karoubi envelope**: for every `k ≥ 1` and every object `P` of
`Karoubi (C_ℤ^{∘k} B)` there is `F : C_ℤ^{∘k} B` with `P ⊞ F ≅ F`. -/
theorem negK_iff_karoubi (B : InvCat) :
    NegK B ↔ ∀ k : ℕ, 1 ≤ k → ∀ P : Karoubi (B.czIter k), ∃ F : B.czIter k,
      Nonempty (P ⊞ (toKaroubi _).obj F ≅ (toKaroubi _).obj F) := by
  constructor
  · intro h k hk P
    obtain ⟨F, hF⟩ := h k hk P.X P.p P.idem
    exact ⟨F, (karStablyFree_iff P F F).mp hF⟩
  · intro h k hk M e he
    obtain ⟨F, hF⟩ := h k hk ⟨M, e, he⟩
    exact ⟨F, (karStablyFree_iff ⟨M, e, he⟩ F F).mpr hF⟩

end Karoubi

end

end HSFormal.LTheory
