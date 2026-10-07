import HSFormal.LTheory.Model.Wall
import HSFormal.LTheory.Model.Swindle

/-!
# Swindle absorption of diagonal Kar objects (NegK, module 6)

`blueprint/negK-proof.md` §1 "Lemma D" and §5 row 6.

* `KarStablyFree.ofKarIso`, `KarStablyFree.karIso`: `KarStablyFree e F F'` is a Kar isomorphism
  `(M ⊞ F, e ⊞ 1) ≅ (F', 1)`; `KarStablyFree.of_karIso` transports it along Kar isomorphisms
  `(M, e) ≅ (N, e')` (`Wall.KarIso`).
* `KarStablyFree.map`: additive functors preserve `KarStablyFree`.
* `karAbsorbs_of_swindle` (pure category theory): if `N = M ⊕ N` (inclusions `i₀`, `i₁` with
  dual projections) compatibly with idempotents `e` on `M` and `E` on `N`, then
  `(M, e) ⊕ N ≅ N`.  The proof adds the complement `(N, 1 - E)`:
  `(M, e) ⊕ N = (M, e) ⊕ (N, E) ⊕ (N, 1 - E) ≅ (N, E) ⊕ (N, 1 - E) = N`, so the absorbing object
  `N` is free.
* `InvCat.Swindle.karAbsorbs`: for any Eilenberg swindle `s` on `A` and any idempotent `e` on
  `M`, `KarAbsorbs e (Σ M)` with `Σ = s.sum`.
* `karAbsorbs_of_splitting`: absorption is additive along a splitting `Q = E ⊕ U` commuting
  with the idempotent.
* **Lemma D** `CZ.karAbsorbs_diag`: for every `InvCat` `B` and every diagonal idempotent
  `diag d` (`d v` idempotent) on `Q : C_ℤ(B)`, i.e. every object of `C_ℤ(Kar B)` viewed in
  `Kar C_ℤ(B)`, there is a free `F` with `(Q, diag d) ⊕ F ≅ F`.  Cut `Q` at `0` (`CZ.cut`), absorb
  the halves by the half-line swindles `CZ.posSwindle`, `CZ.negSwindle`, push forward along the
  inclusions `C_{ℤ≷}(B) ⊂ C_ℤ(B)`, and take `F = Σ₊ Q₊ ⊞ Σ₋ Q₋`.
* `CZ.karAbsorbs_of_karIso_diag`: the same for every idempotent Kar-isomorphic to a diagonal
  one (the form in which Theorem A, `KarDiagStatement`, delivers it; `CZ.karIsoOfFactor` builds
  the Kar isomorphism from `α ≫ β = p`, `β ≫ α = diag d` alone).  `CZ.KarDiagonalizable B`
  (every idempotent on `C_ℤ(B)` is Kar-isomorphic to a diagonal one) implies level `1` of
  `NegK B` (`CZ.karAbsorbs_of_karDiagonalizable`; `negKOne_of_karDiagonalizable` in
  `LevelOne.lean`).
* `karAbsorbs_of_karStablyFree`, `CZ.exists_karAbsorbs_of_karStablyFree`: in `C_ℤ(B)` every
  stably free Kar object (`(M, e) ⊕ F ≅ F'`) is absorbed by a free object, because free objects
  are (Lemma D with `d = 1`).  This gives `NegK B ↔ NegKStablyFree B` (`LevelOne.lean`).

Everything here holds for an arbitrary `InvCat` `B`; nothing about `finSuppFreeQG` is used.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HSFormal.Compression

noncomputable section

universe v u v' u'

/-! ### Kar isomorphisms and `KarStablyFree` -/

section General

variable {V : Type u} [Category.{v} V] [Preadditive V] [HasBinaryBiproducts V]

/-- A Kar isomorphism `(M ⊞ F, e ⊞ 1) ≅ (F', 1)` is a witness of `KarStablyFree e F F'`. -/
lemma KarStablyFree.ofKarIso {M F F' : V} {e : M ⟶ M}
    (γ : Wall.KarIso (biprod.map e (𝟙 F)) (𝟙 F')) : KarStablyFree e F F' :=
  ⟨γ.hom, γ.inv, γ.hom_inv, γ.inv_hom⟩

/-- The Kar isomorphism `(M ⊞ F, e ⊞ 1) ≅ (F', 1)` of a witness of `KarStablyFree e F F'`. -/
lemma KarStablyFree.karIso {M F F' : V} {e : M ⟶ M} (h : KarStablyFree e F F') :
    Nonempty (Wall.KarIso (biprod.map e (𝟙 F)) (𝟙 F')) :=
  let ⟨_, _, huv, hvu⟩ := h
  ⟨Wall.KarIso.ofStablyFree huv hvu⟩

/-- `KarStablyFree` is invariant under Kar isomorphisms `(M, e) ≅ (N, e')`. -/
lemma KarStablyFree.of_karIso {M N F F' : V} {e : M ⟶ M} {e' : N ⟶ N} (α : Wall.KarIso e e')
    (h : KarStablyFree e' F F') : KarStablyFree e F F' := by
  obtain ⟨γ⟩ := h.karIso
  exact .ofKarIso <| ((Wall.KarIso.sum α (Wall.KarIso.refl (id_comp (𝟙 F)))
    (BinaryBiproduct.bicone M F) (BinaryBiproduct.bicone N F)).congr
      (by simp [biprod.map_eq]) (by simp [biprod.map_eq])).trans γ

/-- `KarAbsorbs` is invariant under Kar isomorphisms `(M, e) ≅ (N, e')`. -/
lemma KarAbsorbs.of_karIso {M N F : V} {e : M ⟶ M} {e' : N ⟶ N} (α : Wall.KarIso e e')
    (h : KarAbsorbs e' F) : KarAbsorbs e F :=
  KarStablyFree.of_karIso α h

/-- Additive functors preserve `KarStablyFree`. -/
lemma KarStablyFree.map {W : Type u'} [Category.{v'} W] [Preadditive W] [HasBinaryBiproducts W]
    (Φ : V ⥤ W) [Φ.Additive] {M F F' : V} {e : M ⟶ M} (h : KarStablyFree e F F') :
    KarStablyFree (Φ.map e) (Φ.obj F) (Φ.obj F') := by
  obtain ⟨u, v, huv, hvu⟩ := h
  refine ⟨biprod.desc (Φ.map biprod.inl) (Φ.map biprod.inr) ≫ Φ.map u,
    Φ.map v ≫ biprod.lift (Φ.map biprod.fst) (Φ.map biprod.snd), ?_, ?_⟩
  · have h' : Φ.map u ≫ Φ.map v = Φ.map (biprod.map e (𝟙 F)) := by rw [← Φ.map_comp, huv]
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
      simp only [assoc, biprod.inl_desc_assoc, biprod.inr_desc_assoc, reassoc_of% h',
        biprod.lift_fst, biprod.lift_snd, ← Φ.map_comp] <;> simp
  · have h' : Φ.map biprod.fst ≫ Φ.map biprod.inl + Φ.map biprod.snd ≫ Φ.map biprod.inr =
        𝟙 (Φ.obj (M ⊞ F)) := by
      rw [← Φ.map_comp, ← Φ.map_comp, ← Φ.map_add, biprod.total, Φ.map_id]
    simp only [assoc, biprod.lift_desc_assoc, reassoc_of% h']
    rw [← Φ.map_comp, hvu, Φ.map_id]

/-- Additive functors preserve `KarAbsorbs`. -/
lemma KarAbsorbs.map {W : Type u'} [Category.{v'} W] [Preadditive W] [HasBinaryBiproducts W]
    (Φ : V ⥤ W) [Φ.Additive] {M F : V} {e : M ⟶ M} (h : KarAbsorbs e F) :
    KarAbsorbs (Φ.map e) (Φ.obj F) :=
  KarStablyFree.map Φ h

end General

/-! ### The abstract swindle -/

section Swindle

variable {V : Type u} [Category.{v} V] [Preadditive V] [HasBinaryBiproducts V]

/-- **Abstract swindle.**  Let `N = M ⊕ N` be a biproduct decomposition (inclusions `i₀ : M → N`,
`i₁ : N → N`, projections `p₀`, `p₁`), compatible with idempotents `e` on `M` and `E` on `N`
(`i₀ E = e i₀`, `i₁ E = E i₁`, i.e. `(N, E) ≅ (M, e) ⊕ (N, E)`).  Then `(M, e) ⊕ N ≅ N`:
`(M, e) ⊕ N = (M, e) ⊕ (N, E) ⊕ (N, 1 - E) ≅ (N, E) ⊕ (N, 1 - E) = N`. -/
theorem karAbsorbs_of_swindle {M N : V} {e : M ⟶ M} {E : N ⟶ N} (he : e ≫ e = e)
    (hE : E ≫ E = E) (i₀ : M ⟶ N) (p₀ : N ⟶ M) (i₁ p₁ : N ⟶ N) (h₀₀ : i₀ ≫ p₀ = 𝟙 M)
    (h₁₁ : i₁ ≫ p₁ = 𝟙 N) (h₀₁ : i₀ ≫ p₁ = 0) (h₁₀ : i₁ ≫ p₀ = 0)
    (htot : p₀ ≫ i₀ + p₁ ≫ i₁ = 𝟙 N) (hi₀ : i₀ ≫ E = e ≫ i₀) (hi₁ : i₁ ≫ E = E ≫ i₁) :
    KarAbsorbs e N := by
  -- the projections commute with the idempotents
  have hp₀ : p₀ ≫ e = E ≫ p₀ := by
    have : E ≫ p₀ = (p₀ ≫ i₀ + p₁ ≫ i₁) ≫ E ≫ p₀ := by rw [htot, id_comp]
    rw [this, add_comp, assoc, assoc, reassoc_of% hi₀, reassoc_of% hi₁, h₀₀, h₁₀, comp_id,
      comp_zero, comp_zero, add_zero]
  have hp₁ : p₁ ≫ E = E ≫ p₁ := by
    have : E ≫ p₁ = (p₀ ≫ i₀ + p₁ ≫ i₁) ≫ E ≫ p₁ := by rw [htot, id_comp]
    rw [this, add_comp, assoc, assoc, reassoc_of% hi₀, reassoc_of% hi₁, h₀₁, h₁₁, comp_id,
      comp_zero, comp_zero, zero_add]
  have he' {Z : V} (g : M ⟶ Z) : e ≫ e ≫ g = e ≫ g := by rw [← assoc, he]
  have hE' {Z : V} (g : N ⟶ Z) : E ≫ E ≫ g = E ≫ g := by rw [← assoc, hE]
  have hi₀' {Z : V} (g : N ⟶ Z) : i₀ ≫ E ≫ g = e ≫ i₀ ≫ g := by rw [← assoc, hi₀, assoc]
  have hi₁' {Z : V} (g : N ⟶ Z) : i₁ ≫ E ≫ g = E ≫ i₁ ≫ g := by rw [← assoc, hi₁, assoc]
  have hp₀' {Z : V} (g : M ⟶ Z) : p₀ ≫ e ≫ g = E ≫ p₀ ≫ g := by rw [← assoc, hp₀, assoc]
  have hp₁' {Z : V} (g : N ⟶ Z) : p₁ ≫ E ≫ g = E ≫ p₁ ≫ g := by rw [← assoc, hp₁, assoc]
  have htot' : E ≫ p₁ ≫ i₁ = E - E ≫ p₀ ≫ i₀ := by
    rw [eq_sub_iff_add_eq, ← comp_add, add_comm, htot, comp_id]
  refine ⟨biprod.desc (e ≫ i₀) (E ≫ i₁ + (𝟙 N - E)),
    biprod.lift (E ≫ p₀) (E ≫ p₁ + (𝟙 N - E)), ?_, ?_⟩
  · ext <;> simp [hi₀, hi₀', hi₁, hi₁', he, he', hE, hE', h₀₀, h₁₁, h₀₁, h₁₀, comp_sub, sub_comp]
  · simp only [biprod.lift_desc, add_comp, comp_add, sub_comp, comp_sub, assoc, id_comp,
      comp_id, hp₀', hE', hp₁, hp₁', hE, htot']
    abel

end Swindle

/-! ### Swindles absorb every Kar object -/

namespace InvCat.Swindle

variable {A : InvCat}

/-- **Swindle absorption** (`blueprint/negK-proof.md` §1, Lemma D, generic step): for an
Eilenberg swindle `s` on `A` (`Σ ≅ 𝟙 ⊕ Σ ≫ S`, `Σ ≫ S ≅ Σ`), every Kar object `(M, e)` is absorbed
by the free object `Σ M`: `(M, e) ⊕ Σ M ≅ Σ M`. -/
theorem karAbsorbs (s : A.Swindle) {M : A} {e : M ⟶ M} (he : e ≫ e = e) :
    KarAbsorbs e (s.sum.F.obj M) := by
  let φ₀ : InvCat.UnitaryIso (s.summand false) (𝟙 A) := s.summandIsoId
  let φ₁ : InvCat.UnitaryIso (s.summand true) s.sum := s.summandIsoShift.trans s.sumShiftIso
  let ι₀ := (s.isFinSum.inc false).app M
  let ι₁ := (s.isFinSum.inc true).app M
  let i₀ : M ⟶ s.sum.F.obj M := φ₀.iso.inv.app M ≫ ι₀
  let i₁ : s.sum.F.obj M ⟶ s.sum.F.obj M := φ₁.iso.inv.app M ≫ ι₁
  have hs₀ : A.inv.star i₀ = A.inv.star ι₀ ≫ φ₀.iso.hom.app M := by
    erw [A.inv.star_comp, φ₀.star_inv]
    rfl
  have hs₁ : A.inv.star i₁ = A.inv.star ι₁ ≫ φ₁.iso.hom.app M := by
    rw [A.inv.star_comp, φ₁.star_inv]
  refine karAbsorbs_of_swindle he (by rw [← s.sum.F.map_comp, he]) i₀ (A.inv.star i₀) i₁
    (A.inv.star i₁) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · erw [hs₀, assoc, ← assoc ι₀, s.isFinSum.inc_star_self false M, id_comp]
    exact φ₀.iso.inv_hom_id_app M
  · rw [hs₁, assoc, ← assoc ι₁, s.isFinSum.inc_star_self true M, id_comp]
    exact φ₁.iso.inv_hom_id_app M
  · erw [hs₁, assoc, ← assoc ι₀, s.isFinSum.inc_star_ne false true (by simp) M, zero_comp,
      comp_zero]
  · erw [hs₀, assoc, ← assoc ι₁, s.isFinSum.inc_star_ne true false (by simp) M, zero_comp,
      comp_zero]
  · erw [hs₀, hs₁, assoc, assoc, φ₀.iso.hom_inv_id_app_assoc, φ₁.iso.hom_inv_id_app_assoc,
      ← s.isFinSum.total M, Fintype.sum_bool, add_comm]
  · have h := φ₀.iso.inv.naturality_assoc e ι₀
    change (φ₀.iso.inv.app M ≫ ι₀) ≫ s.sum.F.map e = e ≫ φ₀.iso.inv.app M ≫ ι₀
    rw [assoc, ← (s.isFinSum.inc false).naturality]
    exact h.symm
  · change (φ₁.iso.inv.app M ≫ ι₁) ≫ s.sum.F.map e = s.sum.F.map e ≫ φ₁.iso.inv.app M ≫ ι₁
    rw [assoc, ← (s.isFinSum.inc true).naturality, φ₁.iso.inv.naturality_assoc]

end InvCat.Swindle

/-! ### Absorption along splittings -/

section Splitting

variable {V : Type u} [Category.{v} V] [Preadditive V]

/-- The idempotent of a splitting is idempotent. -/
lemma SplitKar.idem_idem {Q : V} (σ : Splitting Q) : σ.idem ≫ σ.idem = σ.idem := by
  rw [Splitting.idem, assoc, ← assoc σ.ιE, σ.ιE_πE, id_comp]

/-- The complementary idempotent of a splitting is `1 - idem`. -/
lemma SplitKar.πU_ιU {Q : V} (σ : Splitting Q) : σ.πU ≫ σ.ιU = 𝟙 Q - σ.idem := by
  rw [← σ.total, Splitting.idem, add_sub_cancel_left]

/-- The part `ιE q πE` of an idempotent `q` commuting with a splitting is idempotent. -/
lemma SplitKar.idem_E {Q : V} (σ : Splitting Q) {q : Q ⟶ Q} (hq : q ≫ q = q)
    (hc : q ≫ σ.idem = σ.idem ≫ q) : (σ.ιE ≫ q ≫ σ.πE) ≫ σ.ιE ≫ q ≫ σ.πE = σ.ιE ≫ q ≫ σ.πE := by
  have : q ≫ σ.πE ≫ σ.ιE ≫ q = σ.πE ≫ σ.ιE ≫ q := by
    rw [← assoc σ.πE, ← Splitting.idem, ← assoc, hc, assoc, hq]
  rw [assoc, assoc, reassoc_of% this, ← assoc σ.ιE, σ.ιE_πE, id_comp]

/-- The part `ιU q πU` of an idempotent `q` commuting with a splitting is idempotent. -/
lemma SplitKar.idem_U {Q : V} (σ : Splitting Q) {q : Q ⟶ Q} (hq : q ≫ q = q)
    (hc : q ≫ σ.idem = σ.idem ≫ q) : (σ.ιU ≫ q ≫ σ.πU) ≫ σ.ιU ≫ q ≫ σ.πU = σ.ιU ≫ q ≫ σ.πU := by
  have : q ≫ σ.πU ≫ σ.ιU ≫ q = σ.πU ≫ σ.ιU ≫ q := by
    have h : q ≫ σ.idem ≫ q = σ.idem ≫ q := by rw [← assoc, hc, assoc, hq]
    rw [← assoc σ.πU, SplitKar.πU_ιU σ, sub_comp, id_comp, comp_sub, hq, h]
  rw [assoc, assoc, reassoc_of% this, ← assoc σ.ιU, σ.ιU_πU, id_comp]

/-- An idempotent commuting with a splitting is the sum of its two parts. -/
lemma SplitKar.eq_add_of_comm {Q : V} (σ : Splitting Q) {q : Q ⟶ Q}
    (hc : q ≫ σ.idem = σ.idem ≫ q) :
    q = σ.πE ≫ σ.ιE ≫ q ≫ σ.πE ≫ σ.ιE + σ.πU ≫ σ.ιU ≫ q ≫ σ.πU ≫ σ.ιU := by
  have h₁ : σ.πE ≫ σ.ιE ≫ q ≫ σ.πE ≫ σ.ιE = σ.idem ≫ q ≫ σ.idem := by
    simp only [Splitting.idem, assoc]
  have h₂ : σ.πU ≫ σ.ιU ≫ q ≫ σ.πU ≫ σ.ιU = (𝟙 Q - σ.idem) ≫ q ≫ (𝟙 Q - σ.idem) := by
    rw [← SplitKar.πU_ιU σ]; simp only [assoc]
  have hI' {Z : V} (g : Q ⟶ Z) : σ.idem ≫ σ.idem ≫ g = σ.idem ≫ g := by
    rw [← assoc, SplitKar.idem_idem σ]
  rw [h₁, h₂]
  simp only [comp_sub, sub_comp, comp_id, id_comp, hc, hI']
  abel

variable [HasBinaryBiproducts V]

/-- **Absorption along a splitting.**  If the idempotent `q` on `Q` commutes with a splitting
`Q = E ⊕ U`, and its parts `(E, ιE q πE)`, `(U, ιU q πU)` are absorbed by free objects `F₁`,
`F₂`, then `(Q, q)` is absorbed by `F₁ ⊞ F₂`. -/
theorem karAbsorbs_of_splitting {Q : V} (σ : Splitting Q) {q : Q ⟶ Q}
    (hc : q ≫ σ.idem = σ.idem ≫ q) {F₁ F₂ : V} (h₁ : KarAbsorbs (σ.ιE ≫ q ≫ σ.πE) F₁)
    (h₂ : KarAbsorbs (σ.ιU ≫ q ≫ σ.πU) F₂) : KarAbsorbs q (F₁ ⊞ F₂) := by
  obtain ⟨α⟩ := KarStablyFree.karIso h₁
  obtain ⟨β⟩ := KarStablyFree.karIso h₂
  let b : BinaryBicone (σ.E ⊞ F₁) (σ.U ⊞ F₂) :=
    { pt := Q ⊞ (F₁ ⊞ F₂)
      fst := biprod.map σ.πE biprod.fst
      snd := biprod.map σ.πU biprod.snd
      inl := biprod.map σ.ιE biprod.inl
      inr := biprod.map σ.ιU biprod.inr
      inl_fst := by ext <;> simp [σ.ιE_πE]
      inl_snd := by ext <;> simp [σ.ιE_πU]
      inr_fst := by ext <;> simp [σ.ιU_πE]
      inr_snd := by ext <;> simp [σ.ιU_πU] }
  refine .ofKarIso <| (Wall.KarIso.sum α β b (BinaryBiproduct.bicone F₁ F₂)).congr ?_ ?_
  · have hq' := SplitKar.eq_add_of_comm σ hc
    ext <;> first | (simp [b]; done) | simpa [b] using hq'.symm
  · simp

end Splitting

/-! ### Stably free objects are absorbed once free objects are -/

section StablyFree

open Idempotents

variable {V : Type u} [Category.{v} V] [Preadditive V] [HasBinaryBiproducts V]
  [HasFiniteBiproducts V]

/-- If `(M, e) ⊕ F ≅ F'` and the free objects `F`, `F'` are absorbed by `G`, `G'`, then `(M, e)`
is absorbed by `G ⊞ G'`: `P ⊕ G ⊕ G' ≅ P ⊕ F ⊕ G ⊕ G' ≅ F' ⊕ G ⊕ G' ≅ G ⊕ G'`
(`blueprint/negK-proof.md` §1, "Absorbing vs. stably free"). -/
theorem karAbsorbs_of_karStablyFree {M F F' G G' : V} {e : M ⟶ M} (he : e ≫ e = e)
    (h : KarStablyFree e F F') (hG : KarAbsorbs (𝟙 F) G) (hG' : KarAbsorbs (𝟙 F') G') :
    KarAbsorbs e (G ⊞ G') := by
  letI : HasBinaryBiproducts (Karoubi V) := hasBinaryBiproducts_of_finite_biproducts _
  haveI := preservesBinaryBiproducts_of_preservesBiproducts (toKaroubi V)
  let P : Karoubi V := ⟨M, e, he⟩
  let t := toKaroubi V
  obtain ⟨i₁⟩ := (karStablyFree_iff P F F').mp h
  obtain ⟨i₂⟩ := (karStablyFree_iff (t.obj F) G G).mp hG
  obtain ⟨i₃⟩ := (karStablyFree_iff (t.obj F') G' G').mp hG'
  let j := t.mapBiprod G G'
  refine (karStablyFree_iff P _ _).mpr ⟨?_⟩
  exact biprod.mapIso (Iso.refl P) j ≪≫
    biprod.mapIso (Iso.refl P) (biprod.mapIso i₂.symm (Iso.refl _)) ≪≫
    biprod.mapIso (Iso.refl P) (biprod.associator _ _ _) ≪≫ (biprod.associator _ _ _).symm ≪≫
    biprod.mapIso i₁ (Iso.refl _) ≪≫ (biprod.associator _ _ _).symm ≪≫
    biprod.mapIso (biprod.braiding _ _) (Iso.refl _) ≪≫ biprod.associator _ _ _ ≪≫
    biprod.mapIso (Iso.refl _) i₃ ≪≫ j.symm

end StablyFree

/-! ### Lemma D: diagonal Kar objects of `C_ℤ(B)` are absorbed -/

namespace CZ

variable {B : InvCat}

lemma isZero_cut_U (X : B.cz) (p : ℤ → Prop) [DecidablePred p] {v : ℤ} (h : p v) :
    IsZero ((cut X p).U.obj v) := by
  change IsZero (if p v then splitE (X.obj v) else splitU (X.obj v)).U
  rw [if_pos h]
  exact isZero_zero B

/-- Diagonal endomorphisms commute with the cut idempotents. -/
lemma diag_comm_cut_idem {Q : B.cz} (d : ∀ v, Q.obj v ⟶ Q.obj v) (p : ℤ → Prop)
    [DecidablePred p] : diag d ≫ (cut Q p).idem = (cut Q p).idem ≫ diag d := by
  rw [cut_idem, diag_comp_diag, diag_comp_diag]
  exact diag_ext fun v ↦ by split_ifs <;> simp

/-- **Lemma D** (`blueprint/negK-proof.md` §1): for every `InvCat` `B`, every diagonal Kar object
`(Q, diag d)` of `C_ℤ(B)` (`d v` idempotent, i.e. an object of `C_ℤ(Kar B)`) is absorbed by a
free object: `(Q, diag d) ⊕ F ≅ F` with `F = Σ₊ Q₊ ⊞ Σ₋ Q₋`, where `Q = Q₊ ⊕ Q₋` is the cut at
`0` and `Σ₊`, `Σ₋` are the half-line swindles. -/
theorem karAbsorbs_diag {Q : B.cz} (d : ∀ v, Q.obj v ⟶ Q.obj v) (hd : ∀ v, d v ≫ d v = d v) :
    ∃ F : B.cz, KarAbsorbs (diag d) F := by
  let σ := cut Q (fun v ↦ 0 ≤ v)
  have hq : diag d ≫ diag d = diag d := by rw [diag_comp_diag]; exact diag_ext hd
  have hc := diag_comm_cut_idem d (fun v ↦ 0 ≤ v)
  let Qp : B.czPos := ⟨σ.E, 0, fun v hv ↦ isZero_cut_E Q _ (by omega)⟩
  let Qn : B.czNeg := ⟨σ.U, -1, fun v hv ↦ isZero_cut_U Q _ (by omega)⟩
  let qp : Qp ⟶ Qp := ObjectProperty.homMk (σ.ιE ≫ diag d ≫ σ.πE)
  let qn : Qn ⟶ Qn := ObjectProperty.homMk (σ.ιU ≫ diag d ≫ σ.πU)
  have hqp : qp ≫ qp = qp := ObjectProperty.hom_ext _ (SplitKar.idem_E σ hq hc)
  have hqn : qn ≫ qn = qn := ObjectProperty.hom_ext _ (SplitKar.idem_U σ hq hc)
  have hpos := ((posSwindle B).karAbsorbs hqp).map (B.cz.subIncl (posHalf B)).F
  have hneg := ((negSwindle B).karAbsorbs hqn).map (B.cz.subIncl (negHalf B)).F
  exact ⟨_, karAbsorbs_of_splitting σ hc hpos hneg⟩

/-- Free objects of `C_ℤ(B)` are absorbed by free objects (Lemma D for `d = 1`). -/
theorem karAbsorbs_id (X : B.cz) : ∃ G : B.cz, KarAbsorbs (𝟙 X) G :=
  karAbsorbs_diag (fun v ↦ 𝟙 (X.obj v)) fun _ ↦ id_comp _

/-- **Stably free implies absorbed** in `C_ℤ(B)`: `(M, e) ⊕ F ≅ F'` gives `(M, e) ⊕ H ≅ H` for
a free `H`. -/
theorem exists_karAbsorbs_of_karStablyFree {M F F' : B.cz} {e : M ⟶ M} (he : e ≫ e = e)
    (h : KarStablyFree e F F') : ∃ H : B.cz, KarAbsorbs e H :=
  let ⟨_, hG⟩ := karAbsorbs_id F
  let ⟨_, hG'⟩ := karAbsorbs_id F'
  ⟨_, karAbsorbs_of_karStablyFree he h hG hG'⟩

/-- Lemma D for every idempotent Kar-isomorphic to a diagonal one. -/
theorem karAbsorbs_of_karIso_diag {X Q : B.cz} {p : X ⟶ X} {d : ∀ v, Q.obj v ⟶ Q.obj v}
    (hd : ∀ v, d v ≫ d v = d v) (α : Wall.KarIso p (diag d)) : ∃ F : B.cz, KarAbsorbs p F :=
  let ⟨F, hF⟩ := karAbsorbs_diag d hd
  ⟨F, hF.of_karIso α⟩

/-- `α ≫ β = p`, `β ≫ α = q` with `p`, `q` idempotent give a Kar isomorphism `(X, p) ≅ (Q, q)`
(`hom = p α = α q`, `inv = β p = q β`). -/
def karIsoOfFactor {V : Type u} [Category.{v} V] {X Q : V} {p : X ⟶ X} {q : Q ⟶ Q}
    (hp : p ≫ p = p) (hq : q ≫ q = q) (α : X ⟶ Q) (β : Q ⟶ X) (hαβ : α ≫ β = p)
    (hβα : β ≫ α = q) : Wall.KarIso p q where
  hom := α ≫ q
  inv := q ≫ β
  e_hom := by rw [← hαβ]; simp only [assoc]; rw [reassoc_of% hβα, hq]
  hom_e := by rw [assoc, hq]
  e_inv := by rw [← assoc, hq]
  inv_e := by rw [assoc, ← hαβ, reassoc_of% hβα, reassoc_of% hq]
  hom_inv := by
    simp only [assoc]
    rw [reassoc_of% hq, ← hβα]
    simp only [assoc]
    rw [reassoc_of% hαβ, hαβ, hp]
  inv_hom := by
    simp only [assoc]
    rw [reassoc_of% hβα, reassoc_of% hq, hq]

/-- `B` is **Kar-diagonalizable** (the conclusion of Theorem A, `blueprint/negK-proof.md` §2.4):
every idempotent on an object of `C_ℤ(B)` is Kar-isomorphic to a diagonal idempotent, i.e.
`Kar C_ℤ(B)` is generated by `C_ℤ(Kar B)`. -/
def KarDiagonalizable (B : InvCat) : Prop :=
  ∀ (X : B.cz) (p : X ⟶ X), p ≫ p = p → ∃ (Q : B.cz) (d : ∀ v, Q.obj v ⟶ Q.obj v),
    (∀ v, d v ≫ d v = d v) ∧ Nonempty (Wall.KarIso p (diag d))

/-- **Level `1` of `NegK` from Theorem A**: if `B` is Kar-diagonalizable, every Kar object of
`C_ℤ(B)` is absorbed by a free object. -/
theorem karAbsorbs_of_karDiagonalizable (hB : KarDiagonalizable B) (X : B.cz) (p : X ⟶ X)
    (hp : p ≫ p = p) : ∃ F : B.cz, KarAbsorbs p F :=
  let ⟨_, _, hd, ⟨α⟩⟩ := hB X p hp
  karAbsorbs_of_karIso_diag hd α

end CZ

end

end HSFormal.LTheory
