import HSFormal.LTheory.Model.CZFiltration
import HSFormal.LTheory.Interface

/-!
# Half-line categories and the Eilenberg swindle (lower L-theory model, module 20)

`blueprint/lower-L-construction.md` §3.2 "H5 from NegK", §4 row 20.

**Half-lines.**  `CZ.posHalf B` (`CZ.negHalf B`) are the objects of `C_ℤ(B)` supported in some
half-line `[c, ∞)` (`(-∞, c]`).  They are additive, replete and closed under retracts;
`InvCat.czPos B = C_{ℤ≥}(B)` and `InvCat.czNeg B = C_{ℤ≤}(B)` are the full sub-`InvCat`s.
`CZ.posFiltration B`, `CZ.negFiltration B` are the half-line Karoubi filtrations of `C_ℤ(B)`
([CP95, 1.27]).  Their splittings are the diagonal self-dual cuts `X = X|_{[c,∞)} ⊕ X|_{(-∞,c)}`
(`CZ.cut`).  A map of propagation `b` into or out of an object supported in `[c, ∞)` factors
through the cut at `c - b`.  Their `sub` is `czPos`/`czNeg` by `rfl`, and `C_ℤ(Φ)` maps them
(`posFiltrationHom`).

**Swindle.**  `CZ.reindex σ` reindexes `C_ℤ(B)` along an isometry `σ` of `ℤ`.  Reindexings at
bounded distance are unitarily isomorphic through identity matrices of bounded propagation
(`reindexIso`).  This gives the shift `S` (`(SX)_v = X_{v-1}`, `S ≅ 𝟙`) and the reflection `R`
(`R ≫ R ≅ 𝟙`).  On `C_{ℤ≥}(B)`, `CZ.PosSwindle.sigma` is the strict `InvFunctor`
`Σ = ⊕_{j ≥ 0} S^j` with `(ΣX)_v = ⊕_{start X ≤ u ≤ v} X_u`.  The sum is finite because `X`
vanishes below its chosen start, and it is built from chosen unitary partial sums (`CZ.Tower`).
On morphisms, `(Σf)_{w,v} = ∑_u π_u f_{u+(w-v),u} ι_{u+(w-v)}`.  `PosSwindle.isFinSum` is the
finite unitary sum `Σ = 𝟙 ⊕ (Σ ≫ S)`: one summand is `X` itself, the other is the shifted copy
`(ΣX)_{v-1} ↪ (ΣX)_v`.  `InvCat.Swindle A` packages `(Σ, S, S ≅ 𝟙, Σ ≅ 𝟙 ⊕ Σ ≫ S)`;
`sumShiftIso` gives `Σ ≫ S ≅ Σ`.  The swindle transports along `C_ℤ` (`Swindle.cz`,
`Swindle.czIter`) and along unitary equivalences (`Swindle.transport`, used with `R` to get
`CZ.negSwindle` from `CZ.posSwindle`).

**Main results.**
* `InvCat.Swindle.eq_zero_of_map`: every H4-type functor on endofunctors (identity, composition,
  `map_unitaryIso`, `map_finSum`) has trivial target on an `InvCat` with a swindle, because
  `m Σ = 1 + m S ∘ m Σ = 1 + m Σ`.  Instances: `lconc_eq_zero`, `lconc_czIter_eq_zero`,
  `lowerL_eq_zero`.
* `Lconc.czPos_eq_zero`, `Lconc.czNeg_eq_zero`: `Lconc (C_{ℤ≷} B) N = 0` for all `N` and every
  `InvCat` `B` (with `Subsingleton` instances).  The same holds at every level of the colimit
  model (`Lconc.czIter_czPos_eq_zero`, `Lconc.czIter_czNeg_eq_zero`).
* `Lconc.cls_eq_zero_of_posHalf` / `_negHalf`: a Poincaré complex over `C_ℤ(B)` whose chain
  objects all lie in `posHalf` (`negHalf`) has class `0` in `Lconc (C_ℤ B) N`.
* `LowerLTheory.L_czPos_eq_zero`, `L_czNeg_eq_zero`, and with H1
  `map_proj_posFiltration_bijective` / `map_proj_negFiltration_bijective`:
  `L(C_ℤ B) ≅ L(C_ℤ B / C_{ℤ≷} B)`.

**What module 22 (`DecBij`) consumes.**  For `A = C_ℤ^{∘k} B` the claim is that
`tensorLine : Lconc A N → Lconc (C_ℤ A) (N+1)` is bijective under `NegK`, for `N ≥ 0`.
* *Surjectivity.*  Wall (21) represents a class by a free `D` over `C_ℤ A`.  Cutting `D` at
  degree-dependent thresholds (`t_{r-1} ≤ t_r - b`, built from `CZ.cut`) gives pairs over
  `czPos A` and `czNeg A` with a common boundary `∂` over the bounded window.  Gluing (7,
  `Cobordism`) gives `[D] - [∂ ⊗ ℝ] = [X⁺] + [X⁻]`, where `X^±` are closed and all their chain
  objects lie in `posHalf`/`negHalf`.  Both classes vanish by `Lconc.cls_eq_zero_of_posHalf`
  and `_negHalf`; this is the only place the swindle enters.  With `Lconc.cls_eq_zero_iff`
  (`Cobordism`), `Lconc.czPos_eq_zero` also says that every closed complex over `czPos A` is
  null-cobordant.
* *Injectivity* cuts a null-cobordism of `Q ⊗ ℝ` and needs no swindle.
* For the colimit model (6, 19): `Swindle.czIter` with `eq_zero_of_map` (or levelwise
  `lconc_czIter_eq_zero`) gives `L_model(C_{ℤ≷} B) = 0`.  With H1 on `posFiltration` this yields
  the analogue of `map_proj_posFiltration_bijective`.

Still to be done in 22 (not swindle content): the bounded-window category (finite support
objects) `≃ A` by summing entries (the unitary partial sums `CZ.Tower` apply), the threshold cut
of a free Poincaré complex into Poincaré pairs (algebraic transversality), and the comparison of
the cut boundary with `tensorLine`.

**Deviations from the blueprint.**
1. "Supported in `ℤ_{≥0}`" is replaced by "supported in some `[c, ∞)`".  The `U` of a Karoubi
   filtration must be replete, and a bounded isomorphism of propagation `b` moves supports by
   `b`.  Both versions have the same Karoubi envelope up to shifts.
2. "`Σ ≅ id ⊕ shift∘Σ` and `shift∘Σ ≅ Σ`" is encoded as `IsFinSum` with summands `𝟙`, `Σ ≫ S`
   (diagrammatic order) together with `S ≅ 𝟙`; then `Σ ≫ S ≅ Σ` follows (`sumShiftIso`).
3. `Σ` depends on a per-object choice of support start (`Classical.choose`) and on chosen
   iterated unitary biproducts.  It is still a strict `InvFunctor`.
4. The swindle on `C_{ℤ≤}` is transported along the reflection, not constructed a second time.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HSFormal.Compression

noncomputable section

/-! ### Whiskering and restriction of duality-preserving functors -/

namespace InvCat

variable {A B C : InvCat}

namespace UnitaryIso

/-- Whiskering a unitary isomorphism on the left. -/
def whiskerLeft (Θ : C ⟶ A) {Φ Ψ : A ⟶ B} (e : UnitaryIso Φ Ψ) :
    UnitaryIso (Θ ≫ Φ) (Θ ≫ Ψ) where
  iso := Functor.isoWhiskerLeft Θ.F e.iso
  star_hom X := e.star_hom (Θ.F.obj X)

/-- Whiskering a unitary isomorphism on the right. -/
def whiskerRight {Φ Ψ : A ⟶ B} (e : UnitaryIso Φ Ψ) (Θ : B ⟶ C) :
    UnitaryIso (Φ ≫ Θ) (Ψ ≫ Θ) where
  iso := Functor.isoWhiskerRight e.iso Θ.F
  star_hom X := by
    change C.inv.star (Θ.F.map (e.iso.hom.app X)) = Θ.F.map (e.iso.inv.app X)
    rw [← Θ.map_star, e.star_hom]

end UnitaryIso

namespace IsFinSum

variable {ι : Type*} [Fintype ι] {Φ : ι → (A ⟶ B)} {S : A ⟶ B}

/-- Precomposing a finite unitary sum. -/
def whiskerLeft (Θ : C ⟶ A) (h : IsFinSum Φ S) : IsFinSum (fun i ↦ Θ ≫ Φ i) (Θ ≫ S) where
  inc i := Functor.whiskerLeft Θ.F (h.inc i)
  inc_star_self i X := h.inc_star_self i (Θ.F.obj X)
  inc_star_ne i j hij X := h.inc_star_ne i j hij (Θ.F.obj X)
  total X := h.total (Θ.F.obj X)

/-- Postcomposing a finite unitary sum. -/
def whiskerRight (h : IsFinSum Φ S) (Θ : B ⟶ C) : IsFinSum (fun i ↦ Φ i ≫ Θ) (S ≫ Θ) where
  inc i := Functor.whiskerRight (h.inc i) Θ.F
  inc_star_self i X := by
    change Θ.F.map _ ≫ C.inv.star (Θ.F.map _) = 𝟙 _
    rw [← Θ.map_star, ← Θ.F.map_comp, h.inc_star_self, Θ.F.map_id]
  inc_star_ne i j hij X := by
    change Θ.F.map _ ≫ C.inv.star (Θ.F.map _) = 0
    rw [← Θ.map_star, ← Θ.F.map_comp, h.inc_star_ne i j hij, Θ.F.map_zero]
  total X := by
    change ∑ i, C.inv.star (Θ.F.map _) ≫ Θ.F.map _ = 𝟙 _
    simp_rw [← Θ.map_star, ← Θ.F.map_comp]
    rw [← Θ.F.map_sum, h.total, Θ.F.map_id]

end IsFinSum

section Sub

variable {U : ObjectProperty A} [IsAdditiveSub U] {V : ObjectProperty B} [IsAdditiveSub V]

variable (U V) in
/-- The restriction `A.sub U ⟶ B.sub V` of a duality-preserving functor with `Φ(U) ⊆ V`. -/
@[implicit_reducible] def subHom (Φ : A ⟶ B) (h : ∀ X, U X → V (Φ.F.obj X)) : A.sub U ⟶ B.sub V where
  F := V.lift (U.ι ⋙ Φ.F) fun X ↦ h _ X.2
  additive := { map_add := ObjectProperty.hom_ext _ (Φ.F).map_add }
  map_star f := ObjectProperty.hom_ext _ (Φ.map_star f.hom)

@[simp] lemma subHom_obj_obj (Φ : A ⟶ B) (h : ∀ X, U X → V (Φ.F.obj X)) (X : A.sub U) :
    ((subHom U V Φ h).F.obj X).obj = Φ.F.obj X.obj := rfl

@[simp] lemma subHom_map_hom (Φ : A ⟶ B) (h : ∀ X, U X → V (Φ.F.obj X)) {X Y : A.sub U}
    (f : X ⟶ Y) : ((subHom U V Φ h).F.map f).hom = Φ.F.map f.hom := rfl

/-- Unitary isomorphisms restrict to the subcategories. -/
def UnitaryIso.subHom {Φ Ψ : A ⟶ B} (e : UnitaryIso Φ Ψ) (hΦ : ∀ X, U X → V (Φ.F.obj X))
    (hΨ : ∀ X, U X → V (Ψ.F.obj X)) : UnitaryIso (subHom U V Φ hΦ) (subHom U V Ψ hΨ) where
  iso := NatIso.ofComponents (fun X ↦ ObjectProperty.isoMk _ (e.iso.app X.obj))
    fun f ↦ ObjectProperty.hom_ext _ (e.iso.hom.naturality f.hom)
  star_hom X := ObjectProperty.hom_ext _ (e.star_hom X.obj)

end Sub

end InvCat

/-! ### Reindexing `C_ℤ(B)` along isometries of `ℤ` -/

namespace CZ

variable {B : InvCat}

lemma star_id_apply (X : B.cz) (w v : ℤ) :
    B.inv.star ((𝟙 X : X ⟶ X).1 v w) = (𝟙 X : X ⟶ X).1 w v := by
  by_cases h : v = w
  · subst h; rw [id_apply_self, B.inv.star_id]
  · rw [id_apply_ne X (Ne.symm h), id_apply_ne X h, B.inv.star_zero]

lemma id_comp_apply {X Y : B.cz} (f : X ⟶ Y) (u a : ℤ) :
    ∑ᶠ w, (𝟙 X : X ⟶ X).1 w a ≫ f.1 u w = f.1 u a := by
  rw [← comp_apply, id_comp]

lemma comp_id_apply {X Y : B.cz} (f : X ⟶ Y) (u a : ℤ) :
    ∑ᶠ w, f.1 w a ≫ (𝟙 Y : Y ⟶ Y).1 u w = f.1 u a := by
  rw [← comp_apply, comp_id]

/-- A composite through an object vanishing on the window of the first factor is zero. -/
lemma comp_apply_eq_zero {X Y Z : B.cz} (f : X ⟶ Y) (g : Y ⟶ Z) {b : ℕ} (hf : PropLE f.1 b)
    {u v : ℤ} (h : ∀ w ∈ window v b, IsZero (Y.obj w)) : (f ≫ g).1 u v = 0 := by
  rw [comp_apply_left f hf]
  exact Finset.sum_eq_zero fun w hw ↦ by rw [(h w hw).eq_of_tgt (f.1 w v) 0, zero_comp]

/-- A retract of an object vanishing near `v` (relative to the propagation of the section)
vanishes at `v`. -/
lemma isZero_of_comp_eq_id {X Y : B.cz} (f : X ⟶ Y) (g : Y ⟶ X) (h : f ≫ g = 𝟙 X) {b : ℕ}
    (hf : PropLE f.1 b) {v : ℤ} (hv : ∀ w ∈ window v b, IsZero (Y.obj w)) : IsZero (X.obj v) := by
  rw [IsZero.iff_id_eq_zero, ← id_apply_self, ← h]
  exact comp_apply_eq_zero f g hf hv

/-- An isometry of `ℤ`. -/
def IsIsometry (σ : ℤ ≃ ℤ) : Prop := ∀ w v, |σ w - σ v| = |w - v|

/-- The reindexed object `(X_{σ v})_v`. -/
@[implicit_reducible] def reindexObj (σ : ℤ ≃ ℤ) (X : Obj B) : Obj B := ⟨fun v ↦ X.obj (σ v)⟩

lemma PropLE.reindex {σ : ℤ ≃ ℤ} (hσ : IsIsometry σ) {X Y : Obj B} {f : Mat X Y} {b : ℕ}
    (hf : PropLE f b) :
    PropLE (X := reindexObj σ X) (Y := reindexObj σ Y) (fun w v ↦ f (σ w) (σ v)) b :=
  fun w v h ↦ hf _ _ (by rw [hσ]; exact h)

/-- The reindexed morphism `(f_{σ w, σ v})_{w, v}`. -/
def reindexHom {σ : ℤ ≃ ℤ} (hσ : IsIsometry σ) {X Y : Obj B} (f : X ⟶ Y) :
    reindexObj σ X ⟶ reindexObj σ Y :=
  ⟨fun w v ↦ f.1 (σ w) (σ v), f.2.elim fun _ hb ↦ ⟨_, hb.reindex hσ⟩⟩

lemma id_apply_reindex (σ : ℤ ≃ ℤ) (X : Obj B) (w v : ℤ) :
    (𝟙 X : X ⟶ X).1 (σ w) (σ v) = (𝟙 (reindexObj σ X) : _ ⟶ _).1 w v := by
  by_cases h : v = w
  · subst h; rw [id_apply_self, id_apply_self]; rfl
  · rw [id_apply_ne _ h, id_apply_ne _ fun h' ↦ h (σ.injective h')] <;> rfl

/-- **Reindexing** `C_ℤ(B)` along an isometry `σ` of `ℤ`: `(ρ_σ X)_v = X_{σ v}`. -/
@[implicit_reducible] def reindex (σ : ℤ ≃ ℤ) (hσ : IsIsometry σ) : B.cz ⟶ B.cz where
  F :=
    { obj := reindexObj σ
      map := reindexHom hσ
      map_id X := hom_ext fun w v ↦ id_apply_reindex σ X w v
      map_comp f g := hom_ext fun u v ↦
        (finsum_comp_equiv σ (f := fun w ↦ f.1 w (σ v) ≫ g.1 (σ u) w)).symm }
  additive := ⟨fun {_ _ _ _} ↦ hom_ext fun _ _ ↦ rfl⟩
  map_star _ := rfl

@[simp] lemma reindex_obj_obj (σ : ℤ ≃ ℤ) (hσ : IsIsometry σ) (X : B.cz) (v : ℤ) :
    ((reindex σ hσ).F.obj X).obj v = X.obj (σ v) := rfl

@[simp] lemma reindex_map_apply (σ : ℤ ≃ ℤ) (hσ : IsIsometry σ) {X Y : B.cz} (f : X ⟶ Y)
    (w v : ℤ) : ((reindex σ hσ).F.map f).1 w v = f.1 (σ w) (σ v) := rfl

/-- Reindexings along isometries of bounded distance are unitarily isomorphic: the components
are the identity matrices `X_{σ v} → X_{τ w}` (`σ v = τ w`), of propagation `≤ c`. -/
def reindexIso {σ τ : ℤ ≃ ℤ} (hσ : IsIsometry σ) (hτ : IsIsometry τ) (c : ℕ)
    (hc : ∀ v, |σ v - τ v| ≤ c) :
    InvCat.UnitaryIso (reindex σ hσ : B.cz ⟶ B.cz) (reindex τ hτ) where
  iso := NatIso.ofComponents
    (fun X ↦
      { hom := ⟨fun w v ↦ (𝟙 X : X ⟶ X).1 (τ w) (σ v), c, fun w v h ↦ id_apply_ne X fun h' ↦ by
          have h₁ := hτ w v
          have h₂ := hc v
          have h₃ := abs_sub_comm (τ v) (σ v)
          rw [← h', abs_sub_comm] at h₁
          omega⟩
        inv := ⟨fun w v ↦ (𝟙 X : X ⟶ X).1 (σ w) (τ v), c, fun w v h ↦ id_apply_ne X fun h' ↦ by
          have h₁ := hσ w v
          have h₂ := hc v
          have h₃ := abs_sub_comm (τ v) (σ v)
          rw [← h'] at h₁
          omega⟩
        hom_inv_id := hom_ext fun u v ↦ by
          refine (finsum_comp_equiv τ
            (f := fun w ↦ (𝟙 X : X ⟶ X).1 w (σ v) ≫ (𝟙 X : X ⟶ X).1 (σ u) w)).trans ?_
          rw [← comp_apply, id_comp]
          exact id_apply_reindex σ X u v
        inv_hom_id := hom_ext fun u v ↦ by
          refine (finsum_comp_equiv σ
            (f := fun w ↦ (𝟙 X : X ⟶ X).1 w (τ v) ≫ (𝟙 X : X ⟶ X).1 (τ u) w)).trans ?_
          rw [← comp_apply, id_comp]
          exact id_apply_reindex τ X u v })
    fun {X Y} f ↦ hom_ext fun u v ↦ by
      change ∑ᶠ w, f.1 (σ w) (σ v) ≫ (𝟙 Y : Y ⟶ Y).1 (τ u) (σ w) =
        ∑ᶠ w, (𝟙 X : X ⟶ X).1 (τ w) (σ v) ≫ f.1 (τ u) (τ w)
      rw [finsum_comp_equiv σ (f := fun w ↦ f.1 w (σ v) ≫ (𝟙 Y : Y ⟶ Y).1 (τ u) w),
        finsum_comp_equiv τ (f := fun w ↦ (𝟙 X : X ⟶ X).1 w (σ v) ≫ f.1 (τ u) w),
        comp_id_apply, id_comp_apply]
  star_hom X := hom_ext fun w v ↦ star_id_apply X _ _

/-! ### Half-line subcategories -/

variable (B) in
/-- Objects of `C_ℤ(B)` supported in a half-line `[c, ∞)` (the replete version of "supported in
`ℤ_{≥0}`": a bounded isomorphism of propagation `b` moves the support by at most `b`). -/
def posHalf : ObjectProperty B.cz := fun X ↦ ∃ c : ℤ, ∀ v < c, IsZero (X.obj v)

variable (B) in
/-- Objects of `C_ℤ(B)` supported in a half-line `(-∞, c]`. -/
def negHalf : ObjectProperty B.cz := fun X ↦ ∃ c : ℤ, ∀ v, c < v → IsZero (X.obj v)

lemma posHalf_of_comp_eq_id {X Y : B.cz} (f : X ⟶ Y) (g : Y ⟶ X) (h : f ≫ g = 𝟙 X)
    (hY : posHalf B Y) : posHalf B X := by
  obtain ⟨c, hc⟩ := hY
  obtain ⟨b, hb⟩ := f.2
  exact ⟨c - b, fun v hv ↦ isZero_of_comp_eq_id f g h hb fun w hw ↦ hc w <| by
    simp only [window, Finset.mem_Icc] at hw; omega⟩

lemma negHalf_of_comp_eq_id {X Y : B.cz} (f : X ⟶ Y) (g : Y ⟶ X) (h : f ≫ g = 𝟙 X)
    (hY : negHalf B Y) : negHalf B X := by
  obtain ⟨c, hc⟩ := hY
  obtain ⟨b, hb⟩ := f.2
  exact ⟨c + b, fun v hv ↦ isZero_of_comp_eq_id f g h hb fun w hw ↦ hc w <| by
    simp only [window, Finset.mem_Icc] at hw; omega⟩

open ZeroObject in
instance : IsAdditiveSub (posHalf B) where
  of_iso e h := posHalf_of_comp_eq_id e.inv e.hom e.inv_hom_id h
  exists_zero := ⟨zeroObj, isZero_of_forall fun _ ↦ isZero_zero _, 0, fun _ _ ↦ isZero_zero _⟩
  biprod_mem {X Y} b hb hX hY := by
    obtain ⟨c₁, h₁⟩ := hX
    obtain ⟨c₂, h₂⟩ := hY
    obtain ⟨b₁, hb₁⟩ := b.fst.2
    obtain ⟨b₂, hb₂⟩ := b.snd.2
    refine ⟨min (c₁ - b₁) (c₂ - b₂), fun v hv ↦ ?_⟩
    rw [IsZero.iff_id_eq_zero, ← id_apply_self, ← IsBilimit.binary_total hb, add_apply,
      comp_apply_eq_zero _ _ hb₁ fun w hw ↦ h₁ w ?_, comp_apply_eq_zero _ _ hb₂ fun w hw ↦ h₂ w ?_,
      add_zero] <;>
    · simp only [window, Finset.mem_Icc] at hw; omega

open ZeroObject in
instance : IsAdditiveSub (negHalf B) where
  of_iso e h := negHalf_of_comp_eq_id e.inv e.hom e.inv_hom_id h
  exists_zero := ⟨zeroObj, isZero_of_forall fun _ ↦ isZero_zero _, 0, fun _ _ ↦ isZero_zero _⟩
  biprod_mem {X Y} b hb hX hY := by
    obtain ⟨c₁, h₁⟩ := hX
    obtain ⟨c₂, h₂⟩ := hY
    obtain ⟨b₁, hb₁⟩ := b.fst.2
    obtain ⟨b₂, hb₂⟩ := b.snd.2
    refine ⟨max (c₁ + b₁) (c₂ + b₂), fun v hv ↦ ?_⟩
    rw [IsZero.iff_id_eq_zero, ← id_apply_self, ← IsBilimit.binary_total hb, add_apply,
      comp_apply_eq_zero _ _ hb₁ fun w hw ↦ h₁ w ?_, comp_apply_eq_zero _ _ hb₂ fun w hw ↦ h₂ w ?_,
      add_zero] <;>
    · simp only [window, Finset.mem_Icc] at hw; omega

instance : (posHalf B).IsStableUnderRetracts where
  of_retract r h := posHalf_of_comp_eq_id r.i r.r r.retract h

instance : (negHalf B).IsStableUnderRetracts where
  of_retract r h := negHalf_of_comp_eq_id r.i r.r r.retract h

/-! ### Unitary partial sums -/

namespace Tower

variable {B : InvCat} (x : ℤ → B) (s : ℤ)

/-- The chosen unitary bicone. -/
def ub (P Q : B) : UnitaryBicone B.inv P Q := (B.unitary P Q).some

open ZeroObject in
/-- `obj n = x_{s+n-1} ⊕ (⋯ ⊕ (x_s ⊕ 0))`, iterated chosen unitary biproducts. -/
@[implicit_reducible] def obj : ℕ → B
  | 0 => 0
  | n + 1 => (ub (x (s + n)) (obj n)).pt

/-- The inclusion of the summand `x_u` (zero unless `s ≤ u < s + n`). -/
def inc : ∀ (n : ℕ) (u : ℤ), x u ⟶ obj x s n
  | 0, _ => 0
  | n + 1, u => if h : u = s + n then eqToHom (congrArg x h) ≫ (ub (x (s + n)) (obj x s n)).inl
      else inc n u ≫ (ub (x (s + n)) (obj x s n)).inr

lemma inc_succ_self (n : ℕ) : inc x s (n + 1) (s + n) = (ub (x (s + n)) (obj x s n)).inl := by
  simp [inc]

lemma inc_succ_ne (n : ℕ) {u : ℤ} (h : u ≠ s + n) :
    inc x s (n + 1) u = inc x s n u ≫ (ub (x (s + n)) (obj x s n)).inr := by
  simp [inc, h]

lemma inc_eq_zero : ∀ (n : ℕ) {u : ℤ}, u < s ∨ s + n ≤ u → inc x s n u = 0
  | 0, _, _ => rfl
  | n + 1, u, h => by
    rw [inc_succ_ne x s n (by push_cast at h; omega), inc_eq_zero n (by push_cast at h; omega),
      zero_comp]

lemma inc_star_self : ∀ (n : ℕ) {u : ℤ}, s ≤ u → u < s + n →
    inc x s n u ≫ B.inv.star (inc x s n u) = 𝟙 _
  | 0, _, h₁, h₂ => by simp at h₂; omega
  | n + 1, u, h₁, h₂ => by
    by_cases hu : u = s + n
    · subst hu
      rw [inc_succ_self, (ub _ _).star_inl, (ub _ _).inl_fst]
    · rw [inc_succ_ne x s n hu, B.inv.star_comp, (ub _ _).star_inr, assoc,
        (ub _ _).inr_snd_assoc, inc_star_self n h₁ (by push_cast at h₂; omega)]

lemma inc_star_ne : ∀ (n : ℕ) {u u' : ℤ}, u ≠ u' → inc x s n u ≫ B.inv.star (inc x s n u') = 0
  | 0, _, _, _ => zero_comp
  | n + 1, u, u', h => by
    by_cases hu : u = s + n
    · subst hu
      rw [inc_succ_self, inc_succ_ne x s n (Ne.symm h), B.inv.star_comp, (ub _ _).star_inr,
        (ub _ _).inl_snd_assoc, zero_comp]
    · by_cases hu' : u' = s + n
      · subst hu'
        rw [inc_succ_self, inc_succ_ne x s n hu, (ub _ _).star_inl, assoc, (ub _ _).inr_fst,
          comp_zero]
      · rw [inc_succ_ne x s n hu, inc_succ_ne x s n hu', B.inv.star_comp, (ub _ _).star_inr,
          assoc, (ub _ _).inr_snd_assoc, inc_star_ne n h]

open ZeroObject in
lemma total : ∀ n : ℕ,
    ∑ u ∈ Finset.Ico s (s + n), B.inv.star (inc x s n u) ≫ inc x s n u = 𝟙 _
  | 0 => by
    rw [Nat.cast_zero, add_zero, Finset.Ico_self, Finset.sum_empty]
    exact (isZero_zero B).eq_of_src _ _
  | n + 1 => by
    have hI : Finset.Ico s (s + ((n + 1 : ℕ) : ℤ)) = insert (s + n) (Finset.Ico s (s + n)) := by
      ext u; simp only [Finset.mem_Ico, Finset.mem_insert]; push_cast; omega
    rw [hI, Finset.sum_insert (by simp), inc_succ_self, (ub _ _).star_inl]
    rw [Finset.sum_congr rfl fun u hu ↦ by
      rw [inc_succ_ne x s n (by simp only [Finset.mem_Ico] at hu; omega), B.inv.star_comp,
        (ub _ _).star_inr, assoc, ← assoc (B.inv.star _)]]
    rw [← comp_sum, ← sum_comp, total n, id_comp]
    exact IsBilimit.binary_total (ub _ _).isBilimit

end Tower

/-- Reindexing a composite along a coordinate change of a non-dependent function. -/
lemma comp_congr_index {P Q : B} {Y : ℤ → B} (F : ∀ a, P ⟶ Y a) (G : ∀ a, Y a ⟶ Q) {a b : ℤ}
    (h : a = b) : F a ≫ G a = F b ≫ G b := by
  subst h; rfl

lemma sum_window_shift {M : Type*} [AddCommMonoid M] (F : ℤ → M) (b : ℕ) (u v : ℤ) :
    ∑ w ∈ window v b, F (u + (w - v)) = ∑ w ∈ window u b, F w :=
  Finset.sum_equiv (Equiv.addRight (u - v))
    (fun w ↦ by simp only [window, Finset.mem_Icc, Equiv.coe_addRight]; omega)
    fun w _ ↦ by simp only [Equiv.coe_addRight]; congr 1; ring

/-! ### Shift and reflection -/

/-- The translation `v ↦ v - 1`. -/
def shiftEquiv : ℤ ≃ ℤ := Equiv.subRight 1

lemma isIsometry_shiftEquiv : IsIsometry shiftEquiv := fun w v ↦ by
  change |(w - 1) - (v - 1)| = |w - v|
  rw [sub_sub_sub_cancel_right]

/-- The reflection `v ↦ -v`. -/
def reflEquiv : ℤ ≃ ℤ := Equiv.neg ℤ

lemma isIsometry_reflEquiv : IsIsometry reflEquiv := fun w v ↦ by
  simp only [reflEquiv, Equiv.neg_apply, neg_sub_neg, abs_sub_comm]

lemma isIsometry_refl : IsIsometry (Equiv.refl ℤ) := fun _ _ ↦ rfl

variable (B) in
/-- The shift `(S X)_v = X_{v-1}` of `C_ℤ(B)`. -/
@[implicit_reducible] def shift : B.cz ⟶ B.cz := reindex shiftEquiv isIsometry_shiftEquiv

variable (B) in
/-- The reflection `(R X)_v = X_{-v}` of `C_ℤ(B)`. -/
def reflection : B.cz ⟶ B.cz := reindex reflEquiv isIsometry_reflEquiv

variable (B) in
/-- `S ≅ 𝟙` by the identity matrices of propagation `1`. -/
def shiftIso : InvCat.UnitaryIso (shift B) (𝟙 B.cz) :=
  reindexIso isIsometry_shiftEquiv isIsometry_refl 1 fun v ↦ by simp [shiftEquiv]

variable (B) in
/-- `R ≫ R ≅ 𝟙` by the identity matrices `X_{-(-v)} = X_v`. -/
def reflectionIso : InvCat.UnitaryIso (reflection B ≫ reflection B) (𝟙 B.cz) :=
  reindexIso (σ := reflEquiv.trans reflEquiv)
    (fun w v ↦ by simp [reflEquiv]) isIsometry_refl 0 fun v ↦ by simp [reflEquiv]

end CZ

/-- The **positive half-line category** `C_{ℤ≥}(B)`: objects of `C_ℤ(B)` supported in some
`[c, ∞)`, as a full subcategory (the `U` of `CZ.posFiltration B`). -/
abbrev InvCat.czPos (B : InvCat) : InvCat := B.cz.sub (CZ.posHalf B)

/-- The **negative half-line category** `C_{ℤ≤}(B)`: objects of `C_ℤ(B)` supported in some
`(-∞, c]` (the `U` of `CZ.negFiltration B`). -/
abbrev InvCat.czNeg (B : InvCat) : InvCat := B.cz.sub (CZ.negHalf B)

namespace CZ

variable (B : InvCat)

/-- The shift of `C_{ℤ≥}(B)`. -/
@[implicit_reducible] def posShift : B.czPos ⟶ B.czPos :=
  InvCat.subHom _ _ (shift B) fun _ ⟨c, hc⟩ ↦ ⟨c + 1, fun v hv ↦ hc (v - 1) (by omega)⟩

/-- `S ≅ 𝟙` on `C_{ℤ≥}(B)`. -/
def posShiftIso : InvCat.UnitaryIso (posShift B) (𝟙 B.czPos) :=
  InvCat.UnitaryIso.subHom (shiftIso B) _ fun _ h ↦ h

/-- The reflection `C_{ℤ≤}(B) ⟶ C_{ℤ≥}(B)`. -/
def negToPos : B.czNeg ⟶ B.czPos :=
  InvCat.subHom _ _ (reflection B) fun _ ⟨c, hc⟩ ↦ ⟨-c, fun v hv ↦ hc (-v) (by omega)⟩

/-- The reflection `C_{ℤ≥}(B) ⟶ C_{ℤ≤}(B)`. -/
def posToNeg : B.czPos ⟶ B.czNeg :=
  InvCat.subHom _ _ (reflection B) fun _ ⟨c, hc⟩ ↦ ⟨-c, fun v hv ↦ hc (-v) (by omega)⟩

/-- `R ≫ R ≅ 𝟙` on `C_{ℤ≤}(B)`. -/
def negToPosToNegIso : InvCat.UnitaryIso (negToPos B ≫ posToNeg B) (𝟙 B.czNeg) :=
  InvCat.UnitaryIso.subHom (reflectionIso B)
    (fun X h ↦ ((negToPos B ≫ posToNeg B).F.obj ⟨X, h⟩).2) fun _ h ↦ h

/-- `R ≫ R ≅ 𝟙` on `C_{ℤ≥}(B)`. -/
def posToNegToPosIso : InvCat.UnitaryIso (posToNeg B ≫ negToPos B) (𝟙 B.czPos) :=
  InvCat.UnitaryIso.subHom (reflectionIso B)
    (fun X h ↦ ((posToNeg B ≫ negToPos B).F.obj ⟨X, h⟩).2) fun _ h ↦ h

/-! ### The swindle functor `Σ = ⊕_{j ≥ 0} S^j` on `C_{ℤ≥}(B)` -/

namespace PosSwindle

variable {B : InvCat}

/-- A start of the support of `X ∈ C_{ℤ≥}(B)`, chosen once and for all. -/
def start (X : B.czPos) : ℤ := Classical.choose X.property

lemma isZero_of_lt_start (X : B.czPos) {v : ℤ} (h : v < start X) : IsZero (X.obj.obj v) :=
  Classical.choose_spec X.property v h

/-- The number of summands `X_u`, `start X ≤ u ≤ v`, of `(ΣX)_v`. -/
def len (X : B.czPos) (v : ℤ) : ℕ := (v - start X + 1).toNat

/-- `(ΣX)_v = ⊕_{u ≤ v} X_u = X_v ⊕ (X_{v-1} ⊕ ⋯)`, a chosen unitary sum. -/
def pt (X : B.czPos) (v : ℤ) : B := Tower.obj X.obj.obj (start X) (len X v)

/-- The inclusion `X_u → (ΣX)_v` (zero for `u > v`). -/
def ι (X : B.czPos) (v u : ℤ) : X.obj.obj u ⟶ pt X v :=
  Tower.inc X.obj.obj (start X) (len X v) u

/-- The projection `(ΣX)_v → X_u`, the dual of `ι`. -/
def π (X : B.czPos) (v u : ℤ) : pt X v ⟶ X.obj.obj u := B.inv.star (ι X v u)

lemma star_π (X : B.czPos) (v u : ℤ) : B.inv.star (π X v u) = ι X v u := B.inv.star_star _

lemma ι_eq_zero (X : B.czPos) {v u : ℤ} (h : u < start X ∨ v < u) : ι X v u = 0 :=
  Tower.inc_eq_zero _ _ _ (by unfold len; omega)

lemma π_eq_zero (X : B.czPos) {v u : ℤ} (h : u < start X ∨ v < u) : π X v u = 0 := by
  rw [π, ι_eq_zero X h, B.inv.star_zero]

lemma ι_π_self (X : B.czPos) {v u : ℤ} (h : u ≤ v) : ι X v u ≫ π X v u = 𝟙 _ := by
  by_cases hu : start X ≤ u
  · exact Tower.inc_star_self _ _ _ hu (by unfold len; omega)
  · exact (isZero_of_lt_start X (not_le.mp hu)).eq_of_src _ _

lemma ι_π_ne (X : B.czPos) (v : ℤ) {u u' : ℤ} (h : u ≠ u') : ι X v u ≫ π X v u' = 0 :=
  Tower.inc_star_ne _ _ _ h

/-- `∑_u π_u ≫ ι_u = 𝟙` over any finite set containing `[start X, v]`. -/
lemma total (X : B.czPos) (v : ℤ) (T : Finset ℤ) (hT : ∀ u, start X ≤ u → u ≤ v → u ∈ T) :
    ∑ u ∈ T, π X v u ≫ ι X v u = 𝟙 _ := by
  have hsub : Finset.Ico (start X) (start X + len X v) ⊆ T := fun u hu ↦ by
    simp only [Finset.mem_Ico] at hu
    exact hT u hu.1 (by unfold len at hu; omega)
  rw [← Finset.sum_subset hsub fun u _ hu ↦ ?_]
  · exact Tower.total _ _ _
  · simp only [Finset.mem_Ico, not_and_or, not_le, not_lt] at hu
    rw [ι_eq_zero X (by unfold len at hu; omega), comp_zero]

lemma isZero_pt (X : B.czPos) {v : ℤ} (h : v < start X) : IsZero (pt X v) := by
  have : len X v = 0 := by unfold len; omega
  rw [pt, this]
  exact isZero_zero B

/-- The basic absorption rule `ι_a ≫ ∑_u π_u ≫ G_u = G_a` (for `a ≤ w`, `a ∈ T`). -/
lemma ι_comp_sum (X : B.czPos) {w a : ℤ} (ha : a ≤ w) (T : Finset ℤ)
    (hT : start X ≤ a → a ∈ T) {Q : B} (G : ∀ u, X.obj.obj u ⟶ Q) :
    ι X w a ≫ ∑ u ∈ T, π X w u ≫ G u = G a := by
  by_cases hs : start X ≤ a
  · rw [comp_sum, Finset.sum_eq_single a
      (fun u _ hu ↦ by rw [← assoc, ι_π_ne X w (Ne.symm hu), zero_comp])
      (fun h ↦ absurd (hT hs) h), ← assoc, ι_π_self X ha, id_comp]
  · exact (isZero_of_lt_start X (not_le.mp hs)).eq_of_src _ _

/-- The swindle object `ΣX = ⊕_{j ≥ 0} S^j X`. -/
@[implicit_reducible] def sigmaObj (X : B.czPos) : (posHalf B).FullSubcategory :=
  ⟨⟨fun v ↦ pt X v⟩, start X, fun _ h ↦ isZero_pt X h⟩

/-- The swindle matrix: `f` acting diagonally on all shifted copies,
`(Σf)_{w,v} = ∑_{u ≤ v} π_u ≫ f_{u+(w-v),u} ≫ ι_{u+(w-v)}`. -/
def sigmaMat {X Y : B.czPos} (f : X ⟶ Y) : Mat (sigmaObj X).obj (sigmaObj Y).obj :=
  fun w v ↦ ∑ u ∈ Finset.Icc (start X) v,
    π X v u ≫ f.hom.1 (u + (w - v)) u ≫ ι Y w (u + (w - v))

lemma sigmaMat_eq {X Y : B.czPos} (f : X ⟶ Y) (w v : ℤ) (T : Finset ℤ)
    (hT : ∀ u, start X ≤ u → u ≤ v → u ∈ T) :
    sigmaMat f w v = ∑ u ∈ T, π X v u ≫ f.hom.1 (u + (w - v)) u ≫ ι Y w (u + (w - v)) :=
  Finset.sum_subset (fun u hu ↦ by simp only [Finset.mem_Icc] at hu; exact hT u hu.1 hu.2)
    fun u _ hu ↦ by
      rw [π_eq_zero X (by simp only [Finset.mem_Icc, not_and_or, not_le] at hu; omega),
        zero_comp]

lemma propLE_sigmaMat {X Y : B.czPos} (f : X ⟶ Y) {b : ℕ} (hf : PropLE f.hom.1 b) :
    PropLE (sigmaMat f) b := fun w v h ↦ Finset.sum_eq_zero fun u _ ↦ by
  rw [hf _ _ (by rwa [show u + (w - v) - u = w - v by ring]), zero_comp, comp_zero]

/-- The swindle morphism `Σf`. -/
def sigmaHom {X Y : B.czPos} (f : X ⟶ Y) : sigmaObj X ⟶ sigmaObj Y :=
  ObjectProperty.homMk ⟨sigmaMat f, f.hom.2.elim fun _ hb ↦ ⟨_, propLE_sigmaMat f hb⟩⟩

@[simp] lemma sigmaHom_apply {X Y : B.czPos} (f : X ⟶ Y) (w v : ℤ) :
    (sigmaHom f).hom.1 w v = sigmaMat f w v := rfl

lemma sigmaHom_id (X : B.czPos) : sigmaHom (𝟙 X) = 𝟙 (sigmaObj X) := by
  ext w v
  change ∑ u ∈ Finset.Icc (start X) v, π X v u ≫ (𝟙 X.obj : X.obj ⟶ X.obj).1 (u + (w - v)) u ≫
    ι X w (u + (w - v)) = (𝟙 (sigmaObj X).obj : _ ⟶ _).1 w v
  by_cases h : v = w
  · subst h
    rw [id_apply_self]
    refine (Finset.sum_congr rfl fun u _ ↦ ?_).trans
      (total X v _ fun u h₁ h₂ ↦ Finset.mem_Icc.mpr ⟨h₁, h₂⟩)
    rw [comp_congr_index (fun a ↦ (𝟙 X.obj : X.obj ⟶ X.obj).1 a u) (ι X v)
      (show u + (v - v) = u by ring), id_apply_self, id_comp]
  · rw [id_apply_ne _ h]
    exact Finset.sum_eq_zero fun u _ ↦ by
      rw [id_apply_ne _ (show u ≠ u + (w - v) by omega), zero_comp, comp_zero]

lemma sigmaHom_comp {X Y Z : B.czPos} (f : X ⟶ Y) (g : Y ⟶ Z) :
    sigmaHom (f ≫ g) = sigmaHom f ≫ sigmaHom g := by
  obtain ⟨b, hb⟩ := f.hom.2
  ext t v
  change sigmaMat (f ≫ g) t v = ((sigmaHom f).hom ≫ (sigmaHom g).hom).1 t v
  rw [comp_apply_left _ (propLE_sigmaMat f hb)]
  have key (w : ℤ) : (sigmaHom f).hom.1 w v ≫ (sigmaHom g).hom.1 t w =
      ∑ u ∈ Finset.Icc (start X) v, π X v u ≫
        (f.hom.1 (u + (w - v)) u ≫ g.hom.1 (u + (t - v)) (u + (w - v))) ≫ ι Z t (u + (t - v)) := by
    rw [sigmaHom_apply, sigmaHom_apply, sigmaMat, sum_comp]
    refine Finset.sum_congr rfl fun u hu ↦ ?_
    simp only [Finset.mem_Icc] at hu
    rw [assoc, assoc, sigmaMat, ι_comp_sum Y (a := u + (w - v)) (by omega) _
      (fun h ↦ Finset.mem_Icc.mpr ⟨h, by omega⟩)
      (fun u' ↦ g.hom.1 (u' + (t - w)) u' ≫ ι Z t (u' + (t - w))),
      comp_congr_index (fun a ↦ g.hom.1 a (u + (w - v))) (ι Z t)
        (show u + (w - v) + (t - w) = u + (t - v) by ring)]
    simp only [assoc]
  rw [Finset.sum_congr rfl fun w _ ↦ key w, Finset.sum_comm, sigmaMat]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [← comp_sum, ← sum_comp]
  congr 2
  rw [sum_window_shift (fun w' ↦ f.hom.1 w' u ≫ g.hom.1 (u + (t - v)) w') b u v]
  exact comp_apply_left f.hom hb g.hom _ _

lemma sigmaHom_star {X Y : B.czPos} (f : X ⟶ Y) :
    sigmaHom (B.czPos.inv.star f) = B.czPos.inv.star (sigmaHom f) := by
  ext w v
  change ∑ u ∈ Finset.Icc (start Y) v,
      π Y v u ≫ B.inv.star (f.hom.1 u (u + (w - v))) ≫ ι X w (u + (w - v)) =
    B.inv.star (∑ u ∈ Finset.Icc (start X) w,
      π X w u ≫ f.hom.1 (u + (v - w)) u ≫ ι Y v (u + (v - w)))
  rw [star_finsetSum]
  simp only [B.inv.star_comp, star_π, assoc]
  change _ = ∑ u ∈ Finset.Icc (start X) w,
    π Y v (u + (v - w)) ≫ B.inv.star (f.hom.1 (u + (v - w)) u) ≫ ι X w u
  have h₁ : ∑ u ∈ Finset.Icc (start Y) v,
        π Y v u ≫ B.inv.star (f.hom.1 u (u + (w - v))) ≫ ι X w (u + (w - v)) =
      ∑ u ∈ Finset.Icc (min (start Y) (start X + (v - w))) v,
        π Y v u ≫ B.inv.star (f.hom.1 u (u + (w - v))) ≫ ι X w (u + (w - v)) :=
    Finset.sum_subset (fun u hu ↦ by simp only [Finset.mem_Icc] at hu ⊢; omega)
      fun u _ hu ↦ by
        rw [π_eq_zero Y (by simp only [Finset.mem_Icc, not_and_or, not_le] at hu; omega),
          zero_comp]
  have h₂ : ∑ u ∈ Finset.Icc (start X) w,
        π Y v (u + (v - w)) ≫ B.inv.star (f.hom.1 (u + (v - w)) u) ≫ ι X w u =
      ∑ u ∈ Finset.Icc (min (start Y) (start X + (v - w)) + (w - v)) w,
        π Y v (u + (v - w)) ≫ B.inv.star (f.hom.1 (u + (v - w)) u) ≫ ι X w u :=
    Finset.sum_subset (fun u hu ↦ by simp only [Finset.mem_Icc] at hu ⊢; omega)
      fun u hu hu' ↦ by
        simp only [Finset.mem_Icc] at hu hu'
        rw [ι_eq_zero X (by omega), comp_zero, comp_zero]
  rw [h₁, h₂]
  symm
  refine Finset.sum_equiv (Equiv.addRight (v - w))
    (fun u ↦ by simp only [Finset.mem_Icc, Equiv.coe_addRight]; omega) fun u _ ↦ ?_
  simp only [Equiv.coe_addRight]
  rw [← assoc, ← assoc, comp_congr_index (fun b ↦ π Y v (u + (v - w)) ≫
      B.inv.star (f.hom.1 (u + (v - w)) b)) (ι X w) (show u = u + (v - w) + (w - v) by ring)]

variable (B) in
/-- **The swindle functor** `Σ = ⊕_{j ≥ 0} S^j` on `C_{ℤ≥}(B)`: `(ΣX)_v = ⊕_{u ≤ v} X_u` is a
finite sum since `X` vanishes below `start X`. -/
def sigma : B.czPos ⟶ B.czPos where
  F :=
    { obj := sigmaObj
      map := sigmaHom
      map_id := sigmaHom_id
      map_comp := sigmaHom_comp }
  additive := ⟨fun {X Y f g} ↦ ObjectProperty.hom_ext _ <| hom_ext fun w v ↦ by
    change sigmaMat (f + g) w v = sigmaMat f w v + sigmaMat g w v
    simp only [sigmaMat, ← Finset.sum_add_distrib, ← add_comp, ← comp_add]
    rfl⟩
  map_star := sigmaHom_star

/-! #### The decomposition `Σ ≅ 𝟙 ⊕ (Σ ≫ S)` -/

/-- The inclusion `X → ΣX` of the summand `S⁰ X = X`. -/
def d₀ (X : B.czPos) : X.obj ⟶ (sigmaObj X).obj := diag fun v ↦ ι X v v

/-- `J_v : (ΣX)_{v-1} → (ΣX)_v`, the identity on each summand `X_u`, `u ≤ v - 1`. -/
def J (X : B.czPos) (v : ℤ) : pt X (v - 1) ⟶ pt X v :=
  ∑ u ∈ Finset.Icc (start X) (v - 1), π X (v - 1) u ≫ ι X v u

/-- The inclusion `S(ΣX) = ⊕_{j ≥ 1} S^j X → ΣX`. -/
def d₁ (X : B.czPos) : ((posShift B).F.obj (sigmaObj X)).obj ⟶ (sigmaObj X).obj :=
  diag fun v ↦ J X v

lemma star_J (X : B.czPos) (v : ℤ) :
    B.inv.star (J X v) = ∑ u ∈ Finset.Icc (start X) (v - 1), π X v u ≫ ι X (v - 1) u := by
  rw [J, star_finsetSum]
  simp only [B.inv.star_comp, star_π]
  rfl

lemma J_star_J (X : B.czPos) (v : ℤ) : J X v ≫ B.inv.star (J X v) = 𝟙 _ := by
  rw [star_J, J, sum_comp]
  refine (Finset.sum_congr rfl fun u hu ↦ ?_).trans
    (total X (v - 1) _ fun u h₁ h₂ ↦ Finset.mem_Icc.mpr ⟨h₁, h₂⟩)
  simp only [Finset.mem_Icc] at hu
  rw [assoc, ι_comp_sum X (by omega) _ (fun _ ↦ Finset.mem_Icc.mpr hu) (fun u' ↦ ι X (v - 1) u')]

lemma ι_star_J (X : B.czPos) (v : ℤ) : ι X v v ≫ B.inv.star (J X v) = 0 := by
  rw [star_J, comp_sum]
  exact Finset.sum_eq_zero fun u hu ↦ by
    simp only [Finset.mem_Icc] at hu
    rw [← assoc, ι_π_ne X v (by omega), zero_comp]

lemma J_π (X : B.czPos) (v : ℤ) : J X v ≫ π X v v = 0 := by
  rw [J, sum_comp]
  exact Finset.sum_eq_zero fun u hu ↦ by
    simp only [Finset.mem_Icc] at hu
    rw [assoc, ι_π_ne X v (by omega), comp_zero]

lemma total_J (X : B.czPos) (v : ℤ) :
    B.inv.star (J X v) ≫ J X v + π X v v ≫ ι X v v = 𝟙 _ := by
  have h : B.inv.star (J X v) ≫ J X v =
      ∑ u ∈ Finset.Icc (start X) (v - 1), π X v u ≫ ι X v u := by
    rw [star_J, sum_comp]
    refine Finset.sum_congr rfl fun u hu ↦ ?_
    simp only [Finset.mem_Icc] at hu
    rw [assoc, J, ι_comp_sum X (w := v - 1) (by omega) _ (fun _ ↦ Finset.mem_Icc.mpr hu)
      (fun u' ↦ ι X v u')]
  rw [h, add_comm, ← Finset.sum_insert (s := Finset.Icc (start X) (v - 1))
    (f := fun u ↦ π X v u ≫ ι X v u) (by simp)]
  exact total X v _ fun u h₁ h₂ ↦ by
    simp only [Finset.mem_insert, Finset.mem_Icc]; omega

variable (B) in
/-- The natural inclusion `𝟙 ⟶ Σ`. -/
def inc₀ : (𝟙 B.czPos : B.czPos ⟶ B.czPos).F ⟶ (sigma B).F where
  app X := ObjectProperty.homMk (d₀ X)
  naturality X Y f := ObjectProperty.hom_ext _ <| hom_ext fun w v ↦ by
    change (f.hom ≫ d₀ Y).1 w v = (d₀ X ≫ (sigmaHom f).hom).1 w v
    rw [d₀, d₀, comp_diag_apply, diag_comp_apply, sigmaHom_apply, sigmaMat,
      ι_comp_sum X le_rfl _ (fun h ↦ Finset.mem_Icc.mpr ⟨h, le_rfl⟩)
        (fun u ↦ f.hom.1 (u + (w - v)) u ≫ ι Y w (u + (w - v)))]
    exact comp_congr_index (fun a ↦ f.hom.1 a v) (ι Y w) (by ring)

variable (B) in
/-- The natural inclusion `Σ ≫ S ⟶ Σ`. -/
def inc₁ : (sigma B ≫ posShift B).F ⟶ (sigma B).F where
  app X := ObjectProperty.homMk (d₁ X)
  naturality X Y f := ObjectProperty.hom_ext _ <| hom_ext fun w v ↦ by
    change ((shift B).F.map (sigmaHom f).hom ≫ d₁ Y).1 w v = (d₁ X ≫ (sigmaHom f).hom).1 w v
    erw [d₁, d₁, comp_diag_apply, diag_comp_apply, sigmaHom_apply]
    change sigmaMat f (w - 1) (v - 1) ≫ J Y w = J X v ≫ sigmaMat f w v
    have lhs : sigmaMat f (w - 1) (v - 1) ≫ J Y w = ∑ u ∈ Finset.Icc (start X) (v - 1),
        π X (v - 1) u ≫ f.hom.1 (u + (w - v)) u ≫ ι Y w (u + (w - v)) := by
      rw [sigmaMat, sum_comp]
      refine Finset.sum_congr rfl fun u hu ↦ ?_
      simp only [Finset.mem_Icc] at hu
      rw [assoc, assoc, J, ι_comp_sum Y (by omega) _
        (fun h ↦ Finset.mem_Icc.mpr ⟨h, by omega⟩) (fun u' ↦ ι Y w u'),
        comp_congr_index (fun a ↦ f.hom.1 a u) (ι Y w)
          (show u + (w - 1 - (v - 1)) = u + (w - v) by ring)]
    have rhs : J X v ≫ sigmaMat f w v = ∑ u ∈ Finset.Icc (start X) (v - 1),
        π X (v - 1) u ≫ f.hom.1 (u + (w - v)) u ≫ ι Y w (u + (w - v)) := by
      rw [J, sum_comp]
      refine Finset.sum_congr rfl fun u hu ↦ ?_
      simp only [Finset.mem_Icc] at hu
      rw [assoc, sigmaMat, ι_comp_sum X (by omega) _
        (fun h ↦ Finset.mem_Icc.mpr ⟨h, by omega⟩)
        (fun u' ↦ f.hom.1 (u' + (w - v)) u' ≫ ι Y w (u' + (w - v)))]
    rw [lhs, rhs]

lemma inc₀_star_self (X : B.czPos) :
    (inc₀ B).app X ≫ B.czPos.inv.star ((inc₀ B).app X) = 𝟙 _ :=
  ObjectProperty.hom_ext _ <| by
    change d₀ X ≫ involution.star (d₀ X) = 𝟙 X.obj
    rw [d₀, star_diag, diag_comp_diag, ← diag_id]
    exact diag_ext fun v ↦ ι_π_self X le_rfl

lemma inc₁_star_self (X : B.czPos) :
    (inc₁ B).app X ≫ B.czPos.inv.star ((inc₁ B).app X) = 𝟙 _ :=
  ObjectProperty.hom_ext _ <| by
    change d₁ X ≫ involution.star (d₁ X) = 𝟙 _
    erw [d₁, star_diag, diag_comp_diag, ← diag_id]
    exact diag_ext fun v ↦ J_star_J X v

lemma inc₀_star_inc₁ (X : B.czPos) :
    (inc₀ B).app X ≫ B.czPos.inv.star ((inc₁ B).app X) = 0 :=
  ObjectProperty.hom_ext _ <| by
    change d₀ X ≫ involution.star (d₁ X) = 0
    erw [d₀, d₁, star_diag, diag_comp_diag, ← diag_zero]
    exact diag_ext fun v ↦ ι_star_J X v

lemma inc₁_star_inc₀ (X : B.czPos) :
    (inc₁ B).app X ≫ B.czPos.inv.star ((inc₀ B).app X) = 0 :=
  ObjectProperty.hom_ext _ <| by
    change d₁ X ≫ involution.star (d₀ X) = 0
    erw [d₀, d₁, star_diag, diag_comp_diag, ← diag_zero]
    exact diag_ext fun v ↦ J_π X v

lemma total_inc (X : B.czPos) :
    B.czPos.inv.star ((inc₁ B).app X) ≫ (inc₁ B).app X +
      B.czPos.inv.star ((inc₀ B).app X) ≫ (inc₀ B).app X = 𝟙 _ :=
  ObjectProperty.hom_ext _ <| by
    change involution.star (d₁ X) ≫ d₁ X + involution.star (d₀ X) ≫ d₀ X = 𝟙 _
    erw [d₀, d₁, star_diag, star_diag, diag_comp_diag, diag_comp_diag, ← diag_add, ← diag_id]
    exact diag_ext fun v ↦ total_J X v

variable (B) in
/-- The summands of the swindle decomposition: `false ↦ 𝟙`, `true ↦ Σ ≫ S`. -/
def summand (b : Bool) : B.czPos ⟶ B.czPos := cond b (sigma B ≫ posShift B) (𝟙 B.czPos)

variable (B) in
/-- **`Σ ≅ 𝟙 ⊕ (Σ ≫ S)`** as a finite unitary sum: `ΣX = X ⊕ ⊕_{j ≥ 1} S^j X`. -/
def isFinSum : InvCat.IsFinSum (summand B) (sigma B) where
  inc b := match b with
    | false => inc₀ B
    | true => inc₁ B
  inc_star_self b X := by
    cases b
    · exact inc₀_star_self X
    · exact inc₁_star_self X
  inc_star_ne b b' h X := by
    cases b <;> cases b'
    · exact absurd rfl h
    · exact inc₀_star_inc₁ X
    · exact inc₁_star_inc₀ X
    · exact absurd rfl h
  total X := by
    rw [Fintype.sum_bool]
    exact total_inc X

end PosSwindle

end CZ

/-! ### Eilenberg swindles -/

/-- An **Eilenberg swindle** on an `InvCat` `A`: an endofunctor `sum` (`Σ`) which is the finite
unitary sum (`IsFinSum`) of two summands, unitarily isomorphic to `𝟙` and to `Σ ≫ S`, for an
endofunctor `shift` (`S`) unitarily isomorphic to `𝟙`.  Any theory satisfying H4 (functoriality,
`map_unitaryIso`, `map_finSum`) vanishes on `A` (`InvCat.Swindle.eq_zero_of_map`). -/
structure InvCat.Swindle (A : InvCat) where
  /-- `Σ = ⊕_{j ≥ 0} S^j`. -/
  sum : A ⟶ A
  /-- `S`. -/
  shift : A ⟶ A
  shiftIso : InvCat.UnitaryIso shift (𝟙 A)
  /-- The two summands of `Σ`. -/
  summand : Bool → (A ⟶ A)
  isFinSum : InvCat.IsFinSum summand sum
  summandIsoId : InvCat.UnitaryIso (summand false) (𝟙 A)
  summandIsoShift : InvCat.UnitaryIso (summand true) (sum ≫ shift)

namespace InvCat.Swindle

variable {A B : InvCat}

/-- **The swindle argument**: for any H4-type functor `m` on endofunctors of `A` (identity,
composition, unitary invariance, additivity on finite unitary sums), `m Σ = 𝟙 + m S ∘ m Σ =
𝟙 + m Σ`, so the target group is trivial. -/
theorem eq_zero_of_map (s : A.Swindle) {M : Type*} [AddCommGroup M] (m : (A ⟶ A) → (M →+ M))
    (m_id : m (𝟙 A) = AddMonoidHom.id M)
    (m_comp : ∀ Φ Ψ : A ⟶ A, m (Φ ≫ Ψ) = (m Ψ).comp (m Φ))
    (m_iso : ∀ {Φ Ψ : A ⟶ A}, InvCat.UnitaryIso Φ Ψ → m Φ = m Ψ)
    (m_sum : ∀ {Φ : Bool → (A ⟶ A)} {S : A ⟶ A}, InvCat.IsFinSum Φ S → m S = ∑ b, m (Φ b))
    (x : M) : x = 0 := by
  have h := m_sum s.isFinSum
  rw [Fintype.sum_bool, m_iso s.summandIsoShift, m_iso s.summandIsoId, m_comp,
    m_iso s.shiftIso, m_id] at h
  have hx := DFunLike.congr_fun h x
  simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at hx
  simpa using hx

/-- `Σ ≫ S ≅ Σ`, by whiskering `S ≅ 𝟙` ("`shift ∘ Σ ≅ Σ`"). -/
def sumShiftIso (s : A.Swindle) : InvCat.UnitaryIso (s.sum ≫ s.shift) s.sum :=
  s.shiftIso.whiskerLeft s.sum

/-- **`Lconc A N = 0`** for every `N` if `A` admits a swindle. -/
theorem lconc_eq_zero (s : A.Swindle) {N : ℤ} (x : Lconc A N) : x = 0 :=
  s.eq_zero_of_map (fun Φ ↦ Lconc.map Φ) Lconc.map_id (fun Φ Ψ ↦ Lconc.map_comp Φ Ψ)
    (fun e ↦ Lconc.map_eq_of_unitaryIso e) (fun h ↦ Lconc.map_finSum h) x

/-- The ultimate lower L-groups of an `InvCat` with a swindle vanish. -/
theorem lowerL_eq_zero (s : A.Swindle) (𝕃 : LowerLTheory) {n : ℤ} (x : 𝕃.L A n) : x = 0 :=
  s.eq_zero_of_map (fun Φ ↦ 𝕃.map Φ n) (𝕃.map_id A n) (fun Φ Ψ ↦ 𝕃.map_comp Φ Ψ n)
    (fun e ↦ 𝕃.map_unitaryIso e n) (fun h ↦ 𝕃.map_finSum h n) x

/-- A swindle on `A` induces one on `C_ℤ(A)`, entrywise. -/
def cz (s : A.Swindle) : A.cz.Swindle where
  sum := CZ.map s.sum
  shift := CZ.map s.shift
  shiftIso := CZ.mapUnitaryIso s.shiftIso
  summand b := CZ.map (s.summand b)
  isFinSum := CZ.mapIsFinSum s.isFinSum
  summandIsoId := CZ.mapUnitaryIso s.summandIsoId
  summandIsoShift := CZ.mapUnitaryIso s.summandIsoShift

/-- A swindle on `A` induces one on every iterate `C_ℤ^{∘k}(A)`. -/
def czIter : ∀ k : ℕ, A.Swindle → (A.czIter k).Swindle
  | 0, s => s
  | k + 1, s => (czIter k s).cz

/-- `Lconc (C_ℤ^{∘k} A) N = 0` for all `k`, `N` if `A` admits a swindle; this is the vanishing
of every level of the colimit model `colim_k Lconc (C_ℤ^{∘k} A) (n + k)`. -/
theorem lconc_czIter_eq_zero (s : A.Swindle) (k : ℕ) {N : ℤ} (x : Lconc (A.czIter k) N) :
    x = 0 :=
  (s.czIter k).lconc_eq_zero x

/-- Swindles transport along unitary equivalences `Φ : B ⇄ A : Ψ`. -/
def transport (Φ : B ⟶ A) (Ψ : A ⟶ B) (e₁ : InvCat.UnitaryIso (Φ ≫ Ψ) (𝟙 B))
    (e₂ : InvCat.UnitaryIso (Ψ ≫ Φ) (𝟙 A)) (s : A.Swindle) : B.Swindle where
  sum := Φ ≫ s.sum ≫ Ψ
  shift := Φ ≫ s.shift ≫ Ψ
  shiftIso := ((s.shiftIso.whiskerRight Ψ).whiskerLeft Φ).trans e₁
  summand b := Φ ≫ s.summand b ≫ Ψ
  isFinSum := (s.isFinSum.whiskerRight Ψ).whiskerLeft Φ
  summandIsoId := ((s.summandIsoId.whiskerRight Ψ).whiskerLeft Φ).trans e₁
  summandIsoShift := ((s.summandIsoShift.whiskerRight Ψ).whiskerLeft Φ).trans
    (((e₂.symm.whiskerLeft s.sum).whiskerRight (s.shift ≫ Ψ)).whiskerLeft Φ)

end InvCat.Swindle

/-! ### The half-line swindles and the vanishing of `Lconc` -/

namespace CZ

variable (B : InvCat)

/-- **The Eilenberg swindle on the positive half-line** `C_{ℤ≥}(B)`:
`Σ = ⊕_{j ≥ 0} S^j ≅ 𝟙 ⊕ (Σ ≫ S)` and `S ≅ 𝟙`. -/
def posSwindle : B.czPos.Swindle where
  sum := PosSwindle.sigma B
  shift := posShift B
  shiftIso := posShiftIso B
  summand := PosSwindle.summand B
  isFinSum := PosSwindle.isFinSum B
  summandIsoId := .refl _
  summandIsoShift := .refl _

/-- **The Eilenberg swindle on the negative half-line** `C_{ℤ≤}(B)`, transported along the
reflection `v ↦ -v`. -/
def negSwindle : B.czNeg.Swindle :=
  (posSwindle B).transport (negToPos B) (posToNeg B) (negToPosToNegIso B) (posToNegToPosIso B)

end CZ

/-! ### The half-line Karoubi filtrations `C_{ℤ≥}(B) ⊂ C_ℤ(B)` and `C_{ℤ≤}(B) ⊂ C_ℤ(B)` -/

namespace CZ

variable {B : InvCat}

open ZeroObject

/-- The splitting `P = P ⊕ 0`. -/
@[simps]
def splitE (P : B) : Splitting P where
  E := P
  U := 0
  ιE := 𝟙 P
  πE := 𝟙 P
  ιU := 0
  πU := 0
  ιE_πE := id_comp _
  ιU_πU := (isZero_zero B).eq_of_src _ _
  ιE_πU := comp_zero
  ιU_πE := zero_comp
  total := by simp

/-- The splitting `P = 0 ⊕ P`. -/
@[simps]
def splitU (P : B) : Splitting P where
  E := 0
  U := P
  ιE := 0
  πE := 0
  ιU := 𝟙 P
  πU := 𝟙 P
  ιE_πE := (isZero_zero B).eq_of_src _ _
  ιU_πU := id_comp _
  ιE_πU := zero_comp
  ιU_πE := comp_zero
  total := by simp

lemma star_ite_ιE (P : B) (c : Prop) [Decidable c] :
    B.inv.star (if c then splitE P else splitU P).ιE = (if c then splitE P else splitU P).πE := by
  by_cases h : c
  · rw [ite_eq_left h]; exact B.inv.star_id _
  · rw [ite_eq_right h]; exact B.inv.star_zero

lemma star_ite_ιU (P : B) (c : Prop) [Decidable c] :
    B.inv.star (if c then splitE P else splitU P).ιU = (if c then splitE P else splitU P).πU := by
  by_cases h : c
  · rw [ite_eq_left h]; exact B.inv.star_zero
  · rw [ite_eq_right h]; exact B.inv.star_id _

/-- The **cut** of `X : C_ℤ(B)` along a set of positions `p`: `E = X|_p`, `U = X|_{¬p}`
(diagonal, self-dual). -/
def cut (X : B.cz) (p : ℤ → Prop) [DecidablePred p] : Splitting X :=
  diagSplitting fun v ↦ if p v then splitE (X.obj v) else splitU (X.obj v)

lemma isZero_cut_E (X : B.cz) (p : ℤ → Prop) [DecidablePred p] {v : ℤ} (h : ¬p v) :
    IsZero ((cut X p).E.obj v) := by
  change IsZero (if p v then splitE (X.obj v) else splitU (X.obj v)).E
  rw [ite_eq_right h]
  exact isZero_zero B

lemma cut_idem (X : B.cz) (p : ℤ → Prop) [DecidablePred p] :
    (cut X p).idem = diag fun v ↦ if p v then 𝟙 (X.obj v) else 0 := by
  rw [cut, diagSplitting_idem]
  exact diag_ext fun v ↦ by
    split_ifs <;> simp [Splitting.idem] <;> first | exact Category.comp_id _ | exact zero_comp

lemma star_cut_ιE (X : B.cz) (p : ℤ → Prop) [DecidablePred p] :
    B.cz.inv.star (cut X p).ιE = (cut X p).πE := by
  erw [cut, diagSplitting_ιE, diagSplitting_πE, star_diag]
  exact diag_ext fun v ↦ star_ite_ιE (X.obj v) (p v)

lemma star_cut_ιU (X : B.cz) (p : ℤ → Prop) [DecidablePred p] :
    B.cz.inv.star (cut X p).ιU = (cut X p).πU := by
  erw [cut, diagSplitting_ιU, diagSplitting_πU, star_diag]
  exact diag_ext fun v ↦ star_ite_ιU (X.obj v) (p v)

lemma idemLE_cut (X : B.cz) {p q : ℤ → Prop} [DecidablePred p] [DecidablePred q]
    (h : ∀ v, p v → q v) : IdemLE (cut X p).idem (cut X q).idem := by
  rw [cut_idem, cut_idem]
  refine idemLE_diag fun v ↦ ?_
  by_cases hp : p v
  · simp [hp, h v hp, IdemLE]
  · by_cases hq : q v <;> simp [hp, hq, IdemLE]

/-- A map into `X` vanishing outside the cut is absorbed by the cut idempotent. -/
lemma comp_cut_idem {W X : B.cz} (f : W ⟶ X) (p : ℤ → Prop) [DecidablePred p]
    (h : ∀ w v, ¬p w → f.1 w v = 0) : f ≫ (cut X p).idem = f := by
  rw [cut_idem]
  ext w v
  rw [comp_diag_apply]
  by_cases hw : p w
  · rw [ite_eq_left hw, comp_id]
  · rw [ite_eq_right hw, comp_zero, h w v hw]

/-- A map out of `X` vanishing outside the cut is absorbed by the cut idempotent. -/
lemma cut_idem_comp {X W : B.cz} (f : X ⟶ W) (p : ℤ → Prop) [DecidablePred p]
    (h : ∀ w v, ¬p v → f.1 w v = 0) : (cut X p).idem ≫ f = f := by
  rw [cut_idem]
  ext w v
  rw [diag_comp_apply]
  by_cases hv : p v
  · rw [ite_eq_left hv, id_comp]
  · rw [ite_eq_right hv, zero_comp, h w v hv]

/-- The Karoubi filtration of `C_ℤ(B)` by cut splittings along the sets `p c`, given the
factorization estimates. -/
def cutFiltration (U : ObjectProperty B.cz) [IsAdditiveSub U] (p : ℤ → ℤ → Prop)
    [∀ c, DecidablePred (p c)] (mem : ∀ X c, U (cut X (p c)).E)
    (directed : ∀ c₁ c₂, ∃ c, (∀ v, p c₁ v → p c v) ∧ ∀ v, p c₂ v → p c v)
    (factor_to : ∀ {W X : B.cz}, U W → ∀ f : W ⟶ X, ∃ c, ∀ w v, ¬p c w → f.1 w v = 0)
    (factor_from : ∀ {X W : B.cz}, U W → ∀ f : X ⟶ W, ∃ c, ∀ w v, ¬p c v → f.1 w v = 0) :
    KaroubiFiltration B.cz where
  U := U
  filt := HSFormal.KaroubiFiltration.ofFactor U (fun X ↦ Set.range fun c ↦ cut X (p c))
    (by rintro X _ ⟨c, rfl⟩; exact mem X c)
    (fun X ↦ ⟨_, 0, rfl⟩)
    (by
      rintro X _ ⟨c₁, rfl⟩ _ ⟨c₂, rfl⟩
      obtain ⟨c, h₁, h₂⟩ := directed c₁ c₂
      exact ⟨_, ⟨c, rfl⟩, idemLE_cut X h₁, idemLE_cut X h₂⟩)
    (fun {W X} hW f ↦ by
      obtain ⟨c, hc⟩ := factor_to hW f
      exact ⟨_, ⟨c, rfl⟩, f ≫ (cut X (p c)).πE, by
        rw [assoc, ← Splitting.idem, comp_cut_idem f _ hc]⟩)
    (fun {X W} hW f ↦ by
      obtain ⟨c, hc⟩ := factor_from hW f
      exact ⟨_, ⟨c, rfl⟩, (cut X (p c)).ιE ≫ f, by
        rw [← assoc, ← Splitting.idem, cut_idem_comp f _ hc]⟩)
  star_ιE := by rintro X _ ⟨c, rfl⟩; exact star_cut_ιE X _
  star_ιU := by rintro X _ ⟨c, rfl⟩; exact star_cut_ιU X _

variable (B) in
/-- **The positive half-line filtration** `C_{ℤ≥}(B) ⊂ C_ℤ(B)` ([CP95, 1.27]): splittings
`X = X|_{[c, ∞)} ⊕ X|_{(-∞, c)}`; a map of propagation `b` into or out of an object supported in
`[c, ∞)` factors through the cut at `c - b`.  Its `sub` is `B.czPos`; its quotient is the
category of germs at `-∞`. -/
def posFiltration : KaroubiFiltration B.cz :=
  cutFiltration (posHalf B) (fun c v ↦ c ≤ v)
    (fun X c ↦ ⟨c, fun v hv ↦ isZero_cut_E X _ (by omega)⟩)
    (fun c₁ c₂ ↦ ⟨min c₁ c₂, fun v h ↦ by omega, fun v h ↦ by omega⟩)
    (fun {W X} ⟨c, hc⟩ f ↦ by
      obtain ⟨b, hb⟩ := f.2
      refine ⟨c - b, fun w v hw ↦ ?_⟩
      by_cases h : (b : ℤ) < |w - v|
      · exact hb w v h
      · exact (hc v (by rw [not_lt, abs_le] at h; omega)).eq_of_src _ _)
    (fun {X W} ⟨c, hc⟩ f ↦ by
      obtain ⟨b, hb⟩ := f.2
      refine ⟨c - b, fun w v hv ↦ ?_⟩
      by_cases h : (b : ℤ) < |w - v|
      · exact hb w v h
      · exact (hc w (by rw [not_lt, abs_le] at h; omega)).eq_of_tgt _ _)

variable (B) in
/-- **The negative half-line filtration** `C_{ℤ≤}(B) ⊂ C_ℤ(B)`: splittings
`X = X|_{(-∞, c]} ⊕ X|_{(c, ∞)}`.  Its `sub` is `B.czNeg`. -/
def negFiltration : KaroubiFiltration B.cz :=
  cutFiltration (negHalf B) (fun c v ↦ v ≤ c)
    (fun X c ↦ ⟨c, fun v hv ↦ isZero_cut_E X _ (by omega)⟩)
    (fun c₁ c₂ ↦ ⟨max c₁ c₂, fun v h ↦ by omega, fun v h ↦ by omega⟩)
    (fun {W X} ⟨c, hc⟩ f ↦ by
      obtain ⟨b, hb⟩ := f.2
      refine ⟨c + b, fun w v hw ↦ ?_⟩
      by_cases h : (b : ℤ) < |w - v|
      · exact hb w v h
      · exact (hc v (by rw [not_lt, abs_le] at h; omega)).eq_of_src _ _)
    (fun {X W} ⟨c, hc⟩ f ↦ by
      obtain ⟨b, hb⟩ := f.2
      refine ⟨c + b, fun w v hv ↦ ?_⟩
      by_cases h : (b : ℤ) < |w - v|
      · exact hb w v h
      · exact (hc w (by rw [not_lt, abs_le] at h; omega)).eq_of_tgt _ _)

lemma posFiltration_U : (posFiltration B).U = posHalf B := rfl

lemma negFiltration_U : (negFiltration B).U = negHalf B := rfl

lemma posFiltration_sub : (posFiltration B).sub = B.czPos := rfl

lemma negFiltration_sub : (negFiltration B).sub = B.czNeg := rfl

/-- `C_ℤ(Φ)` is a map of positive half-line filtrations. -/
def posFiltrationHom {B' : InvCat} (Φ : B ⟶ B') :
    FiltrationHom (posFiltration B) (posFiltration B') :=
  ⟨map Φ, fun _ ⟨c, hc⟩ ↦ ⟨c, fun v hv ↦ Φ.F.map_isZero (hc v hv)⟩⟩

/-- `C_ℤ(Φ)` is a map of negative half-line filtrations. -/
def negFiltrationHom {B' : InvCat} (Φ : B ⟶ B') :
    FiltrationHom (negFiltration B) (negFiltration B') :=
  ⟨map Φ, fun _ ⟨c, hc⟩ ↦ ⟨c, fun v hv ↦ Φ.F.map_isZero (hc v hv)⟩⟩

end CZ

namespace Lconc

variable (B : InvCat) {N : ℤ}

/-- **`L^p_N(C_{ℤ≥}(B)) = 0`** for all `N` (Eilenberg swindle). -/
theorem czPos_eq_zero (x : Lconc B.czPos N) : x = 0 := (CZ.posSwindle B).lconc_eq_zero x

/-- **`L^p_N(C_{ℤ≤}(B)) = 0`** for all `N` (Eilenberg swindle). -/
theorem czNeg_eq_zero (x : Lconc B.czNeg N) : x = 0 := (CZ.negSwindle B).lconc_eq_zero x

instance : Subsingleton (Lconc B.czPos N) :=
  ⟨fun x y ↦ by rw [czPos_eq_zero B x, czPos_eq_zero B y]⟩

instance : Subsingleton (Lconc B.czNeg N) :=
  ⟨fun x y ↦ by rw [czNeg_eq_zero B x, czNeg_eq_zero B y]⟩

/-- Every level `Lconc (C_ℤ^{∘k}(C_{ℤ≥} B)) N` of the colimit model of `C_{ℤ≥}(B)` vanishes. -/
theorem czIter_czPos_eq_zero (k : ℕ) (x : Lconc (B.czPos.czIter k) N) : x = 0 :=
  (CZ.posSwindle B).lconc_czIter_eq_zero k x

/-- Every level `Lconc (C_ℤ^{∘k}(C_{ℤ≤} B)) N` of the colimit model of `C_{ℤ≤}(B)` vanishes. -/
theorem czIter_czNeg_eq_zero (k : ℕ) (x : Lconc (B.czNeg.czIter k) N) : x = 0 :=
  (CZ.negSwindle B).lconc_czIter_eq_zero k x

variable {B}

/-- A Poincaré complex over `C_ℤ(B)` all of whose chain objects are supported in half-lines
`[c, ∞)` has class zero in `Lconc (C_ℤ B) N`: it is the image of a complex over `C_{ℤ≥}(B)`. -/
theorem cls_eq_zero_of_posHalf (P : SymPoincare B.cz.inv N) (h : ∀ r, CZ.posHalf B (P.C.X r)) :
    cls P = 0 := by
  have e : cls P = map (B.cz.subIncl (CZ.posHalf B)) (cls (P.lift h)) := by
    rw [map_cls]; rfl
  rw [e, czPos_eq_zero B (cls (P.lift h)), map_zero]

/-- A Poincaré complex over `C_ℤ(B)` all of whose chain objects are supported in half-lines
`(-∞, c]` has class zero in `Lconc (C_ℤ B) N`. -/
theorem cls_eq_zero_of_negHalf (P : SymPoincare B.cz.inv N) (h : ∀ r, CZ.negHalf B (P.C.X r)) :
    cls P = 0 := by
  have e : cls P = map (B.cz.subIncl (CZ.negHalf B)) (cls (P.lift h)) := by
    rw [map_cls]; rfl
  rw [e, czNeg_eq_zero B (cls (P.lift h)), map_zero]

end Lconc

namespace LowerLTheory

variable (𝕃 : LowerLTheory) (B : InvCat) {n : ℤ}

/-- The ultimate lower L-groups of the positive half-line category vanish. -/
theorem L_czPos_eq_zero (x : 𝕃.L B.czPos n) : x = 0 := (CZ.posSwindle B).lowerL_eq_zero 𝕃 x

/-- The ultimate lower L-groups of the negative half-line category vanish. -/
theorem L_czNeg_eq_zero (x : 𝕃.L B.czNeg n) : x = 0 := (CZ.negSwindle B).lowerL_eq_zero 𝕃 x

/-- With H1, the projection `L_n(C_ℤ B) → L_n(C_ℤ B / C_{ℤ≥} B)` to the germs at `-∞` is
bijective (exactness at `L(C_ℤ B)` and at `L(C_ℤ B / C_{ℤ≥} B)`, and `L(C_{ℤ≥} B) = 0`). -/
theorem map_proj_posFiltration_bijective (n : ℤ) :
    Function.Bijective (𝕃.map (CZ.posFiltration B).proj n) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_, fun z ↦ ?_⟩
  · obtain ⟨y, rfl⟩ := (𝕃.exact_A (CZ.posFiltration B) n x).mp hx
    erw [L_czPos_eq_zero 𝕃 B y, map_zero]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
    exact (𝕃.exact_Q (CZ.posFiltration B) m z).mp (L_czPos_eq_zero 𝕃 B _)

/-- With H1, the projection `L_n(C_ℤ B) → L_n(C_ℤ B / C_{ℤ≤} B)` to the germs at `+∞` is
bijective. -/
theorem map_proj_negFiltration_bijective (n : ℤ) :
    Function.Bijective (𝕃.map (CZ.negFiltration B).proj n) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_, fun z ↦ ?_⟩
  · obtain ⟨y, rfl⟩ := (𝕃.exact_A (CZ.negFiltration B) n x).mp hx
    erw [L_czNeg_eq_zero 𝕃 B y, map_zero]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
    exact (𝕃.exact_Q (CZ.negFiltration B) m z).mp (L_czNeg_eq_zero 𝕃 B _)

end LowerLTheory

end

end HSFormal.LTheory
