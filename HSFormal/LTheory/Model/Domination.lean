import HSFormal.LTheory.Model.Cascade
import HSFormal.LTheory.Model.Transport
import HSFormal.LTheory.Model.BoundaryConstruction
import HSFormal.CornerClass

/-!
# Domination and Kar(U) models (lower L-theory model, module 14)

`blueprint/lower-L-construction.md` §3.2 (L1-iv), (L1-v) and §4 row 14, for a Karoubi filtration
`F : U ⊂ A`.

* `KaroubiFiltration.ContractibleMod p`: the Kar complex `(D, p)` of `A` is contractible in
  `Kar(A/U)`, i.e. `p ≃ e` for a Kar chain map `e` with components in `I_U`.  It follows from a
  null-homotopy of `[p]` in `A/U` (`contractibleMod_of_homotopy`).
* **Domination** (L1-iv): `exists_domination`.  If `(D, p)` (concentrated in `[lo, hi]`) is
  contractible modulo `U`, then it is `U`-dominated (`Domination`): there are a complex `K` with
  objects in `U`, a strict idempotent `q` of `K` concentrated in `[lo, hi]` and Kar maps
  `i : (D, p) ⟶ (K, q)`, `r : (K, q) ⟶ (D, p)` with `i r ≃ p`.  Here `K` is the `E`-part
  subcomplex of a cascade (`exists_cascade_absorb`) of the compressed complex `(D, p d)`
  absorbing `e`, `i = e` and `r = ι_K`.  The honest bounded case is
  `exists_domination_of_isZero`.
* **Kar(U) model** (L1-v): `Domination.nonempty_subModel`, `exists_subModel`.  BS01 in `U`
  (`KarSplitting.exists_splitting` in `F.sub`) splits the homotopy idempotent `r i` of `(K, q)`:
  `(D, p)` is Kar-homotopy equivalent to the image of a Kar complex `(X, e)` of `U`, `e` strict and
  concentrated in `[lo, hi]` (`SubModel`).
* **Symmetric version**: `SymPoincare.exists_sub`.  A Poincaré complex of `A` contractible modulo
  `U` is homotopy isometric to the image of a Poincaré complex of `F.sub` (transport along the
  Kar(U) model, `SymPoincare.transport`, and `FFLift.preimPoincare`).
* **Boundaries**: `contractibleMod_desusp_cone`, `contractibleMod_bd`.  The desuspended cone of a
  Kar map which is an equivalence in `Kar(A/U)` is contractible modulo `U` (five lemma
  `isKarEquiv_coneMap` against the cone of an identity, and `mapConeInv : Cone(Φj) ≅ Φ(Cone j)`).
  In particular for `∂C = Σ⁻¹Cone(φ)` of a complex whose `φ` is Poincaré modulo `U`:
  `SymComplex.exists_sub_boundary` gives the Kar(U) model of the boundary of the lifting pair.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression

noncomputable section

/-! ### Lifting along fully faithful functors -/

namespace FFLift

variable {V W : Type*} [Category V] [Preadditive V] [Category W] [Preadditive W]
  {Φ : V ⥤ W} [Φ.Additive] (hΦ : Φ.FullyFaithful) {X Y : ChainComplex V ℤ}

/-- The preimage of a chain map between images. -/
@[simps, implicit_reducible]
def preimH (g : (Φ.mapHomologicalComplex _).obj X ⟶ (Φ.mapHomologicalComplex _).obj Y) :
    X ⟶ Y where
  f n := hΦ.preimage (g.f n)
  comm' i j _ := hΦ.map_injective (by simpa using g.comm i j)

@[simp]
lemma map_preimH (g : (Φ.mapHomologicalComplex _).obj X ⟶ (Φ.mapHomologicalComplex _).obj Y) :
    (Φ.mapHomologicalComplex _).map (preimH hΦ g) = g := by
  ext n; simp

include hΦ in
lemma mapH_injective {f f' : X ⟶ Y}
    (h : (Φ.mapHomologicalComplex _).map f = (Φ.mapHomologicalComplex _).map f') : f = f' := by
  ext n; exact hΦ.map_injective (congrArg (fun x ↦ x.f n) h)

/-- The preimage of a homotopy between images. -/
def preimHomotopy {f f' : X ⟶ Y} (H : Homotopy ((Φ.mapHomologicalComplex _).map f)
    ((Φ.mapHomologicalComplex _).map f')) : Homotopy f f' where
  hom i j := hΦ.preimage (H.hom i j)
  zero i j h := hΦ.map_injective (by rw [hΦ.map_preimage, H.zero i j h, Φ.map_zero])
  comm i := hΦ.map_injective (by
    have := homotopy_comm H i (i - 1) (i + 1) (down_rel_pred i) (down_rel_succ i)
    rw [dNext_eq _ (down_rel_pred i), prevD_eq _ (down_rel_succ i)]
    simpa using this)

section Inv

variable {J : StrictInvolution V} {J' : StrictInvolution W} (Ψ : InvFunctor J J')
  (hΨ : Ψ.F.FullyFaithful) {N : ℤ}

@[simp]
lemma mapH_preimH {X Y : ChainComplex V ℤ} (g : Ψ.mapC X ⟶ Ψ.mapC Y) :
    Ψ.mapH (preimH hΨ g) = g :=
  map_preimH hΨ g

include hΨ in
lemma mapDual_injective {C D : ChainComplex V ℤ} {φ φ' : dualComplex J N C ⟶ D}
    (h : Ψ.mapDual φ = Ψ.mapDual φ') : φ = φ' := by
  ext r; exact hΨ.map_injective (by simpa using congrArg (fun x ↦ x.f r) h)

variable (X : ChainComplex V ℤ) (e : X ⟶ X)

@[reassoc]
lemma mapH_dualHom_comp_hom :
    Ψ.mapH (dualHom J N e) ≫ (Ψ.mapDualIso N X).hom =
      (Ψ.mapDualIso N X).hom ≫ dualHom J' N (Ψ.mapH e) := by
  rw [Ψ.dualHom_mapH]; simp

@[reassoc]
lemma inv_comp_mapH_dualHom :
    (Ψ.mapDualIso N X).inv ≫ Ψ.mapH (dualHom J N e) =
      dualHom J' N (Ψ.mapH e) ≫ (Ψ.mapDualIso N X).inv := by
  rw [Ψ.dualHom_mapH]; simp

variable {X} (φ : dualComplex J' N (Ψ.mapC X) ⟶ Ψ.mapC X)

/-- The preimage `Ψ⁻¹ φ : X^{N-*} ⟶ X` of a structure on the image. -/
abbrev preimDual : dualComplex J N X ⟶ X := preimH hΨ ((Ψ.mapDualIso N X).hom ≫ φ)

@[simp]
lemma mapDual_preimDual : Ψ.mapDual (preimDual Ψ hΨ φ) = φ := by
  rw [Ψ.mapDual_eq, preimDual, mapH_preimH, Iso.inv_hom_id_assoc]

/-- **The preimage of a Poincaré structure** on the image `Ψ(X, e)` of a Kar complex of `V` under
a fully faithful duality-preserving functor. -/
@[simps]
def preimPoincare (he : e ≫ e = e) (hs : SupportedIn e 0 N)
    (hkar : dualHom J' N (Ψ.mapH e) ≫ φ ≫ Ψ.mapH e = φ) (hsymm : IsStrictSymm J' N φ)
    (hP : IsPoincare J' N (Ψ.mapH e) φ) : SymPoincare J N where
  C := X
  p := e
  p_idem := he
  support := hs
  φ := preimDual Ψ hΨ φ
  φ_kar := mapH_injective hΨ (by
    simp only [Functor.map_comp, map_preimH, assoc, mapH_dualHom_comp_hom_assoc, hkar])
  symm := mapDual_injective Ψ hΨ (by
    rw [← Ψ.transposeHom_mapDual, mapDual_preimDual]; exact hsymm)
  poincare := by
    obtain ⟨ψ, hψ, ⟨H₁⟩, ⟨H₂⟩⟩ := hP
    refine ⟨preimH hΨ (ψ ≫ (Ψ.mapDualIso N X).inv), mapH_injective hΨ ?_,
      ⟨preimHomotopy hΨ (homotopyCongr H₁ ?_ rfl)⟩,
      ⟨preimHomotopy hΨ (homotopyCongr ((H₂.compRight (Ψ.mapDualIso N X).inv).compLeft
        (Ψ.mapDualIso N X).hom) ?_ ?_)⟩⟩
    · simp only [Functor.map_comp, map_preimH, assoc, inv_comp_mapH_dualHom]
      rw [← assoc (Ψ.mapH e), ← assoc (Ψ.mapH e ≫ ψ), assoc (Ψ.mapH e), hψ]
    · simp
    · simp
    · rw [Ψ.dualHom_mapH]; simp

lemma map_preimPoincare_φ (he : e ≫ e = e) (hs : SupportedIn e 0 N)
    (hkar : dualHom J' N (Ψ.mapH e) ≫ φ ≫ Ψ.mapH e = φ) (hsymm : IsStrictSymm J' N φ)
    (hP : IsPoincare J' N (Ψ.mapH e) φ) :
    ((preimPoincare Ψ hΨ e φ he hs hkar hsymm hP).map Ψ).φ = φ := by
  simp only [SymPoincare.map_φ, preimPoincare_φ]
  exact mapDual_preimDual (Ψ := Ψ) (hΨ := hΨ) (φ := φ)

end Inv

end FFLift

/-! ### The cone of the image of a chain map -/

section MapCone

open homotopyCofiber

variable {V W : Type*} [Category V] [Preadditive V] [HasBinaryBiproducts V] [Category W]
  [Preadditive W] [HasBinaryBiproducts W] (Φ : V ⥤ W) [Φ.Additive] {B D B' D' : ChainComplex V ℤ}
  (j : B ⟶ D)

/-- The comparison `Cone(Φ j) ⟶ Φ(Cone j)` (an isomorphism, `isIso_mapConeInv`). -/
def mapConeInv : cone ((Φ.mapHomologicalComplex _).map j) ⟶
    (Φ.mapHomologicalComplex _).obj (cone j) :=
  desc _ ((Φ.mapHomologicalComplex _).map (inr j))
    (homotopyCongr (Φ.mapHomotopy (inrCompHomotopy j down_exists_rel)) (Functor.map_comp _ _ _)
      (Functor.map_zero _ _ _))

@[reassoc (attr := simp)]
lemma inlX_mapConeInv (i k : ℤ) (hk : (ComplexShape.down ℤ).Rel i k) :
    inlX ((Φ.mapHomologicalComplex _).map j) k i hk ≫ (mapConeInv Φ j).f i =
      Φ.map (inlX j k i hk) := by
  simp [mapConeInv, homotopyCongr, inrCompHomotopy_hom _ _ _ _ hk]

@[reassoc (attr := simp)]
lemma inrX_mapConeInv (i : ℤ) :
    inrX ((Φ.mapHomologicalComplex _).map j) i ≫ (mapConeInv Φ j).f i = Φ.map (inrX j i) := by
  simp [mapConeInv]

/-- The inverse components of `mapConeInv`. -/
def mapConeX (i : ℤ) : Φ.obj ((cone j).X i) ⟶ (cone ((Φ.mapHomologicalComplex _).map j)).X i :=
  Φ.map (fstX j i (i - 1) (down_rel_pred i)) ≫
      inlX ((Φ.mapHomologicalComplex _).map j) (i - 1) i (down_rel_pred i) +
    Φ.map (sndX j i) ≫ inrX ((Φ.mapHomologicalComplex _).map j) i

instance (i : ℤ) : IsIso ((mapConeInv Φ j).f i) := by
  refine ⟨mapConeX Φ j i, ?_, ?_⟩
  · apply ext_from_X ((Φ.mapHomologicalComplex _).map j) (i - 1) i (down_rel_pred i) <;>
      simp [mapConeX, ← Functor.map_comp_assoc]
  · simp only [mapConeX, add_comp, assoc, inlX_mapConeInv, inrX_mapConeInv,
      ← Functor.map_comp]
    rw [← Functor.map_add, ← cone.id_X j i (i - 1) (down_rel_pred i)]
    exact Φ.map_id _

instance isIso_mapConeInv : IsIso (mapConeInv Φ j) := Hom.isIso_of_components _

variable {j} {j' : B' ⟶ D'}

lemma coneMap_comp_mapConeInv {m : B ⟶ B'} {n : D ⟶ D'} (h : m ≫ j' = j ≫ n) :
    coneMap ((Φ.mapHomologicalComplex _).map m) ((Φ.mapHomologicalComplex _).map n)
        (by simp only [← Functor.map_comp, h]) ≫ mapConeInv Φ j' =
      mapConeInv Φ j ≫ (Φ.mapHomologicalComplex _).map (coneMap m n h) := by
  ext i
  apply ext_from_X ((Φ.mapHomologicalComplex _).map j) (i - 1) i (down_rel_pred i)
  · simp only [comp_f, inlX_coneMap_f_assoc, inlX_mapConeInv_assoc,
      Functor.mapHomologicalComplex_map_f, inlX_mapConeInv, ← Functor.map_comp, inlX_coneMap_f]
  · simp only [comp_f, inrX_coneMap_f_assoc, inrX_mapConeInv_assoc,
      Functor.mapHomologicalComplex_map_f, inrX_mapConeInv, ← Functor.map_comp, inrX_coneMap_f]

end MapCone

/-! ### Kar lemmas -/

section KarLemmas

variable {V : Type*} [Category V] [Preadditive V]

lemma coneMap_congr' [HasBinaryBiproducts V] {B D B' D' : ChainComplex V ℤ} {j : B ⟶ D}
    {j' : B' ⟶ D'} {m m' : B ⟶ B'} {n n' : D ⟶ D'} (h : m ≫ j' = j ≫ n) (h' : m' ≫ j' = j ≫ n')
    (hm : m = m') (hn : n = n') : coneMap m n h = coneMap m' n' h' := by
  subst hm hn; rfl

/-- A Kar complex Kar-equivalent to a contractible one is contractible. -/
lemma homotopy_zero_of_isKarEquiv {X Y : ChainComplex V ℤ} {e : X ⟶ X} {e' : Y ⟶ Y}
    {f : X ⟶ Y} (h : IsKarEquiv e e' f) (H : Homotopy e' 0) : Nonempty (Homotopy e 0) := by
  obtain ⟨g, hg, -, ⟨H₂⟩⟩ := h
  exact ⟨H₂.symm.trans (homotopyCongr ((Homotopy.refl f).comp (H.comp (Homotopy.refl (g ≫ e))))
    (by rw [hg]) (by simp))⟩

/-- Contractibility transfers along a strict isomorphism conjugating the idempotents. -/
def homotopyZeroOfIso {X Y : ChainComplex V ℤ} (a : X ⟶ Y) [IsIso a] {u : X ⟶ X} {v : Y ⟶ Y}
    (h : u ≫ a = a ≫ v) (H : Homotopy u 0) : Homotopy v 0 :=
  homotopyCongr ((Homotopy.refl (inv a)).comp (H.comp (Homotopy.refl a)))
    (by rw [h, IsIso.inv_hom_id_assoc]) (by simp)

/-- The cone of the identity of a Kar complex is contractible. -/
def coneIdHomotopy [HasBinaryBiproducts V] {C : ChainComplex V ℤ} {p : C ⟶ C} (hp : p ≫ p = p)
    (h : p ≫ p = p ≫ p) : Homotopy (coneMap (j := p) (j' := p) p p h) 0 :=
  homotopyCongr (coneNullHomotopy p p p) (coneMap_congr' _ _ hp hp) rfl

end KarLemmas

/-! ### Compressed complexes and indicator idempotents -/

section Compress

variable {V : Type*} [Category V] [Preadditive V] {D : ChainComplex V ℤ} (p : D ⟶ D)

/-- `(D, p d)`: the objects of `D` with the differential compressed by the chain map `p`. -/
@[simps, implicit_reducible]
def compressC : ChainComplex V ℤ where
  X := D.X
  d i j := p.f i ≫ D.d i j
  shape i j h := by rw [D.shape i j h, comp_zero]
  d_comp_d' i j k _ _ := by
    simp only [assoc]
    rw [← p.comm_assoc]
    simp

/-- `p d` vanishes unless both degrees lie in the support of `p`. -/
lemma p_f_comp_d_eq_zero {p : D ⟶ D} {lo hi : ℤ} (hs : SupportedIn p lo hi) {i j : ℤ}
    (h : ¬ (lo ≤ i ∧ i ≤ hi ∧ lo ≤ j ∧ j ≤ hi)) : p.f i ≫ D.d i j = 0 := by
  by_cases hi' : lo ≤ i ∧ i ≤ hi
  · rw [p.comm, hs j (by omega), comp_zero]
  · rw [hs i (by omega), zero_comp]

/-- The idempotent `𝟙` in degrees `[lo, hi]` and `0` outside, for a complex whose differential
vanishes unless both degrees lie in `[lo, hi]`. -/
@[simps]
def degIndicator (K : ChainComplex V ℤ) (lo hi : ℤ)
    (hK : ∀ i j, ¬ (lo ≤ i ∧ i ≤ hi ∧ lo ≤ j ∧ j ≤ hi) → K.d i j = 0) : K ⟶ K where
  f n := if lo ≤ n ∧ n ≤ hi then 𝟙 _ else 0
  comm' i j _ := by
    by_cases h : lo ≤ i ∧ i ≤ hi ∧ lo ≤ j ∧ j ≤ hi
    · rw [if_pos ⟨h.1, h.2.1⟩, if_pos ⟨h.2.2.1, h.2.2.2⟩, id_comp, comp_id]
    · rw [hK i j h, comp_zero, zero_comp]

@[reassoc]
lemma degIndicator_idem (K : ChainComplex V ℤ) (lo hi : ℤ)
    (hK : ∀ i j, ¬ (lo ≤ i ∧ i ≤ hi ∧ lo ≤ j ∧ j ≤ hi) → K.d i j = 0) :
    degIndicator K lo hi hK ≫ degIndicator K lo hi hK = degIndicator K lo hi hK := by
  ext n; simp only [comp_f, degIndicator_f]; split_ifs <;> simp

lemma supportedIn_degIndicator (K : ChainComplex V ℤ) (lo hi : ℤ)
    (hK : ∀ i j, ¬ (lo ≤ i ∧ i ≤ hi ∧ lo ≤ j ∧ j ≤ hi) → K.d i j = 0) :
    SupportedIn (degIndicator K lo hi hK) lo hi := fun r hr ↦ by
  rw [degIndicator_f, if_neg (by omega)]

variable {p} (hp : p ≫ p = p)
include hp

/-- `p : D ⟶ (D, p d)`. -/
@[simps]
def toCompress : D ⟶ compressC p where
  f n := p.f n
  comm' i j _ := by rw [compressC_d, idem_f_assoc hp, p.comm]

/-- `p : (D, p d) ⟶ D`. -/
@[simps]
def fromCompress : compressC p ⟶ D where
  f n := p.f n
  comm' i j _ := by simp only [compressC_d, assoc, ← p.comm, idem_f_assoc hp]

@[reassoc (attr := simp)]
lemma p_comp_toCompress : p ≫ toCompress hp = toCompress hp := by ext n; simp [idem_f hp]

@[reassoc (attr := simp)]
lemma fromCompress_comp_p : fromCompress hp ≫ p = fromCompress hp := by ext n; simp [idem_f hp]

@[reassoc (attr := simp)]
lemma toCompress_comp_fromCompress : toCompress hp ≫ fromCompress hp = p := by
  ext n; simp [idem_f hp]

end Compress

/-! ### Contractibility modulo `U` and domination -/

namespace KaroubiFiltration

variable {A : InvCat} (F : KaroubiFiltration A)

/-- The inclusion `U → A` as a duality-preserving functor. -/
abbrev inclI : InvFunctor F.sub.inv A.inv := F.incl

/-- The projection `A → A/U` as a duality-preserving functor. -/
abbrev projI : InvFunctor A.inv F.quot.inv := F.proj

/-- The inclusion `U → A` is fully faithful. -/
def inclI_ff : F.inclI.F.FullyFaithful := F.U.fullyFaithfulι

/-- The Kar complex `(D, p)` of `A` is **contractible modulo `U`** (contractible in `Kar(A/U)`):
`p` is homotopic to a Kar chain map `e = p e p` with components in `I_U`. -/
def ContractibleMod {D : ChainComplex A ℤ} (p : D ⟶ D) : Prop :=
  ∃ e : D ⟶ D, p ≫ e ≫ p = e ∧ (∀ r, FactorsThrough F.U (e.f r)) ∧ Nonempty (Homotopy e p)

variable {F}

/-- A null-homotopy of `[p]` in `A/U` makes `(D, p)` contractible modulo `U`: lift the
null-homotopy `h̄` to `h̃`; then `p - (dh̃ + h̃d)` has components in `I_U`. -/
theorem contractibleMod_of_homotopy {D : ChainComplex A ℤ} {p : D ⟶ D} (hp : p ≫ p = p)
    (H : Homotopy (F.projI.mapH p) 0) : F.ContractibleMod p := by
  let h : ∀ i j, D.X i ⟶ D.X j := fun i j ↦ F.liftQuotHom (H.hom i j)
  have hz : ∀ i j, ¬ (ComplexShape.down ℤ).Rel j i → h i j = 0 :=
    fun i j hij ↦ F.liftQuotHom_zero (H.zero i j hij)
  let e₀ := p - Homotopy.nullHomotopicMap h
  have H₀ : Homotopy e₀ p := (Homotopy.equivSubZero.symm (homotopyCongr
    (Homotopy.nullHomotopy h hz) (sub_sub_cancel _ _).symm rfl)).symm
  have hU : ∀ r, FactorsThrough F.U (e₀.f r) := fun r ↦ by
    have h₁ := homotopy_comm H r (r - 1) (r + 1) (down_rel_pred r) (down_rel_succ r)
    have h₂ := Homotopy.nullHomotopicMap_f (down_rel_succ r) (down_rel_pred r) h
    simp only [Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplex_obj_d,
      zero_f, add_zero] at h₁
    have key : F.proj.F.map (p.f r) = F.proj.F.map ((Homotopy.nullHomotopicMap h).f r) := by
      rw [h₂, Functor.map_add, Functor.map_comp, Functor.map_comp, map_liftQuotHom,
        map_liftQuotHom]
      exact h₁
    simpa [e₀] using (F.proj_map_eq_iff _ _).mp key
  refine ⟨p ≫ e₀ ≫ p, by simp only [assoc, hp, reassoc_of% hp], fun r ↦ ?_,
    ⟨homotopyCongr ((H₀.compRight p).compLeft p) rfl (by simp [hp])⟩⟩
  rw [comp_f, comp_f, ← assoc]
  exact ((hU r).comp_left _).comp_right _

/-- Contractibility modulo `U` is preserved by desuspension. -/
lemma ContractibleMod.desusp {D : ChainComplex A ℤ} {p : D ⟶ D} (h : F.ContractibleMod p) :
    F.ContractibleMod (desuspMap p) := by
  obtain ⟨e, he, hU, ⟨H⟩⟩ := h
  exact ⟨desuspMap e, by rw [← desuspMap_comp, ← desuspMap_comp, he], fun r ↦ hU (r + 1),
    ⟨homotopyCongr (desuspHomotopy H) rfl rfl⟩⟩

variable (F)

/-- A **`U`-domination** of the Kar complex `(D, p)` in degrees `[lo, hi]`: a complex `K` with
objects in `U`, a strict idempotent `q` of `K` concentrated in `[lo, hi]` and Kar maps
`i : (D, p) ⟶ (K, q)`, `r : (K, q) ⟶ (D, p)` with `i r ≃ p`. -/
structure Domination {D : ChainComplex A ℤ} (p : D ⟶ D) (lo hi : ℤ) where
  K : ChainComplex A ℤ
  mem : ∀ n, F.U (K.X n)
  q : K ⟶ K
  q_idem : q ≫ q = q
  support : SupportedIn q lo hi
  i : D ⟶ K
  r : K ⟶ D
  i_kar : p ≫ i ≫ q = i
  r_kar : q ≫ r ≫ p = r
  ir : Homotopy (i ≫ r) p

variable {F}

/-- **Domination** (plan (L1-iv)): a Kar complex concentrated in `[lo, hi]` which is contractible
modulo `U` is `U`-dominated.  With `p ≃ e`, `e ∈ I_U`, a downward cascade of the compressed
complex `(D, p d)` (bounded above by `hi`) gives the `U`-subcomplex `K` absorbing `e`
(`exists_cascade_absorb`); `i = e` (through `K`), `r = ι_K`, so `i r = e ≃ p`. -/
theorem exists_domination {D : ChainComplex A ℤ} {p : D ⟶ D} (hp : p ≫ p = p) {lo hi : ℤ}
    (hs : SupportedIn p lo hi) (hc : F.ContractibleMod p) : Nonempty (F.Domination p lo hi) := by
  obtain ⟨e, he, heU, ⟨H⟩⟩ := hc
  have hpe : p ≫ e = e := kar_left hp he
  let ec : compressC p ⟶ compressC p := fromCompress hp ≫ e ≫ toCompress hp
  have hec : ∀ n, ec.f n = e.f n := fun n ↦ by
    have := congrArg (fun x ↦ x.f n) he
    simp only [HomologicalComplex.comp_f] at this
    exact this
  obtain ⟨c, hc⟩ := F.exists_cascade_absorb hi
    (fun i j h ↦ by simp [hs i (Or.inr h)]) ec (fun r ↦ by rw [hec]; exact heU r)
  have hK : ∀ i j, ¬ (lo ≤ i ∧ i ≤ hi ∧ lo ≤ j ∧ j ≤ hi) → c.ePart.d i j = 0 :=
    fun i j h ↦ by simp [p_f_comp_d_eq_zero hs h]
  let q := degIndicator c.ePart lo hi hK
  have hq : q ≫ q = q := degIndicator_idem _ _ _ _
  have hfq : c.factor ec hc ≫ q = c.factor ec hc := by
    ext n
    simp only [comp_f, degIndicator_f, q]
    split_ifs with h
    · rw [comp_id]
    · rw [comp_zero, Cascade.factor_f, hec, ← hpe, comp_f, hs n (by omega), zero_comp,
        zero_comp]
  have hir : (toCompress hp ≫ c.factor ec hc) ≫ q ≫ c.ι ≫ fromCompress hp = e := by
    simp only [assoc]
    rw [reassoc_of% hfq, Cascade.factor_ι_assoc]
    simp [ec, he]
  exact ⟨{ K := c.ePart
           mem := c.ePart_mem
           q := q
           q_idem := hq
           support := supportedIn_degIndicator _ _ _ _
           i := toCompress hp ≫ c.factor ec hc
           r := q ≫ c.ι ≫ fromCompress hp
           i_kar := by rw [assoc, hfq, p_comp_toCompress_assoc]
           r_kar := by simp only [assoc, fromCompress_comp_p, reassoc_of% hq]
           ir := (Homotopy.ofEq hir).trans H }⟩

/-- **Domination of an honest bounded complex** (plan (L1-iv)): if `D` vanishes outside
`[lo, hi]` and its identity is null-homotopic in `A/U`, there are a complex `K` of `U`-objects
(with an idempotent concentrated in `[lo, hi]`) and chain maps `D ⟶ K ⟶ D` composing to a map
homotopic to `𝟙`. -/
theorem exists_domination_of_isZero {D : ChainComplex A ℤ} {lo hi : ℤ}
    (hD : ∀ r, r < lo ∨ hi < r → IsZero (D.X r)) (H : Homotopy (𝟙 (F.projI.mapC D)) 0) :
    Nonempty (F.Domination (𝟙 D) lo hi) :=
  exists_domination (by simp) (fun r hr ↦ (hD r hr).eq_of_src _ _)
    (contractibleMod_of_homotopy (by simp)
      (homotopyCongr H ((F.projI.F.mapHomologicalComplex _).map_id D).symm rfl))

/-! ### The Kar(U) model -/

/-- A complex with objects in `U` as a complex of `U`. -/
@[simps, implicit_reducible]
def liftSubC (K : ChainComplex A ℤ) (h : ∀ n, F.U (K.X n)) : ChainComplex F.sub ℤ where
  X n := ⟨K.X n, h n⟩
  d i j := ObjectProperty.homMk (K.d i j)
  shape i j hij := F.U.fullyFaithfulι.map_injective (by
    rw [Functor.map_zero]; simp [K.shape i j hij])
  d_comp_d' i j k _ _ := F.U.fullyFaithfulι.map_injective (by
    rw [Functor.map_zero, Functor.map_comp]; simp)

variable (F) in
/-- A **Kar(U) model** of the Kar complex `(D, p)`: a complex `X` of `U` with a strict idempotent
`e` concentrated in `[lo, hi]`, and a Kar homotopy equivalence `(D, p) ≃ (X, e)` in `A`. -/
structure SubModel {D : ChainComplex A ℤ} (p : D ⟶ D) (lo hi : ℤ) where
  X : ChainComplex F.sub ℤ
  e : X ⟶ X
  e_idem : e ≫ e = e
  support : SupportedIn e lo hi
  equiv : KarHtpyEquiv p (F.inclI.mapH e)

/-- **Kar(U) model** (plan (L1-v)): BS01 in `F.sub` (`KarSplitting.exists_splitting`) splits the
homotopy idempotent `r i` of the dominating complex `(K, q)` through a Kar complex `(X, e)` of
`U` with `e` strict; then `(D, p) ≃ (X, e)` via `i ρ`, `ι r`. -/
theorem Domination.nonempty_subModel {D : ChainComplex A ℤ} {p : D ⟶ D} (hp : p ≫ p = p)
    {lo hi : ℤ} (dom : F.Domination p lo hi) : Nonempty (F.SubModel p lo hi) := by
  have hΦ := F.inclI_ff
  let K' := liftSubC dom.K dom.mem
  let q' : K' ⟶ K' := FFLift.preimH hΦ dom.q
  let E' : K' ⟶ K' := FFLift.preimH hΦ (dom.r ≫ dom.i)
  have hpi : p ≫ dom.i = dom.i := kar_left hp dom.i_kar
  have hiq : dom.i ≫ dom.q = dom.i := kar_right dom.q_idem dom.i_kar
  have hqr : dom.q ≫ dom.r = dom.r := kar_left dom.q_idem dom.r_kar
  have hrp : dom.r ≫ p = dom.r := kar_right hp dom.r_kar
  have hq' : q' ≫ q' = q' := FFLift.mapH_injective hΦ (by simp [q', dom.q_idem])
  have hE' : q' ≫ E' ≫ q' = E' := FFLift.mapH_injective hΦ (by
    simp only [Functor.map_comp, FFLift.map_preimH, q', E', assoc, hiq, reassoc_of% hqr])
  have idem' : Homotopy (E' ≫ E') E' := FFLift.preimHomotopy hΦ (homotopyCongr
    ((Homotopy.refl dom.r).comp (dom.ir.comp (Homotopy.refl dom.i)))
    (by simp [E']) (by simp [E', reassoc_of% hrp]))
  have hs' : SupportedIn q' lo hi := fun r hr ↦ hΦ.map_injective (by
    rw [Functor.map_zero]; exact (hΦ.map_preimage (X := K'.X r) (Y := K'.X r) (dom.q.f r)).trans
      (dom.support r hr))
  obtain ⟨S, hS⟩ := KarSplitting.exists_splitting hq' hE' idem' hs'
  have hmE : F.inclI.mapH E' = dom.r ≫ dom.i := FFLift.map_preimH hΦ _
  let T : Homotopy (S.ι ≫ E' ≫ S.r) S.e :=
    ((Homotopy.refl S.ι).comp (S.rι.symm.comp (Homotopy.refl S.r))).trans
      (homotopyCongr (S.ιr.comp S.ιr) (by simp) S.e_idem)
  exact ⟨{ X := S.D
           e := S.e
           e_idem := S.e_idem
           support := hS
           equiv :=
            { f := dom.i ≫ F.inclI.mapH S.r
              g := F.inclI.mapH S.ι ≫ dom.r
              pf := by rw [reassoc_of% hpi]
              fp := by rw [assoc, ← Functor.map_comp, S.r_e]
              pg := by rw [← assoc, ← Functor.map_comp, S.e_ι]
              gp := by rw [assoc, hrp]
              fg := homotopyCongr (((Homotopy.refl dom.i).comp
                  ((F.inclI.F.mapHomotopy S.rι).comp (Homotopy.refl dom.r))).trans
                  (homotopyCongr (dom.ir.comp dom.ir) (by simp [hmE]) hp))
                (by simp) rfl
              gf := homotopyCongr (F.inclI.F.mapHomotopy T) (by simp [hmE]) rfl } }⟩

/-- **Kar(U) model** of a Kar complex contractible modulo `U` (plan (L1-iv)+(L1-v)). -/
theorem exists_subModel {D : ChainComplex A ℤ} {p : D ⟶ D} (hp : p ≫ p = p) {lo hi : ℤ}
    (hs : SupportedIn p lo hi) (hc : F.ContractibleMod p) : Nonempty (F.SubModel p lo hi) :=
  (exists_domination hp hs hc).elim fun dom ↦ dom.nonempty_subModel hp

/-! ### The symmetric version -/

variable {N : ℤ}

/-- **Transport to Kar(U)**: a Poincaré complex `P` of `A` which is contractible modulo `U` is
homotopy isometric to the image of a Poincaré complex `Q` of `U`.  `Q` is the transport of `P`
along its Kar(U) model (`SymPoincare.transport`), pulled back along the fully faithful
inclusion (`FFLift.preimPoincare`). -/
theorem _root_.HSFormal.LTheory.SymPoincare.exists_sub (P : SymPoincare A.inv N)
    (hc : F.ContractibleMod P.p) :
    ∃ Q : SymPoincare F.sub.inv N, Nonempty (SymPoincare.HomotopyIsometry P (Q.map F.inclI)) := by
  obtain ⟨M⟩ := KaroubiFiltration.exists_subModel P.p_idem P.support hc
  have hp' : F.inclI.mapH M.e ≫ F.inclI.mapH M.e = F.inclI.mapH M.e := by
    rw [← Functor.map_comp, M.e_idem]
  have hs' : SupportedIn (F.inclI.mapH M.e) 0 N := fun r hr ↦ by
    change F.inclI.F.map (M.e.f r) = 0
    rw [M.support r hr, Functor.map_zero]
  let P' := P.transport hp' hs' M.equiv
  refine ⟨FFLift.preimPoincare F.inclI F.inclI_ff M.e P'.φ M.e_idem M.support P'.φ_kar P'.symm
    P'.poincare, ⟨(P.transportIsometry hp' hs' M.equiv).trans
      (SymPoincare.HomotopyIsometry.ofIso (Iso.refl _)
        ((Category.id_comp _).trans (Category.comp_id _).symm) ?_)⟩⟩
  rw [FFLift.map_preimPoincare_φ]
  simp [P']
  erw [dualHom_id, Category.id_comp, Category.comp_id]

/-! ### Boundaries: cones of equivalences modulo `U` -/

/-- **The cone of an equivalence modulo `U` is contractible modulo `U`.**  If the Kar map
`j : (B, p_B) ⟶ (D, p_D)` becomes a Kar homotopy equivalence in `A/U`, then
`Σ⁻¹Cone(j)` (with idempotent `Σ⁻¹(p_B ⊕ p_D)`) is contractible modulo `U`: in `Kar(A/U)` the
five lemma (`isKarEquiv_coneMap`) compares `Cone(j)` with the contractible `Cone(p_D)`. -/
theorem contractibleMod_desusp_cone {B D : ChainComplex A ℤ} {j : B ⟶ D} {pB : B ⟶ B}
    {pD : D ⟶ D} (hB : pB ≫ pB = pB) (hD : pD ≫ pD = pD) (hj : pB ≫ j ≫ pD = j)
    (h : IsKarEquiv (F.projI.mapH pB) (F.projI.mapH pD) (F.projI.mapH j)) :
    F.ContractibleMod (desuspMap (coneMap pB pD (comm_of_kar hB hD hj))) := by
  have hB' : F.projI.mapH pB ≫ F.projI.mapH pB = F.projI.mapH pB := by
    rw [← Functor.map_comp, hB]
  have hD' : F.projI.mapH pD ≫ F.projI.mapH pD = F.projI.mapH pD := by
    rw [← Functor.map_comp, hD]
  have hj' : F.projI.mapH pB ≫ F.projI.mapH j ≫ F.projI.mapH pD = F.projI.mapH j := by
    rw [← Functor.map_comp, ← Functor.map_comp, hj]
  have hDD : F.projI.mapH pD ≫ F.projI.mapH pD ≫ F.projI.mapH pD = F.projI.mapH pD := by
    rw [hD', hD']
  have en : IsKarEquiv (F.projI.mapH pD) (F.projI.mapH pD) (F.projI.mapH pD) :=
    ⟨F.projI.mapH pD, hDD, ⟨Homotopy.ofEq hD'⟩, ⟨Homotopy.ofEq hD'⟩⟩
  have K := isKarEquiv_coneMap hB' hD' hD' hD' hj' hDD hj' hDD rfl h en
  obtain ⟨H⟩ := homotopy_zero_of_isKarEquiv K (coneIdHomotopy hD' _)
  have hc := coneMap_comp_mapConeInv F.proj.F (j := j) (j' := j) (m := pB) (n := pD)
    (comm_of_kar hB hD hj)
  have H' : Homotopy (F.projI.mapH (coneMap pB pD (comm_of_kar hB hD hj))) 0 :=
    homotopyZeroOfIso (mapConeInv F.proj.F j) hc H
  exact (contractibleMod_of_homotopy (coneMap_idem (comm_of_kar hB hD hj) hB hD) H').desusp

/-- `φ : C^{N+1-*} ⟶ C` Poincaré in `Kar(A/U)` as a Kar equivalence of images. -/
lemma isKarEquiv_mapH_of_isPoincare {C : ChainComplex A ℤ} {p : C ⟶ C}
    {φ : dualComplex A.inv N C ⟶ C}
    (h : IsPoincare F.quot.inv N (F.projI.mapH p) (F.projI.mapDual φ)) :
    IsKarEquiv (F.projI.mapH (dualHom A.inv N p)) (F.projI.mapH p) (F.projI.mapH φ) := by
  have h' := (isPoincare_iff.mp h).conjIso (F.projI.mapDualIso N C).symm
  have e₁ : (F.projI.mapDualIso N C).symm.inv ≫ dualHom F.quot.inv N (F.projI.mapH p) ≫
      (F.projI.mapDualIso N C).symm.hom = F.projI.mapH (dualHom A.inv N p) := by
    rw [F.projI.dualHom_mapH]; simp
  have e₂ : (F.projI.mapDualIso N C).symm.inv ≫ F.projI.mapDual φ = F.projI.mapH φ := by
    rw [F.projI.mapDual_eq]; simp
  rwa [e₁, e₂] at h'

/-- **The boundary `∂C = Σ⁻¹Cone(φ)` is contractible modulo `U`** if `φ : (C^{N+1-*}, p^*) ⟶
(C, p)` is Poincaré in `Kar(A/U)` (plan (L1-iii)); the idempotent is `SymComplex.bdP`. -/
theorem contractibleMod_bd {C : ChainComplex A ℤ} {p : C ⟶ C} (hp : p ≫ p = p)
    {φ : dualComplex A.inv (N + 1) C ⟶ C} (hφ : dualHom A.inv (N + 1) p ≫ φ ≫ p = φ)
    (hc : dualHom A.inv (N + 1) p ≫ φ = φ ≫ p)
    (h : IsPoincare F.quot.inv (N + 1) (F.projI.mapH p) (F.projI.mapDual φ)) :
    F.ContractibleMod (desuspMap (coneMap (dualHom A.inv (N + 1) p) p hc)) :=
  contractibleMod_desusp_cone (dualHom_idem hp) hp hφ (isKarEquiv_mapH_of_isPoincare h)

/-- **The boundary of the lifting pair lies in `Kar(U)`** (plan §3 (L1-iii)–(L1-v): "domination
plus BS01 puts the boundary in Kar(U)").  Let `(C, p, φ)` be an `(N+1)`-dimensional strictly
symmetric complex of `A` (`p` in `[1, N+1]`) whose `φ` is Poincaré in `Kar(A/U)`.  Then its
boundary `∂C = Σ⁻¹Cone(φ)` (`SymComplex.boundary`) is homotopy isometric to the image of an
`N`-dimensional Poincaré complex of `U`. -/
theorem _root_.HSFormal.LTheory.SymComplex.exists_sub_boundary (X : SymComplex A.inv (N + 1))
    (h : SupportedIn X.p 1 (N + 1))
    (hX : IsPoincare F.quot.inv (N + 1) (F.projI.mapH X.p) (F.projI.mapDual X.φ)) :
    ∃ Q : SymPoincare F.sub.inv N,
      Nonempty (SymPoincare.HomotopyIsometry (X.boundary h) (Q.map F.inclI)) :=
  SymPoincare.exists_sub _ (KaroubiFiltration.contractibleMod_bd X.p_idem X.φ_kar X.comm hX)

end KaroubiFiltration

end

end HSFormal.LTheory
