import HSFormal.LTheory.Interface
import HSFormal.GraphCornerChain
import HSFormal.BalmerSchlichting

/-!
# The corner class of a homotopy action (manuscript §5, Lemmas 5.1 and 5.2)

Karoubi-model version of the graph corner, over a preadditive category `V` with a strict
involution.  The normalizing scalar is a `CentralUnit` `q` (a central self-adjoint automorphism of
`V`): in the application it is multiplication by the sequence `(|G_i|)_i`; `CentralUnit.ofRat`
is a rational scalar.

* `KarSplitting p E`: a splitting (5.4) `(D, e) →ι (C, p) →r (D, e)`, `ιr ≃ 1 = e`, `rι ≃ E`, of
  a homotopy idempotent `E` of a Kar complex, with `e` a *strict* idempotent.
  `KarSplitting.exists_splitting`: Balmer–Schlichting strictification
  (`strictifiable_of_support`) followed by the truncation of l. 322 (blueprint N6) gives one with
  `(D, e)` in the degrees of `p`.  In the Karoubi model the truncation only changes the idempotent
  in the two boundary degrees (`truncBelow`, `truncAbove`); no boundedness of `C` is needed.
  `bs01` proves the interface hypothesis `BS01`.
* `HomotopyProjector W`: the hypotheses of Lemma 5.1 on a Poincaré complex `W = (𝒞, Π, Φ)`.
  `HomotopySplitting.corner q`: the normalized corner (5.5), `r^* Φ q⁻¹ r`, which is the corner
  `rawCorner` of the rescaled complex `W.scale q⁻¹`.  It is strictly symmetric because
  conjugation commutes with `T`, and Kar because `r = r e`; the strictified idempotent needs no
  compatibility with the duality.  It is Poincaré with inverse `ι q Ψ ι^*` (from `ΦE ≃ E^*Φ`),
  independent of the splitting (`cornerIsometry`), natural (`corner_map`) and invariant under
  strict isometries (`corner_transport`).
* `RowColumn π P q`: the data of Lemma 5.2, (5.6)–(5.7) — a row `u` and column `v` with
  `uv ≃ 1`, `vu ≃ E`, `uE ≃ u`, `uΦu^* ≃ qφ` — and `RowColumn.lemma_5_2`: every normalized corner
  is homotopy isometric to `P` via `w = uι`, `z = rv` (5.8).
* `KarAction G P`: a homotopy action of a fixed finite group (manuscript (5.1)) in the Karoubi
  model; `KarAction.rowColumn` instantiates the above on `graphPoincare G P = (⨁_G C, p ⊗ 1, φ ⊗ 1)`
  with the graph idempotent (5.2) and `q = |G|`, giving `KarAction.cornerClass ≃ P`.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive Opposite HomologicalComplex HSFormal.Compression

noncomputable section

local notation "𝐊" => HomotopyCategory.quotient _ (ComplexShape.down ℤ)

/-! ### The corner algebra in an abstract category with duality -/

namespace CornerAlgebra

open GraphCorner

variable {𝒦 : Type*} [Category 𝒦] {𝔻 : 𝒦ᵒᵖ ⥤ 𝒦}
  {C D X : 𝒦} {Φ : 𝔻.obj (op C) ⟶ C} {E : C ⟶ C} {e : D ⟶ D} {ι : D ⟶ C} {r : C ⟶ D}

/-- Lemma 5.1: `b_D φ_D = 1` for a splitting `ιr = e`, `rι = E` with `ι` landing in the image of
`π = ΨΦ`. -/
theorem inv_comp_form {Ψ : C ⟶ 𝔻.obj (op C)} {π : C ⟶ C} (hΨ : Ψ ≫ Φ = π)
    (hΦ : Φ ≫ E = dualMap 𝔻 E ≫ Φ) (hιπ : ι ≫ π = ι) (hrι : r ≫ ι = E) (hιr : ι ≫ r = e)
    (he : e ≫ e = e) :
    (ι ≫ Ψ ≫ dualMap 𝔻 ι) ≫ (dualMap 𝔻 r ≫ Φ ≫ r) = e := by
  calc (ι ≫ Ψ ≫ dualMap 𝔻 ι) ≫ dualMap 𝔻 r ≫ Φ ≫ r
      = ι ≫ Ψ ≫ (dualMap 𝔻 (r ≫ ι) ≫ Φ) ≫ r := by simp
    _ = (ι ≫ (Ψ ≫ Φ)) ≫ (r ≫ ι) ≫ r := by rw [hrι, ← hΦ]; simp
    _ = e := by
      rw [hΨ, hιπ]
      simp only [assoc]
      rw [reassoc_of% hιr, hιr, he]

/-- Lemma 5.1: `φ_D b_D = 1`. -/
theorem form_comp_inv {Ψ : C ⟶ 𝔻.obj (op C)} {π : C ⟶ C} (hΨ : Φ ≫ Ψ = dualMap 𝔻 π)
    (hΦ : Φ ≫ E = dualMap 𝔻 E ≫ Φ) (hιπ : ι ≫ π = ι) (hrι : r ≫ ι = E) (hιr : ι ≫ r = e)
    (he : e ≫ e = e) :
    (dualMap 𝔻 r ≫ Φ ≫ r) ≫ (ι ≫ Ψ ≫ dualMap 𝔻 ι) = dualMap 𝔻 e := by
  calc (dualMap 𝔻 r ≫ Φ ≫ r) ≫ ι ≫ Ψ ≫ dualMap 𝔻 ι
      = dualMap 𝔻 r ≫ (Φ ≫ (r ≫ ι)) ≫ Ψ ≫ dualMap 𝔻 ι := by simp
    _ = dualMap 𝔻 r ≫ dualMap 𝔻 E ≫ (Φ ≫ Ψ) ≫ dualMap 𝔻 ι := by rw [hrι, hΦ]; simp
    _ = dualMap 𝔻 (ι ≫ π ≫ E ≫ r) := by rw [hΨ]; simp
    _ = dualMap 𝔻 e := by
      rw [← assoc, hιπ, ← hrι]
      simp only [assoc]
      rw [reassoc_of% hιr, hιr, he]

/-- Lemma 5.1, independence of the splitting: `r'ι` conjugates the corners. -/
theorem form_conj_splitting {D' : 𝒦} {ι' : D' ⟶ C} {r' : C ⟶ D'} {e' : D' ⟶ D'}
    (hrι : r ≫ ι = E) (hrι' : r' ≫ ι' = E) (hιr' : ι' ≫ r' = e') (hr' : r' ≫ e' = r') :
    dualMap 𝔻 (ι ≫ r') ≫ (dualMap 𝔻 r ≫ Φ ≫ r) ≫ (ι ≫ r') = dualMap 𝔻 r' ≫ Φ ≫ r' := by
  have h : r ≫ ι ≫ r' = r' := by rw [← assoc, hrι, ← hrι', assoc, hιr', hr']
  have h' : dualMap 𝔻 r' ≫ dualMap 𝔻 ι ≫ dualMap 𝔻 r = dualMap 𝔻 r' := by
    rw [← dualMap_comp, ← dualMap_comp, assoc, h]
  simp only [dualMap_comp, assoc, h, reassoc_of% h']

/-- Lemma 5.2, (5.8): `w φ_D w^* = uΦu^* = φ` for `w = uι`. -/
theorem form_conj_row {u : C ⟶ X} {φ : 𝔻.obj (op X) ⟶ X} (hrι : r ≫ ι = E) (hu : E ≫ u = u)
    (hΦu : dualMap 𝔻 u ≫ Φ ≫ u = φ) :
    dualMap 𝔻 (ι ≫ u) ≫ (dualMap 𝔻 r ≫ Φ ≫ r) ≫ (ι ≫ u) = φ := by
  have h : r ≫ ι ≫ u = u := by rw [← assoc, hrι, hu]
  have h' : dualMap 𝔻 u ≫ dualMap 𝔻 ι ≫ dualMap 𝔻 r = dualMap 𝔻 u := by
    rw [← dualMap_comp, ← dualMap_comp, assoc, h]
  simp only [dualMap_comp, assoc, h, reassoc_of% h', hΦu]

end CornerAlgebra

/-! ### Chain-level lemmas -/

variable {V : Type*} [Category V] [Preadditive V] {J : StrictInvolution V} {N : ℤ}

lemma kmap_dualHom {C D : ChainComplex V ℤ} (f : C ⟶ D) :
    𝐊.map (dualHom J N f) = GraphCorner.dualMap (GraphCorner.homotopyDual J N) (𝐊.map f) := rfl

@[reassoc]
lemma dualHom_comp_dualHom {C D E : ChainComplex V ℤ} (f : C ⟶ D) (g : D ⟶ E) :
    dualHom J N g ≫ dualHom J N f = dualHom J N (f ≫ g) :=
  (dualHom_comp J N f g).symm

lemma dualHom_sum {C D : ChainComplex V ℤ} {ι : Type*} (s : Finset ι) (f : ι → (C ⟶ D)) :
    dualHom J N (∑ i ∈ s, f i) = ∑ i ∈ s, dualHom J N (f i) :=
  map_sum (AddMonoidHom.mk' (dualHom J N) (dualHom_add J N)) f s

lemma transposeHom_sum {C D : ChainComplex V ℤ} {ι : Type*} (s : Finset ι)
    (φ : ι → (dualComplex J N C ⟶ D)) :
    transposeHom J N (∑ i ∈ s, φ i) = ∑ i ∈ s, transposeHom J N (φ i) :=
  map_sum (AddMonoidHom.mk' (transposeHom J N) transposeHom_add) φ s

lemma IsStrictSymm.sum {C : ChainComplex V ℤ} {ι : Type*} (s : Finset ι)
    {φ : ι → (dualComplex J N C ⟶ C)} (h : ∀ i ∈ s, IsStrictSymm J N (φ i)) :
    IsStrictSymm J N (∑ i ∈ s, φ i) := by
  rw [IsStrictSymm, transposeHom_sum]
  exact Finset.sum_congr rfl h

lemma SupportedIn.map {C : ChainComplex V ℤ} {p : C ⟶ C} {lo hi : ℤ} (h : SupportedIn p lo hi)
    {V' : Type*} [Category V'] [Preadditive V'] {J' : StrictInvolution V'}
    (Φ : InvFunctor J J') : SupportedIn (Φ.mapH p) lo hi :=
  fun r hr ↦ by simp [h r hr]

/-! ### Central units -/

variable (J) in
/-- A central self-adjoint automorphism `q` of `V`: `q f = f q` for every morphism `f`, and
`q^* = q`.  In the application `q` is multiplication by the sequence `(|G_i|)_i` (l. 396). -/
structure CentralUnit where
  hom : ∀ X : V, X ⟶ X
  inv : ∀ X : V, X ⟶ X
  hom_inv : ∀ X, hom X ≫ inv X = 𝟙 X
  inv_hom : ∀ X, inv X ≫ hom X = 𝟙 X
  comm : ∀ {X Y : V} (f : X ⟶ Y), hom X ≫ f = f ≫ hom Y
  star_hom : ∀ X, J.star (hom X) = hom X

namespace CentralUnit

variable (q : CentralUnit J)

attribute [reassoc (attr := simp)] hom_inv inv_hom

lemma inv_comm {X Y : V} (f : X ⟶ Y) : q.inv X ≫ f = f ≫ q.inv Y :=
  calc q.inv X ≫ f = q.inv X ≫ (f ≫ q.hom Y) ≫ q.inv Y := by simp
    _ = f ≫ q.inv Y := by rw [← q.comm, assoc, q.inv_hom_assoc]

lemma star_inv (X : V) : J.star (q.inv X) = q.inv X :=
  calc J.star (q.inv X) = J.star (q.inv X) ≫ q.hom X ≫ q.inv X := by simp
    _ = q.inv X := by rw [← q.star_hom X, ← assoc, ← J.star_comp, q.hom_inv, J.star_id,
        id_comp]

/-- The inverse central unit. -/
@[simps]
def symm : CentralUnit J where
  hom := q.inv
  inv := q.hom
  hom_inv := q.inv_hom
  inv_hom := q.hom_inv
  comm := q.inv_comm
  star_hom := q.star_inv

/-- Multiplication by a nonzero rational. -/
@[simps]
def ofRat [Linear ℚ V] (c : ℚ) (hc : c ≠ 0) : CentralUnit J where
  hom X := c • 𝟙 X
  inv X := c⁻¹ • 𝟙 X
  hom_inv X := by rw [Linear.smul_comp, id_comp, smul_smul, mul_inv_cancel₀ hc, one_smul]
  inv_hom X := by rw [Linear.smul_comp, id_comp, smul_smul, inv_mul_cancel₀ hc, one_smul]
  comm f := by simp
  star_hom X := by rw [star_rat_smul, J.star_id]

/-- `q` on a chain complex. -/
@[simps]
def chain (C : ChainComplex V ℤ) : C ⟶ C where
  f r := q.hom (C.X r)
  comm' _ _ _ := q.comm _

@[reassoc]
lemma chain_comp {C D : ChainComplex V ℤ} (f : C ⟶ D) : q.chain C ≫ f = f ≫ q.chain D := by
  ext; simp [q.comm]

@[reassoc (attr := simp)]
lemma chain_symm_chain (C : ChainComplex V ℤ) : q.chain C ≫ q.symm.chain C = 𝟙 C := by
  ext; simp

@[reassoc (attr := simp)]
lemma symm_chain_chain (C : ChainComplex V ℤ) : q.symm.chain C ≫ q.chain C = 𝟙 C := by
  ext; simp

@[simp]
lemma dualHom_chain (C : ChainComplex V ℤ) : dualHom J N (q.chain C) = q.chain _ := by
  ext; simp [q.star_hom]

lemma ofRat_chain [Linear ℚ V] (c : ℚ) (hc : c ≠ 0) (C : ChainComplex V ℤ) :
    (ofRat (J := J) c hc).chain C = c • 𝟙 C := by
  ext; simp

end CentralUnit

/-- The rescaled Poincaré complex `(C, p, φ q)`. -/
@[simps, reducible]
def SymPoincare.scale (W : SymPoincare J N) (q : CentralUnit J) : SymPoincare J N where
  C := W.C
  p := W.p
  p_idem := W.p_idem
  support := W.support
  φ := W.φ ≫ q.chain W.C
  φ_kar := by rw [assoc, q.chain_comp]; simp
  symm := by
    have h := transposeHom_comp (𝟙 W.C) W.φ (q.chain W.C)
    rw [dualHom_id, id_comp, comp_id] at h
    rw [IsStrictSymm, h, W.transposeHom_φ, q.dualHom_chain, q.chain_comp]
  poincare := by
    obtain ⟨ψ, hψ, ⟨H₁⟩, ⟨H₂⟩⟩ := W.poincare
    refine ⟨q.symm.chain W.C ≫ ψ, ?_, ⟨homotopyCongr ((H₁.compLeft (q.symm.chain W.C)).compRight
      (q.chain W.C)) (by simp) (by rw [q.symm.chain_comp]; simp)⟩,
      ⟨homotopyCongr H₂ (by simp) rfl⟩⟩
    rw [assoc, ← q.symm.chain_comp_assoc, hψ]

/-! ### Splittings of homotopy idempotents in the Karoubi model -/

/-- Manuscript (5.4): a splitting `(D, e) →ι (C, p) →r (D, e)` in `K(Kar V)` of a homotopy
idempotent `E` of the Kar complex `(C, p)`, by a Kar complex with a strict idempotent `e`:
`ιr ≃ 1_{(D, e)} = e` and `rι ≃ E`. -/
structure KarSplitting {C : ChainComplex V ℤ} (p E : C ⟶ C) where
  D : ChainComplex V ℤ
  e : D ⟶ D
  e_idem : e ≫ e = e
  ι : D ⟶ C
  r : C ⟶ D
  e_ι : e ≫ ι = ι
  ι_p : ι ≫ p = ι
  p_r : p ≫ r = r
  r_e : r ≫ e = r
  /-- `ιr ≃ 1`. -/
  ιr : Homotopy (ι ≫ r) e
  /-- `rι ≃ E`. -/
  rι : Homotopy (r ≫ ι) E

namespace KarSplitting

attribute [reassoc (attr := simp)] e_idem e_ι ι_p p_r r_e

variable {C : ChainComplex V ℤ} {p E : C ⟶ C} (S : KarSplitting p E)

lemma kmap_rι : 𝐊.map S.r ≫ 𝐊.map S.ι = 𝐊.map E := by
  rw [← Functor.map_comp]; exact HomotopyCategory.eq_of_homotopy _ _ S.rι

lemma kmap_ιr : 𝐊.map S.ι ≫ 𝐊.map S.r = 𝐊.map S.e := by
  rw [← Functor.map_comp]; exact HomotopyCategory.eq_of_homotopy _ _ S.ιr

lemma kmap_e_idem : 𝐊.map S.e ≫ 𝐊.map S.e = 𝐊.map S.e := by
  rw [← Functor.map_comp, S.e_idem]

/-- Restriction to a smaller idempotent `e' ≤ e` homotopic to `e`. -/
@[simps]
def restrict (e' : S.D ⟶ S.D) (h₁ : e' ≫ e' = e') (h₃ : e' ≫ S.e = e')
    (T : Homotopy S.e e') : KarSplitting p E where
  D := S.D
  e := e'
  e_idem := h₁
  ι := e' ≫ S.ι
  r := S.r ≫ e'
  e_ι := by rw [reassoc_of% h₁]
  ι_p := by simp
  p_r := by simp
  r_e := by rw [assoc, h₁]
  ιr := homotopyCongr ((S.ιr.compRight e').compLeft e') (by simp) (by rw [reassoc_of% h₃, h₁])
  rι := (homotopyCongr ((T.symm.compRight S.ι).compLeft S.r) (by simp [reassoc_of% h₁])
    (by simp)).trans S.rι

/-- The image under a duality-preserving functor. -/
@[simps]
def map {V' : Type*} [Category V'] [Preadditive V'] {J' : StrictInvolution V'}
    (Φ : InvFunctor J J') : KarSplitting (Φ.mapH p) (Φ.mapH E) where
  D := Φ.mapC S.D
  e := Φ.mapH S.e
  e_idem := by rw [← Functor.map_comp, S.e_idem]
  ι := Φ.mapH S.ι
  r := Φ.mapH S.r
  e_ι := by rw [← Functor.map_comp, S.e_ι]
  ι_p := by rw [← Functor.map_comp, S.ι_p]
  p_r := by rw [← Functor.map_comp, S.p_r]
  r_e := by rw [← Functor.map_comp, S.r_e]
  ιr := homotopyCongr (Φ.F.mapHomotopy S.ιr) (Functor.map_comp _ _ _) rfl
  rι := homotopyCongr (Φ.F.mapHomotopy S.rι) (Functor.map_comp _ _ _) rfl

/-- Transport along an isomorphism `θ : (C, p) ≅ (C', p')` conjugating `E` to `E'`. -/
@[simps]
def transport {C' : ChainComplex V ℤ} {p' E' : C' ⟶ C'} (θ : C ≅ C')
    (hp : θ.hom ≫ p' = p ≫ θ.hom) (hE : E' = θ.inv ≫ E ≫ θ.hom) : KarSplitting p' E' where
  D := S.D
  e := S.e
  e_idem := S.e_idem
  ι := S.ι ≫ θ.hom
  r := θ.inv ≫ S.r
  e_ι := by simp
  ι_p := by rw [assoc, hp, S.ι_p_assoc]
  p_r := by
    have : p' ≫ θ.inv = θ.inv ≫ p := by
      rw [← cancel_epi θ.hom, θ.hom_inv_id_assoc, reassoc_of% hp, θ.hom_inv_id, comp_id]
    rw [reassoc_of% this, S.p_r]
  r_e := by simp
  ιr := homotopyCongr S.ιr (by simp) rfl
  rι := homotopyCongr ((S.rι.compLeft θ.inv).compRight θ.hom) (by simp) (by rw [hE, assoc])

end KarSplitting

/-! ### Truncation (manuscript l. 322, blueprint N6) -/

section Truncation

open HomotopyIdempotent

variable {D : ChainComplex V ℤ} {e g : D ⟶ D} (H : Homotopy e g) (s : ℤ → Prop) [DecidablePred s]

/-- The homotopy `H` in the degrees `i` with `s i`. -/
def truncHom (i j : ℤ) : D.X i ⟶ D.X j := if s i then H.hom i j else 0

/-- `e - (dK + Kd)` for `K` the part of `H` in the degrees `s`. -/
def truncIdem : D ⟶ D := e - Homotopy.nullHomotopicMap (truncHom H s)

/-- `e ≃ truncIdem H s`. -/
def truncHomotopy : Homotopy e (truncIdem H s) :=
  Homotopy.equivSubZero.symm (homotopyCongr (Homotopy.nullHomotopy (truncHom H s)
    fun i j hij ↦ by rw [truncHom, H.zero i j hij, ite_self]) (sub_sub_cancel _ _).symm rfl)

lemma truncNull_f_succ (m : ℤ) :
    (Homotopy.nullHomotopicMap (truncHom H s)).f (m + 1) =
      (if s m then D.d (m + 1) m ≫ H.hom m (m + 1) else 0) +
        (if s (m + 1) then H.hom (m + 1) (m + 1 + 1) ≫ D.d (m + 1 + 1) (m + 1) else 0) := by
  rw [nullHomotopicMap_f_succ]
  simp only [truncHom]
  split_ifs <;> simp

variable {H s}

lemma truncNull_f_succ_of_both {m : ℤ} (h₁ : s m) (h₂ : s (m + 1)) (hg : g.f (m + 1) = 0) :
    (Homotopy.nullHomotopicMap (truncHom H s)).f (m + 1) = e.f (m + 1) := by
  rw [truncNull_f_succ, ite_eq_left h₁, ite_eq_left h₂, comm_succ H m, hg, add_zero]

lemma truncNull_f_succ_of_neither {m : ℤ} (h₁ : ¬s m) (h₂ : ¬s (m + 1)) :
    (Homotopy.nullHomotopicMap (truncHom H s)).f (m + 1) = 0 := by
  rw [truncNull_f_succ, ite_eq_right h₁, ite_eq_right h₂, add_zero]

variable (he : e ≫ e = e) (hl : ∀ i j, e.f i ≫ H.hom i j = H.hom i j)
  (hr : ∀ i j, H.hom i j ≫ e.f j = H.hom i j)
include he

lemma truncIdem_comp (hr : ∀ i j, H.hom i j ≫ e.f j = H.hom i j) :
    truncIdem H s ≫ e = truncIdem H s := by
  rw [truncIdem, sub_comp, he, Homotopy.nullHomotopicMap_comp]
  congr 3
  funext i j
  simp only [truncHom]
  split_ifs <;> simp [hr]

include hl hr

/-- Truncation below `lo` is idempotent if `g` vanishes below `lo`. -/
lemma truncIdem_lower_idem {lo : ℤ} (hg : ∀ k < lo, g.f k = 0) :
    truncIdem H (· < lo) ≫ truncIdem H (· < lo) = truncIdem H (· < lo) := by
  have he' : ∀ k, e.f k ≫ e.f k = e.f k := fun k ↦ by rw [← comp_f, he]
  ext k
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by ring⟩
  simp only [truncIdem, comp_f, sub_f_apply]
  rcases lt_trichotomy (m + 1) lo with h | rfl | h
  · rw [truncNull_f_succ_of_both (by omega) h (hg _ h)]
    simp
  · obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by ring⟩
    rw [truncNull_f_succ, ite_eq_left (by omega), ite_eq_right (lt_irrefl _), add_zero]
    have h₁ := comm_succ H n
    rw [hg _ (by omega), add_zero] at h₁
    have h₂ : H.hom (n + 1) (n + 1 + 1) ≫ D.d (n + 1 + 1) (n + 1) =
        e.f (n + 1) - D.d (n + 1) n ≫ H.hom n (n + 1) := by rw [h₁]; abel
    have hc : e.f (n + 1 + 1) ≫ D.d (n + 1 + 1) (n + 1) = D.d (n + 1 + 1) (n + 1) ≫ e.f (n + 1) :=
      e.comm _ _
    simp only [sub_comp, comp_sub, assoc, he', reassoc_of% hc, hl, hr, reassoc_of% h₂,
      d_comp_d_assoc, zero_comp, sub_zero]
    abel
  · rw [truncNull_f_succ_of_neither (by omega) (by omega)]
    simp [he']

/-- Truncation above `hi` is idempotent if `g` vanishes above `hi`. -/
lemma truncIdem_upper_idem {hi : ℤ} (hg : ∀ k, hi < k → g.f k = 0) :
    truncIdem H (hi ≤ ·) ≫ truncIdem H (hi ≤ ·) = truncIdem H (hi ≤ ·) := by
  have he' : ∀ k, e.f k ≫ e.f k = e.f k := fun k ↦ by rw [← comp_f, he]
  ext k
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by ring⟩
  simp only [truncIdem, comp_f, sub_f_apply]
  rcases lt_trichotomy hi (m + 1) with h | rfl | h
  · rw [truncNull_f_succ_of_both (by omega) (by omega) (hg _ h)]
    simp
  · rw [truncNull_f_succ, ite_eq_right (by omega), ite_eq_left le_rfl, zero_add]
    have h₁ := comm_succ H (m + 1)
    rw [hg _ (by omega), add_zero] at h₁
    have h₂ : D.d (m + 1 + 1) (m + 1) ≫ H.hom (m + 1) (m + 1 + 1) =
        e.f (m + 1 + 1) - H.hom (m + 1 + 1) (m + 1 + 1 + 1) ≫ D.d (m + 1 + 1 + 1) (m + 1 + 1) := by
      rw [h₁]; abel
    have hc : D.d (m + 1 + 1) (m + 1) ≫ e.f (m + 1) = e.f (m + 1 + 1) ≫ D.d (m + 1 + 1) (m + 1) :=
      (e.comm _ _).symm
    simp only [sub_comp, comp_sub, assoc, he', hc, reassoc_of% hl, reassoc_of% hr,
      reassoc_of% h₂, d_comp_d, comp_zero, sub_zero]
    abel
  · rw [truncNull_f_succ_of_neither (by omega) (by omega)]
    simp [he']

omit hl hr he in
lemma truncIdem_lower_f_eq_zero {lo : ℤ} (hg : ∀ k < lo, g.f k = 0) {k : ℤ} (hk : k < lo) :
    (truncIdem H (· < lo)).f k = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by ring⟩
  rw [truncIdem, sub_f_apply, truncNull_f_succ_of_both (by omega) hk (hg _ hk), sub_self]

omit hl hr he in
lemma truncIdem_upper_f_eq_zero {hi : ℤ} (hg : ∀ k, hi < k → g.f k = 0) {k : ℤ} (hk : hi < k) :
    (truncIdem H (hi ≤ ·)).f k = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by ring⟩
  rw [truncIdem, sub_f_apply, truncNull_f_succ_of_both (by omega) (by omega) (hg _ hk), sub_self]

end Truncation

namespace KarSplitting

variable {C : ChainComplex V ℤ} {p E : C ⟶ C} (S : KarSplitting p E)

/-- The homotopy `e ≃ ιr`, compressed by `e`. -/
def karHtpy : Homotopy S.e (S.ι ≫ S.r) :=
  karHomotopy S.ιr.symm (p := S.e) (q := S.e) (by simp) (by simp)

lemma karHtpy_left (i j : ℤ) : S.e.f i ≫ S.karHtpy.hom i j = S.karHtpy.hom i j := by
  simp [karHtpy, ← comp_f_assoc]

lemma karHtpy_right (i j : ℤ) : S.karHtpy.hom i j ≫ S.e.f j = S.karHtpy.hom i j := by
  simp [karHtpy, ← comp_f]

lemma ιr_f_eq_zero {k : ℤ} (hk : p.f k = 0) : (S.ι ≫ S.r).f k = 0 := by
  rw [comp_f, ← S.ι_p, comp_f, hk, comp_zero, zero_comp]

/-- Removal of the degrees below `lo` (manuscript l. 322). -/
def truncBelow (lo : ℤ) (hp : ∀ k < lo, p.f k = 0) : KarSplitting p E :=
  S.restrict (truncIdem S.karHtpy (· < lo))
    (truncIdem_lower_idem S.e_idem S.karHtpy_left S.karHtpy_right
      fun k hk ↦ S.ιr_f_eq_zero (hp k hk))
    (truncIdem_comp S.e_idem S.karHtpy_right)
    (truncHomotopy _ _)

/-- Removal of the degrees above `hi` (manuscript l. 322). -/
def truncAbove (hi : ℤ) (hp : ∀ k, hi < k → p.f k = 0) : KarSplitting p E :=
  S.restrict (truncIdem S.karHtpy (hi ≤ ·))
    (truncIdem_upper_idem S.e_idem S.karHtpy_left S.karHtpy_right
      fun k hk ↦ S.ιr_f_eq_zero (hp k hk))
    (truncIdem_comp S.e_idem S.karHtpy_right)
    (truncHomotopy _ _)

lemma truncBelow_e_f_eq_zero {lo : ℤ} (hp : ∀ k < lo, p.f k = 0) {k : ℤ} (hk : k < lo) :
    (S.truncBelow lo hp).e.f k = 0 :=
  truncIdem_lower_f_eq_zero (fun k hk ↦ S.ιr_f_eq_zero (hp k hk)) hk

lemma truncAbove_e_f_eq_zero {hi : ℤ} (hp : ∀ k, hi < k → p.f k = 0) {k : ℤ} (hk : hi < k) :
    (S.truncAbove hi hp).e.f k = 0 :=
  truncIdem_upper_f_eq_zero (fun k hk ↦ S.ιr_f_eq_zero (hp k hk)) hk

lemma truncAbove_e_f_eq_zero_of {hi : ℤ} (hp : ∀ k, hi < k → p.f k = 0) {k : ℤ}
    (hk : S.e.f k = 0) : (S.truncAbove hi hp).e.f k = 0 := by
  change (truncIdem S.karHtpy (hi ≤ ·)).f k = 0
  rw [← truncIdem_comp S.e_idem S.karHtpy_right, comp_f, hk, comp_zero]

/-- Truncation to the degrees `[lo, hi]` of `p`. -/
def truncate {lo hi : ℤ} (hp : SupportedIn p lo hi) : KarSplitting p E :=
  (S.truncBelow lo fun k hk ↦ hp k (.inl hk)).truncAbove hi fun k hk ↦ hp k (.inr hk)

lemma supportedIn_truncate {lo hi : ℤ} (hp : SupportedIn p lo hi) :
    SupportedIn (S.truncate hp).e lo hi := by
  intro k hk
  rcases hk with hk | hk
  · exact truncAbove_e_f_eq_zero_of _ _ (truncBelow_e_f_eq_zero _ _ hk)
  · exact truncAbove_e_f_eq_zero _ _ hk

/-- Manuscript Lemma 5.1, (5.4) with the truncation of l. 322: a homotopy idempotent `E` of a Kar
complex `(C, p)` concentrated in `[lo, hi]` splits through a Kar complex `(D, e)` with `e` a
strict idempotent concentrated in `[lo, hi]`.  The idempotent is made strict by the
Balmer–Schlichting dilation (`HomotopyIdempotent.strictifiable_of_support`). -/
theorem exists_splitting [HasBinaryBiproducts V] (hp : p ≫ p = p) (hE : p ≫ E ≫ p = E)
    (idem : Homotopy (E ≫ E) E) {lo hi : ℤ} (hsupp : SupportedIn p lo hi) :
    ∃ S : KarSplitting p E, SupportedIn S.e lo hi := by
  have hpE : p ≫ E = E := by rw [← hE, reassoc_of% hp]
  have hEp : E ≫ p = E := by rw [← hE]; simp [hp]
  let H := karHomotopy idem (p := p) (q := p) (by simp [reassoc_of% hpE, hEp]) hE
  have hH : ∀ i j, (i < lo ∨ lo + ((hi - lo + 1).toNat : ℕ) ≤ i) → H.hom i j = 0 := by
    intro i j hij
    have h := Int.self_le_toNat (hi - lo + 1)
    have : p.f i = 0 := hsupp i (by omega)
    simp [H, this]
  obtain ⟨X', ε, hε, -, φ, hφ⟩ := HomotopyIdempotent.strictifiable_of_support _ C E H lo hH
  obtain ⟨f, hf⟩ := (HomotopyCategory.quotient V (ComplexShape.down ℤ)).map_surjective φ.hom
  obtain ⟨g, hg⟩ := (HomotopyCategory.quotient V (ComplexShape.down ℤ)).map_surjective φ.inv
  have hεε : 𝐊.map ε ≫ 𝐊.map ε = 𝐊.map ε := by rw [← Functor.map_comp, hε]
  have hεf : 𝐊.map ε ≫ 𝐊.map f = 𝐊.map f ≫ 𝐊.map E := by rw [hf, hφ]
  have hgε : 𝐊.map g ≫ 𝐊.map ε = 𝐊.map E ≫ 𝐊.map g := by
    rw [hg, ← cancel_epi φ.hom, φ.hom_inv_id_assoc, ← reassoc_of% hφ, φ.hom_inv_id, comp_id]
  have hfg : 𝐊.map f ≫ 𝐊.map g = 𝟙 _ := by rw [hf, hg, φ.hom_inv_id]
  have hgf : 𝐊.map g ≫ 𝐊.map f = 𝟙 _ := by rw [hf, hg, φ.inv_hom_id]
  have hEp' : 𝐊.map E ≫ 𝐊.map p = 𝐊.map E := by rw [← Functor.map_comp, hEp]
  have hpE' : 𝐊.map p ≫ 𝐊.map E = 𝐊.map E := by rw [← Functor.map_comp, hpE]
  have hι : 𝐊.map (ε ≫ f ≫ p) = 𝐊.map ε ≫ 𝐊.map f := by
    rw [Functor.map_comp, Functor.map_comp, reassoc_of% hεf, hEp', hεf]
  have hr : 𝐊.map (p ≫ g ≫ ε) = 𝐊.map g ≫ 𝐊.map ε := by
    rw [Functor.map_comp, Functor.map_comp, hgε, reassoc_of% hpE']
  let S₀ : KarSplitting p E :=
    { D := X'
      e := ε
      e_idem := hε
      ι := ε ≫ f ≫ p
      r := p ≫ g ≫ ε
      e_ι := by rw [reassoc_of% hε]
      ι_p := by simp [hp]
      p_r := by rw [reassoc_of% hp]
      r_e := by simp [hε]
      ιr := HomotopyCategory.homotopyOfEq _ _ (by
        rw [Functor.map_comp, hι, hr, assoc, reassoc_of% hfg, hεε])
      rι := HomotopyCategory.homotopyOfEq _ _ (by
        rw [Functor.map_comp, hι, hr, assoc, reassoc_of% hεε, hεf, reassoc_of% hgf]) }
  exact ⟨S₀.truncate hsupp, S₀.supportedIn_truncate hsupp⟩

end KarSplitting

/-- The interface hypothesis `BS01` ([BS01, Theorem 2.8] for the split exact structure on
`Kar A`) holds. -/
theorem bs01 : BS01 := by
  intro A C lo hi hC e he
  obtain ⟨S, hS⟩ := KarSplitting.exists_splitting (p := 𝟙 C) (by simp) (by simp) he
    (lo := lo) (hi := hi) fun r hr ↦ (hC r hr).eq_of_src _ _
  exact ⟨S.D, S.e, lo, hi, S.ι, S.r, S.e_idem, hS, S.e_ι, S.r_e, ⟨S.rι⟩, ⟨S.ιr⟩⟩

/-! ### Lemma 5.1: the normalized corner -/

variable (J N) in
/-- The hypotheses of manuscript Lemma 5.1 in the Karoubi model: a Kar-endomorphism `E` of the
Poincaré complex `W = (𝒞, Π, Φ)` with specified homotopies `E² ≃ E` and `EΦ ≃ ΦE^*`
(diagrammatically `Φ ≫ E ≃ E^* ≫ Φ`). -/
structure HomotopyProjector (W : SymPoincare J N) where
  /-- The homotopy idempotent `E`. -/
  E : W.C ⟶ W.C
  E_kar : W.p ≫ E ≫ W.p = E
  /-- `E² ≃ E`. -/
  idem : Homotopy (E ≫ E) E
  /-- `EΦ ≃ ΦE^*`. -/
  adj : Homotopy (W.φ ≫ E) (dualHom J N E ≫ W.φ)

namespace HomotopyProjector

variable {W : SymPoincare J N} (π : HomotopyProjector J N W)

/-- The same projector on the rescaled complex `W.scale q`. -/
@[simps]
def scale (q : CentralUnit J) : HomotopyProjector J N (W.scale q) where
  E := π.E
  E_kar := π.E_kar
  idem := π.idem
  adj := homotopyCongr (π.adj.compRight (q.chain W.C)) (by simp [q.chain_comp]) (by simp)

/-- The image of a homotopy projector under a duality-preserving functor. -/
@[simps]
def map {V' : Type*} [Category V'] [Preadditive V'] {J' : StrictInvolution V'}
    (Φ : InvFunctor J J') : HomotopyProjector J' N (W.map Φ) where
  E := Φ.mapH π.E
  E_kar := by simp only [SymPoincare.map_p, ← Functor.map_comp, π.E_kar]
  idem := homotopyCongr (Φ.F.mapHomotopy π.idem) (Functor.map_comp _ _ _) rfl
  adj := homotopyCongr ((Φ.F.mapHomotopy π.adj).compLeft (Φ.mapDualIso N W.C).inv)
    (by rw [SymPoincare.map_φ, Φ.mapDual_eq, Functor.map_comp]; simp)
    (by rw [SymPoincare.map_φ, Φ.mapDual_eq, Φ.dualHom_mapH, Functor.map_comp]; simp)

/-- Manuscript Lemma 5.1, (5.4): a splitting with `(D, e)` in degrees `[0, N]`. -/
theorem exists_splitting [HasBinaryBiproducts V] :
    ∃ S : KarSplitting W.p π.E, SupportedIn S.e 0 N :=
  KarSplitting.exists_splitting W.p_idem π.E_kar π.idem W.support

end HomotopyProjector

/-- A splitting (5.4) of a homotopy projector. -/
abbrev HomotopySplitting {W : SymPoincare J N} (π : HomotopyProjector J N W) :=
  KarSplitting W.p π.E

namespace HomotopySplitting

variable {W : SymPoincare J N} {π : HomotopyProjector J N W} (S : HomotopySplitting π)

/-- The corner `r^* Φ r` of `W` (Lemma 5.1 for the form `Φ`). -/
@[simps, reducible]
def rawCorner (hS : SupportedIn S.e 0 N) : SymPoincare J N where
  C := S.D
  p := S.e
  p_idem := S.e_idem
  support := hS
  φ := dualHom J N S.r ≫ W.φ ≫ S.r
  φ_kar := by simp only [assoc, S.r_e, dualHom_comp_dualHom_assoc]
  symm := W.symm.conj S.r
  poincare := by
    obtain ⟨ψ, hψ, ⟨H₁⟩, ⟨H₂⟩⟩ := W.poincare
    have hΦ := HomotopyCategory.eq_of_homotopy _ _ π.adj
    have h₁ := HomotopyCategory.eq_of_homotopy _ _ H₁
    have h₂ := HomotopyCategory.eq_of_homotopy _ _ H₂
    simp only [Functor.map_comp, kmap_dualHom] at hΦ h₁ h₂
    have hιp : 𝐊.map S.ι ≫ 𝐊.map W.p = 𝐊.map S.ι := by rw [← Functor.map_comp, S.ι_p]
    refine ⟨S.ι ≫ ψ ≫ dualHom J N S.ι, ?_, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩,
      ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
    · simp only [assoc, S.e_ι_assoc, dualHom_comp_dualHom, S.e_ι]
    · simp only [Functor.map_comp, kmap_dualHom]
      exact CornerAlgebra.inv_comp_form (𝔻 := GraphCorner.homotopyDual J N) h₁ hΦ hιp
        S.kmap_rι S.kmap_ιr S.kmap_e_idem
    · simp only [Functor.map_comp, kmap_dualHom]
      exact CornerAlgebra.form_comp_inv (𝔻 := GraphCorner.homotopyDual J N) h₂ hΦ hιp
        S.kmap_rι S.kmap_ιr S.kmap_e_idem

/-- Manuscript (5.5): the normalized corner `(D, e, r^* Φ q⁻¹ r)`, the corner of `W.scale q⁻¹`;
its Poincaré inverse is `ι q Ψ ι^*`. -/
abbrev corner (q : CentralUnit J) (hS : SupportedIn S.e 0 N) : SymPoincare J N :=
  rawCorner (π := π.scale q.symm) S hS

lemma corner_φ (q : CentralUnit J) (hS : SupportedIn S.e 0 N) :
    (S.corner q hS).φ = dualHom J N S.r ≫ (W.φ ≫ q.symm.chain W.C) ≫ S.r := rfl

/-- Lemma 5.1, independence of the splitting: `r'ι` is a homotopy isometry between corners. -/
@[simps]
def rawCornerIsometry (S' : HomotopySplitting π) (hS : SupportedIn S.e 0 N)
    (hS' : SupportedIn S'.e 0 N) :
    SymPoincare.HomotopyIsometry (S.rawCorner hS) (S'.rawCorner hS') where
  f := S.ι ≫ S'.r
  g := S'.ι ≫ S.r
  f_kar := by simp
  g_kar := by simp
  fg := HomotopyCategory.homotopyOfEq _ _ (by
    simp only [rawCorner_p, Functor.map_comp, assoc]
    erw [reassoc_of% S'.kmap_rι, ← reassoc_of% S.kmap_rι, reassoc_of% S.kmap_ιr, S.kmap_ιr,
      S.kmap_e_idem])
  gf := HomotopyCategory.homotopyOfEq _ _ (by
    simp only [rawCorner_p, Functor.map_comp, assoc]
    erw [reassoc_of% S.kmap_rι, ← reassoc_of% S'.kmap_rι, reassoc_of% S'.kmap_ιr, S'.kmap_ιr,
      S'.kmap_e_idem])
  conj := HomotopyCategory.homotopyOfEq _ _ (by
    simp only [rawCorner_φ, Functor.map_comp, kmap_dualHom]
    exact CornerAlgebra.form_conj_splitting (𝔻 := GraphCorner.homotopyDual J N) S.kmap_rι
      S'.kmap_rι S'.kmap_ιr (by rw [← Functor.map_comp, S'.r_e]))

/-- Lemma 5.1, independence of the splitting, for normalized corners. -/
def cornerIsometry (S' : HomotopySplitting π) (q : CentralUnit J) (hS : SupportedIn S.e 0 N)
    (hS' : SupportedIn S'.e 0 N) :
    SymPoincare.HomotopyIsometry (S.corner q hS) (S'.corner q hS') :=
  rawCornerIsometry (π := π.scale q.symm) S S' hS hS'

/-- Naturality of the corner: `F(D, φ_D) = (FD, φ_{FD})` when `F` carries `q` to `q'`. -/
theorem corner_map {V' : Type*} [Category V'] [Preadditive V'] {J' : StrictInvolution V'}
    (Φ : InvFunctor J J') (q : CentralUnit J) (q' : CentralUnit J')
    (hq : ∀ X, Φ.F.map (q.inv X) = q'.inv (Φ.F.obj X)) (hS : SupportedIn S.e 0 N) :
    (S.corner q hS).map Φ =
      HomotopySplitting.corner (π := π.map Φ) (S.map Φ) q' (hS.map Φ) := by
  simp only [SymPoincare.map, rawCorner, KarSplitting.map]
  congr 1
  ext r
  simp [Φ.map_star, hq]

/-- The normalized corner is unchanged under transport along a strict isometry of the ambient
Poincaré complexes. -/
theorem corner_transport {W' : SymPoincare J N} {π' : HomotopyProjector J N W'} (θ : W.C ≅ W'.C)
    (hp : θ.hom ≫ W'.p = W.p ≫ θ.hom) (hE : π'.E = θ.inv ≫ π.E ≫ θ.hom)
    (hφ : dualHom J N θ.hom ≫ W.φ ≫ θ.hom = W'.φ) (q : CentralUnit J)
    (hS : SupportedIn S.e 0 N) :
    HomotopySplitting.corner (π := π') (S.transport θ hp hE) q hS = S.corner q hS := by
  simp only [rawCorner, KarSplitting.transport, SymPoincare.mk.injEq, heq_eq_eq, true_and,
    SymPoincare.scale_φ, ← hφ]
  erw [dualHom_comp]
  simp only [assoc]
  rw [q.symm.chain_comp_assoc θ.inv, θ.hom_inv_id_assoc, dualHom_comp_dualHom_assoc θ.hom θ.inv,
    θ.hom_inv_id, dualHom_id, id_comp]

end HomotopySplitting

/-! ### Lemma 5.2: comparison with the sheet -/

variable (J N) in
/-- The data of manuscript Lemma 5.2, (5.6)–(5.7), for a homotopy projector `π` on `W = (𝒞, Π, Φ)`
and a Poincaré complex `P = (C, p, φ)` (after forgetting the action): Kar-morphisms
`u : 𝒞 ⟶ C` (the row) and `v : C ⟶ 𝒞` (the column) with `uv ≃ 1`, `vu ≃ E`, `uE ≃ u` and
`uΦu^* ≃ qφ`, in the paper's order of composition. -/
structure RowColumn {W : SymPoincare J N} (π : HomotopyProjector J N W) (P : SymPoincare J N)
    (q : CentralUnit J) where
  u : W.C ⟶ P.C
  v : P.C ⟶ W.C
  u_kar : W.p ≫ u ≫ P.p = u
  v_kar : P.p ≫ v ≫ W.p = v
  /-- `uv ≃ 1`. -/
  uv : Homotopy (v ≫ u) P.p
  /-- `vu ≃ E`. -/
  vu : Homotopy (u ≫ v) π.E
  /-- `uE ≃ u`. -/
  uE : Homotopy (π.E ≫ u) u
  /-- (5.7): `uΦu^* ≃ qφ`. -/
  conj : Homotopy (dualHom J N u ≫ W.φ ≫ u) (P.φ ≫ q.chain P.C)

namespace RowColumn

variable {W P : SymPoincare J N} {π : HomotopyProjector J N W} {q : CentralUnit J}
  (R : RowColumn J N π P q)

@[reassoc (attr := simp)]
lemma u_comp_p : R.u ≫ P.p = R.u := by rw [← R.u_kar]; simp

@[reassoc (attr := simp)]
lemma p_comp_v : P.p ≫ R.v = R.v := by rw [← R.v_kar]; simp

/-- Manuscript Lemma 5.2 and (5.8): every normalized corner `(D, r^*Φq⁻¹r)` of `π` is homotopy
isometric to `P` via `w = uι`, with inverse `z = rv`: `wz ≃ uEv ≃ 1`, `zw ≃ rEι ≃ 1` and
`wφ_Dw^* ≃ q⁻¹uΦu^* ≃ φ`. -/
@[simps]
def lemma_5_2 (S : HomotopySplitting π) (hS : SupportedIn S.e 0 N) :
    SymPoincare.HomotopyIsometry (S.corner q hS) P where
  f := S.ι ≫ R.u
  g := R.v ≫ S.r
  f_kar := by simp
  g_kar := by simp
  fg := HomotopyCategory.homotopyOfEq _ _ (by
    have h := HomotopyCategory.eq_of_homotopy _ _ R.vu
    rw [Functor.map_comp] at h
    simp only [HomotopySplitting.rawCorner_p, Functor.map_comp, assoc]
    erw [reassoc_of% h, ← reassoc_of% S.kmap_rι, reassoc_of% S.kmap_ιr, S.kmap_ιr, S.kmap_e_idem])
  gf := HomotopyCategory.homotopyOfEq _ _ (by
    have h₁ := HomotopyCategory.eq_of_homotopy _ _ R.uE
    have h₂ := HomotopyCategory.eq_of_homotopy _ _ R.uv
    rw [Functor.map_comp] at h₁ h₂
    simp only [Functor.map_comp, assoc]
    erw [reassoc_of% S.kmap_rι, h₁, h₂])
  conj := HomotopyCategory.homotopyOfEq _ _ (by
    have h₁ := HomotopyCategory.eq_of_homotopy _ _ R.uE
    have h₂ := HomotopyCategory.eq_of_homotopy _ _ R.conj
    rw [Functor.map_comp] at h₁
    have h₃ : dualHom J N R.u ≫ (W.φ ≫ q.symm.chain W.C) ≫ R.u =
        (dualHom J N R.u ≫ W.φ ≫ R.u) ≫ q.symm.chain P.C := by
      simp [q.symm.chain_comp]
    replace h₂ := congrArg (· ≫ 𝐊.map (q.symm.chain P.C)) h₂
    simp only [← Functor.map_comp, ← h₃, assoc, CentralUnit.chain_symm_chain, comp_id] at h₂
    simp only [HomotopySplitting.corner_φ, Functor.map_comp, kmap_dualHom] at h₂ ⊢
    exact CornerAlgebra.form_conj_row (𝔻 := GraphCorner.homotopyDual J N) S.kmap_rι h₁
      (by erw [assoc]; exact h₂))

include R in
theorem isometric (S : HomotopySplitting π) (hS : SupportedIn S.e 0 N) :
    SymPoincare.Isometric (S.corner q hS) P :=
  ⟨R.lemma_5_2 S hS⟩

end RowColumn

/-! ### The graph corner of a homotopy action of a finite group -/

section Graph

open GraphCorner (sheetwise graphIdem graphRow graphCol graphForm chainDual order order_ne_zero)

variable {G : Type}

section Fintype

variable [Fintype G] {X : ChainComplex V ℤ} [HasBiproduct fun _ : G ↦ X]

lemma kmap_ext_to_graph {Y : ChainComplex V ℤ} {f f' : Y ⟶ ⨁ fun _ : G ↦ X}
    (h : ∀ a, 𝐊.map (f ≫ biproduct.π (fun _ : G ↦ X) a) =
      𝐊.map (f' ≫ biproduct.π (fun _ : G ↦ X) a)) :
    𝐊.map f = 𝐊.map f' := by
  have e (f : Y ⟶ ⨁ fun _ : G ↦ X) :
      f = ∑ a, (f ≫ biproduct.π (fun _ : G ↦ X) a) ≫ biproduct.ι (fun _ : G ↦ X) a := by
    simp only [assoc, ← comp_sum, biproduct.total, comp_id]
  have h' a := by simpa only [Functor.map_comp] using h a
  rw [e f, e f']
  simp only [Functor.map_sum, Functor.map_comp, h']

lemma kmap_ext_from_graph {Y : ChainComplex V ℤ} {f f' : (⨁ fun _ : G ↦ X) ⟶ Y}
    (h : ∀ b, 𝐊.map (biproduct.ι (fun _ : G ↦ X) b ≫ f) =
      𝐊.map (biproduct.ι (fun _ : G ↦ X) b ≫ f')) :
    𝐊.map f = 𝐊.map f' := by
  have e (f : (⨁ fun _ : G ↦ X) ⟶ Y) :
      f = ∑ b, biproduct.π (fun _ : G ↦ X) b ≫ biproduct.ι (fun _ : G ↦ X) b ≫ f := by
    simp only [← assoc, ← sum_comp, biproduct.total, id_comp]
  have h' b := by simpa only [Functor.map_comp] using h b
  rw [e f, e f']
  simp only [Functor.map_sum, Functor.map_comp, h']

lemma kmap_ext_from_dualGraph {Y : ChainComplex V ℤ}
    {f f' : dualComplex J N (⨁ fun _ : G ↦ X) ⟶ Y}
    (h : ∀ b, 𝐊.map (dualHom J N (biproduct.π (fun _ : G ↦ X) b) ≫ f) =
      𝐊.map (dualHom J N (biproduct.π (fun _ : G ↦ X) b) ≫ f')) :
    𝐊.map f = 𝐊.map f' := by
  have e (f : dualComplex J N (⨁ fun _ : G ↦ X) ⟶ Y) :
      f = ∑ b, dualHom J N (biproduct.ι (fun _ : G ↦ X) b) ≫
        dualHom J N (biproduct.π (fun _ : G ↦ X) b) ≫ f := by
    simp only [← assoc, ← sum_comp, dualHom_comp_dualHom, ← dualHom_sum, biproduct.total,
      dualHom_id, id_comp]
  have h' b := by simpa only [Functor.map_comp] using h b
  rw [e f, e f']
  simp only [Functor.map_sum, Functor.map_comp, h']

lemma graphForm_eq (φ : dualComplex J N X ⟶ X) :
    graphForm (G := G) (chainDual J N) φ =
      ∑ g, dualHom J N (biproduct.ι (fun _ : G ↦ X) g) ≫ φ ≫ biproduct.ι (fun _ : G ↦ X) g := rfl

@[reassoc]
lemma dualHom_π_graphForm (φ : dualComplex J N X ⟶ X) (b : G) :
    dualHom J N (biproduct.π (fun _ : G ↦ X) b) ≫ graphForm (chainDual J N) φ =
      φ ≫ biproduct.ι (fun _ : G ↦ X) b :=
  GraphCorner.dualMap_π_graphForm (chainDual J N) φ b

@[reassoc]
lemma graphForm_π_eq (φ : dualComplex J N X ⟶ X) (a : G) :
    graphForm (chainDual J N) φ ≫ biproduct.π (fun _ : G ↦ X) a =
      dualHom J N (biproduct.ι (fun _ : G ↦ X) a) ≫ φ :=
  GraphCorner.graphForm_π (chainDual J N) φ a

lemma sheetwise_eq_sum (f : X ⟶ X) :
    sheetwise (G := G) f =
      ∑ b, biproduct.π (fun _ : G ↦ X) b ≫ f ≫ biproduct.ι (fun _ : G ↦ X) b := by
  rw [← id_comp (sheetwise f), ← biproduct.total, sum_comp]
  simp [sheetwise]

variable (G) in
/-- The graph object `(⨁_G C, p ⊗ 1, φ ⊗ 1)` of manuscript (5.2): `|G|` copies of `P`. -/
@[simps, reducible]
def graphPoincare (P : SymPoincare J N) [HasBiproduct fun _ : G ↦ P.C] : SymPoincare J N where
  C := ⨁ fun _ : G ↦ P.C
  p := sheetwise P.p
  p_idem := biproduct.hom_ext' _ _ fun b ↦ biproduct.hom_ext _ _ fun a ↦ by simp [sheetwise]
  support r hr := by
    rw [sheetwise_eq_sum]
    change Hom.fAddMonoidHom r _ = 0
    rw [map_sum]
    refine Finset.sum_eq_zero fun b _ ↦ ?_
    rw [Hom.fAddMonoidHom_apply, comp_f, comp_f, P.support r hr, zero_comp, comp_zero]
  φ := graphForm (chainDual J N) P.φ
  φ_kar := by
    rw [graphForm_eq]
    simp only [comp_sum, sum_comp, assoc, sheetwise, biproduct.ι_map, dualHom_comp_dualHom_assoc]
    simp only [dualHom_comp, assoc, P.dualHom_p_comp_φ_assoc, P.φ_comp_p_assoc]
  symm := by
    rw [graphForm_eq]
    exact IsStrictSymm.sum _ fun g _ ↦ P.symm.conj _
  poincare := by
    obtain ⟨ψ, hψ, ⟨H₁⟩, ⟨H₂⟩⟩ := P.poincare
    have h₁ := HomotopyCategory.eq_of_homotopy _ _ H₁
    have h₂ := HomotopyCategory.eq_of_homotopy _ _ H₂
    rw [Functor.map_comp] at h₁ h₂
    refine ⟨∑ g, biproduct.π (fun _ : G ↦ P.C) g ≫ ψ ≫
      dualHom J N (biproduct.π (fun _ : G ↦ P.C) g), ?_,
      ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
    · simp only [sheetwise, comp_sum, sum_comp, assoc, biproduct.map_π_assoc,
        dualHom_comp_dualHom, biproduct.map_π]
      simp only [dualHom_comp, reassoc_of% hψ]
    · rw [sum_comp, sheetwise_eq_sum]
      simp only [assoc, dualHom_π_graphForm, Functor.map_sum, Functor.map_comp, reassoc_of% h₁]
    · rw [comp_sum, sheetwise_eq_sum, dualHom_sum]
      simp only [graphForm_π_eq_assoc, dualHom_comp, assoc, Functor.map_sum, Functor.map_comp,
        reassoc_of% h₂]

end Fintype

variable (G) in
/-- Manuscript (5.1) in the Karoubi model: a homotopy action of `G` on `P = (C, p, φ)` by homotopy
isometries, with specified homotopies — Kar-endomorphisms `A_g` with `A_1 = p`,
`A_gA_h ≃ A_{gh}` and `A_gφ ≃ φA_{g⁻¹}^*` (diagrammatically). -/
structure KarAction [Group G] (P : SymPoincare J N) where
  act : G → (P.C ⟶ P.C)
  act_kar : ∀ g, P.p ≫ act g ≫ P.p = act g
  act_one : act 1 = P.p
  mul : ∀ g h, Homotopy (act h ≫ act g) (act (g * h))
  isometry : ∀ g, Homotopy (P.φ ≫ act g) (dualHom J N (act g⁻¹) ≫ P.φ)

namespace KarAction

variable [Group G] {P : SymPoincare J N} (A : KarAction G P)

/-- A homotopy action in the sense of `GraphCornerChain` on a complex with `p = 1`. -/
@[simps]
def ofHomotopyIsometryAction (a : GraphCorner.HomotopyIsometryAction J N G P.C P.φ)
    (hp : P.p = 𝟙 _) : KarAction G P where
  act := a.act
  act_kar g := by rw [hp, id_comp, comp_id]
  act_one := a.act_one.trans hp.symm
  mul := a.mul
  isometry := a.isometry

@[reassoc (attr := simp)]
lemma p_comp_act (g : G) : P.p ≫ A.act g = A.act g := by rw [← A.act_kar]; simp

@[reassoc (attr := simp)]
lemma act_comp_p (g : G) : A.act g ≫ P.p = A.act g := by rw [← A.act_kar]; simp

variable [HasBiproduct fun _ : G ↦ P.C]

@[reassoc (attr := simp)]
lemma graphRow_comp_p : graphRow A.act ≫ P.p = graphRow A.act :=
  biproduct.hom_ext' _ _ fun b ↦ by simp

variable [Fintype G] [Linear ℚ V]

/-- `GraphCorner.graphCol_π`, with the scalar action of `P.C ⟶ P.C` rather than of `End P.C`. -/
@[reassoc (attr := simp)]
lemma graphCol_π (a : G) :
    graphCol A.act ≫ biproduct.π (fun _ : G ↦ P.C) a = (order G)⁻¹ • A.act a⁻¹ :=
  GraphCorner.graphCol_π A.act a

lemma ι_graphIdem_π (a b : G) :
    biproduct.ι (fun _ : G ↦ P.C) b ≫ graphIdem A.act ≫ biproduct.π (fun _ : G ↦ P.C) a =
      (order G)⁻¹ • A.act (a⁻¹ * b) :=
  GraphCorner.ι_graphIdem_π A.act a b

@[reassoc (attr := simp)]
lemma p_comp_graphCol : P.p ≫ graphCol A.act = graphCol A.act :=
  biproduct.hom_ext _ _ fun a ↦ by rw [assoc, A.graphCol_π, Linear.comp_smul, A.p_comp_act]

/-- (5.6), `vu ≃ E`. -/
@[reassoc]
lemma kmap_graphRow_comp_graphCol :
    𝐊.map (graphRow A.act) ≫ 𝐊.map (graphCol A.act) = 𝐊.map (graphIdem A.act) := by
  rw [← Functor.map_comp]
  refine kmap_ext_from_graph fun b ↦ kmap_ext_to_graph fun a ↦ ?_
  simp only [assoc, GraphCorner.ι_graphRow_assoc, A.graphCol_π, Linear.comp_smul,
    Functor.map_smul]
  rw [A.ι_graphIdem_π, Functor.map_smul,
    HomotopyCategory.eq_of_homotopy _ _ (A.mul a⁻¹ b)]

/-- (5.6), `uv ≃ 1`. -/
@[reassoc]
lemma kmap_graphCol_comp_graphRow :
    𝐊.map (graphCol A.act) ≫ 𝐊.map (graphRow A.act) = 𝐊.map P.p := by
  rw [← Functor.map_comp, GraphCorner.graphCol, GraphCorner.graphRow, Linear.smul_comp,
    biproduct.lift_desc, Functor.map_smul, Functor.map_sum,
    Finset.sum_congr rfl fun g _ ↦ HomotopyCategory.eq_of_homotopy _ _ (A.mul g g⁻¹)]
  simp only [mul_inv_cancel, A.act_one, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ order_ne_zero, one_smul]

lemma kmap_graphForm_comp_graphRow :
    𝐊.map (graphForm (chainDual J N) P.φ ≫ graphRow A.act) =
      𝐊.map (order G • (dualHom J N (graphCol A.act) ≫ P.φ)) := by
  refine kmap_ext_from_dualGraph fun b ↦ ?_
  rw [dualHom_π_graphForm_assoc, GraphCorner.ι_graphRow, Linear.comp_smul,
    dualHom_comp_dualHom_assoc, A.graphCol_π, dualHom_smul, Linear.smul_comp, smul_smul,
    mul_inv_cancel₀ order_ne_zero, one_smul]
  exact HomotopyCategory.eq_of_homotopy _ _ (A.isometry b)

lemma kmap_dualHom_graphRow_comp_graphForm :
    𝐊.map (dualHom J N (graphRow A.act) ≫ graphForm (chainDual J N) P.φ) =
      𝐊.map (order G • (P.φ ≫ graphCol A.act)) := by
  refine kmap_ext_to_graph fun a ↦ ?_
  rw [assoc, graphForm_π_eq, dualHom_comp_dualHom_assoc, GraphCorner.ι_graphRow,
    Linear.smul_comp, assoc, A.graphCol_π, Linear.comp_smul, smul_smul,
    mul_inv_cancel₀ order_ne_zero, one_smul]
  have h := HomotopyCategory.eq_of_homotopy _ _ (A.isometry a⁻¹)
  rw [inv_inv] at h
  exact h.symm

/-- (5.3), `E² ≃ E`. -/
lemma kmap_graphIdem_idem :
    𝐊.map (graphIdem A.act) ≫ 𝐊.map (graphIdem A.act) = 𝐊.map (graphIdem A.act) := by
  rw [← A.kmap_graphRow_comp_graphCol, assoc, A.kmap_graphCol_comp_graphRow_assoc,
    ← Functor.map_comp_assoc, A.graphRow_comp_p]

/-- (5.6), `uE ≃ u`. -/
lemma kmap_graphIdem_comp_graphRow :
    𝐊.map (graphIdem A.act) ≫ 𝐊.map (graphRow A.act) = 𝐊.map (graphRow A.act) := by
  rw [← A.kmap_graphRow_comp_graphCol, assoc, A.kmap_graphCol_comp_graphRow,
    ← Functor.map_comp, A.graphRow_comp_p]

/-- (5.3), `EΦ ≃ ΦE^*`. -/
lemma kmap_graphForm_comp_graphIdem :
    𝐊.map (graphForm (chainDual J N) P.φ ≫ graphIdem A.act) =
      𝐊.map (dualHom J N (graphIdem A.act) ≫ graphForm (chainDual J N) P.φ) := by
  have h : 𝐊.map (dualHom J N (graphIdem A.act)) =
      𝐊.map (dualHom J N (graphCol A.act)) ≫ 𝐊.map (dualHom J N (graphRow A.act)) := by
    rw [kmap_dualHom, kmap_dualHom, kmap_dualHom, ← A.kmap_graphRow_comp_graphCol,
      GraphCorner.dualMap_comp]
    rfl
  rw [Functor.map_comp, ← A.kmap_graphRow_comp_graphCol, ← assoc, ← Functor.map_comp,
    A.kmap_graphForm_comp_graphRow, Functor.map_comp, h, assoc,
    ← Functor.map_comp (f := dualHom J N _), A.kmap_dualHom_graphRow_comp_graphForm]
  simp only [Functor.map_smul, Functor.map_comp, Linear.smul_comp, Linear.comp_smul, assoc]

/-- (5.7), `uΦu^* ≃ qφ`. -/
lemma kmap_graphRow_isometry :
    𝐊.map (dualHom J N (graphRow A.act) ≫ graphForm (chainDual J N) P.φ ≫ graphRow A.act) =
      𝐊.map (P.φ ≫ (CentralUnit.ofRat (J := J) (order G) order_ne_zero).chain P.C) := by
  rw [← assoc, Functor.map_comp, A.kmap_dualHom_graphRow_comp_graphForm,
    CentralUnit.ofRat_chain, Linear.comp_smul, comp_id, Functor.map_smul, Functor.map_smul,
    Functor.map_comp, Linear.smul_comp, assoc, A.kmap_graphCol_comp_graphRow,
    ← Functor.map_comp, P.φ_comp_p]

/-- The graph idempotent (5.2) `E = q⁻¹ Σ_g A_g ⊗ R_{g⁻¹}`, a homotopy projector on the graph
object with the homotopies (5.3). -/
@[simps]
def projector : HomotopyProjector J N (graphPoincare G P) where
  E := graphIdem A.act
  E_kar := biproduct.hom_ext' _ _ fun b ↦ biproduct.hom_ext _ _ fun a ↦ by
    have h := A.ι_graphIdem_π a b
    simp only [graphPoincare_p, sheetwise, assoc, biproduct.ι_map_assoc, biproduct.map_π,
      reassoc_of% h, h, Linear.smul_comp, Linear.comp_smul, p_comp_act, act_comp_p]
  idem := HomotopyCategory.homotopyOfEq _ _ (by erw [Functor.map_comp, A.kmap_graphIdem_idem])
  adj := HomotopyCategory.homotopyOfEq _ _ A.kmap_graphForm_comp_graphIdem

/-- The graph row `u` and column `v` (5.6)–(5.7) of a homotopy action, with `q = |G|`. -/
@[simps]
def rowColumn :
    RowColumn J N A.projector P (CentralUnit.ofRat (J := J) (order G) order_ne_zero) where
  u := graphRow A.act
  v := graphCol A.act
  u_kar := biproduct.hom_ext' _ _ fun b ↦ by simp [sheetwise]
  v_kar := biproduct.hom_ext _ _ fun a ↦ by
    simp only [graphPoincare_p, sheetwise, assoc, biproduct.map_π, A.graphCol_π_assoc,
      A.p_comp_graphCol_assoc, A.graphCol_π]
    erw [Linear.smul_comp, A.act_comp_p]
  uv := HomotopyCategory.homotopyOfEq _ _ (by erw [Functor.map_comp, A.kmap_graphCol_comp_graphRow])
  vu := HomotopyCategory.homotopyOfEq _ _ (by
    erw [Functor.map_comp, A.kmap_graphRow_comp_graphCol]; rfl)
  uE := HomotopyCategory.homotopyOfEq _ _ (by
    erw [Functor.map_comp]; exact A.kmap_graphIdem_comp_graphRow)
  conj := HomotopyCategory.homotopyOfEq _ _ A.kmap_graphRow_isometry

variable [HasBinaryBiproducts V]

/-- The corner class `𝔡` of a homotopy action (manuscript Lemma 5.1 for (5.2)): the normalized
corner of a truncated Balmer–Schlichting splitting of the graph idempotent. -/
def cornerClass : SymPoincare J N :=
  HomotopySplitting.corner (π := A.projector) A.projector.exists_splitting.choose
    (CentralUnit.ofRat (order G) order_ne_zero) A.projector.exists_splitting.choose_spec

/-- Manuscript Lemma 5.2 for a homotopy action of a finite group: `𝔡 ≃ P`. -/
theorem cornerClass_isometric : SymPoincare.Isometric A.cornerClass P :=
  A.rowColumn.isometric _ _

end KarAction

end Graph

end

end HSFormal.LTheory
