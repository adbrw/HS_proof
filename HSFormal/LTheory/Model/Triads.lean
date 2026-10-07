import HSFormal.LTheory.Model.Cobordism
import HSFormal.LTheory.Model.Transport

/-!
# Symmetric triads (L-model module 8)

`blueprint/lower-L-construction.md` §4, row 8 (consumed by rows 10 `BoundaryConstructionRel` and
17 `LiftingPairUnique`, plan (L2)).  Strictly symmetric `(N+2)`-dimensional triads in the Karoubi
model of `Pairs.lean` (Ran80I §1–3, Ran81 §1.3, Ran92 §1 as adapted there: `δφ : Homotopy _ 0`,
`IsSymmHomotopy` for `T δφ = δφ`, Kar idempotents, faces of dimension `N + 1`, top of dimension
`N + 1 + 1`):

```
  P = ∂₀₁C ──j₀──▶ ∂₀C          X₀ = (j₀, (δφ₀, φ)), X₁ = (j₁, (δφ₁, φ)) : PairData P
     │j₁           │i₀          j₀ i₀ = j₁ i₁ (strictly)
     ▼             ▼            δφ : θ ≃ 0,  θ = i₀ δφ₀ i₀^* - i₁ δφ₁ i₁^*  (`triadCycle`)
    ∂₁C ──i₁──▶    E
```

* `PairData P`: a symmetric pair on the fixed boundary `P` **without** the Poincaré condition
  (`PairOn P` minus `poincare`); `PairData.IsPoincare`, `toPairOn`, `ofPairOn`.
* `TriadOn X₀ X₁`: a symmetric triad with prescribed faces (prescribed faces avoid dependent
  equalities, as `PairOn` does for pairs).  Orientation: `∂E = ∂₀C ∪_{∂₀₁C} -∂₁C`, so a Poincaré
  triad is a cobordism rel `P` from `X₀` to `X₁`.
* `TriadOn.Ψ : Cone(i₀)^{N+2-*} ⟶ Cone(i₁)`: the relative duality map of the map of pairs
  `(P ⟶ ∂₀C) ⟶ (∂₁C ⟶ E)` (`H^{N+2-*}(E, ∂₀) ≅ H_*(E, ∂₁)`), a chain map (`ΨF_comm`) and Kar
  (`Ψ_kar`).  **Poincaré** (`TriadOn.IsPoincare`): both faces are Poincaré pairs and `Ψ` is a Kar
  equivalence (`IsPoincareTop`).
* **Faces** (`R1 for triads`): `TriadOn.pair₀ h`, `TriadOn.pair₁ h : PairOn P` for
  `h : T.IsPoincare`, with boundary `P` *definitionally*; `TriadOn.nullCobordant_bd`.
* Constructions: `cylinder X` (`X × I` rel `∂X`, top always Poincaré), `PairData.zero P` (empty
  face), `PairData.ofClosed Q` (closed complex as a pair with empty boundary, Poincaré),
  `ofPair Y` (an `(N+2)`-dimensional pair as the triad `(D; ∂D, ∅; ∅)`, `Ψ = inr ∘ Ψ_Y`),
  `ofRel` (a pair whose boundary is the pair `W`, from the relative lift), `neg`, `swap`
  (`Ψ(T.swap) = -TΨ(T)`), `map Φ` (naturality of `Ψ` under cone comparisons), all preserving
  `IsPoincare`.
* `PairOn.RelCobordant`: cobordism rel boundary of Poincaré pairs (`refl`, `symm`,
  `TriadOn.relCobordant`).
* Supports: `SymPair.lift` (a Poincaré pair with all objects in a full additive subcategory `U`
  is a Poincaré pair in `U`), `SymPair.nullCobordant_lift`, `SymPair.nullCobordant_bdLift`,
  `TriadOn.nullCobordant_lift`.

**Conventions and the Poincaré condition.**  Ranicki calls a triad Poincaré if `∂₀₁C` is
Poincaré, the faces are Poincaré pairs and the `(N+2)`-pair `(∂₀C ∪_{∂₀₁C} ∂₁C ⟶ E)` is Poincaré.
With Poincaré faces, the last condition is equivalent to `IsPoincareTop`: the triples
`(E, ∂E, ∂₀C)` and `(E, ∂E, ∂₁C)` give ladders relating the union duality, `Ψ` (resp. `TΨ`) and
the duality of `∂₁C` (resp. `∂₀C`), and two-out-of-three applies.  This equivalence and Wall's
lemma (union pair Poincaré and one face Poincaré ⇒ the other face Poincaré) are **not**
formalized: they need two-out-of-three for non-split ladders in `Kar V` (even R1 for pairs is
only formalized in the degreewise split, based case, `BoundaryPoincare.lean`).  Exactly as
`SymPair` records its boundary as a `SymPoincare`, `IsPoincare` records the faces as Poincaré.
Ranicki's squares commute up to a homotopy `g`; here `j₀ i₀ = j₁ i₁` strictly (the relative lift
and the boundary constructions produce strict squares; `g = 0` keeps `θ` strictly symmetric).

**Consumer statements.**
* Module 10 (`BoundaryConstructionRel`): input a triad `T₀ : TriadOn W (PairData.zero Y)` (an
  `(N+2)`-pair `(W ⟶ E)` rel `∂W = Y`, Poincaré modulo `U`; built by `TriadOn.ofRel` from
  `LiftComplex.RelLift.Cascade`, whose `relH_comm` is `ofRel`'s `H_comm` for
  `ψ = relTop W.δφ`); output a Poincaré triad `T : TriadOn W' Z` (`T.IsPoincare`) on a boundary
  `Y' ≃ Y`, with `W' ≃ W` and `Z` contractible modulo `U`.
* Module 17 (`LiftingPairUnique`, (L2)): from `h : T.IsPoincare`, `TriadOn.pair₁ h : PairOn Y'`
  is a null-cobordism of `Y'`; after domination and `SymPair.transportD`/`transportBd` (module
  11) it has all objects in `F.U`, and `SymPair.nullCobordant_bdLift F` gives
  `NullCobordant (X.bdLift F hU)`, i.e. `Lconc.cls (Y.bdLift F hU) = 0`
  (`Lconc.cls_eq_zero_iff`).  Applied to `W₁ ⊕ -W₂` (`PairOn.sum`, `SymPair.neg`) this gives
  `[Y₁] = [Y₂]` in `L(U)`.

Not provided: direct sums of triads (sums of pairs are `PairOn.sum`), gluing triads along a
common face (transitivity of `RelCobordant`; with strictly commuting squares the glued square
only commutes up to the cone homotopy, so this needs Ranicki's homotopy-commutative triads or a
relative union; it is not a consequence of `PairOn.glue`, which glues along a direct summand of a
*closed* boundary).
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex homotopyCofiber
  HSFormal.Compression

noncomputable section

universe v v' u u'

attribute [local implicit_reducible] SymPoincare.zero SymPoincare.lift

variable {V : Type u} [Category.{v} V] [Preadditive V] {J : StrictInvolution V} {N : ℤ}

/-- Closes `u = v` for products and negations of `Int.negOnePow`s by parity (as `bd_sign_tac` in
`BoundaryConstruction`). -/
macro "triad_sign_tac" : tactic =>
  `(tactic| (simp only [← Int.negOnePow_add, ← Int.negOnePow_succ, neg_neg, ← Int.negOnePow_one]
             try rw [← Int.negOnePow_zero]
             rw [Int.negOnePow_eq_iff]
             simp [parity_simps, ← Int.not_even_iff_odd]
             try tauto))

/-! ### Top components of homotopies -/

section HTop

variable {D : ChainComplex V ℤ} {f : dualComplex J N D ⟶ D}

/-- The top component `H_r : D^{N+1-r} ⟶ D_r` of a null-homotopy `H : f ≃ 0` of a map
`f : D^{N-*} ⟶ D` (for `f = j φ j^*` this is `relTop`). -/
def hTop (H : Homotopy f 0) (r : ℤ) : D.X (N + 1 - r) ⟶ D.X r :=
  (D.XIsoOfEq (by omega : N + 1 - r = N - (r - 1))).hom ≫ H.hom (r - 1) r

lemma hTop_eq (H : Homotopy f 0) (s r : ℤ) (h : s + 1 = r) :
    hTop H r = (D.XIsoOfEq (by omega : N + 1 - r = N - s)).hom ≫ H.hom s r := by
  obtain rfl : s = r - 1 := by omega
  rfl

/-- The cycle condition `H_r d = δ H_{r-1} + f_{r-1}` in the `(N+1)`-dual indexing. -/
lemma hTop_comm (H : Homotopy f 0) (r r' : ℤ) (h : (ComplexShape.down ℤ).Rel r r') :
    hTop H r ≫ D.d r r' = ((dualComplex J (N + 1) D).d r r' ≫ hTop H r' :
      D.X (N + 1 - r) ⟶ D.X r') +
      (D.XIsoOfEq (by simp only [ComplexShape.down_Rel] at h; omega : N + 1 - r = N - r')).hom ≫
        f.f r' := by
  obtain rfl : r = r' + 1 := by simp only [ComplexShape.down_Rel] at h; omega
  have hc : H.hom r' (r' + 1) ≫ D.d (r' + 1) r' = f.f r' -
      (dualComplex J N D).d r' (r' - 1) ≫ H.hom (r' - 1) r' := by
    rw [H.comm r', dNext_eq _ (show (ComplexShape.down ℤ).Rel r' (r' - 1) by simp),
      prevD_eq _ h, zero_f, add_zero]
    abel
  rw [hTop_eq H r' _ rfl, hTop_eq H (r' - 1) r' (by omega), assoc, hc]
  simp only [dualComplex_d, comp_sub, Linear.units_smul_comp, Linear.comp_units_smul,
    XIsoOfEq_star_d_assoc D (show N + 1 - r' = N - (r' - 1) by omega)
      (show N + 1 - (r' + 1) = N - r' by omega)]
  rw [Int.negOnePow_succ, Units.neg_smul]
  abel

/-- A symmetric null-homotopy gives a strictly symmetric top structure in dimension `N + 1`
(`relTop_transpose` for arbitrary `f`). -/
lemma hTop_transpose (H : Homotopy f 0) (hH : IsSymmHomotopy J N H) (r : ℤ) :
    (r * (N + 1 - r)).negOnePow •
      (J.star (hTop H (N + 1 - r)) ≫ eqToHom (congrArg D.X (sub_sub_cancel (N + 1) r))) =
      hTop H r := by
  rw [IsSymmHomotopy, transposeHomotopy_hom] at hH
  have h := congrFun (congrFun hH (r - 1)) r
  rw [hTop_eq H (N - r) (N + 1 - r) (by omega), hTop, ← h]
  simp only [transposeHomFamily, bidual_hom_f, J.star_comp, XIsoOfEq, eqToIso.hom, star_eqToHom,
    Linear.comp_units_smul, smul_smul, assoc, eqToHom_trans]
  rw [eqToHom_comp_star_homotopy_hom_assoc H _ _ _ (by omega : N + 1 - r = N - (r - 1)),
    ← Int.negOnePow_add]
  congr 1
  exact negOnePow_eq_of_eq 0 (by ring)

/-- `hTop` symmetry with general indices: `(δφ_a)^* = ± δφ_s` for `a + s = N + 1`. -/
lemma star_hTop (H : Homotopy f 0) (hH : IsSymmHomotopy J N H) (a s : ℤ) (h : a + s = N + 1) :
    J.star (hTop H a) = (s * (N + 1 - s)).negOnePow •
      ((D.XIsoOfEq (by omega : a = N + 1 - s)).hom ≫ hTop H s ≫
        (D.XIsoOfEq (by omega : s = N + 1 - a)).hom) := by
  obtain rfl : a = N + 1 - s := by omega
  rw [← hTop_transpose H hH s]
  simp only [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul, Int.units_mul_self,
    one_smul, XIsoOfEq, eqToIso.hom, eqToHom_trans, eqToHom_refl, id_comp, assoc, comp_id]

lemma relTop_eq_hTop {B : ChainComplex V ℤ} {j : B ⟶ D} {φ : dualComplex J N B ⟶ B}
    (H : Homotopy (dualHom J N j ≫ φ ≫ j) 0) : relTop H = hTop H := rfl

end HTop

section CastLemmas

variable {K L : ChainComplex V ℤ}

/-- A cast on the source side is absorbed by a dual differential. -/
@[reassoc (attr := simp)]
lemma XIsoOfEq_hom_comp_star_d (K : ChainComplex V ℤ) {b b' : ℤ} (h : b = b') (a : ℤ) :
    (K.XIsoOfEq h).hom ≫ J.star (K.d a b') = J.star (K.d a b) := by
  subst h; simp

lemma negOnePow_sub_one (r : ℤ) : (r - 1).negOnePow = -r.negOnePow := by
  rw [Int.negOnePow_sub, Int.negOnePow_one]; simp

/-- `f^* d^* = d^* f^*` for a chain map `f`. -/
@[reassoc]
lemma star_f_star_d (f : K ⟶ L) (a b : ℤ) :
    J.star (f.f b) ≫ J.star (K.d a b) = J.star (L.d a b) ≫ J.star (f.f a) := by
  rw [← J.star_comp, ← J.star_comp, f.comm]

@[simp]
lemma star_XIsoOfEq_hom' (K : ChainComplex V ℤ) {a b : ℤ} (h : a = b) :
    J.star (K.XIsoOfEq h).hom = (K.XIsoOfEq h.symm).hom := by
  subst h; simp

/-- Strict symmetry with general indices: `φ_a^* = ± φ_s` for `a + s = N`. -/
lemma star_φ_f_eq {C : ChainComplex V ℤ} {φ : dualComplex J N C ⟶ C} (hφ : IsStrictSymm J N φ)
    (a s : ℤ) (h : a + s = N) :
    J.star (φ.f a) = (s * (N - s)).negOnePow •
      ((C.XIsoOfEq (by omega : a = N - s)).hom ≫ φ.f s ≫
        (C.XIsoOfEq (by omega : s = N - a)).hom) := by
  obtain rfl : a = N - s := by omega
  have hs := congrArg (fun g ↦ g.f s) hφ
  simp only [transposeHom_f] at hs
  rw [← hs]
  simp only [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul, Int.units_mul_self,
    one_smul, XIsoOfEq, eqToIso.hom, eqToHom_trans, eqToHom_refl, id_comp, assoc, comp_id]

@[reassoc]
lemma XIsoOfEq_comp_f_comp_eqToHom (f : K ⟶ L) {n n' : ℤ} (h : n = n') (h' : L.X n' = L.X n) :
    (K.XIsoOfEq h).hom ≫ f.f n' ≫ eqToHom h' = f.f n := by
  subst h; simp

end CastLemmas

section ConeHelpers

variable [HasBinaryBiproducts V] {B D B' D' : ChainComplex V ℤ} {j : B ⟶ D} {j' : B' ⟶ D'}
  {m : B ⟶ B'} {n : D ⟶ D'} (hmn : m ≫ j' = j ≫ n)

@[reassoc (attr := simp)]
lemma star_fstX_comp_star_coneMap_f (i k : ℤ) (hk : (ComplexShape.down ℤ).Rel i k) :
    J.star (fstX j' i k hk) ≫ J.star ((coneMap m n hmn).f i) =
      J.star (m.f k) ≫ J.star (fstX j i k hk) := by
  rw [← J.star_comp, ← J.star_comp, coneMap_f_fstX]

@[reassoc (attr := simp)]
lemma star_sndX_comp_star_coneMap_f (i : ℤ) :
    J.star (sndX j' i) ≫ J.star ((coneMap m n hmn).f i) = J.star (n.f i) ≫ J.star (sndX j i) := by
  rw [← J.star_comp, ← J.star_comp, coneMap_f_sndX]

lemma coneMap_eq_of_eq {m' : B ⟶ B'} {n' : D ⟶ D'} (h' : m' ≫ j' = j ≫ n') (hm : m = m')
    (hn : n = n') : coneMap m n hmn = coneMap m' n' h' := by
  subst hm hn; rfl

end ConeHelpers

/-- A map between Kar-contractible complexes (both idempotents null-homotopic) is a Kar
equivalence. -/
lemma isKarEquiv_of_contractible {X Y : ChainComplex V ℤ} {e : X ⟶ X} {e' : Y ⟶ Y} (f : X ⟶ Y)
    (he : Homotopy e 0) (he' : Homotopy e' 0) : IsKarEquiv e e' f :=
  ⟨0, by simp, ⟨homotopyCongr he'.symm (by simp) rfl⟩, ⟨homotopyCongr he.symm (by simp) rfl⟩⟩

/-! ### Symmetric pairs on a fixed boundary, not necessarily Poincaré -/

/-- A strictly symmetric `(N+1)`-dimensional pair structure `(j : C ⟶ D, (δφ, φ))` on a fixed
`N`-dimensional Poincaré boundary `P = (C, φ)`, **not** necessarily Poincaré: the fields of
`PairOn P` without `poincare`.  These are the faces of a symmetric triad. -/
structure PairData (P : SymPoincare J N) where
  D : ChainComplex V ℤ
  pD : D ⟶ D
  pD_idem : pD ≫ pD = pD
  support : SupportedIn pD 0 (N + 1)
  j : P.C ⟶ D
  j_kar : P.p ≫ j ≫ pD = j
  δφ : Homotopy (dualHom J N j ≫ P.φ ≫ j) 0
  δφ_kar : ∀ r r', (dualHom J N pD).f r ≫ δφ.hom r r' ≫ pD.f r' = δφ.hom r r'
  symm : IsSymmHomotopy J N δφ

namespace PairData

variable {P : SymPoincare J N} (X : PairData P)

attribute [reassoc (attr := simp)] pD_idem

@[reassoc (attr := simp)]
lemma p_comp_j : P.p ≫ X.j = X.j := kar_left P.p_idem X.j_kar

@[reassoc (attr := simp)]
lemma j_comp_pD : X.j ≫ X.pD = X.j := kar_right X.pD_idem X.j_kar

@[reassoc (attr := simp)]
lemma p_f_comp_j_f (r : ℤ) : P.p.f r ≫ X.j.f r = X.j.f r := by rw [← comp_f, X.p_comp_j]

@[reassoc (attr := simp)]
lemma j_f_comp_pD_f (r : ℤ) : X.j.f r ≫ X.pD.f r = X.j.f r := by rw [← comp_f, X.j_comp_pD]

@[reassoc (attr := simp)]
lemma star_pD_f_comp_star_j_f (r : ℤ) :
    J.star (X.pD.f r) ≫ J.star (X.j.f r) = J.star (X.j.f r) := by
  rw [← J.star_comp, X.j_f_comp_pD_f]

lemma dualHom_pD_comp_δφ_hom (r r' : ℤ) :
    (dualHom J N X.pD).f r ≫ X.δφ.hom r r' = X.δφ.hom r r' := by
  conv_lhs => rw [← X.δφ_kar]
  rw [← assoc, ← comp_f, ← dualHom_comp, X.pD_idem, X.δφ_kar]

lemma δφ_hom_comp_pD (r r' : ℤ) : X.δφ.hom r r' ≫ X.pD.f r' = X.δφ.hom r r' := by
  conv_lhs => rw [← X.δφ_kar]
  rw [assoc, assoc, ← comp_f, X.pD_idem, X.δφ_kar]

@[reassoc (attr := simp)]
lemma star_pD_comp_relTop (r : ℤ) :
    J.star (X.pD.f (N + 1 - r)) ≫ relTop X.δφ r = relTop X.δφ r :=
  star_comp_relTop X.δφ X.dualHom_pD_comp_δφ_hom r

@[reassoc (attr := simp)]
lemma relTop_comp_pD (r : ℤ) : relTop X.δφ r ≫ X.pD.f r = relTop X.δφ r := by
  simp [relTop, X.δφ_hom_comp_pD]

variable [HasBinaryBiproducts V]

/-- A Poincaré pair on `P`, as pair data. -/
@[simps]
def ofPairOn (Y : PairOn P) : PairData P :=
  ⟨Y.D, Y.pD, Y.pD_idem, Y.support, Y.j, Y.j_kar, Y.δφ, Y.δφ_kar, Y.symm⟩

/-- The Kar idempotent `p_C ⊕ p_D` of `Cone(j)`. -/
abbrev coneIdem : cone X.j ⟶ cone X.j :=
  coneMap P.p X.pD (comm_of_kar P.p_idem X.pD_idem X.j_kar)

lemma coneIdem_idem : X.coneIdem ≫ X.coneIdem = X.coneIdem :=
  coneMap_idem _ P.p_idem X.pD_idem

/-- The pair is **Poincaré**: its relative duality map `Ψ : Cone(j)^{N+1-*} ⟶ D` is a Kar
homotopy equivalence (the `poincare` field of `SymPair`). -/
def IsPoincare : Prop :=
  IsKarEquiv (dualHom J (N + 1) X.coneIdem) X.pD (relDuality X.δφ)

/-- A Poincaré pair datum is a Poincaré pair on `P`. -/
@[simps]
def toPairOn (h : X.IsPoincare) : PairOn P :=
  ⟨X.D, X.pD, X.pD_idem, X.support, X.j, X.j_kar, X.δφ, X.δφ_kar, X.symm, h⟩

lemma isPoincare_ofPairOn (Y : PairOn P) : (ofPairOn Y).IsPoincare := Y.poincare

@[simp]
lemma toPairOn_ofPairOn (Y : PairOn P) : (ofPairOn Y).toPairOn (isPoincare_ofPairOn Y) = Y := rfl

@[simp]
lemma ofPairOn_toPairOn (h : X.IsPoincare) : ofPairOn (X.toPairOn h) = X := rfl

end PairData

namespace PairData

variable {P : SymPoincare J N} (X : PairData P)

/-- The relative structure pushed along `i : D ⟶ E`: `i δφ i^*` on `j ≫ i`. -/
def push {E : ChainComplex V ℤ} (i : X.D ⟶ E) :
    Homotopy (dualHom J N (X.j ≫ i) ≫ P.φ ≫ X.j ≫ i) 0 :=
  homotopyCongr ((X.δφ.compRight i).compLeft (dualHom J N i)) (by simp) (by simp)

@[simp]
lemma push_hom {E : ChainComplex V ℤ} (i : X.D ⟶ E) (r r' : ℤ) :
    (X.push i).hom r r' = (dualHom J N i).f r ≫ X.δφ.hom r r' ≫ i.f r' := rfl

lemma relTop_push {E : ChainComplex V ℤ} (i : X.D ⟶ E) (r : ℤ) :
    relTop (X.push i) r = J.star (i.f (N + 1 - r)) ≫ relTop X.δφ r ≫ i.f r := by
  simp only [relTop, push_hom, dualHom_f, assoc, star_f_XIsoOfEq_assoc]

end PairData

/-- The closed `(N+1)`-dimensional structure `θ = i₀ δφ₀ i₀^* - i₁ δφ₁ i₁^* : E^{N+1-*} ⟶ E`
(the union structure `δφ₀ ∪_φ -δφ₁` of `∂₀C ∪_{∂₀₁C} ∂₁C`, pushed into the top `E`; a chain map
since `j₀ i₀ = j₁ i₁`). -/
def triadCycle {P : SymPoincare J N} (X₀ X₁ : PairData P) {E : ChainComplex V ℤ}
    (i₀ : X₀.D ⟶ E) (i₁ : X₁.D ⟶ E) (h : X₀.j ≫ i₀ = X₁.j ≫ i₁) :
    dualComplex J (N + 1) E ⟶ E :=
  relTopDiff (X₀.push i₀) (homotopyCongr (X₁.push i₁) (by rw [h]) rfl)

lemma triadCycle_f {P : SymPoincare J N} (X₀ X₁ : PairData P) {E : ChainComplex V ℤ}
    (i₀ : X₀.D ⟶ E) (i₁ : X₁.D ⟶ E) (h : X₀.j ≫ i₀ = X₁.j ≫ i₁) (r : ℤ) :
    (triadCycle X₀ X₁ i₀ i₁ h).f r =
      J.star (i₀.f (N + 1 - r)) ≫ relTop X₀.δφ r ≫ i₀.f r -
        J.star (i₁.f (N + 1 - r)) ≫ relTop X₁.δφ r ≫ i₁.f r := by
  rw [triadCycle, relTopDiff_f, ← X₀.relTop_push, ← X₁.relTop_push]
  rfl

/-- An `(N+2)`-dimensional **strictly symmetric triad** in `Kar V` with prescribed faces
(Ranicki's triad with a strictly commuting square, cf. [Ran81, §1.3], [Ran92, §1]):

```
  ∂₀₁C ──j₀──▶ ∂₀C
   │j₁          │i₀
   ▼            ▼
  ∂₁C ──i₁──▶   E
```

`P = ∂₀₁C` is an `N`-dimensional Poincaré complex, `X₀ = (j₀ : C ⟶ ∂₀C, (δφ₀, φ))` and
`X₁ = (j₁ : C ⟶ ∂₁C, (δφ₁, φ))` are `(N+1)`-dimensional symmetric pairs on `P` (not necessarily
Poincaré), `(E, p_E)` is concentrated in `[0, N+2]`, `j₀ i₀ = j₁ i₁`, and `δφ` is the top
structure: `δφ : θ ≃ 0` for `θ = i₀ δφ₀ i₀^* - i₁ δφ₁ i₁^*` (`triadCycle`), strictly symmetric
(`T δφ = δφ` in dimension `N+2`) and Kar.  Orientation: `∂E = ∂₀C ∪_{∂₀₁C} -∂₁C`, so a Poincaré
triad is a cobordism rel `∂₀₁C` from `X₀` to `X₁`. -/
structure TriadOn {P : SymPoincare J N} (X₀ X₁ : PairData P) where
  E : ChainComplex V ℤ
  pE : E ⟶ E
  pE_idem : pE ≫ pE = pE
  support : SupportedIn pE 0 (N + 1 + 1)
  i₀ : X₀.D ⟶ E
  i₀_kar : X₀.pD ≫ i₀ ≫ pE = i₀
  i₁ : X₁.D ⟶ E
  i₁_kar : X₁.pD ≫ i₁ ≫ pE = i₁
  comm : X₀.j ≫ i₀ = X₁.j ≫ i₁
  δφ : Homotopy (triadCycle X₀ X₁ i₀ i₁ comm) 0
  δφ_kar : ∀ r r', (dualHom J (N + 1) pE).f r ≫ δφ.hom r r' ≫ pE.f r' = δφ.hom r r'
  symm : IsSymmHomotopy J (N + 1) δφ

namespace TriadOn

variable {P : SymPoincare J N} {X₀ X₁ : PairData P} (T : TriadOn X₀ X₁)

attribute [reassoc (attr := simp)] pE_idem

@[reassoc (attr := simp)]
lemma pD_comp_i₀ : X₀.pD ≫ T.i₀ = T.i₀ := kar_left X₀.pD_idem T.i₀_kar

@[reassoc (attr := simp)]
lemma i₀_comp_pE : T.i₀ ≫ T.pE = T.i₀ := kar_right T.pE_idem T.i₀_kar

@[reassoc (attr := simp)]
lemma pD_comp_i₁ : X₁.pD ≫ T.i₁ = T.i₁ := kar_left X₁.pD_idem T.i₁_kar

@[reassoc (attr := simp)]
lemma i₁_comp_pE : T.i₁ ≫ T.pE = T.i₁ := kar_right T.pE_idem T.i₁_kar

@[reassoc]
lemma comm_f (r : ℤ) : X₀.j.f r ≫ T.i₀.f r = X₁.j.f r ≫ T.i₁.f r := by
  rw [← comp_f, T.comm, comp_f]

/-- The top component `δφ_r : E^{N+2-r} ⟶ E_r` of the top structure. -/
abbrev top (r : ℤ) : T.E.X (N + 1 + 1 - r) ⟶ T.E.X r := hTop T.δφ r

/-- The relative cycle condition of the top: `δφ_r d = δ δφ_{r-1} + θ_{r-1}`. -/
lemma top_comm (r r' : ℤ) (h : (ComplexShape.down ℤ).Rel r r') :
    T.top r ≫ T.E.d r r' = ((dualComplex J (N + 1 + 1) T.E).d r r' ≫ T.top r' :
      T.E.X (N + 1 + 1 - r) ⟶ T.E.X r') +
      (T.E.XIsoOfEq (by simp only [ComplexShape.down_Rel] at h; omega :
        N + 1 + 1 - r = N + 1 - r')).hom ≫
        (triadCycle X₀ X₁ T.i₀ T.i₁ T.comm).f r' :=
  hTop_comm T.δφ r r' h

variable [HasBinaryBiproducts V]

/-- The Kar idempotent `p₀ ⊕ p_E` of `Cone(i₀)`. -/
abbrev coneIdem₀ : cone T.i₀ ⟶ cone T.i₀ :=
  coneMap X₀.pD T.pE (comm_of_kar X₀.pD_idem T.pE_idem T.i₀_kar)

/-- The Kar idempotent `p₁ ⊕ p_E` of `Cone(i₁)`. -/
abbrev coneIdem₁ : cone T.i₁ ⟶ cone T.i₁ :=
  coneMap X₁.pD T.pE (comm_of_kar X₁.pD_idem T.pE_idem T.i₁_kar)

/-- The components of the relative duality map `Ψ`. -/
def ΨF (r : ℤ) : (dualComplex J (N + 1 + 1) (cone T.i₀)).X r ⟶ (cone T.i₁).X r :=
  J.star (inrX T.i₀ (N + 1 + 1 - r)) ≫ (T.top r ≫ inrX T.i₁ r +
      J.star (T.i₁.f (N + 1 + 1 - r)) ≫
        (X₁.D.XIsoOfEq (by omega : N + 1 + 1 - r = N + 1 - (r - 1))).hom ≫
          relTop X₁.δφ (r - 1) ≫ inlX T.i₁ (r - 1) r (down_rel_pred r)) +
    J.star (inlX T.i₀ (N + 1 - r) (N + 1 + 1 - r) (down_rel_sub (N + 1) r)) ≫
      ((r + 1).negOnePow • (relTop X₀.δφ r ≫ T.i₀.f r ≫ inrX T.i₁ r) +
        r.negOnePow • (J.star (X₀.j.f (N + 1 - r)) ≫
          (P.C.XIsoOfEq (by omega : N + 1 - r = N - (r - 1))).hom ≫ P.φ.f (r - 1) ≫
            X₁.j.f (r - 1) ≫ inlX T.i₁ (r - 1) r (down_rel_pred r)))

@[reassoc (attr := simp)]
lemma star_sndX_ΨF (r : ℤ) :
    J.star (sndX T.i₀ (N + 1 + 1 - r)) ≫ T.ΨF r = T.top r ≫ inrX T.i₁ r +
      J.star (T.i₁.f (N + 1 + 1 - r)) ≫
        (X₁.D.XIsoOfEq (by omega : N + 1 + 1 - r = N + 1 - (r - 1))).hom ≫
          relTop X₁.δφ (r - 1) ≫ inlX T.i₁ (r - 1) r (down_rel_pred r) := by
  simp [ΨF]

@[reassoc (attr := simp)]
lemma star_fstX_ΨF (r k : ℤ) (hk : (ComplexShape.down ℤ).Rel (N + 1 + 1 - r) k) :
    J.star (fstX T.i₀ (N + 1 + 1 - r) k hk) ≫ T.ΨF r =
      (X₀.D.XIsoOfEq (by simp at hk; omega : k = N + 1 - r)).hom ≫
      ((r + 1).negOnePow • (relTop X₀.δφ r ≫ T.i₀.f r ≫ inrX T.i₁ r) +
        r.negOnePow • (J.star (X₀.j.f (N + 1 - r)) ≫
          (P.C.XIsoOfEq (by omega : N + 1 - r = N - (r - 1))).hom ≫ P.φ.f (r - 1) ≫
            X₁.j.f (r - 1) ≫ inlX T.i₁ (r - 1) r (down_rel_pred r))) := by
  obtain rfl : k = N + 1 - r := by simp at hk; omega
  simp [ΨF]

omit [HasBinaryBiproducts V] in
@[reassoc (attr := simp)]
lemma pD_f_comp_i₀_f (r : ℤ) : X₀.pD.f r ≫ T.i₀.f r = T.i₀.f r := by rw [← comp_f, T.pD_comp_i₀]

omit [HasBinaryBiproducts V] in
@[reassoc (attr := simp)]
lemma i₀_f_comp_pE_f (r : ℤ) : T.i₀.f r ≫ T.pE.f r = T.i₀.f r := by rw [← comp_f, T.i₀_comp_pE]

omit [HasBinaryBiproducts V] in
@[reassoc (attr := simp)]
lemma pD_f_comp_i₁_f (r : ℤ) : X₁.pD.f r ≫ T.i₁.f r = T.i₁.f r := by rw [← comp_f, T.pD_comp_i₁]

omit [HasBinaryBiproducts V] in
@[reassoc (attr := simp)]
lemma i₁_f_comp_pE_f (r : ℤ) : T.i₁.f r ≫ T.pE.f r = T.i₁.f r := by rw [← comp_f, T.i₁_comp_pE]

omit [HasBinaryBiproducts V] in
@[reassoc (attr := simp)]
lemma star_pE_f_comp_star_i₀_f (r : ℤ) :
    J.star (T.pE.f r) ≫ J.star (T.i₀.f r) = J.star (T.i₀.f r) := by
  rw [← J.star_comp, T.i₀_f_comp_pE_f]

omit [HasBinaryBiproducts V] in
@[reassoc (attr := simp)]
lemma star_pE_f_comp_star_i₁_f (r : ℤ) :
    J.star (T.pE.f r) ≫ J.star (T.i₁.f r) = J.star (T.i₁.f r) := by
  rw [← J.star_comp, T.i₁_f_comp_pE_f]

omit [HasBinaryBiproducts V] in
lemma dualHom_pE_comp_δφ_hom (r r' : ℤ) :
    (dualHom J (N + 1) T.pE).f r ≫ T.δφ.hom r r' = T.δφ.hom r r' := by
  conv_lhs => rw [← T.δφ_kar]
  rw [← assoc, ← comp_f, ← dualHom_comp, T.pE_idem, T.δφ_kar]

omit [HasBinaryBiproducts V] in
lemma δφ_hom_comp_pE (r r' : ℤ) : T.δφ.hom r r' ≫ T.pE.f r' = T.δφ.hom r r' := by
  conv_lhs => rw [← T.δφ_kar]
  rw [assoc, assoc, ← comp_f, T.pE_idem, T.δφ_kar]

omit [HasBinaryBiproducts V] in
@[reassoc (attr := simp)]
lemma star_pE_comp_top (r : ℤ) : J.star (T.pE.f (N + 1 + 1 - r)) ≫ T.top r = T.top r := by
  rw [top, hTop, star_f_XIsoOfEq_assoc, ← dualHom_f, T.dualHom_pE_comp_δφ_hom]

omit [HasBinaryBiproducts V] in
@[reassoc (attr := simp)]
lemma top_comp_pE (r : ℤ) : T.top r ≫ T.pE.f r = T.top r := by
  rw [top, hTop, assoc, T.δφ_hom_comp_pE]

omit [HasBinaryBiproducts V] in
@[reassoc]
lemma star_i₁_star_j₁ (x : ℤ) : J.star (T.i₁.f x) ≫ J.star (X₁.j.f x) =
    J.star (T.i₀.f x) ≫ J.star (X₀.j.f x) := by
  rw [← J.star_comp, ← J.star_comp, T.comm_f]

lemma ΨF_comm (r r' : ℤ) (h : (ComplexShape.down ℤ).Rel r r') :
    T.ΨF r ≫ (cone T.i₁).d r r' = (dualComplex J (N + 1 + 1) (cone T.i₀)).d r r' ≫ T.ΨF r' := by
  obtain rfl : r' = r - 1 := by simp only [ComplexShape.down_Rel] at h; omega
  have hi : (ComplexShape.down ℤ).Rel (N + 1 + 1 - (r - 1)) (N + 1 + 1 - r) := by
    simp only [ComplexShape.down_Rel]; omega
  have hφ := P.φ.comm (r - 1) (r - 1 - 1)
  have h₀ := relTop_comm X₀.δφ r (r - 1) h
  have h₁ := relTop_comm X₁.δφ (r - 1) (r - 1 - 1) (down_rel_pred (r - 1))
  have hT := T.top_comm r (r - 1) h
  simp only [dualComplex_d, triadCycle_f, comp_f, dualHom_f] at hφ h₀ h₁ hT
  apply cone.ext_star (J := J) T.i₀ (N + 1 + 1 - r) (N + 1 - r) (down_rel_sub (N + 1) r)
  · apply ext_to_X T.i₁ (r - 1) (r - 1 - 1) (down_rel_pred (r - 1))
    · simp only [assoc, dualComplex_d, Linear.units_smul_comp, Linear.comp_units_smul,
        cone.star_fstX_d_assoc T.i₀ _ _ _ hi, star_fstX_ΨF_assoc]
      simp only [homotopyCofiber_d, d_fstX T.i₁ r (r - 1) (r - 1 - 1) h (down_rel_pred (r - 1)),
        neg_comp, comp_neg, assoc, star_fstX_ΨF_assoc, add_comp, Linear.units_smul_comp,
        Linear.comp_units_smul, inrX_fstX_assoc, inlX_fstX_assoc, inrX_fstX, inlX_fstX, zero_comp,
        comp_zero, smul_zero, zero_add, smul_neg, comp_id, Hom.comm, reassoc_of% hφ, XIsoOfEq_rfl,
        Iso.refl_hom, id_comp]
      simp only [XIsoOfEq_hom_comp_star_d_assoc, star_f_star_d_assoc, star_f_XIsoOfEq_assoc,
        XIsoOfEq_hom_comp_XIsoOfEq_hom_assoc, star_d_XIsoOfEq_assoc]
    · simp only [assoc, dualComplex_d, Linear.units_smul_comp, Linear.comp_units_smul,
        cone.star_fstX_d_assoc T.i₀ _ _ _ hi, star_fstX_ΨF_assoc]
      simp only [homotopyCofiber_d, d_sndX T.i₁ r (r - 1) h, neg_comp, assoc, star_fstX_ΨF_assoc,
        add_comp, comp_add, Linear.units_smul_comp, Linear.comp_units_smul, inrX_fstX_assoc,
        inlX_fstX_assoc, inrX_sndX, inlX_sndX, inrX_sndX_assoc, inlX_sndX_assoc, zero_comp,
        comp_zero, smul_zero, zero_add, add_zero, smul_neg, comp_id, Hom.comm, reassoc_of% h₀,
        XIsoOfEq_rfl, Iso.refl_hom, id_comp, ← T.comm_f]
      simp only [star_f_XIsoOfEq_assoc, star_d_XIsoOfEq_assoc, Int.negOnePow_succ, sub_add_cancel,
        smul_smul, neg_mul, Int.units_mul_self, one_smul, Units.neg_smul, smul_add]
      abel
  · apply ext_to_X T.i₁ (r - 1) (r - 1 - 1) (down_rel_pred (r - 1))
    · simp only [assoc, dualComplex_d, Linear.units_smul_comp, Linear.comp_units_smul,
        cone.star_sndX_d_assoc T.i₀ _ _ hi, star_sndX_ΨF_assoc]
      simp only [homotopyCofiber_d, d_fstX T.i₁ r (r - 1) (r - 1 - 1) h (down_rel_pred (r - 1)),
        comp_neg, assoc, star_fstX_ΨF_assoc, star_sndX_ΨF_assoc, add_comp, comp_add,
        Linear.units_smul_comp, Linear.comp_units_smul, inrX_fstX_assoc, inlX_fstX_assoc, inrX_fstX,
        inlX_fstX, zero_comp, comp_zero, smul_zero, zero_add, comp_id, h₁]
      simp only [XIsoOfEq_hom_comp_star_d_assoc, star_f_star_d_assoc, star_f_XIsoOfEq_assoc,
        XIsoOfEq_hom_comp_XIsoOfEq_hom_assoc, star_d_XIsoOfEq_assoc, star_i₁_star_j₁_assoc,
        negOnePow_sub_one, smul_smul, Int.units_mul_self, one_smul, Units.neg_smul, smul_neg,
        smul_add]
      abel
    · simp only [assoc, dualComplex_d, Linear.units_smul_comp, Linear.comp_units_smul,
        cone.star_sndX_d_assoc T.i₀ _ _ hi, star_sndX_ΨF_assoc]
      simp only [homotopyCofiber_d, d_sndX T.i₁ r (r - 1) h, assoc, star_fstX_ΨF_assoc,
        star_sndX_ΨF_assoc, add_comp, comp_add, Linear.units_smul_comp, Linear.comp_units_smul,
        inrX_fstX_assoc, inlX_fstX_assoc, inrX_sndX, inlX_sndX, inrX_sndX_assoc, inlX_sndX_assoc,
        zero_comp, comp_zero, smul_zero, zero_add, add_zero, comp_id, hT]
      simp only [star_f_XIsoOfEq_assoc, sub_add_cancel, smul_smul, Int.units_mul_self, one_smul,
        smul_add, comp_sub]
      abel

/-- **The relative duality map of the triad** `Ψ : Cone(i₀)^{N+2-*} ⟶ Cone(i₁)`, the chain-level
cap product `H^{N+2-*}(E, ∂₀) ⟶ H_*(E, ∂₁)` with the fundamental class (the duality of the map of
pairs `(∂₀₁C ⟶ ∂₀C) ⟶ (∂₁C ⟶ E)`).  In the coordinates `(α, β) ∈ ∂₀C^{N+1-r} ⊕ E^{N+2-r}` of
`Cone(i₀)^{N+2-r}` and `(x, y) ∈ ∂₁C_{r-1} ⊕ E_r` of `Cone(i₁)_r`:
`Ψ(α, β) = (i₁^* δφ₁ β + (-1)^r j₁ φ j₀^* α, δφ β + (-1)^{r+1} i₀ δφ₀ α)`. -/
def Ψ : dualComplex J (N + 1 + 1) (cone T.i₀) ⟶ cone T.i₁ where
  f := T.ΨF
  comm' r r' h := T.ΨF_comm r r' h

@[simp]
lemma Ψ_f (r : ℤ) : T.Ψ.f r = T.ΨF r := rfl

/-- `Ψ` is a Kar morphism `(Cone(i₀)^{N+2-*}, (p₀ ⊕ p_E)^*) ⟶ (Cone(i₁), p₁ ⊕ p_E)`. -/
lemma Ψ_kar : dualHom J (N + 1 + 1) T.coneIdem₀ ≫ T.Ψ ≫ T.coneIdem₁ = T.Ψ := by
  have hφ (k : ℤ) {Z : V} (g : P.C.X k ⟶ Z) : P.φ.f k ≫ P.p.f k ≫ g = P.φ.f k ≫ g := by
    rw [← assoc, ← comp_f, P.φ_comp_p]
  ext r
  apply cone.ext_star (J := J) T.i₀ (N + 1 + 1 - r) (N + 1 - r) (down_rel_sub (N + 1) r)
  · apply ext_to_X T.i₁ r (r - 1) (down_rel_pred r) <;> simp
  · apply ext_to_X T.i₁ r (r - 1) (down_rel_pred r) <;> simp

/-- The top of the triad is **Poincaré**: `Ψ` is a Kar homotopy equivalence (with Poincaré
faces, this is equivalent to Ranicki's condition that the `(N+2)`-dimensional pair
`(∂₀C ∪_{∂₀₁C} ∂₁C ⟶ E)` is Poincaré, by two-out-of-three on the ladder of the triple
`(E, ∂E, ∂₀C)`; see the module docstring). -/
def IsPoincareTop : Prop :=
  IsKarEquiv (dualHom J (N + 1 + 1) T.coneIdem₀) T.coneIdem₁ T.Ψ

/-- A **Poincaré triad**: both faces are Poincaré pairs and the top is Poincaré. -/
structure IsPoincare : Prop where
  face₀ : X₀.IsPoincare
  face₁ : X₁.IsPoincare
  top : T.IsPoincareTop

variable {T}

/-- **The faces of a Poincaré triad are Poincaré pairs**: face `0`. -/
@[simps!]
def pair₀ (h : T.IsPoincare) : PairOn P := X₀.toPairOn h.face₀

/-- **The faces of a Poincaré triad are Poincaré pairs**: face `1`. -/
@[simps!]
def pair₁ (h : T.IsPoincare) : PairOn P := X₁.toPairOn h.face₁

/-- The common boundary `∂₀₁C` of a Poincaré triad is null-cobordant (by either face). -/
lemma nullCobordant_bd (h : T.IsPoincare) : NullCobordant P :=
  nullCobordant_iff_nonempty_pairOn.2 ⟨pair₁ h⟩

end TriadOn

/-! ### Degenerate triads -/

section Degenerate

variable [HasBinaryBiproducts V]

/-- The chain map `Cone(0 : B ⟶ D) ⟶ D`, `(x, y) ↦ y`. -/
@[simps]
def coneZeroSnd (B D : ChainComplex V ℤ) : cone (0 : B ⟶ D) ⟶ D where
  f n := sndX (0 : B ⟶ D) n
  comm' n n' h := by simp [d_sndX (0 : B ⟶ D) n n' h]

@[reassoc (attr := simp)]
lemma inr_comp_coneZeroSnd (B D : ChainComplex V ℤ) : inr (0 : B ⟶ D) ≫ coneZeroSnd B D = 𝟙 D := by
  ext n; simp

/-- For the cone of a zero map, the Kar idempotent `0 ⊕ p` factors through `D`. -/
lemma coneMap_zero_eq {B D : ChainComplex V ℤ} (p : D ⟶ D) :
    coneMap (j := (0 : B ⟶ D)) (j' := (0 : B ⟶ D)) 0 p (by simp) =
      coneZeroSnd B D ≫ p ≫ inr (0 : B ⟶ D) := by
  ext n
  rw [coneMap_f _ n (n - 1) (down_rel_pred n)]
  simp

/-- `inr : (D, p) ⟶ (Cone(0 : B ⟶ D), 0 ⊕ p)` is a Kar isomorphism. -/
lemma isKarEquiv_inr_zero {B D : ChainComplex V ℤ} {p : D ⟶ D} (hp : p ≫ p = p) :
    IsKarEquiv p (coneMap (j := (0 : B ⟶ D)) (j' := (0 : B ⟶ D)) 0 p (by simp))
      (p ≫ inr (0 : B ⟶ D)) := by
  rw [coneMap_zero_eq]
  have hp' : p ≫ p ≫ inr (0 : B ⟶ D) = p ≫ inr (0 : B ⟶ D) := by rw [reassoc_of% hp]
  refine ⟨coneZeroSnd B D ≫ p, by simp [hp], ⟨Homotopy.ofEq ?_⟩, ⟨Homotopy.ofEq ?_⟩⟩
  · simp [hp']
  · simp [hp]

variable {P : SymPoincare J N}

namespace TriadOn

/-- **The cylinder** `X × I` rel `∂X` on a pair `X`: the triad `(D; X, X; C)` with
`i₀ = i₁ = p_D` and top structure `0` (`θ = δφ - δφ = 0`).  Its top is Poincaré for every `X`
(both cones are Kar-contractible), so it is a Poincaré triad iff `X` is a Poincaré pair. -/
@[simps]
def cylinder (X : PairData P) : TriadOn X X where
  E := X.D
  pE := X.pD
  pE_idem := X.pD_idem
  support := X.support.mono le_rfl (by omega)
  i₀ := X.pD
  i₀_kar := by simp
  i₁ := X.pD
  i₁_kar := by simp
  comm := rfl
  δφ := Homotopy.ofEq (by ext r; simp [triadCycle_f])
  δφ_kar r r' := by simp [Homotopy.ofEq]
  symm := by
    rw [IsSymmHomotopy, transposeHomotopy_hom]
    funext r r'
    simp [Homotopy.ofEq, transposeHomFamily]

/-- The Kar idempotent of `Cone(p_D)` is null-homotopic. -/
def coneIdemContraction (X : PairData P) :
    Homotopy (coneMap (j := X.pD) (j' := X.pD) X.pD X.pD (by simp)) 0 :=
  homotopyCongr (coneNullHomotopy X.pD X.pD X.pD)
    (coneMap_eq_of_eq _ _ (by simp) (by simp)) rfl

lemma cylinder_isPoincareTop (X : PairData P) : (cylinder X).IsPoincareTop :=
  isKarEquiv_of_contractible _
    (homotopyCongr (dualHomotopy J (N + 1 + 1) (coneIdemContraction X)) rfl (dualHom_zero _ _))
    (coneIdemContraction X)

lemma cylinder_isPoincare {X : PairData P} (h : X.IsPoincare) : (cylinder X).IsPoincare :=
  ⟨h, h, cylinder_isPoincareTop X⟩

end TriadOn

namespace PairData

/-- **The empty face** `(C ⟶ 0)`: the Kar complex `(C, 0)` (which is zero) with `j = 0` and
`δφ = 0`.  A triad with face `zero P` and top `E` is an `(N+2)`-dimensional pair `(∂₀C ⟶ E)` whose
boundary is the pair `(∂₀₁C ⟶ ∂₀C)` (the input shape of the relative boundary construction). -/
@[simps, implicit_reducible]
def zero (P : SymPoincare J N) : PairData P where
  D := P.C
  pD := 0
  pD_idem := by simp
  support _ _ := rfl
  j := 0
  j_kar := by simp
  δφ := Homotopy.ofEq (by simp)
  δφ_kar r r' := by simp [Homotopy.ofEq]
  symm := by
    rw [IsSymmHomotopy, transposeHomotopy_hom]
    funext r r'
    simp [Homotopy.ofEq, transposeHomFamily]

omit [HasBinaryBiproducts V] in
@[simp]
lemma relTop_zero_δφ (r : ℤ) : relTop (zero P).δφ r = 0 := by
  simp [relTop, Homotopy.ofEq]

/-- The empty face on a boundary with `p = 0` is a Poincaré pair. -/
lemma zero_isPoincare (hP : P.p = 0) : (zero P).IsPoincare := by
  have h0 : (zero P).coneIdem = 0 := by
    rw [coneIdem, ← coneMap_zero]
    exact coneMap_eq_of_eq _ _ hP rfl
  rw [IsPoincare, h0, dualHom_zero]
  exact ⟨0, by simp, ⟨Homotopy.ofEq (by simp)⟩, ⟨Homotopy.ofEq (by simp)⟩⟩

end PairData

namespace TriadOn

variable {X₀ : PairData P} {E : ChainComplex V ℤ} (i : X₀.D ⟶ E)

omit [HasBinaryBiproducts V] in
/-- The top cycle of a triad with empty second face is `i δφ₀ i^*`. -/
lemma triadCycle_zero_f (h : X₀.j ≫ i = (PairData.zero P).j ≫ 0) (r : ℤ) :
    (triadCycle X₀ (PairData.zero P) i 0 h).f r =
      J.star (i.f (N + 1 - r)) ≫ relTop X₀.δφ r ≫ i.f r := by
  simp [triadCycle_f]

omit [HasBinaryBiproducts V] in
/-- **An `(N+2)`-dimensional pair whose boundary is the pair `W`** ("relative pair", the input
shape of the relative boundary construction): the triad `(E; W, ∅; P)` with `i : ∂W ⟶ E`,
`j_W i = 0`, and top structure a family `H` with `i^* δφ_W i = δH + Hd` **on the nose** — the
output shape of the relative lift `LiftComplex.RelLift.Cascade` (`relH_comm`, `relH_symm`) for
`ψ = relTop δφ_W`. -/
def ofRel (pE : E ⟶ E) (hpE : pE ≫ pE = pE) (hs : SupportedIn pE 0 (N + 1 + 1))
    (hi_kar : X₀.pD ≫ i ≫ pE = i) (hi : X₀.j ≫ i = 0)
    (H : ∀ r r', (dualComplex J (N + 1) E).X r ⟶ E.X r')
    (H_shape : ∀ r r', ¬ (ComplexShape.down ℤ).Rel r' r → H r r' = 0)
    (H_comm : ∀ r, J.star (i.f (N + 1 - r)) ≫ relTop X₀.δφ r ≫ i.f r =
      (dualComplex J (N + 1) E).d r (r - 1) ≫ H (r - 1) r + H r (r + 1) ≫ E.d (r + 1) r)
    (H_kar : ∀ r r', (dualHom J (N + 1) pE).f r ≫ H r r' ≫ pE.f r' = H r r')
    (H_symm : transposeHomFamily J (N + 1) (C := E) (D := E) H = H) :
    TriadOn X₀ (PairData.zero P) where
  E := E
  pE := pE
  pE_idem := hpE
  support := hs
  i₀ := i
  i₀_kar := hi_kar
  i₁ := 0
  i₁_kar := by simp
  comm := by simp [hi]
  δφ :=
    { hom := H
      zero := H_shape
      comm r := by
        rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel r (r - 1) by simp),
          prevD_eq _ (show (ComplexShape.down ℤ).Rel (r + 1) r by simp), triadCycle_zero_f,
          H_comm r, zero_f, add_zero] }
  δφ_kar := H_kar
  symm := by rw [IsSymmHomotopy, transposeHomotopy_hom]; exact H_symm

omit [HasBinaryBiproducts V] in
@[simp]
lemma ofRel_i₀ (pE : E ⟶ E) (hpE hs hi_kar hi H H_shape H_comm H_kar H_symm) :
    (ofRel (X₀ := X₀) i pE hpE hs hi_kar hi H H_shape H_comm H_kar H_symm).i₀ = i := rfl

omit [HasBinaryBiproducts V] in
lemma ofRel_δφ_hom (pE : E ⟶ E) (hpE hs hi_kar hi H H_shape H_comm H_kar H_symm) :
    (ofRel (X₀ := X₀) i pE hpE hs hi_kar hi H H_shape H_comm H_kar H_symm).δφ.hom = H := rfl

end TriadOn

namespace PairData

omit [HasBinaryBiproducts V] in
/-- The relative structure of a closed complex `Q` viewed as a pair with empty boundary:
`δφ_{r-1, r} = φ_r` (cast). -/
def closedHom (Q : SymPoincare J (N + 1)) (i k : ℤ) : (dualComplex J N Q.C).X i ⟶ Q.C.X k :=
  if h : i + 1 = k then (Q.C.XIsoOfEq (by omega : N - i = N + 1 - k)).hom ≫ Q.φ.f k else 0

omit [HasBinaryBiproducts V] in
lemma closedHom_eq (Q : SymPoincare J (N + 1)) (i k : ℤ) (h : i + 1 = k) :
    closedHom Q i k = (Q.C.XIsoOfEq (by omega : N - i = N + 1 - k)).hom ≫ Q.φ.f k := dif_pos h

omit [HasBinaryBiproducts V] in
lemma closedHom_eq_zero (Q : SymPoincare J (N + 1)) (i k : ℤ) (h : ¬ i + 1 = k) :
    closedHom Q i k = 0 := dif_neg h

omit [HasBinaryBiproducts V] in
/-- `φ_a^*` commutes with casts of the index. -/
@[reassoc]
lemma star_φ_f_XIsoOfEq {M : ℤ} {C : ChainComplex V ℤ} (φ : dualComplex J M C ⟶ C) {a a' : ℤ}
    (h : a = a') (h' : M - a = M - a') :
    J.star (φ.f a) ≫ (C.XIsoOfEq h').hom = (C.XIsoOfEq h).hom ≫ J.star (φ.f a') := by
  subst h; simp

omit [HasBinaryBiproducts V] in
lemma closedHom_symm (Q : SymPoincare J (N + 1)) :
    transposeHomFamily J N (C := Q.C) (D := Q.C) (closedHom Q) = closedHom Q := by
  funext r k
  by_cases h : r + 1 = k
  · subst h
    have hs := congrArg (fun f ↦ f.f (r + 1)) Q.symm
    simp only [transposeHom_f] at hs
    conv_rhs => rw [closedHom_eq Q r (r + 1) rfl, ← hs]
    simp only [transposeHomFamily, closedHom_eq Q (N - (r + 1)) (N - r) (by omega), bidual_hom_f,
      J.star_comp, star_XIsoOfEq_hom', Linear.comp_units_smul, smul_smul, assoc]
    rw [← star_φ_f_XIsoOfEq_assoc Q.φ (by omega : N - r = N + 1 - (r + 1)) (by omega),
      ← Int.negOnePow_add]
    simp only [XIsoOfEq, eqToIso.hom, eqToHom_trans]
    congr 2
    ring
  · simp [transposeHomFamily, closedHom_eq_zero Q _ _ (by omega : ¬ N - k + 1 = N - r),
      closedHom_eq_zero Q r k h]

/-- **A closed `(N+1)`-dimensional complex `Q` as a pair with empty boundary**: the pair
`(0 : (C, 0) ⟶ (C, p), (φ, 0))` on the zero boundary `(C, 0, 0)`, whose relative structure is
`φ`.  It is a Poincaré pair (`isPoincare_ofClosed`). -/
@[simps, implicit_reducible]
def ofClosed (Q : SymPoincare J (N + 1)) : PairData (SymPoincare.zero (J := J) (N := N) Q.C) where
  D := Q.C
  pD := Q.p
  pD_idem := Q.p_idem
  support := Q.support
  j := 0
  j_kar := by simp
  δφ :=
    { hom := closedHom Q
      zero i k h := closedHom_eq_zero Q i k (by simp only [ComplexShape.down_Rel] at h; omega)
      comm i := by
        rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel i (i - 1) by simp),
          prevD_eq _ (show (ComplexShape.down ℤ).Rel (i + 1) i by simp),
          closedHom_eq Q (i - 1) i (by omega), closedHom_eq Q i (i + 1) rfl]
        have hφ := Q.φ.comm (i + 1) i
        simp only [dualComplex_d] at hφ
        simp only [SymPoincare.zero_φ, comp_zero, zero_f, add_zero, dualComplex_d, assoc,
          Linear.units_smul_comp, hφ, star_d_XIsoOfEq_assoc, Int.negOnePow_succ, Units.neg_smul,
          neg_comp, comp_neg, Linear.comp_units_smul, XIsoOfEq_hom_comp_star_d_assoc]
        abel }
  δφ_kar r k := by
    by_cases h : r + 1 = k
    · simp only [closedHom_eq Q r k h, dualHom_f, assoc, star_f_XIsoOfEq_assoc]
      rw [← assoc (J.star _), ← dualHom_f, ← comp_f, Q.dualHom_p_comp_φ, ← comp_f, Q.φ_comp_p]
    · simp [closedHom_eq_zero Q r k h]
  symm := by
    rw [IsSymmHomotopy, transposeHomotopy_hom]
    exact closedHom_symm Q

omit [HasBinaryBiproducts V] in
@[simp]
lemma relTop_ofClosed (Q : SymPoincare J (N + 1)) (r : ℤ) :
    relTop (ofClosed Q).δφ r = Q.φ.f r := by
  change (Q.C.XIsoOfEq (by omega : N + 1 - r = N - (r - 1))).hom ≫ closedHom Q (r - 1) r = _
  rw [closedHom_eq Q (r - 1) r (by omega)]
  simp

lemma relDuality_ofClosed (Q : SymPoincare J (N + 1)) :
    relDuality (ofClosed Q).δφ = dualHom J (N + 1) (inr (0 : Q.C ⟶ Q.C)) ≫ Q.φ := by
  ext r
  simp [relDuality_f]

/-- A closed Poincaré complex is a Poincaré pair with empty boundary. -/
theorem isPoincare_ofClosed (Q : SymPoincare J (N + 1)) : (ofClosed Q).IsPoincare := by
  rw [IsPoincare, relDuality_ofClosed]
  have hc : (ofClosed Q).coneIdem =
      coneMap (j := (0 : Q.C ⟶ Q.C)) (j' := (0 : Q.C ⟶ Q.C)) 0 Q.p (by simp) := rfl
  rw [hc]
  have h₁ := (isKarEquiv_inr_zero (B := Q.C) Q.p_idem).dualHom (J := J) (N := N + 1)
  refine (h₁.comp Q.poincare (dualHom_idem (coneMap_idem _ (by simp) Q.p_idem))
    (dualHom_idem Q.p_idem) Q.p_idem).of_eq ?_
  rw [dualHom_comp, assoc, Q.dualHom_p_comp_φ]

end PairData

namespace TriadOn

/-- **An `(N+2)`-dimensional pair as a triad** `(D; ∂D, ∅; ∅)` ("degenerate faces"): the
boundary `Y.bd` becomes the closed face `PairData.ofClosed Y.bd` on the zero `N`-dimensional
boundary, the second face is empty, `i₀ = j`, `i₁ = 0`, and the top structure is `δφ` itself
(`θ = j φ j^*`).  `Ψ = inr ∘ Ψ_Y` (`Ψ_ofPair`), so it is a Poincaré triad (`isPoincare_ofPair`). -/
@[implicit_reducible]
def ofPair (Y : SymPair J (N + 1)) :
    TriadOn (PairData.ofClosed Y.bd)
      (PairData.zero (SymPoincare.zero (J := J) (N := N) Y.bd.C)) where
  E := Y.D
  pE := Y.pD
  pE_idem := Y.pD_idem
  support := Y.support
  i₀ := Y.j
  i₀_kar := Y.j_kar
  i₁ := 0
  i₁_kar := by simp
  comm := by simp
  δφ := homotopyCongr Y.δφ (by ext r; simp [triadCycle_f]) rfl
  δφ_kar := Y.δφ_kar
  symm := Y.symm

@[simp]
lemma ofPair_E (Y : SymPair J (N + 1)) : (ofPair Y).E = Y.D := rfl

@[simp]
lemma ofPair_i₀ (Y : SymPair J (N + 1)) : (ofPair Y).i₀ = Y.j := rfl

@[simp]
lemma ofPair_i₁ (Y : SymPair J (N + 1)) : (ofPair Y).i₁ = 0 := rfl

@[simp]
lemma ofPair_pE (Y : SymPair J (N + 1)) : (ofPair Y).pE = Y.pD := rfl

@[simp]
lemma ofPair_top (Y : SymPair J (N + 1)) (r : ℤ) : (ofPair Y).top r = relTop Y.δφ r := rfl

lemma Ψ_ofPair (Y : SymPair J (N + 1)) :
    (ofPair Y).Ψ = relDuality Y.δφ ≫ inr (0 : Y.bd.C ⟶ Y.D) := by
  ext r
  simp [ΨF]

lemma ofPair_isPoincareTop (Y : SymPair J (N + 1)) : (ofPair Y).IsPoincareTop := by
  rw [IsPoincareTop, Ψ_ofPair]
  refine (Y.poincare.comp (isKarEquiv_inr_zero Y.pD_idem) Y.dualHom_coneIdem_idem Y.pD_idem
    (coneMap_idem _ (by simp) Y.pD_idem)).of_eq ?_
  rw [← assoc, Y.Ψ_comp_pD]

/-- **A Poincaré pair is a Poincaré triad** with degenerate faces. -/
theorem isPoincare_ofPair (Y : SymPair J (N + 1)) : (ofPair Y).IsPoincare :=
  ⟨PairData.isPoincare_ofClosed _, PairData.zero_isPoincare rfl, ofPair_isPoincareTop Y⟩

end TriadOn

end Degenerate

/-! ### Supports: pairs with objects in a full subcategory -/

section Lift

variable [HasBinaryBiproducts V] {U : ObjectProperty V} [IsAdditiveSub U]

/-- The inclusion of the full subcategory `U`, as a duality-preserving functor. -/
abbrev subInvIncl (J : StrictInvolution V) (U : ObjectProperty V) : InvFunctor (subInv J U) J :=
  ⟨U.ι, fun _ ↦ rfl⟩

omit [HasBinaryBiproducts V] [IsAdditiveSub U] in
/-- Kar equivalences are reflected by the inclusion of a full subcategory. -/
lemma isKarEquiv_of_map_ι {K L : ChainComplex U.FullSubcategory ℤ} {e : K ⟶ K} {e' : L ⟶ L}
    {f : K ⟶ L}
    (h : IsKarEquiv ((U.ι.mapHomologicalComplex _).map e) ((U.ι.mapHomologicalComplex _).map e')
      ((U.ι.mapHomologicalComplex _).map f)) : IsKarEquiv e e' f := by
  obtain ⟨g, hg, ⟨H₁⟩, ⟨H₂⟩⟩ := h
  refine ⟨liftHom g, ?_, ⟨liftHomotopy (homotopyCongr H₁ ?_ rfl)⟩,
    ⟨liftHomotopy (homotopyCongr H₂ ?_ rfl)⟩⟩
  · ext r; exact congrArg (fun φ ↦ φ.f r) hg
  · ext r; rfl
  · ext r; rfl

namespace SymPair

variable (X : SymPair J N) (hC : ∀ r, U (X.bd.C.X r)) (hD : ∀ r, U (X.D.X r))

/-- The lifted boundary map. -/
abbrev liftJ : liftComplex U X.bd.C hC ⟶ liftComplex U X.D hD := liftHom X.j

/-- The lifted relative structure. -/
def liftδφ :
    Homotopy (dualHom (subInv J U) N (X.liftJ hC hD) ≫ (X.bd.lift hC).φ ≫ X.liftJ hC hD) 0 :=
  liftHomotopy (homotopyCongr X.δφ (by ext r; rfl) (by ext r; rfl))

omit [IsAdditiveSub U] in
lemma liftδφ_hom (r r' : ℤ) : ((X.liftδφ hC hD).hom r r').hom = X.δφ.hom r r' := rfl

omit [IsAdditiveSub U] in
lemma relDuality_mapRel_liftδφ :
    relDuality ((subInvIncl J U).mapRel (X.liftδφ hC hD)) = relDuality X.δφ := by
  ext r
  simp [relDuality_f, relTop, liftδφ_hom]
  rfl

/-- The lifted idempotent of the top. -/
abbrev liftPD : liftComplex U X.D hD ⟶ liftComplex U X.D hD := liftHom X.pD

omit [IsAdditiveSub U] in
lemma liftPD_idem : X.liftPD hD ≫ X.liftPD hD = X.liftPD hD := by
  ext r; exact congrArg (fun f ↦ f.f r) X.pD_idem

omit [IsAdditiveSub U] in
lemma liftJ_kar : (X.bd.lift hC).p ≫ X.liftJ hC hD ≫ X.liftPD hD = X.liftJ hC hD := by
  ext r; exact congrArg (fun f ↦ f.f r) X.j_kar

lemma lift_poincare : IsKarEquiv (dualHom (subInv J U) (N + 1)
      (coneMap (X.bd.lift hC).p (X.liftPD hD)
        (comm_of_kar (X.bd.lift hC).p_idem (X.liftPD_idem hD) (X.liftJ_kar hC hD))))
      (X.liftPD hD) (relDuality (X.liftδφ hC hD)) := by
  apply isKarEquiv_of_map_ι
  let α := ((subInvIncl J U).mapDualIso (N + 1) (cone (X.liftJ hC hD))) ≪≫
    dualIso J (N + 1) (asIso ((subInvIncl J U).coneComparison (X.liftJ hC hD)))
  have h := X.poincare.conjIso α.symm
  convert h using 2
  · rfl
  · have e := (subInvIncl J U).coneComparison_comp_map_coneMap (X.liftJ hC hD)
      (comm_of_kar (X.bd.lift hC).p_idem (X.liftPD_idem hD) (X.liftJ_kar hC hD))
    have e' : (subInvIncl J U).mapH (coneMap (X.bd.lift hC).p (X.liftPD hD)
        (comm_of_kar (X.bd.lift hC).p_idem (X.liftPD_idem hD) (X.liftJ_kar hC hD))) =
        inv ((subInvIncl J U).coneComparison (X.liftJ hC hD)) ≫ coneMap X.bd.p X.pD
          (comm_of_kar X.bd.p_idem X.pD_idem X.j_kar) ≫
            (subInvIncl J U).coneComparison (X.liftJ hC hD) := by
      rw [← cancel_epi ((subInvIncl J U).coneComparison (X.liftJ hC hD)), e,
        IsIso.hom_inv_id_assoc]
      rfl
    have e'' := (subInvIncl J U).dualHom_mapH (N := N + 1) (coneMap (X.bd.lift hC).p (X.liftPD hD)
      (comm_of_kar (X.bd.lift hC).p_idem (X.liftPD_idem hD) (X.liftJ_kar hC hD)))
    rw [← cancel_epi ((subInvIncl J U).mapDualIso (N + 1) _).inv,
      ← cancel_mono ((subInvIncl J U).mapDualIso (N + 1) _).hom]
    rw [assoc, ← e'', e']
    erw [dualHom_comp, dualHom_comp]
    simp only [α, Iso.symm_inv, Iso.symm_hom, Iso.trans_hom, Iso.trans_inv, dualIso_hom,
      dualIso_inv, asIso_hom, asIso_inv, assoc]
    have key {P Q R R' : ChainComplex V ℤ} (m : P ≅ Q) (f : Q ⟶ R) (g₁ : R ⟶ R') (g₂ : R' ⟶ Q) :
        f ≫ g₁ ≫ g₂ = m.inv ≫ ((m.hom ≫ f) ≫ g₁ ≫ g₂ ≫ m.inv) ≫ m.hom := by simp
    exact key _ _ _ _
  · rfl
  · apply heq_of_eq
    have h1 := (subInvIncl J U).dualHom_coneComparison_comp_relDuality (N := N) (X.liftδφ hC hD)
    rw [InvFunctor.mapDual_eq (Φ := subInvIncl J U) (relDuality (X.liftδφ hC hD))] at h1
    have h2 : (subInvIncl J U).mapH (relDuality (X.liftδφ hC hD)) =
        α.hom ≫ relDuality ((subInvIncl J U).mapRel (X.liftδφ hC hD)) := by
      simp only [α, Iso.trans_hom, dualIso_hom, asIso_hom, assoc]
      rw [h1, Iso.hom_inv_id_assoc]
    exact h2.trans (congrArg (α.hom ≫ ·) (X.relDuality_mapRel_liftδφ hC hD))

/-- **A Poincaré pair with all objects in `U` lifts to the full subcategory `U`** (the supports
needed by `LiftingPairUnique`: a face of a triad which is a null-cobordism over `Kar U`). -/
def lift : SymPair (subInv J U) N where
  bd := X.bd.lift hC
  D := liftComplex U X.D hD
  pD := X.liftPD hD
  pD_idem := X.liftPD_idem hD
  support r hr := ObjectProperty.hom_ext _ (X.support r hr)
  j := X.liftJ hC hD
  j_kar := X.liftJ_kar hC hD
  δφ := X.liftδφ hC hD
  δφ_kar r r' := ObjectProperty.hom_ext _ (X.δφ_kar r r')
  symm := by
    have h := X.symm
    rw [IsSymmHomotopy, transposeHomotopy_hom] at h ⊢
    funext r r'
    apply ObjectProperty.hom_ext
    have h' := congrFun (congrFun h r) r'
    simp [transposeHomFamily, ObjectProperty.eqToHom_hom, liftδφ_hom] at h' ⊢
    exact h'
  poincare := X.lift_poincare hC hD

@[simp]
lemma lift_bd : (X.lift hC hD).bd = X.bd.lift hC := rfl

/-- Including the lifted pair recovers the pair (on the underlying data). -/
lemma map_lift_bd : ((X.lift hC hD).map (subInvIncl J U)).bd = X.bd := rfl

include hD in
/-- The boundary of a Poincaré pair with all objects in `U` is null-cobordant in `U`. -/
theorem nullCobordant_lift : NullCobordant (X.bd.lift hC) := ⟨X.lift hC hD, rfl⟩

end SymPair

/-- **The consumer form for `LiftingPairUnique`**: if the second face of a Poincaré triad and its
boundary lie in `U`, the boundary is null-cobordant in `U`. -/
theorem TriadOn.nullCobordant_lift {P : SymPoincare J N} {X₀ X₁ : PairData P}
    {T : TriadOn X₀ X₁} (h : T.IsPoincare) (hC : ∀ r, U (P.C.X r)) (hD : ∀ r, U (X₁.D.X r)) :
    NullCobordant (P.lift hC) :=
  (TriadOn.pair₁ h).toPair.nullCobordant_lift hC hD

/-- The same for a Karoubi filtration `F`: a Poincaré pair over `A` with all objects in `F.U`
gives a null-cobordism of `X.bdLift F hU` over `F.sub`. -/
theorem SymPair.nullCobordant_bdLift {A : InvCat} (F : KaroubiFiltration A) (X : SymPair A.inv N)
    (hU : ∀ r, F.U (X.bd.C.X r)) (hD : ∀ r, F.U (X.D.X r)) : NullCobordant (X.bdLift F hU) :=
  X.nullCobordant_lift hU hD

end Lift

/-! ### Orientation reversal -/

namespace PairData

variable {P : SymPoincare J N}

/-- `-(C ⊂ D, (δφ, φ)) = (C ⊂ D, (-δφ, -φ))`, a pair datum on `-P`. -/
@[implicit_reducible]
def neg (X : PairData P) : PairData P.neg where
  D := X.D
  pD := X.pD
  pD_idem := X.pD_idem
  support := X.support
  j := X.j
  j_kar := X.j_kar
  δφ := homotopyCongr (X.δφ.smul (-1 : ℤ)) (by simp) (by simp)
  δφ_kar r r' := by
    change _ ≫ ((-1 : ℤ) • X.δφ.hom r r') ≫ _ = (-1 : ℤ) • X.δφ.hom r r'
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, X.δφ_kar]
  symm := by
    have := X.symm
    rw [IsSymmHomotopy, transposeHomotopy_hom] at this ⊢
    funext r r'
    simpa [transposeHomFamily] using congrFun (congrFun this r) r'

@[simp] lemma neg_D (X : PairData P) : X.neg.D = X.D := rfl
@[simp] lemma neg_pD (X : PairData P) : X.neg.pD = X.pD := rfl
@[simp] lemma neg_j (X : PairData P) : X.neg.j = X.j := rfl

@[simp]
lemma relTop_neg (X : PairData P) (r : ℤ) : relTop X.neg.δφ r = -relTop X.δφ r := by
  simp [relTop, neg]

variable [HasBinaryBiproducts V]

lemma neg_isPoincare {X : PairData P} (h : X.IsPoincare) : X.neg.IsPoincare :=
  (X.toPairOn h).toPair.neg.poincare

end PairData

namespace TriadOn

variable {P : SymPoincare J N} {X₀ X₁ : PairData P} (T : TriadOn X₀ X₁)

/-- The orientation reversal `-T`: all structures negated, a triad with faces `-X₀`, `-X₁` on
`-P`. -/
@[implicit_reducible]
def neg : TriadOn X₀.neg X₁.neg where
  E := T.E
  pE := T.pE
  pE_idem := T.pE_idem
  support := T.support
  i₀ := T.i₀
  i₀_kar := T.i₀_kar
  i₁ := T.i₁
  i₁_kar := T.i₁_kar
  comm := T.comm
  δφ := homotopyCongr (T.δφ.smul (-1 : ℤ))
    (by ext r; simp only [triadCycle_f, PairData.relTop_neg, neg_comp, comp_neg, zsmul_f_apply,
      PairData.neg_D]; simp; abel) (by simp)
  δφ_kar r r' := by
    change _ ≫ ((-1 : ℤ) • T.δφ.hom r r') ≫ _ = (-1 : ℤ) • T.δφ.hom r r'
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, T.δφ_kar]
  symm := by
    have := T.symm
    rw [IsSymmHomotopy, transposeHomotopy_hom] at this ⊢
    funext r r'
    simpa [transposeHomFamily] using congrFun (congrFun this r) r'

@[simp] lemma neg_E : T.neg.E = T.E := rfl
@[simp] lemma neg_pE : T.neg.pE = T.pE := rfl
@[simp] lemma neg_i₀ : T.neg.i₀ = T.i₀ := rfl
@[simp] lemma neg_i₁ : T.neg.i₁ = T.i₁ := rfl

@[simp]
lemma neg_top (r : ℤ) : T.neg.top r = -T.top r := by
  simp [top, hTop, neg]

variable [HasBinaryBiproducts V]

lemma Ψ_neg : T.neg.Ψ = -T.Ψ := by
  ext r
  simp [ΨF]
  abel

lemma neg_isPoincare {T : TriadOn X₀ X₁} (h : T.IsPoincare) : T.neg.IsPoincare :=
  ⟨PairData.neg_isPoincare h.face₀, PairData.neg_isPoincare h.face₁, by
    rw [IsPoincareTop, Ψ_neg]; exact h.top.neg⟩

end TriadOn

/-! ### Exchanging the faces -/

namespace TriadOn

variable {P : SymPoincare J N} {X₀ X₁ : PairData P} (T : TriadOn X₀ X₁)

/-- **The swapped triad** `(E; X₁, X₀; P)`: the faces are exchanged and the top structure is
negated (the union `X₁ ∪ -X₀` is `-(X₀ ∪ -X₁)`); `Ψ(T.swap) = -TΨ(T)` (`Ψ_swap`). -/
@[implicit_reducible]
def swap : TriadOn X₁ X₀ where
  E := T.E
  pE := T.pE
  pE_idem := T.pE_idem
  support := T.support
  i₀ := T.i₁
  i₀_kar := T.i₁_kar
  i₁ := T.i₀
  i₁_kar := T.i₀_kar
  comm := T.comm.symm
  δφ := homotopyCongr (T.δφ.smul (-1 : ℤ)) (by ext r; simp [triadCycle_f]) (by simp)
  δφ_kar r r' := by
    change _ ≫ ((-1 : ℤ) • T.δφ.hom r r') ≫ _ = (-1 : ℤ) • T.δφ.hom r r'
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, T.δφ_kar]
  symm := by
    have := T.symm
    rw [IsSymmHomotopy, transposeHomotopy_hom] at this ⊢
    funext r r'
    simpa [transposeHomFamily] using congrFun (congrFun this r) r'

@[simp] lemma swap_E : T.swap.E = T.E := rfl
@[simp] lemma swap_pE : T.swap.pE = T.pE := rfl
@[simp] lemma swap_i₀ : T.swap.i₀ = T.i₁ := rfl
@[simp] lemma swap_i₁ : T.swap.i₁ = T.i₀ := rfl

@[simp]
lemma swap_top (r : ℤ) : T.swap.top r = -T.top r := by
  simp [top, hTop, swap]

/-- The top structure is strictly symmetric in dimension `N + 2`. -/
lemma top_transpose (r : ℤ) : (r * (N + 1 + 1 - r)).negOnePow •
      (J.star (T.top (N + 1 + 1 - r)) ≫ eqToHom (congrArg T.E.X (sub_sub_cancel (N + 1 + 1) r))) =
      T.top r :=
  hTop_transpose T.δφ T.symm r

variable [HasBinaryBiproducts V]

@[reassoc]
lemma star_ΨF_comp_sndX (s : ℤ) : J.star (T.ΨF s) ≫ sndX T.i₀ (N + 1 + 1 - s) =
    J.star (T.top s ≫ inrX T.i₁ s +
      J.star (T.i₁.f (N + 1 + 1 - s)) ≫
        (X₁.D.XIsoOfEq (by omega : N + 1 + 1 - s = N + 1 - (s - 1))).hom ≫
          relTop X₁.δφ (s - 1) ≫ inlX T.i₁ (s - 1) s (down_rel_pred s)) := by
  rw [← star_sndX_ΨF, J.star_comp, J.star_star]

@[reassoc]
lemma star_ΨF_comp_fstX (s k : ℤ) (hk : (ComplexShape.down ℤ).Rel (N + 1 + 1 - s) k) :
    J.star (T.ΨF s) ≫ fstX T.i₀ (N + 1 + 1 - s) k hk =
      J.star ((X₀.D.XIsoOfEq (by simp at hk; omega : k = N + 1 - s)).hom ≫
      ((s + 1).negOnePow • (relTop X₀.δφ s ≫ T.i₀.f s ≫ inrX T.i₁ s) +
        s.negOnePow • (J.star (X₀.j.f (N + 1 - s)) ≫
          (P.C.XIsoOfEq (by omega : N + 1 - s = N - (s - 1))).hom ≫ P.φ.f (s - 1) ≫
            X₁.j.f (s - 1) ≫ inlX T.i₁ (s - 1) s (down_rel_pred s)))) := by
  rw [← star_fstX_ΨF, J.star_comp, J.star_star]

lemma Ψ_swap : T.swap.Ψ = -transposeHom J (N + 1 + 1) T.Ψ := by
  ext r
  apply cone.ext_star (J := J) T.swap.i₀ (N + 1 + 1 - r) (N + 1 - r) (down_rel_sub (N + 1) r)
  · apply ext_to_X T.swap.i₁ r (r - 1) (down_rel_pred r)
    · simp only [Ψ_f, neg_f_apply, comp_neg, neg_comp, transposeHom_f, Linear.units_smul_comp,
        Linear.comp_units_smul, assoc, star_fstX_ΨF_assoc]
      erw [eqToHom_fstX (j := T.i₀) (sub_sub_cancel (N + 1 + 1) r) _
        (down_rel_sub (N + 1) (N + 1 + 1 - r)) (down_rel_pred r)]
      rw [T.star_ΨF_comp_fstX_assoc]
      simp [J.star_add, J.star_comp]
      rw [cone.star_fstX_inlX'_assoc (J := J) T.i₁,
        star_φ_f_eq P.symm (N + 1 + 1 - r - 1) (r - 1) (by omega)]
      rw [← star_f_XIsoOfEq_assoc]
      simp only [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul, assoc,
        XIsoOfEq_hom_comp_XIsoOfEq_hom_assoc, XIsoOfEq_comp_f_comp_eqToHom]
      rw [← Units.neg_smul]
      congr 1
      triad_sign_tac
    · simp only [Ψ_f, neg_f_apply, comp_neg, neg_comp, transposeHom_f, Linear.units_smul_comp,
        Linear.comp_units_smul, assoc, star_fstX_ΨF_assoc]
      erw [eqToHom_sndX (j := T.i₀) (sub_sub_cancel (N + 1 + 1) r)]
      rw [T.star_ΨF_comp_sndX_assoc]
      simp [J.star_add, J.star_comp]
      rw [cone.star_fstX_inlX'_assoc (J := J) T.i₁, relTop_eq_hTop,
        star_hTop X₁.δφ X₁.symm (N + 1 + 1 - r - 1) r (by omega)]
      simp only [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul, assoc, XIsoOfEq,
        eqToIso.hom, eqToHom_trans_assoc, eqToHom_refl, id_comp]
      rw [← Units.neg_smul]
      congr 1
      triad_sign_tac
  · apply ext_to_X T.swap.i₁ r (r - 1) (down_rel_pred r)
    · simp only [Ψ_f, neg_f_apply, comp_neg, neg_comp, transposeHom_f, Linear.units_smul_comp,
        Linear.comp_units_smul, assoc, star_sndX_ΨF_assoc]
      erw [eqToHom_fstX (j := T.i₀) (sub_sub_cancel (N + 1 + 1) r) _
        (down_rel_sub (N + 1) (N + 1 + 1 - r)) (down_rel_pred r)]
      rw [T.star_ΨF_comp_fstX_assoc]
      simp [J.star_add, J.star_comp]
      rw [relTop_eq_hTop, star_hTop X₀.δφ X₀.symm (N + 1 + 1 - r) (r - 1) (by omega)]
      simp only [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul, assoc, XIsoOfEq,
        eqToIso.hom, eqToHom_trans, eqToHom_refl, comp_id]
      rw [← Units.neg_smul]
      conv_lhs => rw [← one_smul ℤˣ (J.star (T.i₀.f (N + 1 + 1 - r)) ≫ _)]
      congr 1
      triad_sign_tac
    · simp only [Ψ_f, neg_f_apply, comp_neg, neg_comp, transposeHom_f, Linear.units_smul_comp,
        Linear.comp_units_smul, assoc, star_sndX_ΨF_assoc]
      erw [eqToHom_sndX (j := T.i₀) (sub_sub_cancel (N + 1 + 1) r)]
      rw [T.star_ΨF_comp_sndX_assoc]
      simp [J.star_add, J.star_comp]
      exact (T.top_transpose r).symm

/-- The swap of a triad with Poincaré top has Poincaré top (`Ψ(T.swap) = -TΨ(T)`). -/
lemma swap_isPoincareTop {T : TriadOn X₀ X₁} (h : T.IsPoincareTop) : T.swap.IsPoincareTop := by
  rw [IsPoincareTop, Ψ_swap]
  exact (IsKarEquiv.transposeHom (coneMap_idem _ X₀.pD_idem T.pE_idem)
    (coneMap_idem _ X₁.pD_idem T.pE_idem) h).neg

/-- The swap of a Poincaré triad is a Poincaré triad. -/
theorem swap_isPoincare {T : TriadOn X₀ X₁} (h : T.IsPoincare) : T.swap.IsPoincare :=
  ⟨h.face₁, h.face₀, swap_isPoincareTop h.top⟩

end TriadOn

/-! ### Images under duality-preserving functors -/

/-- Transport of a Kar equivalence along an isomorphism of the target. -/
lemma IsKarEquiv.conjIsoRight {X Y Y' : ChainComplex V ℤ} {e : X ⟶ X} {e' : Y ⟶ Y} {f : X ⟶ Y}
    (h : IsKarEquiv e e' f) (β : Y ≅ Y') : IsKarEquiv e (β.inv ≫ e' ≫ β.hom) (f ≫ β.hom) := by
  obtain ⟨g, hg, ⟨H₁⟩, ⟨H₂⟩⟩ := h
  refine ⟨β.inv ≫ g, by simp [hg], ⟨homotopyCongr ((H₁.compLeft β.inv).compRight β.hom)
    (by simp) (by simp)⟩, ⟨homotopyCongr H₂ (by simp) rfl⟩⟩

section Map

variable [HasBinaryBiproducts V] {W : Type u'} [Category.{v'} W] [Preadditive W]
  [HasBinaryBiproducts W] {J' : StrictInvolution W} (Φ : InvFunctor J J') {P : SymPoincare J N}

namespace PairData

/-- The image `F(C ⊂ D, (δφ, φ))` of a pair datum under a duality-preserving functor. -/
@[simps, implicit_reducible]
def map (X : PairData P) : PairData (P.map Φ) where
  D := Φ.mapC X.D
  pD := Φ.mapH X.pD
  pD_idem := by rw [← Functor.map_comp, X.pD_idem]
  support r hr := by simp [X.support r hr]
  j := Φ.mapH X.j
  j_kar := by simp only [SymPoincare.map_p, ← Functor.map_comp, X.j_kar]
  δφ := Φ.mapRel X.δφ
  δφ_kar r r' := by
    simp only [InvFunctor.mapRel_hom, dualHom_f, InvFunctor.mapH,
      Functor.mapHomologicalComplex_map_f, ← Φ.map_star, ← Functor.map_comp]
    rw [← dualHom_f, X.δφ_kar]
  symm := by
    have e : (Φ.mapRel X.δφ).hom = fun r r' ↦ Φ.F.map (X.δφ.hom r r') :=
      funext₂ fun _ _ ↦ InvFunctor.mapRel_hom _ _ _ _
    have hs := X.symm
    rw [IsSymmHomotopy, transposeHomotopy_hom] at hs ⊢
    rw [e, Φ.transposeHomFamily_map, hs]

lemma map_isPoincare {X : PairData P} (h : X.IsPoincare) : (X.map Φ).IsPoincare :=
  ((X.toPairOn h).toPair.map Φ).poincare

end PairData

namespace TriadOn

variable {X₀ X₁ : PairData P} (T : TriadOn X₀ X₁)

omit [HasBinaryBiproducts V] [HasBinaryBiproducts W] in
lemma map_comm : (X₀.map Φ).j ≫ Φ.mapH T.i₀ = (X₁.map Φ).j ≫ Φ.mapH T.i₁ := by
  simp only [PairData.map_j, ← Functor.map_comp, T.comm]

omit [HasBinaryBiproducts V] [HasBinaryBiproducts W] in
lemma map_triadCycle :
    (Φ.mapDualIso (N + 1) T.E).inv ≫ Φ.mapH (triadCycle X₀ X₁ T.i₀ T.i₁ T.comm) =
      triadCycle (X₀.map Φ) (X₁.map Φ) (Φ.mapH T.i₀) (Φ.mapH T.i₁) (T.map_comm Φ) := by
  ext r
  simp [triadCycle_f, InvFunctor.relTop_mapRel, Φ.map_star]

/-- The image of a triad under a duality-preserving functor. -/
@[implicit_reducible]
def map : TriadOn (X₀.map Φ) (X₁.map Φ) where
  E := Φ.mapC T.E
  pE := Φ.mapH T.pE
  pE_idem := by rw [← Functor.map_comp, T.pE_idem]
  support r hr := by simp [T.support r hr]
  i₀ := Φ.mapH T.i₀
  i₀_kar := by simp only [PairData.map_pD, ← Functor.map_comp, T.i₀_kar]
  i₁ := Φ.mapH T.i₁
  i₁_kar := by simp only [PairData.map_pD, ← Functor.map_comp, T.i₁_kar]
  comm := T.map_comm Φ
  δφ := homotopyCongr ((Φ.F.mapHomotopy T.δφ).compLeft (Φ.mapDualIso (N + 1) T.E).inv)
    (T.map_triadCycle Φ) (by simp)
  δφ_kar r r' := by
    simp only [homotopyCongr_hom, Homotopy.compLeft_hom, Functor.mapHomotopy_hom,
      InvFunctor.mapDualIso_inv_f, id_comp, dualHom_f, InvFunctor.mapH,
      Functor.mapHomologicalComplex_map_f, ← Φ.map_star, ← Functor.map_comp]
    rw [← dualHom_f, T.δφ_kar]
  symm := by
    have e : ((Φ.F.mapHomotopy T.δφ).compLeft (Φ.mapDualIso (N + 1) T.E).inv).hom =
        fun r r' ↦ Φ.F.map (T.δφ.hom r r') := by
      funext r r'; simp
    have hs := T.symm
    rw [IsSymmHomotopy, transposeHomotopy_hom] at hs ⊢
    change transposeHomFamily J' (N + 1)
      ((Φ.F.mapHomotopy T.δφ).compLeft (Φ.mapDualIso (N + 1) T.E).inv).hom =
        ((Φ.F.mapHomotopy T.δφ).compLeft (Φ.mapDualIso (N + 1) T.E).inv).hom
    rw [e, Φ.transposeHomFamily_map, hs]

omit [HasBinaryBiproducts V] [HasBinaryBiproducts W] in
@[simp]
lemma map_i₀ : (T.map Φ).i₀ = Φ.mapH T.i₀ := rfl

omit [HasBinaryBiproducts V] [HasBinaryBiproducts W] in
@[simp]
lemma map_i₁ : (T.map Φ).i₁ = Φ.mapH T.i₁ := rfl

omit [HasBinaryBiproducts V] [HasBinaryBiproducts W] in
@[simp]
lemma map_pE : (T.map Φ).pE = Φ.mapH T.pE := rfl

omit [HasBinaryBiproducts V] [HasBinaryBiproducts W] in
lemma map_δφ_hom (r r' : ℤ) : (T.map Φ).δφ.hom r r' = Φ.F.map (T.δφ.hom r r') := by
  simp [map]

omit [HasBinaryBiproducts V] [HasBinaryBiproducts W] in
@[simp]
lemma map_top (r : ℤ) : (T.map Φ).top r = Φ.F.map (T.top r) := by
  simp [top, hTop, map_δφ_hom, XIsoOfEq, eqToHom_map]

/-- **Naturality of `Ψ`**: under the cone comparison isomorphisms, `Ψ(F T) = F Ψ(T)`. -/
lemma dualHom_coneComparison_comp_Ψ :
    dualHom J' (N + 1 + 1) (Φ.coneComparison T.i₀) ≫ (T.map Φ).Ψ ≫ Φ.coneComparison T.i₁ =
      Φ.mapDual T.Ψ := by
  ext r
  have h₁ := congrArg J'.star (Φ.inrX_coneComparison_f T.i₀ (N + 1 + 1 - r))
  have h₂ := congrArg J'.star (Φ.inlX_coneComparison_f T.i₀ _ _ (down_rel_sub (N + 1) r))
  simp only [J'.star_comp, ← Φ.map_star] at h₁ h₂
  simp [ΨF, reassoc_of% h₁, reassoc_of% h₂, Φ.map_star, InvFunctor.relTop_mapRel, eqToHom_map,
    XIsoOfEq]

/-- The image of a triad with Poincaré top has Poincaré top. -/
lemma map_isPoincareTop {T : TriadOn X₀ X₁} (h : T.IsPoincareTop) : (T.map Φ).IsPoincareTop := by
  have h₀ := (h.map Φ.F).conjIso (Φ.mapDualIso (N + 1 + 1) (cone T.i₀))
  rw [← Φ.dualHom_mapH, ← Φ.mapDual_eq, ← T.dualHom_coneComparison_comp_Ψ Φ] at h₀
  have h₁ := (h₀.conjIso (dualIso J' (N + 1 + 1) (asIso (Φ.coneComparison T.i₀)))).conjIsoRight
    (asIso (Φ.coneComparison T.i₁)).symm
  have e₀ := Φ.coneComparison_comp_map_coneMap T.i₀
    (comm_of_kar X₀.pD_idem T.pE_idem T.i₀_kar)
  have e₁ := Φ.coneComparison_comp_map_coneMap T.i₁
    (comm_of_kar X₁.pD_idem T.pE_idem T.i₁_kar)
  rw [← cancel_mono (inv (Φ.coneComparison T.i₀)), assoc, assoc, IsIso.hom_inv_id, comp_id] at e₀
  rw [← cancel_mono (inv (Φ.coneComparison T.i₁)), assoc, assoc, IsIso.hom_inv_id, comp_id] at e₁
  have hs : (dualIso J' (N + 1 + 1) (asIso (Φ.coneComparison T.i₀))).inv ≫
      dualHom J' (N + 1 + 1) (Φ.mapH T.coneIdem₀) ≫
        (dualIso J' (N + 1 + 1) (asIso (Φ.coneComparison T.i₀))).hom =
      dualHom J' (N + 1 + 1) (T.map Φ).coneIdem₀ := by
    simp only [dualIso_inv, dualIso_hom, asIso_hom, asIso_inv, ← dualHom_comp, assoc, e₀]
    rfl
  have ht : (asIso (Φ.coneComparison T.i₁)).symm.inv ≫ Φ.mapH T.coneIdem₁ ≫
      (asIso (Φ.coneComparison T.i₁)).symm.hom = (T.map Φ).coneIdem₁ := by
    simp only [Iso.symm_inv, Iso.symm_hom, asIso_hom, asIso_inv, e₁]
    rfl
  have hf : ((dualIso J' (N + 1 + 1) (asIso (Φ.coneComparison T.i₀))).inv ≫
      dualHom J' (N + 1 + 1) (Φ.coneComparison T.i₀) ≫ (T.map Φ).Ψ ≫ Φ.coneComparison T.i₁) ≫
        (asIso (Φ.coneComparison T.i₁)).symm.hom = (T.map Φ).Ψ := by
    simp only [dualIso_inv, asIso_inv, Iso.symm_hom, assoc, IsIso.hom_inv_id, comp_id]
    rw [← assoc, ← dualHom_comp, IsIso.hom_inv_id, dualHom_id, id_comp]
  rw [hs, ht, hf] at h₁
  exact h₁

/-- The image of a Poincaré triad is a Poincaré triad. -/
theorem map_isPoincare {T : TriadOn X₀ X₁} (h : T.IsPoincare) : (T.map Φ).IsPoincare :=
  ⟨PairData.map_isPoincare Φ h.face₀, PairData.map_isPoincare Φ h.face₁,
    map_isPoincareTop Φ h.top⟩

end TriadOn

end Map

/-! ### Cobordism of pairs relative to the boundary -/

/-- Poincaré pairs `Y₀`, `Y₁` on the same boundary `P` are **cobordant rel `P`**: they are the
faces of a Poincaré triad. -/
def PairOn.RelCobordant [HasBinaryBiproducts V] {P : SymPoincare J N} (Y₀ Y₁ : PairOn P) : Prop :=
  ∃ T : TriadOn (PairData.ofPairOn Y₀) (PairData.ofPairOn Y₁), T.IsPoincareTop

namespace PairOn

variable [HasBinaryBiproducts V] {P : SymPoincare J N}

/-- Cobordism rel boundary is reflexive (the cylinder). -/
lemma RelCobordant.refl (Y : PairOn P) : Y.RelCobordant Y :=
  ⟨TriadOn.cylinder _, TriadOn.cylinder_isPoincareTop _⟩

/-- Cobordism rel boundary is symmetric (exchange the faces). -/
lemma RelCobordant.symm {Y₀ Y₁ : PairOn P} (h : Y₀.RelCobordant Y₁) : Y₁.RelCobordant Y₀ := by
  obtain ⟨T, hT⟩ := h
  exact ⟨T.swap, TriadOn.swap_isPoincareTop hT⟩

/-- The faces of a Poincaré triad are cobordant rel boundary. -/
lemma _root_.HSFormal.LTheory.TriadOn.relCobordant {X₀ X₁ : PairData P} {T : TriadOn X₀ X₁}
    (h : T.IsPoincare) : (TriadOn.pair₀ h).RelCobordant (TriadOn.pair₁ h) :=
  ⟨T, h.top⟩

end PairOn

end

end HSFormal.LTheory
