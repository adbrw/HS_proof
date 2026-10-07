import HSFormal.LTheory.Model.LiftingPairLine
import HSFormal.LTheory.Model.Colim
import HSFormal.LTheory.Model.Cobordism

/-!
# The boundary map `∂` of the colimit model (lower L-theory model, module 18)

`blueprint/lower-L-construction.md` §3.2 ("Lifting pairs (definition of ∂)"), §4 row 18 and §6
(signs): for a Karoubi filtration `F : U ⊂ A`, the boundary
`Lmodel.bdry F hF n : Lmodel (A/U) (n + 1) →+ Lmodel U n` and the interface fields `bdry`,
`bdry_natural`, `bsign`, `bdry_pair` of `LowerLTheory` (`Interface.lean`) for `L = Lmodel`.

## The hypothesis (L2)

Uniqueness of lifting pairs (module 17, relative lifting) is isolated as one `Prop`:

* `KaroubiFiltration.LiftingPairNull F`: for every level `k`, every closed `(N+1)`-complex `D`
  over `C_ℤ^{∘k}(A/U)` with `0 ≤ N + 1` which is **null-cobordant** (over `Kar`), and every
  lifting pair `P` at level `k + 1` of `D ⊗ ℝ`, the boundary class `[∂P]` vanishes in the colimit
  `Lmodel U n` (`N + 1 = n + (k + 1)`), i.e. after finitely many further transitions.  This is
  (L2) verbatim: "a lifting pair whose `D` bounds has null-cobordant boundary".
* It is equivalent (`liftingPairUnique_iff`) to the class form `LiftingPairUnique F`: lifting
  pairs of `D₁ ⊗ ℝ`, `D₂ ⊗ ℝ` with `[D₁] = [D₂]` have equal boundary classes in the colimit.
* `LiftingPairNullAll` is the hypothesis for all filtrations, under which `Lmodel.bdryAll`,
  `bdryAll_natural`, `bdryAll_pair` are the interface fields verbatim.

Everything else is proved here.  Well-definedness of `∂` on a single complex (any two lifting
pairs, `LiftingPairNull.of_bdClsAt_eq`) comes from (L2) for `D ⊕ -D` and the lifting pair
`P₁ ⊕ -P₂`; additivity from **sums of lifting pairs** (`LiftingPair.sum`, `sum_bdCls`:
`X₁ ⊕ X₂` with `(X₁ ⊕ X₂).toQuot ≃ X₁.toQuot ⊕ X₂.toQuot`, `SymPair.toQuotSumIsometry`, and
`(X₁ ⊕ X₂).bdLift = X₁.bdLift ⊕ X₂.bdLift`, `SymPair.bdLift_sum`); vanishing on null-cobordant
complexes is (L2) itself, so the level map `bdLevel` descends to `Lconc` by `Lconc.lift`.

## Main definitions and results

* `KaroubiFiltration.bdVal n k D = ι_{k+1}((-1)^{k+1} [∂P])` for the chosen lifting pair `P` at
  level `k + 1` of `D ⊗ ℝ` (`nonempty_liftingPairAt_succ`), `bdVal_eq` (any `P` gives the same
  value), `bdLevel` (the level homomorphism), `bdLevel_tensorLine` (**compatibility with the
  transitions**: `P.lineNeg` is a lifting pair of `D ⊗ ℝ ⊗ ℝ` with
  `σ_{k+2}[∂ P.lineNeg] = σ_{k+1}[∂P] ⊗ ℝ`, `lineNeg_sgnBdClsAt`).
* `Lmodel.bdry F hF n` via `Lmodel.lift`; `bdry_of`; the defining formula `bdry_ofDeg_cls`.
* `Lmodel.bdry_natural` (H1 naturality, `LiftingPairAt.map`, `map_sgnBdClsAt`,
  `LineData.Hom.symMapIsometry`).
* `Lmodel.bsign = fun _ ↦ 1` and `Lmodel.bdry_pair` (H2: `X.liftingPairAt`'s line `-(X ⊗ ℝ)` is
  a lifting pair at level `1` of `X.toQuot ⊗ ℝ` with `σ_1[∂] = [X.bdLift] ⊗ ℝ`,
  `liftingPairAt_lineNeg_sgnBdClsAt`, then `of_tensorLine`).
* Infrastructure: `SymPoincare.HomotopyIsometry.sum`, `SymPair.sum`, `LineData.sym_neg`,
  `LiftingPairAt.ofIsometryAt`/`negAt`/`sumAt`.

## Negative degrees

Lifting pairs of `D ⊗ ℝ` are only known to exist for `0 ≤ dim D = n + k + 1`
(`nonempty_liftingPairAt_succ`).  At levels with `n + k + 1 < 0` the group
`Lconc (C_ℤ^{∘k}(A/U)) (n + k + 1)` is `0` (`Lconc.cls_eq_zero_of_neg`), so `bdVal` is defined
as `0` there and compatibility with the transitions out of such a level is trivial (its source
is `0`); every class of `Lmodel (A/U) (n + 1)` is in any case represented at every
sufficiently large level (`of_transit`), in particular at one with `n + k + 1 ≥ 0`.  For `bdry_pair` with `N + 1 < 0` both sides vanish (`[X.bdLift] ∈ Lconc U N = 0`).
The interface demands nothing else in low degrees.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression

noncomputable section

attribute [local implicit_reducible] InvCat.czIter SymPair.map SymPair.closedOfIsZero SymPair.neg
  SymPair.toPairOn PairOn.toPair CZ.mapIter CZ.lineHom

/-! ### Sums of homotopy isometries -/

namespace SymPoincare.HomotopyIsometry

variable {V : Type*} [Category V] [Preadditive V] {J : StrictInvolution V} {N : ℤ}
  {P P' Q Q' : SymPoincare J N}

/-- **Sums of homotopy isometries**: `P ≃ P'` and `Q ≃ Q'` give `P ⊕ Q ≃ P' ⊕ Q'` (along any
bicones). -/
def sum (e : P.HomotopyIsometry P') (e' : Q.HomotopyIsometry Q')
    (b : ∀ r, BinaryBicone (P.C.X r) (Q.C.X r)) (b' : ∀ r, BinaryBicone (P'.C.X r) (Q'.C.X r)) :
    (P.sum Q b).HomotopyIsometry (P'.sum Q' b') where
  f := sumFst b ≫ e.f ≫ sumInl b' + sumSnd b ≫ e'.f ≫ sumInr b'
  g := sumFst b' ≫ e.g ≫ sumInl b + sumSnd b' ≫ e'.g ≫ sumInr b
  f_kar := by simp [add_comp, comp_add]
  g_kar := by simp [add_comp, comp_add]
  fg := homotopyCongr (((e.fg.compLeft (sumFst b)).compRight (sumInl b)).add
      ((e'.fg.compLeft (sumSnd b)).compRight (sumInr b))) (by simp [add_comp, comp_add])
    (by simp)
  gf := homotopyCongr (((e.gf.compLeft (sumFst b')).compRight (sumInl b')).add
      ((e'.gf.compLeft (sumSnd b')).compRight (sumInr b'))) (by simp [add_comp, comp_add])
    (by simp)
  conj := homotopyCongr (((e.conj.compLeft (dualHom J N (sumInl b'))).compRight (sumInl b')).add
      ((e'.conj.compLeft (dualHom J N (sumInr b'))).compRight (sumInr b')))
    (by simp [add_comp, comp_add, dualHom_comp])
    (by simp)

end SymPoincare.HomotopyIsometry

/-! ### Sums of Poincaré pairs and their images modulo `U` -/

namespace PairSum

variable {V : Type*} [Category V] [Preadditive V] [HasBinaryBiproducts V]
  {J : StrictInvolution V} {N : ℤ} {P Q : SymPoincare J N} (X : PairOn P) (Z : PairOn Q)
  (b : ∀ r, BinaryBicone (P.C.X r) (Q.C.X r))

/-- The relative top structure of a sum of pairs is the sum of the relative top structures. -/
lemma relTop_δφ (r : ℤ) :
    relTop (δφ X Z b) r =
      J.star ((sumInl (bD X Z)).f (N + 1 - r)) ≫ relTop X.δφ r ≫ (sumInl (bD X Z)).f r +
        J.star ((sumInr (bD X Z)).f (N + 1 - r)) ≫ relTop Z.δφ r ≫ (sumInr (bD X Z)).f r := by
  simp only [relTop, δφ_hom, Homotopy.compLeft_hom, Homotopy.compRight_hom, dualHom_f, comp_add,
    star_f_XIsoOfEq_assoc, assoc]

end PairSum

namespace SymPair

variable {A : InvCat} {N : ℤ}

/-- **The direct sum of Poincaré pairs** `X ⊕ Z` (`PairOn.sum`), with boundary
`X.bd ⊕ Z.bd` along the given bicones. -/
@[implicit_reducible]
def sum (X Z : SymPair A.inv N) (b : ∀ r, BinaryBicone (X.bd.C.X r) (Z.bd.C.X r)) :
    SymPair A.inv N :=
  (X.toPairOn.sum Z.toPairOn b).toPair

@[simp]
lemma sum_bd (X Z : SymPair A.inv N) (b : ∀ r, BinaryBicone (X.bd.C.X r) (Z.bd.C.X r)) :
    (X.sum Z b).bd = X.bd.sum Z.bd b := rfl

variable (F : KaroubiFiltration A)

/-- The bicones of the images modulo `U` of the tops of two pairs. -/
abbrev quotSumBicone (X Z : SymPair A.inv N) (r : ℤ) :
    BinaryBicone (F.proj.F.obj (X.D.X r)) (F.proj.F.obj (Z.D.X r)) :=
  F.proj.F.mapBinaryBicone (PairSum.bD X.toPairOn Z.toPairOn r)

/-- **`toQuot` of a sum of pairs is the sum of the `toQuot`s** (a strict isometry with identity
components). -/
def toQuotSumIsometry (X Z : SymPair A.inv N) (b : ∀ r, BinaryBicone (X.bd.C.X r) (Z.bd.C.X r))
    (hX : ∀ r, F.U (X.bd.C.X r)) (hZ : ∀ r, F.U (Z.bd.C.X r))
    (hS : ∀ r, F.U ((X.sum Z b).bd.C.X r)) :
    ((X.sum Z b).toQuot F hS).HomotopyIsometry
      ((X.toQuot F hX).sum (Z.toQuot F hZ) (quotSumBicone F X Z)) :=
  .ofIso (Hom.isoOfComponents (fun _ ↦ Iso.refl _) (fun r r' _ ↦ by
      simp only [Iso.refl_hom, id_comp, comp_id, SymPoincare.sum_C, sumComplex_d,
        closedOfIsZero_C, map_D, quotSumBicone, Functor.mapBinaryBicone_fst,
        Functor.mapBinaryBicone_inl, Functor.mapBinaryBicone_snd, Functor.mapBinaryBicone_inr,
        Functor.mapHomologicalComplex_obj_d, ← Functor.map_comp]
      exact (id_comp _).trans (comp_id _).symm))
    (by
      ext r
      simp only [Iso.refl_hom, comp_f, Hom.isoOfComponents_hom_f, id_comp, comp_id,
        SymPoincare.sum_p, closedOfIsZero_p, map_pD, add_f_apply, sumFst_f, sumInl_f, sumSnd_f,
        sumInr_f, quotSumBicone, Functor.mapBinaryBicone_fst, Functor.mapBinaryBicone_inl,
        Functor.mapBinaryBicone_snd, Functor.mapBinaryBicone_inr, InvFunctor.mapH,
        Functor.mapHomologicalComplex_map_f, ← Functor.map_comp]
      exact (id_comp _).trans (comp_id _).symm)
    (by
      ext r
      simp only [comp_f, Hom.isoOfComponents_hom_f, Iso.refl_hom, dualHom_f, comp_id,
        SymPoincare.sum_φ, closedOfIsZero_φ, topHom_f, map_top]
      rw [show (X.sum Z b).top r = relTop (PairSum.δφ X.toPairOn Z.toPairOn b) r from rfl,
        PairSum.relTop_δφ]
      simp only [add_f_apply, comp_f, dualHom_f, topHom_f, map_top, sumInl_f, sumInr_f,
        quotSumBicone, Functor.mapBinaryBicone_inl, Functor.mapBinaryBicone_inr,
        ← F.proj.map_star, Functor.map_add, Functor.map_comp]
      erw [F.quot.inv.star_id, id_comp]
      exact comp_id _)

/-- The bicones in `U` of the boundary of a sum of pairs. -/
abbrev subSumBicone (X Z : SymPair A.inv N) (b : ∀ r, BinaryBicone (X.bd.C.X r) (Z.bd.C.X r))
    (hX : ∀ r, F.U (X.bd.C.X r)) (hZ : ∀ r, F.U (Z.bd.C.X r))
    (hS : ∀ r, F.U ((X.sum Z b).bd.C.X r)) (r : ℤ) :
    BinaryBicone ((X.bdLift F hX).C.X r) ((Z.bdLift F hZ).C.X r) :=
  subBicone F.U (b r) (hS r)

/-- **`bdLift` of a sum of pairs is the sum of the `bdLift`s** (on the nose). -/
lemma bdLift_sum (X Z : SymPair A.inv N) (b : ∀ r, BinaryBicone (X.bd.C.X r) (Z.bd.C.X r))
    (hX : ∀ r, F.U (X.bd.C.X r)) (hZ : ∀ r, F.U (Z.bd.C.X r))
    (hS : ∀ r, F.U ((X.sum Z b).bd.C.X r)) :
    (X.sum Z b).bdLift F hS =
      (X.bdLift F hX).sum (Z.bdLift F hZ) (subSumBicone F X Z b hX hZ hS) := rfl

end SymPair

/-! ### Sums, negatives and transport of lifting pairs -/

namespace LineData

variable {A B : InvCat} (L : LineData A B) {N : ℤ}

/-- `(-P) ⊗ ℝ = -(P ⊗ ℝ)`. -/
lemma sym_neg (P : SymPoincare A.inv N) : L.sym P.neg = (L.sym P).neg :=
  SymPoincare.ext_of_φ rfl HEq.rfl (heq_of_eq (by
    rw [sym_φ, SymPoincare.neg_φ, SymPoincare.neg_φ, sym_φ, map_neg, comp_neg]))

end LineData

namespace KaroubiFiltration.LiftingPair

variable {A : InvCat} {F : KaroubiFiltration A} {N : ℤ} {D₁ D₂ : SymPoincare F.quot.inv (N + 1)}
  (P₁ : F.LiftingPair D₁) (P₂ : F.LiftingPair D₂)

/-- Unitary bicones of the boundaries of two lifting pairs. -/
abbrev bdBicone (r : ℤ) : BinaryBicone (P₁.X.bd.C.X r) (P₂.X.bd.C.X r) :=
  (Lconc.ub P₁.X.bd P₂.X.bd r).toBinaryBicone

lemma sum_mem (r : ℤ) : F.U ((P₁.X.sum P₂.X (bdBicone P₁ P₂)).bd.C.X r) :=
  haveI := F.additive
  IsAdditiveSub.biprod_mem _ (Lconc.ub P₁.X.bd P₂.X.bd r).isBilimit (P₁.mem r) (P₂.mem r)

/-- **The sum of lifting pairs is a lifting pair of the sum**: `X₁ ⊕ X₂` (boundary
`Y₁ ⊕ Y₂ ⊂ U`) with `(X₁ ⊕ X₂).toQuot = X₁.toQuot ⊕ X₂.toQuot ≃ D₁ ⊕ D₂`. -/
def sum (c : ∀ r, BinaryBicone (D₁.C.X r) (D₂.C.X r)) : F.LiftingPair (D₁.sum D₂ c) where
  X := P₁.X.sum P₂.X (bdBicone P₁ P₂)
  mem := sum_mem P₁ P₂
  iso := (SymPair.toQuotSumIsometry F P₁.X P₂.X _ P₁.mem P₂.mem (sum_mem P₁ P₂)).trans
    (SymPoincare.HomotopyIsometry.sum P₁.iso P₂.iso _ c)

/-- The boundary class of a sum of lifting pairs is the sum of the boundary classes. -/
lemma sum_bdCls (c : ∀ r, BinaryBicone (D₁.C.X r) (D₂.C.X r)) :
    (P₁.sum P₂ c).bdCls = P₁.bdCls + P₂.bdCls := by
  change Lconc.cls ((P₁.X.sum P₂.X (bdBicone P₁ P₂)).bdLift F (sum_mem P₁ P₂)) = _
  rw [SymPair.bdLift_sum F _ _ _ P₁.mem P₂.mem, Lconc.cls_sum]

end KaroubiFiltration.LiftingPair

namespace KaroubiFiltration.LiftingPairAt

variable {A : InvCat} {F : KaroubiFiltration A} {N : ℤ} {j : ℕ}

/-- Change of target along an isometry, at level `j`. -/
def ofIsometryAt {D D' : SymPoincare (F.quot.czIter j).inv (N + 1)} (P : F.LiftingPairAt j D)
    (e : D.HomotopyIsometry D') : F.LiftingPairAt j D' :=
  LiftingPair.ofIsometry P (e.map (F.czIterQuotIso j).inv)

@[simp]
lemma ofIsometryAt_bdClsAt {D D' : SymPoincare (F.quot.czIter j).inv (N + 1)}
    (P : F.LiftingPairAt j D) (e : D.HomotopyIsometry D') :
    (P.ofIsometryAt e).bdClsAt = P.bdClsAt := rfl

@[simp]
lemma ofIsometryAt_sgnBdClsAt {D D' : SymPoincare (F.quot.czIter j).inv (N + 1)}
    (P : F.LiftingPairAt j D) (e : D.HomotopyIsometry D') :
    (P.ofIsometryAt e).sgnBdClsAt = P.sgnBdClsAt := rfl

/-- A lifting pair at level `j` of `-D`: the negated pair. -/
def negAt {D : SymPoincare (F.quot.czIter j).inv (N + 1)} (P : F.LiftingPairAt j D) :
    F.LiftingPairAt j D.neg :=
  (LiftingPair.neg P).ofIsometry (.ofEq' (SymPoincare.map_neg _ _).symm)

@[simp]
lemma negAt_bdClsAt {D : SymPoincare (F.quot.czIter j).inv (N + 1)} (P : F.LiftingPairAt j D) :
    P.negAt.bdClsAt = -P.bdClsAt := by
  change Lconc.map (F.czIterSubIso j).hom (LiftingPair.neg P).bdCls = _
  rw [LiftingPair.neg_bdCls, map_neg]

/-- **Sums at level `j`**: lifting pairs of `D₁`, `D₂` give a lifting pair of `D₁ ⊕ D₂`. -/
def sumAt {D₁ D₂ : SymPoincare (F.quot.czIter j).inv (N + 1)} (P₁ : F.LiftingPairAt j D₁)
    (P₂ : F.LiftingPairAt j D₂) (c : ∀ r, BinaryBicone (D₁.C.X r) (D₂.C.X r)) :
    F.LiftingPairAt j (D₁.sum D₂ c) :=
  (LiftingPair.sum P₁ P₂ fun r ↦ (F.czIterQuotIso j).inv.F.mapBinaryBicone (c r)).ofIsometry
    (SymPoincare.mapSum (F.czIterQuotIso j).inv D₁ D₂ c).symm

@[simp]
lemma sumAt_bdClsAt {D₁ D₂ : SymPoincare (F.quot.czIter j).inv (N + 1)}
    (P₁ : F.LiftingPairAt j D₁) (P₂ : F.LiftingPairAt j D₂)
    (c : ∀ r, BinaryBicone (D₁.C.X r) (D₂.C.X r)) :
    (P₁.sumAt P₂ c).bdClsAt = P₁.bdClsAt + P₂.bdClsAt := by
  change Lconc.map (F.czIterSubIso j).hom
    (LiftingPair.sum P₁ P₂ fun r ↦ (F.czIterQuotIso j).inv.F.mapBinaryBicone (c r)).bdCls = _
  rw [LiftingPair.sum_bdCls, map_add]

end KaroubiFiltration.LiftingPairAt

/-! ### The hypothesis (L2) -/

namespace KaroubiFiltration

variable {A : InvCat} (F : KaroubiFiltration A)

/-- **(L2), isolated for module 17** (`blueprint/lower-L-construction.md` §3.2 "(L2) Relative
lifting"): if a closed `(N+1)`-complex `D` over `C_ℤ^{∘k}(A/U)` (any Kar complex, `N + 1 ≥ 0`)
bounds over `Kar(C_ℤ^{∘k}(A/U))`, then the boundary `Y` of **every** lifting pair at level
`k + 1` of its transition image `D ⊗ ℝ` vanishes in the colimit `Lmodel U n`
(`n + k + 1 = N + 1`), i.e. after finitely many further transitions `⊗ ℝ`.  (The relative
lifting of the null-cobordism of `D ⊗ ℝ` rel the given lifting pair produces a null-cobordism of
`Y` over `Kar(C_ℤ^{∘(k+1)} U)`, possibly after one more transition for the free-ification.) -/
def LiftingPairNull : Prop :=
  ∀ (k : ℕ) {N : ℤ} (D : SymPoincare (F.quot.czIter k).inv (N + 1)), 0 ≤ N + 1 →
    NullCobordant D →
    ∀ (P : F.LiftingPairAt (k + 1) ((CZ.lineData (F.quot.czIter k)).sym D)) (n : ℤ)
      (h : N + 1 = n + ((k + 1 : ℕ) : ℤ)), Lmodel.ofDeg F.sub n (k + 1) h P.bdClsAt = 0

variable {F}

namespace LiftingPairNull

variable (hF : F.LiftingPairNull) {n : ℤ} {k : ℕ}
include hF

/-- (L2) in the level degrees of the colimit. -/
lemma of_bdClsAt {D : SymPoincare (F.quot.czIter k).inv (Lmodel.deg n k + 1)}
    (hN : 0 ≤ Lmodel.deg n k + 1) (hD : NullCobordant D)
    (P : F.LiftingPairAt (k + 1) ((CZ.lineData (F.quot.czIter k)).sym D)) :
    Lmodel.of F.sub n (k + 1) P.bdClsAt = 0 :=
  hF k D hN hD P n (by rw [Lmodel.deg_eq]; push_cast; ring)

/-- **Uniqueness of lifting pairs** (from (L2) applied to `D ⊕ -D` and the lifting pair
`P₁ ⊕ -P₂`): two lifting pairs at level `k + 1` of `D ⊗ ℝ` have the same boundary class in the
colimit. -/
lemma of_bdClsAt_eq {D : SymPoincare (F.quot.czIter k).inv (Lmodel.deg n k + 1)}
    (hN : 0 ≤ Lmodel.deg n k + 1)
    (P₁ P₂ : F.LiftingPairAt (k + 1) ((CZ.lineData (F.quot.czIter k)).sym D)) :
    Lmodel.of F.sub n (k + 1) P₁.bdClsAt = Lmodel.of F.sub n (k + 1) P₂.bdClsAt := by
  let L := CZ.lineData (F.quot.czIter k)
  let b : ∀ r, BinaryBicone (D.C.X r) (D.neg.C.X r) :=
    fun r ↦ (Lconc.ub D D.neg r).toBinaryBicone
  let c : ∀ r, BinaryBicone ((L.sym D).C.X r) ((L.sym D.neg).C.X r) :=
    fun r ↦ (Lconc.ub (L.sym D) (L.sym D.neg) r).toBinaryBicone
  let P₂' : F.LiftingPairAt (k + 1) (L.sym D.neg) :=
    P₂.negAt.ofIsometryAt (.ofEq' (L.sym_neg D).symm)
  let Q : F.LiftingPairAt (k + 1) (L.sym (D.sum D.neg b)) :=
    (P₁.sumAt P₂' c).ofIsometryAt (L.symSumIsometry D D.neg b c).symm
  have h := hF.of_bdClsAt hN (D.nullCobordant_sum_neg_self b) Q
  simp only [Q, P₂', LiftingPairAt.ofIsometryAt_bdClsAt, LiftingPairAt.sumAt_bdClsAt,
    LiftingPairAt.negAt_bdClsAt, map_add, map_neg] at h
  exact add_neg_eq_zero.mp h

/-- Uniqueness for the sign-normalized boundary classes. -/
lemma of_sgnBdClsAt_eq {D : SymPoincare (F.quot.czIter k).inv (Lmodel.deg n k + 1)}
    (hN : 0 ≤ Lmodel.deg n k + 1)
    (P₁ P₂ : F.LiftingPairAt (k + 1) ((CZ.lineData (F.quot.czIter k)).sym D)) :
    Lmodel.of F.sub n (k + 1) P₁.sgnBdClsAt = Lmodel.of F.sub n (k + 1) P₂.sgnBdClsAt := by
  rw [LiftingPairAt.sgnBdClsAt, LiftingPairAt.sgnBdClsAt, Units.smul_def, Units.smul_def,
    map_zsmul, map_zsmul, hF.of_bdClsAt_eq hN P₁ P₂]

end LiftingPairNull

/-! ### The boundary on a level -/

variable (F) in
/-- **The value of `∂` on a closed complex `D` at level `k`** (`dim D = n + k + 1`):
`ι_{k+1}(σ_{k+1} [Y])` for the chosen lifting pair `(Y ⟶ W)` at level `k + 1` of `D ⊗ ℝ`
(blueprint §6, `sgnBdClsAt`), and `0` in negative degree `n + k + 1 < 0` (where
`Lconc = 0` and lifting pairs need not exist). -/
def bdVal (n : ℤ) (k : ℕ) (D : SymPoincare (F.quot.czIter k).inv (Lmodel.deg n k + 1)) :
    Lmodel F.sub n :=
  if hN : 0 ≤ Lmodel.deg n k + 1 then
    Lmodel.of F.sub n (k + 1) (F.nonempty_liftingPairAt_succ k D hN).some.sgnBdClsAt
  else 0

variable {n : ℤ} {k : ℕ}

/-- **`∂` may be computed with any lifting pair** (given (L2)). -/
lemma bdVal_eq (hF : F.LiftingPairNull)
    {D : SymPoincare (F.quot.czIter k).inv (Lmodel.deg n k + 1)} (hN : 0 ≤ Lmodel.deg n k + 1)
    (P : F.LiftingPairAt (k + 1) ((CZ.lineData (F.quot.czIter k)).sym D)) :
    F.bdVal n k D = Lmodel.of F.sub n (k + 1) P.sgnBdClsAt := by
  rw [bdVal, dif_pos hN]
  exact hF.of_sgnBdClsAt_eq hN _ P

lemma bdVal_of_neg {D : SymPoincare (F.quot.czIter k).inv (Lmodel.deg n k + 1)}
    (hN : Lmodel.deg n k + 1 < 0) : F.bdVal n k D = 0 := by
  rw [bdVal, dif_neg (not_le.mpr hN)]

/-- **Additivity**: the sum of lifting pairs is a lifting pair of the sum. -/
lemma bdVal_sum (hF : F.LiftingPairNull) (D₁ D₂ : SymPoincare (F.quot.czIter k).inv
    (Lmodel.deg n k + 1)) (c : ∀ r, BinaryBicone (D₁.C.X r) (D₂.C.X r)) :
    F.bdVal n k (D₁.sum D₂ c) = F.bdVal n k D₁ + F.bdVal n k D₂ := by
  by_cases hN : 0 ≤ Lmodel.deg n k + 1
  · obtain ⟨P₁⟩ := F.nonempty_liftingPairAt_succ k D₁ hN
    obtain ⟨P₂⟩ := F.nonempty_liftingPairAt_succ k D₂ hN
    let L := CZ.lineData (F.quot.czIter k)
    let c' : ∀ r, BinaryBicone ((L.sym D₁).C.X r) ((L.sym D₂).C.X r) :=
      fun r ↦ (Lconc.ub (L.sym D₁) (L.sym D₂) r).toBinaryBicone
    let Q : F.LiftingPairAt (k + 1) (L.sym (D₁.sum D₂ c)) :=
      (P₁.sumAt P₂ c').ofIsometryAt (L.symSumIsometry D₁ D₂ c c').symm
    rw [bdVal_eq hF hN Q, bdVal_eq hF hN P₁, bdVal_eq hF hN P₂, ← map_add]
    congr 1
    simp only [Q, LiftingPairAt.sgnBdClsAt, LiftingPairAt.ofIsometryAt_bdClsAt,
      LiftingPairAt.sumAt_bdClsAt, smul_add]
  · rw [bdVal_of_neg (not_le.mp hN), bdVal_of_neg (not_le.mp hN), bdVal_of_neg (not_le.mp hN),
      add_zero]

/-- **(L2)**: null-cobordant complexes have boundary `0`. -/
lemma bdVal_eq_zero (hF : F.LiftingPairNull)
    {D : SymPoincare (F.quot.czIter k).inv (Lmodel.deg n k + 1)} (hD : NullCobordant D) :
    F.bdVal n k D = 0 := by
  by_cases hN : 0 ≤ Lmodel.deg n k + 1
  · obtain ⟨P⟩ := F.nonempty_liftingPairAt_succ k D hN
    rw [bdVal_eq hF hN P, LiftingPairAt.sgnBdClsAt, Units.smul_def, map_zsmul,
      hF.of_bdClsAt hN hD P, smul_zero]
  · exact bdVal_of_neg (not_le.mp hN)

variable (F) in
/-- **The boundary on the level `k`**, `Lconc (C_ℤ^{∘k}(A/U)) (n + k + 1) → Lmodel U n`. -/
def bdLevel (hF : F.LiftingPairNull) (n : ℤ) (k : ℕ) :
    Lconc (F.quot.czIter k) (Lmodel.deg n k + 1) →+ Lmodel F.sub n :=
  Lconc.lift (F.bdVal n k) (fun P Q _ ↦ bdVal_sum hF P Q _) (fun _ hP ↦ bdVal_eq_zero hF hP)

@[simp]
lemma bdLevel_cls (hF : F.LiftingPairNull)
    (D : SymPoincare (F.quot.czIter k).inv (Lmodel.deg n k + 1)) :
    F.bdLevel hF n k (Lconc.cls D) = F.bdVal n k D :=
  Lconc.lift_cls _ _ _ D

/-- **Compatibility with the transitions** (`lineNeg_sgnBdClsAt` and uniqueness):
`∂ [D ⊗ ℝ] = ∂ [D]`. -/
lemma bdLevel_tensorLine (hF : F.LiftingPairNull)
    (x : Lconc (F.quot.czIter k) (Lmodel.deg n k + 1)) :
    F.bdLevel hF n (k + 1) (Lconc.tensorLine (F.quot.czIter k) (Lmodel.deg n k + 1) x) =
      F.bdLevel hF n k x := by
  by_cases hN : 0 ≤ Lmodel.deg n k + 1
  · obtain ⟨D, rfl⟩ := Lconc.cls_surjective x
    obtain ⟨P⟩ := F.nonempty_liftingPairAt_succ k D hN
    have hN' : 0 ≤ Lmodel.deg n (k + 1) + 1 := by rw [Lmodel.deg_succ]; omega
    rw [Lconc.tensorLine_cls, bdLevel_cls, bdLevel_cls, bdVal_eq hF hN P,
      bdVal_eq hF hN' P.lineNeg, LiftingPairAt.lineNeg_sgnBdClsAt]
    exact Lmodel.of_tensorLine (k + 1) P.sgnBdClsAt
  · obtain ⟨D, rfl⟩ := Lconc.cls_surjective x
    rw [Lconc.cls_eq_zero_of_neg (not_le.mp hN) D, map_zero, map_zero, map_zero]

variable (F) in
/-- The level maps in the degrees `deg (n + 1) k` of `Lmodel (A/U) (n + 1)`. -/
def bdLevelDeg (hF : F.LiftingPairNull) (n : ℤ) (k : ℕ) :
    Lconc (F.quot.czIter k) (Lmodel.deg (n + 1) k) →+ Lmodel F.sub n :=
  (F.bdLevel hF n k).comp (Lconc.castDeg (Lmodel.deg_add n 1 k)).toAddMonoidHom

lemma bdLevelDeg_apply (hF : F.LiftingPairNull) (x : Lconc (F.quot.czIter k)
    (Lmodel.deg (n + 1) k)) :
    F.bdLevelDeg hF n k x = F.bdLevel hF n k (Lconc.castDeg (Lmodel.deg_add n 1 k) x) := rfl

lemma bdLevelDeg_tensorLine (hF : F.LiftingPairNull)
    (x : Lconc (F.quot.czIter k) (Lmodel.deg (n + 1) k)) :
    F.bdLevelDeg hF n (k + 1) (Lconc.tensorLine (F.quot.czIter k) (Lmodel.deg (n + 1) k) x) =
      F.bdLevelDeg hF n k x :=
  (congrArg (F.bdLevel hF n (k + 1))
    (Lconc.tensorLine_castDeg (Lmodel.deg_add n 1 k) x).symm).trans (bdLevel_tensorLine hF _)

end KaroubiFiltration

/-! ### The boundary map `∂` on the colimit model -/

namespace Lmodel

variable {A B : InvCat}

/-- **The boundary map** `∂ : Lmodel (A/U) (n + 1) → Lmodel U n` of the colimit model, given
(L2): on the level `k`, `∂ ι_k [D] = ι_{k+1} ((-1)^{k+1} [Y])` for any lifting pair `(Y ⟶ W)` at
level `k + 1` of `D ⊗ ℝ` (`bdry_ofDeg_cls`), and `0` in negative level degree. -/
def bdry (F : KaroubiFiltration A) (hF : F.LiftingPairNull) (n : ℤ) :
    Lmodel F.quot (n + 1) →+ Lmodel F.sub n :=
  lift F.quot (n + 1) (F.bdLevelDeg hF n) fun _ x ↦ F.bdLevelDeg_tensorLine hF x

variable {F : KaroubiFiltration A} (hF : F.LiftingPairNull)

@[simp]
lemma bdry_of (n : ℤ) (k : ℕ) (x : Lconc (F.quot.czIter k) (deg (n + 1) k)) :
    bdry F hF n (of F.quot (n + 1) k x) =
      F.bdLevel hF n k (Lconc.castDeg (deg_add n 1 k) x) :=
  lift_of _ _ k x

/-- **The defining formula of `∂`** (blueprint §3.2, §6): for a closed `(N+1)`-complex `D` over
`C_ℤ^{∘k}(A/U)` with `N = n + k ≥ -1` and any lifting pair `P` at level `k + 1` of `D ⊗ ℝ`,
`∂ [D] = (-1)^{k+1} [∂P]` in the colimit. -/
theorem bdry_ofDeg_cls {n : ℤ} {k : ℕ} {N : ℤ} (hNk : N = n + k)
    (D : SymPoincare (F.quot.czIter k).inv (N + 1)) (hN : 0 ≤ N + 1)
    (P : F.LiftingPairAt (k + 1) ((CZ.lineData (F.quot.czIter k)).sym D)) :
    bdry F hF n (ofDeg F.quot (n + 1) k (by rw [hNk]; ring) (Lconc.cls D)) =
      ofDeg F.sub n (k + 1) (by rw [hNk]; push_cast; ring) P.sgnBdClsAt := by
  obtain rfl : N = deg n k := hNk.trans (deg_eq n k).symm
  rw [ofDeg_apply, bdry_of, Lconc.castDeg_castDeg]
  exact (F.bdLevel_cls hF D).trans (F.bdVal_eq hF hN P)

/-! #### Naturality -/

variable {F' : KaroubiFiltration B} (hF' : F'.LiftingPairNull) (Φ : FiltrationHom F F')

include hF hF' in
/-- Naturality on a level: lifting pairs map to lifting pairs (`LiftingPairAt.map`), and
`(Φ X) ⊗ ℝ ≃ Φ (X ⊗ ℝ)` (`symMapIsometry`). -/
lemma bdLevel_map (n : ℤ) (k : ℕ) (y : Lconc (F.quot.czIter k) (deg n k + 1)) :
    F'.bdLevel hF' n k (Lconc.map (CZ.mapIter k Φ.quot) y) =
      map Φ.sub n (F.bdLevel hF n k y) := by
  obtain ⟨D, rfl⟩ := Lconc.cls_surjective y
  by_cases hN : 0 ≤ deg n k + 1
  · obtain ⟨P⟩ := F.nonempty_liftingPairAt_succ k D hN
    rw [Lconc.map_cls, KaroubiFiltration.bdLevel_cls, KaroubiFiltration.bdLevel_cls,
      F'.bdVal_eq (D := D.map (CZ.mapIter k Φ.quot)) hF' hN ((P.map Φ).ofIsometryAt
        ((CZ.lineHom (CZ.mapIter k Φ.quot)).symMapIsometry D).symm),
      F.bdVal_eq hF hN P, map_of, KaroubiFiltration.LiftingPairAt.ofIsometryAt_sgnBdClsAt,
      KaroubiFiltration.LiftingPairAt.map_sgnBdClsAt]
  · rw [Lconc.cls_eq_zero_of_neg (not_le.mp hN) D, map_zero, map_zero, map_zero, map_zero]

include hF hF' in
/-- **`bdry_natural`** (H1 naturality of `∂` under maps of filtrations). -/
theorem bdry_natural (n : ℤ) :
    (bdry F' hF' n).comp (map Φ.quot (n + 1)) = (map Φ.sub n).comp (bdry F hF n) :=
  hom_ext fun k x ↦ by
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, map_of, bdry_of, bdry_of,
      ← Lconc.map_castDeg]
    exact bdLevel_map hF hF' Φ n k _

/-! #### The pair formula (H2) with `bsign = 1` -/

/-- **`bsign`**: the universal sign of H2 is `+1` in every degree (blueprint §6, signs). -/
def bsign : ℤ → ℤˣ := fun _ ↦ 1

include hF in
/-- **`bdry_pair`** (H2): a pair `X` over `A` with boundary in `U` is a level-`0` lifting pair
of `X.toQuot`, so `∂ [X.toQuot] = [X.bdLift]` (via its line `-(X ⊗ ℝ)` at level `1`,
`liftingPairAt_lineNeg_sgnBdClsAt`). -/
theorem bdry_pair {N : ℤ} (X : SymPair A.inv N) (hU : ∀ r, F.U (X.bd.C.X r)) :
    bdry F hF N (cls F.quot (N + 1) (Lconc.cls (X.toQuot F hU))) =
      bsign N • cls F.sub N (Lconc.cls (X.bdLift F hU)) := by
  rw [bsign, one_smul, cls_eq_of, bdry_of]
  change F.bdLevel hF N 0 (Lconc.cls (X.toQuot F hU)) = _
  rw [KaroubiFiltration.bdLevel_cls]
  by_cases hN : 0 ≤ N + 1
  · rw [F.bdVal_eq (n := N) (k := 0) hF hN (X.liftingPairAt F hU).lineNeg,
      SymPair.liftingPairAt_lineNeg_sgnBdClsAt, cls_eq_of]
    exact of_tensorLine (A := F.sub) (n := N) 0 (Lconc.cls (X.bdLift F hU))
  · rw [F.bdVal_of_neg (n := N) (k := 0) (not_le.mp hN), Lconc.cls_eq_zero_of_neg (by omega),
      map_zero]

end Lmodel

/-! ### Equivalent form of (L2): well-definedness on classes -/

namespace KaroubiFiltration

variable {A : InvCat} (F : KaroubiFiltration A)

/-- **Uniqueness of lifting pairs (L2), class form**: lifting pairs at level `k + 1` of the
transition images `D₁ ⊗ ℝ`, `D₂ ⊗ ℝ` of closed complexes with `[D₁] = [D₂]` have the same
boundary class in the colimit.  Equivalent to `LiftingPairNull` (`liftingPairUnique_iff`). -/
def LiftingPairUnique : Prop :=
  ∀ (k : ℕ) {N : ℤ} (D₁ D₂ : SymPoincare (F.quot.czIter k).inv (N + 1)), 0 ≤ N + 1 →
    Lconc.cls D₁ = Lconc.cls D₂ →
    ∀ (P₁ : F.LiftingPairAt (k + 1) ((CZ.lineData (F.quot.czIter k)).sym D₁))
      (P₂ : F.LiftingPairAt (k + 1) ((CZ.lineData (F.quot.czIter k)).sym D₂)) (n : ℤ)
      (h : N + 1 = n + ((k + 1 : ℕ) : ℤ)),
      Lmodel.ofDeg F.sub n (k + 1) h P₁.bdClsAt = Lmodel.ofDeg F.sub n (k + 1) h P₂.bdClsAt

variable {F}

/-- (L2) in null-cobordism form gives the class form. -/
theorem LiftingPairNull.unique (hF : F.LiftingPairNull) : F.LiftingPairUnique := by
  intro k N D₁ D₂ hN h₁₂ P₁ P₂ n h
  obtain rfl : N = Lmodel.deg n k := by rw [Lmodel.deg_eq]; push_cast at h; omega
  have e : Lmodel.of F.sub n (k + 1) P₁.sgnBdClsAt = Lmodel.of F.sub n (k + 1) P₂.sgnBdClsAt := by
    rw [← F.bdVal_eq hF hN P₁, ← F.bdVal_eq hF hN P₂, ← F.bdLevel_cls hF, ← F.bdLevel_cls hF, h₁₂]
  rw [LiftingPairAt.sgnBdClsAt, LiftingPairAt.sgnBdClsAt, Units.smul_def, Units.smul_def,
    map_zsmul, map_zsmul, ← Units.smul_def, ← Units.smul_def, smul_left_cancel_iff] at e
  exact e

/-- The class form of (L2) gives the null-cobordism form (apply it to `D` and `D ⊕ D`). -/
theorem LiftingPairUnique.null (hF : F.LiftingPairUnique) : F.LiftingPairNull := by
  intro k N D hN hD P n h
  let L := CZ.lineData (F.quot.czIter k)
  let c : ∀ r, BinaryBicone (D.C.X r) (D.C.X r) := fun r ↦ (Lconc.ub D D r).toBinaryBicone
  let c' : ∀ r, BinaryBicone ((L.sym D).C.X r) ((L.sym D).C.X r) :=
    fun r ↦ (Lconc.ub (L.sym D) (L.sym D) r).toBinaryBicone
  let Q : F.LiftingPairAt (k + 1) (L.sym (D.sum D c)) :=
    (P.sumAt P c').ofIsometryAt (L.symSumIsometry D D c c').symm
  have hD0 : Lconc.cls D = 0 := Lconc.cls_eq_zero hD
  have e := hF k D (D.sum D c) hN (by rw [Lconc.cls_sum, hD0, add_zero]) P Q n h
  simp only [Q, LiftingPairAt.ofIsometryAt_bdClsAt, LiftingPairAt.sumAt_bdClsAt,
    map_add] at e
  exact left_eq_add.mp e

/-- **The two forms of (L2) are equivalent.** -/
theorem liftingPairUnique_iff : F.LiftingPairUnique ↔ F.LiftingPairNull :=
  ⟨LiftingPairUnique.null, LiftingPairNull.unique⟩

end KaroubiFiltration

/-! ### The interface fields for the model -/

/-- (L2) for every Karoubi filtration: the hypothesis under which the model has `bdry`. -/
def LiftingPairNullAll : Prop :=
  ∀ (A : InvCat) (F : KaroubiFiltration A), F.LiftingPairNull

namespace Lmodel

variable (hL : LiftingPairNullAll)

/-- The interface field `bdry` of the model (`Interface.lean`, H1). -/
def bdryAll {A : InvCat} (F : KaroubiFiltration A) (n : ℤ) :
    Lmodel F.quot (n + 1) →+ Lmodel F.sub n :=
  bdry F (hL A F) n

/-- The interface field `bdry_natural` of the model (H1). -/
theorem bdryAll_natural {A B : InvCat} {F : KaroubiFiltration A} {F' : KaroubiFiltration B}
    (Φ : FiltrationHom F F') (n : ℤ) :
    (bdryAll hL F' n).comp (map Φ.quot (n + 1)) = (map Φ.sub n).comp (bdryAll hL F n) :=
  bdry_natural (hL A F) (hL B F') Φ n

/-- The interface field `bdry_pair` of the model (H2), with `bsign = 1`. -/
theorem bdryAll_pair {A : InvCat} (F : KaroubiFiltration A) {N : ℤ} (X : SymPair A.inv N)
    (hU : ∀ r, F.U (X.bd.C.X r)) :
    bdryAll hL F N (cls F.quot (N + 1) (Lconc.cls (X.toQuot F hU))) =
      bsign N • cls F.sub N (Lconc.cls (X.bdLift F hU)) :=
  bdry_pair (hL A F) X hU

end Lmodel

end

end HSFormal.LTheory
