import HSFormal.LTheory.Model.Bdry
import HSFormal.LTheory.Model.Triads

/-!
# Exactness of the localization sequence of the colimit model (lower L-theory model, module 19)

`blueprint/lower-L-construction.md` §3.2 ("H1 exactness"), §4 row 19, §6: for a Karoubi
filtration `F : U ⊂ A` and the boundary `∂ = Lmodel.bdry F hF n` of `Bdry.lean` (defined given
(L2), `hF : F.LiftingPairNull`), the three exactness fields of `LowerLTheory` (`Interface.lean`)
for `L = Lmodel`:

  `L_n(U) ⟶ L_n(A) ⟶ L_n(A/U) ⟶∂ L_{n-1}(U)`, i.e.
  `exact_A : Function.Exact (map F.incl n) (map F.proj n)`,
  `exact_Q : Function.Exact (map F.proj (n + 1)) (bdry F hF n)`,
  `exact_U : Function.Exact (bdry F hF n) (map F.incl n)`.

## Main results

* `Lmodel.exact_U hF n` and `Lmodel.exact_Q hF n`: **proved from `hF : F.LiftingPairNull`
  alone** (no further hypothesis).
* `Lmodel.exact_A hA n`: proved from the separate hypothesis
  `hA : F.LiftingClosedSub`, **(L2) for lifting pairs with empty boundary** (`Y = 0`): a closed
  complex `W` over `C_ℤ^{∘(k+1)}(A)` with `W/U ≃ D ⊗ ℝ`, `D` null-cobordant over
  `C_ℤ^{∘k}(A/U)`, comes from `U` in the colimit.  This is the part of (L2) that `LiftingPairNull`
  does not record (it only records that the boundary `Y` of a lifting pair dies, which for
  `Y = 0` is empty).  `liftingClosedSub_iff`: it is equivalent to the plain form
  `LiftingClosedSub'` (a closed complex over `A` whose image over `A/U` bounds comes from `U`).
* Interface form: `Lmodel.exactAll_A hA F n`, `exactAll_Q hL F n`, `exactAll_U hL F n` (with
  `bdryAll hL`, `hL : LiftingPairNullAll`, `hA : LiftingClosedSubAll`).
* The composites: `map_proj_map_incl` (no hypothesis), `bdry_map_proj`, `map_incl_bdry`.

## Proofs (blueprint §3.2)

* *Composites vanish*: complexes of `U` vanish in `A/U` (`isZero_proj_obj`, via the strict isos
  `czIterSubIso`, `czIterQuotIso`); a closed complex `Q` over `A` is its own lifting pair with
  zero boundary (`PairData.ofClosedZero`, `SymPoincare.closedPair`,
  `KaroubiFiltration.closedLiftingPairAt`); `W` null-bounds `incl(Y)`
  (`LiftingPairAt.map_incl_bdClsAt`).
* `bdry_ofDeg_liftingPairAt` (H2 at level `j`): `∂[D] = σ_j[∂P]` for any lifting pair `P` at the
  level of `D` itself (via `P.lineNeg` and `bdry_ofDeg_cls`).
* *exact_U*: if `incl(Q) = ∂W` over `A` (after transitions), then `W` is a lifting pair of
  `W.toQuot` with boundary `Q`, so `[Q] = ±∂[W.toQuot]`.
* *exact_Q*: if `∂[D] = 0`, iterate `lineNeg` (`exists_liftingPairAt_transit`) to a level where
  the boundary `Y` of a lifting pair `(Y ⟶ W)` of (a representative of) `[D]` is null-cobordant,
  `Y = ∂Z` over `U`; the closed union `W ∪_Y -Z` (`PairOn.union`) maps to `[D]`
  (`exists_cls_eq_map_proj`).  The key input is **excision for unions**
  (`SymPair.isometric_toQuot_union`, R3): `(W ∪_Y Z)/U ≃ W.toQuot` when `Y` and `Z` lie in `U`.
  The inclusion `D_W ⟶ D_W ∪_Y D_Z` is a Kar equivalence modulo `U` because its cokernel
  `Cone(j_Z)` lies in `U` (`KarSplit.isKarEquiv_proj` on `Glue.splitBot`), and the symmetrized
  union structure `δφZ = ι_W δφ_W ι_W^* + ½(G + TG) + H_Z` differs from `ι_W δφ_W ι_W^*` by
  terms through `C_Y` and `D_Z` (`factorsThrough_conjHomotopy_hom`,
  `factorsThrough_transposeHomFamily`).
* *exact_A*: if `proj[P] = 0`, then `proj(P)` bounds at some level and `P ⊗ ℝ` is a closed
  lifting pair of `proj(P) ⊗ ℝ` (`symMapIsometry`); `hA` concludes.

## Negative degrees

As in `Bdry.lean`, levels with negative level degree have `Lconc = 0`
(`Lconc.eq_zero_of_neg`); every case split on the sign of the level degree is trivial on the
negative side, and `LiftingClosedSub` only quantifies over `N ≥ 0`.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression
  homotopyCofiber

noncomputable section

attribute [local implicit_reducible] InvCat.czIter SymPair.map SymPair.closedOfIsZero SymPair.neg
  CZ.mapIter CZ.lineHom SymPoincare.zero PairOn.union PairOn.glue PairOn.toPair

/-! ### Kar split sequences whose third term lies in `U` -/

section KarSplitQuot

variable {A : InvCat} (F : KaroubiFiltration A) {K M Q : ChainComplex A ℤ} {eK : K ⟶ K}
  {eM : M ⟶ M} {eQ : Q ⟶ Q} {i : K ⟶ M} {q : M ⟶ Q}

/-- In a Kar split sequence `0 ⟶ K ⟶ M ⟶ Q ⟶ 0` whose third term has all chain objects in `U`,
the retraction `t` is a chain map modulo `U`. -/
lemma KarSplit.factorsThrough_comm (S : KarSplit eK eM eQ i q) (heK : eK ≫ eK = eK)
    (heM : eM ≫ eM = eM) (hQ : ∀ n, F.U (Q.X n)) (a b : ℤ) :
    FactorsThrough F.U (S.t a ≫ K.d a b - M.d a b ≫ S.t b) := by
  have htK (n : ℤ) : S.t n ≫ eK.f n = S.t n := by
    conv_lhs => rw [← S.t_kar n]
    rw [assoc, assoc, ← comp_f, heK, S.t_kar]
  have htM (n : ℤ) : eM.f n ≫ S.t n = S.t n := by
    conv_lhs => rw [← S.t_kar n]
    rw [← assoc, ← comp_f, heM, S.t_kar]
  have e : S.t a ≫ K.d a b - M.d a b ≫ S.t b =
      -(q.f a ≫ S.s a ≫ M.d a b ≫ S.t b) := by
    have h1 : S.t a ≫ K.d a b = S.t a ≫ i.f a ≫ M.d a b ≫ S.t b := by
      rw [i.comm_assoc, S.it, ← eK.comm, ← assoc, htK]
    have h2 : S.t a ≫ i.f a = eM.f a - q.f a ≫ S.s a := by
      rw [← S.total a]; abel
    rw [h1, ← assoc (S.t a), h2, sub_comp, eM.comm_assoc, htM]
    simp
  rw [e]
  exact (FactorsThrough.of_mem (hQ a) (q.f a) (S.s a ≫ M.d a b ≫ S.t b)).neg

/-- The retraction of a Kar split sequence with third term in `U`, as a chain map modulo `U`. -/
@[simps]
def KarSplit.quotInv (S : KarSplit eK eM eQ i q) (heK : eK ≫ eK = eK) (heM : eM ≫ eM = eM)
    (hQ : ∀ n, F.U (Q.X n)) : F.proj.mapC M ⟶ F.proj.mapC K where
  f n := F.proj.F.map (S.t n)
  comm' a b _ := by
    simp only [InvFunctor.mapC, Functor.mapHomologicalComplex_obj_d, ← Functor.map_comp]
    exact (F.proj_map_eq_iff _ _).mpr (S.factorsThrough_comm F heK heM hQ a b)

/-- **A Kar split sequence `0 ⟶ K ⟶ M ⟶ Q ⟶ 0` with `Q` in `U` gives a Kar equivalence
`K ≃ M` modulo `U`.** -/
theorem KarSplit.isKarEquiv_proj (S : KarSplit eK eM eQ i q) (heK : eK ≫ eK = eK)
    (heM : eM ≫ eM = eM) (hQ : ∀ n, F.U (Q.X n)) :
    IsKarEquiv (F.proj.mapH eK) (F.proj.mapH eM) (F.proj.mapH i) := by
  refine ⟨S.quotInv F heK heM hQ, ?_, ⟨Homotopy.ofEq ?_⟩, ⟨Homotopy.ofEq ?_⟩⟩
  · ext n
    simp only [InvFunctor.mapH, comp_f, Functor.mapHomologicalComplex_map_f, quotInv_f,
      ← Functor.map_comp, S.t_kar]
  · ext n
    simp only [InvFunctor.mapH, comp_f, Functor.mapHomologicalComplex_map_f, quotInv_f,
      ← Functor.map_comp]
    refine (F.proj_map_eq_iff _ _).mpr ?_
    have e : S.t n ≫ i.f n - eM.f n = -(q.f n ≫ S.s n) := by rw [← S.total n]; abel
    rw [e]
    exact (FactorsThrough.of_mem (hQ n) (q.f n) (S.s n)).neg
  · ext n
    simp only [InvFunctor.mapH, comp_f, Functor.mapHomologicalComplex_map_f, quotInv_f,
      ← Functor.map_comp, S.it]

end KarSplitQuot

/-! ### A closed complex as a pair on the zero boundary -/

namespace PairData

variable {A : InvCat} {N : ℤ}

/-- **A closed `(N+1)`-dimensional complex `Q` as a pair on the zero complex** `zeroP`: the pair
`(0 : 0 ⟶ (C, p), (φ, 0))`, with relative structure `φ` (as `PairData.ofClosed`, whose boundary
is `(C, 0)`; here the boundary has zero chain objects, so it lies in every `U`). -/
@[implicit_reducible]
def ofClosedZero (Q : SymPoincare A.inv (N + 1)) : PairData (zeroP (J := A.inv) (N := N)) where
  D := Q.C
  pD := Q.p
  pD_idem := Q.p_idem
  support := Q.support
  j := 0
  j_kar := by simp
  δφ := homotopyCongr (ofClosed Q).δφ (by simp) rfl
  δφ_kar := (ofClosed Q).δφ_kar
  symm := (ofClosed Q).symm

@[simp] lemma ofClosedZero_D (Q : SymPoincare A.inv (N + 1)) : (ofClosedZero Q).D = Q.C := rfl

@[simp] lemma ofClosedZero_pD (Q : SymPoincare A.inv (N + 1)) : (ofClosedZero Q).pD = Q.p := rfl

@[simp] lemma ofClosedZero_j (Q : SymPoincare A.inv (N + 1)) : (ofClosedZero Q).j = 0 := rfl

@[simp]
lemma relTop_ofClosedZero (Q : SymPoincare A.inv (N + 1)) (r : ℤ) :
    relTop (ofClosedZero Q).δφ r = Q.φ.f r :=
  relTop_ofClosed Q r

lemma relDuality_ofClosedZero (Q : SymPoincare A.inv (N + 1)) :
    relDuality (ofClosedZero Q).δφ =
      dualHom A.inv (N + 1) (inr (0 : (zeroP (J := A.inv) (N := N)).C ⟶ Q.C)) ≫ Q.φ := by
  ext r
  simp [relDuality_f]

/-- The closed complex on the zero boundary is a Poincaré pair. -/
theorem isPoincare_ofClosedZero (Q : SymPoincare A.inv (N + 1)) : (ofClosedZero Q).IsPoincare := by
  rw [IsPoincare, relDuality_ofClosedZero]
  have hc : (ofClosedZero Q).coneIdem =
      coneMap (j := (0 : (zeroP (J := A.inv) (N := N)).C ⟶ Q.C))
        (j' := (0 : (zeroP (J := A.inv) (N := N)).C ⟶ Q.C)) 0 Q.p (by simp) := rfl
  rw [hc]
  have h₁ := (isKarEquiv_inr_zero (B := (zeroP (J := A.inv) (N := N)).C) Q.p_idem).dualHom
    (J := A.inv) (N := N + 1)
  refine (h₁.comp Q.poincare (dualHom_idem (coneMap_idem _ (by simp) Q.p_idem))
    (dualHom_idem Q.p_idem) Q.p_idem).of_eq ?_
  rw [dualHom_comp, assoc, Q.dualHom_p_comp_φ]

end PairData

namespace SymPoincare

variable {A : InvCat} {N : ℤ}

/-- A closed `(N+1)`-complex as a Poincaré pair with zero boundary. -/
abbrev closedPair (Q : SymPoincare A.inv (N + 1)) : SymPair A.inv N :=
  ((PairData.ofClosedZero Q).toPairOn (PairData.isPoincare_ofClosedZero Q)).toPair

lemma closedPair_bd (Q : SymPoincare A.inv (N + 1)) :
    Q.closedPair.bd = zeroP (J := A.inv) (N := N) := rfl

lemma closedPair_mem {A : InvCat} (F : KaroubiFiltration A) (Q : SymPoincare A.inv (N + 1))
    (r : ℤ) : F.U (Q.closedPair.bd.C.X r) :=
  F.U.prop_of_isZero (isZero_zeroP_X r)

/-- The image modulo `U` of the closed pair of `Q` is the image of `Q`. -/
lemma closedPair_toQuot (F : KaroubiFiltration A) (Q : SymPoincare A.inv (N + 1)) :
    Q.closedPair.toQuot F (closedPair_mem F Q) = Q.map F.proj := by
  refine SymPoincare.ext_of_φ rfl HEq.rfl (heq_of_eq ?_)
  ext r
  rw [SymPair.toClosed_φ_f]
  simp only [SymPoincare.map_φ, InvFunctor.mapDual_f]
  exact congrArg _ (PairData.relTop_ofClosed Q r)

/-- The boundary of the closed pair has class `0`. -/
lemma cls_closedPair_bdLift (F : KaroubiFiltration A) (Q : SymPoincare A.inv (N + 1)) :
    Lconc.cls (Q.closedPair.bdLift F (closedPair_mem F Q)) = 0 :=
  Lconc.cls_eq_zero_of_p_eq_zero (by ext r; rfl)

end SymPoincare

/-! ### Excision for unions along a boundary in `U` -/

section UnionQuot

variable {A : InvCat} (F : KaroubiFiltration A) {N : ℤ}

/-- Components of a homotopy into a complex with chain objects in `U` lie in `I_U`. -/
lemma factorsThrough_hom_of_target {X Y : ChainComplex A ℤ} {a b : X ⟶ Y} (H : Homotopy a b)
    (hY : ∀ k, F.U (Y.X k)) (i k : ℤ) : FactorsThrough F.U (H.hom i k) := by
  simpa using FactorsThrough.of_mem (hY k) (H.hom i k) (𝟙 _)

/-- The conjugation homotopy `f ψ f^* ≃ f' ψ f'^*` of a homotopy `f ≃ f'` out of a complex with
chain objects in `U` has components in `I_U`. -/
lemma factorsThrough_conjHomotopy_hom {C C' : ChainComplex A ℤ} {f f' : C ⟶ C'}
    (Hf : Homotopy f f') (ψ : dualComplex A.inv N C ⟶ C) (hC : ∀ r, F.U (C.X r)) (i k : ℤ) :
    FactorsThrough F.U ((conjHomotopy Hf (Homotopy.refl ψ)).hom i k) := by
  simp only [conjHomotopy, Homotopy.comp, Homotopy.trans_hom, Homotopy.compRight_hom,
    Homotopy.compLeft_hom, Homotopy.refl]
  refine ((factorsThrough_hom_of_target F _ (fun k ↦ hC (N - k)) i k).comp_right _).add
    (FactorsThrough.comp_left _ (((factorsThrough_hom_of_target F _ hC i k).comp_right _).add ?_))
  simpa using FactorsThrough.of_mem (hC i) (ψ.f i) (Hf.hom i k)

/-- Transposes of families in `I_U` lie in `I_U`. -/
lemma factorsThrough_transposeHomFamily {C D : ChainComplex A ℤ}
    {h : ∀ i j, (dualComplex A.inv N C).X i ⟶ D.X j} (hh : ∀ i j, FactorsThrough F.U (h i j))
    (i k : ℤ) : FactorsThrough F.U (transposeHomFamily A.inv N h i k) := by
  rw [transposeHomFamily, Units.smul_def]
  exact (((hh _ _).star A.inv).comp_right _).smul (R := ℤ) _

lemma isKarEquiv_idem_comp {X Y : ChainComplex A ℤ} {e : X ⟶ X} {e' : Y ⟶ Y} {f : X ⟶ Y}
    (h : IsKarEquiv e e' f) (he : e ≫ e = e) : IsKarEquiv e e' (e ≫ f) := by
  obtain ⟨g, hg, ⟨H₁⟩, ⟨H₂⟩⟩ := h
  have hge : g ≫ e = g := by rw [← hg]; simp [he]
  exact ⟨g, hg, ⟨homotopyCongr H₁ (by rw [← assoc, hge]) rfl⟩,
    ⟨homotopyCongr (H₂.compLeft e) (by simp) (by simp [he])⟩⟩

/-- **Excision for the union along a boundary in `U`** (R3 for `W ∪_Y Z`): if the boundary `Y`
of a pair `W` lies in `U` and `Z` is a pair on `-Y` with all chain objects in `U`, then the closed
union `W ∪_Y Z` represents `W.toQuot` modulo `U`.  The inclusion `D_W ⟶ D_W ∪_Y D_Z` is a Kar
equivalence modulo `U` (its cokernel `Cone(j_Z)` lies in `U`, `Glue.splitBot`), and the union
structure differs from `ι_W δφ_W ι_W^*` by the cross terms through `C_Y` and the terms through
`D_Z`. -/
theorem SymPair.isometric_toQuot_union (W : SymPair A.inv N) (hU : ∀ r, F.U (W.bd.C.X r))
    (Z : PairOn W.bd.neg) (hZ : ∀ r, F.U (Z.D.X r)) :
    SymPoincare.Isometric (W.toQuot F hU) ((W.toPairOn.union Z).map F.proj) := by
  set σ := BdSplit.ofRight W.bd (zeroP (J := A.inv) (N := N)) rfl
  set W' := W.toPairOn
  set ι : W.D ⟶ (W'.union Z).C := Glue.ιW σ W' Z
  have hι : ι ≫ (W'.union Z).p = W.pD ≫ ι := Glue.ιW_pU σ W' Z
  refine W.isometric_toQuot F hU _ (W.pD ≫ ι) ?_ ?_ ?_
  · rw [assoc, hι, W.pD_idem_assoc, W.pD_idem_assoc]
  · have h := (Glue.splitBot σ W' Z).isKarEquiv_proj F W.pD_idem (Glue.pU_idem σ W' Z)
      fun n ↦ cone_X_mem F.U Z.j (hU (n - 1)) (hZ n)
    refine (isKarEquiv_idem_comp h ?_).of_eq ?_
    · rw [← Functor.map_comp]; exact congrArg _ W.pD_idem
    · rw [← Functor.map_comp]; rfl
  · intro r
    have key1 : (Glue.δφZ σ W' Z).hom (r - 1) r = (Glue.HW σ W' Z).hom (r - 1) r +
        ((1 / 2 : ℚ) • ((Glue.G σ W' Z).hom (r - 1) r +
          (transposeHomotopy A.inv N (Glue.G σ W' Z)).hom (r - 1) r) +
          (Glue.HY σ W' Z).hom (r - 1) r) := by
      rw [Glue.δφZ, symmHomotopy_hom, ← transposeHomotopy_hom]
      simp only [Pi.smul_apply, Pi.add_apply, Glue.transposeHomotopy_Hns_hom, Glue.Hns_hom]
      module
    have key2 : (dualHom A.inv (N + 1) (W.pD ≫ ι)).f r ≫ W.top r ≫ (W.pD ≫ ι).f r =
        ((Glue.U σ W' Z).XIsoOfEq (by omega : N + 1 - r = N - (r - 1))).hom ≫
          (Glue.HW σ W' Z).hom (r - 1) r := by
      have h1 : A.inv.star (W.pD.f (N + 1 - r)) ≫ W.top r = W.top r :=
        star_comp_relTop W.δφ W.dualHom_pD_comp_δφ_hom r
      have h2 : W.top r ≫ W.pD.f r = W.top r := by
        simp only [SymPair.top, relTop, assoc, W.δφ_hom_comp_pD]
      simp only [Glue.HW, Homotopy.compRight_hom, Homotopy.compLeft_hom, dualHom_f, comp_f,
        A.inv.star_comp, assoc]
      rw [← star_f_XIsoOfEq_assoc, reassoc_of% h1, reassoc_of% h2]
      simp only [SymPair.top, relTop, assoc]
      rfl
    have hR : FactorsThrough F.U ((1 / 2 : ℚ) • ((Glue.G σ W' Z).hom (r - 1) r +
          (transposeHomotopy A.inv N (Glue.G σ W' Z)).hom (r - 1) r) +
          (Glue.HY σ W' Z).hom (r - 1) r) := by
      have hG (i k : ℤ) : FactorsThrough F.U ((Glue.G σ W' Z).hom i k) :=
        factorsThrough_conjHomotopy_hom F _ _ hU i k
      refine (((hG _ _).add ?_).smul _).add ?_
      · rw [transposeHomotopy_hom]
        exact factorsThrough_transposeHomFamily F hG _ _
      · simp only [Glue.HY, Homotopy.compRight_hom, Homotopy.compLeft_hom]
        rw [← assoc]
        exact FactorsThrough.of_mem (hZ r) _ _
    have hφ : (W'.union Z).φ.f r = relTop (Glue.δφZ σ W' Z) r := rfl
    rw [hφ, key2, relTop, key1, comp_add, sub_add_cancel_left]
    exact (hR.comp_left _).neg

end UnionQuot

/-! ### Lifting pairs at a level: closed complexes, and the image of the boundary in `A` -/

lemma Lconc.eq_zero_of_neg {A : InvCat} {N : ℤ} (hN : N < 0) (x : Lconc A N) : x = 0 := by
  obtain ⟨P, rfl⟩ := Lconc.cls_surjective x
  exact Lconc.cls_eq_zero_of_neg hN P

namespace KaroubiFiltration

variable {A : InvCat} {F : KaroubiFiltration A} {N : ℤ} {j : ℕ}

lemma mapIter_incl_eq (j : ℕ) :
    CZ.mapIter j F.incl = (F.czIterSubIso j).inv ≫ (F.czIter j).incl := by
  rw [← F.czIterSubIso_hom_comp_mapIter_incl, Iso.inv_hom_id_assoc]

lemma mapIter_proj_eq (j : ℕ) :
    CZ.mapIter j F.proj ≫ (F.czIterQuotIso j).inv = (F.czIter j).proj := by
  rw [← F.proj_comp_czIterQuotIso_hom, assoc, Iso.hom_inv_id, comp_id]

/-- **The boundary of a lifting pair vanishes in `A`**: `incl_*[Y] = [∂W] = 0`. -/
lemma LiftingPairAt.map_incl_bdClsAt {D : SymPoincare (F.quot.czIter j).inv (N + 1)}
    (P : F.LiftingPairAt j D) : Lconc.map (CZ.mapIter j F.incl) P.bdClsAt = 0 := by
  rw [LiftingPairAt.bdClsAt, ← AddMonoidHom.comp_apply, ← Lconc.map_comp,
    F.czIterSubIso_hom_comp_mapIter_incl, Lconc.map_cls]
  exact Lconc.cls_eq_zero ⟨P.X, rfl⟩

lemma LiftingPairAt.map_incl_sgnBdClsAt {D : SymPoincare (F.quot.czIter j).inv (N + 1)}
    (P : F.LiftingPairAt j D) : Lconc.map (CZ.mapIter j F.incl) P.sgnBdClsAt = 0 := by
  rw [LiftingPairAt.sgnBdClsAt, Units.smul_def, map_zsmul, P.map_incl_bdClsAt, smul_zero]

variable (F) in
/-- **A closed complex `Q` over `C_ℤ^{∘j}(A)` is a lifting pair at level `j` of its image**
`Q.map (C_ℤ^{∘j} proj)`, with zero boundary (`closedPair`). -/
def closedLiftingPairAt (j : ℕ) (Q : SymPoincare (A.czIter j).inv (N + 1)) :
    F.LiftingPairAt j (Q.map (CZ.mapIter j F.proj)) where
  X := Q.closedPair
  mem := SymPoincare.closedPair_mem (F.czIter j) Q
  iso := .ofEq' (by
    rw [SymPoincare.closedPair_toQuot]
    change _ = Q.map (CZ.mapIter j F.proj ≫ (F.czIterQuotIso j).inv)
    rw [mapIter_proj_eq])

@[simp]
lemma closedLiftingPairAt_bdClsAt (j : ℕ) (Q : SymPoincare (A.czIter j).inv (N + 1)) :
    (F.closedLiftingPairAt j Q).bdClsAt = 0 := by
  rw [LiftingPairAt.bdClsAt]
  change Lconc.map _ (Lconc.cls (Q.closedPair.bdLift (F.czIter j) _)) = 0
  rw [SymPoincare.cls_closedPair_bdLift, map_zero]

@[simp]
lemma closedLiftingPairAt_sgnBdClsAt (j : ℕ) (Q : SymPoincare (A.czIter j).inv (N + 1)) :
    (F.closedLiftingPairAt j Q).sgnBdClsAt = 0 := by
  rw [LiftingPairAt.sgnBdClsAt, closedLiftingPairAt_bdClsAt, smul_zero]

end KaroubiFiltration

/-! ### The hypothesis for exactness at `L_n(A)`: (L2) for closed lifting pairs -/

namespace KaroubiFiltration

variable {A : InvCat} (F : KaroubiFiltration A)

/-- **(L2) for lifting pairs with empty boundary (`Y = 0`)**, isolated for module 17: if a closed
`N`-complex `D` over `C_ℤ^{∘k}(A/U)` (`N ≥ 0`) bounds over `Kar(C_ℤ^{∘k}(A/U))`, then every
closed complex `W` over `C_ℤ^{∘(k+1)}(A)` whose image in `C_ℤ^{∘(k+1)}(A/U)` is homotopy
isometric to the transition image `D ⊗ ℝ` (i.e. `W`, as the pair `W.closedPair` with zero
boundary, is a lifting pair at level `k + 1` of `D ⊗ ℝ`) is, in the colimit `Lmodel A n`
(`N + 1 = n + (k + 1)`, i.e. after finitely many further transitions), the image of a class over
`U`.  (The relative lifting of the null-cobordism of `D ⊗ ℝ` rel `W` is a triad over `A` whose
third face is a closed complex `Z` over `U` and whose top is a cobordism `W ∼ incl Z`.) -/
def LiftingClosedSub : Prop :=
  ∀ (k : ℕ) {N : ℤ} (D : SymPoincare (F.quot.czIter k).inv N), 0 ≤ N → NullCobordant D →
    ∀ W : SymPoincare (A.czIter (k + 1)).inv (N + 1),
      SymPoincare.Isometric (W.map (CZ.mapIter (k + 1) F.proj))
        ((CZ.lineData (F.quot.czIter k)).sym D) →
      ∀ (n : ℤ) (h : N + 1 = n + ((k + 1 : ℕ) : ℤ)),
        Lmodel.ofDeg A n (k + 1) h (Lconc.cls W) ∈ Set.range (Lmodel.map F.incl n)

end KaroubiFiltration

/-- (L2) with `Y = 0` for every Karoubi filtration. -/
def LiftingClosedSubAll : Prop :=
  ∀ (A : InvCat) (F : KaroubiFiltration A), F.LiftingClosedSub

namespace Lmodel

variable {A : InvCat} {F : KaroubiFiltration A} (hF : F.LiftingPairNull)
include hF

/-- **`∂` via a lifting pair at the same level** (H2 at level `j`): for a closed `(N+1)`-complex
`D` over `C_ℤ^{∘j}(A/U)` and any lifting pair `P` at level `j` of `D` itself,
`∂ [D] = σ_j [∂P]` (via `P.lineNeg` at level `j + 1`, `lineNeg_sgnBdClsAt`). -/
theorem bdry_ofDeg_liftingPairAt {n : ℤ} {j : ℕ} {N : ℤ} (hNj : N = n + j)
    (D : SymPoincare (F.quot.czIter j).inv (N + 1)) (P : F.LiftingPairAt j D) :
    bdry F hF n (ofDeg F.quot (n + 1) j (by rw [hNj]; ring) (Lconc.cls D)) =
      ofDeg F.sub n j hNj P.sgnBdClsAt := by
  by_cases hN : 0 ≤ N + 1
  · rw [bdry_ofDeg_cls hF hNj D hN P.lineNeg, KaroubiFiltration.LiftingPairAt.lineNeg_sgnBdClsAt,
      ofDeg_tensorLine]
  · rw [Lconc.cls_eq_zero_of_neg (by omega) D, map_zero, map_zero,
      Lconc.eq_zero_of_neg (by omega) P.sgnBdClsAt, map_zero]

omit hF

/-! #### The composites vanish -/

variable (F) in
/-- `proj ∘ incl = 0`: complexes of `U` vanish in `A/U` (levelwise, via the strict isos
`C_ℤ^{∘k}(U) ≅ (C_ℤ^{∘k} F).sub` and `(C_ℤ^{∘k} F).quot ≅ C_ℤ^{∘k}(A/U)`). -/
theorem map_proj_map_incl (n : ℤ) (y : Lmodel F.sub n) : map F.proj n (map F.incl n y) = 0 := by
  obtain ⟨k, x, rfl⟩ := exists_of y
  have h0 : (Lconc.map ((F.czIter k).incl ≫ (F.czIter k).proj) :
      Lconc (F.czIter k).sub (deg n k) →+ _) = 0 :=
    Lconc.map_eq_zero_of_isZero fun X ↦ (F.czIter k).isZero_proj_obj X.2
  have key : Lconc.map (CZ.mapIter k F.proj) (Lconc.map (CZ.mapIter k F.incl) x) = 0 := by
    rw [← AddMonoidHom.comp_apply, ← Lconc.map_comp, F.mapIter_incl_eq,
      ← F.proj_comp_czIterQuotIso_hom,
      show ((F.czIterSubIso k).inv ≫ (F.czIter k).incl) ≫ (F.czIter k).proj ≫
        (F.czIterQuotIso k).hom = (F.czIterSubIso k).inv ≫
          ((F.czIter k).incl ≫ (F.czIter k).proj) ≫ (F.czIterQuotIso k).hom by simp only [assoc],
      Lconc.map_comp, Lconc.map_comp, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, h0,
      AddMonoidHom.zero_apply, map_zero]
  rw [map_of, map_of, key, map_zero]

include hF in
/-- `∂ ∘ proj = 0`: a closed complex over `A` is a lifting pair of its image with zero
boundary (`closedLiftingPairAt`). -/
theorem bdry_map_proj (n : ℤ) (y : Lmodel A (n + 1)) : bdry F hF n (map F.proj (n + 1) y) = 0 := by
  obtain ⟨k, x, rfl⟩ := exists_ofDeg y
  have e : n + 1 + (k : ℤ) = n + k + 1 := by ring
  obtain ⟨Q, hQ⟩ := Lconc.cls_surjective (Lconc.castDeg e x)
  have hx : ofDeg A (n + 1) k rfl x = ofDeg A (n + 1) k (by ring) (Lconc.cls Q) := by
    rw [hQ, ofDeg_castDeg]
  rw [hx, map_ofDeg, Lconc.map_cls,
    bdry_ofDeg_liftingPairAt hF rfl _ (F.closedLiftingPairAt k Q),
    KaroubiFiltration.closedLiftingPairAt_sgnBdClsAt, map_zero]

include hF in
/-- `incl ∘ ∂ = 0`: the boundary `Y` of a lifting pair `(Y ⟶ W)` bounds `W` over `A`. -/
theorem map_incl_bdry (n : ℤ) (y : Lmodel F.quot (n + 1)) :
    map F.incl n (bdry F hF n y) = 0 := by
  obtain ⟨k, x, rfl⟩ := exists_ofDeg y
  have e : n + 1 + (k : ℤ) = n + k + 1 := by ring
  obtain ⟨D, hD⟩ := Lconc.cls_surjective (Lconc.castDeg e x)
  have hx : ofDeg F.quot (n + 1) k rfl x = ofDeg F.quot (n + 1) k (by ring) (Lconc.cls D) := by
    rw [hD, ofDeg_castDeg]
  rw [hx]
  by_cases hN : 0 ≤ n + k + 1
  · obtain ⟨P⟩ := F.nonempty_liftingPairAt_succ k D hN
    rw [bdry_ofDeg_cls hF rfl D hN P, map_ofDeg, P.map_incl_sgnBdClsAt, map_zero]
  · rw [Lconc.cls_eq_zero_of_neg (by omega) D, map_zero, map_zero, map_zero]

/-! #### Exactness at `L_n(U)` -/

include hF in
/-- **H1 exactness at `L_n(U)`** (`exact_U`): if `incl_*[Q] = 0`, then after transitions
`incl(Q)` bounds a pair `W` over `A`, which is a lifting pair of `W.toQuot` with boundary `Q`,
so `[Q] = ±∂[W.toQuot]` (`bdry_ofDeg_liftingPairAt`). -/
theorem exact_U (n : ℤ) : Function.Exact (bdry F hF n) (map F.incl n) := by
  intro y
  refine ⟨fun hy ↦ ?_, ?_⟩
  · obtain ⟨k, x, rfl⟩ := exists_of y
    rw [map_of, of_eq_zero_iff] at hy
    obtain ⟨l, hkl, hl⟩ := hy
    rw [← map_mapIter_transit] at hl
    rw [← of_transit hkl x]
    obtain ⟨Q, hQ⟩ := Lconc.cls_surjective (transit F.sub n hkl x)
    rw [← hQ] at hl ⊢
    rw [Lconc.map_cls, Lconc.cls_eq_zero_iff] at hl
    let Q' : SymPoincare (F.czIter l).sub.inv (deg n l) := Q.map (F.czIterSubIso l).inv
    have hQ' : Q'.map (F.czIter l).incl = Q.map (CZ.mapIter l F.incl) := by
      change Q.map ((F.czIterSubIso l).inv ≫ (F.czIter l).incl) = _
      rw [F.mapIter_incl_eq]
    rw [← hQ'] at hl
    obtain ⟨T⟩ := nullCobordant_iff_nonempty_pairOn.1 hl
    let X : SymPair (A.czIter l).inv (deg n l) := T.toPair
    have mem : ∀ r, (F.czIter l).U (X.bd.C.X r) := fun r ↦ (Q'.C.X r).2
    let D := (X.toQuot (F.czIter l) mem).map (F.czIterQuotIso l).hom
    let P : F.LiftingPairAt l D :=
      (X.liftingPair (F.czIter l) mem).ofIsometry (.ofEq' (SymPoincare.map_hom_inv _ _).symm)
    have hP : P.bdClsAt = Lconc.cls Q := by
      change Lconc.map (F.czIterSubIso l).hom (Lconc.cls Q') = _
      rw [Lconc.map_cls, SymPoincare.map_inv_hom]
    have hb := bdry_ofDeg_liftingPairAt hF (deg_eq n l) D P
    rw [KaroubiFiltration.LiftingPairAt.sgnBdClsAt, hP, Units.smul_def, map_zsmul,
      ← Units.smul_def] at hb
    refine ⟨((l : ℤ).negOnePow) • ofDeg F.quot (n + 1) l (by rw [deg_eq]; ring) (Lconc.cls D),
      ?_⟩
    rw [Units.smul_def, map_zsmul, ← Units.smul_def, hb, smul_smul, Int.units_mul_self, one_smul,
      of_eq_ofDeg]
  · rintro ⟨z, rfl⟩
    exact map_incl_bdry hF n z

/-! #### Exactness at `L_{n+1}(A/U)` -/

variable (F) in
/-- The class in `Lmodel (A/U) (n + 1)` of a closed complex `D` over `C_ℤ^{∘j}(A/U)` written in
the boundary degree `deg n j + 1`. -/
abbrev repQ (n : ℤ) (j : ℕ) (D : SymPoincare (F.quot.czIter j).inv (deg n j + 1)) :
    Lmodel F.quot (n + 1) :=
  of F.quot (n + 1) j (Lconc.castDeg (deg_add n 1 j).symm (Lconc.cls D))

lemma repQ_sym (n : ℤ) (j : ℕ) (D : SymPoincare (F.quot.czIter j).inv (deg n j + 1)) :
    repQ F n (j + 1) ((CZ.lineData (F.quot.czIter j)).sym D) = repQ F n j D := by
  rw [repQ, repQ, ← Lconc.tensorLine_cls, ← of_tensorLine j, Lconc.tensorLine_castDeg]
  rfl

/-- **Iterating `lineNeg`**: a lifting pair `P₀` at level `k` of `D` gives, at every level
`j ≥ k`, a lifting pair of a representative of `[D]` whose boundary class is `±` the transition
image of that of `P₀`. -/
lemma exists_liftingPairAt_transit {n : ℤ} {k : ℕ}
    (D : SymPoincare (F.quot.czIter k).inv (deg n k + 1)) (P₀ : F.LiftingPairAt k D) :
    ∀ j (hj : k ≤ j), ∃ (D' : SymPoincare (F.quot.czIter j).inv (deg n j + 1))
      (P' : F.LiftingPairAt j D') (u : ℤˣ),
      repQ F n j D' = repQ F n k D ∧ P'.bdClsAt = u • transit F.sub n hj P₀.bdClsAt := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => exact ⟨D, P₀, 1, rfl, by rw [transit_self, one_smul]; rfl⟩
  | succ j hkj ih =>
    obtain ⟨D', P', u, hrep, hP'⟩ := ih
    refine ⟨(CZ.lineData (F.quot.czIter j)).sym D', P'.lineNeg, -u, ?_, ?_⟩
    · rw [repQ_sym, hrep]
    · rw [KaroubiFiltration.LiftingPairAt.lineNeg_bdClsAt, hP', transit_succ hkj, Units.smul_def,
        Units.smul_def, map_zsmul, Units.val_neg, neg_smul]

/-- **Gluing a null-cobordism of the boundary** (the core of `exact_Q`): if the boundary class
of a lifting pair `(Y ⟶ W)` at level `j` of `D` vanishes, then `Y` bounds a pair `Z` over `U`,
and `D` is isometric to the image of the closed union `W ∪_Y -Z` over `A`
(`SymPair.isometric_toQuot_union`). -/
lemma exists_cls_eq_map_proj {j : ℕ} {N : ℤ} {D : SymPoincare (F.quot.czIter j).inv (N + 1)}
    (P : F.LiftingPairAt j D) (h : P.bdClsAt = 0) :
    ∃ E : SymPoincare (A.czIter j).inv (N + 1),
      Lconc.cls D = Lconc.cls (E.map (CZ.mapIter j F.proj)) := by
  have h1 : Lconc.cls (P.bd.map (F.czIterSubIso j).hom) = 0 := by
    rw [← Lconc.map_cls]; exact h
  have h2 : NullCobordant P.bd := by
    have := (Lconc.cls_eq_zero_iff.1 h1).map (F.czIterSubIso j).inv
    rwa [SymPoincare.map_hom_inv] at this
  obtain ⟨T₀⟩ := nullCobordant_iff_nonempty_pairOn.1 h2
  let Z : PairOn P.X.bd.neg := ((PairData.ofPairOn T₀).map (F.czIter j).incl).neg.toPairOn
    (PairData.neg_isPoincare (PairData.map_isPoincare _ (PairData.isPoincare_ofPairOn T₀)))
  have hZ : ∀ r, (F.czIter j).U (Z.D.X r) := fun r ↦ (T₀.D.X r).2
  refine ⟨P.X.toPairOn.union Z, ?_⟩
  obtain ⟨e⟩ := SymPair.isometric_toQuot_union (F.czIter j) P.X P.mem Z hZ
  have h3 := Lconc.cls_eq_of_isometry ((e.symm.trans P.iso).map (F.czIterQuotIso j).hom)
  rw [SymPoincare.map_inv_hom] at h3
  rw [← h3]
  congr 1
  change (P.X.toPairOn.union Z).map ((F.czIter j).proj ≫ (F.czIterQuotIso j).hom) = _
  rw [F.proj_comp_czIterQuotIso_hom]

include hF in
/-- **H1 exactness at `L_{n+1}(A/U)`** (`exact_Q`): if `∂[D] = 0`, the boundary `Y` of a lifting
pair `(Y ⟶ W)` of a representative of `[D]` bounds `Z` over `U` at some level, and the closed union
`W ∪_Y -Z` over `A` maps to `[D]`. -/
theorem exact_Q (n : ℤ) : Function.Exact (map F.proj (n + 1)) (bdry F hF n) := by
  intro y
  refine ⟨fun hy ↦ ?_, ?_⟩
  · obtain ⟨k, x, rfl⟩ := exists_of y
    obtain ⟨D, hD⟩ := Lconc.cls_surjective (Lconc.castDeg (deg_add n 1 k) x)
    have hx : of F.quot (n + 1) k x = repQ F n k D := by
      rw [repQ, hD, Lconc.castDeg_castDeg]; rfl
    rw [hx] at hy ⊢
    by_cases hN : 0 ≤ deg n k + 1
    · obtain ⟨P₀⟩ := F.nonempty_liftingPairAt_succ k D hN
      have hy' : of F.sub n (k + 1) P₀.bdClsAt = 0 := by
        rw [repQ, bdry_of, Lconc.castDeg_castDeg, Lconc.castDeg_self,
          KaroubiFiltration.bdLevel_cls, F.bdVal_eq hF hN P₀,
          KaroubiFiltration.LiftingPairAt.sgnBdClsAt, Units.smul_def, map_zsmul] at hy
        rcases Int.units_eq_one_or ((k + 1 : ℕ) : ℤ).negOnePow with h | h <;>
          rw [h] at hy <;> simpa using hy
      obtain ⟨l, hl, hl0⟩ := (of_eq_zero_iff _).1 hy'
      obtain ⟨D', P', u, hrep, hP'⟩ := exists_liftingPairAt_transit (F := F) (n := n) (k := k + 1)
        ((CZ.lineData (F.quot.czIter k)).sym D) P₀ l hl
      have hP0 : P'.bdClsAt = 0 :=
        hP'.trans ((congrArg (fun z ↦ u • z) hl0).trans (smul_zero u))
      obtain ⟨E, hE⟩ := exists_cls_eq_map_proj P' hP0
      refine ⟨of A (n + 1) l (Lconc.castDeg (deg_add n 1 l).symm (Lconc.cls E)), ?_⟩
      rw [← repQ_sym, ← hrep, repQ, map_of, Lconc.map_castDeg, Lconc.map_cls, hE]
    · refine ⟨0, ?_⟩
      rw [map_zero, repQ, Lconc.cls_eq_zero_of_neg (by omega) D, map_zero, map_zero]
  · rintro ⟨z, rfl⟩
    exact bdry_map_proj hF n z

/-! #### Exactness at `L_n(A)` -/

/-- **H1 exactness at `L_n(A)`** (`exact_A`), given (L2) for closed lifting pairs
(`LiftingClosedSub`): if `proj_*[P] = 0`, then after transitions `proj(P)` bounds, and `P ⊗ ℝ` is
a closed lifting pair of `proj(P) ⊗ ℝ`. -/
theorem exact_A (hA : F.LiftingClosedSub) (n : ℤ) :
    Function.Exact (map F.incl n) (map F.proj n) := by
  intro y
  refine ⟨fun hy ↦ ?_, ?_⟩
  · obtain ⟨k, x, rfl⟩ := exists_of y
    rw [map_of, of_eq_zero_iff] at hy
    obtain ⟨l, hkl, hl⟩ := hy
    rw [← map_mapIter_transit] at hl
    rw [← of_transit hkl x]
    obtain ⟨P, hP⟩ := Lconc.cls_surjective (transit A n hkl x)
    rw [← hP] at hl ⊢
    rw [Lconc.map_cls, Lconc.cls_eq_zero_iff] at hl
    by_cases hN : 0 ≤ deg n l
    · have hW := (CZ.lineHom (CZ.mapIter l F.proj)).symMapIsometry P
      have h := hA l (P.map (CZ.mapIter l F.proj)) hN hl ((CZ.lineData (A.czIter l)).sym P)
        ⟨hW.symm⟩ n (by rw [deg_eq]; push_cast; ring)
      rwa [← Lconc.tensorLine_cls, ofDeg_tensorLine l (deg_eq n l), ← of_eq_ofDeg] at h
    · rw [Lconc.cls_eq_zero_of_neg (by omega) P, map_zero]
      exact ⟨0, map_zero _⟩
  · rintro ⟨z, rfl⟩
    exact map_proj_map_incl F n z

end Lmodel

/-! ### An equivalent form of the hypothesis -/

namespace KaroubiFiltration

variable {A : InvCat} (F : KaroubiFiltration A)

/-- `LiftingClosedSub` in its plain form: a closed complex over `C_ℤ^{∘k}(A)` (dimension `≥ 0`)
whose image over `C_ℤ^{∘k}(A/U)` is null-cobordant comes from `U` in the colimit. -/
def LiftingClosedSub' : Prop :=
  ∀ (k : ℕ) {N : ℤ} (P : SymPoincare (A.czIter k).inv N), 0 ≤ N →
    NullCobordant (P.map (CZ.mapIter k F.proj)) →
    ∀ (n : ℤ) (h : N = n + (k : ℤ)),
      Lmodel.ofDeg A n k h (Lconc.cls P) ∈ Set.range (Lmodel.map F.incl n)

/-- **The two forms of the hypothesis for `exact_A` are equivalent** (`(P ⊗ ℝ)/U ≃ (P/U) ⊗ ℝ`,
`symMapIsometry`, and null-cobordisms survive `⊗ ℝ` and isometries). -/
theorem liftingClosedSub_iff : F.LiftingClosedSub ↔ F.LiftingClosedSub' := by
  constructor
  · intro hA k N P hN hP n h
    have hW := (CZ.lineHom (CZ.mapIter k F.proj)).symMapIsometry P
    have h' := hA k (P.map (CZ.mapIter k F.proj)) hN hP ((CZ.lineData (A.czIter k)).sym P)
      ⟨hW.symm⟩ n (by rw [h]; push_cast; ring)
    rwa [← Lconc.tensorLine_cls, Lmodel.ofDeg_tensorLine k h] at h'
  · intro hA k N D hN hD W ⟨e⟩ n h
    exact hA (k + 1) W (by omega)
      ((LineData.NullCobordant.sym (CZ.lineData (F.quot.czIter k)) hD).of_isometry e.symm) n h

end KaroubiFiltration

/-! ### The interface fields for the model -/

namespace Lmodel

variable {A : InvCat}

/-- The interface field `exact_A` of the model (H1), given (L2) for closed lifting pairs. -/
theorem exactAll_A (hA : LiftingClosedSubAll) (F : KaroubiFiltration A) (n : ℤ) :
    Function.Exact (map F.incl n) (map F.proj n) :=
  exact_A (hA A F) n

/-- The interface field `exact_Q` of the model (H1), given (L2). -/
theorem exactAll_Q (hL : LiftingPairNullAll) (F : KaroubiFiltration A) (n : ℤ) :
    Function.Exact (map F.proj (n + 1)) (bdryAll hL F n) :=
  exact_Q (hL A F) n

/-- The interface field `exact_U` of the model (H1), given (L2). -/
theorem exactAll_U (hL : LiftingPairNullAll) (F : KaroubiFiltration A) (n : ℤ) :
    Function.Exact (bdryAll hL F n) (map F.incl n) :=
  exact_U (hL A F) n

end Lmodel

end

end HSFormal.LTheory
