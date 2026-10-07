import HSFormal.LTheory.Model.CutBoundary

/-!
# The complement of the lower cut pair: chain level (lower L-theory model, module 22, part 5)

For an honest free `(N+1)`-dimensional Poincaré complex `P = (C, 1, φ)` over `C_ℤ(A)` and cut
data `D`, the lower cut pair is Ranicki's boundary pair `(j⁻ : ∂T ⟶ T^{N+1-*})` of the lower
Thom complex `T = C/S`, where `S = C|_{[t_*, ∞)}` is the upper subcomplex
(`CutData.subC`, all chain objects in the positive half-line).  This file constructs and checks
the chain-level data of the *complementary* pair over the positive half-line, with the **same**
boundary `∂T = Σ⁻¹Cone(θ)`:

* `CutData.jPlus : ∂T ⟶ S`, `(α, c) ↦ ι_E φ π_U α + ι_E d π_U c` (on
  `∂T_r = T^{N+1-r} ⊕ T_{r+1}`), **a chain map** (`jPlus`, checked against the cone conventions
  of `BoundaryConstruction`: `d(α, c) = (δα, -θα - dc)`).  The two identities behind it are
  `A d_S = δ A - θ x` (`compA_d`) and `x d_S = -d_T x` (`cross_d`) for `A = ι_E φ π_U` and the
  crossing `x = ι_E d π_U` (the extension class of `0 ⟶ S ⟶ C ⟶ T ⟶ 0`).
* `CutData.glueHomotopy`: `j⁺ ι_S ≃ j⁻ q^* φ` as chain maps `∂T ⟶ C`, by the homotopy
  `(α, c) ↦ ι_E c`.  This is the datum making `Cone((j⁺, j⁻) : ∂T ⟶ S ⊕ T^{N+1-*}) ⟶ C` a chain
  map, i.e. the comparison `X⁺ ∪_{∂T} X⁻ ⟶ P` of the union (`PairOn.union`) with `P`.

## Remaining steps for `DecBij` (module 22)

Notation: `A = C^{∘k} B`, `N = n + k ≥ 0`, `P = (C, 1, φ)` free `(N+1)`-dimensional Poincaré over
`C_ℤ(A)` (by `Wall` under `NegK`; for `N = 0` only up to class, with the hyperbolic correction),
`D = CutData` with the `Sec` data of `CZ.exists_lowerPair`, `X⁻ = lowerPair S hp hN : SymPair N`
(boundary `∂ = ` the truncation of `(∂T, 1, ∂θ)` along `e = truncEquiv S hp hN`, interior
`T^{N+1-*}`), `Q` the window model of `∂` (`exists_lowerPair_window`), `L = tensorLine`.

**(a) Without `LineComplex` / `Triads`** (only `Transport`, `GlueKar`, `Glue`, `Union`, `Swindle`):
1. *Relative structure of the complement.* `δφ⁺ : Homotopy (dualHom (j⁺) ≫ (-∂θ) ≫ j⁺) 0` with
   `relTop δφ⁺ = ± ι_U^* φ π_U` (the restriction of `φ` to `S`; `π_U^* = ι_U` by self-duality of
   the cut, cf. `star_cut_πE`), symmetric because `Tφ = φ`; the cycle identity
   `δφ_r d = δ δφ_{r-1} + j φ j^*` (`SymPair.top_comm`) is proved like `compA_d` from
   `φ d = δ φ` and `π_U ι_U = 1 - π_E ι_E` (`πU_ιU`).  The boundary structure is `-∂θ`
   because `PairOn.union X Y` takes `X : PairOn B`, `Y : PairOn B.neg`; we glue
   `X⁻.toPairOn.union X⁺` with `X⁺ : PairOn X⁻.bd.neg`.
2. *Same truncated boundary.* Package `(j⁺, δφ⁺)` as a `RawPair` on `(∂T, 1, -∂θ)` and apply
   `RawPair.transportBd` along the **same** `e`; its `bd` must be *equal* to `X⁻.bd.neg`
   (`SymPoincare` ext + `Preadditive.comp_neg`), since `PairOn` fixes the boundary on the nose.
   Support of `S` in `[0, N+1]` holds because `P.p = 1`.
3. *Comparison `X⁻ ∪ X⁺ ≃ P`.* `homotopyCofiber.desc` of `α = (q^* φ, -ι_S) : T^{N+1-*} ⊞ S ⟶ C`
   along `Glue.u = (j⁻, j⁺)`, with null-homotopy of `u ≫ α` given by `glueHomotopy` (composed
   with `e`).  It is a homotopy equivalence by `homotopyEquivMiddle`/`isKarEquiv_middle` on the
   ladder `S ⟶ X⁻ ∪ X⁺ ⟶ Cone(j⁻)` over `S ⟶ C ⟶ T` (outer maps `𝟙_S` and the equivalence
   `Cone(j⁻) ≃ T` of `BoundaryConstruction.coneπ`; the right square must be made to commute
   strictly, e.g. by adding the boundary term `-φ e` of `coneπ` to `α`), and an isometry for
   the symmetrized union structure `δφZ` of `Glue` (`relDualityδφZHomotopy`).
4. *Poincaré-ness of `X⁺`.* The relative duality `Ψ⁺ : Cone(j⁺)^{N+1-*} ⟶ S` is the **outer**
   map of a ladder whose middle (`φ`, via 3) and other outer map (`Ψ⁻ = ±(pι)^*`,
   `relDuality_bdRel`) are Kar equivalences.  The repo only has the *middle* two-out-of-three
   (`GlueKar`); the outer version needs "a degreewise split sequence with contractible middle and
   quotient has contractible kernel" (a variant of `DegreewiseSplit.contractionMiddle`).
5. *Half-line placement.* `X⁻` has all objects in `negHalf` (`lowerPair_D_negHalf`,
   `lowerPair_bd_negHalf`) and `S` in `posHalf` (`subC_posHalf`), but the boundary objects of
   both pairs are those of `∂T` (negative half-line only).  Transport both pairs once more
   along the boundary Kar equivalence `(∂, p') ≃ Q.map incl` (`HomotopyIsometry.toKarHtpyEquiv`
   of `exists_lowerPair_window`; `SymPair.transportBd` allows a different target complex).
   Then every chain object of `X⁺`, resp. `X⁻`, and of the unions in step 7 lies in `posHalf`,
   resp. `negHalf` (window objects are in both), so the unions are `SymPoincare.lift` (`Union`)
   of complexes over `A.czPos`/`A.czNeg` mapped by `subIncl`, and their classes vanish by
   `czPos_eq_zero`/`czNeg_eq_zero` (`Swindle`) and naturality of `Lconc.cls`.

**(b) Needing `Triads` (gluing cobordisms):**
6. *Relation (R)*: for pairs `Y, Y'` on `B` and `Z, Z'` on `B.neg` (`PairOn`),
   `[Y ∪ Z] - [Y' ∪ Z] = [Y ∪ Y'.neg]` and `[Y ∪ Z] - [Y ∪ Z'] = [Z'.neg ∪ Z]` in `Lconc`
   (`(Y ∪ Z) ⊔ -(Y' ∪ Z)` and `Y ∪ Y'.neg` are cobordant through the union with the cylinder
   on `Z`; this needs gluing of triads along a face, recorded in the blueprint §6 as not
   formalized).
7. *Surjectivity of `L`*: with `L⁻, L⁺` the two cut pairs of `L Q` (step 9; boundary `∂_Q`,
   identified with `∂` through `Q` by step 5; `Q` replaced by `-Q` if step 9 gives the sign `-1`),
   `[P] - [L Q] = [X⁻ ∪ X⁺] - [L⁻ ∪ L⁺] = [X⁻ ∪ L⁻.neg] + [L⁺.neg ∪ X⁺]`; the first union lies
   over `negHalf`, the second over `posHalf` (after step 5), so both vanish by
   `czNeg_eq_zero`/`czPos_eq_zero` (`Swindle`).
8. *Injectivity of `L`*: if `L Q` bounds a free `W` over `C_ℤ(A)` (`Wall`), cut `W` relative to
   its boundary: relative Thom complex and relative boundary construction
   (`BoundaryConstructionRel`, a triad), whose window face is a null-cobordism of the cut of
   `L Q`, i.e. of `±Q`.

**(c) Needing `LineComplex`:**
9. *Cut of a line complex*: for a Kar `Q` over `A` (the window model is only Kar), `L Q` is
   Kar; replace it by its free model `L.freeSym Q` (`FreeLine`, `freeSymIsometry`; identity
   idempotent, propagation `1`), cut it at thresholds `t_r = 0`, and show that the boundary of
   its lower Thom complex is homotopy isometric to `Q` placed at `0` up to the sign
   `(-1)^N · s`: `(-1)^N` is the boundary-pair sign (as in `LiftingPair.bdPair_isometric(_neg)`)
   and `s` the sign of `φ_ℝ` (`bsign`).  This is where the projective class of `Q` reappears
   (the e-trick `Δp s - 1` of `freeCx` cut at `0` has boundary `(Q, p)`).  The two cut pairs of
   `L.freeSym Q` are the `L⁻, L⁺` of step 7 (no reflection is used, so they share `∂`).
10. *`dec_bij`*: steps 7–9 give that each transition `Lconc (C^{∘k}B) (n+k) ⟶
    Lconc (C^{∘k+1}B) (n+k+1)` is bijective for `n ≥ 0`, hence `cls` is bijective.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression
  homotopyCofiber

noncomputable section

namespace CZ

namespace CutData

variable {A : InvCat} {N : ℤ} {P : SymPoincare A.cz.inv (N + 1)} (D : CutData P)

/-- The upper subcomplex `S = C|_{[t_*, ∞)}`. -/
abbrev subC : ChainComplex A.cz ℤ := SplitCx.sub D.isSubU

/-- The inclusion `S ⟶ C`. -/
abbrev inclS : D.subC ⟶ P.C := SplitCx.fromSub D.isSubU

/-- The crossing `x = ι_E d π_U : T_r ⟶ S_{r'}`. -/
abbrev cross (r r' : ℤ) : D.thomC.X r ⟶ D.subC.X r' := SplitCx.cross (C := P.C) (σ := D.σ) r r'

/-- All chain objects of the upper subcomplex lie in the positive half-line. -/
lemma subC_posHalf (r : ℤ) : posHalf A (D.subC.X r) :=
  ⟨D.t r, fun _ hv ↦ isZero_cut_U (P.C.X r) (fun x ↦ x < D.t r) hv⟩

/-- The `α`-component `A_r = ι_E φ_r π_U : T^{N+1-r} ⟶ S_r` of `j⁺`. -/
def compA (r : ℤ) : (dualComplex A.cz.inv (N + 1) D.thomC).X r ⟶ D.subC.X r :=
  (D.σ (N + 1 - r)).ιE ≫ P.φ.f r ≫ (D.σ r).πU

lemma πU_ιU (r : ℤ) : (D.σ r).πU ≫ (D.σ r).ιU = 𝟙 _ - (D.σ r).πE ≫ (D.σ r).ιE := by
  rw [← (D.σ r).total]; abel

/-- `x d_S = -d_T x`. -/
lemma cross_d (r r' r'' : ℤ) :
    D.cross r r' ≫ D.subC.d r' r'' = -(D.thomC.d r r' ≫ D.cross r' r'') := by
  simp only [cross, SplitCx.cross, SplitCx.sub_d, SplitCx.quot_d, assoc]
  rw [← assoc (D.σ r').πU, πU_ιU, sub_comp, id_comp, comp_sub, comp_sub, P.C.d_comp_d_assoc,
    zero_comp, comp_zero, zero_sub]
  simp only [assoc]

/-- `A d_S = δ A - θ x`. -/
lemma compA_d (r : ℤ) :
    D.compA (r + 1) ≫ D.subC.d (r + 1) r =
      (dualComplex A.cz.inv (N + 1) D.thomC).d (r + 1) r ≫ D.compA r -
        D.θ.f (r + 1) ≫ D.cross (r + 1) r := by
  have hq : (dualComplex A.cz.inv (N + 1) D.thomC).d (r + 1) r ≫ (D.σ (N + 1 - r)).ιE =
      (D.σ (N + 1 - (r + 1))).ιE ≫ (dualComplex A.cz.inv (N + 1) P.C).d (r + 1) r := by
    have := (dualHom A.cz.inv (N + 1) D.q).comm (r + 1) r
    simp only [dualHom_f, SplitCx.toQuot_f] at this
    erw [star_cut_πE, star_cut_πE] at this
    exact this.symm
  have hφ := P.φ.comm (r + 1) r
  simp only [compA, cross, SplitCx.cross, SplitCx.sub_d, θ, comp_f, dualHom_f,
    SplitCx.toQuot_f, assoc]
  erw [star_cut_πE]
  rw [← assoc (D.σ (r + 1)).πU, πU_ιU, sub_comp, id_comp, comp_sub, comp_sub,
    reassoc_of% hq, ← reassoc_of% hφ]
  simp only [assoc]

/-- The components of `j⁺` on `∂T_r = T^{N+1-r} ⊕ T_{r+1}`. -/
def jPlusF (r : ℤ) : D.thom.bdC.X r ⟶ D.subC.X r :=
  fstX D.thom.φ (r + 1) r (by simp) ≫ D.compA r + sndX D.thom.φ (r + 1) ≫ D.cross (r + 1) r

/-- **The complement boundary map** `j⁺ : ∂T ⟶ S`, `(α, c) ↦ ι_E φ π_U α + ι_E d π_U c`, a chain
map. -/
def jPlus : D.thom.bdC ⟶ D.subC where
  f := D.jPlusF
  comm' r r' h := by
    obtain rfl : r = r' + 1 := by simp only [ComplexShape.down_Rel] at h; omega
    apply ext_from_X D.thom.φ (r' + 1) (r' + 1 + 1) (by simp)
    · change inlX D.thom.φ (r' + 1) (r' + 1 + 1) _ ≫ D.jPlusF (r' + 1) ≫ D.subC.d (r' + 1) r' =
        inlX D.thom.φ (r' + 1) (r' + 1 + 1) _ ≫ (-(cone D.thom.φ).d (r' + 1 + 1) (r' + 1)) ≫
          D.jPlusF r'
      rw [Preadditive.neg_comp, Preadditive.comp_neg, homotopyCofiber_d,
        inlX_d_assoc D.thom.φ (r' + 1 + 1) (r' + 1) r' (by simp) (by simp)]
      simp only [jPlusF, comp_add, add_comp, assoc, inlX_fstX_assoc, inlX_sndX_assoc,
        inrX_fstX_assoc, inrX_sndX_assoc, zero_comp, add_zero, comp_zero,
        Preadditive.neg_comp, neg_add_rev, neg_neg]
      rw [D.compA_d]
      change _ = -(D.θ.f (r' + 1) ≫ D.cross (r' + 1) r') +
        (dualComplex A.cz.inv (N + 1) D.thomC).d (r' + 1) r' ≫ D.compA r'
      abel
    · change inrX D.thom.φ (r' + 1 + 1) ≫ D.jPlusF (r' + 1) ≫ D.subC.d (r' + 1) r' =
        inrX D.thom.φ (r' + 1 + 1) ≫ (-(cone D.thom.φ).d (r' + 1 + 1) (r' + 1)) ≫ D.jPlusF r'
      rw [Preadditive.neg_comp, Preadditive.comp_neg, homotopyCofiber_d, inrX_d_assoc]
      simp only [jPlusF, comp_add, add_comp, assoc, inrX_fstX_assoc, inrX_sndX_assoc,
        zero_comp, zero_add]
      rw [D.cross_d]
      rfl

@[simp] lemma jPlus_f (r : ℤ) : D.jPlus.f r = D.jPlusF r := rfl

/-- The degree `+1` homotopy data `(α, c) ↦ ι_E c : ∂T_a ⟶ C_{a+1}`. -/
def glueHom (a b : ℤ) (hab : (ComplexShape.down ℤ).Rel b a) : D.thom.bdC.X a ⟶ P.C.X b :=
  sndX D.thom.φ (a + 1) ≫ (D.σ (a + 1)).ιE ≫
    (P.C.XIsoOfEq (by simp only [ComplexShape.down_Rel] at hab; omega : a + 1 = b)).hom

lemma glueHom_succ (a : ℤ) (h : (ComplexShape.down ℤ).Rel (a + 1) a) :
    D.glueHom a (a + 1) h = sndX D.thom.φ (a + 1) ≫ (D.σ (a + 1)).ιE := by
  simp [glueHom]

lemma d_glueHom_aux (i m : ℤ) (hm : m = i) :
    homotopyCofiber.d D.thom.φ (i + 1) m ≫ sndX D.thom.φ m ≫ (D.σ m).ιE ≫
      (P.C.XIsoOfEq hm).hom =
    homotopyCofiber.d D.thom.φ (i + 1) i ≫ sndX D.thom.φ i ≫ (D.σ i).ιE := by
  subst hm; simp

/-- **The gluing homotopy** `j⁺ ι_S ≃ j₀ q^* φ : ∂T ⟶ C` (`j₀ = coneFst`, the projection to
`T^{N+1-*}`), by `(α, c) ↦ ι_E c`.  It makes `Cone((j⁺, j₀))` map to `C`, the comparison of the
union `X⁺ ∪_{∂T} X⁻` with `P`. -/
def glueHomotopy :
    Homotopy (D.jPlus ≫ D.inclS) (coneFst D.thom.φ ≫ dualHom A.cz.inv (N + 1) D.q ≫ P.φ) :=
  homotopyCongr ((Homotopy.nullHomotopy' D.glueHom).add
    (Homotopy.refl (coneFst D.thom.φ ≫ dualHom A.cz.inv (N + 1) D.q ≫ P.φ))) (by
      ext i : 1
      rw [add_f_apply, Homotopy.nullHomotopicMap'_f (k₂ := i + 1) (k₁ := i) (k₀ := i - 1)
        (by simp) (by simp), glueHom_succ]
      have e₁ : D.thom.bdC.d i (i - 1) ≫ D.glueHom (i - 1) i (by simp) =
          -(homotopyCofiber.d D.thom.φ (i + 1) i ≫ sndX D.thom.φ i ≫ (D.σ i).ιE) := by
        rw [← D.d_glueHom_aux i (i - 1 + 1) (by omega)]
        simp [glueHom]
      rw [e₁]
      apply ext_from_X D.thom.φ i (i + 1) (by simp)
      · simp only [comp_f, jPlus_f, jPlusF, SplitCx.fromSub_f, comp_add, add_comp, assoc,
          inlX_fstX_assoc, inlX_sndX_assoc, zero_comp, add_zero, Preadditive.comp_neg]
        rw [inlX_d_assoc D.thom.φ (i + 1) i (i - 1) (by simp) (by simp)]
        simp only [Preadditive.neg_comp, add_comp, assoc, inlX_sndX_assoc, inrX_sndX_assoc,
          zero_comp, comp_zero, neg_zero, zero_add, coneFst_f, dualHom_f, SplitCx.toQuot_f,
          inlX_fstX_assoc]
        change -(D.θ.f i ≫ (D.σ i).ιE) + _ = _
        simp only [compA, θ, comp_f, dualHom_f, SplitCx.toQuot_f, assoc]
        erw [star_cut_πE]
        rw [D.πU_ιU, comp_sub, comp_sub, comp_id, neg_add_eq_sub]
      · simp only [comp_f, jPlus_f, jPlusF, SplitCx.fromSub_f, coneFst_f, comp_add, add_comp,
          assoc, Preadditive.comp_neg, inrX_fstX_assoc, inrX_sndX_assoc, zero_comp, add_zero,
          zero_add]
        rw [inrX_d_assoc]
        simp only [inrX_sndX_assoc, cross, SplitCx.cross, assoc]
        rw [D.πU_ιU, comp_sub, comp_sub, comp_id, neg_add_eq_sub]
        congr 1
        change ((D.σ (i + 1)).ιE ≫ P.C.d (i + 1) i ≫ (D.σ i).πE) ≫ (D.σ i).ιE = _
        simp only [assoc]) (zero_add _)

end CutData

end CZ

end

end HSFormal.LTheory
