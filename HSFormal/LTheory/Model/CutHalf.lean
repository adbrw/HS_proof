import HSFormal.LTheory.Model.CutUpper

/-!
# The two cut pairs with a common window boundary, and half-line vanishing
(lower L-theory model, module 22, part 7)

For an honest free `(N+1)`-dimensional Poincaré complex `P` over `C_ℤ(A)` (`N ≥ 0`):

* `CZ.exists_cutPairs`: there are `(N+1)`-dimensional Poincaré pairs `X⁻`, `X⁺` over `C_ℤ(A)`
  with **opposite boundaries** `∂X⁺ = -∂X⁻` (so `SymPair.union X⁻ X⁺` is defined), the interior
  of `X⁻` in the negative half-line, the interior of `X⁺` in the positive half-line, and the
  common boundary on **bounded** (window) objects, homotopy isometric to a complex over
  `C_ℤ^{bdd}(A)`.  They are the lower and upper cut pairs (`lowerPair`, `upperPair`) transported
  once more along the window equivalence of `exists_lowerPair_window` (`SymPair.transportBd`
  allows a different boundary complex): `lowerPairW`, `upperPairW`, `upperPairW_bd`.
* `CZ.cls_union_eq_zero_of_negHalf`/`_of_posHalf`: the union of two pairs all of whose chain
  objects (interiors and common boundary) lie in the negative (positive) half-line has class `0`
  in `Lconc (C_ℤ A) (N+1)`: it is the image of a complex over `C_{ℤ≤}(A)` (`SymPoincare.lift`),
  and `Lconc (C_{ℤ≤} A) = 0` by the Eilenberg swindle (`Lconc.czNeg_eq_zero`).  Window objects
  lie in both half-lines, so after the window transport the unions `X⁻ ∪ Z` with `Z` over the
  negative half-line (e.g. a reflected half of a line complex) vanish.

## Status of `DecBij` (module 22) after this file

Done (compiled): window category `≃ A` (`CutWindow`); threshold cuts, Thom complex Poincaré mod
bounded (`CutComplex`); truncation of raw boundaries (`CutTrunc`); lower pair with window
boundary (`CutBoundary`); complement chain map `j⁺` and gluing homotopy (`CutComplement`);
upper pair `X⁺` with relative structure `(-1)^N ι_U φ π_U`, Poincaré duality, boundary exactly
`-∂X⁻`, and `cutUnion = X⁻ ∪ X⁺` (`CutUpper`); window transports and half-line vanishing (this
file); outer two-out-of-three for Kar ladders (`KarTwoOutOfThree`).

Remaining, in order:
1. *`cutUnion ≃ ±P` (homotopy isometry).*  The comparison is `g = desc u α (e.g H)` on
   `Cone(u)`, `u = (j⁻, j⁺)` truncated by `c = truncIdem`, with `α = (φ q^*, -ι_S)` and `H` the
   gluing homotopy (`glueHomotopy`); it is a Kar equivalence by `isKarEquiv_middle` on the ladder
   `S ⟶ Cone(u) ⟶ Cone(j⁻)` over `S ⟶ C ⟶ T` (right map `coneπ ∘ coneMap c 1`).  For the
   structure, replace `δφZ` by `Hns` (`relTopDiffHomotopy`, as in `relDualityδφZHomotopy`) and
   push `relTop Hns = ι_W δφ⁻ ι_W^* + (K'^*(-φ_B)β' + c'^*φ_B K') + ι_Y δφ⁺ ι_Y^*` along `g`:
   `g ι_W = φ q^*`, `g ι_Y = -ι_S`, `g K' = c H`.  Before truncation the three terms give the
   `E⊗E`, mixed and `U⊗U` blocks of `φ` (the `U⊗U` block is `(-1)^N π_U ι_U φ π_U ι_U`, so the
   expected answer is `cutUnion ≃ (-1)^N P`); the truncation contributes the terms of
   `W : c^* ∂φ c ≃ ∂φ` (`RawPair.bdW`) in `δφ⁻ = j⁻ W j⁻^*`, `δφ⁺ + j⁺ W j⁺^*` and
   `φ_B = c^* ∂φ c`, which cancel up to the homotopy `W` conjugated by `H`, `j⁻`, `j⁺`.
   (Not done: the components of `W`, built from `cancelHomotopy` of the two `KarCancel` steps,
   make this a long but finite computation.)
2. *Relation (R)* `[Y ∪ Z] - [Y' ∪ Z] = [Y ∪ Y'.neg]` (needs gluing a triad along a face;
   `Triads` has `TriadOn`, faces, `cylinder`, `ofRel`, `RelCobordant`, but no gluing).
3. *Line cut* (needs `LineComplex`/`FreeLine`): cut `L.freeSym Q` at `t_r = r`; its lower
   boundary is homotopy isometric to `±(Q at 0)`; the sign is the boundary-pair sign `(-1)^N`
   (`LiftingPair.bdPair_isometric`) times the line signs (`s_N = +1` for `X ⊗ ℝ`, `t_N = -1` for
   its quotient, `LineNatural.pair_toQuot`); not computed.
4. With 1–3: surjectivity `[P] = ±[L Q]` via `[P] - [L Q] = [X⁻ ∪ L⁻.neg] + [L⁺.neg ∪ X⁺]` and
   `cls_union_eq_zero_of_negHalf/_of_posHalf`; injectivity by the relative cut of a free
   null-cobordism (`BoundaryConstructionRel` + triads); then `dec_bij`.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression
  homotopyCofiber

noncomputable section

namespace CZ

variable {A : InvCat} {N : ℤ}

/-! ### Objects of cones, sums and unions in an additive subcategory -/

section Objects

variable (U : ObjectProperty A.cz) [IsAdditiveSub U]

lemma cone_X_mem {K L : ChainComplex A.cz ℤ} (f : K ⟶ L) (hK : ∀ r, U (K.X r))
    (hL : ∀ r, U (L.X r)) (r : ℤ) : U ((cone f).X r) :=
  U.prop_of_iso (XIsoBiprod f r (r - 1) (by simp)).symm
    (IsAdditiveSub.biprod_mem _ (BinaryBiproduct.isBilimit _ _) (hK _) (hL _))

lemma sumComplex_X_mem {K L : ChainComplex A.cz ℤ} (b : ∀ r, BinaryBicone (K.X r) (L.X r))
    (hb : ∀ r, (b r).IsBilimit) (hK : ∀ r, U (K.X r)) (hL : ∀ r, U (L.X r)) (r : ℤ) :
    U ((sumComplex b).X r) :=
  IsAdditiveSub.biprod_mem _ (hb r) (hK r) (hL r)

lemma PairOn.cast_D {J : StrictInvolution A.cz} {P Q : SymPoincare J N} (h : P = Q)
    (T : PairOn P) : (h ▸ T).D = T.D := by
  subst h; rfl

/-- The chain objects of a union lie in `U` if those of both interiors and of the boundary do. -/
lemma union_X_mem (X Y : SymPair A.cz.inv N) (h : Y.bd = X.bd.neg)
    (hX : ∀ r, U (X.D.X r)) (hY : ∀ r, U (Y.D.X r)) (hB : ∀ r, U (X.bd.C.X r)) (r : ℤ) :
    U ((SymPair.union X Y h).C.X r) := by
  refine cone_X_mem U _ hB (fun r ↦ sumComplex_X_mem U _ (fun _ ↦ BinaryBiproduct.isBilimit _ _)
    hX (fun r ↦ ?_) r) r
  change U ((h ▸ Y.toPairOn).D.X r)
  rw [PairOn.cast_D]
  exact hY r

end Objects

/-- A closed complex over `C_ℤ(A)` with all chain objects in the negative half-line has class
`0` (Eilenberg swindle on `C_{ℤ≤}(A)`). -/
theorem cls_eq_zero_of_negHalf {M : ℤ} (P : SymPoincare A.cz.inv M)
    (h : ∀ r, negHalf A (P.C.X r)) : Lconc.cls P = 0 := by
  have e : P = (P.lift h).map (A.cz.subIncl (negHalf A)) := rfl
  have h0 : (Lconc.cls (P.lift h) : Lconc A.czNeg M) = 0 := Lconc.czNeg_eq_zero A _
  rw [e, ← Lconc.map_cls, h0, map_zero]

/-- A closed complex over `C_ℤ(A)` with all chain objects in the positive half-line has class
`0`. -/
theorem cls_eq_zero_of_posHalf {M : ℤ} (P : SymPoincare A.cz.inv M)
    (h : ∀ r, posHalf A (P.C.X r)) : Lconc.cls P = 0 := by
  have e : P = (P.lift h).map (A.cz.subIncl (posHalf A)) := rfl
  have h0 : (Lconc.cls (P.lift h) : Lconc A.czPos M) = 0 := Lconc.czPos_eq_zero A _
  rw [e, ← Lconc.map_cls, h0, map_zero]

/-- **Half-line vanishing for unions**: the union of two pairs whose interiors and common
boundary lie in the negative half-line is `0` in `Lconc (C_ℤ A) (N+1)`. -/
theorem cls_union_eq_zero_of_negHalf (X Y : SymPair A.cz.inv N) (h : Y.bd = X.bd.neg)
    (hX : ∀ r, negHalf A (X.D.X r)) (hY : ∀ r, negHalf A (Y.D.X r))
    (hB : ∀ r, negHalf A (X.bd.C.X r)) : Lconc.cls (SymPair.union X Y h) = 0 :=
  cls_eq_zero_of_negHalf _ (union_X_mem _ X Y h hX hY hB)

/-- **Half-line vanishing for unions**, positive half-line. -/
theorem cls_union_eq_zero_of_posHalf (X Y : SymPair A.cz.inv N) (h : Y.bd = X.bd.neg)
    (hX : ∀ r, posHalf A (X.D.X r)) (hY : ∀ r, posHalf A (Y.D.X r))
    (hB : ∀ r, posHalf A (X.bd.C.X r)) : Lconc.cls (SymPair.union X Y h) = 0 :=
  cls_eq_zero_of_posHalf _ (union_X_mem _ X Y h hX hY hB)

/-! ### The two cut pairs over a common window boundary -/

namespace CutData

variable {P : SymPoincare A.cz.inv (N + 1)} {D : CutData P} (S : D.Sec) (hp : P.p = 𝟙 _)
  (hN : 0 ≤ N) {Q : SymPoincare A.czBdd.inv N}
  (e : (lowerPair S hp hN).bd.HomotopyIsometry (Q.map (A.cz.subIncl (bdd A))))

/-- The lower cut pair with its boundary transported to the window complex. -/
def lowerPairW : SymPair A.cz.inv N :=
  (lowerPair S hp hN).transportBd e.toKarHtpyEquiv (Q.map (A.cz.subIncl (bdd A))).p_idem
    (Q.map (A.cz.subIncl (bdd A))).support

/-- The upper cut pair with its boundary transported to the window complex (along the same
equivalence). -/
def upperPairW : SymPair A.cz.inv N :=
  (upperPair S hp hN).transportBd e.toKarHtpyEquiv (Q.map (A.cz.subIncl (bdd A))).p_idem
    (Q.map (A.cz.subIncl (bdd A))).support

theorem upperPairW_bd : (upperPairW S hp hN e).bd = (lowerPairW S hp hN e).bd.neg :=
  SymPoincare.ext_of_φ rfl HEq.rfl (heq_of_eq (by
    simp [upperPairW, lowerPairW, SymPair.transportBd, SymPoincare.transport, upperPair,
      lowerPair, rawUpperPair, RawPair.transportBd, RawPair.bdTransport, SymPoincare.neg]
    rfl))

lemma lowerPairW_D_negHalf (r : ℤ) : negHalf A ((lowerPairW S hp hN e).D.X r) :=
  lowerPair_D_negHalf S hp hN r

lemma upperPairW_D_posHalf (r : ℤ) : posHalf A ((upperPairW S hp hN e).D.X r) :=
  upperPair_D_posHalf S hp hN r

lemma lowerPairW_bd_bdd (r : ℤ) : bdd A ((lowerPairW S hp hN e).bd.C.X r) :=
  (Q.C.X r).property

/-- The window boundary is homotopy isometric to `Q`. -/
def lowerPairW_bdIsometry :
    (lowerPairW S hp hN e).bd.HomotopyIsometry (Q.map (A.cz.subIncl (bdd A))) :=
  ((lowerPair S hp hN).bd.transportIsometry _ _ e.toKarHtpyEquiv).symm.trans e

end CutData

/-- **Algebraic transversality for honest free complexes over `C_ℤ(A)`** (the half of the
`DecBij` input that needs neither the line complex nor triads): every honest free
`(N+1)`-dimensional Poincaré complex `P` over `C_ℤ(A)` (`N ≥ 0`) admits `(N+1)`-dimensional
Poincaré pairs `X⁻`, `X⁺` with **opposite boundaries** `∂X⁺ = -∂X⁻`, interiors in the negative
resp. positive half-line, and common boundary on bounded objects, homotopy isometric to a
complex over `C_ℤ^{bdd}(A)` (`≃ A`, `Lconc.czBddEquiv`).  (The cut pairs; that `P` is homotopy
isometric to `X⁻ ∪ X⁺` is not proved here.) -/
theorem exists_cutPairs (hN : 0 ≤ N) (P : SymPoincare A.cz.inv (N + 1)) (hp : P.p = 𝟙 _) :
    ∃ (X Y : SymPair A.cz.inv N) (_ : Y.bd = X.bd.neg) (Q : SymPoincare A.czBdd.inv N),
      (∀ r, negHalf A (X.D.X r)) ∧ (∀ r, posHalf A (Y.D.X r)) ∧ (∀ r, bdd A (X.bd.C.X r)) ∧
      Nonempty (X.bd.HomotopyIsometry (Q.map (A.cz.subIncl (bdd A)))) := by
  obtain ⟨ψ, -, ⟨H⟩, -⟩ := P.poincare
  obtain ⟨b₁, hb₁⟩ := exists_bound_family (X := fun r ↦ P.C.X r) (Y := fun r ↦ P.C.X (r - 1))
    (fun r ↦ P.C.d r (r - 1)) (Finset.Icc 1 (N + 1)) fun r hr ↦ by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hr
      rcases hr with hr | hr
      · exact (isZero_X_of_p_eq_id hp (by omega)).eq_of_tgt _ _
      · exact (isZero_X_of_p_eq_id hp (by omega)).eq_of_src _ _
  obtain ⟨b₂, hb₂⟩ := exists_bound_family
    (X := fun r ↦ (dualComplex A.cz.inv (N + 1) P.C).X r) (Y := fun r ↦ P.C.X r)
    (fun r ↦ P.φ.f r) (Finset.Icc 0 (N + 1)) fun r hr ↦ by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hr
      exact (isZero_X_of_p_eq_id hp (by omega)).eq_of_tgt _ _
  obtain ⟨b₃, hb₃⟩ := exists_propLE (ψ.f 0)
  obtain ⟨b₄, hb₄⟩ := exists_propLE (H.hom 0 1)
  set b := b₁ + b₂ + b₃ + b₄ with hb
  let D : CutData P :=
    { b := b
      t := fun r ↦ r * b
      hd := fun r ↦ (hb₁ r).mono (by omega)
      hφ := fun r ↦ (hb₂ r).mono (by omega)
      ht := fun r ↦ le_of_eq (by ring)
      hp := fun r ↦ Or.inl (by rw [hp, id_f]) }
  let S : D.Sec :=
    { ψ := ψ
      H := H
      hψ := hb₃.mono (show b₃ ≤ b by omega)
      hH := hb₄.mono (show b₄ ≤ b by omega)
      ht := by
        change 0 * (b : ℤ) + b ≤ (N + 1 - 0) * b
        nlinarith [(Nat.cast_nonneg b : (0 : ℤ) ≤ b)] }
  obtain ⟨Q, ⟨e⟩⟩ := CutData.exists_lowerPair_window S hp hN
  exact ⟨_, _, CutData.upperPairW_bd S hp hN e, Q, CutData.lowerPairW_D_negHalf S hp hN e,
    CutData.upperPairW_D_posHalf S hp hN e, CutData.lowerPairW_bd_bdd S hp hN e,
    ⟨CutData.lowerPairW_bdIsometry S hp hN e⟩⟩

end CZ

end

end HSFormal.LTheory
