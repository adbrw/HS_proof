import HSFormal.LTheory.Model.LiftingClosedSubTrace
import HSFormal.LTheory.Model.LiftingPairNull

/-!
# (L2) for closed lifting pairs: `LiftingClosedSubAll`

Proof of the hypothesis `LiftingClosedSubAll` of `Model/Exact.lean` (exactness of the colimit
model at `L_n(A)`): a closed complex `W` over `C_ℤ^{∘(k+1)}(A)` whose image over
`C_ℤ^{∘(k+1)}(A/U)` is isometric to `D ⊗ ℝ` with `D` null-cobordant comes from `U`.

## Proof

1. **Free null-cobordism.**  A null-cobordism `Y` of `D` gives the free line pair
   `LineData.freePairOn Y` (module 17a) with boundary `D ⊗ ℝ` and identity interior idempotent;
   transported along `czIterQuotIso` and retargeted along the given isometry
   (`PairOn.retargetIso`) it is a null-cobordism of `W/U = quotBd` (`closedPair_toQuot`), free on
   `[0, N + 2]`.
2. **Relative lift and compression** (module 10): with the face `ofClosedZero W` (a pair on the
   zero boundary), `exists_of_quotPair` (with `lo = 0`) gives a triad `T` whose top is Poincaré
   modulo `U`; `exists_flat` compresses `E_0` so that the bottom of the new face splits.
3. **Truncation of the new face** (`exists_faceTrunc`, the proof of `exists_relBd`): a Kar
   equivalence `e : (Z_D, p_Z) ≃ (Z_D, q)` with `q` supported in `[0, N + 1]`; the honest face
   `Z' = Z.transport e` is contractible modulo `U` (`contractibleMod_pZ`).
4. **The trace cobordism in general degrees** (`LiftingClosedSubTrace.lean`): the raw pair
   `(i₀', i₁') : W ⊕ -Z ⟶ M` is Poincaré (Wall's two-out-of-three on a ladder); its boundary
   transported along `1 ⊕ e` (`RawPair.transportBd`) is exactly `W ⊕ -Z'`, so
   `[W] = [Z']` in `Lconc`.
5. **Domination** (`SymPoincare.exists_sub`): `Z' ≃ incl(R)` for a Poincaré complex `R` of `U`;
   then `map_ofDeg` and `czIterSubIso` place `[W]` in the image of `Lmodel.map F.incl`.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression
  homotopyCofiber

noncomputable section

attribute [local implicit_reducible] KaroubiFiltration.czIter InvCat.czIter SymPair.map

namespace TriadOn

variable {A : InvCat} {N : ℤ} {Q : SymPoincare A.inv (N + 1)}
  (T : TriadOn (PairData.ofClosedZero Q) (PairData.zero (zeroP (J := A.inv) (N := N))))

/-- **Truncation of the new face in general degrees** (the proof of `exists_relBd`, keeping the
equivalence): if the bottom differential of `Z_D` is Kar-split, `(Z_D, p_Z)` is Kar equivalent
to `(Z_D, q)` with `q` supported in `[0, N + 1]`. -/
theorem exists_faceTrunc (hW : (PairData.ofClosedZero Q).IsPoincare)
    (a : T.E.X 0 ⟶ T.E.X (N + 1 + 1 - 0)) (b : T.E.X 0 ⟶ Q.C.X 0) (c : T.E.X 0 ⟶ T.E.X 1)
    (hab : T.pE.f 0 ≫ (a ≫ T.top 0 + b ≫ T.i₀.f 0 + c ≫ T.E.d 1 0) ≫ T.pE.f 0 = T.pE.f 0) :
    ∃ q : T.ZD ⟶ T.ZD, q ≫ q = q ∧ SupportedIn q 0 (N + 1) ∧ Nonempty (KarHtpyEquiv T.pZ q) := by
  obtain ⟨q₁, hq₁, hneg, hle, ⟨e₁⟩⟩ := exists_truncBot T.pZc (T.botS a b c) T.pZc_idem
    (fun k hk ↦ T.pZc_f_neg hk) (T.botS_kar a b c) (T.botS_d a b c hab)
  have hs₁ : SupportedIn q₁ 0 (N + 1 + 1) := by
    intro r hr
    rcases hr with hr | hr
    · exact hneg r hr
    · rw [← hle, comp_f, T.pZ_support T.support le_rfl (by omega) r (Or.inr (by omega)),
        comp_zero]
  let X₁ := (T.relBdRaw hW).transportD e₁ hq₁
  exact ⟨X₁.truncTopIdem hs₁, X₁.truncTopIdem_idem hs₁, X₁.supportedIn_truncTopIdem hs₁,
    ⟨e₁.trans (X₁.truncTopEquiv hs₁)⟩⟩

variable (hW : (PairData.ofClosedZero Q).IsPoincare) {q : T.ZD ⟶ T.ZD} (hq : q ≫ q = q)
  (hs : SupportedIn q 0 (N + 1)) (e : KarHtpyEquiv T.pZ q)

/-- The honest new face `Z' = (Z_D, q, f φ_Z f^*)`. -/
abbrev faceZ : SymPoincare A.inv (N + 1) := (T.Zr hW).transport e hq hs

/-- The boundary equivalence `1 ⊕ e : (Q ⊕ Z, p_Q ⊕ p_Z) ≃ (Q ⊕ Z, p_Q ⊕ q)`. -/
abbrev eB : KarHtpyEquiv (T.unionRaw hW).p
    (sumFst T.bT ≫ Q.p ≫ sumInl T.bT + sumSnd T.bT ≫ q ≫ sumInr T.bT) :=
  KarHtpyEquiv.sum (KarHtpyEquiv.refl Q.p_idem) e T.bT T.bT

include hq in
lemma pB'_idem : (sumFst T.bT ≫ Q.p ≫ sumInl T.bT + sumSnd T.bT ≫ q ≫ sumInr T.bT) ≫
    (sumFst T.bT ≫ Q.p ≫ sumInl T.bT + sumSnd T.bT ≫ q ≫ sumInr T.bT) =
      sumFst T.bT ≫ Q.p ≫ sumInl T.bT + sumSnd T.bT ≫ q ≫ sumInr T.bT := by
  simp [add_comp, comp_add, reassoc_of% hq]

include hs in
lemma pB'_support : SupportedIn
    (sumFst T.bT ≫ Q.p ≫ sumInl T.bT + sumSnd T.bT ≫ q ≫ sumInr T.bT) 0 (N + 1) := by
  intro r hr
  simp [Q.support r hr, hs r hr]

/-- **The trace cobordism, transported**: its boundary is exactly `Q ⊕ -Z'`. -/
lemma transportBd_bd : ((T.unionRaw hW).transportBd (T.eB hW e) (T.pB'_idem hq)
    (T.pB'_support hs)).bd = Q.sum (T.faceZ hW hq hs e).neg T.bT := by
  refine SymPoincare.ext_of_φ rfl HEq.rfl (heq_of_eq ?_)
  simp only [RawPair.transportBd_bd, RawPair.bdTransport_φ, unionRaw_φ, Bu, RawSym.sum_φ,
    RawSym.ofSymPoincare_φ, RawSym.neg_φ, KarHtpyEquiv.sum_f, KarHtpyEquiv.refl_f,
    SymPoincare.sum_φ, SymPoincare.neg_φ, faceZ, RawSym.transport_φ]
  simp [add_comp, comp_add]

end TriadOn

/-! ### The level-wise statement -/

namespace KaroubiFiltration

variable {A : InvCat} (F : KaroubiFiltration A)

/-- **(L2) for closed complexes, level-wise**: a closed `(N+1)`-dimensional complex `Q` over `A`
whose image `Q/U` (as `quotBd` of the closed pair) bounds a Poincaré pair over `A/U` free on
`[0, N + 2]` is, in `Lconc`, the image of a Poincaré complex of `U`. -/
theorem exists_cls_eq_map_incl {N : ℤ} (hN : 0 ≤ N + 1) (Q : SymPoincare A.inv (N + 1))
    (Y : PairOn (TriadOn.quotBd F (PairData.isPoincare_ofClosedZero Q)
      (SymPoincare.closedPair_mem F Q)))
    (hpY : ∀ r, 0 ≤ r → r ≤ N + 1 + 1 → Y.pD.f r = 𝟙 _) :
    ∃ R : SymPoincare F.sub.inv (N + 1), Lconc.cls Q = Lconc.cls (R.map F.inclI) := by
  have hW := PairData.isPoincare_ofClosedZero Q
  have hP := SymPoincare.closedPair_mem F Q
  obtain ⟨T, hT, -, hp⟩ := TriadOn.exists_of_quotPair hW hP Y 0 le_rfl Y.support hpY
  have hp0 : T.pE.f 0 = 𝟙 _ := hp 0 le_rfl (by omega)
  obtain ⟨ε, hε, hU, a, b, c, hab⟩ := T.exists_flat hT hp0 hN
  have hT' := T.isPoincareTopMod_flat ε hp0 hε hW hP hU hN hT
  obtain ⟨q, hq, hs, ⟨e⟩⟩ := (T.flat ε hp0 hε hN).exists_faceTrunc hW a b c hab
  let T' := T.flat ε hp0 hε hN
  have hnull : NullCobordant (Q.sum (T'.faceZ hW hq hs e).neg T'.bT) :=
    ⟨_, T'.transportBd_bd hW hq hs e⟩
  have hcls : Lconc.cls Q = Lconc.cls (T'.faceZ hW hq hs e) := by
    have h0 := Lconc.cls_eq_zero hnull
    rw [Lconc.cls_sum, Lconc.cls_neg] at h0
    exact add_neg_eq_zero.mp h0
  have hc : F.ContractibleMod (T'.faceZ hW hq hs e).p :=
    (T'.contractibleMod_pZ hT').of_karHtpyEquiv e
  obtain ⟨R, ⟨iso⟩⟩ := (T'.faceZ hW hq hs e).exists_sub hc
  exact ⟨R, hcls.trans (Lconc.cls_eq_of_isometry iso)⟩

/-- **(L2) for lifting pairs with empty boundary** (`LiftingClosedSub`) for every Karoubi
filtration. -/
theorem liftingClosedSub : F.LiftingClosedSub := by
  intro k N D hN hD W ⟨e₀⟩ n h
  obtain ⟨Y₀⟩ := nullCobordant_iff_nonempty_pairOn.1 hD
  let L := CZ.lineData (F.quot.czIter k)
  let Φ := (F.czIterQuotIso (k + 1)).inv
  let F' := F.czIter (k + 1)
  let Z : PairOn ((L.sym D).map Φ) := ((L.freePairOn Y₀).toPair.map Φ).toPairOn
  have hq : TriadOn.quotBd F' (PairData.isPoincare_ofClosedZero W)
      (SymPoincare.closedPair_mem F' W) = (W.map (CZ.mapIter (k + 1) F.proj)).map Φ := by
    rw [TriadOn.quotBd, SymPoincare.closedPair_toQuot]
    · change _ = W.map (CZ.mapIter (k + 1) F.proj ≫ (F.czIterQuotIso (k + 1)).inv)
      rw [mapIter_proj_eq]
    · exact SymPoincare.closedPair_mem F' W
  let iso : SymPoincare.HomotopyIsometry (TriadOn.quotBd F' (PairData.isPoincare_ofClosedZero W)
      (SymPoincare.closedPair_mem F' W)) ((L.sym D).map Φ) :=
    (SymPoincare.HomotopyIsometry.ofEq' hq).trans (e₀.map Φ)
  have hZ : ∀ r, 0 ≤ r → r ≤ N + 1 + 1 → Z.pD.f r = 𝟙 _ := fun r _ _ ↦ by
    dsimp [Z, SymPair.toPairOn]; simp
    exact congrArg (fun f ↦ HomologicalComplex.Hom.f f r)
      ((Φ.F.mapHomologicalComplex (ComplexShape.down ℤ)).map_id _)
  obtain ⟨R, hR⟩ := F'.exists_cls_eq_map_incl (by omega) W (Z.retargetIso iso.symm) hZ
  refine ⟨Lmodel.ofDeg F.sub n (k + 1) h (Lconc.cls (R.map (F.czIterSubIso (k + 1)).hom)), ?_⟩
  rw [Lmodel.map_ofDeg, Lconc.map_cls, hR]
  congr 2
  change R.map ((F.czIterSubIso (k + 1)).hom ≫ CZ.mapIter (k + 1) F.incl) = _
  rw [mapIter_incl_eq, Iso.hom_inv_id_assoc]

end KaroubiFiltration

/-- **`LiftingClosedSubAll`**: (L2) for lifting pairs with empty boundary holds for every Karoubi
filtration, so the colimit model is exact at `L_n(A)` (`Lmodel.exactAll_A`). -/
theorem liftingClosedSubAll : LiftingClosedSubAll := fun _ F ↦ F.liftingClosedSub

/-- The interface field `exact_A` of the colimit model, without hypothesis. -/
theorem Lmodel.exactAll_A_of_liftingClosedSub {A : InvCat} (F : KaroubiFiltration A) (n : ℤ) :
    Function.Exact (Lmodel.map F.incl n) (Lmodel.map F.proj n) :=
  Lmodel.exactAll_A liftingClosedSubAll F n

end

end HSFormal.LTheory
