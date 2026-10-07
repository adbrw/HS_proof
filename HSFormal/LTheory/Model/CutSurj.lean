import HSFormal.LTheory.Model.CutIso
import HSFormal.LTheory.Model.UnionRelStatement
import HSFormal.LTheory.Model.Wall
import HSFormal.LTheory.Model.LinePairs

/-!
# Surjectivity of the line transitions from relation (R) (lower L-theory model, module 22)

Assembly of the surjectivity half of `DecBij`.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression
  homotopyCofiber CZ

noncomputable section

/-! ### Consequences of relation (R) for unions over a window boundary -/

section UnionRelChain

variable {A : InvCat} {N : ℤ}

lemma bdd_neg_neg (B : SymPoincare A.cz.inv N) : B.neg = B.neg.neg.neg := by
  rw [SymPoincare.neg_neg]

/-- **Unions over a window boundary depend only on the boundary** (from relation (R) and the
half-line swindles): for pairs `X, L` on `B` with interiors in the negative half-line and pairs
`X', L'` on `-B` with interiors in the positive half-line, `B` bounded,
`[X ∪ X'] = [L ∪ L']`. -/
theorem cls_union_eq_of_unionRel (hR : UnionRel A.cz N) {B : SymPoincare A.cz.inv N}
    (hB : ∀ r, bdd A (B.C.X r)) (X L : PairOn B) (X' L' : PairOn B.neg)
    (hX : ∀ r, negHalf A (X.D.X r)) (hL : ∀ r, negHalf A (L.D.X r))
    (hX' : ∀ r, posHalf A (X'.D.X r)) (hL' : ∀ r, posHalf A (L'.D.X r)) :
    Lconc.cls (X.union X') = Lconc.cls (L.union L') := by
  have h₁ := hR X.toPair L.toPair X'.toPair rfl rfl rfl
  have v₁ : Lconc.cls (SymPair.union X.toPair L.toPair.neg rfl) = 0 :=
    cls_union_eq_zero_of_negHalf X.toPair L.toPair.neg rfl hX hL (fun r ↦ (hB r).2)
  have h₂ := hR X'.toPair.neg L.toPair X'.toPair (bdd_neg_neg B) rfl (bdd_neg_neg B)
  have v₂ : Lconc.cls (SymPair.union X'.toPair.neg X'.toPair (bdd_neg_neg B)) = 0 :=
    cls_union_eq_zero_of_posHalf X'.toPair.neg X'.toPair _ hX' hX' (fun r ↦ (hB r).1)
  have h₃ := hR L'.toPair.neg L.toPair L'.toPair (bdd_neg_neg B) rfl (bdd_neg_neg B)
  have v₃ : Lconc.cls (SymPair.union L'.toPair.neg L'.toPair (bdd_neg_neg B)) = 0 :=
    cls_union_eq_zero_of_posHalf L'.toPair.neg L'.toPair _ hL' hL' (fun r ↦ (hB r).1)
  have h₄ := hR X'.toPair.neg L'.toPair.neg L.toPair.neg (bdd_neg_neg B) (bdd_neg_neg B) rfl
  have v₄ : Lconc.cls (SymPair.union X'.toPair.neg L'.toPair.neg.neg rfl) = 0 :=
    cls_union_eq_zero_of_posHalf X'.toPair.neg L'.toPair.neg.neg rfl hX' hL' (fun r ↦ (hB r).1)
  change Lconc.cls (SymPair.union X.toPair X'.toPair rfl) =
    Lconc.cls (SymPair.union L.toPair L'.toPair rfl)
  rw [v₁] at h₁
  rw [v₂] at h₂
  rw [v₃] at h₃
  rw [v₄] at h₄
  have e₁ := sub_eq_zero.mp h₁
  have e₄ := sub_eq_zero.mp h₄
  rw [zero_sub] at h₂ h₃
  rw [e₄, ← h₃] at h₂
  rw [e₁]
  exact neg_injective h₂

end UnionRelChain

/-! ### Cut data and window boundaries -/

namespace CZ

variable {A : InvCat} {N : ℤ}

/-- Every honest free `(N+1)`-dimensional Poincaré complex over `C_ℤ(A)` (`N ≥ 0`) has cut data
with `Sec` data (thresholds `t_r = r b`; as in `CZ.exists_cutPairs`). -/
theorem exists_cutData_sec (hN : 0 ≤ N) (P : SymPoincare A.cz.inv (N + 1)) (hp : P.p = 𝟙 _) :
    ∃ D : CutData P, Nonempty D.Sec := by
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
  exact ⟨D, ⟨S⟩⟩

/-- A window complex is homotopy isometric to its sum placed at `0`:
`Q.map incl ≃ (Q.map Σ).map atZero` (`Window.sumOfBaseIso`). -/
theorem nonempty_window_isometry (Q : SymPoincare A.czBdd.inv N) :
    Nonempty ((Q.map (A.cz.subIncl (bdd A))).HomotopyIsometry
      ((Q.map (Window.sumF A)).map (atZero A))) := by
  let e := Window.sumOfBaseIso A
  have hι : ∀ X, e.iso.inv.app X ≫ A.czBdd.inv.star (e.iso.inv.app X) = 𝟙 _ :=
    fun X ↦ by erw [e.star_inv]; exact e.iso.inv_hom_id_app X
  have hr : ∀ i, (retractIdem e.iso.inv Q).f i = 𝟙 _ := fun i ↦ by
    change A.czBdd.inv.star (e.iso.inv.app (Q.C.X i)) ≫ e.iso.inv.app (Q.C.X i) = 𝟙 _
    erw [e.star_inv]
    exact e.iso.hom_inv_id_app _
  have hcut : (Q.map (Window.sumF A ≫ Window.ofBase A)).p ≫ retractIdem e.iso.inv Q =
      (Q.map (Window.sumF A ≫ Window.ofBase A)).p := by
    ext i
    rw [comp_f, hr, comp_id]
  have e₁ := ((Q.map (Window.sumF A ≫ Window.ofBase A)).cutIsometry
    (isReducing_retractIdem Q hι) hcut).trans (retractIsometry Q hι)
  exact ⟨e₁.symm.map (A.cz.subIncl (bdd A))⟩

end CZ

/-! ### The half-line splitting of the line complex -/

/-- **Half-line splitting** of `Q ⊗ ℝ` (the line input of `DecBij` surjectivity): for every
honest free `N`-dimensional Poincaré complex `Q` over `A`, there are an `(N+1)`-dimensional
Poincaré pair `Y` on `Q` placed at `0` (`Q.map (atZero A)`) with interior in the negative
half-line and a pair `Z` on `-(Q at 0)` with interior in the positive half-line whose union has
the class `±[Q ⊗ ℝ] = ±tensorLine [Q]` (geometrically: `Q × (-∞, 0]` and `Q × [0, ∞)`). -/
def HalfLineSplit (A : InvCat) (N : ℤ) : Prop :=
  ∀ Q : SymPoincare A.inv N, Q.p = 𝟙 _ →
    ∃ (Y : PairOn (Q.map (CZ.atZero A))) (Z : PairOn (Q.map (CZ.atZero A)).neg),
      (∀ r, CZ.negHalf A (Y.D.X r)) ∧ (∀ r, CZ.posHalf A (Z.D.X r)) ∧
      (Lconc.cls (Y.union Z) = Lconc.tensorLine A N (Lconc.cls Q) ∨
        Lconc.cls (Y.union Z) = -Lconc.tensorLine A N (Lconc.cls Q))

/-- `HalfLineSplit` for all (Kar) `N`-dimensional Poincaré complexes over `A`, without the
freeness hypothesis (needed at level `k = 0`, where `NegK` gives no free models over `A`). -/
def HalfLineSplitKar (A : InvCat) (N : ℤ) : Prop :=
  ∀ Q : SymPoincare A.inv N,
    ∃ (Y : PairOn (Q.map (CZ.atZero A))) (Z : PairOn (Q.map (CZ.atZero A)).neg),
      (∀ r, CZ.negHalf A (Y.D.X r)) ∧ (∀ r, CZ.posHalf A (Z.D.X r)) ∧
      (Lconc.cls (Y.union Z) = Lconc.tensorLine A N (Lconc.cls Q) ∨
        Lconc.cls (Y.union Z) = -Lconc.tensorLine A N (Lconc.cls Q))

/-- The line input in the form of the task statement: pairs `L⁻` (negative half-line) and `L⁺`
(positive half-line) with `∂L⁺ = -∂L⁻`, `∂L⁻ ≃ Q` placed at `0`, and `[L⁻ ∪ L⁺] = ±[Q ⊗ ℝ]`. -/
def LineCutIso (A : InvCat) (N : ℤ) : Prop :=
  ∀ Q : SymPoincare A.inv N, Q.p = 𝟙 _ →
    ∃ (L₁ L₂ : SymPair A.cz.inv N) (h : L₂.bd = L₁.bd.neg),
      (∀ r, CZ.negHalf A (L₁.D.X r)) ∧ (∀ r, CZ.posHalf A (L₂.D.X r)) ∧
      Nonempty (L₁.bd.HomotopyIsometry (Q.map (CZ.atZero A))) ∧
      (Lconc.cls (SymPair.union L₁ L₂ h) = Lconc.tensorLine A N (Lconc.cls Q) ∨
        Lconc.cls (SymPair.union L₁ L₂ h) = -Lconc.tensorLine A N (Lconc.cls Q))

/-- The task-statement form of the line input implies `HalfLineSplit` (retarget both pairs to
`Q` at `0` along the boundary isometry, `nonempty_union_retargetIso`). -/
theorem LineCutIso.halfLineSplit {A : InvCat} {N : ℤ} (h : LineCutIso A N) :
    HalfLineSplit A N := by
  intro Q hQ
  obtain ⟨L₁, L₂, hb, h₁, h₂, ⟨e⟩, hc⟩ := h Q hQ
  obtain ⟨eU⟩ := nonempty_union_retargetIso e L₁.toPairOn (hb ▸ L₂.toPairOn)
  refine ⟨L₁.toPairOn.retargetIso e, (hb ▸ L₂.toPairOn).retargetIsoNeg e, h₁, fun r ↦ ?_, ?_⟩
  · change CZ.posHalf A ((hb ▸ L₂.toPairOn).D.X r)
    rw [CZ.PairOn.cast_D]
    exact h₂ r
  · rw [Lconc.cls_eq_of_isometry eU]
    exact hc

namespace CZ

variable {A : InvCat} {N : ℤ}

lemma bdd_atZero_X (Q : SymPoincare A.inv N) (r : ℤ) : bdd A ((Q.map (atZero A)).C.X r) :=
  ((Q.map (Window.ofBase A)).C.X r).property

/-- **Surjectivity onto free classes, given (R) and the half-line splitting**: every honest free
`(N+1)`-dimensional Poincaré complex `P` over `C_ℤ(A)` (`N ≥ 0`) has class `±tensorLine [Q]`,
provided every `N`-dimensional Poincaré complex over `A` is homotopy isometric to a free one.
Proof: cut `P` (`cls_cutUnion`), retarget the two cut pairs to the free model `Q` of the window
boundary placed at `0` (`nonempty_union_retargetIso`), and compare with the half-line pairs of
`Q ⊗ ℝ` by (R) (`cls_union_eq_of_unionRel`). -/
theorem cls_mem_range_tensorLine (hR : UnionRel A.cz N) (hL : HalfLineSplit A N)
    (hfree : ∀ Q : SymPoincare A.inv N, ∃ Q' : SymPoincare A.inv N, Q'.p = 𝟙 _ ∧
      Nonempty (Q.HomotopyIsometry Q'))
    (hN : 0 ≤ N) (P : SymPoincare A.cz.inv (N + 1)) (hp : P.p = 𝟙 _) :
    Lconc.cls P ∈ Set.range (Lconc.tensorLine A N) := by
  obtain ⟨D, ⟨S⟩⟩ := exists_cutData_sec hN P hp
  obtain ⟨Qw, ⟨ew⟩⟩ := CutData.exists_lowerPair_window S hp hN
  obtain ⟨e₁⟩ := nonempty_window_isometry Qw
  obtain ⟨Q, hQ, ⟨e₂⟩⟩ := hfree (Qw.map (Window.sumF A))
  let e : (CutData.cutBd S hp hN).HomotopyIsometry (Q.map (atZero A)) :=
    ew.trans (e₁.trans (e₂.map (atZero A)))
  obtain ⟨Y, Z, hY, hZ, hYZ⟩ := hL Q hQ
  have hU := cls_union_eq_of_unionRel hR (bdd_atZero_X Q)
    ((CutData.lowerPair S hp hN).toPairOn.retargetIso e) Y
    ((CutData.upperOn S hp hN).retargetIsoNeg e) Z
    (CutData.lowerPair_D_negHalf S hp hN) hY (D.subC_posHalf) hZ
  obtain ⟨eU⟩ := nonempty_union_retargetIso e (CutData.lowerPair S hp hN).toPairOn
    (CutData.upperOn S hp hN)
  rw [Lconc.cls_eq_of_isometry eU, show (CutData.lowerPair S hp hN).toPairOn.union
    (CutData.upperOn S hp hN) = CutData.cutUnion S hp hN from (CutData.cutUnion_eq S hp hN).symm,
    CutData.cls_cutUnion] at hU
  rcases Int.units_eq_one_or N.negOnePow with hε | hε <;> rw [hε] at hU <;>
    rcases hYZ with h | h <;> rw [h] at hU <;>
    simp only [Units.val_neg, Units.val_one, neg_smul, one_smul, neg_inj] at hU
  all_goals first
    | exact ⟨Lconc.cls Q, hU.symm⟩
    | (refine ⟨-Lconc.cls Q, ?_⟩; rw [map_neg, ← hU, neg_neg])
    | (refine ⟨-Lconc.cls Q, ?_⟩; rw [map_neg, hU, neg_neg])
    | (refine ⟨-Lconc.cls Q, ?_⟩; rw [map_neg, ← hU])

/-- `cls_mem_range_tensorLine` with the Kar half-line splitting (no free models needed). -/
theorem cls_mem_range_tensorLine_kar (hR : UnionRel A.cz N) (hL : HalfLineSplitKar A N)
    (hN : 0 ≤ N) (P : SymPoincare A.cz.inv (N + 1)) (hp : P.p = 𝟙 _) :
    Lconc.cls P ∈ Set.range (Lconc.tensorLine A N) := by
  obtain ⟨D, ⟨S⟩⟩ := exists_cutData_sec hN P hp
  obtain ⟨Qw, ⟨ew⟩⟩ := CutData.exists_lowerPair_window S hp hN
  obtain ⟨e₁⟩ := nonempty_window_isometry Qw
  let Q := Qw.map (Window.sumF A)
  let e : (CutData.cutBd S hp hN).HomotopyIsometry (Q.map (atZero A)) := ew.trans e₁
  obtain ⟨Y, Z, hY, hZ, hYZ⟩ := hL Q
  have hU := cls_union_eq_of_unionRel hR (bdd_atZero_X Q)
    ((CutData.lowerPair S hp hN).toPairOn.retargetIso e) Y
    ((CutData.upperOn S hp hN).retargetIsoNeg e) Z
    (CutData.lowerPair_D_negHalf S hp hN) hY (D.subC_posHalf) hZ
  obtain ⟨eU⟩ := nonempty_union_retargetIso e (CutData.lowerPair S hp hN).toPairOn
    (CutData.upperOn S hp hN)
  rw [Lconc.cls_eq_of_isometry eU, show (CutData.lowerPair S hp hN).toPairOn.union
    (CutData.upperOn S hp hN) = CutData.cutUnion S hp hN from (CutData.cutUnion_eq S hp hN).symm,
    CutData.cls_cutUnion] at hU
  rcases Int.units_eq_one_or N.negOnePow with hε | hε <;> rw [hε] at hU <;>
    rcases hYZ with h | h <;> rw [h] at hU <;>
    simp only [Units.val_neg, Units.val_one, neg_smul, one_smul, neg_inj] at hU
  all_goals first
    | exact ⟨Lconc.cls Q, hU.symm⟩
    | (refine ⟨-Lconc.cls Q, ?_⟩; rw [map_neg, ← hU, neg_neg])
    | (refine ⟨-Lconc.cls Q, ?_⟩; rw [map_neg, hU, neg_neg])
    | (refine ⟨-Lconc.cls Q, ?_⟩; rw [map_neg, ← hU])

end CZ


/-! ### Free complexes with identity idempotent -/

section FreeId

open FreeLine

/-- A complex whose idempotent is the identity in its support range `[0, M]` is homotopy
isometric to one with identity idempotent (zero-truncation, `FreeLine.cutEquiv`). -/
theorem SymPoincare.exists_p_eq_id {A : InvCat} {M : ℤ} (P : SymPoincare A.inv M)
    (h : ∀ r, 0 ≤ r → r ≤ M → P.p.f r = 𝟙 _) :
    ∃ P' : SymPoincare A.inv M, P'.p = 𝟙 _ ∧ Nonempty (P.HomotopyIsometry P') := by
  refine ⟨P.transport (cutP_idem P.support P.p_idem) (supportedIn_cutP P.support)
    (cutEquiv P.support P.p_idem), ?_, ⟨P.transportIsometry _ _ _⟩⟩
  ext r : 1
  change (cutP P.support).f r = 𝟙 _
  by_cases hr : 0 ≤ r ∧ r ≤ M
  · rw [cutP_f, h r hr.1 hr.2, id_comp, cutOut_cutIn]
    rfl
  · exact (isZero_cutX hr).eq_of_src _ _

end FreeId

/-! ### Surjectivity of the transitions under `NegK` -/

/-- **Surjectivity of the line transitions from relation (R)** (the surjectivity half of
`DecBij`, lower L-theory module 22): under `NegK B`, for `k ≥ 1` and `N ≥ 1`, if relation (R)
holds over `C_ℤ^{∘k+1}(B)` in dimension `N` and the line complexes of free complexes over
`C_ℤ^{∘k}(B)` split into half-lines (`HalfLineSplit`), then
`tensorLine : Lconc (C_ℤ^{∘k} B) N → Lconc (C_ℤ^{∘k+1} B) (N + 1)` is surjective. -/
theorem NegK.tensorLine_surjective {B : InvCat} (hK : NegK B) {k : ℕ} (hk : 1 ≤ k) {N : ℤ}
    (hN : 1 ≤ N) (hR : UnionRel (B.czIter k).cz N) (hL : HalfLineSplit (B.czIter k) N) :
    Function.Surjective (Lconc.tensorLine (B.czIter k) N) := by
  intro x
  obtain ⟨P, hP, rfl⟩ := hK.exists_free_of_lconc (k := k + 1) (by omega) x
  obtain ⟨P', hP', ⟨e⟩⟩ := P.exists_p_eq_id hP
  rw [Lconc.cls_eq_of_isometry e]
  refine CZ.cls_mem_range_tensorLine hR hL (fun Q ↦ ?_) (by omega) P' hP'
  obtain ⟨Q₁, ⟨e₁⟩, hQ₁⟩ := hK.exists_isometric_free hk hN Q
  obtain ⟨Q₂, hQ₂, ⟨e₂⟩⟩ := Q₁.exists_p_eq_id hQ₁
  exact ⟨Q₂, hQ₂, ⟨e₁.trans e₂⟩⟩

/-- `NegK.tensorLine_surjective` with the line input in the task-statement form `LineCutIso`. -/
theorem NegK.tensorLine_surjective_of_lineCutIso {B : InvCat} (hK : NegK B) {k : ℕ} (hk : 1 ≤ k)
    {N : ℤ} (hN : 1 ≤ N) (hR : UnionRel (B.czIter k).cz N) (hL : LineCutIso (B.czIter k) N) :
    Function.Surjective (Lconc.tensorLine (B.czIter k) N) :=
  hK.tensorLine_surjective hk hN hR hL.halfLineSplit

/-- **Surjectivity of all line transitions in degrees `N ≥ 0`** (the surjectivity half of
`dec_bij` for every level `k ≥ 0`), from relation (R) and the Kar half-line splitting. -/
theorem NegK.tensorLine_surjective_kar {B : InvCat} (hK : NegK B) (k : ℕ) {N : ℤ} (hN : 0 ≤ N)
    (hR : UnionRel (B.czIter k).cz N) (hL : HalfLineSplitKar (B.czIter k) N) :
    Function.Surjective (Lconc.tensorLine (B.czIter k) N) := by
  intro x
  obtain ⟨P, hP, rfl⟩ := hK.exists_free_of_lconc (k := k + 1) (by omega) x
  obtain ⟨P', hP', ⟨e⟩⟩ := P.exists_p_eq_id hP
  rw [Lconc.cls_eq_of_isometry e]
  exact CZ.cls_mem_range_tensorLine_kar hR hL hN P' hP'

end

end HSFormal.LTheory
