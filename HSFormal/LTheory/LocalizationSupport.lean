import HSFormal.LTheory.Localization

/-!
# Localization for support categories: excision, exterior cuts, Mayer–Vietoris, Lemma 6.2

L-theory module M7, concrete part (manuscript §4, l.181–240, and §6, l.398–455).  `X` is a
compact space with an isometric action of `H`; supports are closed invariant sets.

* `exists_split`: an `(A ∪ B)`-supported object splits unitarily into its orbits nearer to `A`
  and those nearer to `B`; with `inIdeal_inter` this gives excision
  `𝒜_A/𝒜_{A∩B} ≃ 𝒜_{A∪B}/𝒜_B` (`isUnitaryEquiv_excision`, Lemma 2.2 inside `A ∪ B`), and for
  `A ∪ B = X` also `𝒜_A/𝒜_{A∩B} ≃ ℬ_B(X)` (`isUnitaryEquiv_exteriorExcision`).
* `isLES_support`: the localization sequence of `𝒜_Y ⊂ 𝒜_A`; `bdry41`, `isLES_bdry41`:
  Mayer–Vietoris (4.1) on `L(𝒜(X))` for a cover `X = A ∪ B` (`A ∩ B` may be empty);
  `relabelEquiv`: Lemma 2.4 on `L`.
* `projSep`: `L(𝒜_S) → L(𝒜_S/𝒜_Z) ≅ L(𝒜_Y)` for `S = Y ⊔ Z` disjoint.
* `cutBdry` (4.2): `L_{n+1}(ℬ_Z) → L_{n+1}(ℬ_{B∪Z}) ≅ L_{n+1}(𝒜_A/𝒜_{A∩(B∪Z)}) → L_n(𝒜_{A∩(B∪Z)})
  → L_n(𝒜_{A∩B})`: only the excision with `B' = B ∪ Z` is used, no (4.3); Lemma 4.1 for it is
  `cutBdry_cls`.
* `mvSystem`: Mayer–Vietoris for `L_n(𝒜_S(X))` over all pairs of closed invariant sets, with
  Lemma 4.1 `mvSystem_bdry_cls`.
* `tensorNatEnd`: `τ ⊗ −` commutes with inclusions and Mayer–Vietoris boundaries;
  `map_supportTensorHom_tau` is Lemma 6.1 on `L`, and `lemma_6_2` gives `(p - τ ⊗ −) ^ s = 0`
  on `L_n(𝒜_G(X))` for a cover by `s` trivializing pieces.

Comparisons between objects of different support subcategories are only made through the
abstract lemmas of `LTheory.Localization` (kernel reduction of the concrete support conditions
is expensive).
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive Filter Topology Metric HSFormal.MVNilpotence
  AsymptoticCategory AsymptoticObject
open scoped ENNReal Pointwise

noncomputable section

variable {H : Type} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  {π : ∀ i, G i →* H} {X : Type} [MulAction H X] [PseudoEMetricSpace X]

/-! ### Supports -/

section Support

variable (H) in
/-- `S` is closed and `H`-invariant. -/
def IsClosedInv (S : Set X) : Prop := IsClosed S ∧ ∀ h : H, h • S = S

theorem IsClosedInv.union {S T : Set X} (hS : IsClosedInv H S) (hT : IsClosedInv H T) :
    IsClosedInv H (S ∪ T) :=
  ⟨hS.1.union hT.1, fun h ↦ by rw [Set.smul_set_union, hS.2, hT.2]⟩

theorem IsClosedInv.inter {S T : Set X} (hS : IsClosedInv H S) (hT : IsClosedInv H T) :
    IsClosedInv H (S ∩ T) :=
  ⟨hS.1.inter hT.1, fun h ↦ by rw [Set.smul_set_inter, hS.2, hT.2]⟩

/-- The inclusion `𝒜_S ⊂ 𝒜_T` for `S ⊆ T`. -/
abbrev supportIncl {S T : Set X} (h : S ⊆ T) :
    (supportKaroubiFiltration π S).sub ⟶ (supportKaroubiFiltration π T).sub :=
  (asymptoticInvCat π X).subMap fun _ hP ↦ IsSupported.mono h hP

/-- Morphisms between objects of `𝒜_A` lying in `I_B` lie in `I_{A ∩ B}` (Lemma 2.2). -/
theorem inIdeal_inter [CompactSpace X] {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    {P Q : AsymptoticCategory π X} (hP : supportProperty A P) (hQ : supportProperty A Q)
    {f : P ⟶ Q} (h : InIdeal B f) : InIdeal (A ∩ B) f := by
  obtain ⟨f, rfl⟩ := exists_rep f
  rw [inIdeal_map_iff] at h ⊢
  exact tendsto_endpointDist_inter hA hB f.1
    (tendsto_zero_of_le (by simpa using hQ.max hP) (endpointDist_le_of_supported f.1)) h

theorem eq_zero_of_inIdeal_empty {P Q : AsymptoticCategory π X} {f : P ⟶ Q}
    (h : InIdeal (∅ : Set X) f) : f = 0 := by
  obtain ⟨W, hW, u, v, rfl⟩ := h
  have hz : IsZero W := isZero_of_isSupported_empty hW
  rw [hz.eq_of_tgt u 0, zero_comp]

/-- Splitting an `(A ∪ B)`-supported object into its orbits nearer to `A` and those nearer to
`B` (the unitary essential surjectivity in Lemma 2.2). -/
theorem exists_split [IsIsometricSMul H X] {A B : Set X} (hAinv : ∀ h : H, h • A = A)
    (hBinv : ∀ h : H, h • B = B) (P : AsymptoticCategory π X) (hP : supportProperty (A ∪ B) P) :
    ∃ (M : AsymptoticCategory π X) (_ : supportProperty A M) (u : M ⟶ P) (v : P ⟶ M),
      transpose u = v ∧ u ≫ v = 𝟙 M ∧ InIdeal B (v ≫ u - 𝟙 P) := by
  classical
  set N := P.as
  have hinv {S : Set X} (hS : ∀ h : H, h • S = S) (i : ℕ) (b : Fin (N.rank i) × G i) :
      infEDist (N.fullLabel i b) S = infEDist (N.label i b.1) S := by
    conv_lhs => rw [← hS (π i b.2)]
    exact infEDist_smul _ _ _
  have hmin (i : ℕ) (b : Fin (N.rank i) × G i) :
      min (infEDist (N.label i b.1) A) (infEDist (N.label i b.1) B) ≤ N.supportDist (A ∪ B) i := by
    rw [← infEDist_union, ← hinv (fun h ↦ by rw [Set.smul_set_union, hAinv, hBinv]) i b]
    exact infEDist_le_supportDist i b
  let Pr : ∀ i, Fin (N.rank i) → Prop := fun i k ↦
    infEDist (N.label i k) A ≤ infEDist (N.label i k) B
  refine ⟨functor.obj (N.restrict Pr), ?_, functor.map (N.restrictEmb Pr).incl,
    functor.map (N.restrictEmb Pr).proj, ?_, ?_, ?_⟩
  · refine tendsto_zero_of_le hP fun i ↦ iSup_le fun b ↦ ?_
    set k := (N.restrictEmb Pr).toFun i b.1
    have hk : Pr i k := (N.mem_range_restrictEmb Pr i k).mp ⟨b.1, rfl⟩
    have h := hmin i (k, b.2)
    rw [min_eq_left hk, ← hinv hAinv i (k, b.2)] at h
    exact h
  · rw [transpose_map, OrbitEmbedding.transpose_incl]
  · rw [← Functor.map_comp, OrbitEmbedding.incl_proj]
    rfl
  · rw [← Functor.map_comp, restrict_proj_incl]
    change InIdeal B (functor.map _ - functor.map (𝟙 N))
    rw [← Functor.map_sub, inIdeal_map_iff]
    refine tendsto_zero_of_le hP fun i ↦ endpointDist_le_iff.mpr fun c a hca ↦ ?_
    have hc : c = a ∧ ¬ Pr i a.1 := by
      by_cases hca' : c = a
      · subst hca'
        by_cases hPr : Pr i c.1
        · simp [hPr] at hca
        · exact ⟨rfl, hPr⟩
      · simp [Matrix.diagonal_apply_ne _ hca', Matrix.one_apply_ne hca'] at hca
    obtain ⟨rfl, hPr⟩ := hc
    have h := hmin i c
    rw [min_eq_right (not_le.mp hPr).le, ← hinv hBinv i c] at h
    exact ⟨h, h⟩

theorem isSupported_univ (P : AsymptoticCategory π X) : supportProperty Set.univ P :=
  tendsto_zero_of_forall_eq_zero fun _ ↦
    le_antisymm (iSup_le fun _ ↦ (infEDist_zero_of_mem (Set.mem_univ _)).le) bot_le

theorem isSupported_of_union_eq_univ {A B : Set X} (hcover : A ∪ B = Set.univ)
    (P : AsymptoticCategory π X) : supportProperty (A ∪ B) P :=
  hcover ▸ isSupported_univ P

end Support

/-! ### Excision (Lemma 2.2) and separated projections -/

section Excision

variable [CompactSpace X] [IsIsometricSMul H X] {A B : Set X}

variable (π A B) in
/-- The inclusion `(𝒜_{A∩B} ⊂ 𝒜_A) → (𝒜_B ⊂ 𝒜_{A∪B})`. -/
abbrev excisionHom :
    FiltrationHom (supportRestrictFiltration π (A ∩ B) A) (supportRestrictFiltration π B (A ∪ B)) :=
  (supportKaroubiFiltration π (A ∩ B)).restrictMap (supportKaroubiFiltration π B)
    (fun _ h ↦ IsSupported.mono Set.inter_subset_right h)
    (fun _ h ↦ IsSupported.mono Set.subset_union_left h)

/-- **Lemma 2.2 inside `A ∪ B`**: `𝒜_A/𝒜_{A∩B} → 𝒜_{A∪B}/𝒜_B` is a unitary equivalence. -/
theorem isUnitaryEquiv_excision (hA : IsClosedInv H A) (hB : IsClosedInv H B) :
    IsUnitaryEquiv (excisionHom π A B).quot :=
  KaroubiFiltration.isUnitaryEquiv_restrictMap _ _
    (fun _ h ↦ IsSupported.mono Set.inter_subset_left h)
    (fun _ h ↦ IsSupported.mono Set.subset_union_right h)
    (fun _ hP hQ hf ↦ inIdeal_inter hA.1 hB.1 hP hQ hf) fun Y hY ↦ exists_split hA.2 hB.2 Y hY

variable (π A B) in
/-- The inclusion `(𝒜_{A∩B} ⊂ 𝒜_A) → (𝒜_B ⊂ 𝒜(X))`. -/
abbrev exteriorExcisionHom :
    FiltrationHom (supportRestrictFiltration π (A ∩ B) A) (supportKaroubiFiltration π B) :=
  (supportKaroubiFiltration π (A ∩ B)).restrictTo (V := (supportKaroubiFiltration π A).U)
    (supportKaroubiFiltration π B) fun _ h ↦ IsSupported.mono Set.inter_subset_right h

/-- **Lemma 2.2** with duality: for `A ∪ B = X`, `𝒜_A/𝒜_{A∩B} → ℬ_B(X)` is a unitary
equivalence. -/
theorem isUnitaryEquiv_exteriorExcision (hA : IsClosedInv H A) (hB : IsClosedInv H B)
    (hcover : A ∪ B = Set.univ) : IsUnitaryEquiv (exteriorExcisionHom π A B).quot :=
  KaroubiFiltration.isUnitaryEquiv_restrictTo _ (fun _ h ↦ IsSupported.mono Set.inter_subset_left h)
    (fun _ hP hQ hf ↦ inIdeal_inter hA.1 hB.1 hP hQ hf)
    fun Y ↦ exists_split hA.2 hB.2 Y (isSupported_of_union_eq_univ hcover Y)

variable {S Y Z : Set X}

/-- For `S = Y ⊔ Z`, `𝒜_Y → 𝒜_S → 𝒜_S/𝒜_Z` is a unitary equivalence. -/
theorem isUnitaryEquiv_sep (hY : IsClosedInv H Y) (hZ : IsClosedInv H Z) (hYS : Y ⊆ S)
    (hZS : Z ⊆ S) (hS : S ⊆ Y ∪ Z) (hYZ : Disjoint Y Z) :
    IsUnitaryEquiv (supportIncl (π := π) hYS ≫ (supportRestrictFiltration π Z S).proj) :=
  KaroubiFiltration.isUnitaryEquiv_subMap_proj _ (fun _ h ↦ IsSupported.mono hZS h)
    (fun _ hP hQ hf ↦ eq_zero_of_inIdeal_empty (hYZ.inter_eq ▸ inIdeal_inter hY.1 hZ.1 hP hQ hf))
    fun P hP ↦ exists_split hY.2 hZ.2 P (IsSupported.mono hS hP)

/-- The separated projection `L(𝒜_S) → L(𝒜_S/𝒜_Z) ≅ L(𝒜_Y)` for `S = Y ⊔ Z`. -/
def projSep (𝕃 : LowerLTheory) (hY : IsClosedInv H Y) (hZ : IsClosedInv H Z) (hYS : Y ⊆ S)
    (hZS : Z ⊆ S) (hS : S ⊆ Y ∪ Z) (hYZ : Disjoint Y Z) (n : ℤ) :
    𝕃.L (supportKaroubiFiltration π S).sub n →+ 𝕃.L (supportKaroubiFiltration π Y).sub n :=
  𝕃.projSepOf _ (isUnitaryEquiv_sep hY hZ hYS hZS hS hYZ) n

theorem projSep_incl (𝕃 : LowerLTheory) (hY : IsClosedInv H Y) (hZ : IsClosedInv H Z)
    (hYS : Y ⊆ S) (hZS : Z ⊆ S) (hS : S ⊆ Y ∪ Z) (hYZ : Disjoint Y Z) (n : ℤ)
    (x : 𝕃.L (supportKaroubiFiltration π Y).sub n) :
    projSep 𝕃 hY hZ hYS hZS hS hYZ n (𝕃.map (supportIncl hYS) n x) = x :=
  𝕃.projSepOf_subMap _ _ n x

omit [CompactSpace X] [IsIsometricSMul H X] in
variable (π) in
/-- The localization sequence of `𝒜_Y ⊂ 𝒜_A` (Lemma 2.1, H1), on `L(𝒜_Y)` itself. -/
theorem isLES_support (𝕃 : LowerLTheory) (hYA : Y ⊆ A) :
    IsLES (fun n ↦ 𝕃.map (supportIncl (π := π) hYA) n)
      (fun n ↦ 𝕃.map (supportRestrictFiltration π Y A).proj n)
      (fun n ↦ (𝕃.map (supportRestrictSubIso (π := π) hYA).hom n).comp
        (𝕃.bdry (supportRestrictFiltration π Y A) n)) :=
  𝕃.isLES_iso _ _ _ (KaroubiFiltration.restrictSubIso_hom_comp _)

variable (π) in
/-- The Mayer–Vietoris boundary (4.1) `∂_{A,B} : L_{n+1}(𝒜(X)) → L_n(𝒜_{A∩B}(X))` for a closed
invariant cover `X = A ∪ B`. -/
def bdry41 (𝕃 : LowerLTheory) (hA : IsClosedInv H A) (hB : IsClosedInv H B)
    (hcover : A ∪ B = Set.univ) (n : ℤ) :
    𝕃.L (asymptoticInvCat π X) (n + 1) →+ 𝕃.L (supportKaroubiFiltration π (A ∩ B)).sub n :=
  𝕃.mvBdryOf (exteriorExcisionHom π A B) (isUnitaryEquiv_exteriorExcision hA hB hcover)
    (supportRestrictSubIso (π := π) (Set.inter_subset_left : A ∩ B ⊆ A)) n

/-- **Mayer–Vietoris (4.1)** for a closed invariant cover `X = A ∪ B` (Y = A ∩ B may be empty):
`L_n(𝒜_{A∩B}) → L_n(𝒜_A) × L_n(𝒜_B) → L_n(𝒜(X)) → L_{n-1}(𝒜_{A∩B})`. -/
theorem isLES_bdry41 (𝕃 : LowerLTheory) (hA : IsClosedInv H A) (hB : IsClosedInv H B)
    (hcover : A ∪ B = Set.univ) :
    IsLES (mvIn (fun n ↦ 𝕃.map (supportIncl (π := π) (Set.inter_subset_left : A ∩ B ⊆ A)) n)
        (fun n ↦ 𝕃.map (supportIncl (π := π) (Set.inter_subset_right : A ∩ B ⊆ B)) n))
      (mvOut (fun n ↦ 𝕃.map (supportKaroubiFiltration π B).incl n)
        (fun n ↦ 𝕃.map (supportKaroubiFiltration π A).incl n))
      (bdry41 π 𝕃 hA hB hcover) :=
  𝕃.isLES_mayerVietoris_restrictTo (F := supportKaroubiFiltration π (A ∩ B))
    (F' := supportKaroubiFiltration π B) (V := (supportKaroubiFiltration π A).U)
    (fun _ h ↦ IsSupported.mono Set.inter_subset_right h)
    (fun _ h ↦ IsSupported.mono Set.inter_subset_left h)
    (isUnitaryEquiv_exteriorExcision hA hB hcover)

variable (π) in
/-- **Lemma 2.4** on `L`: relabeling `L_n(𝒜_G(S)) ≅ L_n(𝒜_S(X))` for a closed invariant
nonempty `S`. -/
def relabelEquiv (𝕃 : LowerLTheory) (S : SubMulAction H X) (hS : IsClosed (S : Set X))
    [Nonempty S] (n : ℤ) :
    𝕃.L (asymptoticInvCat π S) n ≃+ 𝕃.L (supportKaroubiFiltration π (S : Set X)).sub n :=
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp hS.isCompact
  𝕃.equivOf (relabelInvCatHom_equiv (π := π) (j := ((↑) : S → X))
    (fun h y ↦ SubMulAction.val_smul h y) (fun _ _ ↦ rfl) Subtype.range_coe) n

end Excision

/-! ### The exterior cut (4.2) -/

/-- Boundary lifts to `𝒜_Y` and `𝒜_{Y'}` agree in `𝒜_{Y'}`. -/
theorem bdLift_map_supportRestrictSubIso {Y Y' A : Set X} (hYY' : Y ⊆ Y') (hYA : Y ⊆ A)
    (hY'A : Y' ⊆ A) {N : ℤ} (V : SymPair (supportKaroubiFiltration π A).sub.inv N)
    (hY : ∀ r, (supportRestrictFiltration π Y A).U (V.bd.C.X r)) :
    ((V.bdLift _ hY).map (supportRestrictSubIso (π := π) hYA).hom).map (supportIncl hYY') =
      (V.bdLift (supportRestrictFiltration π Y' A) fun r ↦ IsSupported.mono hYY' (hY r)).map
        (supportRestrictSubIso (π := π) hY'A).hom :=
  KaroubiFiltration.bdLift_map_restrictSubIso _ _ _ V hY

section Cut

variable [CompactSpace X] [IsIsometricSMul H X] {A B Z : Set X} (𝕃 : LowerLTheory)
  (hA : IsClosedInv H A) (hB : IsClosedInv H B) (hZ : IsClosedInv H Z)
  (hcover : A ∪ B = Set.univ) (hZA : Z ⊆ A) (hZB : Disjoint Z B)

/-- **The exterior cut (4.2)** `∂_{A,B} : L_{n+1}(ℬ_Z(X)) → L_n(𝒜_{A∩B}(X))` for `Z ⊆ A`,
`Z ∩ B = ∅`, `A ∪ B = X`: the quotient map to `ℬ_{B∪Z}`, inverse excision for the cover
`X = A ∪ (B ∪ Z)`, the localization boundary of `𝒜_{A∩(B∪Z)} ⊂ 𝒜_A`, and the separated
projection onto `𝒜_{A∩B}` (`A ∩ (B ∪ Z) = (A ∩ B) ⊔ Z`). -/
def cutBdry (n : ℤ) :
    𝕃.L (exteriorInvCat π Z) (n + 1) →+ 𝕃.L (supportKaroubiFiltration π (A ∩ B)).sub n :=
  (projSep 𝕃 (hA.inter hB) hZ (Set.inter_subset_inter_right A Set.subset_union_left)
    (Set.subset_inter hZA Set.subset_union_right)
    (fun _ ⟨hxA, hx⟩ ↦ hx.elim (fun hxB ↦ Or.inl ⟨hxA, hxB⟩) Or.inr)
    (hZB.symm.mono_left Set.inter_subset_right) n).comp
  ((𝕃.map (supportRestrictSubIso (π := π) (Set.inter_subset_left : A ∩ (B ∪ Z) ⊆ A)).hom n).comp
  (𝕃.cutOf (isUnitaryEquiv_exteriorExcision hA (hB.union hZ)
    (by rw [← Set.union_assoc, hcover, Set.univ_union]))
    (supportFiltrationHom (π := π) (Set.subset_union_right : Z ⊆ B ∪ Z)).quot n))

/-- **Lemma 4.1 for (4.2)**: if `Q` over `ℬ_Z` becomes, in `ℬ_{B∪Z}`, isometric to the image of a
pair `X` over `𝒜_A` with boundary in `𝒜_{A∩B}` (a union `X ∪_∂ X'` with `X'` on `B`), then
`∂_{A,B} [Q] = bsign · [∂X]`. -/
theorem cutBdry_cls {N : ℤ} (X : SymPair (supportKaroubiFiltration π A).sub.inv N)
    (hY : ∀ r, (supportRestrictFiltration π (A ∩ B) A).U (X.bd.C.X r))
    (Q : SymPoincare (exteriorInvCat π Z).inv (N + 1))
    (hQ : SymPoincare.Isometric ((X.map (exteriorExcisionHom π A (B ∪ Z)).toHom).toQuot
      (supportKaroubiFiltration π (B ∪ Z)) fun r ↦ IsSupported.mono
        (Set.inter_subset_right.trans Set.subset_union_left) (hY r))
      (Q.map (supportFiltrationHom (π := π) (Set.subset_union_right : Z ⊆ B ∪ Z)).quot)) :
    cutBdry 𝕃 hA hB hZ hcover hZA hZB N (𝕃.cls _ (N + 1) (Lconc.cls Q)) =
      𝕃.bsign N • 𝕃.cls _ N (Lconc.cls ((X.bdLift (supportRestrictFiltration π (A ∩ B) A) hY).map
        (supportRestrictSubIso (π := π) (Set.inter_subset_left : A ∩ B ⊆ A)).hom)) := by
  have hYS : A ∩ B ⊆ A ∩ (B ∪ Z) := Set.inter_subset_inter_right A Set.subset_union_left
  have hU₁ : ∀ r, (supportRestrictFiltration π (A ∩ (B ∪ Z)) A).U (X.bd.C.X r) :=
    fun r ↦ IsSupported.mono hYS (hY r)
  simp only [cutBdry, LowerLTheory.cutOf, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  erw [← 𝕃.cls_map, Lconc.map_cls,
    𝕃.bdry_symm_cls (exteriorExcisionHom π A (B ∪ Z)) _ (fun _ _ ↦ rfl) X hU₁ _ hQ,
    Units.smul_def, map_zsmul, map_zsmul, Units.smul_def, ← 𝕃.cls_map, Lconc.map_cls,
    ← bdLift_map_supportRestrictSubIso hYS Set.inter_subset_left Set.inter_subset_left X hY,
    ← Lconc.map_cls, 𝕃.cls_map, projSep_incl]

end Cut

/-! ### Mayer–Vietoris over closed invariant supports -/

section MV

variable [CompactSpace X] [IsIsometricSMul H X]

variable (H X) in
/-- The lattice of closed `H`-invariant subsets of `X`. -/
def ClosedInvariant : Type := {S : Set X // IsClosedInv H S}

instance : Lattice (ClosedInvariant H X) :=
  Subtype.lattice (fun _ _ hS hT ↦ hS.union hT) fun _ _ hS hT ↦ hS.inter hT

variable (π) in
/-- **Mayer–Vietoris** (§4, l.215) for the support categories `𝒜_S(X)` of all closed invariant
`S`: for every pair `A, B` (any intersection, any union), the localization sequences of
`𝒜_{A∩B} ⊂ 𝒜_A` and `𝒜_B ⊂ 𝒜_{A∪B}` and excision give
`L_n(𝒜_{A∩B}) → L_n(𝒜_A) × L_n(𝒜_B) → L_n(𝒜_{A∪B}) → L_{n-1}(𝒜_{A∩B})`. -/
def mvSystem (𝕃 : LowerLTheory) : MVSystem (ClosedInvariant H X) where
  L S n := 𝕃.L (supportKaroubiFiltration π S.1).sub n
  incl h n := 𝕃.map (supportIncl h) n
  bdry A B n := 𝕃.mvBdryOf (excisionHom π A.1 B.1) (isUnitaryEquiv_excision A.2 B.2)
    (supportRestrictSubIso (π := π) (Set.inter_subset_left : A.1 ∩ B.1 ⊆ A.1)) n
  isLES A B := 𝕃.isLES_mayerVietoris_restrict (F := supportKaroubiFiltration π (A.1 ∩ B.1))
    (F' := supportKaroubiFiltration π B.1) (V := (supportKaroubiFiltration π A.1).U)
    (V' := (supportKaroubiFiltration π (A.1 ∪ B.1)).U)
    (fun _ h ↦ IsSupported.mono Set.inter_subset_right h)
    (fun _ h ↦ IsSupported.mono Set.subset_union_left h)
    (fun _ h ↦ IsSupported.mono Set.inter_subset_left h)
    (fun _ h ↦ IsSupported.mono Set.subset_union_right h) (isUnitaryEquiv_excision A.2 B.2)

/-- **Lemma 4.1** for the Mayer–Vietoris boundary of `mvSystem`: `∂_{A,B} [V ∪_∂ V'] = bsign · [∂V]`
for a pair `V` over `𝒜_A` with boundary on `A ∩ B` (and `V'` on `B`). -/
theorem mvSystem_bdry_cls (𝕃 : LowerLTheory) (A B : ClosedInvariant H X) {N : ℤ}
    (V : SymPair (supportKaroubiFiltration π A.1).sub.inv N)
    (hY : ∀ r, (supportRestrictFiltration π (A.1 ∩ B.1) A.1).U (V.bd.C.X r))
    (P : SymPoincare (supportKaroubiFiltration π (A.1 ∪ B.1)).sub.inv (N + 1))
    (hP : SymPoincare.Isometric ((V.map (excisionHom π A.1 B.1).toHom).toQuot
      (supportRestrictFiltration π B.1 (A.1 ∪ B.1)) fun r ↦
        (excisionHom π A.1 B.1).map_mem _ (hY r))
      (P.map (supportRestrictFiltration π B.1 (A.1 ∪ B.1)).proj)) :
    (mvSystem π 𝕃).bdry A B N (𝕃.cls _ (N + 1) (Lconc.cls P)) =
      𝕃.bsign N • 𝕃.cls _ N (Lconc.cls ((V.bdLift _ hY).map
        (supportRestrictSubIso (π := π) (Set.inter_subset_left : A.1 ∩ B.1 ⊆ A.1)).hom)) :=
  𝕃.mvBdryOf_cls _ _ _ V hY P hP

end MV

/-! ### `τ ⊗ −` and Lemmas 6.1, 6.2 -/

section Tensor

variable [CompactSpace X] [IsIsometricSMul H X] {Q : Type*} [Fintype Q] (ρ : H →* Equiv.Perm Q)

variable (π X) in
/-- `ℚ[Q] ⊗ −` on `𝒜_G(X)` as an endomorphism of `InvCat`s. -/
def tensorHom : asymptoticInvCat π X ⟶ asymptoticInvCat π X :=
  tensorInv ρ

/-- `ℚ[Q] ⊗ −` on `𝒜_S(X)`. -/
abbrev supportTensorHom (S : Set X) :
    (supportKaroubiFiltration π S).sub ⟶ (supportKaroubiFiltration π S).sub :=
  (asymptoticInvCat π X).subRestrict (tensorHom π X ρ) fun _ h ↦ IsSupported.tensorObj h

variable (π) in
/-- `τ ⊗ −` commutes with the inclusions and Mayer–Vietoris boundaries (l.239), including the
excision equivalences. -/
def tensorNatEnd (𝕃 : LowerLTheory) : (mvSystem (H := H) (X := X) π 𝕃).NatEnd where
  app S n := 𝕃.map (supportTensorHom ρ S.1) n
  incl_comm {S T} h n x := by
    change 𝕃.map _ n (𝕃.map _ n x) = 𝕃.map _ n (𝕃.map _ n x)
    refine (𝕃.map_comp_apply (supportTensorHom ρ S.1) (supportIncl (π := π) h) n x).trans ?_
    refine Eq.trans ?_ (𝕃.map_comp_apply (supportIncl (π := π) h) (supportTensorHom ρ T.1) n x).symm
    exact congrArg (𝕃.map · n x) (InvCat.subRestrict_comp_subMap _ _ _ _)
  bdry_comm A B n x := 𝕃.mvBdryOf_restrict_comm (F := supportKaroubiFiltration π (A.1 ∩ B.1))
    (F' := supportKaroubiFiltration π B.1) (V := (supportKaroubiFiltration π A.1).U)
    (V' := (supportKaroubiFiltration π (A.1 ∪ B.1)).U) _ _ _ _ (tensorHom π X ρ)
    (fun _ h ↦ IsSupported.tensorObj h) (fun _ h ↦ IsSupported.tensorObj h)
    (fun _ h ↦ IsSupported.tensorObj h) (fun _ h ↦ IsSupported.tensorObj h) n x

variable [Fintype H]

/-- `ℚ[H]^{triv} ⊗ −` is the `|H|`-fold unitary sum of the identity. -/
def isFinSum_trivial (S : Set X) :
    InvCat.IsFinSum (fun _ : H ↦ 𝟙 (supportKaroubiFiltration π S).sub)
      (supportTensorHom (1 : H →* Equiv.Perm H) S) where
  inc q := sumIncl S q
  inc_star_self q P := (sumIncl_sumProj S q q P).trans (ite_eq_left rfl)
  inc_star_ne q q' h P := (sumIncl_sumProj S q q' P).trans (ite_eq_right h)
  total P := sum_sumProj_sumIncl S P

omit [CompactSpace X] [IsIsometricSMul H X] in
/-- **Lemma 6.1** on `L`: on a support category inside a compact subset of the lift of a
trivializing open set, `τ ⊗ −` acts on `L_n` as multiplication by `p = |H|`. -/
theorem map_supportTensorHom_tau [ContinuousConstSMul H X] (𝕃 : LowerLTheory) {W₀ K S : Set X}
    (hW₀ : IsOpen W₀) (hdisj : ∀ h : H, h ≠ 1 → Disjoint (h • W₀) W₀) (hK : IsCompact K)
    (hKW : K ⊆ ⋃ h : H, h • W₀) (hSK : S ⊆ K) (n : ℤ) :
    𝕃.map (supportTensorHom (π := π) (tauAction H) S) n =
      (Fintype.card H : AddMonoid.End (𝕃.L (supportKaroubiFiltration π S).sub n)) := by
  obtain ⟨e, he⟩ := exists_unitary_localTriv (π := π) hW₀ hdisj hK hKW hSK
  refine (𝕃.map_unitaryIso (Φ := supportTensorHom (tauAction H) S)
    (Ψ := supportTensorHom (1 : H →* Equiv.Perm H) S) ⟨e, he⟩ n).trans
    ((𝕃.map_finSum (isFinSum_trivial S) n).trans (AddMonoidHom.ext fun x ↦ ?_))
  erw [AddMonoid.End.natCast_apply]
  simp [𝕃.map_id]

omit [CompactSpace X] [IsIsometricSMul H X] [Fintype H] in
theorem pow_eq_zero_of_semiconj {M N : Type*} [AddCommGroup M] [AddCommGroup N] (E : M ≃+ N)
    {f : AddMonoid.End M} {g : AddMonoid.End N} (h : ∀ x, g (E x) = E (f x)) {s : ℕ}
    (hf : f ^ s = 0) : g ^ s = 0 := by
  have hsc : Function.Semiconj E f g := fun x ↦ (h x).symm
  refine AddMonoidHom.ext fun y ↦ ?_
  obtain ⟨x, rfl⟩ := E.surjective y
  have := hsc.iterate_right s x
  rw [← AddMonoid.End.coe_pow, ← AddMonoid.End.coe_pow, hf] at this
  exact this.symm.trans (map_zero E)

omit [CompactSpace X] [IsIsometricSMul H X] [Fintype H] in
theorem natSub_semiconj {M N : Type*} [AddCommGroup M] [AddCommGroup N] (E : M ≃+ N) (p : ℕ)
    {f : AddMonoid.End M} {g : AddMonoid.End N} (h : ∀ x, g (E x) = E (f x)) (x : M) :
    ((p : AddMonoid.End N) - g) (E x) = E (((p : AddMonoid.End M) - f) x) := by
  change p • E x - g (E x) = E (p • x - f x)
  rw [map_sub, map_nsmul, h]

variable (π) in
/-- **Lemma 6.2** (l.437–441) on `L`: if `X` is covered by `s` closed invariant pieces `T a`,
each in a compact subset of the lift `⋃ h, h • W₀ a` of a trivializing open set (the translates
of the open sheet `W₀ a` are disjoint), then `(p - τ ⊗ −) ^ s = 0` on `L_n(𝒜_G(X))`. -/
theorem lemma_6_2 [ContinuousConstSMul H X] (𝕃 : LowerLTheory) {s : ℕ} (hs : 0 < s)
    (T : Fin s → Set X) (hT : ∀ a, IsClosedInv H (T a)) (hcover : ⋃ a, T a = Set.univ)
    (W₀ : Fin s → Set X) (hW₀ : ∀ a, IsOpen (W₀ a))
    (hdisj : ∀ a, ∀ h : H, h ≠ 1 → Disjoint (h • W₀ a) (W₀ a))
    (hTW : ∀ a, T a ⊆ ⋃ h : H, h • W₀ a) (n : ℤ) :
    ((Fintype.card H : AddMonoid.End (𝕃.L (asymptoticInvCat π X) n)) -
      𝕃.mapEnd (tensorHom π X (tauAction H)) n) ^ s = 0 := by
  let top : ClosedInvariant H X := ⟨Set.univ, isClosed_univ, fun _ ↦ Set.smul_set_univ⟩
  have hX : IsLUB (Set.range fun a ↦ (⟨T a, hT a⟩ : ClosedInvariant H X)) top := by
    refine ⟨?_, fun U hU x _ ↦ ?_⟩
    · rintro _ ⟨a, rfl⟩
      exact Set.subset_univ (T a)
    · obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (hcover.symm ▸ Set.mem_univ x : x ∈ ⋃ a, T a)
      exact hU ⟨a, rfl⟩ ha
  have h := (tensorNatEnd π (tauAction H) 𝕃).natSub_pow_eq_zero (Fintype.card H) hs _ hX
    (fun a S hS n ↦ map_supportTensorHom_tau 𝕃 (hW₀ a) (hdisj a) (hT a).1.isCompact (hTW a) hS n) n
  refine pow_eq_zero_of_semiconj (𝕃.mapIso (InvCat.subTopIso _ isSupported_univ) n)
    (natSub_semiconj _ _ fun x ↦ ?_) h
  change 𝕃.map _ n (𝕃.map _ n x) = 𝕃.map _ n (𝕃.map _ n x)
  erw [LowerLTheory.map_comp_apply, LowerLTheory.map_comp_apply, ← InvCat.subTopIso_hom_comp]

end Tensor

end

end HSFormal.LTheory
