import HSFormal.InducedClassUniform

/-!
# The induced class `𝔡` and `Res 𝔡 = [C]` (manuscript §10, (10.1)–(10.4), Lemmas 5.1–5.2)

For `S : cd.SheetData π` (the hypotheses of (★)):

* `Ech`: the averaged projector `E = q⁻¹ ∑_{g ∈ G_i} A_g ⊗ R_{g⁻¹}` (10.2) on `Ind C`, a chain map
  of `ℬ_{G,Z}(T × Sⁿ)` (`Eg_comm`); `idemH : E² ≃ E` with homotopy `q⁻² ∑_{g,h} B̂_{g,h}` and
  `adjH : ΦE ≃ E^*Φ` with homotopy `q⁻¹ ∑_g V̂_g`.  Each equation holds sequencewise by
  `SheetData` (`R0_seq`, `R2_seq`, `R3_seq`); the worst-sequence lemma turns this into uniform
  endpoint estimates, so the shifted sums satisfy the equations (`extM_eq_of_sum_unif`).
* `proj`, `split`, `corner`: Lemma 5.1, the normalized corner `(D, q⁻¹ r Φ r^*)` (10.3) of a
  truncated Balmer–Schlichting splitting, with `q = (|G_i|)_i` (`qG`).
* `rowColumn`: the data (5.6)–(5.7) of Lemma 5.2 after `Res`, with row `u = q Res(E) ε` and column
  `v = η Res(E)` through the sheet `1` (`u_b = A_b`, `v_a = q⁻¹ A_{a⁻¹}`).  `uv`, `uE` and `conj`
  follow formally from `E² ≃ E`, `ΦE ≃ E^*Φ` and `A_1 = 1`; `vu` uses the blocks `q⁻¹ B̂_{s'⁻¹,s}`
  (`vuH`), which are `T`-controlled after forgetting `G`.
* `res_cls_corner`: `Res 𝔡 = [C]` (Lemma 5.2, (5.8)), hence `inducedClass : InducedClass` and the
  weak form `inducedClass_weak` (equality after `push`).
-/

noncomputable section

namespace HSFormal

open Filter Matrix CategoryTheory CategoryTheory.Limits Metric LTheory AsymptoticObject
  AsymptoticCategory Compression
open scoped ENNReal Topology Pointwise

theorem sum_sheet_prod_mul {Γ B A : Type*} [Group Γ] [Fintype Γ] (a : Γ → Matrix B A ℚ) :
    ∑ p : Γ × Γ, sheet (p.1 * p.2) (a (p.1 * p.2)) =
      (Fintype.card Γ : ℚ) • ∑ k, sheet k (a k) := by
  rw [Fintype.sum_prod_type]
  have h : ∀ g : Γ, ∑ h, sheet (g * h) (a (g * h)) = ∑ k, sheet k (a k) := fun g ↦
    Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun _ ↦ rfl
  simp only [h, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℚ]

section HomotopySucc

variable {V : Type*} [Category V] [Preadditive V]

/-- A homotopy on `ℤ`-indexed chain complexes from its components `k m : K_m ⟶ L_{m+1}`. -/
def homotopyOfSucc {K L : ChainComplex V ℤ} {f g : K ⟶ L} (k : ∀ m, K.X m ⟶ L.X (m + 1))
    (hk : ∀ m, f.f (m + 1) = K.d (m + 1) m ≫ k m + k (m + 1) ≫ L.d (m + 1 + 1) (m + 1) +
      g.f (m + 1)) : Homotopy f g where
  hom i j := if h : i + 1 = j then k i ≫ eqToHom (by rw [h]) else 0
  zero i j hij := dif_neg fun h ↦ hij h
  comm i := by
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by ring⟩
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel (m + 1) m from rfl),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (m + 1 + 1) (m + 1) from rfl), dif_pos rfl,
      dif_pos rfl]
    simpa only [eqToHom_refl, Category.comp_id] using hk m

end HomotopySucc

namespace ControlData

variable {p : ℕ} {cd : ControlData p} {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  {π : ∀ i, G i →* cd.Cp}

namespace SheetData

variable (S : cd.SheetData π)

/-- The scalar based module in degree `r`. -/
abbrev Mo (r : ℤ) : AsymptoticObject (scalarHom cd.Cp) cd.X := (S.toAction.C.C.X r).as.as

/-- Its free sheets `Ind`, (10.1). -/
abbrev Mg (r : ℤ) : AsymptoticObject π cd.X := cd.sheetObj π (S.toAction.C.C.X r)

/-- A controlled representative of the differential `d̂`. -/
def δ (r r' : ℤ) : S.Mo r ⟶ S.Mo r' := repM (S.toAction.C.C.d r r')

/-- A controlled representative of `φ̂`. -/
def Φr (r : ℤ) : S.Mo (cd.N - r) ⟶ S.Mo r := repM (S.toAction.C.φ.f r)

/-- The matrices of `d̂` on the orbit representatives. -/
abbrev Dm (r r' : ℤ) : ScalarFamily (S.Mg r) (S.Mg r') := scalarMatrix π (S.δ r r').1

/-- The matrices of `φ̂` on the orbit representatives. -/
abbrev Pm (r : ℤ) : ScalarFamily (S.Mg (cd.N - r)) (S.Mg r) := scalarMatrix π (S.Φr r).1

theorem CG_d (r r' : ℤ) :
    S.toAction.CG.d r r' = extM cd.Z ((AsymptoticObject.freeSheet π).map (S.δ r r')) := by
  change (cd.ind π).F.map (S.toAction.C.C.d r r') = _
  rw [← extM_repM (S.toAction.C.C.d r r')]
  rfl

theorem ind_d (r r' : ℤ) : (cd.ind π).F.map (S.toAction.C.C.d r r') =
    extM cd.Z ((AsymptoticObject.freeSheet π).map (S.δ r r')) :=
  S.CG_d r r'

theorem φG_f (r : ℤ) :
    S.toAction.φG.f r = extM cd.Z ((AsymptoticObject.freeSheet π).map (S.Φr r)) := by
  change (cd.ind π).F.map (S.toAction.C.φ.f r) = _
  rw [← extM_repM (S.toAction.C.φ.f r)]
  rfl

/-- The normalizing sequence `q = (|G_i|)_i`. -/
def qs (i : ℕ) : ℚ := (Fintype.card (G i) : ℚ)

theorem qs_ne_zero (i : ℕ) : qs (G := G) i ≠ 0 :=
  Nat.cast_ne_zero.mpr Fintype.card_ne_zero

/-- The averaged projector `E_r = q⁻¹ ∑_g A_g ⊗ R_{g⁻¹}` of (10.2) in degree `r`. -/
abbrev Eg (r : ℤ) : S.Mg r ⟶ S.Mg r := graphAverage (S.toAction.A r) (S.toAction.hA r)

theorem Eg_val (r : ℤ) (i : ℕ) :
    (S.Eg r).1 i = ∑ g, sheet g ((qs (G := G) i)⁻¹ • S.toAction.A r i g) :=
  rfl

/-- The residual of `A_g d = d A_g`. -/
def R0 (r r' : ℤ) : GraphFamily G (S.Mg r) (S.Mg r') :=
  fun i g ↦ S.Dm r r' i * S.toAction.A r i g - S.toAction.A r' i g * S.Dm r r' i

theorem R0_seq (r r' : ℤ) (g : ∀ i, G i) :
    Tendsto (fun i ↦ matEd cd.Z (S.R0 r r' i (g i)) ((S.Mg r).label i) ((S.Mg r').label i))
      atTop (𝓝 0) := by
  have h := S.toAction.comm g r r'
  rw [CG_d] at h
  simp only [ControlData.shift] at h
  erw [extM_comp, extM_comp] at h
  refine tendsto_matEd_of_extM_eq (fun h ↦ cd.smul_Z h) h g _ fun i ↦ ?_
  simp only [comp_val, freeSheet_map, sheetHom_val, Pi.one_apply, sheet_mul, one_mul, mul_one,
    ← sheet_sub, R0]

theorem Eg_comm (r r' : ℤ) :
    extM cd.Z (S.Eg r) ≫ S.toAction.CG.d r r' = S.toAction.CG.d r r' ≫ extM cd.Z (S.Eg r') := by
  erw [CG_d, extM_comp, extM_comp]
  refine extM_eq_of_sum_unif (fun h ↦ cd.smul_Z h) (fun _ ↦ id) (S.R0 r r')
    (fun i _ ↦ (qs (G := G) i)⁻¹) (tendsto_iSup_of_forall_seq (S.R0_seq r r')) fun i ↦ ?_
  simp only [comp_val, Eg_val, freeSheet_map, sheetHom_val, Pi.one_apply, Matrix.mul_sum,
    Matrix.sum_mul, sheet_mul, one_mul, mul_one, ← Finset.sum_sub_distrib, ← sheet_sub, R0,
    Matrix.mul_smul, Matrix.smul_mul, smul_sub, id]

/-- The averaged projector `E` of (10.2) as a chain map of `ℬ_{G,Z}(T × Sⁿ)`. -/
def Ech : S.toAction.CG ⟶ S.toAction.CG where
  f r := extM cd.Z (S.Eg r)
  comm' r r' _ := S.Eg_comm r r'

/-- The residual of `A_g A_h ≃ A_{gh}` with the homotopy `B̂_{g,h}`, in degree `m + 1`. -/
def R2 (m : ℤ) : GraphFamily (fun i ↦ G i × G i) (S.Mg (m + 1)) (S.Mg (m + 1)) :=
  fun i p ↦ S.toAction.A (m + 1) i p.1 * S.toAction.A (m + 1) i p.2 -
    (S.B m i p * S.Dm (m + 1) m i + S.Dm (m + 1 + 1) (m + 1) i * S.B (m + 1) i p +
      S.toAction.A (m + 1) i (p.1 * p.2))

theorem R2_seq (m : ℤ) (gh : ∀ i, G i × G i) :
    Tendsto (fun i ↦ matEd cd.Z (S.R2 m i (gh i)) ((S.Mg (m + 1)).label i)
      ((S.Mg (m + 1)).label i)) atTop (𝓝 0) := by
  obtain ⟨H, hH⟩ := S.mul (fun i ↦ (gh i).1) (fun i ↦ (gh i).2)
  have h := HomotopyIdempotent.comm_succ H m
  rw [hH m, hH (m + 1), CG_d, CG_d] at h
  dsimp only [HomologicalComplex.comp_f, SheetAction.act, ControlData.shift] at h
  erw [extM_comp, extM_comp, extM_comp] at h
  (try erw [extM_add] at h); (try erw [extM_add] at h)
  refine tendsto_matEd_of_extM_eq (fun h ↦ cd.smul_Z h) h (fun i ↦ (gh i).1 * (gh i).2) _
    fun i ↦ ?_
  erw [add_val, add_val, comp_val, comp_val]
  simp only [comp_val, add_val, freeSheet_map, sheetHom_val, Pi.one_apply, Pi.mul_apply,
    sheet_mul, one_mul, mul_one, ← sheet_add, ← sheet_sub, R2, Prod.mk.eta]
  erw [← sheet_add, ← sheet_sub]

theorem Eg_val_prod (r : ℤ) (i : ℕ) :
    (S.Eg r).1 i = ∑ p : G i × G i,
      sheet (p.1 * p.2) (((qs (G := G) i)⁻¹ ^ 2) • S.toAction.A r i (p.1 * p.2)) := by
  rw [sum_sheet_prod_mul (fun k ↦ ((qs (G := G) i)⁻¹ ^ 2) • S.toAction.A r i k), Eg_val,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← sheet_smul, smul_smul]
  congr 2
  have := qs_ne_zero (G := G) i
  rw [qs] at this ⊢
  field_simp

theorem Eg_mul_Eg (r : ℤ) (i : ℕ) :
    (S.Eg r).1 i * (S.Eg r).1 i = ∑ p : G i × G i, sheet (p.1 * p.2)
      (((qs (G := G) i)⁻¹ ^ 2) • (S.toAction.A r i p.1 * S.toAction.A r i p.2)) := by
  rw [Eg_val, Matrix.sum_mul, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  rw [Matrix.mul_sum]
  refine Finset.sum_congr rfl fun h _ ↦ ?_
  rw [sheet_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_two]

/-- The homotopy `q⁻² ∑_{g,h} B̂_{g,h} ⊗ R_{(gh)⁻¹}` of (10.2). -/
abbrev K1 (m : ℤ) : S.Mg m ⟶ S.Mg (m + 1) :=
  graphSum _ _ ((S.hB m).smul fun i _ ↦ (qs (G := G) i)⁻¹ ^ 2)

/-- (10.2): `E² ≃ E` in `ℬ_{G,Z}(T × Sⁿ)`. -/
def idemH : Homotopy (S.Ech ≫ S.Ech) S.Ech :=
  homotopyOfSucc (fun m ↦ extM cd.Z (S.K1 m)) fun m ↦ by
    rw [HomologicalComplex.comp_f, CG_d, CG_d]
    dsimp only [Ech]
    erw [extM_comp, extM_comp, extM_comp]
    (try erw [extM_add]); (try erw [extM_add])
    refine extM_eq_of_sum_unif (fun h ↦ cd.smul_Z h) (fun _ p ↦ p.1 * p.2) (S.R2 m)
      (fun i _ ↦ (qs (G := G) i)⁻¹ ^ 2) (tendsto_iSup_of_forall_seq (S.R2_seq m)) fun i ↦ ?_
    erw [comp_val, add_val, add_val, comp_val, comp_val, Eg_mul_Eg, Eg_val_prod, graphSum_val,
      graphSum_val, freeSheet_map, freeSheet_map, sheetHom_val, sheetHom_val, Matrix.sum_mul,
      Matrix.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    simp only [Pi.one_apply, sheet_mul, one_mul, mul_one, ← sheet_add, ← sheet_sub]
    erw [← sheet_add, ← sheet_sub]
    congr 1
    simp only [R2, smul_sub, smul_add, Matrix.smul_mul, Matrix.mul_smul]

/-- The sign `(-1)^{m+1}` of the dual differential. -/
def sg (m : ℤ) : ℚ := (((m + 1).negOnePow : ℤˣ) : ℤ)

/-- The residual of `A_g φ̂ ≃ φ̂ A_{g⁻¹}^*` with the homotopy `V̂_g`, in degree `m + 1`. -/
def R3 (m : ℤ) : GraphFamily G (S.Mg (cd.N - (m + 1))) (S.Mg (m + 1)) :=
  fun i g ↦ S.toAction.A (m + 1) i g * S.Pm (m + 1) i -
    (sg m • (S.V m i g * (S.Dm (cd.N - m) (cd.N - (m + 1)) i)ᵀ) +
      S.Dm (m + 1 + 1) (m + 1) i * S.V (m + 1) i g +
      S.Pm (m + 1) i * (S.toAction.A (cd.N - (m + 1)) i g⁻¹)ᵀ)

theorem R3_seq (m : ℤ) (g : ∀ i, G i) :
    Tendsto (fun i ↦ matEd cd.Z (S.R3 m i (g i)) ((S.Mg (cd.N - (m + 1))).label i)
      ((S.Mg (m + 1)).label i)) atTop (𝓝 0) := by
  obtain ⟨H, hH⟩ := S.adj g
  have h := HomotopyIdempotent.comm_succ H m
  rw [hH m, hH (m + 1)] at h
  simp only [HomologicalComplex.comp_f, CG_d, φG_f, dualComplex_d, dualHom_f] at h
  dsimp only [SheetAction.act, ControlData.shift] at h
  erw [extM_star, extM_star, extM_units_smul_rat, extM_comp, extM_comp, extM_comp, extM_comp] at h
  (try erw [extM_add] at h); (try erw [extM_add] at h)
  refine tendsto_matEd_of_extM_eq (fun h ↦ cd.smul_Z h) h g _ fun i ↦ ?_
  erw [add_val, add_val, comp_val, comp_val, comp_val, smul_val]
  simp only [comp_val, add_val, smul_val, freeSheet_map, sheetHom_val, Pi.one_apply,
    Pi.inv_apply, transpose_val, sheet_transpose, inv_one, inv_inv, sheet_mul, one_mul, mul_one,
    Matrix.mul_smul, ← sheet_smul, ← sheet_add, ← sheet_sub, R3, sg]
  erw [← sheet_add, ← sheet_sub]

/-- The homotopy `q⁻¹ ∑_g V̂_g ⊗ R_{g⁻¹}` of (10.2). -/
abbrev K2 (m : ℤ) : S.Mg (cd.N - m) ⟶ S.Mg (m + 1) :=
  graphSum _ _ ((S.hV m).smul fun i _ ↦ (qs (G := G) i)⁻¹)

theorem dual_part (m : ℤ) (i : ℕ) :
    sheet (1 : G i) (S.Pm (m + 1) i) * ((S.Eg (cd.N - (m + 1))).1 i)ᵀ = ∑ g, sheet g
      ((qs (G := G) i)⁻¹ • (S.Pm (m + 1) i * (S.toAction.A (cd.N - (m + 1)) i g⁻¹)ᵀ)) := by
  rw [Eg_val, Matrix.transpose_sum, Matrix.mul_sum]
  exact Fintype.sum_equiv (Equiv.inv (G i)) _ _ fun g ↦ by
    simp [sheet_transpose, sheet_mul, Matrix.transpose_smul, Matrix.mul_smul, sheet_smul]

/-- (10.2): `ΦE ≃ E^*Φ` in `ℬ_{G,Z}(T × Sⁿ)`. -/
def adjH :
    Homotopy (S.toAction.φG ≫ S.Ech) (dualHom (cd.BG π).inv cd.N S.Ech ≫ S.toAction.φG) :=
  homotopyOfSucc (fun m ↦ extM cd.Z (S.K2 m)) fun m ↦ by
    simp only [HomologicalComplex.comp_f, CG_d, φG_f, dualComplex_d, dualHom_f]
    dsimp only [Ech]
    erw [extM_star, extM_star, extM_units_smul_rat, extM_comp, extM_comp, extM_comp, extM_comp]
    (try erw [extM_add]); (try erw [extM_add])
    refine extM_eq_of_sum_unif (fun h ↦ cd.smul_Z h) (fun _ ↦ id) (S.R3 m)
      (fun i _ ↦ (qs (G := G) i)⁻¹) (tendsto_iSup_of_forall_seq (S.R3_seq m)) fun i ↦ ?_
    erw [comp_val, add_val, add_val, comp_val, comp_val, comp_val, smul_val, transpose_val,
      transpose_val, freeSheet_map, freeSheet_map, freeSheet_map, sheetHom_val, sheetHom_val,
      sheetHom_val, Pi.one_apply, dual_part, Eg_val, graphSum_val,
      graphSum_val, Matrix.sum_mul, Matrix.sum_mul, Matrix.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    simp only [sheet_transpose, inv_one, Matrix.mul_smul, sheet_mul, one_mul, mul_one, id,
      ← sheet_smul, ← sheet_add, ← sheet_sub]
    erw [← sheet_add, ← sheet_sub]
    congr 1
    simp only [R3, sg, smul_sub, smul_add, Matrix.smul_mul]
    rw [smul_comm ((qs (G := G) i)⁻¹)]

/-- `W = Ind(C, φ̂) = (C ⊗ ℚ[G], Φ)`, (10.1)–(10.2). -/
abbrev W : SymPoincare (cd.BG π).inv cd.N := S.toAction.C.map (cd.ind π)

theorem W_p : S.W.p = 𝟙 _ := by
  rw [SymPoincare.map_p, S.toAction.p_eq]
  exact CategoryTheory.Functor.map_id _ _

/-- The hypotheses of Lemma 5.1 for the averaged projector (10.2). -/
def proj : HomotopyProjector (cd.BG π).inv cd.N S.W where
  E := S.Ech
  E_kar := by rw [W_p, Category.id_comp, Category.comp_id]
  idem := S.idemH
  adj := S.adjH

/-- `q = (|G_i|)_i` on `ℬ_{G,Z}(T × Sⁿ)`. -/
abbrev qG (_ : cd.SheetData π) : CentralUnit (cd.BG π).inv :=
  seqUnit cd.Z (π := π) (qs (G := G)) qs_ne_zero

/-- `q = (|G_i|)_i` on `ℬ_{1,Z}(T × Sⁿ)`. -/
abbrev q1 (_ : cd.SheetData π) : CentralUnit cd.B1.inv :=
  seqUnit cd.Z (π := scalarHom cd.Cp) (qs (G := G)) qs_ne_zero

/-- A truncated Balmer–Schlichting splitting (5.4) of `E`. -/
def split : HomotopySplitting S.proj := S.proj.exists_splitting.choose

theorem split_supp : SupportedIn S.split.e 0 cd.N := S.proj.exists_splitting.choose_spec

/-- The normalized corner `(D, q⁻¹ r Φ r^*)` of (10.3). -/
def corner : SymPoincare (cd.BG π).inv cd.N :=
  HomotopySplitting.corner S.split S.qG S.split_supp

theorem hq (A : cd.BG π) : (cd.res π).F.map (S.qG.inv A) = S.q1.inv ((cd.res π).F.obj A) :=
  congrArg (extM cd.Z) (forgetHom_seqScalar _ _)

/-- `Res E`. -/
abbrev ResE : (cd.res π).mapC S.toAction.CG ⟶ (cd.res π).mapC S.toAction.CG :=
  (cd.res π).mapH S.Ech

/-- The inclusion of the sheet `1`, `η : C → Res Ind C`. -/
abbrev ηC := sheetInclC π (fun h ↦ cd.smul_Z h) S.toAction.C.C

/-- The projection onto the sheet `1`, `ε : Res Ind C → C`. -/
abbrev εC := sheetProjC π (fun h ↦ cd.smul_Z h) S.toAction.C.C

/-- The `(1, 1)` block of `E` is `q⁻¹ A_1 = q⁻¹` (manuscript (5.3) with `A_1 = 1`). -/
theorem ηC_ResE_εC : S.ηC ≫ S.ResE ≫ S.εC = S.q1.symm.chain S.toAction.C.C := by
  ext r
  change extM _ _ ≫ extM _ (forgetHom (S.Eg r)) ≫ extM _ _ = extM _ _
  rw [extM_comp, extM_comp]
  congr 1
  refine hom_ext fun i ↦ ?_
  dsimp only [Eg, graphAverage]
  rw [sheetIncl_graphSum_sheetProj, seqScalar_val]
  ext c b
  rw [Matrix.of_apply, Matrix.smul_apply, Matrix.smul_apply, id_val_scalar_apply,
    S.toAction.A_one]
  rfl

local notation "𝐊" => HomotopyCategory.quotient _ (ComplexShape.down ℤ)

/-- The homotopy of `vu ≃ E` (5.6): the block `(s', s)` is `q⁻¹ B̂_{s'⁻¹, s}`. -/
def Kvu (m : ℤ) : forgetObj (S.Mg m) ⟶ forgetObj (S.Mg (m + 1)) :=
  blockHom (S.B m) (S.hB m) fun i ↦ (qs (G := G) i)⁻¹

theorem Kvu_val (m : ℤ) (i : ℕ) :
    (S.Kvu m).1 i = blockMat (M := S.Mg m) (N := S.Mg (m + 1))
      (fun i s' s ↦ (qs (G := G) i)⁻¹ • S.B m i (s'⁻¹, s)) i :=
  rfl

/-- The row `u = q Res(E) ε` of (5.6), `u_b = A_b`. -/
abbrev u : (cd.res π).mapC S.toAction.CG ⟶ S.toAction.C.C :=
  S.ResE ≫ S.εC ≫ S.q1.chain S.toAction.C.C

/-- The column `v = η Res(E)` of (5.6), `v_a = q⁻¹ A_{a⁻¹}`. -/
abbrev v : S.toAction.C.C ⟶ (cd.res π).mapC S.toAction.CG := S.ηC ≫ S.ResE

theorem kResE_idem : 𝐊.map S.ResE ≫ 𝐊.map S.ResE = 𝐊.map S.ResE := by
  rw [← Functor.map_comp]
  exact HomotopyCategory.eq_of_homotopy _ _ (S.proj.map (cd.res π)).idem

theorem kResE_adj : 𝐊.map ((S.W.map (cd.res π)).φ ≫ S.ResE) =
    𝐊.map (dualHom cd.B1.inv cd.N S.ResE ≫ (S.W.map (cd.res π)).φ) :=
  HomotopyCategory.eq_of_homotopy _ _ (S.proj.map (cd.res π)).adj

theorem Wres_p : (S.W.map (cd.res π)).p = 𝟙 _ := by
  rw [SymPoincare.map_p, W_p]
  exact CategoryTheory.Functor.map_id _ _

theorem kdual_ResE :
    𝐊.map (dualHom cd.B1.inv cd.N S.ResE ≫ (S.W.map (cd.res π)).φ ≫ S.ResE) =
      𝐊.map ((S.W.map (cd.res π)).φ ≫ S.ResE) := by
  calc 𝐊.map (dualHom cd.B1.inv cd.N S.ResE ≫ (S.W.map (cd.res π)).φ ≫ S.ResE)
      = 𝐊.map (dualHom cd.B1.inv cd.N S.ResE) ≫
          𝐊.map ((S.W.map (cd.res π)).φ ≫ S.ResE) := Functor.map_comp _ _ _
    _ = 𝐊.map (dualHom cd.B1.inv cd.N S.ResE) ≫
          𝐊.map (dualHom cd.B1.inv cd.N S.ResE ≫ (S.W.map (cd.res π)).φ) := by rw [kResE_adj]
    _ = 𝐊.map (dualHom cd.B1.inv cd.N (S.ResE ≫ S.ResE)) ≫ 𝐊.map (S.W.map (cd.res π)).φ := by
        rw [dualHom_comp]; simp only [Functor.map_comp, Category.assoc]
    _ = 𝐊.map (dualHom cd.B1.inv cd.N S.ResE) ≫ 𝐊.map (S.W.map (cd.res π)).φ := by
        rw [kmap_dualHom, kmap_dualHom, Functor.map_comp, kResE_idem]
    _ = 𝐊.map ((S.W.map (cd.res π)).φ ≫ S.ResE) := by rw [← Functor.map_comp, kResE_adj]

theorem vu_residual (m : ℤ) (i : ℕ) :
    (forgetHom (S.Eg (m + 1)) ≫ sheetProj π (S.Mo (m + 1)) ≫ seqScalar (qs (G := G)) (S.Mo (m + 1)) ≫
        sheetIncl π (S.Mo (m + 1)) ≫ forgetHom (S.Eg (m + 1))).1 i -
      ((forgetHom ((AsymptoticObject.freeSheet π).map (S.δ (m + 1) m)) ≫ S.Kvu m :
          forgetObj (S.Mg (m + 1)) ⟶ forgetObj (S.Mg (m + 1))) +
        (S.Kvu (m + 1) ≫ forgetHom ((AsymptoticObject.freeSheet π).map (S.δ (m + 1 + 1) (m + 1))) :
          forgetObj (S.Mg (m + 1)) ⟶ forgetObj (S.Mg (m + 1))) +
        forgetHom (S.Eg (m + 1))).1 i =
      blockMat (M := S.Mg (m + 1)) (N := S.Mg (m + 1))
        (fun i s' s ↦ (qs (G := G) i)⁻¹ • S.R2 m i (s'⁻¹, s)) i := by
  dsimp only [Eg, graphAverage]
  rw [forgetHom_sheetOne_comp, add_val, add_val, comp_val, comp_val, Kvu_val, Kvu_val,
    freeSheet_map, freeSheet_map, blockMat_mul_freeSheet, freeSheet_mul_blockMat,
    forgetHom_graphSum, blockMat_add, blockMat_add, blockMat_sub]
  congr 1
  funext i s' s
  have hq := qs_ne_zero (G := G) i
  simp only [R2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_sub, smul_add]
  simp only [qs] at hq ⊢
  rw [show (Fintype.card (G i) : ℚ) * ((Fintype.card (G i) : ℚ)⁻¹ * (Fintype.card (G i) : ℚ)⁻¹) =
    (Fintype.card (G i) : ℚ)⁻¹ by field_simp]

theorem vu_eq (m : ℤ) :
    extM cd.Z (forgetHom (S.Eg (m + 1)) ≫ sheetProj π (S.Mo (m + 1)) ≫
        seqScalar (qs (G := G)) (S.Mo (m + 1)) ≫ sheetIncl π (S.Mo (m + 1)) ≫
          forgetHom (S.Eg (m + 1))) =
      extM cd.Z ((forgetHom ((AsymptoticObject.freeSheet π).map (S.δ (m + 1) m)) ≫ S.Kvu m :
          forgetObj (S.Mg (m + 1)) ⟶ forgetObj (S.Mg (m + 1))) +
        (S.Kvu (m + 1) ≫ forgetHom ((AsymptoticObject.freeSheet π).map (S.δ (m + 1 + 1) (m + 1))) :
          forgetObj (S.Mg (m + 1)) ⟶ forgetObj (S.Mg (m + 1))) +
        forgetHom (S.Eg (m + 1))) := by
  refine extM_eq_of_forget_entries (r := fun i ↦ ⨆ p, matEd cd.Z (S.R2 m i p)
    ((S.Mg (m + 1)).label i) ((S.Mg (m + 1)).label i)) (tendsto_iSup_of_forall_seq (S.R2_seq m))
    fun i x y hxy ↦ ?_
  rw [S.vu_residual m i, blockMat_apply, Matrix.smul_apply, smul_eq_mul] at hxy
  have h := infEDist_le_matEd (Z := cd.Z) (source := (S.Mg (m + 1)).label i)
    (target := (S.Mg (m + 1)).label i) (right_ne_zero_of_mul hxy)
  simp only [fullLabel, infEDist_smul_of_invariant (fun h ↦ cd.smul_Z h)]
  exact ⟨h.1.trans (le_iSup_of_le _ le_rfl), h.2.trans (le_iSup_of_le _ le_rfl)⟩

theorem res_map_extM {M N : AsymptoticObject π cd.X} (f : M ⟶ N) :
    (cd.res π).F.map (extM cd.Z f) = extM cd.Z (forgetHom f) :=
  rfl

/-- `vu ≃ E` (5.6) after forgetting the action, with the homotopy `Kvu`. -/
def vuH : Homotopy (S.u ≫ S.v) (S.proj.map (cd.res π)).E :=
  homotopyOfSucc (fun m ↦ extM cd.Z (S.Kvu m)) fun m ↦ by
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_obj_d,
      Functor.mapHomologicalComplex_map_f, HomotopyProjector.map_E, sheetInclC_f, sheetProjC_f,
      CentralUnit.chain_f, seqUnit_hom]
    dsimp only [proj, Ech, sheetInclE, sheetProjE]
    erw [ind_d, ind_d, res_map_extM, res_map_extM, res_map_extM, sheetProjC_f, sheetInclC_f]
    dsimp only [sheetInclE, sheetProjE]
    repeat erw [extM_comp]
    (try erw [extM_add]); (try erw [extM_add])
    refine Eq.trans ?_ (S.vu_eq m)
    congr 1
    erw [Category.assoc, Category.assoc] <;> rfl

/-- **Lemma 5.2, (5.6)–(5.7)** for the averaged projector, after forgetting the action. -/
def rowColumn : RowColumn cd.B1.inv cd.N (S.proj.map (cd.res π)) S.toAction.C S.q1 where
  u := S.u
  v := S.v
  u_kar := by rw [Wres_p, S.toAction.p_eq, Category.id_comp, Category.comp_id]
  v_kar := by rw [Wres_p, S.toAction.p_eq, Category.id_comp, Category.comp_id]
  uv := HomotopyCategory.homotopyOfEq _ _ (by
    rw [S.toAction.p_eq]
    calc 𝐊.map (S.v ≫ S.u) = 𝐊.map S.ηC ≫ (𝐊.map S.ResE ≫ 𝐊.map S.ResE) ≫
          𝐊.map (S.εC ≫ S.q1.chain S.toAction.C.C) := by
          simp only [Functor.map_comp, Category.assoc]
      _ = 𝐊.map ((S.ηC ≫ S.ResE ≫ S.εC) ≫ S.q1.chain S.toAction.C.C) := by
          erw [kResE_idem]; simp only [Functor.map_comp, Category.assoc]
      _ = 𝐊.map (𝟙 _) := by rw [ηC_ResE_εC, CentralUnit.symm_chain_chain])
  vu := S.vuH
  uE := HomotopyCategory.homotopyOfEq _ _ (by
    calc 𝐊.map (S.ResE ≫ S.u) = (𝐊.map S.ResE ≫ 𝐊.map S.ResE) ≫
          𝐊.map (S.εC ≫ S.q1.chain S.toAction.C.C) := by
          simp only [Functor.map_comp, Category.assoc]
      _ = 𝐊.map S.u := by rw [kResE_idem]; simp only [Functor.map_comp])
  conj := HomotopyCategory.homotopyOfEq _ _ (by
    have hε := dualHom_sheetProjC_comp (π := π) (hZ := fun h ↦ cd.smul_Z h) (N := cd.N)
      S.toAction.C.φ
    calc 𝐊.map (dualHom cd.B1.inv cd.N S.u ≫ (S.W.map (cd.res π)).φ ≫ S.u)
        = 𝐊.map (S.q1.chain _ ≫ dualHom cd.B1.inv cd.N S.εC) ≫
            𝐊.map (dualHom cd.B1.inv cd.N S.ResE ≫ (S.W.map (cd.res π)).φ ≫ S.ResE) ≫
            𝐊.map (S.εC ≫ S.q1.chain S.toAction.C.C) := by
          simp only [u, dualHom_comp, CentralUnit.dualHom_chain, Functor.map_comp,
            Category.assoc]
      _ = 𝐊.map (S.q1.chain _ ≫ (dualHom cd.B1.inv cd.N S.εC ≫ (S.W.map (cd.res π)).φ) ≫
            S.ResE ≫ S.εC ≫ S.q1.chain S.toAction.C.C) := by
          erw [kdual_ResE]; simp only [Functor.map_comp, Category.assoc]
      _ = 𝐊.map (S.q1.chain _ ≫ S.toAction.C.φ ≫ (S.ηC ≫ S.ResE ≫ S.εC) ≫
            S.q1.chain S.toAction.C.C) := by
          erw [hε]; simp only [Category.assoc]
      _ = 𝐊.map (S.toAction.C.φ ≫ S.q1.chain S.toAction.C.C) := by
          rw [ηC_ResE_εC, CentralUnit.symm_chain_chain, Category.comp_id,
            CentralUnit.chain_comp])

/-- **(10.3)–(10.4)**: `Res 𝔡 = [C]` already over `T × Sⁿ`, by Lemma 5.2 (5.8). -/
theorem res_cls_corner : Lconc.map (cd.res π) (Lconc.cls S.corner) = Lconc.cls S.toAction.C := by
  rw [Lconc.map_cls, corner, S.split.corner_map (cd.res π) S.qG S.q1 S.hq S.split_supp]
  exact Lconc.cls_eq_of_isometry (S.rowColumn.lemma_5_2 _ _)

/-- The corner class `𝔡 ∈ Lconc_N(ℬ_{G,Z}(T × Sⁿ))` of (10.3) with `Res 𝔡 = [C]`. -/
theorem exists_induced :
    ∃ 𝔡 : Lconc (cd.BG π) cd.N, Lconc.map (cd.res π) 𝔡 = Lconc.cls S.toAction.C :=
  ⟨_, S.res_cls_corner⟩

end SheetData

end ControlData

/-- **S4–S6** (Lemmas 5.1–5.2, (10.1)–(10.4)): the step `InducedClass` of `Assembly`. -/
theorem inducedClass : InducedClass :=
  fun _ _ _ _ S ↦ S.exists_induced

/-- The weak form of `InducedClass` used by (★): equality after forgetting `T` as well. -/
theorem inducedClass_weak (p : ℕ) [Fact p.Prime] (cd : ControlData p) (Γ : TailGroups p cd.Cp)
    (S : cd.SheetData Γ.π) :
    ∃ 𝔡 : Lconc (cd.BG Γ.π) cd.N,
      Lconc.map (cd.res Γ.π ≫ cd.push) 𝔡 = Lconc.map cd.push (Lconc.cls S.toAction.C) := by
  obtain ⟨𝔡, h⟩ := S.exists_induced
  exact ⟨𝔡, by rw [Lconc.map_comp, AddMonoidHom.comp_apply, h]⟩

end HSFormal
