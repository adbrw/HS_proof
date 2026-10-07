import HSFormal.Cubical.CubeExt
import HSFormal.Cubical.EndClass

/-!
# The last stage of the cube flag: `∂Φ₁ ⊗ CPcell` and the positive end point

The level `∂K_1 = ∂I ⊗ CPcell` of the flag is the sum of the constant complexes `pt ⊗ CPcell`
at the two end points; its boundary structure is `φ_CP` at the positive end
(`defect_cubeTop_one_last`).  In `𝒜_{Y₀}/𝒜_Q` the inclusion of the positive end is an
isometry (`SymPoincare.isometric_proj_of_split`), so the projection `projSep` to `𝒜_P` of the
class of `∂K_1` is the class of the constant sequence `pt ⊗ CPcell` (`cpConstDuality`), whose
`σ_tail` is a sign tail (`EndClass`).
-/

noncomputable section

namespace HSFormal.LTheory

open CategoryTheory HSFormal.Compression

/-- **Isometry in a quotient from a split inclusion**: `t : P → Q`, `i : Q → P` with `i t = 1`,
`1 - t i` through `U` and `t^* φ_P t = φ_Q` give `P ≃ Q` in `A/U`. -/
theorem SymPoincare.isometric_proj_of_split {A : InvCat} (F : KaroubiFiltration A) {N : ℤ}
    (P Q : SymPoincare A.inv N) (hP : P.p = 𝟙 _) (hQ : Q.p = 𝟙 _) (t : P.C ⟶ Q.C)
    (i : Q.C ⟶ P.C) (hit : i ≫ t = 𝟙 _) (hc : ∀ r, FactorsThrough F.U (𝟙 _ - t.f r ≫ i.f r))
    (hφ : dualHom A.inv N t ≫ P.φ ≫ t = Q.φ) :
    SymPoincare.Isometric (P.map F.proj) (Q.map F.proj) := by
  refine ⟨⟨F.proj.mapH t, F.proj.mapH i, ?_, ?_, Homotopy.ofEq ?_, Homotopy.ofEq ?_,
    Homotopy.ofEq ?_⟩⟩
  · simp [hP, hQ]
  · simp [hP, hQ]
  · ext r
    simp only [SymPoincare.map_p, hP, InvFunctor.mapH, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f, HomologicalComplex.id_f]
    rw [← CategoryTheory.Functor.map_comp]
    exact ((F.proj_map_eq_iff _ _).mpr (by
      have := (hc r).neg
      rwa [neg_sub] at this))
  · rw [SymPoincare.map_p, hQ, InvFunctor.mapH, InvFunctor.mapH, ← CategoryTheory.Functor.map_comp,
      hit]
  · ext r
    have h := congrArg (fun g ↦ F.proj.F.map (HomologicalComplex.Hom.f g r)) hφ
    simp only [HomologicalComplex.comp_f, CategoryTheory.Functor.map_comp] at h
    refine Eq.trans ?_ h
    change F.quot.inv.star (F.proj.F.map (t.f (N - r))) ≫ F.proj.F.map (P.φ.f r) ≫
      F.proj.F.map (t.f r) = _
    rw [← F.proj.map_star]
    rfl

theorem SymPoincare.lift_p_eq_id {A : InvCat} {U : ObjectProperty A} [IsAdditiveSub U] {N : ℤ}
    (P : SymPoincare A.inv N) (h : ∀ r, U (P.C.X r)) (hp : P.p = 𝟙 _) : (P.lift h).p = 𝟙 _ := by
  ext r
  change P.p.f r = 𝟙 _
  rw [hp]
  rfl

end HSFormal.LTheory

namespace HSFormal.Cubical.BasedComplex

open Filter Matrix Metric Topology HSFormal.RoundSphere HSFormal.LTheory CategoryTheory HSFormal.Compression
open scoped ENNReal

/-! ### The cells of `∂K_1 = ∂I ⊗ CPcell` -/

section Bdry1

variable (m : ℕ)

/-- The cells of `∂K_1` have even degree (a vertex times a cell of `CPcell`). -/
theorem bdry1_deg (y : (cubeCP.bdry m 1).X) : (cubeCP.bdry m 1).deg y = 2 * (y.1.2 : ℕ) := by
  obtain ⟨⟨⟨x₀, ⟨⟩⟩, c⟩, ⟨t, ht⟩⟩ := y
  obtain rfl : t = 0 := Subsingleton.elim _ _
  rcases ht with h | h <;>
  · change x₀ = _ at h
    subst h
    change 0 + (cube (m + 1) 0).deg () + 2 * (c : ℕ) = 2 * (c : ℕ)
    rw [show (cube (m + 1) 0).deg () = 0 from rfl]
    simp

theorem bdry1_d : (cubeCP.bdry m 1).d = 0 := by
  ext y y'
  by_contra h
  have := (cubeCP.bdry m 1).d_deg y y' h
  rw [bdry1_deg, bdry1_deg] at this
  omega

/-- The cell `v₊ ⊗ c` of the positive end. -/
def bdry1Pt (c : CPcell.X) : (cubeCP.bdry m 1).X :=
  ⟨((.inl (Fin.last (m + 1)), ()), c), ⟨0, Or.inr rfl⟩⟩

theorem bdry1Pt_inj {c c' : CPcell.X} (h : bdry1Pt m c = bdry1Pt m c') : c = c' :=
  (Prod.mk.inj (congrArg Subtype.val h)).2

/-- The inclusion `pt ⊗ CPcell → ∂K_1` of the positive end. -/
def bdry1Incl : Hom CPcell (cubeCP.bdry m 1) where
  f := Matrix.of fun y c ↦ if y = bdry1Pt m c then 1 else 0
  deg0 y c h := by
    have hy : y = bdry1Pt m c := by by_contra h'; exact h (by simp [h'])
    subst hy
    rw [bdry1_deg]
    simp [bdry1Pt]
  comm := by rw [bdry1_d]; simp

/-- The projection `∂K_1 → pt ⊗ CPcell` onto the positive end. -/
def bdry1Proj : Hom (cubeCP.bdry m 1) CPcell where
  f := Matrix.of fun c y ↦ if y = bdry1Pt m c then 1 else 0
  deg0 c y h := by
    have hy : y = bdry1Pt m c := by by_contra h'; exact h (by simp [h'])
    subst hy
    rw [bdry1_deg]
    simp [bdry1Pt]
  comm := by rw [bdry1_d]; simp

theorem bdry1Proj_mul_incl : (bdry1Proj m).f * (bdry1Incl m).f = 1 := by
  ext c c'
  rw [mul_apply, Finset.sum_eq_single (bdry1Pt m c)]
  · by_cases h : c = c'
    · subst h; simp [bdry1Proj, bdry1Incl]
    · have hne : bdry1Pt m c ≠ bdry1Pt m c' := fun h' ↦ h (bdry1Pt_inj m h')
      simp [bdry1Proj, bdry1Incl, one_apply_ne h, hne]
  · intro y _ hy
    simp [bdry1Proj, hy]
  · simp

/-- `1 - i t` is the projection onto the cells off the positive end. -/
theorem one_sub_incl_mul_proj_apply (y y' : (cubeCP.bdry m 1).X) :
    ((1 : Matrix (cubeCP.bdry m 1).X (cubeCP.bdry m 1).X ℚ) - (bdry1Incl m).f * (bdry1Proj m).f) y y' =
      if y = y' ∧ y.1.1.1 ≠ .inl (Fin.last (m + 1)) then 1 else 0 := by
  rw [Matrix.sub_apply, mul_apply]
  by_cases hP : y.1.1.1 = .inl (Fin.last (m + 1))
  · have hy : y = bdry1Pt m y.1.2 := by
      obtain ⟨⟨⟨x₀, ⟨⟩⟩, c⟩, hb⟩ := y
      change x₀ = _ at hP
      subst hP
      rfl
    rw [Finset.sum_eq_single y.1.2]
    · simp only [bdry1Incl, bdry1Proj, of_apply]
      by_cases hyy : y = y'
      · subst hyy
        simp [hP, ← hy]
      · simp [one_apply_ne hyy, hyy, ← hy, Ne.symm hyy]
    · intro c _ hc
      simp only [bdry1Incl, of_apply]
      rw [if_neg (fun h ↦ hc ((bdry1Pt_inj m (hy.symm.trans h)).symm)), zero_mul]
    · simp
  · rw [Finset.sum_eq_zero fun c _ ↦ by
      simp only [bdry1Incl, of_apply]
      rw [if_neg (fun h ↦ hP (by rw [h]; rfl)), zero_mul]]
    by_cases hyy : y = y'
    · subst hyy; simp [hP]
    · simp [one_apply_ne hyy, hyy]

/-- The boundary structure of `∂K_1` at the positive end is `φ_CP`. -/
theorem bdry1_bdHom_pt (c c' : CPcell.X) :
    defect ((cube (m + 1) 1).tensor CPcell) (1 + 3 + 1) (cubeTop_dimLE m 1) (cubeTop m 1)
      (bdry1Pt m c).1 (bdry1Pt m c').1 = CPcell.φ.f c c' :=
  defect_cubeTop_one_last m c c'

theorem bdry1_neg_end {y : (cubeCP.bdry m 1).X} (h : y.1.1.1 ≠ .inl (Fin.last (m + 1))) :
    y.1.1 = (.inl 0, ()) := by
  obtain ⟨⟨⟨x₀, ⟨⟩⟩, c⟩, ⟨t, ht⟩⟩ := y
  obtain rfl : t = 0 := Subsingleton.elim _ _
  rcases ht with h' | h'
  · change x₀ = _ at h'
    subst h'
    rfl
  · exact absurd h' h

theorem bdry1Proj_conj (M : Matrix (cubeCP.bdry m 1).X (cubeCP.bdry m 1).X ℚ) (c c' : CPcell.X) :
    ((bdry1Proj m).f * M * ((bdry1Proj m).f)ᵀ) c c' = M (bdry1Pt m c) (bdry1Pt m c') := by
  rw [mul_apply, Finset.sum_eq_single (bdry1Pt m c')]
  · rw [transpose_apply, mul_apply, Finset.sum_eq_single (bdry1Pt m c)]
    · simp [bdry1Proj]
    · intro y _ hy; simp [bdry1Proj, hy]
    · simp
  · intro y _ hy; simp [bdry1Proj, hy]
  · simp

end Bdry1

namespace CubeGeom

open ControlledSeq

variable {r : ℝ} (hr : 0 < r) (n : ℕ) (h1 : 1 ≤ n)

variable (r) in
/-- The labels `ℓ_i` of the positive end point `v₊` of the last edge. -/
def endLabel (i : ℕ) : RoundSphere n := cubeLabel r (germMesh i) n 1 (.inl (Fin.last _), ())

/-- The inclusion of the positive end `pt ⊗ CPcell → ∂K_1`, controlled (propagation `0`). -/
def endIncl : ControlledSeq.Hom (cpConst (endLabel r n)) (facePair hr n 1 h1).Bd where
  f i := bdry1Incl (mBox r (germMesh i))
  tendsto := tendsto_zero_of_forall_eq_zero fun i ↦ le_antisymm (prop_le_iff.mpr fun y c h ↦ by
    have hy : y = bdry1Pt _ c := by
      by_contra h'
      exact h (if_neg h')
    subst hy
    change edist (endLabel r n i) (endLabel r n i) ≤ 0
    rw [edist_self]) bot_le

/-- The projection `∂K_1 → pt ⊗ CPcell` onto the positive end, controlled. -/
def endProj : ControlledSeq.Hom (facePair hr n 1 h1).Bd (cpConst (endLabel r n)) where
  f i := bdry1Proj (mBox r (germMesh i))
  tendsto := tendsto_zero_of_forall_eq_zero fun i ↦ le_antisymm (prop_le_iff.mpr fun c y h ↦ by
    have hy : y = bdry1Pt _ c := by
      by_contra h'
      exact h (if_neg h')
    subst hy
    change edist (endLabel r n i) (endLabel r n i) ≤ 0
    rw [edist_self]) bot_le

theorem endProj_comp_incl :
    (endProj hr n h1).comp (endIncl hr n h1) = ControlledSeq.Hom.id _ :=
  Hom.ext_f fun _ ↦ BasedComplex.Hom.ext (bdry1Proj_mul_incl _)

variable {H : Type} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  (π : ∀ i, G i →* H) [MulAction H (RoundSphere n)] [@IsIsometricSMul H (RoundSphere n) _
    (@SemigroupAction.toSMul _ _ _ MulAction.toSemigroupAction)]

/-- The realized boundary structure of `∂K_1` restricted to the positive end is `φ_CP`. -/
theorem end_dual_eq :
    dualHom (asymptoticObjInvolution π (RoundSphere n)) (((facePair hr n 1 h1).N : ℕ) : ℤ)
      ((endProj hr n h1).toComplex π) ≫
      dualityMap π (facePair hr n 1 h1).hBd (facePair hr n 1 h1).bdHom ≫
        (endProj hr n h1).toComplex π =
    dualityMap π (cpConst_dimLE (endLabel r n)) (cpConstDuality (endLabel r n)).hom := by
  rw [dualityMap_comp_toComplex, dualHom_toComplex_comp_dualityMap π (facePair hr n 1 h1).hBd
    (cpConst_dimLE _)]
  refine dualityMap_congr π _ fun i ↦ ?_
  ext c c'
  change ((bdry1Proj (mBox r (germMesh i))).f *
    (@id (Matrix (cubeCP.bdry (mBox r (germMesh i)) 1).X (cubeCP.bdry (mBox r (germMesh i)) 1).X ℚ)
      ((facePair hr n 1 h1).bdHom.f i).f) *
    ((bdry1Proj (mBox r (germMesh i))).f)ᵀ) c c' = CPcell.φ.f c c'
  exact (bdry1Proj_conj _ _ c c').trans (bdry1_bdHom_pt _ c c')

section Supports

variable (hr1 : r ≤ 1)

include hr hr1 h1

/-- The positive end point lies near `P` (G8). -/
theorem endLabel_near {P : Set (RoundSphere n)} (hPe : chartV '' cubeEndV r r ⊆ P) :
    (cpConst (endLabel r n)).LabelsNear P :=
  (labelsNear_of_face hr hr1 n (A := cpConst (endLabel r n)) (j := 1)
    (fun _ _ ↦ (.inl (Fin.last _), ())) (fun _ _ ↦ rfl)
    (fun _ x ↦ x = (.inl (Fin.last _), ())) (fun _ _ ↦ rfl) (cubeEndV r r) (by
      filter_upwards [clampV_mem_end hr hr1 h1] with i hi x hx
      subst hx
      exact hi.1)).mono hPe

/-- The negative end point lies near `Q` (G8). -/
theorem endQ_tendsto {Q : Set (RoundSphere n)} (hQe : chartV '' cubeEndV r (-r) ⊆ Q) :
    Tendsto (fun i ↦ infEDist (cubeLabel r (germMesh i) n 1 (.inl 0, ())) Q) atTop (𝓝 0) :=
  tendsto_zero_of_le (tendsto_cubeLabel hr hr1 n 1 (fun _ x ↦ x = (.inl 0, ())) (cubeEndV r (-r))
    (by
      filter_upwards [clampV_mem_end hr hr1 h1] with i hi x hx
      subst hx
      exact hi.2)) fun i ↦ (infEDist_anti hQe).trans
    (le_iSup₂_of_le (f := fun x (_ : x = ((.inl 0, ()) : (cube (mBox r (germMesh i) + 1) 1).X)) ↦
      infEDist (cubeLabel r (germMesh i) n 1 x) (chartV '' cubeEndV r (-r))) (.inl 0, ()) rfl le_rfl)

end Supports

/-! ### The last stage -/

/-- **The last stage of the flag**: `projSep` of the level `[∂K_1]` to `𝒜_P`, included into
`𝒜(Sⁿ)`, is the class `[pt ⊗ CPcell]` of the constant sequence at the positive end point. -/
theorem endStep (hr1 : r ≤ 1) (𝕃 : LowerLTheory) {P Q Y₀ : Set (RoundSphere n)}
    (hP : IsClosedInv H P) (hQ : IsClosedInv H Q) (hY₀ : IsClosedInv H Y₀) (PY : P ⊆ Y₀)
    (QY : Q ⊆ Y₀) (YPQ : Y₀ ⊆ P ∪ Q) (PQ : Disjoint P Q)
    (hYe : chartV '' cubeBdryV r (n - 1) ⊆ Y₀) (hPe : chartV '' cubeEndV r r ⊆ P)
    (hQe : chartV '' cubeEndV r (-r) ⊆ Q) :
    𝕃.map (supportKaroubiFiltration π P).incl 4 (projSep 𝕃 hP hQ PY QY YPQ PQ 4
      (𝕃.cls _ 4 (Lconc.cls (A := (supportKaroubiFiltration π Y₀).sub) (N := 4)
        ((levelAmb hr n π 1 h1).lift (SeqCut.supp_mapC π hY₀
          ((labelsNear_bd hr hr1 n 1 h1).mono hYe)))))) =
      𝕃.cls _ 4 (Lconc.cls ((cpConstDuality (endLabel r n)).symPoincare π)) := by
  have hnP := endLabel_near hr n h1 hr1 hPe
  have hCP : ∀ r', (supportKaroubiFiltration π Y₀).U
      (((cpConstDuality (endLabel r n)).symPoincare π).C.X r') :=
    SeqCut.supp_mapC π hY₀ (hnP.mono PY)
  have hL0 : ∀ r', (supportKaroubiFiltration π Y₀).U ((levelAmb hr n π 1 h1).C.X r') :=
    SeqCut.supp_mapC π hY₀ ((labelsNear_bd hr hr1 n 1 h1).mono hYe)
  set P' : SymPoincare (supportKaroubiFiltration π Y₀).sub.inv 4 :=
    (levelAmb hr n π 1 h1).lift hL0 with hP'def
  let Q' : SymPoincare (supportKaroubiFiltration π Y₀).sub.inv 4 :=
    ((cpConstDuality (endLabel r n)).symPoincare π).lift hCP
  let t : P'.C ⟶ Q'.C :=
    liftHom ((asymptoticQuotInv π (RoundSphere n)).mapH ((endProj hr n h1).toComplex π))
  let i : Q'.C ⟶ P'.C :=
    liftHom ((asymptoticQuotInv π (RoundSphere n)).mapH ((endIncl hr n h1).toComplex π))
  have hp : P'.p = 𝟙 _ := SymPoincare.lift_p_eq_id _ _ (by
    change (asymptoticQuotInv π (RoundSphere n)).mapH (𝟙 _) = _
    exact CategoryTheory.Functor.map_id _ _)
  have hq : Q'.p = 𝟙 _ := SymPoincare.lift_p_eq_id _ _ (by
    change (asymptoticQuotInv π (RoundSphere n)).mapH (𝟙 _) = _
    exact CategoryTheory.Functor.map_id _ _)
  have hit : i ≫ t = 𝟙 _ := by
    ext r'
    apply ObjectProperty.hom_ext
    change AsymptoticCategory.functor.map (((endIncl hr n h1).toComplex π).f r') ≫
      AsymptoticCategory.functor.map (((endProj hr n h1).toComplex π).f r') = 𝟙 _
    rw [← CategoryTheory.Functor.map_comp, ← HomologicalComplex.comp_f, ← Hom.toComplex_comp,
      endProj_comp_incl, Hom.toComplex_id]
    exact CategoryTheory.Functor.map_id _ _
  have hc : ∀ r', FactorsThrough (supportRestrictFiltration π Q Y₀).U (𝟙 _ - t.f r' ≫ i.f r') := by
    intro r'
    refine (KaroubiFiltration.factorsThrough_restrict_iff (supportKaroubiFiltration π Q)
      (V := (supportKaroubiFiltration π Y₀).U)
      (fun _ h ↦ AsymptoticObject.IsSupported.mono QY h) _).mpr ?_
    haveI := AsymptoticCategory.functor_additive (π := π) (X := RoundSphere n)
    have e : (𝟙 _ - t.f r' ≫ i.f r').hom = AsymptoticCategory.functor.map
        (hom (A := (facePair hr n 1 h1).Bd) (B := (facePair hr n 1 h1).Bd) π
          (fun i ↦ 1 - ((endIncl hr n h1).f i).f * ((endProj hr n h1).f i).f)
          (PropTendsto.one.sub ((endIncl hr n h1).tendsto.mul (endProj hr n h1).tendsto)) r' r') := by
      rw [SeqCut.hom_sub π _ _ PropTendsto.one
        ((endIncl hr n h1).tendsto.mul (endProj hr n h1).tendsto), CategoryTheory.Functor.map_sub,
        hom_one, CategoryTheory.Functor.map_id]
      change 𝟙 (AsymptoticCategory.functor.obj (((facePair hr n 1 h1).Bd.toComplex π).X r')) -
        AsymptoticCategory.functor.map (((endProj hr n h1).toComplex π).f r') ≫
        AsymptoticCategory.functor.map (((endIncl hr n h1).toComplex π).f r') = _
      rw [← CategoryTheory.Functor.map_comp, ← HomologicalComplex.comp_f, ← Hom.toComplex_comp]
      rfl
    rw [e]
    refine inIdeal_hom π _ _ r' r' hQ.2 (tendsto_zero_of_le (endQ_tendsto hr n h1 hr1 hQe)
      fun i' ↦ iSup_le fun κ ↦ iSup_le fun σ ↦ iSup_le fun hne ↦ ?_)
    change ((1 : Matrix (cubeCP.bdry (mBox r (germMesh i')) 1).X
      (cubeCP.bdry (mBox r (germMesh i')) 1).X ℚ) -
      (bdry1Incl (mBox r (germMesh i'))).f * (bdry1Proj (mBox r (germMesh i'))).f) κ σ ≠ 0 at hne
    rw [one_sub_incl_mul_proj_apply _ κ σ] at hne
    split_ifs at hne with hκσ
    · obtain ⟨rfl, hκ⟩ := hκσ
      rw [max_self]
      change infEDist (cubeLabel r (germMesh i') n 1 κ.1.1) Q ≤ _
      rw [bdry1_neg_end _ hκ]
    · exact absurd rfl hne
  have hφ : dualHom (supportKaroubiFiltration π Y₀).sub.inv 4 t ≫ P'.φ ≫ t = Q'.φ := by
    ext r'
    apply ObjectProperty.hom_ext
    have h := congrArg (fun g ↦ (asymptoticQuotInv π (RoundSphere n)).F.map
      (HomologicalComplex.Hom.f g r')) (end_dual_eq hr n h1 π)
    simp only [HomologicalComplex.comp_f, CategoryTheory.Functor.map_comp] at h
    refine Eq.trans ?_ h
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom]
    congr 1
  have hcls := Lconc.cls_eq_of_isometric (SymPoincare.isometric_proj_of_split
    (supportRestrictFiltration π Q Y₀) P' Q' hp hq t i hit hc hφ)
  let CPP : SymPoincare (supportKaroubiFiltration π P).sub.inv 4 :=
    ((cpConstDuality (endLabel r n)).symPoincare π).lift (SeqCut.supp_mapC π hP hnP)
  have key : 𝕃.map (supportRestrictFiltration π Q Y₀).proj 4 (𝕃.cls _ 4 (Lconc.cls P')) =
      𝕃.map (supportRestrictFiltration π Q Y₀).proj 4
        (𝕃.map (supportIncl PY) 4 (𝕃.cls _ 4 (Lconc.cls CPP))) := by
    rw [← 𝕃.cls_map, ← 𝕃.cls_map, ← 𝕃.cls_map, Lconc.map_cls, Lconc.map_cls, Lconc.map_cls]
    exact congrArg (𝕃.cls _ 4) hcls
  have hsep : projSep 𝕃 hP hQ PY QY YPQ PQ 4 (𝕃.cls _ 4 (Lconc.cls P')) =
      𝕃.cls _ 4 (Lconc.cls CPP) := by
    rw [← projSep_incl 𝕃 hP hQ PY QY YPQ PQ 4 (𝕃.cls _ 4 (Lconc.cls CPP))]
    simp only [projSep, LowerLTheory.projSepOf, AddMonoidHom.comp_apply]
    exact congrArg _ key
  rw [hsep, ← 𝕃.cls_map, Lconc.map_cls]
  rfl

end CubeGeom

end HSFormal.Cubical.BasedComplex
