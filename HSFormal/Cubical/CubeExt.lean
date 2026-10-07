import HSFormal.Cubical.CubeMV

/-!
# The exterior cut of the germ along the box (cubical module C8, Lemma 11.2)

The germ `W_i = Tⁿ_{M_i} ⊗ CPcell` of the identity control map is cut along the box
`∏ [a, a + m_i + 1]` of the cube cut (`CubeGeom`): `W_A` the cells off the open box, `W_B` the
cells of the box (`extSeqCut`).  The interface `Σ = W_A ∩ W_B` is the boundary `∂K_n` of the
`n`-dimensional face pair (`boxSigIso`), with the same labels (G2) and boundary structures
(`torusCP.cutTop_boxIso`); the B-pair is the controlled cube pair duality (`extSeqCut_hR`).
-/

noncomputable section

namespace HSFormal.Cubical.BasedComplex

/-- Iterated tensor products of composites. -/
theorem CellInj.prod_comp_apply : (k : ℕ) → {C D E : Fin k → BasedComplex} →
    (f : ∀ i, CellInj (D i) (E i)) → (g : ∀ i, CellInj (C i) (D i)) →
    (p : (prodComplex k C).X) →
    (CellInj.prod k fun i ↦ (f i).comp (g i)).toFun p =
      (CellInj.prod k f).toFun ((CellInj.prod k g).toFun p)
  | 0, _, _, _, _, _, _ => rfl
  | k + 1, _, _, _, f, g, ⟨p, p'⟩ => by
    change ((f 0).toFun ((g 0).toFun p), _) = ((f 0).toFun ((g 0).toFun p), _)
    rw [CellInj.prod_comp_apply k (fun i ↦ f i.succ) (fun i ↦ g i.succ) p']
    rfl

section Box

variable (M m : ℕ) [NeZero M] (h : m + 1 < M) {n : ℕ} (a : Fin n → Fin M)

theorem torus.boxRelInj_eq (p : (cubeRel m n).X) :
    (torus.boxRelInj M m h a).toFun p =
      (torus.boxInj M m h a).toFun ((cubeRelInj m n).toFun p) :=
  CellInj.prod_comp_apply n _ _ p

/-- The cells of the interface `Σ = W_A ∩ W_B` of the box cut, as `∂K_n`. -/
def boxSigInj : CellInj (cubeCP.bdry m n) (torusCP M n) :=
  ((torus.boxInj M m h a).tensor (CellInj.id CPcell)).comp (CellInj.subtype _ _)

theorem boxSigInj_apply (y : (cubeCP.bdry m n).X) :
    (boxSigInj M m h a).toFun y = ((torus.boxInj M m h a).toFun y.1.1, y.1.2) := rfl

theorem boxSig_range_iff (σ : (torusCP M n).X) :
    (torusCP.WA M n a (fun _ ↦ m + 1) σ ∧ torusCP.WB M n a (fun _ ↦ m + 1) σ) ↔
      ∃ y, (boxSigInj M m h a).toFun y = σ := by
  obtain ⟨τ, c⟩ := σ
  constructor
  · rintro ⟨hO, hI⟩
    obtain ⟨x, hx⟩ := (torus.boxInj_range_iff M m h a τ).mpr hI
    have hb : cube.Bdry (m + 1) x := by
      by_contra hb
      obtain ⟨p, rfl⟩ := (cube.not_bdry_iff m n x).mp hb
      exact (torus.boxRelInj_range_iff M m h a τ).mp ⟨p, (torus.boxRelInj_eq M m h a p).trans hx⟩
        hO
    exact ⟨⟨(x, c), hb⟩, Prod.ext hx rfl⟩
  · rintro ⟨⟨⟨x, c'⟩, hb⟩, hy⟩
    rw [boxSigInj_apply] at hy
    obtain ⟨h₁, -⟩ := Prod.mk.inj hy
    subst h₁
    refine ⟨?_, (torus.boxInj_range_iff M m h a _).mp ⟨x, rfl⟩⟩
    by_contra hO
    obtain ⟨p, hp⟩ := (torus.boxRelInj_range_iff M m h a _).mpr hO
    rw [torus.boxRelInj_eq] at hp
    exact (cube.not_bdry_iff m n x).mpr ⟨p, (torus.boxInj M m h a).inj hp⟩ hb

variable [DecidablePred (torusCP.WA M n a fun _ ↦ m + 1)]
  [DecidablePred (torusCP.WB M n a fun _ ↦ m + 1)]

/-- **The interface of the box cut is `∂K_n`.** -/
def boxSigIso : CellIso (cubeCP.bdry m n)
    ((torusCP M n).restrict
      (fun σ ↦ torusCP.WA M n a (fun _ ↦ m + 1) σ ∧ torusCP.WB M n a (fun _ ↦ m + 1) σ)
      ((torusCP.isSub_WA M n a _).and (torusCP.isSub_WB M n a _ fun _ ↦ h)).isLocallyClosed) :=
  (boxSigInj M m h a).toIso _ _ (boxSig_range_iff M m h a)

theorem boxSigIso_apply (y : (cubeCP.bdry m n).X) :
    ((boxSigIso M m h a).toEquiv y).1 = ((torus.boxInj M m h a).toFun y.1.1, y.1.2) := rfl

end Box

namespace CubeGeom

open Filter Matrix Metric Topology HSFormal.RoundSphere HSFormal.LTheory CategoryTheory
open scoped ENNReal
open ControlledSeq

variable {r : ℝ} (hr : 0 < r) (n : ℕ)

/-- The face points of the full box are the arc labels (G2 for `j = n`). -/
theorem facePt_full {M : ℕ} [NeZero M] (hM : 2 ≤ M) (x : (cube (mBox r M + 1) n).X) :
    facePt r M n n x = prodLabel n (arcs hr hM n) x := by
  funext t
  have e := prodLabel_arcLabel_eq hr hM le_rfl x t
  rw [e]
  congr 1
  exact Fin.ext (by simp)

theorem center_boxInj {M : ℕ} [NeZero M] (hM : 2 ≤ M) (x : (cube (mBox r M + 1) n).X) :
    torus.center 16 M n ((torus.boxInj M (mBox r M) (mBox_lt hr hM) fun _ ↦ aBox r M).toFun x) =
      facePt r M n n x :=
  (torus.prodLabel_boxInj 16 M (mBox r M) (mBox_lt hr hM) n _ x).symm.trans
    (facePt_full hr n hM x).symm

/-- The germ duality of the identity control map. -/
abbrev germDual : IsControlledDuality (fun i ↦ torusCP.duality (germMesh i) n)
    fun i σ ↦ (ContinuousMap.id (RoundSphere n)) (germCollapse n (torus.center 16 (germMesh i) n σ.1)) :=
  germ_isControlledDuality n (ContinuousMap.id _)

variable (r) in
/-- The first vertices of the box. -/
abbrev boxA (i : ℕ) : Fin n → Fin (germMesh i) := fun _ ↦ aBox r (germMesh i)

open Classical in
/-- **The exterior (box) cut** of the germ `W = Tⁿ ⊗ CPcell`: `W_A` the cells off the open box,
`W_B` the cells of the box. -/
def extSeqCut : SeqCut (RoundSphere n) where
  W := (germDual n).seq
  N := n + 3
  hW i := torusCP.dimLE (germMesh i) n
  ψ := (germDual n).symDuality.hom
  hψ := (germDual n).symDuality.symm
  SA i := torusCP.WA (germMesh i) n (boxA r n i) fun _ ↦ mBox r (germMesh i) + 1
  SB i := torusCP.WB (germMesh i) n (boxA r n i) fun _ ↦ mBox r (germMesh i) + 1
  hA _ := torusCP.isSub_WA _ n _ _
  hB i := torusCP.isSub_WB _ n _ _ fun _ ↦ mBox_lt hr (two_le_germMesh i)
  cover _ σ := torus.offBox_or_inBox _ n _ _ σ.1
  loc i σ τ h hτ := (torusCP.boxCut_local (two_le_germMesh i)
    (fun _ ↦ mBox_lt hr (two_le_germMesh i)) σ τ h).1 hτ
  loc' i σ τ h hτ := (torusCP.boxCut_local (two_le_germMesh i)
    (fun _ ↦ mBox_lt hr (two_le_germMesh i)) σ τ h).2 hτ
  hSig i σ hA hB := by
    obtain ⟨y, hy⟩ := (boxSig_range_iff (germMesh i) (mBox r (germMesh i))
      (mBox_lt hr (two_le_germMesh i)) (boxA r n i) σ).mp ⟨hA, hB⟩
    rw [← hy, (boxSigInj _ _ _ _).deg_eq]
    exact cubeCP.dimLE_bdry _ n y

variable {H : Type} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  (π : ∀ i, G i →* H) [MulAction H (RoundSphere n)] [@IsIsometricSMul H (RoundSphere n) _
    (@SemigroupAction.toSMul _ _ _ MulAction.toSemigroupAction)]

theorem extSeqCut_hψ :
    IsKarEquiv (𝟙 _) (𝟙 _) (dualityMap π (extSeqCut hr n).hW (extSeqCut hr n).ψ) :=
  ControlledSeq.isKarEquiv_dualityMap π _ (germDual n).symDuality.toHtpyEquiv

open Classical in
/-- The B-pair of the box cut as a controlled equivalence (the local cube pair duality). -/
def extSeqCut_ladderEquiv :
    ControlledSeq.HtpyEquiv ((extSeqCut hr n).WB.dual ((extSeqCut hr n).N + 1)
      (extSeqCut hr n).hWB) (extSeqCut hr n).WnA :=
  ControlledSeq.HtpyEquiv.ofPropLE (fun i ↦ (cubeCP.symAbsDualityLoc (mBox r (germMesh i)) n).transport
      (torusCP.boxIso (germMesh i) (mBox r (germMesh i)) (mBox_lt hr (two_le_germMesh i))
        (boxA r n i) (torusCP.isSub_WB _ n _ _ fun _ ↦ mBox_lt hr (two_le_germMesh i)).isLocallyClosed)
      (torusCP.boxRelIso (germMesh i) (mBox r (germMesh i)) (mBox_lt hr (two_le_germMesh i))
        (boxA r n i) (torusCP.isSub_WA _ n _ _).isLocallyClosed_compl)
      ((torusCP.dimLE (germMesh i) n).restrict _ _))
    (ucont_germCollapse n)
    (a := fun i (q : {σ : (torusCP (germMesh i) n).X //
      torusCP.WB (germMesh i) n (boxA r n i) (fun _ ↦ mBox r (germMesh i) + 1) σ}) ↦
        torus.center 16 (germMesh i) n q.1.1)
    (b := fun i (q : {σ : (torusCP (germMesh i) n).X //
      ¬torusCP.WA (germMesh i) n (boxA r n i) (fun _ ↦ mBox r (germMesh i) + 1) σ}) ↦
        torus.center 16 (germMesh i) n q.1.1)
    (fun _ ↦ rfl) (fun _ ↦ rfl) (tendsto_halfMesh) (tendsto_ofReal_mesh 16 tendsto_germMesh)
    fun i ↦ (cubeCP.symAbsDualityLoc_propLE 16 (germMesh i) (mBox r (germMesh i))
      (mBox_lt hr (two_le_germMesh i)) n (boxA r n i)).transport
      (torusCP.boxIso (germMesh i) (mBox r (germMesh i)) (mBox_lt hr (two_le_germMesh i))
        (boxA r n i) (torusCP.isSub_WB _ n _ _ fun _ ↦ mBox_lt hr (two_le_germMesh i)).isLocallyClosed)
      (torusCP.boxRelIso (germMesh i) (mBox r (germMesh i)) (mBox_lt hr (two_le_germMesh i))
        (boxA r n i) (torusCP.isSub_WA _ n _ _).isLocallyClosed_compl)
      ((torusCP.dimLE (germMesh i) n).restrict _ _)
      (fun x ↦ (torus.prodLabel_boxInj 16 (germMesh i) (mBox r (germMesh i))
        (mBox_lt hr (two_le_germMesh i)) n (boxA r n i) x.1).symm)
      (fun x ↦ prodLabel_cellInj n _ _ x.1)

open Classical in
theorem extSeqCut_hR :
    IsKarEquiv (𝟙 _) (𝟙 _) (dualityMap π (extSeqCut hr n).hWB (extSeqCut hr n).ladderR) := by
  have h := ControlledSeq.isKarEquiv_dualityMap π (extSeqCut hr n).hWB (extSeqCut_ladderEquiv hr n)
  have e : ∀ i, ((extSeqCut_ladderEquiv hr n).hom.f i).f = ((extSeqCut hr n).ladderR.f i).f :=
    fun i ↦ by
      ext ρ σ
      obtain ⟨x, rfl⟩ := (torusCP.boxRelIso (germMesh i) (mBox r (germMesh i))
        (mBox_lt hr (two_le_germMesh i)) (boxA r n i)
        (torusCP.isSub_WA _ n _ _).isLocallyClosed_compl).toEquiv.surjective ρ
      obtain ⟨y, rfl⟩ := (torusCP.boxIso (germMesh i) (mBox r (germMesh i))
        (mBox_lt hr (two_le_germMesh i)) (boxA r n i)
        (torusCP.isSub_WB _ n _ _ fun _ ↦ mBox_lt hr (two_le_germMesh i)).isLocallyClosed).toEquiv.surjective σ
      refine (HtpyEquiv.transport_hom_f_apply _ _ _ _ x y).trans ?_
      rw [cubeCP.symAbsDualityLoc_hom_f]
      exact (torusCP.boxCut_ladderRight_apply _ _ _ _ ((extSeqCut hr n).loc i) x y).symm
  rwa [ControlledSeq.dualityMap_congr π _ e] at h

/-- The interface isomorphism `Σ ≅ ∂K_n` at mesh `i`. -/
abbrev extSig (i : ℕ) :=
  open Classical in
  boxSigIso (germMesh i) (mBox r (germMesh i)) (mBox_lt hr (two_le_germMesh i)) (boxA r n i)

open Classical in
/-- The interface labels match (G2). -/
theorem extSeqCut_hl (i : ℕ) (σ : ((extSeqCut hr n).Sig.C i).X) :
    (facePair hr n n le_rfl).Bd.label i ((extSig hr n i).symm.toEquiv σ) =
      (extSeqCut hr n).W.label i σ.1 := by
  obtain ⟨y, rfl⟩ := (extSig hr n i).toEquiv.surjective σ
  rw [CellIso.symm_apply_apply]
  change cubeLabel r (germMesh i) n n y.1.1 = germCollapse n (torus.center 16 (germMesh i) n
    ((torus.boxInj (germMesh i) (mBox r (germMesh i)) (mBox_lt hr (two_le_germMesh i))
      (boxA r n i)).toFun y.1.1))
  rw [center_boxInj hr n (two_le_germMesh i)]
  rfl

open Classical in
/-- **The interface carries the next boundary structure** (`torusCP.cutTop_boxIso`). -/
theorem extSeqCut_hmatch (i : ℕ) (σ τ : ((extSeqCut hr n).Sig.C i).X) :
    ((facePair hr n n le_rfl).bdHom.f i).f ((extSig hr n i).symm.toEquiv σ)
      ((extSig hr n i).symm.toEquiv τ) = ((extSeqCut hr n).bdB i).f σ τ := by
  obtain ⟨y, rfl⟩ := (extSig hr n i).toEquiv.surjective σ
  obtain ⟨y', rfl⟩ := (extSig hr n i).toEquiv.surjective τ
  rw [CellIso.symm_apply_apply, CellIso.symm_apply_apply, SeqPair.bdHom_f]
  have hB := (torusCP.isSub_WB (germMesh i) n (boxA r n i) (fun _ ↦ mBox r (germMesh i) + 1)
    fun _ ↦ mBox_lt hr (two_le_germMesh i)).isLocallyClosed
  have h1 := congr_fun (congr_fun (defect_submatrix (torusCP.boxIso (germMesh i)
    (mBox r (germMesh i)) (mBox_lt hr (two_le_germMesh i)) (boxA r n i) hB)
    (cubeTop_dimLE _ n) ((torusCP.dimLE (germMesh i) n).restrict _ hB)
    (cutTop (torusCP.dimLE (germMesh i) n) (torusCP.duality (germMesh i) n).hom
      (torusCP.WB (germMesh i) n (boxA r n i) fun _ ↦ mBox r (germMesh i) + 1))) y.1) y'.1
  have h2 : (cutTop (torusCP.dimLE (germMesh i) n) (torusCP.duality (germMesh i) n).hom
      (torusCP.WB (germMesh i) n (boxA r n i) fun _ ↦ mBox r (germMesh i) + 1)).submatrix
      (torusCP.boxIso (germMesh i) (mBox r (germMesh i)) (mBox_lt hr (two_le_germMesh i))
        (boxA r n i) hB).toEquiv
      (torusCP.boxIso (germMesh i) (mBox r (germMesh i)) (mBox_lt hr (two_le_germMesh i))
        (boxA r n i) hB).toEquiv = cubeTop (mBox r (germMesh i)) n := by
    ext p q
    exact torusCP.cutTop_boxIso _ _ _ _ hB p q
  rw [h2, submatrix_apply] at h1
  exact h1

/-! ### Supports of the box cut (G3, G5, G6) -/

theorem _root_.HSFormal.Cubical.BasedComplex.ControlledSeq.labelsNear_of_eventually_mem
    {X : Type} [PseudoEMetricSpace X] {A : ControlledSeq X} {S : Set X}
    (h : ∀ᶠ i in atTop, ∀ σ, A.label i σ ∈ S) : A.LabelsNear S :=
  tendsto_const_nhds.congr' (by
    filter_upwards [h] with i hi
    exact (le_antisymm (iSup_le fun σ ↦ (infEDist_zero_of_mem (hi σ)).le) (zero_le)).symm)

section Supports

variable (hr1 : r ≤ 1)

include hr1

/-- The cells off the open box are labelled outside the open cube (G3). -/
theorem extSeqCut_WA_near :
    (extSeqCut hr n).WA.LabelsNear {z | ∀ v, chartV v = z → r ≤ ‖v‖} :=
  labelsNear_of_eventually_mem (by
    filter_upwards [germCollapse_center_offBox hr hr1 n] with i hi σ
    exact hi σ.1.1 σ.2)

open Classical in
theorem extSeqCut_Bd_near :
    (extSeqCut hr n).Apair.Bd.LabelsNear (chartV '' cubeBdryV r (n - n)) :=
  labelsNear_of_face hr hr1 n (A := (extSeqCut hr n).Apair.Bd) (j := n)
    (fun i x ↦ ((extSig hr n i).symm.toEquiv ⟨x.1.1, x.1.2, x.2⟩).1.1)
    (fun i x ↦ (extSeqCut_hl hr n i ⟨x.1.1, x.1.2, x.2⟩).symm)
    (fun i y ↦ cube.Bdry (mBox r (germMesh i) + 1) y)
    (fun i x ↦ ((extSig hr n i).symm.toEquiv ⟨x.1.1, x.1.2, x.2⟩).2) _
    (clampV_mem_bdry hr hr1 le_rfl)

open Classical in
theorem extSeqCut_WnA_near :
    (extSeqCut hr n).WnA.LabelsNear (chartV '' cubeFaceV r (n - n)) := by
  refine labelsNear_of_face hr hr1 n (A := (extSeqCut hr n).WnA) (j := n)
    (fun i σ ↦ ((torusCP.boxIso (germMesh i) (mBox r (germMesh i))
      (mBox_lt hr (two_le_germMesh i)) (boxA r n i)
      ((extSeqCut hr n).hB i).isLocallyClosed).symm.toEquiv
        ⟨σ.1, ((extSeqCut hr n).cover i σ.1).resolve_left σ.2⟩).1) (fun i σ ↦ ?_)
    (fun _ _ ↦ True) (fun _ _ ↦ trivial) _ ?_
  · set w : {σ : (torusCP (germMesh i) n).X //
        torusCP.WB (germMesh i) n (boxA r n i) (fun _ ↦ mBox r (germMesh i) + 1) σ} :=
      ⟨σ.1, ((extSeqCut hr n).cover i σ.1).resolve_left σ.2⟩
    have hw := (torusCP.boxIso (germMesh i) (mBox r (germMesh i))
      (mBox_lt hr (two_le_germMesh i)) (boxA r n i)
      ((extSeqCut hr n).hB i).isLocallyClosed).apply_symm_apply w
    have hσ : σ.1.1 = (torus.boxInj (germMesh i) (mBox r (germMesh i))
        (mBox_lt hr (two_le_germMesh i)) (boxA r n i)).toFun
        ((torusCP.boxIso (germMesh i) (mBox r (germMesh i))
          (mBox_lt hr (two_le_germMesh i)) (boxA r n i)
          ((extSeqCut hr n).hB i).isLocallyClosed).symm.toEquiv w).1 := by
      have := congrArg (fun q ↦ q.1.1) hw
      exact this.symm
    change germCollapse n (torus.center 16 (germMesh i) n σ.1.1) = _
    rw [hσ, center_boxInj hr n (two_le_germMesh i)]
    rfl
  · filter_upwards [clampV_mem_face hr hr1 (le_refl n)] with i hi x _
    exact hi x

end Supports

/-! ### The exterior step -/

/-- **The exterior step on the cube flag**: the exterior cut of the germ class is `-bsign` times
the level `[∂K_n]`. -/
theorem extStep_cube (hr1 : r ≤ 1) (𝕃 : LowerLTheory) {A B Z Y : Set (RoundSphere n)}
    (hA : IsClosedInv H A) (hB : IsClosedInv H B) (hZ : IsClosedInv H Z) (hY : IsClosedInv H Y)
    (hcover : A ∪ B = Set.univ) (hZA : Z ⊆ A) (hZB : Disjoint Z B) (htop : A ∩ B ⊆ Y)
    (hAe : {z | ∀ v, chartV v = z → r ≤ ‖v‖} ⊆ A) (hBe : chartV '' cubeFaceV r (n - n) ⊆ B)
    (hABe : chartV '' cubeBdryV r (n - n) ⊆ A ∩ B) (hYe : chartV '' cubeBdryV r (n - n) ⊆ Y) :
    𝕃.map (supportIncl htop) ((n + 3 : ℕ) : ℤ) (cutBdry 𝕃 hA hB hZ hcover hZA hZB ((n + 3 : ℕ) : ℤ)
      (𝕃.cls _ (((n + 3 : ℕ) : ℤ) + 1) (Lconc.cls
        (((germDual n).toAsymptotic π).map (supportKaroubiFiltration π Z).proj)))) =
      (-𝕃.bsign ((n + 3 : ℕ) : ℤ)) • 𝕃.cls _ ((n + 3 : ℕ) : ℤ) (Lconc.cls
        ((levelAmb hr n π n le_rfl).lift (SeqCut.supp_mapC π hY
          ((labelsNear_bd hr hr1 n n le_rfl).mono hYe)))) :=
  (extSeqCut hr n).extStep π 𝕃 (extSeqCut_hψ hr n π) (extSeqCut_hR hr n π) hA hB hZ hY hcover
    hZA hZB htop ((extSeqCut_WA_near hr n hr1).mono hAe)
    ((extSeqCut_Bd_near hr n hr1).mono hABe) ((extSeqCut_WnA_near hr n hr1).mono hBe)
    (facePair hr n n le_rfl).bdHom_symm (levelPoincare hr n π n le_rfl)
    (fun i ↦ (extSig hr n i).symm) (extSeqCut_hl hr n) (extSeqCut_hmatch hr n)
    ((labelsNear_bd hr hr1 n n le_rfl).mono hYe)

end CubeGeom

end HSFormal.Cubical.BasedComplex
