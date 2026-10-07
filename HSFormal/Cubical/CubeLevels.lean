import HSFormal.Cubical.CubeGeom
import HSFormal.Cubical.CubeFaceBased
import HSFormal.Cubical.CutClass

/-!
# The levels of the cube cut flag as controlled Poincaré complexes (cubical module C8)

For the radius `r ∈ (0, 1]` of the cut cube and the germ meshes `M_i = germMesh i`, the
`j`-dimensional top face of the box of the cut is the controlled sequence
`K_j = I_{m_i+1}^{⊗j} ⊗ CPcell` (`m_i = mBox r M_i`) labelled by `cubeLabel` (`faceSeq`).

* Labels: the face points are the arc labels of the box padded by the constant top coordinates,
  so propagation bounds in the arc labels (`PinchControl`, `CubeFaceBased`) carry over
  (`edist_facePt_le`, `HtpyEquiv.PropLE.facePt`), and through the uniformly continuous
  `germCollapse` to `Sⁿ` (`ControlledSeq.HtpyEquiv.ofPropLE`).
* `facePair j`: the controlled based pair `(K_j, ∂K_j)` with top `cubeTop` (a `SeqPair`), whose
  relative cap is a controlled equivalence (`facePair_hrel`, from `cubePair_relEquiv`).
* **`levelPoincare`**: the boundary `∂K_j` with the boundary structure `cubeCP.bdHom` (the
  `(j-1)`-th level of the flag) is Poincaré in the prequotient.
-/

noncomputable section

namespace HSFormal.Cubical.BasedComplex.CubeGeom

open Filter Matrix Metric Topology HSFormal.RoundSphere HSFormal.LTheory CategoryTheory
open scoped ENNReal
open ControlledSeq

variable {r : ℝ}

/-! ### Face labels -/

section Labels

variable {M : ℕ} [NeZero M]

/-- The arc labels of the sides of the box at mesh `M`. -/
abbrev arcs (hr : 0 < r) (hM : 2 ≤ M) (j : ℕ) :
    Fin j → (interval (mBox r M + 1)).X → AddCircle (16 : ℝ) :=
  fun _ ↦ interval.arcLabel 16 M (mBox r M) (mBox_lt hr hM) (aBox r M)

/-- The face points are the arc labels padded by constant coordinates: `1`-Lipschitz. -/
theorem edist_facePt_le (hr : 0 < r) (hM : 2 ≤ M) {n j : ℕ} (hj : j ≤ n)
    (x y : (cube (mBox r M + 1) j).X) :
    edist (facePt r M n j x) (facePt r M n j y) ≤
      edist (prodLabel j (arcs hr hM j) x) (prodLabel j (arcs hr hM j) y) := by
  refine edist_pi_le_iff.mpr fun t ↦ ?_
  by_cases h : n - j ≤ t.val
  · have ht : (⟨t.val - (n - j) + (n - j), by omega⟩ : Fin n) = t := Fin.ext (by simp; omega)
    have ex := prodLabel_arcLabel_eq hr hM hj x ⟨t.val - (n - j), by omega⟩
    have ey := prodLabel_arcLabel_eq hr hM hj y ⟨t.val - (n - j), by omega⟩
    rw [ht] at ex ey
    rw [← ex, ← ey]
    exact edist_le_pi_edist _ _ _
  · have : facePt r M n j x t = facePt r M n j y t := by
      simp only [facePt, cubeCoords, dif_neg h]
    rw [this, edist_self]
    exact zero_le

/-- Propagation in face points is bounded by propagation in arc labels. -/
theorem prop_facePt_le (hr : 0 < r) (hM : 2 ≤ M) {n j : ℕ} (hj : j ≤ n) {A B : Type*}
    {u : Matrix B A ℚ} (α : A → (cube (mBox r M + 1) j).X) (β : B → (cube (mBox r M + 1) j).X) :
    prop u (fun x ↦ facePt r M n j (α x)) (fun x ↦ facePt r M n j (β x)) ≤
      prop u (fun x ↦ prodLabel j (arcs hr hM j) (α x))
        (fun x ↦ prodLabel j (arcs hr hM j) (β x)) :=
  prop_le_iff.mpr fun _ _ h ↦ (edist_facePt_le hr hM hj _ _).trans
    (edist_le_prop (source := fun x ↦ prodLabel j (arcs hr hM j) (α x))
      (target := fun x ↦ prodLabel j (arcs hr hM j) (β x)) h)

/-- Radii of homotopy equivalences carry over from arc labels to face points. -/
theorem _root_.HSFormal.Cubical.BasedComplex.HtpyEquiv.PropLE.facePt (hr : 0 < r) (hM : 2 ≤ M)
    {n j : ℕ} (hj : j ≤ n) {C D : BasedComplex} {e : HtpyEquiv C D}
    {α : C.X → (cube (mBox r M + 1) j).X} {β : D.X → (cube (mBox r M + 1) j).X} {ρ s : ℝ≥0∞}
    (he : e.PropLE (fun x ↦ prodLabel j (arcs hr hM j) (α x))
      (fun x ↦ prodLabel j (arcs hr hM j) (β x)) ρ s) :
    e.PropLE (fun x ↦ facePt r M n j (α x)) (fun x ↦ facePt r M n j (β x)) ρ s :=
  ⟨(prop_facePt_le hr hM hj α β).trans he.hom, (prop_facePt_le hr hM hj β α).trans he.inv,
    (prop_facePt_le hr hM hj α α).trans he.homInv, (prop_facePt_le hr hM hj β β).trans he.invHom⟩

theorem prop_cellInj_d_le {C D : BasedComplex} (f : CellInj C D) {E : Type*}
    [PseudoEMetricSpace E] (lab : D.X → E) :
    prop C.d (lab ∘ f.toFun) (lab ∘ f.toFun) ≤ prop D.d lab lab :=
  prop_le_iff.mpr fun κ σ h ↦ edist_le_prop (u := D.d) (by rwa [f.d_eq])

/-- The box inclusion `K_j → Tʲ ⊗ CPcell`. -/
abbrev boxCP (hr : 0 < r) (hM : 2 ≤ M) (j : ℕ) :
    CellInj ((cube (mBox r M + 1) j).tensor CPcell) (torusCP M j) :=
  (torus.boxInj M (mBox r M) (mBox_lt hr hM) fun _ ↦ aBox r M).tensor (CellInj.id CPcell)

theorem prodLabel_arcs_eq_center (hr : 0 < r) (hM : 2 ≤ M) (j : ℕ)
    (q : ((cube (mBox r M + 1) j).tensor CPcell).X) :
    prodLabel j (arcs hr hM j) q.1 = torus.center 16 M j ((boxCP hr hM j).toFun q).1 :=
  torus.prodLabel_boxInj 16 M (mBox r M) (mBox_lt hr hM) j _ q.1

/-- The boundary of `K_j` has radius `η/2` in the arc labels. -/
theorem prop_faceCP_d_le (hr : 0 < r) (hM : 2 ≤ M) (j : ℕ) :
    prop ((cube (mBox r M + 1) j).tensor CPcell).d (fun q ↦ prodLabel j (arcs hr hM j) q.1)
      (fun q ↦ prodLabel j (arcs hr hM j) q.1) ≤ ENNReal.ofReal (mesh 16 M / 2) := by
  have e : (fun q : ((cube (mBox r M + 1) j).tensor CPcell).X ↦ prodLabel j (arcs hr hM j) q.1) =
      (fun q ↦ torus.center 16 M j q.1) ∘ (boxCP hr hM j).toFun :=
    funext (prodLabel_arcs_eq_center hr hM j)
  rw [e]
  exact (prop_cellInj_d_le _ _).trans (torusCP.prop_d_le 16 M j)

/-- The cube top has radius `η/2` in the arc labels (it is the torus duality on the box). -/
theorem prop_cubeTop_le (hr : 0 < r) (hM : 2 ≤ M) (j : ℕ) :
    prop (cubeTop (mBox r M) j) (fun q ↦ prodLabel j (arcs hr hM j) q.1)
      (fun q ↦ prodLabel j (arcs hr hM j) q.1) ≤ ENNReal.ofReal (mesh 16 M / 2) := by
  classical
  have hP := (torusCP.isSub_WB M j (fun _ ↦ aBox r M) (fun _ ↦ mBox r M + 1)
    fun _ ↦ mBox_lt hr hM).isLocallyClosed
  refine prop_le_iff.mpr fun x y hxy ↦ ?_
  rw [← torusCP.cutTop_boxIso (mBox r M) M (mBox_lt hr hM) (fun _ ↦ aBox r M) hP] at hxy
  rw [prodLabel_arcs_eq_center hr hM j x, prodLabel_arcs_eq_center hr hM j y]
  exact (edist_le_prop (u := (torusCP.duality M j).hom.f)
    (source := fun q ↦ torus.center 16 M j q.1) (target := fun q ↦ torus.center 16 M j q.1)
    hxy).trans (torusCP.propLE 16 M j).hom

end Labels

/-! ### The face sequences and pairs -/

section Faces

variable (hr : 0 < r) (n : ℕ)

theorem ucont_germCollapse : UniformContinuous (germCollapse n) :=
  CompactSpace.uniformContinuous_of_continuous (germCollapse n).continuous

theorem tendsto_halfMesh :
    Tendsto (fun i ↦ ENNReal.ofReal (mesh 16 (germMesh i) / 2)) atTop (𝓝 0) :=
  tendsto_zero_of_le (tendsto_ofReal_mesh 16 tendsto_germMesh) fun _ ↦ interval.half_le_mesh

/-- **The `j`-dimensional top face** `K_j = I^j ⊗ CPcell` of the box, labelled by `cubeLabel`. -/
def faceSeq (j : ℕ) (hj : j ≤ n) : ControlledSeq (RoundSphere n) where
  C i := (cube (mBox r (germMesh i) + 1) j).tensor CPcell
  label i q := cubeLabel r (germMesh i) n j q.1
  tendsto_d := PropTendsto.of_uniformContinuous (ucont_germCollapse n)
    (a := fun i (q : ((cube (mBox r (germMesh i) + 1) j).tensor CPcell).X) ↦
      facePt r (germMesh i) n j q.1)
    (b := fun i (q : ((cube (mBox r (germMesh i) + 1) j).tensor CPcell).X) ↦
      facePt r (germMesh i) n j q.1)
    (tendsto_zero_of_le (tendsto_halfMesh) fun i ↦
      (prop_facePt_le hr (two_le_germMesh i) hj
        (u := ((cube (mBox r (germMesh i) + 1) j).tensor CPcell).d) Prod.fst Prod.fst).trans
        (prop_faceCP_d_le hr (two_le_germMesh i) j))

/-- **The based cube pair** `(K_j, ∂K_j)` with top `cubeTop`. -/
def facePair (j : ℕ) (hj : j ≤ n) : SeqPair (RoundSphere n) where
  D := faceSeq hr n j hj
  N := j + 3
  hD _ := cubeTop_dimLE _ j
  S i x := cube.Bdry (mBox r (germMesh i) + 1) x.1
  hS _ := cubeCP.isSub_bdry _ j
  hSN _ σ hσ := cubeCP.dimLE_bdry _ j ⟨σ, hσ⟩
  T _ := cubeTop _ j
  T_deg _ _ _ h := cubeTop_deg _ j h
  T_symm _ σ τ := cubeTop_symm _ j σ τ
  T_tendsto := PropTendsto.of_uniformContinuous (ucont_germCollapse n)
    (a := fun i (q : ((cube (mBox r (germMesh i) + 1) j).tensor CPcell).X) ↦
      facePt r (germMesh i) n j q.1)
    (b := fun i (q : ((cube (mBox r (germMesh i) + 1) j).tensor CPcell).X) ↦
      facePt r (germMesh i) n j q.1)
    (tendsto_zero_of_le (tendsto_halfMesh) fun i ↦
      (prop_facePt_le hr (two_le_germMesh i) hj (u := cubeTop _ j) Prod.fst Prod.fst).trans
        (prop_cubeTop_le hr (two_le_germMesh i) j))
  supp _ _ _ h := cubeTop_defect_supp _ j h

/-- The relative cap of the face pair as a controlled equivalence (`cubePair_relEquiv`). -/
def facePair_relEquiv (j : ℕ) (hj : j ≤ n) :
    ControlledSeq.HtpyEquiv ((facePair hr n j hj).Rel.dual ((facePair hr n j hj).N + 1)
      (facePair hr n j hj).hRel) (facePair hr n j hj).D :=
  ControlledSeq.HtpyEquiv.ofPropLE (fun i ↦ cubePair_relEquiv (mBox r (germMesh i)) j)
    (ucont_germCollapse n)
    (a := fun i (q : {x : ((cube (mBox r (germMesh i) + 1) j).tensor CPcell).X //
      ¬cube.Bdry (mBox r (germMesh i) + 1) x.1}) ↦ facePt r (germMesh i) n j q.1.1)
    (b := fun i (q : ((cube (mBox r (germMesh i) + 1) j).tensor CPcell).X) ↦
      facePt r (germMesh i) n j q.1) (fun _ ↦ rfl) (fun _ ↦ rfl)
    (tendsto_halfMesh) (tendsto_ofReal_mesh 16 tendsto_germMesh) fun i ↦
      (cubePair_relEquiv_propLE (mBox r (germMesh i)) 16 (germMesh i)
        (mBox_lt hr (two_le_germMesh i)) j fun _ ↦ aBox r (germMesh i)).facePt hr
        (two_le_germMesh i) hj

variable {H : Type} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  (π : ∀ i, G i →* H) [MulAction H (RoundSphere n)]
  [@IsIsometricSMul H (RoundSphere n) _ (@SemigroupAction.toSMul _ _ _ MulAction.toSemigroupAction)]

theorem facePair_hrel (j : ℕ) (hj : j ≤ n) :
    IsKarEquiv (𝟙 _) (𝟙 _) (dualityMap π (facePair hr n j hj).hRel (facePair hr n j hj).relHom) := by
  have h := ControlledSeq.isKarEquiv_dualityMap π (facePair hr n j hj).hRel
    (facePair_relEquiv hr n j hj)
  rwa [ControlledSeq.dualityMap_congr π _ fun i ↦
    (cubePair_relEquiv_hom_f (mBox r (germMesh i)) j).trans
      ((facePair hr n j hj).relHom_f i).symm] at h

/-- **The levels of the flag are Poincaré**: `∂K_j` with the boundary structure of the face pair. -/
theorem levelPoincare (j : ℕ) (hj : j ≤ n) :
    IsKarEquiv (𝟙 _) (𝟙 _)
      (dualityMap π (facePair hr n j hj).hBd (facePair hr n j hj).bdHom) := by
  have h := ((facePair hr n j hj).toSymPair π (facePair_hrel hr n π j hj)).bd.poincare
  rw [isPoincare_iff] at h
  simpa using h

end Faces

/-! ### Supports of the levels -/

section Supports

variable (hr : 0 < r) (hr1 : r ≤ 1) (n : ℕ)

include hr hr1 in
/-- Labels of cells carried to face cells satisfying `P` approach `chartV '' T` (G4). -/
theorem labelsNear_of_face {A : ControlledSeq (RoundSphere n)} {j : ℕ}
    (f : ∀ i, (A.C i).X → (cube (mBox r (germMesh i) + 1) j).X)
    (hf : ∀ i σ, A.label i σ = cubeLabel r (germMesh i) n j (f i σ))
    (P : ∀ i, (cube (mBox r (germMesh i) + 1) j).X → Prop) (hP : ∀ i σ, P i (f i σ))
    (T : Set (Fin n → ℝ))
    (hT : ∀ᶠ i in atTop, ∀ x, P i x → clampV r (cubeCoords r (germMesh i) n j x) ∈ T) :
    A.LabelsNear (chartV '' T) :=
  tendsto_zero_of_le (tendsto_cubeLabel hr hr1 n j P T hT) fun i ↦ iSup_le fun σ ↦ by
    rw [hf]
    exact le_iSup₂_of_le (f := fun x (_ : P i x) ↦
      infEDist (cubeLabel r (germMesh i) n j x) (chartV '' T)) (f i σ) (hP i σ) le_rfl

include hr1 in
/-- **The level `∂K_j` lies near `∂Φ_j`** (G6). -/
theorem labelsNear_bd (j : ℕ) (hj : j ≤ n) :
    (facePair hr n j hj).Bd.LabelsNear (chartV '' cubeBdryV r (n - j)) :=
  labelsNear_of_face hr hr1 n (A := (facePair hr n j hj).Bd) (j := j) (fun _ σ ↦ σ.1.1)
    (fun _ _ ↦ rfl)
    (fun i x ↦ cube.Bdry (mBox r (germMesh i) + 1) x) (fun _ σ ↦ σ.2) _
    (clampV_mem_bdry hr hr1 hj)

end Supports

end HSFormal.Cubical.BasedComplex.CubeGeom
