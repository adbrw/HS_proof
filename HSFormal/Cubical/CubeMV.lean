import HSFormal.Cubical.CubeLevels

/-!
# The hemisphere cuts of the cube flag (cubical module C8, Lemma 11.2)

The `k`-th hemisphere cut of the flag cuts the level `∂K_{k+2}` (`facePair (k+2)`) into the rest
`R` and the top face `F` (`mvSeqCut`, a `SeqCut` with the data of `CubeFaceBased` (c)); the
B-pair of the top face is the controlled cube pair duality (`mvSeqCut_hR`), the interface
`R ∩ F ≅ ∂K_{k+1}` carries the B-side boundary structure to the next level (`cubeFace_sigIso_bdHom`)
and the labels match (G1).  The supports of all pieces are near the flag sets (G6, G7).
-/

noncomputable section

namespace HSFormal.Cubical.BasedComplex.CubeGeom

open Filter Matrix Metric Topology HSFormal.RoundSphere HSFormal.LTheory CategoryTheory
open scoped ENNReal
open ControlledSeq

variable {r : ℝ} (hr : 0 < r) (n : ℕ)

/-- **The `k`-th hemisphere cut** `∂K_{k+2} = R ∪ F` of the level `∂K_{k+2}`. -/
def mvSeqCut (k : ℕ) (hk : k + 2 ≤ n) : SeqCut (RoundSphere n) where
  W := (facePair hr n (k + 2) hk).Bd
  N := k + 4
  hW := (facePair hr n (k + 2) hk).hBd
  ψ := (facePair hr n (k + 2) hk).bdHom
  hψ := (facePair hr n (k + 2) hk).bdHom_symm
  SA i σ := cube.Rest (mBox r (germMesh i) + 1) σ.1.1
  SB i σ := cube.Top (mBox r (germMesh i) + 1) σ.1.1
  hA _ := cubeFace.isSub_rest _ k
  hB _ := cubeFace.isSub_top _ k
  cover _ σ := cubeFace.cover _ k σ
  loc _ σ τ h hτ := cubeCP.bdHom_loc _ k σ τ h hτ
  loc' _ σ τ h hτ := cubeCP.bdHom_loc' _ k σ τ h hτ
  hSig _ σ hA hB := cubeFace.hSig _ k σ hA hB

/-- The B-pair of the top face as a controlled equivalence (`cubeFace_ladderEquiv`). -/
def mvSeqCut_ladderEquiv (k : ℕ) (hk : k + 2 ≤ n) :
    ControlledSeq.HtpyEquiv ((mvSeqCut hr n k hk).WB.dual ((mvSeqCut hr n k hk).N + 1)
      (mvSeqCut hr n k hk).hWB) (mvSeqCut hr n k hk).WnA :=
  ControlledSeq.HtpyEquiv.ofPropLE (fun i ↦ cubeFace_ladderEquiv (mBox r (germMesh i)) k)
    (ucont_germCollapse n)
    (a := fun i (q : {x : (cubeCP.bdry (mBox r (germMesh i)) (k + 2)).X //
      cube.Top (mBox r (germMesh i) + 1) x.1.1}) ↦ facePt r (germMesh i) n (k + 2) q.1.1.1)
    (b := fun i (q : {x : (cubeCP.bdry (mBox r (germMesh i)) (k + 2)).X //
      ¬cube.Rest (mBox r (germMesh i) + 1) x.1.1}) ↦ facePt r (germMesh i) n (k + 2) q.1.1.1)
    (fun _ ↦ rfl) (fun _ ↦ rfl) (tendsto_halfMesh) (tendsto_ofReal_mesh 16 tendsto_germMesh)
    fun i ↦ (cubeFace_ladderEquiv_propLE (mBox r (germMesh i)) k 16 (germMesh i)
      (mBox_lt hr (two_le_germMesh i)) fun _ ↦ aBox r (germMesh i)).facePt hr
        (two_le_germMesh i) hk

variable {H : Type} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  (π : ∀ i, G i →* H) [MulAction H (RoundSphere n)] [@IsIsometricSMul H (RoundSphere n) _
    (@SemigroupAction.toSMul _ _ _ MulAction.toSemigroupAction)]

/-- **The B-pair of the top-face cut is Poincaré** (realized). -/
theorem mvSeqCut_hR (k : ℕ) (hk : k + 2 ≤ n) :
    IsKarEquiv (𝟙 _) (𝟙 _)
      (dualityMap π (mvSeqCut hr n k hk).hWB (mvSeqCut hr n k hk).ladderR) := by
  have h := ControlledSeq.isKarEquiv_dualityMap π (mvSeqCut hr n k hk).hWB
    (mvSeqCut_ladderEquiv hr n k hk)
  have e : ∀ i, ((mvSeqCut_ladderEquiv hr n k hk).hom.f i).f =
      ((mvSeqCut hr n k hk).ladderR.f i).f := fun i ↦ by
    have e := congrArg BasedComplex.Hom.f (cubeFace_ladderEquiv_hom (mBox r (germMesh i)) k)
    exact e
  rwa [ControlledSeq.dualityMap_congr π _ e] at h

/-- The cut complex is the level `∂K_{k+2}`, Poincaré. -/
theorem mvSeqCut_hψ (k : ℕ) (hk : k + 2 ≤ n) :
    IsKarEquiv (𝟙 _) (𝟙 _) (dualityMap π (mvSeqCut hr n k hk).hW (mvSeqCut hr n k hk).ψ) :=
  levelPoincare hr n π (k + 2) hk

/-- The interface labels: `R ∩ F ≅ ∂K_{k+1}` preserves labels (G1). -/
theorem mvSeqCut_hl (k : ℕ) (hk : k + 2 ≤ n) (i : ℕ) (σ) :
    (facePair hr n (k + 1) (by omega)).Bd.label i
        ((cubeFace_sigIso (mBox r (germMesh i)) k).toEquiv σ) =
      (mvSeqCut hr n k hk).W.label i σ.1 := by
  change cubeLabel r (germMesh i) n (k + 1)
      ((cubeFace_sigIso (mBox r (germMesh i)) k).toEquiv σ).1.1 =
    cubeLabel r (germMesh i) n (k + 2) σ.1.1.1
  rw [cubeFace_sigIso_label]
  obtain ⟨⟨⟨⟨x₀, x'⟩, c⟩, hb⟩, hR, hT⟩ := σ
  change x₀ = _ at hT
  subst hT
  exact (cubeLabel_topEmb (by omega) x').symm

/-! ### Supports of the hemisphere cut (G6, G7) -/

section Supports

variable (hr1 : r ≤ 1)

include hr1

theorem mvSeqCut_W_near (k : ℕ) (hk : k + 2 ≤ n) :
    (mvSeqCut hr n k hk).W.LabelsNear (chartV '' cubeBdryV r (n - (k + 2))) :=
  labelsNear_bd hr hr1 n (k + 2) hk

theorem mvSeqCut_WA_near (k : ℕ) (hk : k + 2 ≤ n) :
    (mvSeqCut hr n k hk).WA.LabelsNear (chartV '' cubeRestV r (n - (k + 2))) :=
  labelsNear_of_face hr hr1 n (A := (mvSeqCut hr n k hk).WA) (j := k + 2) (fun _ σ ↦ σ.1.1.1)
    (fun _ _ ↦ rfl) (fun i x ↦ cube.Rest (mBox r (germMesh i) + 1) x) (fun _ σ ↦ σ.2) _
    (clampV_mem_rest hr hr1 (k := k + 1) hk)

theorem mvSeqCut_Bd_near (k : ℕ) (hk : k + 2 ≤ n) :
    (mvSeqCut hr n k hk).Apair.Bd.LabelsNear
      (chartV '' cubeRestV r (n - (k + 2)) ∩ chartV '' cubeFaceV r (n - (k + 1))) :=
  LabelsNear.mono (labelsNear_of_face hr hr1 n (A := (mvSeqCut hr n k hk).Apair.Bd) (j := k + 2)
    (fun _ σ ↦ σ.1.1.1.1) (fun _ _ ↦ rfl)
    (fun i x ↦ cube.Rest (mBox r (germMesh i) + 1) x ∧ cube.Top (mBox r (germMesh i) + 1) x)
    (fun _ σ ↦ ⟨σ.1.2, σ.2⟩) (cubeRestV r (n - (k + 2)) ∩ cubeFaceV r (n - (k + 1)))
    (by
      filter_upwards [clampV_mem_rest hr hr1 (k := k + 1) hk, clampV_mem_top hr hr1 (k := k + 1) hk]
        with i h₁ h₂ x hx
      exact ⟨h₁ x hx.1, h₂ x hx.2⟩)) (Set.image_inter_subset _ _ _)

theorem mvSeqCut_WnA_near (k : ℕ) (hk : k + 2 ≤ n) :
    (mvSeqCut hr n k hk).WnA.LabelsNear (chartV '' cubeFaceV r (n - (k + 1))) :=
  labelsNear_of_face hr hr1 n (A := (mvSeqCut hr n k hk).WnA) (j := k + 2) (fun _ σ ↦ σ.1.1.1)
    (fun _ _ ↦ rfl) (fun i x ↦ cube.Top (mBox r (germMesh i) + 1) x)
    (fun _ σ ↦ (cubeFace.cover _ k σ.1).resolve_left σ.2) _
    (clampV_mem_top hr hr1 (k := k + 1) hk)

end Supports

/-! ### The hemisphere step -/

/-- The realized level `∂K_j` with its boundary structure, in `𝒜(Sⁿ)`. -/
abbrev levelAmb (j : ℕ) (hj : j ≤ n) :
    SymPoincare (asymptoticInvCat π (RoundSphere n)).inv
      (((facePair hr n j hj).N : ℕ) : ℤ) :=
  (symPoincareOf π (facePair hr n j hj).hBd (facePair hr n j hj).bdHom
    (facePair hr n j hj).bdHom_symm (levelPoincare hr n π j hj)).map
      (asymptoticQuotInv π (RoundSphere n))

/-- **The hemisphere step on the cube flag**: the `k`-th hemisphere boundary of the level
`[∂K_{k+2}]` (near `Y'`) is `-bsign` times the level `[∂K_{k+1}]` (near `Y`). -/
theorem mvStep_cube (hr1 : r ≤ 1) (𝕃 : LowerLTheory) (k : ℕ) (hk : k + 2 ≤ n)
    {a b Y Y' : Set (RoundSphere n)} (ha : IsClosedInv H a) (hb : IsClosedInv H b)
    (hY : IsClosedInv H Y) (hY' : IsClosedInv H Y') (hsucc : Y' ⊆ a ∪ b) (hinter : a ∩ b ⊆ Y)
    (hYe : chartV '' cubeBdryV r (n - (k + 1)) ⊆ Y)
    (hY'e : chartV '' cubeBdryV r (n - (k + 2)) ⊆ Y')
    (hae : chartV '' cubeRestV r (n - (k + 2)) ⊆ a)
    (hbe : chartV '' cubeFaceV r (n - (k + 1)) ⊆ b) :
    𝕃.map (supportIncl hinter) ((k + 4 : ℕ) : ℤ) (mvBdry41 π 𝕃 ha hb ((k + 4 : ℕ) : ℤ)
      (𝕃.map (supportIncl hsucc) (((k + 4 : ℕ) : ℤ) + 1) (𝕃.cls _ (((k + 4 : ℕ) : ℤ) + 1)
        (Lconc.cls ((levelAmb hr n π (k + 2) hk).lift (SeqCut.supp_mapC π hY'
          ((labelsNear_bd hr hr1 n (k + 2) hk).mono hY'e))))))) =
      (-𝕃.bsign ((k + 4 : ℕ) : ℤ)) • 𝕃.cls _ ((k + 4 : ℕ) : ℤ) (Lconc.cls
        ((levelAmb hr n π (k + 1) (by omega)).lift (SeqCut.supp_mapC π hY
          ((labelsNear_bd hr hr1 n (k + 1) (by omega)).mono hYe)))) :=
  (mvSeqCut hr n k hk).mvStep π 𝕃 (mvSeqCut_hψ hr n π k hk) (mvSeqCut_hR hr n π k hk) ha hb hY hY'
    hsucc hinter ((mvSeqCut_W_near hr n hr1 k hk).mono hY'e)
    ((mvSeqCut_WA_near hr n hr1 k hk).mono hae)
    ((mvSeqCut_Bd_near hr n hr1 k hk).mono (Set.inter_subset_inter hae hbe))
    ((mvSeqCut_WnA_near hr n hr1 k hk).mono hbe) (facePair hr n (k + 1) (by omega)).bdHom_symm
    (levelPoincare hr n π (k + 1) (by omega)) (fun i ↦ cubeFace_sigIso (mBox r (germMesh i)) k)
    (mvSeqCut_hl hr n k hk) (fun i σ τ ↦ cubeFace_sigIso_bdHom (mBox r (germMesh i)) k σ τ)
    ((labelsNear_bd hr hr1 n (k + 1) (by omega)).mono hYe)

end HSFormal.Cubical.BasedComplex.CubeGeom
