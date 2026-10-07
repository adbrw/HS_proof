import HSFormal.Cubical.CubeEnd

/-!
# The cut steps of the cube flag and `PinchSignature` (cubical module C8, Lemma 11.2)

For control data `cd` (radius `r = r_Q`, sphere `Sⁿ`, scalar group `C_p`) the classes
`x k = [∂K_{k+1}] ∈ L_{k+4}(𝒜_{Y k}(Sⁿ))` of the levels of the cube flag (`CubeLevels`) satisfy
the exterior cut equation (`extStep_cube`), the hemisphere cut equations (`mvStep_cube`) and the
last stage (`endStep`, `EndClass`): **`cubeCutSteps : CubeCutSteps' 𝕃 cd`**, hence
**`pinchSignature : PinchSignature (fibreSignatureOf 𝕃 cubeFlagChoice) manifoldGerm`**
(`pinchSignature_of_cutSteps'`).
-/

noncomputable section

namespace HSFormal

open Filter Matrix Metric Topology HSFormal.RoundSphere HSFormal.LTheory CategoryTheory
  HSFormal.Cubical HSFormal.Cubical.BasedComplex HSFormal.Cubical.BasedComplex.CubeGeom
  AsymptoticCategory
open scoped ENNReal

namespace LTheory.CutFlag

variable {H : Type} [Group H] {X : Type} [MulAction H X] [PseudoEMetricSpace X] [CompactSpace X]
  [IsIsometricSMul H X] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  (π : ∀ i, G i →* H) (𝕃 : LowerLTheory) {Z : Set X} {m : ℕ} (F : CutFlag H X Z m)

theorem mvCut_castDeg (k : ℕ) {d n₁ n₂ : ℤ} (h : n₁ = n₂) (h₁ : d = n₁ + 1) (h₂ : d = n₂ + 1)
    (y : 𝕃.L (F.C π (k + 1)) d) :
    F.mvCut π 𝕃 k n₂ (𝕃.castDeg _ h₂ y) = 𝕃.castDeg _ h (F.mvCut π 𝕃 k n₁ (𝕃.castDeg _ h₁ y)) := by
  subst h
  rfl

theorem cut_castDeg {d n₁ n₂ : ℤ} (h : n₁ = n₂) (h₁ : d = n₁ + 1) (h₂ : d = n₂ + 1)
    (y : 𝕃.L (exteriorInvCat π Z) d) :
    F.cut π 𝕃 n₂ (𝕃.castDeg _ h₂ y) = 𝕃.castDeg _ h (F.cut π 𝕃 n₁ (𝕃.castDeg _ h₁ y)) := by
  subst h
  rfl

end LTheory.CutFlag

theorem LTheory.LowerLTheory.castDeg_self (𝕃 : LowerLTheory) (A : InvCat) {n : ℤ} (h : n = n)
    (x : 𝕃.L A n) : 𝕃.castDeg A h x = x := rfl

theorem CubeGeom.cast_levelAmb {r : ℝ} (hr : 0 < r) {n : ℕ} {H : Type} [Group H] {G : ℕ → Type}
    [∀ i, Group (G i)] [∀ i, Fintype (G i)] (π : ∀ i, G i →* H) [MulAction H (RoundSphere n)]
    [@IsIsometricSMul H (RoundSphere n) _
    (@SemigroupAction.toSMul _ _ _ MulAction.toSemigroupAction)]
    (𝕃 : LowerLTheory) {Y : Set (RoundSphere n)} {d : ℤ}
    (j j' : ℕ) (h : j = j') (hj : j ≤ n) (hj' : j' ≤ n)
    (hS : ∀ r', (supportKaroubiFiltration π Y).U ((levelAmb hr n π j hj).C.X r'))
    (hS' : ∀ r', (supportKaroubiFiltration π Y).U ((levelAmb hr n π j' hj').C.X r'))
    (e : ((((facePair hr n j hj).N : ℕ)) : ℤ) = d) (e' : ((((facePair hr n j' hj').N : ℕ)) : ℤ) = d) :
    𝕃.castDeg _ e (𝕃.cls (supportKaroubiFiltration π Y).sub _
      (Lconc.cls ((levelAmb hr n π j hj).lift hS))) =
    𝕃.castDeg _ e' (𝕃.cls (supportKaroubiFiltration π Y).sub _
      (Lconc.cls ((levelAmb hr n π j' hj').lift hS'))) := by
  subst h
  rfl

namespace ControlData

variable {p : ℕ} (cd : ControlData p) (𝕃 : LowerLTheory)

theorem cubeFlag_Y (k : ℕ) :
    cd.cubeFlag.Y k = chartV '' cubeBdryV cd.cubeRadius (cd.n - (k + 1)) := by
  change chartV '' cubeBdryV cd.cubeRadius (cd.n - 1 - k) = _
  rw [show cd.n - 1 - k = cd.n - (k + 1) by omega]

theorem cubeFlag_hY (k : ℕ) : IsClosedInv cd.Cp (cd.cubeFlag.Y k) :=
  cd.isClosedInv_of_isClosed (isClosed_image_chartV (isClosed_cubeBdryV _)
    fun _ hv ↦ cubeFaceV_subset _ hv.1)

/-- The level class `[∂K_{k+1}] ∈ L(𝒜_{Y k}(Sⁿ))`. -/
def levelCls (k : ℕ) (hk : k + 1 ≤ cd.n) :
    𝕃.L (cd.cubeFlag.C (scalarHom cd.Cp) k) ((((facePair cd.cubeRadius_pos cd.n (k + 1) hk).N : ℕ) : ℤ)) :=
  𝕃.cls _ _ (Lconc.cls ((levelAmb cd.cubeRadius_pos cd.n (scalarHom cd.Cp) (k + 1) hk).lift
    (SeqCut.supp_mapC (scalarHom cd.Cp) (cd.cubeFlag_hY k)
      ((labelsNear_bd cd.cubeRadius_pos cd.cubeRadius_le_one cd.n (k + 1) hk).mono
        (cd.cubeFlag_Y k).symm.subset))))

theorem levelDeg (k : ℕ) (hk : k + 1 ≤ cd.n) :
    ((((facePair cd.cubeRadius_pos cd.n (k + 1) hk).N : ℕ) : ℤ)) = (k : ℤ) + 4 := by
  change (((k + 1 + 3 : ℕ)) : ℤ) = _
  push_cast
  ring

/-- **The classes of the cut steps**: `x k = [∂K_{k+1}]` for `k ≤ n - 1`. -/
def cubeX (k : ℕ) : 𝕃.L (cd.cubeFlag.C (scalarHom cd.Cp) k) ((k : ℤ) + 4) :=
  if hk : k + 1 ≤ cd.n then 𝕃.castDeg _ (cd.levelDeg k hk) (cd.levelCls 𝕃 k hk) else 0

theorem cubeX_of_le (k : ℕ) (hk : k + 1 ≤ cd.n) :
    cd.cubeX 𝕃 k = 𝕃.castDeg _ (cd.levelDeg k hk) (cd.levelCls 𝕃 k hk) :=
  dif_pos hk

/-- **The hemisphere cut equations** for `k < n - 1` (`mvStep_cube`). -/
theorem cubeX_mvCut (k : ℕ) (hk : k < cd.n - 1) :
    cd.cubeFlag.mvCut (scalarHom cd.Cp) 𝕃 k ((k : ℤ) + 4)
      (𝕃.castDeg _ (LowerLTheory.natDeg_succ k 4) (cd.cubeX 𝕃 (k + 1))) =
    (-𝕃.bsign ((k + 4 : ℕ) : ℤ)) • cd.cubeX 𝕃 k := by
  have hk2 : k + 2 ≤ cd.n := by omega
  have hstep : cd.cubeFlag.mvCut (scalarHom cd.Cp) 𝕃 k ((k + 4 : ℕ) : ℤ)
      (𝕃.castDeg _ (rfl : ((((facePair cd.cubeRadius_pos cd.n (k + 1 + 1) (by omega)).N : ℕ) : ℤ)) =
        ((k + 4 : ℕ) : ℤ) + 1) (cd.levelCls 𝕃 (k + 1) (by omega))) =
      (-𝕃.bsign ((k + 4 : ℕ) : ℤ)) • cd.levelCls 𝕃 k (by omega) := by
    have ha := cd.cubeFlag.ha k
    have hb := cd.cubeFlag.hb k
    exact mvStep_cube cd.cubeRadius_pos cd.n (scalarHom cd.Cp) cd.cubeRadius_le_one 𝕃 k hk2 ha hb
      (cd.cubeFlag_hY k) (cd.cubeFlag_hY (k + 1)) (cd.cubeFlag.succ k) (cd.cubeFlag.inter k)
      (cd.cubeFlag_Y k).symm.subset (cd.cubeFlag_Y (k + 1)).symm.subset
      (by
        change chartV '' cubeRestV cd.cubeRadius (cd.n - (k + 2)) ⊆
          chartV '' cubeRestV cd.cubeRadius (cd.n - 2 - k)
        rw [show cd.n - 2 - k = cd.n - (k + 2) by omega])
      (by
        change chartV '' cubeFaceV cd.cubeRadius (cd.n - (k + 1)) ⊆
          chartV '' cubeFaceV cd.cubeRadius (cd.n - 1 - k)
        rw [show cd.n - 1 - k = cd.n - (k + 1) by omega])
  rw [cd.cubeX_of_le 𝕃 (k + 1) (by omega), cd.cubeX_of_le 𝕃 k (by omega), 𝕃.castDeg_trans,
    LTheory.CutFlag.mvCut_castDeg (scalarHom cd.Cp) 𝕃 cd.cubeFlag k
      (d := (((facePair cd.cubeRadius_pos cd.n (k + 1 + 1) (by omega)).N : ℕ) : ℤ))
      (show ((k + 4 : ℕ) : ℤ) = (k : ℤ) + 4 by push_cast; ring) rfl]
  refine (congrArg (𝕃.castDeg _ _) hstep).trans ?_
  rw [Units.smul_def]
  exact (map_zsmul _ _ _).trans (Units.smul_def _ _).symm

theorem cubeBdry_zero_subset :
    chartV '' cubeBdryV cd.cubeRadius (cd.n - cd.n) ⊆ cd.cubeFlag.A ∩ cd.cubeFlag.B := by
  rintro _ ⟨v, ⟨hv, i, -, hi⟩, rfl⟩
  rw [Nat.sub_self] at hv
  refine ⟨fun w hw ↦ ?_, ⟨v, hv, rfl⟩⟩
  rw [chartV_injective hw]
  calc cd.cubeRadius = |v i| := hi.symm
    _ = ‖v i‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖v‖ := norm_le_pi_norm v i

/-- **The exterior cut equation** (`extStep_cube`). -/
theorem cubeX_cut :
    cd.cubeFlag.cut (scalarHom cd.Cp) 𝕃 (((cd.n - 1 : ℕ) : ℤ) + 4)
      (𝕃.castDeg _ cd.N_eq (germClass 𝕃 cd)) =
    (-𝕃.bsign ((cd.n + 3 : ℕ) : ℤ)) • cd.cubeX 𝕃 (cd.n - 1) := by
  have hn := cd.n_pos
  have hk : cd.n - 1 + 1 ≤ cd.n := by omega
  have hg : germClass 𝕃 cd = 𝕃.cls _ cd.N (Lconc.cls
      (((germDual cd.n).toAsymptotic (scalarHom cd.Cp)).map
        (supportKaroubiFiltration (scalarHom cd.Cp) cd.Z₀).proj)) := by
    rw [germClass, manifoldGerm_def, Lconc.map_cls]
    rfl
  have hYe : chartV '' cubeBdryV cd.cubeRadius (cd.n - cd.n) ⊆ cd.cubeFlag.Y (cd.n - 1) := by
    rw [cd.cubeFlag_Y, show cd.n - (cd.n - 1 + 1) = cd.n - cd.n by omega]
  have hstep : cd.cubeFlag.cut (scalarHom cd.Cp) 𝕃 ((cd.n + 3 : ℕ) : ℤ)
      (𝕃.castDeg _ (rfl : cd.N = ((cd.n + 3 : ℕ) : ℤ) + 1) (germClass 𝕃 cd)) =
      (-𝕃.bsign ((cd.n + 3 : ℕ) : ℤ)) • 𝕃.cls _ ((cd.n + 3 : ℕ) : ℤ) (Lconc.cls
        ((levelAmb cd.cubeRadius_pos cd.n (scalarHom cd.Cp) cd.n le_rfl).lift
          (SeqCut.supp_mapC (scalarHom cd.Cp) (cd.cubeFlag_hY (cd.n - 1))
            ((labelsNear_bd cd.cubeRadius_pos cd.cubeRadius_le_one cd.n cd.n le_rfl).mono
              hYe)))) := by
    rw [hg]
    exact extStep_cube cd.cubeRadius_pos cd.n (scalarHom cd.Cp) cd.cubeRadius_le_one 𝕃
      cd.cubeFlag.hA cd.cubeFlag.hB cd.cubeFlag.hZ (cd.cubeFlag_hY (cd.n - 1)) cd.cubeFlag.cover
      cd.cubeFlag.ZA cd.cubeFlag.ZB cd.cubeFlag.top (fun _ hz ↦ hz)
      (by
        change chartV '' cubeFaceV cd.cubeRadius (cd.n - cd.n) ⊆
          chartV '' cubeFaceV cd.cubeRadius 0
        rw [Nat.sub_self])
      cd.cubeBdry_zero_subset hYe
  rw [LTheory.CutFlag.cut_castDeg (scalarHom cd.Cp) 𝕃 cd.cubeFlag (d := cd.N)
    (show ((cd.n + 3 : ℕ) : ℤ) = ((cd.n - 1 : ℕ) : ℤ) + 4 by omega) rfl]
  refine (congrArg (𝕃.castDeg _ _) hstep).trans ?_
  rw [Units.smul_def, map_zsmul, ← Units.smul_def, cd.cubeX_of_le 𝕃 (cd.n - 1) hk]
  congr 1
  exact CubeGeom.cast_levelAmb cd.cubeRadius_pos (scalarHom cd.Cp) 𝕃 _ _ (by omega) _ _ _ _ _ _

/-- **The last stage** (`endStep`, `EndClass`): `σ_tail` of the positive end of `[∂K_1]`. -/
theorem cubeX_last :
    IsSignTail (𝕃.σtail (scalarHom cd.Cp)
      (𝕃.map ((supportKaroubiFiltration (scalarHom cd.Cp) cd.cubeFlag.P).incl ≫
        forgetControl (scalarHom cd.Cp) (RoundSphere cd.n)) 4
        (projSep 𝕃 cd.cubeFlag.hP cd.cubeFlag.hQ cd.cubeFlag.PY cd.cubeFlag.QY cd.cubeFlag.YPQ
          cd.cubeFlag.PQ 4 (𝕃.castDeg _ (by simp) (cd.cubeX 𝕃 0))))) := by
  have h1 : 1 ≤ cd.n := cd.n_pos
  have hYe : chartV '' cubeBdryV cd.cubeRadius (cd.n - 1) ⊆ cd.cubeFlag.Y 0 := by
    rw [cd.cubeFlag_Y]
  have hz := endStep cd.cubeRadius_pos cd.n h1 (scalarHom cd.Cp) cd.cubeRadius_le_one 𝕃
    cd.cubeFlag.hP cd.cubeFlag.hQ (cd.cubeFlag_hY 0) cd.cubeFlag.PY cd.cubeFlag.QY
    cd.cubeFlag.YPQ cd.cubeFlag.PQ hYe le_rfl le_rfl
  have hx0 : 𝕃.castDeg _ (by simp) (cd.cubeX 𝕃 0) =
      𝕃.cls _ 4 (Lconc.cls (A := (supportKaroubiFiltration (scalarHom cd.Cp) (cd.cubeFlag.Y 0)).sub)
        (N := 4) ((levelAmb cd.cubeRadius_pos cd.n (scalarHom cd.Cp) 1 h1).lift
          (SeqCut.supp_mapC (scalarHom cd.Cp) (cd.cubeFlag_hY 0)
            ((labelsNear_bd cd.cubeRadius_pos cd.cubeRadius_le_one cd.n 1 h1).mono hYe)))) := by
    rw [cd.cubeX_of_le 𝕃 0 (by omega), 𝕃.castDeg_trans]
    rfl
  rw [hx0]
  exact 𝕃.isSignTail_σtail_map_forgetControl_cpConst _ _ (endLabel cd.cubeRadius cd.n) 1
    (by rw [one_smul]; exact hz)

/-- **The cut steps of Lemma 11.2 on the cube flag.** -/
def cubeCutSteps : CubeCutSteps' 𝕃 cd where
  x := cd.cubeX 𝕃
  u₀ := -𝕃.bsign ((cd.n + 3 : ℕ) : ℤ)
  u k := -𝕃.bsign ((k + 4 : ℕ) : ℤ)
  cut := cd.cubeX_cut 𝕃
  mvCut k hk := cd.cubeX_mvCut 𝕃 k hk
  last := cd.cubeX_last 𝕃

end ControlData

variable (𝕃 : LowerLTheory)

/-- **`PinchSignature`** (Lemma 11.2, (11.4)–(11.5)) for the cube flag and the cubical manifold
germ, for every lower L-theory. -/
theorem pinchSignature : PinchSignature (fibreSignatureOf 𝕃 cubeFlagChoice) manifoldGerm :=
  pinchSignature_of_cutSteps' 𝕃 fun _ _ cd ↦ ⟨cd.cubeCutSteps 𝕃⟩

end HSFormal
