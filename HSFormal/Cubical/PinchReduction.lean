import HSFormal.Cubical.PinchSignature

/-!
# The corrected reduction of `PinchSignature` to cut steps (cubical module C8)

`CubeCutSteps` (`PinchSignature`) asks for the cut equation `mvCut k (x (k+1)) = u k • x k` for
**every** `k : ℕ`.  The cube flag has `m = n - 1` cuts; the step `k = n - 1` lies past the flag:
there `a (n-1) = cubeRestV r 0 ⊆ b (n-1) = cubeFaceV r 0` (the whole cube), so the
Mayer–Vietoris boundary of that degenerate cut factors through `L(𝒜_{a∪b}/𝒜_b) = 0`
(`LowerLTheory.eq_zero_of_forall_U`), `mvCut (n-1) = 0`, all `x k` (`k ≤ n - 1`) vanish, and
the field `last` would assert `IsSignTail 0`.  Hence **`CubeCutSteps 𝕃 cd` is empty**
(`CubeCutSteps.false`) and `pinchSignature_of_cutSteps` is vacuous.

The fix: `CubeCutSteps'` asks for the cut equations only for the `n - 1` cuts of the flag,
`k < n - 1`, which is all that the iterated boundary `Δ_1` uses
(`LowerLTheory.iterDown_eq_of_steps_lt`); `pinchSignature_of_cutSteps'` is the reduction.
Edge cases: `n ≥ 1` (`ControlData.n_pos`); for `n = 1` there are no cuts after the exterior one
(`n - 1 = 0`), `Y 0 = ∂Q = {±r}` and only `cut` and `last` matter.
-/

noncomputable section

open CategoryTheory

namespace HSFormal

namespace LTheory.LowerLTheory

variable (𝕃 : LowerLTheory)

/-- **Iterated cuts with the step equations only below `n`.** -/
theorem iterDown_eq_of_steps_lt (C : ℕ → InvCat) (d : ℤ)
    (f : ∀ k : ℕ, 𝕃.L (C (k + 1)) ((k : ℤ) + d + 1) →+ 𝕃.L (C k) ((k : ℤ) + d))
    (x : ∀ k : ℕ, 𝕃.L (C k) ((k : ℤ) + d)) (u : ℕ → ℤˣ) (n : ℕ)
    (hx : ∀ k < n, f k (𝕃.castDeg _ (natDeg_succ k d) (x (k + 1))) = u k • x k) :
    𝕃.iterDown C d f n (x n) =
      (∏ k ∈ Finset.range n, u k) • 𝕃.castDeg (C 0) (by simp) (x 0) := by
  induction n with
  | zero => simp [iterDown]
  | succ n ih =>
    simp only [iterDown, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
    rw [hx n (Nat.lt_succ_self n), Units.smul_def, map_zsmul,
      ih fun k hk ↦ hx k (Nat.lt_succ_of_lt hk), ← Units.smul_def, smul_smul,
      Finset.prod_range_succ, mul_comm]

/-- If every object of `A` lies in `U`, then `L(A/U) = 0`: the identity of `A/U` is the empty
unitary sum (all objects of `A/U` are zero). -/
theorem eq_zero_of_forall_U {A : InvCat} (F : KaroubiFiltration A) (hU : ∀ X, F.U X) {n : ℤ}
    (x : 𝕃.L F.quot n) : x = 0 := by
  have hz : ∀ X : F.quot, (𝟙 X : X ⟶ X) = 0 := fun X ↦
    (F.isZero_proj_obj (hU X.as)).eq_of_src _ _
  have hS : InvCat.IsFinSum (fun i : Empty ↦ i.elim) (𝟙 F.quot) :=
    { inc := fun i ↦ i.elim
      inc_star_self := fun i ↦ i.elim
      inc_star_ne := fun i ↦ i.elim
      total := fun X ↦ by
        rw [Finset.univ_eq_empty, Finset.sum_empty]; exact (hz X).symm }
  have h := 𝕃.map_finSum hS n
  rw [𝕃.map_id, Finset.univ_eq_empty, Finset.sum_empty] at h
  exact DFunLike.congr_fun h x

end LTheory.LowerLTheory

open LTheory AsymptoticCategory

variable (𝕃 : LowerLTheory)

/-- **The single cut steps of Lemma 11.2 on the cube flag** (corrected `CubeCutSteps`): the
equations of the hemisphere cuts only for the `n - 1` cuts `k < n - 1` of the flag. -/
structure CubeCutSteps' {p : ℕ} (cd : ControlData p) where
  x : ∀ k : ℕ, 𝕃.L (cd.cubeFlag.C (scalarHom cd.Cp) k) ((k : ℤ) + 4)
  u₀ : ℤˣ
  u : ℕ → ℤˣ
  cut : cd.cubeFlag.cut (scalarHom cd.Cp) 𝕃 (((cd.n - 1 : ℕ) : ℤ) + 4)
      (𝕃.castDeg _ cd.N_eq (germClass 𝕃 cd)) = u₀ • x (cd.n - 1)
  mvCut : ∀ k < cd.n - 1, cd.cubeFlag.mvCut (scalarHom cd.Cp) 𝕃 k ((k : ℤ) + 4)
      (𝕃.castDeg _ (LowerLTheory.natDeg_succ k 4) (x (k + 1))) = u k • x k
  last : IsSignTail (𝕃.σtail (scalarHom cd.Cp)
      (𝕃.map ((supportKaroubiFiltration (scalarHom cd.Cp) cd.cubeFlag.P).incl ≫
        forgetControl (scalarHom cd.Cp) (RoundSphere cd.n)) 4
        (projSep 𝕃 cd.cubeFlag.hP cd.cubeFlag.hQ cd.cubeFlag.PY cd.cubeFlag.QY cd.cubeFlag.YPQ
          cd.cubeFlag.PQ 4 (𝕃.castDeg _ (by simp) (x 0)))))

/-- **`PinchSignature` from the corrected cut steps** (Lemma 11.2, (11.4)–(11.5)). -/
theorem pinchSignature_of_cutSteps'
    (h : ∀ ⦃p : ℕ⦄ [Fact p.Prime] (cd : ControlData p), Nonempty (CubeCutSteps' 𝕃 cd)) :
    PinchSignature (fibreSignatureOf 𝕃 cubeFlagChoice) manifoldGerm := by
  intro p _ cd
  obtain ⟨S⟩ := h cd
  change IsSignTail (𝕃.σtail (scalarHom cd.Cp) (cd.delta1 𝕃 cd.cubeFlag (germClass 𝕃 cd)))
  simp only [ControlData.delta1, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  rw [CutFlag.delta_apply, S.cut, Units.smul_def, map_zsmul,
    𝕃.iterDown_eq_of_steps_lt _ 4 _ S.x S.u _ S.mvCut, Units.smul_def, map_zsmul, map_zsmul,
    map_zsmul, map_zsmul, map_zsmul, map_zsmul, ← Units.smul_def, ← Units.smul_def]
  exact (S.last.units_smul _).units_smul _

namespace ControlData

variable {p : ℕ} (cd : ControlData p)

/-- The step `k = n - 1` of `CubeCutSteps` is past the flag: `a ⊆ b` there. -/
theorem cubeFlag_a_subset_b : cd.cubeFlag.a (cd.n - 1) ⊆ cd.cubeFlag.b (cd.n - 1) := by
  intro z hz
  obtain ⟨v, hv, rfl⟩ := hz
  refine ⟨v, ?_, rfl⟩
  have h1 : cd.n - 2 - (cd.n - 1) = 0 := by omega
  have h2 : cd.n - 1 - (cd.n - 1) = 0 := by omega
  simp only [h1, h2] at hv ⊢
  exact hv.1

/-- The degenerate cut past the flag is zero. -/
theorem cubeFlag_mvCut_last (d : ℤ) (y : 𝕃.L (cd.cubeFlag.C (scalarHom cd.Cp) (cd.n - 1 + 1))
    (d + 1)) : cd.cubeFlag.mvCut (scalarHom cd.Cp) 𝕃 (cd.n - 1) d y = 0 := by
  rw [CutFlag.mvCut_apply]
  simp only [mvBdry41, LowerLTheory.mvBdryOf, MVNilpotence.mvBdry_apply]
  rw [𝕃.eq_zero_of_forall_U _ (fun X ↦ ?_) (𝕃.map _ _ _), map_zero, map_zero, map_zero]
  have h : X.obj.as.IsSupported (cd.cubeFlag.a (cd.n - 1) ∪ cd.cubeFlag.b (cd.n - 1)) := X.2
  exact AsymptoticObject.IsSupported.mono (Set.union_subset cd.cubeFlag_a_subset_b le_rfl) h

end ControlData

theorem units_smul_eq_zero {M : Type*} [AddCommGroup M] {u : ℤˣ} {x : M} (h : u • x = 0) :
    x = 0 := by
  have := congrArg (u⁻¹ • ·) h
  simpa [smul_smul] using this

/-- **`CubeCutSteps` is empty**: the step equation past the flag (`k = n - 1`) forces all
classes to vanish, and `IsSignTail 0` is false. -/
theorem CubeCutSteps.false {p : ℕ} {cd : ControlData p} (S : CubeCutSteps 𝕃 cd) : False := by
  have hx : ∀ j ≤ cd.n - 1, S.x (cd.n - 1 - j) = 0 := by
    intro j
    induction j with
    | zero =>
      intro _
      have h := S.mvCut (cd.n - 1)
      rw [cd.cubeFlag_mvCut_last 𝕃] at h
      exact units_smul_eq_zero h.symm
    | succ j ih =>
      intro hj
      have h := S.mvCut (cd.n - 1 - (j + 1))
      have e : cd.n - 1 - (j + 1) + 1 = cd.n - 1 - j := by omega
      have h' : S.x (cd.n - 1 - (j + 1) + 1) = 0 := by
        rw [e]; exact ih (by omega)
      rw [h', map_zero, map_zero] at h
      exact units_smul_eq_zero h.symm
  have h0 := hx (cd.n - 1) le_rfl
  rw [Nat.sub_self] at h0
  have h := S.last
  rw [h0, map_zero, map_zero, map_zero, map_zero] at h
  have h' : IsSignTail ((fun _ ↦ (0 : ℤ) : ℕ → ℤ) : Tail) := h
  rw [isSignTail_coe] at h'
  obtain ⟨i, hi⟩ := h'.exists
  exact not_isUnit_zero hi

end HSFormal
