import HSFormal.Cubical.PinchFace

/-!
# Local inverses of the cube pair dualities (cubical module C8, controlled B-pairs)

`interval.relDuality` inverts the relative cap `F : C^{1-*}(I, ∂I) → C(I)` by `g = e₀^* ε`, which
is global: in the box of the cut its propagation is the side length of the box, which stays
fixed while the mesh tends to `0`.  So the cube pair dualities of `GridPair` are homotopy
equivalences but not controlled ones, and cannot make the B-pair of a cut Poincaré in the
controlled categories.  Here `F` gets a **local** inverse:

* `g(v_k) = e_k^*` (`k ≤ m`), `g(v_{m+1}) = e_m^*`, `g(e_i) = v_{i+1}^*` (`i < m`), `g(e_m) = 0`;
* `g F = 1` exactly, and `F g - 1 = d h + h d` with the single entry `h(v_{m+1}) = -e_m`
  (`interval.relDualityLoc`).

Every entry of `g` and `h` joins a cell to a face or coface.  Symmetrizing along the same local
flip homotopy as `GridPair` and transposing gives `interval.symAbsDualityLoc` with the *same*
chain map as `interval.symAbsDuality` (`interval.symAbsDualityLoc_hom`), and the tensor products
`cube.symAbsDualityLoc`, `cubeCP.symAbsDualityLoc` with the same maps as the C4 B-pair dualities
(`cube.symAbsDualityLoc_hom_f`).  Hence the B-pair map of the box cut
(`torusCP.boxCut_ladderRight_apply`) has a local inverse.
-/

noncomputable section

namespace HSFormal.Cubical

open Matrix
open scoped Kronecker

namespace BasedComplex

section Interval

variable (m : ℕ)

theorem fin_last_ne_castSucc (e : Fin (m + 1)) : Fin.last (m + 1) ≠ e.castSucc := fun h ↦ by
  have := congrArg Fin.val h; simp at this; omega

theorem fin_last_eq_succ_iff (e : Fin (m + 1)) : Fin.last (m + 1) = e.succ ↔ e = Fin.last m := by
  rw [Fin.ext_iff, Fin.ext_iff]; simp [eq_comm]

/-- The local inverse `g` on all cells (rows: cochains, columns: chains). -/
def interval.locG : Matrix (interval (m + 1)).X (interval (m + 1)).X ℚ :=
  Matrix.of fun τ σ ↦ match τ, σ with
    | .inr e, .inl v => (if v = e.castSucc then 1 else 0) +
        (if e = Fin.last m ∧ v = Fin.last (m + 1) then 1 else 0)
    | .inl w, .inr e => if w = e.succ ∧ w ≠ Fin.last (m + 1) then 1 else 0
    | _, _ => 0

/-- The relative cap `F` on all cells (zero on the end columns). -/
def interval.capFull : Matrix (interval (m + 1)).X (interval (m + 1)).X ℚ :=
  Matrix.of fun τ σ ↦ match τ, σ with
    | .inl v, .inr e => if v = e.castSucc then 1 else 0
    | .inr e, .inl v => if v = e.succ ∧ v ≠ Fin.last (m + 1) then 1 else 0
    | _, _ => 0

/-- The homotopy `h(v_{m+1}) = -e_m`. -/
def interval.locH : Matrix (interval (m + 1)).X (interval (m + 1)).X ℚ :=
  Matrix.of fun τ σ ↦ match τ, σ with
    | .inr e, .inl v => if e = Fin.last m ∧ v = Fin.last (m + 1) then -1 else 0
    | _, _ => 0

theorem interval.capRel_f_eq (σ : (interval (m + 1)).X) (τ : (interval.rel m).X) :
    (interval.capRel m).f σ τ = interval.capFull m σ τ.1 := by
  rw [interval.capRel_f]
  obtain ⟨τ, hτ⟩ := τ
  simp only [interval.IsEnd, not_or] at hτ
  rcases σ with v | e <;> rcases τ with w | f
  · rfl
  · rfl
  · have hw : w ≠ Fin.last (m + 1) := fun h ↦ hτ.2 (by rw [h])
    simp [interval.capFull, hw]
  · rfl

theorem interval.locG_end {κ σ : (interval (m + 1)).X} (h : interval.locG m κ σ ≠ 0) :
    ¬interval.IsEnd m κ := by
  rintro (rfl | rfl) <;> rcases σ with v | e <;>
    simp [interval.locG, (Fin.succ_ne_zero _).symm] at h

/-- `g F = 1` on the relative cells. -/
theorem interval.locG_mul_capFull (τ σ : (interval (m + 1)).X) (hτ : ¬interval.IsEnd m τ)
    (hσ : ¬interval.IsEnd m σ) :
    (interval.locG m * interval.capFull m) τ σ = if τ = σ then 1 else 0 := by
  simp only [interval.IsEnd, not_or] at hτ hσ
  rcases τ with v | e <;> rcases σ with w | f <;>
    simp [mul_apply, Fintype.sum_sum_type, interval.locG, interval.capFull] at hτ hσ ⊢
  · simp only [hσ.2, hτ.2, not_false_eq_true, and_true]
    rw [sum_ite_succ_eq, dif_neg hσ.1, Fin.succ_pred]
  · simp [eq_comm]

/-- `F g - 1 = d h + h d` on all cells. -/
theorem interval.capFull_mul_locG : interval.capFull m * interval.locG m - 1 =
    (interval (m + 1)).d * interval.locH m + interval.locH m * (interval (m + 1)).d := by
  ext τ σ
  rcases τ with v | e <;> rcases σ with w | f <;>
    simp [mul_apply, Fintype.sum_sum_type, interval.locG, interval.capFull, interval.locH,
      one_apply]
  all_goals simp only [ite_and]
  all_goals simp [Finset.sum_ite_eq', sum_ite_castSucc_eq]
  · by_cases hv : v = Fin.last (m + 1)
    · subst hv
      by_cases hw : w = Fin.last (m + 1)
      · subst hw; simp [fin_last_ne_castSucc m _]
      · simp [hw, Ne.symm hw]
    · rw [dif_neg hv]
      have e₁ : v.castPred hv = Fin.last m ↔ v = (Fin.last m).castSucc :=
        ⟨fun h ↦ by rw [← h, Fin.castSucc_castPred], fun h ↦ by simp [h]⟩
      by_cases hw : w = Fin.last (m + 1)
      · subst hw; simp [e₁, hv, Ne.symm hv]
      · simp [hw, eq_comm]
  · by_cases he : e = Fin.last m
    · subst he
      simp [fin_last_eq_succ_iff, eq_comm]
    · simp [he]
      by_cases hf : f = e
      · simp [hf, he]
      · simp [hf, Ne.symm hf]

/-- `g` is a chain map (full form). -/
theorem interval.dual_mul_locG (τ σ : (interval (m + 1)).X) (hτ : ¬interval.IsEnd m τ) :
    ∑ κ, -((-1 : ℚ) ^ (interval (m + 1)).deg κ * (interval (m + 1)).d κ τ) *
      interval.locG m κ σ = (interval.locG m * (interval (m + 1)).d) τ σ := by
  simp only [interval.IsEnd, not_or] at hτ
  rcases τ with v | e <;> rcases σ with w | f <;>
    simp [mul_apply, Fintype.sum_sum_type, interval.locG] at hτ ⊢
  simp only [ite_and]
  simp [Finset.sum_ite_eq']
  simp only [add_mul, mul_sub, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  simp [Finset.sum_ite_eq']
  have hfe : f.succ = e.castSucc → f ≠ Fin.last m := fun h h' ↦ by
    subst h'; have := congrArg Fin.val h; simp at this; omega
  by_cases he : e = Fin.last m
  · subst he
    by_cases hf : f = Fin.last m
    · subst hf; simp [eq_comm]
    · simp [hf, Ne.symm hf, fin_last_eq_succ_iff, eq_comm]
  · by_cases hf : f = Fin.last m
    · subst hf
      simp [he]
    · by_cases h1 : f = e
      · subst h1; simp [hf, eq_comm]
      · simp [hf, he, h1, Ne.symm h1, eq_comm]

/-- **The local inverse** `g : C(I) → C^{1-*}(I, ∂I)` of the relative cap. -/
def interval.gLoc : Hom (interval (m + 1)) ((interval.rel m).dual 1 (interval.dimLE_rel m)) where
  f := (interval.locG m).submatrix Subtype.val id
  deg0 τ σ h := by
    obtain ⟨τ, hτ⟩ := τ
    change ((1 - (interval (m + 1)).deg τ : ℕ) : ℤ) = ((interval (m + 1)).deg σ : ℤ) + 0
    rcases τ with v | e <;> rcases σ with w | f <;>
      simp [interval.locG] at h ⊢
  comm := by
    ext τ σ
    rw [mul_apply, show ((interval.locG m).submatrix Subtype.val id * (interval (m + 1)).d) τ σ =
      (interval.locG m * (interval (m + 1)).d) τ.1 σ from rfl,
      ← interval.dual_mul_locG m τ.1 σ τ.2, ← sum_subtype_eq (P := fun κ ↦
      ¬interval.IsEnd m κ) _ fun κ h ↦ interval.locG_end m (right_ne_zero_of_mul h)]
    refine Finset.sum_congr rfl fun κ _ ↦ ?_
    rw [dual_d_apply]
    simp only [submatrix_apply, id]
    change (-1 : ℚ) ^ 1 * ((-1) ^ (interval (m + 1)).deg κ.1 * (interval (m + 1)).d κ.1 τ.1) *
      interval.locG m κ.1 σ = _
    ring

/-- **The relative cap with a local inverse**: `F : C^{1-*}(I, ∂I) ≃ C(I)` with `g F = 1` and the
one-entry homotopy `h(v_{m+1}) = -e_m`. -/
def interval.relDualityLoc :
    HtpyEquiv ((interval.rel m).dual 1 (interval.dimLE_rel m)) (interval (m + 1)) where
  hom := interval.capRel m
  inv := interval.gLoc m
  homInv := Htpy.ofEq <| Hom.ext <| Matrix.ext fun τ σ ↦ by
    change ∑ κ, interval.locG m τ.1 κ * (interval.capRel m).f κ σ = (1 : Matrix _ _ ℚ) τ σ
    simp only [interval.capRel_f_eq]
    rw [← mul_apply, interval.locG_mul_capFull m _ _ τ.2 σ.2, one_apply]
    exact if_congr Subtype.ext_iff.symm rfl rfl
  invHom :=
    { h := interval.locH m
      deg1 := by
        rintro (v | e) (w | f) h <;> simp [interval.locH] at h
        rfl
      eq := by
        rw [← interval.capFull_mul_locG]
        ext τ σ
        rw [Matrix.sub_apply, Matrix.sub_apply, Hom.comp_f, mul_apply, mul_apply, Hom.id_f]
        congr 1
        rw [← sum_subtype_eq (P := fun κ ↦ ¬interval.IsEnd m κ) _ fun κ h ↦
          interval.locG_end m (right_ne_zero_of_mul h)]
        refine Finset.sum_congr rfl fun κ _ ↦ ?_
        rw [interval.capRel_f_eq]
        rfl }

theorem interval.relDualityLoc_hom : (interval.relDualityLoc m).hom = interval.capRel m := rfl

/-- The symmetric pair duality `C^{1-*}(I, ∂I) ≃ C(I)` with the local inverse. -/
def interval.symRelDualityLoc :
    HtpyEquiv ((interval.rel m).dual 1 (interval.dimLE_rel m)) (interval (m + 1)) :=
  (interval.relDualityLoc m).ofHtpy (Htpy.subNull _ _ (interval.halfFlip_hasDeg m))

theorem interval.symRelDualityLoc_hom :
    (interval.symRelDualityLoc m).hom = (interval.symRelDuality m).hom := rfl

/-- The opposite symmetric pair map `C^{1-*}(I) ≃ C(I, ∂I)` with local inverse and homotopies;
the same chain map as `interval.symAbsDuality`. -/
def interval.symAbsDualityLoc :
    HtpyEquiv ((interval (m + 1)).dual 1 dimLE_oneDim) (interval.rel m) :=
  (interval.symRelDualityLoc m).transpose (interval.dimLE_rel m) dimLE_oneDim

theorem interval.symAbsDualityLoc_hom :
    (interval.symAbsDualityLoc m).hom = (interval.symAbsDuality m).hom := rfl

end Interval

/-! ### Cubes -/

theorem HtpyEquiv.dualProd_hom_f_congr : (n : ℕ) → {C D : Fin n → BasedComplex} →
    (hC : ∀ i, (C i).DimLE 1) → (e e' : ∀ i, HtpyEquiv ((C i).dual 1 (hC i)) (D i)) →
    (∀ i, (e i).hom.f = (e' i).hom.f) →
    (HtpyEquiv.dualProd n hC e).hom.f = (HtpyEquiv.dualProd n hC e').hom.f
  | 0, _, _, _, _, _, _ => rfl
  | n + 1, _, _, hC, e, e', h => by
    rw [HtpyEquiv.dualProd_succ, HtpyEquiv.dualProd_succ, HtpyEquiv.castDim_hom_f,
      HtpyEquiv.castDim_hom_f, HtpyEquiv.dualTensor_hom_f, HtpyEquiv.dualTensor_hom_f, h 0,
      HtpyEquiv.dualProd_hom_f_congr n (fun i ↦ hC i.succ) (fun i ↦ e i.succ)
        (fun i ↦ e' i.succ) fun i ↦ h i.succ]

section Cube

variable (m n : ℕ)

/-- **The controlled cube pair duality** `C^{n-*}(Iⁿ) ≃ C(Iⁿ, ∂Iⁿ)`: the tensor product of the
local interval equivalences. -/
def cube.symAbsDualityLoc :
    HtpyEquiv ((cube (m + 1) n).dual n (cube.dimLE n (m + 1))) (cubeRel m n) :=
  HtpyEquiv.dualProd n _ fun _ ↦ interval.symAbsDualityLoc m

theorem cube.symAbsDualityLoc_hom_f :
    (cube.symAbsDualityLoc m n).hom.f = (cube.symAbsDuality m n).hom.f :=
  HtpyEquiv.dualProd_hom_f_congr n _ _ _ fun _ ↦ rfl

/-- The controlled B-pair duality `C^{n+4-*}(Iⁿ ⊗ CP) ≃ C(Iⁿ, ∂Iⁿ) ⊗ CP`. -/
def cubeCP.symAbsDualityLoc :
    HtpyEquiv (((cube (m + 1) n).tensor CPcell).dual (n + 4)
      ((cube.dimLE n (m + 1)).tensor CPcell.dimLE)) ((cubeRel m n).tensor CPcell) :=
  (cube.symAbsDualityLoc m n).dualTensor CPcell.duality.toHtpyEquiv

theorem cubeCP.symAbsDualityLoc_hom_f :
    (cubeCP.symAbsDualityLoc m n).hom.f = (cubeCP.symAbsDuality m n).hom.f := by
  rw [cubeCP.symAbsDualityLoc, cubeCP.symAbsDuality, HtpyEquiv.dualTensor_hom_f,
    HtpyEquiv.dualTensor_hom_f, cube.symAbsDualityLoc_hom_f]

end Cube

end BasedComplex

end HSFormal.Cubical
