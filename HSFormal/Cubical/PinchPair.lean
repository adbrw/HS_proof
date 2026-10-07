import HSFormal.Cubical.PinchFlag

/-!
# Cut pairs of a local symmetric duality (cubical module C8, part 2)

Let `φ : W^{N+1-*} → W` be a strictly symmetric duality chain map of a based complex `W` and
`W = A ∪ B` a cover by subcomplexes for which `φ` is local in both directions (the hypotheses of
the excision ladder, `torusCP.boxCut_local`).  Write `Σ = A ∩ B`.

* `cutTop φ P`: the relative top structure of the pair `(W_P, ∂)`, the restriction of `φ` to
  the cells of `P`; for `P = A` it is the relative structure whose relative cap is the left column
  `ladderLeft` of the ladder, for `P = B` the right column `ladderRight` (the B-pair of
  `PinchFlag`).
* `cutDefect φ P = d T - T δ` (in dimension `N + 1`) is given by the cells off `P`
  (`cutDefect_apply`); for `P = A` or `P = B` it vanishes off `Σ × Σ` (`cutDefect_ne_zero`), so it
  is `j φ_Σ j^*` for the **boundary structure** `cutBd hW φ P S` on `Σ`, a strictly symmetric chain
  map `Σ^{N-*} → Σ` (`cutBdHom`, `isSymm_cutBdHom`).  This is the relative boundary equation
  `j φ_Σ j^* = d δφ + δφ δ` of a `SymPair` with `δφ = cutTop`.
* **The two sides have opposite boundaries up to homotopy** (`cutBdHtpy`):
  `φ_Σ^A ≃ -φ_Σ^B` with the explicit homotopy `cutTop φ Σ` (`t_W = t_A + t_B - t_Σ`, l. 950–958).
  Hence after Lemma 4.1 the cut boundary of `[W]` may be computed with the B-pair's boundary
  structure, which for the box cut is a tensor product.
-/

noncomputable section

namespace HSFormal.Cubical

open Matrix
open scoped Kronecker

namespace BasedComplex

variable {W : BasedComplex} {N : ℕ} (hW : W.DimLE (N + 1)) (φ : Hom (W.dual (N + 1) hW) W)

/-! ### Top structures and their defects -/

section Defect

variable (P : W.X → Prop) [DecidablePred P] (hP : W.IsLocallyClosed P)

/-- The relative top structure of `(W_P, ∂)`: `φ` restricted to the cells of `P`. -/
def cutTop : Matrix {σ // P σ} {σ // P σ} ℚ := φ.f.submatrix Subtype.val Subtype.val

/-- The defect `d T - T δ` of the top structure, in dimension `N + 1`. -/
def cutDefect : Matrix {σ // P σ} {σ // P σ} ℚ :=
  (W.restrict P hP).d * cutTop hW φ P -
    cutTop hW φ P * ((W.restrict P hP).dual (N + 1) (hW.restrict P hP)).d

/-- The defect is carried by the cells off `P`, since `φ` is a chain map. -/
theorem cutDefect_apply (σ τ : {σ // P σ}) :
    cutDefect hW φ P hP σ τ = ∑ κ, if P κ then 0 else
      (φ.f σ.1 κ * (W.dual (N + 1) hW).d κ τ.1 - W.d σ.1 κ * φ.f κ τ.1) := by
  have hc := congr_fun (congr_fun φ.comm σ.1) τ.1
  simp only [mul_apply] at hc
  have h1 := Fintype.sum_subtype_add_sum_subtype P (fun κ ↦ W.d σ.1 κ * φ.f κ τ.1)
  have h2 := Fintype.sum_subtype_add_sum_subtype P
    (fun κ ↦ φ.f σ.1 κ * (W.dual (N + 1) hW).d κ τ.1)
  have h3 := Fintype.sum_subtype_add_sum_subtype P (fun κ ↦ if P κ then 0 else
      (φ.f σ.1 κ * (W.dual (N + 1) hW).d κ τ.1 - W.d σ.1 κ * φ.f κ τ.1))
  have h4 : ∑ κ : {κ // P κ}, (if P κ.1 then (0 : ℚ) else
      (φ.f σ.1 κ * (W.dual (N + 1) hW).d κ τ.1 - W.d σ.1 κ * φ.f κ τ.1)) = 0 :=
    Finset.sum_eq_zero fun κ _ ↦ ite_eq_left κ.2
  have h5 : ∑ κ : {κ // ¬P κ}, (if P κ.1 then (0 : ℚ) else
      (φ.f σ.1 κ * (W.dual (N + 1) hW).d κ τ.1 - W.d σ.1 κ * φ.f κ τ.1)) =
      ∑ κ : {κ // ¬P κ}, (φ.f σ.1 κ * (W.dual (N + 1) hW).d κ τ.1 - W.d σ.1 κ * φ.f κ τ.1) :=
    Finset.sum_congr rfl fun κ _ ↦ ite_eq_right κ.2
  rw [cutDefect, restrict_dual_d hW, Matrix.sub_apply, mul_apply, mul_apply, ← h3, h4, h5, zero_add,
    Finset.sum_sub_distrib]
  simp only [cutTop, submatrix_apply]
  linear_combination h1 - h2 + hc

variable {hW φ}

/-- The degrees of a nonzero defect entry add up to `N`. -/
theorem cutDefect_deg {σ τ : {σ // P σ}} (h : cutDefect hW φ P hP σ τ ≠ 0) :
    W.deg σ.1 + W.deg τ.1 = N := by
  rw [cutDefect_apply] at h
  obtain ⟨κ, -, hκ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  split_ifs at hκ with hPκ
  · exact (hκ rfl).elim
  have hτ := hW τ.1
  have hκ' := hW κ
  by_cases h₁ : φ.f σ.1 κ * (W.dual (N + 1) hW).d κ τ.1 = 0
  · rw [h₁, zero_sub, neg_ne_zero] at hκ
    have e₁ := W.d_deg _ _ (left_ne_zero_of_mul hκ)
    have e₂ := φ.deg0 _ _ (right_ne_zero_of_mul hκ)
    change (W.deg κ : ℤ) = ((N + 1 - W.deg τ.1 : ℕ) : ℤ) + 0 at e₂
    omega
  · have e₁ := φ.deg0 _ _ (left_ne_zero_of_mul h₁)
    have e₂ := (W.dual (N + 1) hW).d_deg _ _ (right_ne_zero_of_mul h₁)
    change (W.deg σ.1 : ℤ) = ((N + 1 - W.deg κ : ℕ) : ℤ) + 0 at e₁
    change N + 1 - W.deg τ.1 = N + 1 - W.deg κ + 1 at e₂
    omega

/-- `d 𝒟 = -𝒟 δ`: the defect is a chain map `W_P^{N-*} → W_P`. -/
theorem d_mul_cutDefect :
    (W.restrict P hP).d * cutDefect hW φ P hP =
      -(cutDefect hW φ P hP * ((W.restrict P hP).dual (N + 1) (hW.restrict P hP)).d) := by
  rw [cutDefect, Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, (W.restrict P hP).d_d,
    Matrix.zero_mul, Matrix.mul_assoc (cutTop hW φ P), ((W.restrict P hP).dual (N + 1) _).d_d,
    Matrix.mul_zero, Matrix.mul_assoc]
  abel

end Defect

/-! ### Locality: the defect lives on the interface -/

section Interface

variable {A B : W.X → Prop} [DecidablePred A] {hW φ}

/-- For a cover by subcomplexes and a local `φ`, the defect of the A-side is carried by
`Σ × Σ`. -/
theorem cutDefect_ne_zero (hA : W.IsLocallyClosed A) (hB : W.IsSub B) (hcov : ∀ σ, A σ ∨ B σ)
    (hloc : ∀ σ τ, φ.f σ τ ≠ 0 → ¬B τ → A σ) (hloc' : ∀ σ τ, φ.f σ τ ≠ 0 → ¬A τ → B σ)
    {σ τ : {σ // A σ}} (h : cutDefect hW φ A hA σ τ ≠ 0) : B σ.1 ∧ B τ.1 := by
  rw [cutDefect_apply] at h
  obtain ⟨κ, -, hκ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  split_ifs at hκ with hAκ
  · exact (hκ rfl).elim
  have hBκ := (hcov κ).resolve_left hAκ
  by_cases h₁ : φ.f σ.1 κ * (W.dual (N + 1) hW).d κ τ.1 = 0
  · rw [h₁, zero_sub, neg_ne_zero] at hκ
    refine ⟨hB _ _ (left_ne_zero_of_mul hκ) hBκ, by_contra fun hτ ↦ hAκ ?_⟩
    exact hloc _ _ (right_ne_zero_of_mul hκ) hτ
  · refine ⟨hloc' _ _ (left_ne_zero_of_mul h₁) hAκ, hB _ _ (fun h₀ ↦ ?_) hBκ⟩
    apply right_ne_zero_of_mul h₁
    rw [dual_d_apply, h₀]
    ring

end Interface


/-! ### The boundary structure on the interface -/

theorem cut_sign₁ {a b N : ℕ} (h : a + b = N) :
    ((-1 : ℚ) ^ (N + 1)) ^ a * ((-1 : ℚ) ^ (N + 1 + 1)) ^ b * ((-1) ^ (N + 1) * (-1) ^ a) =
      -1 := by
  rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← pow_add]
  calc _ = (-1 : ℚ) ^ 1 := neg_one_pow_eq_of_zmod ?_
    _ = -1 := pow_one _
  subst h
  push_cast
  generalize (a : ZMod 2) = x
  generalize (b : ZMod 2) = y
  revert x y
  decide

theorem cut_sign₂ {a b N : ℕ} (h : a + b = N) :
    ((-1 : ℚ) ^ (N + 1)) ^ a * ((-1 : ℚ) ^ (N + 1 + 1)) ^ (b + 1) =
      -((-1) ^ (N + 1) * (-1) ^ b) := by
  have e : -((-1 : ℚ) ^ (N + 1) * (-1) ^ b) = (-1) ^ (N + 1 + b + 1) := by
    ring
  rw [e, ← pow_mul, ← pow_mul, ← pow_add]
  refine neg_one_pow_eq_of_zmod ?_
  subst h
  push_cast
  generalize (a : ZMod 2) = x
  generalize (b : ZMod 2) = y
  revert x y
  decide

section Bd

section Terms

variable {hW φ}

/-- Transposition of the defect, first kind of term (a face of `σ` off the side). -/
theorem cutDefect_term₁ (hφ : IsSymm hW φ) (σ τ κ : W.X) :
    ((-1 : ℚ) ^ (N + 1)) ^ W.deg σ * (φ.f τ κ * (W.dual (N + 1) hW).d κ σ) =
      -(W.d σ κ * φ.f κ τ) := by
  rw [← (isSymm_iff φ).mp hφ τ κ, dual_d_apply]
  by_cases hd : W.d σ κ = 0
  · simp [hd]
  by_cases h0 : φ.f κ τ = 0
  · simp [h0]
  have e₁ := W.d_deg _ _ hd
  have e₂ := φ.deg0 _ _ h0
  change (W.deg κ : ℤ) = ((N + 1 - W.deg τ : ℕ) : ℤ) + 0 at e₂
  have hτ := hW τ
  have hs := cut_sign₁ (a := W.deg σ) (b := W.deg τ) (N := N) (by omega)
  linear_combination (W.d σ κ * φ.f κ τ) * hs

/-- Transposition of the defect, second kind of term. -/
theorem cutDefect_term₂ (hφ : IsSymm hW φ) (σ τ κ : W.X) :
    ((-1 : ℚ) ^ (N + 1)) ^ W.deg σ * (-(W.d τ κ * φ.f κ σ)) =
      φ.f σ κ * (W.dual (N + 1) hW).d κ τ := by
  rw [← (isSymm_iff φ).mp hφ κ σ, dual_d_apply]
  by_cases hd : W.d τ κ = 0
  · simp [hd]
  by_cases h0 : φ.f σ κ = 0
  · simp [h0]
  have e₁ := W.d_deg _ _ hd
  have e₂ := φ.deg0 _ _ h0
  change (W.deg σ : ℤ) = ((N + 1 - W.deg κ : ℕ) : ℤ) + 0 at e₂
  have hκ := hW κ
  have hs := cut_sign₂ (a := W.deg σ) (b := W.deg τ) (N := N) (by omega)
  rw [e₁]
  linear_combination (-(W.d τ κ * φ.f σ κ)) * hs

/-- The defect is `(N)`-symmetric when `φ` is symmetric. -/
theorem cutDefect_symm (hφ : IsSymm hW φ) (P : W.X → Prop) [DecidablePred P]
    (hP : W.IsLocallyClosed P) (σ τ : {σ // P σ}) :
    ((-1 : ℚ) ^ (N + 1)) ^ W.deg σ.1 * cutDefect hW φ P hP τ σ = cutDefect hW φ P hP σ τ := by
  rw [cutDefect_apply, cutDefect_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun κ _ ↦ ?_
  split_ifs
  · simp
  · rw [mul_sub, sub_eq_add_neg, ← mul_neg, cutDefect_term₁ hφ, cutDefect_term₂ hφ]
    ring

end Terms

variable (P S : W.X → Prop) [DecidablePred P] [DecidablePred S] (hP : W.IsLocallyClosed P)
  (hSP : ∀ σ, S σ → P σ)

/-- **The boundary structure** on `S ⊆ P` induced by the side `P`: the defect restricted to
`S` (for `P = A` and `S = Σ` the boundary `φ_Σ` of the A-pair). -/
def cutBd : Matrix {σ // S σ} {σ // S σ} ℚ :=
  (cutDefect hW φ P hP).submatrix (fun σ ↦ ⟨σ.1, hSP _ σ.2⟩) (fun σ ↦ ⟨σ.1, hSP _ σ.2⟩)

omit [DecidablePred S] in
theorem cutBd_apply (σ τ : {σ // S σ}) :
    cutBd hW φ P S hP hSP σ τ = ∑ κ, if P κ then 0 else
      (φ.f σ.1 κ * (W.dual (N + 1) hW).d κ τ.1 - W.d σ.1 κ * φ.f κ τ.1) :=
  cutDefect_apply hW φ P hP _ _

omit [DecidablePred S] in
theorem sum_subtype_of_supp (f : {σ // P σ} → ℚ) (hf : ∀ κ, f κ ≠ 0 → S κ.1)
    [DecidablePred S] : ∑ κ : {σ // S σ}, f ⟨κ.1, hSP _ κ.2⟩ = ∑ κ, f κ := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun κ : {σ // P σ} ↦ S κ.1) f,
    Finset.sum_eq_zero (s := Finset.univ) (f := fun κ : {κ : {σ // P σ} // ¬S κ.1} ↦ f κ)
      fun κ _ ↦ by_contra fun h ↦ κ.2 (hf _ h), add_zero]
  exact Fintype.sum_equiv
    ⟨fun σ ↦ ⟨⟨σ.1, hSP _ σ.2⟩, σ.2⟩, fun κ ↦ ⟨κ.1.1, κ.2⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩ _ _
    fun _ ↦ rfl

variable (hS : W.IsSub S) (hSN : (W.restrict S hS.isLocallyClosed).DimLE N)

/-- The boundary structure as a chain map `Σ^{N-*} → Σ`, given that the defect of the side `P`
lives on `S × S`. -/
def cutBdHom (hsupp : ∀ σ τ : {σ // P σ}, cutDefect hW φ P hP σ τ ≠ 0 → S σ.1 ∧ S τ.1) :
    Hom ((W.restrict S hS.isLocallyClosed).dual N hSN) (W.restrict S hS.isLocallyClosed) where
  f := cutBd hW φ P S hP hSP
  deg0 σ τ h := by
    have h₁ := cutDefect_deg (hW := hW) (φ := φ) P hP (σ := ⟨σ.1, hSP _ σ.2⟩)
      (τ := ⟨τ.1, hSP _ τ.2⟩) h
    have h₂ := hSN τ
    change (W.deg σ.1 : ℤ) = ((N - W.deg τ.1 : ℕ) : ℤ) + 0
    change W.deg σ.1 + W.deg τ.1 = N at h₁
    change W.deg τ.1 ≤ N at h₂
    omega
  comm := by
    ext σ τ
    have hd := congr_fun (congr_fun (d_mul_cutDefect (hW := hW) (φ := φ) P hP)
      ⟨σ.1, hSP _ σ.2⟩) ⟨τ.1, hSP _ τ.2⟩
    rw [neg_apply, mul_apply, mul_apply] at hd
    rw [← sum_subtype_of_supp P S hSP (fun κ ↦ (W.restrict P hP).d ⟨σ.1, hSP _ σ.2⟩ κ *
      cutDefect hW φ P hP κ ⟨τ.1, hSP _ τ.2⟩) (fun κ h ↦ (hsupp _ _ (right_ne_zero_of_mul h)).1),
      ← sum_subtype_of_supp P S hSP (fun κ ↦ cutDefect hW φ P hP ⟨σ.1, hSP _ σ.2⟩ κ *
      ((W.restrict P hP).dual (N + 1) (hW.restrict P hP)).d κ ⟨τ.1, hSP _ τ.2⟩)
      (fun κ h ↦ (hsupp _ _ (left_ne_zero_of_mul h)).2)] at hd
    rw [mul_apply, mul_apply]
    refine (Finset.sum_congr rfl fun _ _ ↦ rfl).trans (hd.trans ?_)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun κ _ ↦ ?_
    rw [dual_d_apply, dual_d_apply]
    change -(cutDefect hW φ P hP _ _ * ((-1 : ℚ) ^ (N + 1) * ((-1) ^ W.deg τ.1 * W.d τ.1 κ.1))) =
      cutDefect hW φ P hP _ _ * ((-1) ^ N * ((-1) ^ W.deg τ.1 * W.d τ.1 κ.1))
    rw [pow_succ]
    ring

variable (hsupp : ∀ σ τ : {σ // P σ}, cutDefect hW φ P hP σ τ ≠ 0 → S σ.1 ∧ S τ.1)

theorem cutBdHom_f : (cutBdHom hW φ P S hP hSP hS hSN hsupp).f = cutBd hW φ P S hP hSP := rfl

/-- The boundary structure is strictly symmetric. -/
theorem isSymm_cutBdHom (hφ : IsSymm hW φ) : IsSymm hSN (cutBdHom hW φ P S hP hSP hS hSN hsupp) :=
  (isSymm_iff _).mpr fun σ τ ↦ cutDefect_symm hφ P hP ⟨σ.1, hSP _ σ.2⟩ ⟨τ.1, hSP _ τ.2⟩

end Bd

/-! ### The two sides of a cut have homotopic boundary structures -/

theorem IsSub.and {C : BasedComplex} {A B : C.X → Prop} (hA : C.IsSub A) (hB : C.IsSub B) :
    C.IsSub fun σ ↦ A σ ∧ B σ :=
  fun σ τ h hτ ↦ ⟨hA σ τ h hτ.1, hB σ τ h hτ.2⟩

/-- In dimension `N`, the `N`-dual differential of a restriction is minus the `(N+1)`-dual one,
so the defect `d T - T δ_{N+1}` is the homotopy expression `d T + T δ_N`. -/
theorem cutDefect_eq_htpy (P : W.X → Prop) [DecidablePred P] (hP : W.IsLocallyClosed P)
    (hPN : (W.restrict P hP).DimLE N) :
    cutDefect hW φ P hP = (W.restrict P hP).d * cutTop hW φ P +
      cutTop hW φ P * ((W.restrict P hP).dual N hPN).d := by
  rw [cutDefect, dual_d, dual_d, pow_succ, mul_neg_one, neg_smul, Matrix.mul_neg, sub_neg_eq_add]

section TwoSides

variable {A B : W.X → Prop} [DecidablePred A] [DecidablePred B] (hA : W.IsSub A)
  (hB : W.IsSub B)
  (hSN : (W.restrict (fun σ ↦ A σ ∧ B σ) (hA.and hB).isLocallyClosed).DimLE N)

include hB in
omit [DecidablePred B] in
variable {hW φ} in
/-- Support of the A-side defect (local `φ`, cover by subcomplexes). -/
theorem cutDefect_supp_left (hcov : ∀ σ, A σ ∨ B σ) (hloc : ∀ σ τ, φ.f σ τ ≠ 0 → ¬B τ → A σ)
    (hloc' : ∀ σ τ, φ.f σ τ ≠ 0 → ¬A τ → B σ) (σ τ : {σ // A σ})
    (h : cutDefect hW φ A hA.isLocallyClosed σ τ ≠ 0) : (A σ.1 ∧ B σ.1) ∧ (A τ.1 ∧ B τ.1) :=
  have h' := cutDefect_ne_zero hA.isLocallyClosed hB hcov hloc hloc' h
  ⟨⟨σ.2, h'.1⟩, ⟨τ.2, h'.2⟩⟩

include hA in
omit [DecidablePred A] in
variable {hW φ} in
/-- Support of the B-side defect. -/
theorem cutDefect_supp_right (hcov : ∀ σ, A σ ∨ B σ) (hloc : ∀ σ τ, φ.f σ τ ≠ 0 → ¬B τ → A σ)
    (hloc' : ∀ σ τ, φ.f σ τ ≠ 0 → ¬A τ → B σ) (σ τ : {σ // B σ})
    (h : cutDefect hW φ B hB.isLocallyClosed σ τ ≠ 0) : (A σ.1 ∧ B σ.1) ∧ (A τ.1 ∧ B τ.1) :=
  have h' := cutDefect_ne_zero hB.isLocallyClosed hA (fun σ ↦ (hcov σ).symm) hloc' hloc h
  ⟨⟨h'.1, σ.2⟩, ⟨h'.2, τ.2⟩⟩

/-- The defects of the two sides add up to the defect of the interface. -/
theorem cutDefect_add (hcov : ∀ σ, A σ ∨ B σ) (σ τ : {σ // A σ ∧ B σ}) :
    cutDefect hW φ A hA.isLocallyClosed ⟨σ.1, σ.2.1⟩ ⟨τ.1, τ.2.1⟩ +
      cutDefect hW φ B hB.isLocallyClosed ⟨σ.1, σ.2.2⟩ ⟨τ.1, τ.2.2⟩ =
    cutDefect hW φ (fun σ ↦ A σ ∧ B σ) (hA.and hB).isLocallyClosed σ τ := by
  rw [cutDefect_apply, cutDefect_apply, cutDefect_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun κ _ ↦ ?_
  by_cases hAκ : A κ <;> by_cases hBκ : B κ
  · simp [hAκ, hBκ]
  · simp [hAκ, hBκ]
  · simp [hAκ, hBκ]
  · exact ((hcov κ).elim hAκ hBκ).elim

/-- **The A-pair and the B-pair have opposite boundaries up to homotopy**: on `Σ = A ∩ B`,
`φ_Σ^A - (-φ_Σ^B) = d λ + λ δ` with `λ = cutTop φ Σ` (the restriction of `φ` to `Σ`). -/
def cutBdHtpy (hcov : ∀ σ, A σ ∨ B σ)
    (hsuppA : ∀ σ τ : {σ // A σ}, cutDefect hW φ A hA.isLocallyClosed σ τ ≠ 0 →
      (A σ.1 ∧ B σ.1) ∧ (A τ.1 ∧ B τ.1))
    (hsuppB : ∀ σ τ : {σ // B σ}, cutDefect hW φ B hB.isLocallyClosed σ τ ≠ 0 →
      (A σ.1 ∧ B σ.1) ∧ (A τ.1 ∧ B τ.1)) :
    Htpy (cutBdHom hW φ A (fun σ ↦ A σ ∧ B σ) hA.isLocallyClosed (fun _ h ↦ h.1) (hA.and hB) hSN
        hsuppA)
      ((cutBdHom hW φ B (fun σ ↦ A σ ∧ B σ) hB.isLocallyClosed (fun _ h ↦ h.2) (hA.and hB) hSN
        hsuppB).smul (-1)) where
  h := cutTop hW φ (fun σ ↦ A σ ∧ B σ)
  deg1 σ τ h := by
    have e := φ.deg0 _ _ h
    have := hSN τ
    change (W.deg σ.1 : ℤ) = ((N + 1 - W.deg τ.1 : ℕ) : ℤ) + 0 at e
    change W.deg τ.1 ≤ N at this
    change (W.deg σ.1 : ℤ) = ((N - W.deg τ.1 : ℕ) : ℤ) + 1
    omega
  eq := by
    rw [← cutDefect_eq_htpy hW φ _ _ hSN]
    ext σ τ
    rw [← cutDefect_add hW φ hA hB hcov σ τ]
    rw [Matrix.sub_apply]
    change cutBd hW φ A (fun σ ↦ A σ ∧ B σ) hA.isLocallyClosed (fun _ h ↦ h.1) σ τ -
      ((-1 : ℚ) • cutBd hW φ B (fun σ ↦ A σ ∧ B σ) hB.isLocallyClosed (fun _ h ↦ h.2)) σ τ = _
    simp [cutBd]

end TwoSides

end BasedComplex

end HSFormal.Cubical

end
