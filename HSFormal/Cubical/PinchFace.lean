import HSFormal.Cubical.PinchPair

/-!
# The flag iterates on structures: cube pair tops and their boundaries (cubical module C8)

* `defect C N X = d X - X δ_N` for any matrix `X : C^{N-*} → C`; for the top `cutTop φ P` of a
  cut it is `cutDefect` (`cutDefect_eq_defect`).  **Leibniz rule** for Koszul tensors
  (`defect_kronecker`): `𝒟((X ⊗ Y) Θ) = (𝒟X ⊗ Y + sgn X ⊗ 𝒟Y) Θ` for `X` of degree `0`.
* `cubeSym m k`: the symmetric top of the cube pair `(I_{m+1}^k, ∂)`, the Koszul tensor of the
  interval matrices `interval.symMat`; it is the restriction of the torus duality to any box
  (`torus.duality_box_box`), and on relative rows it is the symmetric cube pair duality
  (`cubeSym_relInj`).  `cubeTop m k = (cubeSym ⊗ φ_CP) Θ` is the top of the B-pair
  `(I^k, ∂I^k) ⊗ CPcell`; on the box cut of `W = Tⁿ ⊗ CPcell` it is the top `cutTop φ_W W_B`
  (`torusCP.cutTop_boxIso`).
* **The flag iterates** (`defect_cubeTop_top`): the boundary structure `𝒟(cubeTop (k+1))` of the
  B-pair, restricted to the top face `F = {x₀ = m + 1} ≅ I^k ⊗ CP` (`cube.topEmb`), is
  `cubeTop k` itself, with sign `+1`: the B-pair of the next cut (inside the boundary sphere) is
  again a cube pair `⊗ CPcell`.  At the bottom of the flag, `𝒟(symMat)` is `+1` at the top vertex
  (`interval.defect_symMat_last`): the positive component `pt ⊗ CPcell` of `∂I ⊗ CPcell` carries
  exactly `φ_CP` (`defect_cubeTop_one_last`).
-/

noncomputable section

namespace HSFormal.Cubical

open Matrix
open scoped Kronecker

namespace BasedComplex

variable {C D : BasedComplex} {N M : ℕ}

/-! ### Defects and the Leibniz rule -/

/-- The defect `d X - X δ_N` of a matrix `X : C^{N-*} → C` (zero iff `X` is a chain map). -/
def defect (C : BasedComplex) (N : ℕ) (hC : C.DimLE N) (X : Matrix C.X C.X ℚ) :
    Matrix C.X C.X ℚ :=
  C.d * X - X * (C.dual N hC).d

theorem defect_congr {N' : ℕ} (hC : C.DimLE N) (h : N = N') (hC' : C.DimLE N')
    (X : Matrix C.X C.X ℚ) : defect C N hC X = defect C N' hC' X := by
  subst h; rfl

theorem cutDefect_eq_defect {W : BasedComplex} (hW : W.DimLE (N + 1))
    (φ : Hom (W.dual (N + 1) hW) W) (P : W.X → Prop) [DecidablePred P]
    (hP : W.IsLocallyClosed P) :
    cutDefect hW φ P hP = defect (W.restrict P hP) (N + 1) (hW.restrict P hP) (cutTop hW φ P) :=
  rfl

/-- Degree-`0` matrices commute with the signs: `X sgn_{C^{N-*}} = sgn_C X`. -/
theorem mul_dual_sgn (hC : C.DimLE N) {X : Matrix C.X C.X ℚ}
    (hX : ∀ σ τ, X σ τ ≠ 0 → C.deg σ + C.deg τ = N) : X * (C.dual N hC).sgn = C.sgn * X := by
  rw [dual_sgn]
  ext σ τ
  simp only [Matrix.mul_smul, Matrix.smul_apply, sgn, mul_diagonal, diagonal_mul, smul_eq_mul]
  by_cases h : X σ τ = 0
  · simp [h]
  · rw [← hX σ τ h, pow_add]
    linear_combination ((-1 : ℚ) ^ C.deg σ * X σ τ) * neg_one_pow_mul_self (C.deg τ)

/-- **Leibniz rule** for the Koszul tensor of a degree-`0` matrix with any matrix. -/
theorem defect_kronecker (hC : C.DimLE N) (hD : D.DimLE M) (X : Matrix C.X C.X ℚ)
    (Y : Matrix D.X D.X ℚ) (hX : ∀ σ τ, X σ τ ≠ 0 → C.deg σ + C.deg τ = N) :
    defect (C.tensor D) (N + M) (hC.tensor hD) ((X ⊗ₖ Y) * koszul C D M) =
      (defect C N hC X ⊗ₖ Y + (C.sgn * X) ⊗ₖ defect D M hD Y) * koszul C D M := by
  have hcomm := (dualTensor hC hD).comm
  have hk := koszul_mul_koszul (C := C) (D := D) (M := M)
  have hδ : ((C.tensor D).dual (N + M) (hC.tensor hD)).d =
      koszul C D M * (((C.dual N hC).tensor (D.dual M hD)).d * koszul C D M) := by
    change _ = koszul C D M * (((C.dual N hC).tensor (D.dual M hD)).d * (dualTensor hC hD).f)
    rw [hcomm]
    change _ = koszul C D M * (koszul C D M * _)
    rw [← Matrix.mul_assoc, hk, Matrix.one_mul]
  rw [defect, hδ]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (koszul C D M) (koszul C D M), hk, Matrix.one_mul, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc (X ⊗ₖ Y), ← Matrix.sub_mul]
  congr 1
  change (C.d ⊗ₖ (1 : Matrix D.X D.X ℚ) + C.sgn ⊗ₖ D.d) * (X ⊗ₖ Y) -
      (X ⊗ₖ Y) * ((C.dual N hC).d ⊗ₖ (1 : Matrix D.X D.X ℚ) +
        (C.dual N hC).sgn ⊗ₖ (D.dual M hD).d) = _
  rw [Matrix.add_mul, Matrix.mul_add, ← mul_kronecker_mul,
    ← mul_kronecker_mul, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul,
    Matrix.mul_one, mul_dual_sgn hC hX, defect, defect, sub_kronecker, kronecker_sub]
  abel

/-- The defect of a chain map vanishes. -/
theorem defect_hom {hC : C.DimLE N} (φ : Hom (C.dual N hC) C) : defect C N hC φ.f = 0 := by
  rw [defect, φ.comm, sub_self]

/-- Cell isomorphisms transport defects. -/
theorem defect_submatrix (e : CellIso C D) (hC : C.DimLE N) (hD : D.DimLE N)
    (X : Matrix D.X D.X ℚ) :
    defect C N hC (X.submatrix e.toEquiv e.toEquiv) =
      (defect D N hD X).submatrix e.toEquiv e.toEquiv := by
  ext σ τ
  rw [submatrix_apply, defect, defect, Matrix.sub_apply, Matrix.sub_apply, mul_apply, mul_apply, mul_apply,
    mul_apply]
  congr 1
  · rw [← Equiv.sum_comp e.toEquiv]
    refine Finset.sum_congr rfl fun κ _ ↦ ?_
    rw [submatrix_apply, e.d_eq]
  · rw [← Equiv.sum_comp e.toEquiv]
    refine Finset.sum_congr rfl fun κ _ ↦ ?_
    rw [submatrix_apply, dual_d_apply, dual_d_apply, e.d_eq, e.deg_eq]


/-! ### The symmetric tops of cube pairs -/

section Cube

variable (m : ℕ)

theorem interval.symMat_deg {x y : (interval (m + 1)).X} (h : interval.symMat m x y ≠ 0) :
    (interval (m + 1)).deg x + (interval (m + 1)).deg y = 1 := by
  rcases x with v | e <;> rcases y with w | f <;> simp_all [interval.symMat]

/-- The symmetric top of the cube pair `(I_{m+1}^k, ∂)`: the Koszul tensor of `interval.symMat`
(the restriction of the symmetrized circle caps to the box). -/
def cubeSym : (k : ℕ) → Matrix (cube (m + 1) k).X (cube (m + 1) k).X ℚ
  | 0 => 1
  | k + 1 => (interval.symMat m ⊗ₖ cubeSym k) * koszul (interval (m + 1)) (cube (m + 1) k) k

theorem cubeSym_deg : (k : ℕ) → {x y : (cube (m + 1) k).X} → cubeSym m k x y ≠ 0 →
    (cube (m + 1) k).deg x + (cube (m + 1) k).deg y = k
  | 0, _, _, _ => rfl
  | k + 1, ⟨x₀, x'⟩, ⟨y₀, y'⟩, h => by
    rw [cubeSym, koszul, mul_diagonal, kronecker_apply] at h
    have h₁ := interval.symMat_deg m (left_ne_zero_of_mul (left_ne_zero_of_mul h))
    have h₂ := cubeSym_deg k (right_ne_zero_of_mul (left_ne_zero_of_mul h))
    change ((interval (m + 1)).deg x₀ + (cube (m + 1) k).deg x') +
      ((interval (m + 1)).deg y₀ + (cube (m + 1) k).deg y') = k + 1
    omega

/-- **The torus duality on a box is the cube top** `cubeSym` (all entries, cells of the box). -/
theorem torus.duality_box_box (M : ℕ) [NeZero M] (h : m + 1 < M) : (n : ℕ) →
    (a : Fin n → Fin M) → (x y : (cube (m + 1) n).X) →
    (torus.duality M n).hom.f ((torus.boxInj M m h a).toFun x)
      ((torus.boxInj M m h a).toFun y) = cubeSym m n x y
  | 0, _, _, _ => rfl
  | n + 1, a, ⟨x₀, x'⟩, ⟨y₀, y'⟩ => by
    have ih := torus.duality_box_box M h n (fun i ↦ a i.succ) x' y'
    change (torus.duality M (n + 1)).hom.f
        ((circle.arc M (a 0) (m + 1) h).toFun x₀, (torus.boxInj M m h fun i ↦ a i.succ).toFun x')
        ((circle.arc M (a 0) (m + 1) h).toFun y₀, (torus.boxInj M m h fun i ↦ a i.succ).toFun y') =
      ((interval.symMat m ⊗ₖ cubeSym m n) * koszul (interval (m + 1)) (cube (m + 1) n) n)
        (x₀, x') (y₀, y')
    rw [torus.duality_succ_hom_f, koszul, koszul, mul_diagonal, mul_diagonal, kronecker_apply,
      kronecker_apply, ih, circle.duality_arc, (circle.arc M (a 0) (m + 1) h).deg_eq,
      (torus.boxInj M m h fun i ↦ a i.succ).deg_eq]

/-- The relative cells `C(Iᵏ, ∂Iᵏ)` inside the cube. -/
def cubeRelInj (k : ℕ) : CellInj (cubeRel m k) (cube (m + 1) k) :=
  CellInj.prod k fun _ ↦ CellInj.subtype _ (interval.isSub_isEnd m).isLocallyClosed_compl

/-- On relative rows the cube top is the symmetric cube pair duality. -/
theorem cubeSym_relInj : (k : ℕ) → (x : (cubeRel m k).X) → (y : (cube (m + 1) k).X) →
    cubeSym m k ((cubeRelInj m k).toFun x) y = (cube.symAbsDuality m k).hom.f x y
  | 0, _, _ => rfl
  | k + 1, ⟨x₀, x'⟩, ⟨y₀, y'⟩ => by
    have ih := cubeSym_relInj k x' y'
    change ((interval.symMat m ⊗ₖ cubeSym m k) * koszul (interval (m + 1)) (cube (m + 1) k) k)
        (x₀.1, (cubeRelInj m k).toFun x') (y₀, y') =
      (((interval.symAbsDuality m).dualTensor (cube.symAbsDuality m k)).castDim
        (Nat.add_comm 1 k) _).hom.f (x₀, x') (y₀, y')
    rw [HtpyEquiv.castDim_hom_f, HtpyEquiv.dualTensor_hom_f]
    simp only [koszul, mul_diagonal, kronecker_apply]
    rw [ih, interval.symAbsDuality_hom_f, interval.symMat_comm]

/-- The top `(cubeSym ⊗ φ_CP) Θ` of the B-pair `(Iᵏ, ∂Iᵏ) ⊗ CPcell`. -/
def cubeTop (k : ℕ) :
    Matrix ((cube (m + 1) k).tensor CPcell).X ((cube (m + 1) k).tensor CPcell).X ℚ :=
  (cubeSym m k ⊗ₖ CPcell.φ.f) * koszul (cube (m + 1) k) CPcell 4

/-- **The top of the box cut's B-pair is the cube top**: `cutTop φ_W W_B` at the cells of the box
`W_B ≅ Iⁿ ⊗ CP` (`torusCP.boxIso`) is `cubeTop m n`. -/
theorem torusCP.cutTop_boxIso (M : ℕ) [NeZero M] (h : m + 1 < M) {n : ℕ} (a : Fin n → Fin M)
    [DecidablePred (torusCP.WB M n a fun _ ↦ m + 1)]
    (hP : (torusCP M n).IsLocallyClosed (torusCP.WB M n a fun _ ↦ m + 1))
    (x y : ((cube (m + 1) n).tensor CPcell).X) :
    cutTop (torusCP.dimLE M n) (torusCP.duality M n).hom (torusCP.WB M n a fun _ ↦ m + 1)
      ((torusCP.boxIso M m h a hP).toEquiv x) ((torusCP.boxIso M m h a hP).toEquiv y) =
      cubeTop m n x y := by
  obtain ⟨x, c⟩ := x
  obtain ⟨y, c'⟩ := y
  rw [cutTop, submatrix_apply, torusCP.boxIso_apply, torusCP.boxIso_apply, torusCP.duality,
    SymDuality.tensor_hom_f, cubeTop, koszul, koszul, mul_diagonal, mul_diagonal,
    kronecker_apply, kronecker_apply, torus.duality_box_box, (torus.boxInj M m h a).deg_eq]
  rfl

/-- The boundary structure of the interval pair is `+1` at the top vertex. -/
theorem interval.defect_symMat_last : defect (interval (m + 1)) 1 dimLE_oneDim (interval.symMat m)
    (.inl (Fin.last _)) (.inl (Fin.last _)) = 1 := by
  have hs : ∀ e : Fin (m + 1), Fin.last (m + 1) = e.succ ↔ e = Fin.last m := fun e ↦ by
    rw [Fin.ext_iff, Fin.ext_iff]; simp [eq_comm]
  have hc : ∀ e : Fin (m + 1), Fin.last (m + 1) ≠ e.castSucc := fun e h ↦ by
    have := congrArg Fin.val h; simp at this; omega
  have h₁ : ∑ κ, (interval (m + 1)).d (.inl (Fin.last _)) κ *
      interval.symMat m κ (.inl (Fin.last _)) = 1 / 2 := by
    rw [Finset.sum_eq_single (.inr (Fin.last m))]
    · simp [interval.symMat, hc]
    · rintro (v | e) _ hκ
      · simp
      · have : e ≠ Fin.last m := fun h ↦ hκ (by rw [h])
        simp [hc, (hs e).not.mpr this]
    · simp
  have h₂ : ∑ κ, interval.symMat m (.inl (Fin.last _)) κ *
      ((interval (m + 1)).dual 1 dimLE_oneDim).d κ (.inl (Fin.last _)) = -(1 / 2) := by
    rw [Finset.sum_eq_single (.inr (Fin.last m))]
    · rw [dual_d_apply]; simp [interval.symMat, hc]
    · rintro (v | e) _ hκ
      · simp [interval.symMat]
      · have : e ≠ Fin.last m := fun h ↦ hκ (by rw [h])
        simp [interval.symMat, hc, (hs e).not.mpr this]
    · simp
  rw [defect, Matrix.sub_apply, mul_apply, mul_apply, h₁, h₂]
  norm_num

/-- **The flag iterates (cube level)**: on the top face `x₀ = m + 1` the boundary structure of
`cubeSym (k+1)` is `cubeSym k`. -/
theorem defect_cubeSym_top (k : ℕ) (x y : (cube (m + 1) k).X) :
    defect (cube (m + 1) (k + 1)) (k + 1) (cube.dimLE (k + 1) (m + 1)) (cubeSym m (k + 1))
      (.inl (Fin.last _), x) (.inl (Fin.last _), y) = cubeSym m k x y := by
  rw [defect_congr (C := cube (m + 1) (k + 1)) _ (Nat.add_comm k 1)
    (dimLE_oneDim.tensor (cube.dimLE k (m + 1)))]
  have h := defect_kronecker (C := interval (m + 1)) (D := cube (m + 1) k) dimLE_oneDim
    (cube.dimLE k (m + 1)) (interval.symMat m) (cubeSym m k)
    (fun σ τ h ↦ interval.symMat_deg m h)
  change defect ((interval (m + 1)).tensor (cube (m + 1) k)) (1 + k) _
    ((interval.symMat m ⊗ₖ cubeSym m k) * koszul _ _ k) (.inl (Fin.last _), x)
      (.inl (Fin.last _), y) = _
  rw [h, koszul, mul_diagonal, Matrix.add_apply, kronecker_apply, kronecker_apply,
    interval.defect_symMat_last]
  simp [sgn, interval.symMat]

/-- **The flag iterates (with `CPcell`)**: on the top face `F ≅ Iᵏ ⊗ CP` the boundary structure
`𝒟(cubeTop (k+1))` of the B-pair is the next B-pair top `cubeTop k`, with sign `+1`. -/
theorem defect_cubeTop_top (k : ℕ) (x y : (cube (m + 1) k).X) (c c' : CPcell.X) :
    defect ((cube (m + 1) (k + 1)).tensor CPcell) (k + 1 + 4)
      ((cube.dimLE (k + 1) (m + 1)).tensor CPcell.dimLE) (cubeTop m (k + 1))
      ((.inl (Fin.last _), x), c) ((.inl (Fin.last _), y), c') = cubeTop m k (x, c) (y, c') := by
  have hd : (cube (m + 1) (k + 1)).deg (Sum.inl (Fin.last (m + 1)), y) =
      (cube (m + 1) k).deg y := zero_add _
  rw [cubeTop, defect_kronecker (cube.dimLE (k + 1) (m + 1)) CPcell.dimLE _ _
      (fun σ τ h ↦ cubeSym_deg m (k + 1) h),
    defect_hom CPcell.φ, kronecker_zero, add_zero, koszul, mul_diagonal, kronecker_apply,
    defect_cubeSym_top, cubeTop, koszul, mul_diagonal, kronecker_apply, hd]

/-- At the bottom of the flag: the top vertex `+` of `∂I` carries exactly `φ_CP`. -/
theorem defect_cubeTop_one_last (c c' : CPcell.X) :
    defect ((cube (m + 1) 1).tensor CPcell) (0 + 1 + 4)
      ((cube.dimLE (0 + 1) (m + 1)).tensor CPcell.dimLE) (cubeTop m 1)
      ((.inl (Fin.last _), ()), c) ((.inl (Fin.last _), ()), c') = CPcell.φ.f c c' := by
  rw [defect_cubeTop_top, cubeTop, koszul, mul_diagonal, kronecker_apply,
    show (cube (m + 1) 0).deg () = 0 from rfl]
  simp [cubeSym]

end Cube

end BasedComplex

end HSFormal.Cubical
