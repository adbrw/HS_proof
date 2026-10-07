import HSFormal.Cubical.Contraction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Shifted duals, transposition and symmetric dualities (cubical module C2)

The `N`-dual of a based complex of dimension `≤ N` in the sign conventions of
`HSFormal.Compression` (manuscript l. 245–253): the same cells with `deg = N - deg`, and the
transposed boundary `δ_r = (-1)^r d^*_{N-r+1}`, written `δ = (-1)^N dᵀ sgn`.  Chain maps
dualize by transposition (no sign), homotopies by `K = -(-1)^N Hᵀ sgn` (`K_r = (-1)^{r+1}T^*`).
Ranicki's transposition of `φ : C^{N-*} → D` is `Tφ = ε φᵀ` with `ε = diag (-1)^{(N+1) deg}`
(which equals `(-1)^{r(N-r)}` in degree `r`); it is the bidual `ε` composed with `φ^{N-*}`.

A `SymDuality` is a strictly symmetric `φ` with an explicit homotopy inverse; `ofFlip`
symmetrizes `φ₀` to `(φ₀ + Tφ₀)/2` along a flip homotopy `φ₀ ≃ Tφ₀`, keeping the inverse.

The right slant `λ(t)(τ^*) = Σ_σ t(σ, τ) σ` (l. 257) turns homogeneous cycles of the Koszul
tensor `C ⊗ C` into chain maps `C^{N-*} → C`; caps `z ∩ = λ(Δ z)` of diagonals satisfy
`ε ∘ (z ∩) = ⟨-, z⟩`.  Tensor products: the Koszul isomorphism
`(C ⊗ D)^{N+M-*} ≅ C^{N-*} ⊗ D^{M-*}`, `(c ⊗ d)^* ↦ (-1)^{|c| |d^*|} c^* ⊗ d^*`, makes
`φ_{C⊗D} = (φ_C ⊗ φ_D) Θ` strictly symmetric, and it is the slant of the shuffled tensor
(`slant_shuffle`).
-/

namespace HSFormal.Cubical

open Matrix
open scoped Kronecker

theorem neg_one_pow_eq_of_zmod {m n : ℕ} (h : (m : ZMod 2) = n) : (-1 : ℚ) ^ m = (-1) ^ n := by
  rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := n),
    (ZMod.natCast_eq_natCast_iff' m n 2).mp h]

theorem neg_one_pow_sub {N k : ℕ} (h : k ≤ N) : (-1 : ℚ) ^ (N - k) = (-1) ^ N * (-1) ^ k := by
  rw [← pow_add]
  refine neg_one_pow_eq_of_zmod ?_
  push_cast [Nat.cast_sub h]
  generalize (N : ZMod 2) = a
  generalize (k : ZMod 2) = b
  revert a b; decide

theorem sign_dual_tensor₁ (N M a b : ℕ) :
    (-1 : ℚ) ^ N * (-1) ^ a * (-1) ^ (a * (b + M)) =
      (-1) ^ ((a + 1) * (b + M)) * (-1) ^ (N + M) * (-1) ^ (a + b) := by
  simp only [← pow_add]
  refine neg_one_pow_eq_of_zmod ?_
  push_cast
  generalize (N : ZMod 2) = x₁; generalize (M : ZMod 2) = x₂
  generalize (a : ZMod 2) = x₃; generalize (b : ZMod 2) = x₄
  revert x₁ x₂ x₃ x₄; decide

theorem sign_dual_tensor₂ (N M a b : ℕ) :
    (-1 : ℚ) ^ N * (-1) ^ a * (-1) ^ M * (-1) ^ b * (-1) ^ (a * (b + M)) =
      (-1) ^ (a * (b + 1 + M)) * (-1) ^ (N + M) * (-1) ^ (a + b) * (-1) ^ a := by
  simp only [← pow_add]
  refine neg_one_pow_eq_of_zmod ?_
  push_cast
  generalize (N : ZMod 2) = x₁; generalize (M : ZMod 2) = x₂
  generalize (a : ZMod 2) = x₃; generalize (b : ZMod 2) = x₄
  revert x₁ x₂ x₃ x₄; decide

theorem sign_transpose_tensor {N M a a' b b' : ℕ} (hN : a + a' = N) (hM : b + b' = M) :
    ((-1 : ℚ) ^ (N + M + 1)) ^ (a + b) * (-1) ^ (a * (b + M)) =
      ((-1 : ℚ) ^ (N + 1)) ^ a * ((-1 : ℚ) ^ (M + 1)) ^ b * (-1) ^ (a' * (b' + M)) := by
  subst hN hM
  simp only [← pow_mul, ← pow_add]
  refine neg_one_pow_eq_of_zmod ?_
  push_cast
  generalize (a : ZMod 2) = x₁; generalize (a' : ZMod 2) = x₂
  generalize (b : ZMod 2) = x₃; generalize (b' : ZMod 2) = x₄
  revert x₁ x₂ x₃ x₄; decide

theorem neg_one_pow_mul_self (N : ℕ) : (-1 : ℚ) ^ N * (-1) ^ N = 1 := by
  rw [← mul_pow]; norm_num

namespace BasedComplex

variable {C D C' D' E : BasedComplex} {N M : ℕ}

/-! ### The shifted dual -/

/-- All cells have degree `≤ N`. -/
def DimLE (C : BasedComplex) (N : ℕ) : Prop := ∀ σ, C.deg σ ≤ N

theorem sgn_transpose (C : BasedComplex) : C.sgnᵀ = C.sgn := diagonal_transpose _

theorem sgn_mul_d_transpose (C : BasedComplex) : C.sgn * C.dᵀ = -(C.dᵀ * C.sgn) := by
  have := congrArg transpose C.d_sgn
  rwa [transpose_mul, transpose_neg, transpose_mul, sgn_transpose] at this

/-- The `N`-dual `C^{N-*}`: the same cells in degree `N - deg`, with `δ = (-1)^N dᵀ sgn`,
i.e. `δ_r = (-1)^r d^*_{N-r+1}` (Ranicki; `Compression.dualComplex`). -/
@[reducible]
def dual (C : BasedComplex) (N : ℕ) (hN : C.DimLE N) : BasedComplex where
  X := C.X
  deg σ := N - C.deg σ
  d := (-1 : ℚ) ^ N • (C.dᵀ * C.sgn)
  d_deg σ τ h := by
    have h' : C.d τ σ ≠ 0 := fun h₀ ↦ h (by simp [sgn, mul_diagonal, h₀])
    have := C.d_deg τ σ h'
    have := hN σ
    show N - C.deg τ = N - C.deg σ + 1
    omega
  d_d := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Matrix.mul_assoc, Matrix.mul_assoc _ C.sgn,
      sgn_mul_d_transpose, Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc,
      ← transpose_mul, C.d_d, Matrix.mul_assoc, sgn_mul_sgn]
    simp

theorem dual_d (hN : C.DimLE N) : (C.dual N hN).d = (-1 : ℚ) ^ N • (C.dᵀ * C.sgn) := rfl

theorem dual_d_apply (hN : C.DimLE N) (σ τ : C.X) :
    (C.dual N hN).d σ τ = (-1) ^ N * ((-1) ^ C.deg τ * C.d τ σ) := by
  simp [sgn, mul_diagonal, mul_comm]

theorem dimLE_dual (hN : C.DimLE N) : (C.dual N hN).DimLE N := fun _ ↦ Nat.sub_le _ _

theorem dual_sgn (hN : C.DimLE N) : (C.dual N hN).sgn = (-1 : ℚ) ^ N • C.sgn := by
  ext σ τ
  simp only [sgn, Matrix.smul_apply, diagonal_apply, smul_eq_mul]
  split_ifs with h
  · subst h; exact neg_one_pow_sub (hN σ)
  · simp

theorem dual_aug (hN : C.DimLE N) (σ : C.X) :
    (C.dual N hN).aug σ = if C.deg σ = N then 1 else 0 := by
  have := hN σ
  change (if N - C.deg σ = 0 then (1 : ℚ) else 0) = _
  by_cases h : C.deg σ = N
  · rw [ite_eq_left h, ite_eq_left (by omega)]
  · rw [ite_eq_right h, ite_eq_right (by omega)]

/-- Every diagonal matrix has degree `0`. -/
theorem hasDeg_diagonal (v : C.X → ℚ) : HasDeg C C 0 (diagonal v) := fun σ τ h ↦ by
  by_cases hs : σ = τ
  · simp [hs]
  · exact (h (diagonal_apply_ne _ hs)).elim

theorem HasDeg.transpose {k : ℤ} {u : Matrix D.X C.X ℚ} (hC : C.DimLE N) (hD : D.DimLE N)
    (hu : HasDeg C D k u) : HasDeg (D.dual N hD) (C.dual N hC) k uᵀ := fun σ τ h ↦ by
  have := hu τ σ h
  have := hC σ
  have := hD τ
  change ((N - C.deg σ : ℕ) : ℤ) = ((N - D.deg τ : ℕ) : ℤ) + k
  omega

/-- The dual chain map `f^{N-*} = fᵀ` (no sign). -/
def Hom.dual (f : Hom C D) (N : ℕ) (hC : C.DimLE N) (hD : D.DimLE N) :
    Hom (D.dual N hD) (C.dual N hC) where
  f := f.fᵀ
  deg0 := f.deg0.transpose hC hD
  comm := by
    have h₁ : C.sgn * f.fᵀ = f.fᵀ * D.sgn := by
      have := congrArg Matrix.transpose f.deg0.sgn_comm
      rw [transpose_mul, transpose_mul, sgn_transpose, sgn_transpose] at this
      exact this.symm
    rw [dual_d, dual_d, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, h₁,
      ← Matrix.mul_assoc, ← transpose_mul, ← f.comm, transpose_mul, Matrix.mul_assoc]

@[simp] theorem Hom.dual_f (f : Hom C D) (hC : C.DimLE N) (hD : D.DimLE N) :
    (f.dual N hC hD).f = f.fᵀ := rfl

theorem Hom.dual_comp (g : Hom D E) (f : Hom C D) (hC : C.DimLE N) (hD : D.DimLE N)
    (hE : E.DimLE N) : (g.comp f).dual N hC hE = (f.dual N hC hD).comp (g.dual N hD hE) :=
  Hom.ext (transpose_mul _ _)

theorem Hom.dual_id (hC : C.DimLE N) : (Hom.id C).dual N hC hC = Hom.id (C.dual N hC) :=
  Hom.ext transpose_one

/-- The dual homotopy `K = -(-1)^N Hᵀ sgn`, i.e. `K_r = (-1)^{r+1} T^*_{N-r-1}`
(`Compression.dualHomotopy`). -/
def Htpy.dual {f g : Hom C D} (H : Htpy f g) (hC : C.DimLE N) (hD : D.DimLE N) :
    Htpy (f.dual N hC hD) (g.dual N hC hD) where
  h := (-(-1 : ℚ) ^ N) • (H.hᵀ * D.sgn)
  deg1 := by
    have h₁ : HasDeg (D.dual N hD) (D.dual N hD) 0 D.sgn := hasDeg_diagonal _
    simpa using ((H.deg1.transpose hC hD).mul h₁).smul (-(-1 : ℚ) ^ N)
  eq := by
    have h₁ : C.sgn * H.hᵀ = -(H.hᵀ * D.sgn) := by
      have := congrArg Matrix.transpose H.deg1.sgn_anticomm
      rw [transpose_mul, transpose_neg, transpose_mul, sgn_transpose, sgn_transpose] at this
      rw [this, neg_neg]
    have e₁ : C.dᵀ * C.sgn * (H.hᵀ * D.sgn) = -(C.dᵀ * H.hᵀ) := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc C.sgn, h₁, Matrix.neg_mul, Matrix.mul_assoc,
        sgn_mul_sgn, Matrix.mul_one, Matrix.mul_neg]
    have e₂ : H.hᵀ * D.sgn * (D.dᵀ * D.sgn) = -(H.hᵀ * D.dᵀ) := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc D.sgn, sgn_mul_d_transpose, Matrix.neg_mul,
        Matrix.mul_assoc, sgn_mul_sgn, Matrix.mul_one, Matrix.mul_neg]
    rw [Hom.dual_f, Hom.dual_f, ← transpose_sub, H.eq, transpose_add, transpose_mul,
      transpose_mul, dual_d, dual_d]
    have hs := neg_one_pow_mul_self N
    generalize (-1 : ℚ) ^ N = s at hs ⊢
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [e₁, e₂, show s * -s = -1 by rw [mul_neg, hs], show -s * s = -1 by rw [neg_mul, hs],
      neg_one_smul, neg_one_smul, neg_neg, neg_neg, add_comm]

/-- The dual of a homotopy equivalence. -/
def HtpyEquiv.dual (e : HtpyEquiv C D) (hC : C.DimLE N) (hD : D.DimLE N) :
    HtpyEquiv (D.dual N hD) (C.dual N hC) where
  hom := e.hom.dual N hC hD
  inv := e.inv.dual N hD hC
  homInv := (e.invHom.dual hD hD).congr (Hom.dual_comp _ _ _ _ _) (Hom.dual_id _)
  invHom := (e.homInv.dual hC hC).congr (Hom.dual_comp _ _ _ _ _) (Hom.dual_id _)

/-- A chain map with a two-sided inverse matrix of degree `0`: the inverse is a chain map. -/
def Hom.ofInverse (f : Hom C D) (g : Matrix C.X D.X ℚ) (hg : HasDeg D C 0 g)
    (h₁ : g * f.f = 1) (h₂ : f.f * g = 1) : Hom D C where
  f := g
  deg0 := hg
  comm := by
    calc C.d * g = g * f.f * C.d * g := by rw [h₁, Matrix.one_mul]
      _ = g * D.d * (f.f * g) := by rw [Matrix.mul_assoc g, ← f.comm]; simp only [Matrix.mul_assoc]
      _ = g * D.d := by rw [h₂, Matrix.mul_one]

/-- A chain isomorphism as a homotopy equivalence with zero homotopies. -/
def HtpyEquiv.ofIso (f : Hom C D) (g : Matrix C.X D.X ℚ) (hg : HasDeg D C 0 g)
    (h₁ : g * f.f = 1) (h₂ : f.f * g = 1) : HtpyEquiv C D :=
  ⟨f, f.ofInverse g hg h₁ h₂, Htpy.ofEq (Hom.ext h₁), Htpy.ofEq (Hom.ext h₂)⟩

/-! ### Transposition -/

/-- The bidual sign `ε = diag (-1)^{(N+1) deg}`; in degree `r` it is `(-1)^{r(N-r)}`. -/
def eps (C : BasedComplex) (N : ℕ) : Matrix C.X C.X ℚ :=
  diagonal fun σ ↦ ((-1 : ℚ) ^ (N + 1)) ^ C.deg σ

theorem eps_transpose (C : BasedComplex) (N : ℕ) : (C.eps N)ᵀ = C.eps N := diagonal_transpose _

theorem eps_mul_eps (C : BasedComplex) (N : ℕ) : C.eps N * C.eps N = 1 := by
  rw [eps, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  ext σ
  rw [← mul_pow, ← mul_pow]
  norm_num

theorem eps_eq_neg_one_pow (C : BasedComplex) {N : ℕ} (hN : C.DimLE N) (σ : C.X) :
    ((-1 : ℚ) ^ (N + 1)) ^ C.deg σ = (-1) ^ (C.deg σ * (N - C.deg σ)) := by
  rw [← pow_mul]
  refine neg_one_pow_eq_of_zmod ?_
  have := hN σ
  push_cast [Nat.cast_sub this]
  generalize (N : ZMod 2) = a
  generalize (C.deg σ : ZMod 2) = b
  revert a b; decide

/-- `ε_a ε_b = 1` when `a + b = N`. -/
theorem eps_pow_mul_eps_pow {a b : ℕ} (h : a + b = N) :
    ((-1 : ℚ) ^ (N + 1)) ^ a * ((-1 : ℚ) ^ (N + 1)) ^ b = 1 := by
  rw [← pow_add, h, ← pow_mul]
  rw [show (1 : ℚ) = (-1) ^ 0 by simp]
  refine neg_one_pow_eq_of_zmod ?_
  push_cast
  generalize (N : ZMod 2) = a
  revert a; decide

theorem dual_dual_d (hN : C.DimLE N) :
    ((C.dual N hN).dual N (dimLE_dual hN)).d = (-1 : ℚ) ^ (N + 1) • C.d := by
  have e : C.sgn * C.d * C.sgn = -C.d := by
    rw [Matrix.mul_assoc, C.d_sgn, Matrix.mul_neg, ← Matrix.mul_assoc, sgn_mul_sgn,
      Matrix.one_mul]
  rw [dual_d, dual_sgn, dual_d, transpose_smul, transpose_mul, transpose_transpose,
    sgn_transpose]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [e, smul_neg, ← neg_smul]
  congr 1
  have := neg_one_pow_mul_self N
  rw [pow_succ]
  linear_combination (-(-1 : ℚ) ^ N) * this

/-- The bidual isomorphism `C^{N-(N-*)} → C`, multiplication by `ε`. -/
def bidual (C : BasedComplex) (N : ℕ) (hN : C.DimLE N) :
    Hom ((C.dual N hN).dual N (dimLE_dual hN)) C where
  f := C.eps N
  deg0 σ τ h := by
    by_cases hs : σ = τ
    · subst hs; have := hN σ
      show (C.deg σ : ℤ) = ((N - (N - C.deg σ) : ℕ) : ℤ) + 0; omega
    · exact (h (diagonal_apply_ne _ hs)).elim
  comm := by
    rw [dual_dual_d, Matrix.mul_smul]
    ext σ τ
    simp only [eps, mul_diagonal, diagonal_mul, Matrix.smul_apply, smul_eq_mul]
    by_cases h : C.d σ τ = 0
    · simp [h]
    · rw [C.d_deg σ τ h, pow_succ]; ring

/-- The inverse bidual map, again multiplication by `ε`. -/
def bidualInv (C : BasedComplex) (N : ℕ) (hN : C.DimLE N) :
    Hom C ((C.dual N hN).dual N (dimLE_dual hN)) where
  f := C.eps N
  deg0 σ τ h := by
    by_cases hs : σ = τ
    · subst hs; have := hN σ
      show ((N - (N - C.deg σ) : ℕ) : ℤ) = (C.deg σ : ℤ) + 0; omega
    · exact (h (diagonal_apply_ne _ hs)).elim
  comm := by
    rw [dual_dual_d, Matrix.smul_mul]
    ext σ τ
    simp only [eps, mul_diagonal, diagonal_mul, Matrix.smul_apply, smul_eq_mul]
    by_cases h : C.d σ τ = 0
    · simp [h]
    · have := neg_one_pow_mul_self (N + 1)
      rw [C.d_deg σ τ h, pow_succ ((-1 : ℚ) ^ (N + 1)) (C.deg σ)]
      linear_combination (C.d σ τ * ((-1 : ℚ) ^ (N + 1)) ^ C.deg σ) * this

/-- The bidual isomorphism as a homotopy equivalence (with zero homotopies). -/
def bidualEquiv (C : BasedComplex) (N : ℕ) (hN : C.DimLE N) :
    HtpyEquiv ((C.dual N hN).dual N (dimLE_dual hN)) C where
  hom := bidual C N hN
  inv := bidualInv C N hN
  homInv := Htpy.ofEq (Hom.ext (C.eps_mul_eps N))
  invHom := Htpy.ofEq (Hom.ext (C.eps_mul_eps N))

/-- Ranicki's transposition `Tφ = ε ∘ φ^{N-*} : D^{N-*} → C` of `φ : C^{N-*} → D`,
`(Tφ)_r = (-1)^{r(N-r)} φ^*_{N-r}`. -/
def transpose (hC : C.DimLE N) (hD : D.DimLE N) (φ : Hom (C.dual N hC) D) :
    Hom (D.dual N hD) C :=
  (bidual C N hC).comp (φ.dual N (dimLE_dual hC) hD)

theorem transpose_f (hC : C.DimLE N) (hD : D.DimLE N) (φ : Hom (C.dual N hC) D) :
    (transpose hC hD φ).f = C.eps N * φ.fᵀ := rfl

theorem transpose_f_apply (hC : C.DimLE N) (hD : D.DimLE N) (φ : Hom (C.dual N hC) D)
    (σ : C.X) (τ : D.X) :
    (transpose hC hD φ).f σ τ = ((-1 : ℚ) ^ (N + 1)) ^ C.deg σ * φ.f τ σ := by
  simp [transpose_f, eps, diagonal_mul]

/-- `T² = 1`. -/
@[simp]
theorem transpose_transpose (hC : C.DimLE N) (hD : D.DimLE N) (φ : Hom (C.dual N hC) D) :
    transpose hD hC (transpose hC hD φ) = φ := by
  ext σ τ
  rw [transpose_f_apply, transpose_f_apply, ← mul_assoc]
  by_cases h : φ.f σ τ = 0
  · simp [h]
  · have := φ.deg0 σ τ h
    have := hC τ
    rw [eps_pow_mul_eps_pow (a := D.deg σ) (b := C.deg τ) (by simp only [dual] at *; omega),
      one_mul]

theorem transpose_add (hC : C.DimLE N) (hD : D.DimLE N) (φ ψ : Hom (C.dual N hC) D) :
    transpose hC hD (φ.add ψ) = (transpose hC hD φ).add (transpose hC hD ψ) :=
  Hom.ext (by simp [transpose_f, Hom.add, Matrix.mul_add])

theorem transpose_smul (hC : C.DimLE N) (hD : D.DimLE N) (c : ℚ) (φ : Hom (C.dual N hC) D) :
    transpose hC hD (φ.smul c) = (transpose hC hD φ).smul c :=
  Hom.ext (by simp [transpose_f, Hom.smul])

/-- `T(g φ a^{N-*}) = a (Tφ) g^{N-*}`. -/
theorem transpose_comp {C₁ D₁ : BasedComplex} (hC : C.DimLE N) (hD : D.DimLE N)
    (hC₁ : C₁.DimLE N) (hD₁ : D₁.DimLE N) (a : Hom C C₁) (φ : Hom (C.dual N hC) D)
    (g : Hom D D₁) :
    transpose hC₁ hD₁ (g.comp (φ.comp (a.dual N hC hC₁))) =
      a.comp ((transpose hC hD φ).comp (g.dual N hD hD₁)) := by
  have h : C₁.eps N * a.f = a.f * C.eps N := by
    ext σ τ
    simp only [eps, diagonal_mul, mul_diagonal]
    by_cases h : a.f σ τ = 0
    · simp [h]
    · rw [show C₁.deg σ = C.deg τ by have := a.deg0 σ τ h; omega]; ring
  apply Hom.ext
  simp only [transpose_f, Hom.comp_f, Hom.dual_f, transpose_mul, Matrix.transpose_transpose,
    ← Matrix.mul_assoc, h]

/-- The transpose of a homotopy. -/
def Htpy.transpose (hC : C.DimLE N) (hD : D.DimLE N) {φ ψ : Hom (C.dual N hC) D}
    (H : Htpy φ ψ) : Htpy (BasedComplex.transpose hC hD φ) (BasedComplex.transpose hC hD ψ) :=
  (H.dual (dimLE_dual hC) hD).compLeft (bidual C N hC)

/-- The transpose of a duality homotopy equivalence is one. -/
def HtpyEquiv.transpose (hC : C.DimLE N) (hD : D.DimLE N) (e : HtpyEquiv (C.dual N hC) D) :
    HtpyEquiv (D.dual N hD) C :=
  (e.dual (dimLE_dual hC) hD).trans (bidualEquiv C N hC)

theorem HtpyEquiv.transpose_hom (hC : C.DimLE N) (hD : D.DimLE N)
    (e : HtpyEquiv (C.dual N hC) D) :
    (e.transpose hC hD).hom = BasedComplex.transpose hC hD e.hom := rfl

/-! ### Strictly symmetric dualities -/

variable (hN : C.DimLE N)

/-- Strict symmetry `Tφ = φ`. -/
def IsSymm (φ : Hom (C.dual N hN) C) : Prop := transpose hN hN φ = φ

variable {hN}

theorem isSymm_iff (φ : Hom (C.dual N hN) C) :
    IsSymm hN φ ↔ ∀ σ τ, ((-1 : ℚ) ^ (N + 1)) ^ C.deg σ * φ.f τ σ = φ.f σ τ := by
  refine ⟨fun h σ τ ↦ ?_, fun h ↦ Hom.ext (Matrix.ext fun σ τ ↦ ?_)⟩
  · rw [← transpose_f_apply hN hN]; exact congrFun (congrFun (congrArg Hom.f h) σ) τ
  · rw [transpose_f_apply]; exact h σ τ

variable (hN) in
/-- The symmetrization `(φ + Tφ)/2` (l. 271). -/
def sym (φ : Hom (C.dual N hN) C) : Hom (C.dual N hN) C :=
  (φ.add (transpose hN hN φ)).smul (1 / 2)

theorem isSymm_sym (φ : Hom (C.dual N hN) C) : IsSymm hN (sym hN φ) := by
  rw [IsSymm, sym, transpose_smul, transpose_add, transpose_transpose]
  exact Hom.ext (by simp [Hom.smul, Hom.add, add_comm])

theorem IsSymm.sym_eq {φ : Hom (C.dual N hN) C} (h : IsSymm hN φ) : sym hN φ = φ := by
  rw [sym, h]
  exact Hom.ext (by simp only [Hom.smul, Hom.add, ← two_smul ℚ φ.f, smul_smul]; norm_num)

/-- A flip homotopy `U : φ ≃ Tφ` gives `U/2 : φ ≃ (φ + Tφ)/2`. -/
def Htpy.toSym {φ : Hom (C.dual N hN) C} (U : Htpy φ (BasedComplex.transpose hN hN φ)) :
    Htpy φ (sym hN φ) where
  h := (1 / 2 : ℚ) • U.h
  deg1 := U.deg1.smul _
  eq := by
    simp only [sym, Hom.smul, Hom.add]
    rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_add, ← U.eq]
    module

/-- A homotopy `e.hom ≃ f` makes `f` a homotopy equivalence with the same inverse. -/
def HtpyEquiv.ofHtpy {A B : BasedComplex} (e : HtpyEquiv A B) {f : Hom A B}
    (H : Htpy e.hom f) : HtpyEquiv A B where
  hom := f
  inv := e.inv
  homInv := (H.symm.compLeft e.inv).trans e.homInv
  invHom := (H.symm.compRight e.inv).trans e.invHom

variable (C N hN) in
/-- An `N`-dimensional strictly symmetric chain duality: a strictly symmetric `φ : C^{N-*} → C`
with an explicit homotopy inverse and explicit homotopies. -/
structure SymDuality extends HtpyEquiv (C.dual N hN) C where
  symm : IsSymm hN hom

/-- Symmetrize a duality equivalence along a flip homotopy `U : φ₀ ≃ Tφ₀`: the duality
`(φ₀ + Tφ₀)/2` keeps the inverse `b` of `φ₀`; its homotopies are those of `φ₀` corrected by
`∓ U b / 2` (for an isomorphism `φ₀`, `H = -½ U b`). -/
def SymDuality.ofFlip (e : HtpyEquiv (C.dual N hN) C) (U : Htpy e.hom (transpose hN hN e.hom)) :
    SymDuality C N hN where
  toHtpyEquiv := e.ofHtpy U.toSym
  symm := isSymm_sym _

theorem SymDuality.ofFlip_hom (e : HtpyEquiv (C.dual N hN) C)
    (U : Htpy e.hom (transpose hN hN e.hom)) : (SymDuality.ofFlip e U).hom = sym hN e.hom := rfl

theorem SymDuality.ofFlip_inv (e : HtpyEquiv (C.dual N hN) C)
    (U : Htpy e.hom (transpose hN hN e.hom)) : (SymDuality.ofFlip e U).inv = e.inv := rfl

/-- The middle form `b(x, y) = ⟨x, φ y⟩` on cochains of the middle degree `m` (`N = 2m`),
as a Gram matrix in the cell basis. -/
def middleForm (φ : Matrix C.X C.X ℚ) (m : ℕ) :
    Matrix {σ // C.deg σ = m} {σ // C.deg σ = m} ℚ :=
  φ.submatrix Subtype.val Subtype.val

/-! ### Slant products, diagonals and caps -/

variable (hN)

/-- The right slant `λ(t)(τ^*) = Σ_σ t(σ, τ) σ` of `t ∈ C ⊗ C` (l. 257), as a matrix. -/
def slant (t : C.X × C.X → ℚ) : Matrix C.X C.X ℚ := Matrix.of fun σ τ ↦ t (σ, τ)

@[simp] theorem slant_apply (t : C.X × C.X → ℚ) (σ τ : C.X) : slant t σ τ = t (σ, τ) := rfl

theorem slant_add (t t' : C.X × C.X → ℚ) : slant (t + t') = slant t + slant t' := rfl

theorem slant_kronecker_mulVec (A B : Matrix C.X C.X ℚ) (t : C.X × C.X → ℚ) :
    slant ((A ⊗ₖ B) *ᵥ t) = A * slant t * Bᵀ := by
  ext σ τ
  simp only [slant_apply, mulVec, dotProduct, kronecker_apply, Fintype.sum_prod_type, mul_apply,
    transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

variable (C N) in
/-- `t` is homogeneous of degree `N`. -/
def IsHomog (t : C.X × C.X → ℚ) : Prop := ∀ σ τ, t (σ, τ) ≠ 0 → C.deg σ + C.deg τ = N

theorem sgn_mul_slant {t : C.X × C.X → ℚ} (ht : IsHomog C N t) :
    C.sgn * slant t = (-1 : ℚ) ^ N • (slant t * C.sgn) := by
  ext σ τ
  simp only [sgn, diagonal_mul, mul_diagonal, slant_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases h : t (σ, τ) = 0
  · simp [h]
  · rw [← ht σ τ h, pow_add]
    have := neg_one_pow_mul_self (C.deg τ)
    linear_combination (-(-1 : ℚ) ^ C.deg σ * t (σ, τ)) * this

/-- The chain-map defect of a slant is the slant of the boundary:
`d λ(t) - λ(t) δ = λ(d t)` for homogeneous `t`. -/
theorem d_mul_slant_sub {t : C.X × C.X → ℚ} (ht : IsHomog C N t) :
    C.d * slant t - slant t * (C.dual N hN).d = slant ((C.tensor C).d *ᵥ t) := by
  rw [tensor_d, add_mulVec, slant_add, slant_kronecker_mulVec, slant_kronecker_mulVec,
    transpose_one, Matrix.mul_one, sgn_mul_slant ht, Matrix.smul_mul, Matrix.mul_assoc,
    sgn_mul_d_transpose, dual_d, Matrix.mul_smul, Matrix.mul_neg, smul_neg, sub_eq_add_neg]

/-- The slant of a homogeneous `N`-cycle of the Koszul tensor `C ⊗ C` is a chain map
`C^{N-*} → C`: the Koszul sign of `d (x ⊗ y)` matches `δ_r = (-1)^r d^*`, with no extra sign. -/
def slantHom (t : C.X × C.X → ℚ) (ht : IsHomog C N t) (hc : (C.tensor C).d *ᵥ t = 0) :
    Hom (C.dual N hN) C where
  f := slant t
  deg0 σ τ h := by
    have := ht σ τ h
    have := hN τ
    change (C.deg σ : ℤ) = ((N - C.deg τ : ℕ) : ℤ) + 0
    omega
  comm := by
    have h := d_mul_slant_sub hN ht
    rw [hc] at h
    exact sub_eq_zero.mp (h.trans (by ext; rfl))

@[simp] theorem slantHom_f (t : C.X × C.X → ℚ) (ht : IsHomog C N t)
    (hc : (C.tensor C).d *ᵥ t = 0) : (slantHom hN t ht hc).f = slant t := rfl

/-- The graded flip `(x ⊗ y) ↦ (-1)^{|x||y|} y ⊗ x`. -/
def flipT (t : C.X × C.X → ℚ) : C.X × C.X → ℚ :=
  fun p ↦ (-1) ^ (C.deg p.1 * C.deg p.2) * t (p.2, p.1)

/-- Transposition is the graded flip (l. 259). -/
theorem transpose_slantHom (t : C.X × C.X → ℚ) (ht : IsHomog C N t)
    (hc : (C.tensor C).d *ᵥ t = 0) :
    (transpose hN hN (slantHom hN t ht hc)).f = slant (flipT t) := by
  ext σ τ
  rw [transpose_f_apply, slant_apply, flipT, slantHom_f, slant_apply]
  by_cases h : t (τ, σ) = 0
  · simp [h]
  · congr 1
    rw [← pow_mul]
    refine neg_one_pow_eq_of_zmod ?_
    rw [← ht τ σ h]
    push_cast
    generalize (C.deg σ : ZMod 2) = x
    generalize (C.deg τ : ZMod 2) = y
    revert x y; decide

/-- A cellular diagonal `C → C ⊗ C`. -/
abbrev Diagonal (C : BasedComplex) := Hom C (C.tensor C)

variable (C N) in
/-- A homogeneous `N`-cycle. -/
structure IsCycle (z : C.X → ℚ) : Prop where
  deg : ∀ σ, z σ ≠ 0 → C.deg σ = N
  cycle : C.d *ᵥ z = 0

/-- The cap product `z ∩ = λ(Δ z) : C^{N-*} → C` with an `N`-cycle `z`. -/
def cap (Δ : Diagonal C) {z : C.X → ℚ} (hz : IsCycle C N z) : Hom (C.dual N hN) C :=
  slantHom hN (Δ.f *ᵥ z)
    (fun σ τ h ↦ by
      obtain ⟨ρ, h₁, h₂⟩ := exists_mulVec_ne_zero h
      have := Δ.deg0 (σ, τ) ρ h₁
      have := hz.deg ρ h₂
      simp only [tensor] at *
      omega)
    (by rw [mulVec_mulVec, Δ.comm, ← mulVec_mulVec, hz.cycle, mulVec_zero])

theorem cap_f_apply (Δ : Diagonal C) {z : C.X → ℚ} (hz : IsCycle C N z) (σ τ : C.X) :
    (cap hN Δ hz).f σ τ = ∑ ρ, Δ.f (σ, τ) ρ * z ρ := rfl

/-- `(ε ⊗ 1) Δ = 1`. -/
def IsLeftCounital (Δ : Diagonal C) : Prop :=
  ∀ τ ρ, ∑ σ, C.aug σ * Δ.f (σ, τ) ρ = if τ = ρ then 1 else 0

/-- `(1 ⊗ ε) Δ = 1`. -/
def IsRightCounital (Δ : Diagonal C) : Prop :=
  ∀ σ ρ, ∑ τ, C.aug τ * Δ.f (σ, τ) ρ = if σ = ρ then 1 else 0

theorem sum_aug_mulVec {Δ : Diagonal C} (hΔ : IsLeftCounital Δ) (z : C.X → ℚ) (τ : C.X) :
    ∑ σ, C.aug σ * (Δ.f *ᵥ z) (σ, τ) = z τ := by
  simp_rw [mulVec, dotProduct, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hΔ τ]
  simp

/-- `ε ∘ (z ∩) = ⟨-, z⟩` (the degree-0 augmentation of (8.6)). -/
theorem aug_cap {Δ : Diagonal C} (hΔ : IsLeftCounital Δ) {z : C.X → ℚ} (hz : IsCycle C N z)
    (τ : C.X) : ∑ σ, C.aug σ * (cap hN Δ hz).f σ τ = z τ :=
  sum_aug_mulVec hΔ z τ

theorem aug_transpose_cap {Δ : Diagonal C} (hΔ : IsRightCounital Δ) {z : C.X → ℚ}
    (hz : IsCycle C N z) (τ : C.X) :
    ∑ σ, C.aug σ * (transpose hN hN (cap hN Δ hz)).f σ τ = z τ := by
  have h : ∀ σ, C.aug σ * (transpose hN hN (cap hN Δ hz)).f σ τ =
      C.aug σ * (cap hN Δ hz).f τ σ := fun σ ↦ by
    rw [transpose_f_apply]
    by_cases h : C.deg σ = 0
    · rw [h, pow_zero, one_mul]
    · simp [aug, h]
  simp_rw [h, cap_f_apply, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hΔ τ]
  simp

theorem aug_sym_cap {Δ : Diagonal C} (hΔ : IsLeftCounital Δ) (hΔ' : IsRightCounital Δ)
    {z : C.X → ℚ} (hz : IsCycle C N z) (τ : C.X) :
    ∑ σ, C.aug σ * (sym hN (cap hN Δ hz)).f σ τ = z τ := by
  have h₁ := aug_cap hN hΔ hz τ
  have h₂ := aug_transpose_cap hN hΔ' hz τ
  have e : ∀ σ, C.aug σ * (sym hN (cap hN Δ hz)).f σ τ =
      1 / 2 * (C.aug σ * (cap hN Δ hz).f σ τ) +
        1 / 2 * (C.aug σ * (transpose hN hN (cap hN Δ hz)).f σ τ) := fun σ ↦ by
    simp only [sym, Hom.smul, Hom.add, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]; ring
  rw [Finset.sum_congr rfl fun σ _ ↦ e σ, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, h₁, h₂]
  ring

/-! ### Tensor products of dualities -/

theorem DimLE.tensor (hC : C.DimLE N) (hD : D.DimLE M) : (C.tensor D).DimLE (N + M) :=
  fun p ↦ Nat.add_le_add (hC p.1) (hD p.2)

variable (C D M) in
/-- The Koszul sign `(-1)^{|c| |d^*|}` of `(c ⊗ d)^* ↦ c^* ⊗ d^*` (`|d^*| ≡ |d| + M`). -/
def koszul : Matrix (C.X × D.X) (C.X × D.X) ℚ :=
  diagonal fun p ↦ (-1) ^ (C.deg p.1 * (D.deg p.2 + M))

theorem koszul_mul_koszul : koszul C D M * koszul C D M = 1 := by
  rw [koszul, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  ext p
  rw [← mul_pow]
  norm_num

theorem d_self (C : BasedComplex) (σ : C.X) : C.d σ σ = 0 :=
  by_contra fun h ↦ by have := C.d_deg σ σ h; omega

variable (hC : C.DimLE N) (hD : D.DimLE M)

/-- `(C ⊗ D)^{N+M-*} → C^{N-*} ⊗ D^{M-*}`. -/
def dualTensor :
    Hom ((C.tensor D).dual (N + M) (hC.tensor hD)) ((C.dual N hC).tensor (D.dual M hD)) where
  f := koszul C D M
  deg0 x y h := by
    by_cases hxy : x = y
    · subst hxy; have := hC x.1; have := hD x.2
      change (((N - C.deg x.1) + (M - D.deg x.2) : ℕ) : ℤ) =
        ((N + M - (C.deg x.1 + D.deg x.2) : ℕ) : ℤ) + 0
      omega
    · exact (h (diagonal_apply_ne _ hxy)).elim
  comm := by
    ext ⟨c', d'⟩ ⟨c, d⟩
    rw [koszul, mul_diagonal, diagonal_mul, tensor_d, dual_sgn]
    simp only [Matrix.add_apply, kronecker_apply, Matrix.smul_apply, smul_eq_mul, sgn, diagonal_apply,
      one_apply, mul_diagonal, transpose_apply]
    by_cases hc : c' = c <;> by_cases hd : d' = d
    · subst hc hd; simp [d_self]
    · subst hc
      simp only [ite_true, ite_eq_right hd, ite_eq_right (Ne.symm hd), mul_zero, zero_add]
      by_cases h : D.d d d' = 0
      · simp [h]
      · rw [D.d_deg d d' h]
        linear_combination D.d d d' * sign_dual_tensor₂ N M (C.deg c') (D.deg d)
    · subst hd
      simp only [ite_true, ite_eq_right hc, ite_eq_right (Ne.symm hc), mul_zero, add_zero, mul_one, zero_mul]
      by_cases h : C.d c c' = 0
      · simp [h]
      · rw [C.d_deg c c' h]
        linear_combination C.d c c' * sign_dual_tensor₁ N M (C.deg c) (D.deg d')
    · simp [hc, hd, Ne.symm hc, Ne.symm hd]

/-- `C^{N-*} ⊗ D^{M-*} → (C ⊗ D)^{N+M-*}`, the inverse Koszul isomorphism. -/
def tensorDual :
    Hom ((C.dual N hC).tensor (D.dual M hD)) ((C.tensor D).dual (N + M) (hC.tensor hD)) where
  f := koszul C D M
  deg0 x y h := by
    have := (dualTensor hC hD).deg0 x y h
    have hxy : x = y := by_contra fun hxy ↦ h (diagonal_apply_ne _ hxy)
    subst hxy; omega
  comm := by
    have h := (dualTensor hC hD).comm
    have e := koszul_mul_koszul (C := C) (D := D) (M := M)
    change _ * koszul C D M = koszul C D M * _
    change _ * koszul C D M = koszul C D M * _ at h
    calc _ = koszul C D M * (koszul C D M * ((C.tensor D).dual (N + M) (hC.tensor hD)).d) *
          koszul C D M := by rw [← Matrix.mul_assoc, e, Matrix.one_mul]
      _ = _ := by rw [← h, ← Matrix.mul_assoc, Matrix.mul_assoc _ _ (koszul C D M), e,
          Matrix.mul_one]

/-- The Koszul isomorphism `(C ⊗ D)^{N+M-*} ≅ C^{N-*} ⊗ D^{M-*}`. -/
def dualTensorEquiv :
    HtpyEquiv ((C.tensor D).dual (N + M) (hC.tensor hD)) ((C.dual N hC).tensor (D.dual M hD)) where
  hom := dualTensor hC hD
  inv := tensorDual hC hD
  homInv := Htpy.ofEq (Hom.ext koszul_mul_koszul)
  invHom := Htpy.ofEq (Hom.ext koszul_mul_koszul)

/-- Transposition commutes with tensor products: `T((φ ⊗ ψ)Θ) = (Tφ ⊗ Tψ)Θ`. -/
theorem transpose_tensor (φ : Hom (C.dual N hC) C) (ψ : Hom (D.dual M hD) D) :
    transpose (hC.tensor hD) (hC.tensor hD) ((φ.tensor ψ).comp (dualTensor hC hD)) =
      ((transpose hC hC φ).tensor (transpose hD hD ψ)).comp (dualTensor hC hD) := by
  ext ⟨c, d⟩ ⟨c', d'⟩
  rw [transpose_f_apply]
  simp only [Hom.comp_f, Hom.tensor_f, dualTensor, koszul, mul_diagonal, kronecker_apply,
    transpose_f_apply]
  by_cases h : φ.f c' c * ψ.f d' d = 0
  · rcases mul_eq_zero.mp h with h | h <;> simp [h]
  · have h₁ := φ.deg0 c' c (left_ne_zero_of_mul h)
    have h₂ := ψ.deg0 d' d (right_ne_zero_of_mul h)
    have := hC c; have := hD d
    change (C.deg c' : ℤ) = ((N - C.deg c : ℕ) : ℤ) + 0 at h₁
    change (D.deg d' : ℤ) = ((M - D.deg d : ℕ) : ℤ) + 0 at h₂
    have hN : C.deg c + C.deg c' = N := by omega
    have hM : D.deg d + D.deg d' = M := by omega
    linear_combination φ.f c' c * ψ.f d' d * sign_transpose_tensor hN hM

variable {hC hD}

/-- The tensor product of symmetric dualities, `φ_{C⊗D} = (φ_C ⊗ φ_D) Θ`. -/
def SymDuality.tensor (P : SymDuality C N hC) (Q : SymDuality D M hD) :
    SymDuality (C.tensor D) (N + M) (hC.tensor hD) where
  toHtpyEquiv := (dualTensorEquiv hC hD).trans (P.toHtpyEquiv.tensor Q.toHtpyEquiv)
  symm := by
    change transpose _ _ ((P.hom.tensor Q.hom).comp (dualTensor hC hD)) = _
    rw [transpose_tensor, show transpose hC hC P.hom = P.hom from P.symm,
      show transpose hD hD Q.hom = Q.hom from Q.symm]
    rfl

theorem SymDuality.tensor_hom_f (P : SymDuality C N hC) (Q : SymDuality D M hD) :
    (P.tensor Q).hom.f = (P.hom.f ⊗ₖ Q.hom.f) * koszul C D M := rfl

theorem kronecker_mulVec_tmul {l m n p : Type*} [Fintype m] [Fintype p] (A : Matrix l m ℚ)
    (B : Matrix n p ℚ) (u : m → ℚ) (v : p → ℚ) :
    (A ⊗ₖ B) *ᵥ (fun q ↦ u q.1 * v q.2) = fun q ↦ (A *ᵥ u) q.1 * (B *ᵥ v) q.2 := by
  ext ⟨i, j⟩
  simp only [mulVec, dotProduct, kronecker_apply, Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

/-- The tensor product of cycles is a cycle (the product fundamental cycle). -/
theorem IsCycle.tensor {z : C.X → ℚ} {z' : D.X → ℚ} (hz : IsCycle C N z)
    (hz' : IsCycle D M z') : IsCycle (C.tensor D) (N + M) fun p ↦ z p.1 * z' p.2 where
  deg p h := by
    change C.deg p.1 + D.deg p.2 = N + M
    rw [hz.deg _ (left_ne_zero_of_mul h), hz'.deg _ (right_ne_zero_of_mul h)]
  cycle := by
    rw [tensor_d, add_mulVec, kronecker_mulVec_tmul, kronecker_mulVec_tmul, hz.cycle, hz'.cycle]
    ext; simp

/-- `ε ∘ φ_{C⊗D} = ⟨-, z ⊗ z'⟩` when `ε ∘ φ_C = ⟨-, z⟩` and `ε ∘ φ_D = ⟨-, z'⟩`. -/
theorem SymDuality.aug_tensor (P : SymDuality C N hC) (Q : SymDuality D M hD) {z : C.X → ℚ}
    {z' : D.X → ℚ} (hz : IsCycle C N z) (hz' : IsCycle D M z')
    (hP : ∀ τ, ∑ σ, C.aug σ * P.hom.f σ τ = z τ) (hQ : ∀ τ, ∑ σ, D.aug σ * Q.hom.f σ τ = z' τ)
    (τ : C.X × D.X) :
    ∑ σ, (C.tensor D).aug σ * (P.tensor Q).hom.f σ τ = z τ.1 * z' τ.2 := by
  obtain ⟨c', d'⟩ := τ
  rw [SymDuality.tensor_hom_f]
  simp only [koszul, mul_diagonal, kronecker_apply, tensor_aug, Fintype.sum_prod_type]
  have e : ∀ c d, C.aug c * D.aug d * (P.hom.f c c' * Q.hom.f d d' *
      (-1) ^ (C.deg c' * (D.deg d' + M))) = (C.aug c * P.hom.f c c') * (D.aug d * Q.hom.f d d') *
      (-1) ^ (C.deg c' * (D.deg d' + M)) := fun _ _ ↦ by ring
  simp only [e, ← Finset.sum_mul, ← Finset.mul_sum, hP, hQ]
  by_cases h : z c' * z' d' = 0
  · simp [h]
  · rw [hz.deg _ (left_ne_zero_of_mul h), hz'.deg _ (right_ne_zero_of_mul h), ← two_mul,
      mul_left_comm, pow_mul]
    norm_num

/-! ### Slants of shuffled tensors -/

/-- The shuffle `(x ⊗ y) ⊗ (x' ⊗ y') ↦ (-1)^{|y| |x'|} (x ⊗ x') ⊗ (y ⊗ y')` of `t ⊗ t'`. -/
def shuffle (t : C.X × C.X → ℚ) (t' : D.X × D.X → ℚ) : (C.X × D.X) × (C.X × D.X) → ℚ :=
  fun p ↦ (-1) ^ (C.deg p.2.1 * D.deg p.1.2) * (t (p.1.1, p.2.1) * t' (p.1.2, p.2.2))

/-- The slant of the shuffled tensor is the tensor of slants twisted by the Koszul
isomorphism: `λ(sh(t ⊗ t')) = (λt ⊗ λt') Θ`.  For `t = Δz`, `t' = Δ'z'` this identifies
`(φ_C ⊗ φ_D) Θ` with the cap of the Serre diagonal. -/
theorem slant_shuffle {t : C.X × C.X → ℚ} {t' : D.X × D.X → ℚ} (ht' : IsHomog D M t') :
    slant (C := C.tensor D) (shuffle t t') = (slant t ⊗ₖ slant t') * koszul C D M := by
  ext ⟨c₁, d₁⟩ ⟨c₂, d₂⟩
  simp only [slant_apply, shuffle, koszul, mul_diagonal, kronecker_apply]
  by_cases h : t' (d₁, d₂) = 0
  · simp [h]
  · rw [← ht' d₁ d₂ h, mul_comm]
    congr 1
    refine neg_one_pow_eq_of_zmod ?_
    push_cast
    generalize (C.deg c₂ : ZMod 2) = x₁; generalize (D.deg d₁ : ZMod 2) = x₂
    generalize (D.deg d₂ : ZMod 2) = x₃
    revert x₁ x₂ x₃; decide

end BasedComplex

end HSFormal.Cubical
