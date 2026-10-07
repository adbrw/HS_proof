import HSFormal.Cubical.Dual

/-!
# Relative caps and the strict excision ladder (cubical module C2)

For a duality map `φ : W^{N-*} → W` and subcomplexes `A, B` covering `W` (`Σ = A ∩ B`), the
restriction of `φ` to cochains vanishing on `B` lands in `A` when `φ` is *local*
(`φ σ τ ≠ 0`, `τ ∉ B` ⟹ `σ ∈ A`).  Caps of cellular diagonals and their symmetrizations are
local (`IsCellLocal.local`).  Then (design §2.5, review fix 3)
```
0 → C^{N-*}(W, W_B) → C^{N-*}(W) → C^{N-*}(W_B) → 0
        ↓ ladderLeft        ↓ φ          ↓ ladderRight
0 →     C(W_A)      →     C(W)     →  C(W_B, Σ)   → 0
```
commutes *strictly* (`ladderLeft_comm`, `ladderRight_comm`), with both rows split by bases.
`C^{N-*}(W, W_B)` is the dual of the quotient `W/B` and `C(W_B, Σ) = W/A` (cells of `B` not
in `A`).  The right column is the B-pair map from absolute cochains to relative chains; the
opposite B-pair map `relB : C^{N-*}(W_B, Σ) → C(W_B)` is its transpose (`transpose_relB`), so
equivalence data for one gives the other (`HtpyEquiv.transpose`).
-/

namespace HSFormal.Cubical

open Matrix
open scoped Kronecker

namespace BasedComplex

variable {C W : BasedComplex} {N : ℕ}

theorem DimLE.restrict (hW : W.DimLE N) (Q : W.X → Prop) [DecidablePred Q]
    (hQ : W.IsLocallyClosed Q) : (W.restrict Q hQ).DimLE N := fun σ ↦ hW σ.1

theorem sum_subtype_eq {α : Type*} [Fintype α] {P : α → Prop} [DecidablePred P] (f : α → ℚ)
    (h : ∀ a, f a ≠ 0 → P a) : ∑ a : {a // P a}, f a = ∑ a, f a := by
  rw [← Fintype.sum_subtype_add_sum_subtype P f,
    Finset.sum_eq_zero (s := Finset.univ) (f := fun a : {a // ¬P a} ↦ f a)
      fun a _ ↦ by_contra fun ha ↦ a.2 (h _ ha), add_zero]

theorem mul_submatrix_apply {l m n l' n' : Type*} [Fintype m] {P : m → Prop} [DecidablePred P]
    (A : Matrix l m ℚ) (B : Matrix m n ℚ) (f : l' → l) (g : n' → n) (i : l') (j : n')
    (h : ∀ κ, A (f i) κ * B κ (g j) ≠ 0 → P κ) :
    (A.submatrix f (Subtype.val : {κ // P κ} → m) * B.submatrix Subtype.val g : Matrix l' n' ℚ)
      i j = (A * B) (f i) (g j) := by
  simp only [mul_apply]
  exact sum_subtype_eq (fun κ ↦ A (f i) κ * B κ (g j)) h

theorem restrict_dual_d (hW : W.DimLE N) (Q : W.X → Prop) [DecidablePred Q]
    (hQ : W.IsLocallyClosed Q) :
    ((W.restrict Q hQ).dual N (hW.restrict Q hQ)).d =
      (W.dual N hW).d.submatrix Subtype.val Subtype.val := by
  ext σ τ
  simp [sgn, mul_diagonal]

/-! ### Restricted duality maps -/

variable (hW : W.DimLE N)

/-- The restriction of `φ : W^{N-*} → W` to cochains on `Q` and chains on `P`; it is a chain map
when no boundary path leaves `P` or `Q` through a nonzero entry of `φ`. -/
def Hom.restrictDual (φ : Hom (W.dual N hW) W) (P Q : W.X → Prop) [DecidablePred P]
    [DecidablePred Q] (hP : W.IsLocallyClosed P) (hQ : W.IsLocallyClosed Q)
    (hP' : ∀ σ κ τ, P σ → Q τ → W.d σ κ ≠ 0 → φ.f κ τ ≠ 0 → P κ)
    (hQ' : ∀ σ κ τ, P σ → Q τ → φ.f σ κ ≠ 0 → W.d τ κ ≠ 0 → Q κ) :
    Hom ((W.restrict Q hQ).dual N (hW.restrict Q hQ)) (W.restrict P hP) where
  f := φ.f.submatrix Subtype.val Subtype.val
  deg0 σ τ h := φ.deg0 σ.1 τ.1 h
  comm := by
    ext σ τ
    change (W.d.submatrix Subtype.val Subtype.val * φ.f.submatrix Subtype.val Subtype.val :
        Matrix {σ // P σ} {σ // Q σ} ℚ) σ τ =
      (φ.f.submatrix Subtype.val Subtype.val * ((W.restrict Q hQ).dual N (hW.restrict Q hQ)).d :
        Matrix {σ // P σ} {σ // Q σ} ℚ) σ τ
    rw [restrict_dual_d hW, mul_submatrix_apply, mul_submatrix_apply, φ.comm]
    · intro κ hκ
      refine hQ' _ _ _ σ.2 τ.2 (left_ne_zero_of_mul hκ) fun h₀ ↦ right_ne_zero_of_mul hκ ?_
      rw [dual_d_apply, h₀]; ring
    · exact fun κ hκ ↦ hP' _ _ _ σ.2 τ.2 (left_ne_zero_of_mul hκ) (right_ne_zero_of_mul hκ)

@[simp] theorem Hom.restrictDual_f (φ : Hom (W.dual N hW) W) (P Q : W.X → Prop)
    [DecidablePred P] [DecidablePred Q] (hP hQ hP' hQ') :
    (φ.restrictDual hW P Q hP hQ hP' hQ').f = φ.f.submatrix Subtype.val Subtype.val := rfl

/-! ### Locality of caps -/

/-- Every nonzero entry `u σ τ` lies over one cell `ρ`: every subcomplex containing `ρ`
contains `σ` and `τ`. -/
def IsCellLocal (u : Matrix C.X C.X ℚ) : Prop :=
  ∀ σ τ, u σ τ ≠ 0 → ∃ ρ, ∀ Q : C.X → Prop, C.IsSub Q → Q ρ → Q σ ∧ Q τ

namespace IsCellLocal

variable {u v : Matrix C.X C.X ℚ}

theorem add (hu : IsCellLocal u) (hv : IsCellLocal v) : IsCellLocal (u + v) := fun σ τ h ↦ by
  by_cases h' : u σ τ = 0
  · exact hv σ τ (by simpa [h'] using h)
  · exact hu σ τ h'

theorem smul (c : ℚ) (hu : IsCellLocal u) : IsCellLocal (c • u) :=
  fun σ τ h ↦ hu σ τ (right_ne_zero_of_mul h)

theorem transpose (hu : IsCellLocal u) : IsCellLocal uᵀ := fun σ τ h ↦ by
  obtain ⟨ρ, hρ⟩ := hu τ σ h
  exact ⟨ρ, fun Q hQ h ↦ (hρ Q hQ h).symm⟩

theorem diagonal_mul (v : C.X → ℚ) (hu : IsCellLocal u) : IsCellLocal (diagonal v * u) :=
  fun σ τ h ↦ hu σ τ (right_ne_zero_of_mul (by simpa [Matrix.diagonal_mul] using h))

theorem mul_diagonal (v : C.X → ℚ) (hu : IsCellLocal u) : IsCellLocal (u * diagonal v) :=
  fun σ τ h ↦ hu σ τ (left_ne_zero_of_mul (by simpa [Matrix.mul_diagonal] using h))

/-- Tensor products of cell-local maps are cell-local (over product cells). -/
theorem kronecker {D : BasedComplex} {v : Matrix D.X D.X ℚ} (hu : IsCellLocal u)
    (hv : IsCellLocal v) : IsCellLocal (C := C.tensor D) (u ⊗ₖ v) := by
  rintro ⟨c, d⟩ ⟨c', d'⟩ h
  rw [kronecker_apply] at h
  obtain ⟨ρ₁, h₁⟩ := hu c c' (left_ne_zero_of_mul h)
  obtain ⟨ρ₂, h₂⟩ := hv d d' (right_ne_zero_of_mul h)
  refine ⟨(ρ₁, ρ₂), fun Q hQ hρ ↦ ?_⟩
  have hC : ∀ y, C.IsSub fun x ↦ Q (x, y) := fun y σ τ hd hτ ↦ by
    have hne : σ ≠ τ := fun h ↦ hd (by rw [h, d_self])
    exact hQ (σ, y) (τ, y) (by simpa [tensor_d, sgn, d_self, diagonal_apply_ne _ hne] using hd) hτ
  have hD : ∀ x, D.IsSub fun y ↦ Q (x, y) := fun x σ τ hd hτ ↦ by
    have hne : σ ≠ τ := fun h ↦ hd (by rw [h, d_self])
    exact hQ (x, σ) (x, τ) (by simpa [tensor_d, sgn, d_self, one_apply_ne hne] using hd) hτ
  obtain ⟨hc, hc'⟩ := h₁ _ (hC ρ₂) hρ
  exact ⟨(h₂ _ (hD c) hc).1, (h₂ _ (hD c') hc').2⟩

/-- A cell-local map is local for every cover `A ∪ B` by subcomplexes: cochains vanishing on
`B` go to chains of `A`. -/
theorem «local» (hu : IsCellLocal u) {A B : C.X → Prop} (hA : C.IsSub A) (hB : C.IsSub B)
    (hcov : ∀ σ, A σ ∨ B σ) : ∀ σ τ, u σ τ ≠ 0 → ¬B τ → A σ := fun σ τ h hτ ↦ by
  obtain ⟨ρ, hρ⟩ := hu σ τ h
  rcases hcov ρ with h' | h'
  · exact (hρ A hA h').1
  · exact (hτ (hρ B hB h').2).elim

end IsCellLocal

/-- A diagonal is cellular: `Δρ` lies in `Q ⊗ Q` for every subcomplex `Q ∋ ρ`. -/
def IsCellular (Δ : Diagonal C) : Prop :=
  ∀ Q : C.X → Prop, C.IsSub Q → ∀ σ τ ρ, Δ.f (σ, τ) ρ ≠ 0 → Q ρ → Q σ ∧ Q τ

variable {hW}

theorem isCellLocal_cap {Δ : Diagonal W} (hΔ : IsCellular Δ) {z : W.X → ℚ}
    (hz : IsCycle W N z) : IsCellLocal (cap hW Δ hz).f := fun σ τ h ↦ by
  rw [cap_f_apply] at h
  obtain ⟨ρ, -, hρ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨ρ, fun Q hQ h' ↦ hΔ Q hQ σ τ ρ (left_ne_zero_of_mul hρ) h'⟩

theorem IsCellLocal.transpose_f {φ : Hom (W.dual N hW) W} (h : IsCellLocal φ.f) :
    IsCellLocal (BasedComplex.transpose hW hW φ).f :=
  h.transpose.diagonal_mul _

theorem IsCellLocal.sym_f {φ : Hom (W.dual N hW) W} (h : IsCellLocal φ.f) :
    IsCellLocal (sym hW φ).f :=
  (h.add h.transpose_f).smul _

/-! ### Relative caps of pairs -/

variable (hW) in
/-- The relative cap of a pair `(W, P)`: for a homogeneous `N`-chain `z` with `∂z` in `P` and a
cellular diagonal, `λ(Δ z)` on cochains vanishing on `P` is a chain map
`C^{N-*}(W, P) → C(W)` (relative cochains to absolute chains). -/
def relCap (Δ : Diagonal W) (hΔ : IsCellular Δ) {P : W.X → Prop} [DecidablePred P]
    (hP : W.IsSub P) {z : W.X → ℚ} (hz : ∀ σ, z σ ≠ 0 → W.deg σ = N)
    (hdz : ∀ σ, (W.d *ᵥ z) σ ≠ 0 → P σ) :
    Hom ((W.restrict (fun σ ↦ ¬P σ) hP.isLocallyClosed_compl).dual N (hW.restrict _ _)) W where
  f := (slant (Δ.f *ᵥ z)).submatrix id Subtype.val
  deg0 σ τ h := by
    obtain ⟨ρ, h₁, h₂⟩ := exists_mulVec_ne_zero h
    have := Δ.deg0 (σ, τ.1) ρ h₁
    have := hz ρ h₂
    have := hW τ.1
    change (W.deg σ : ℤ) = ((N - W.deg τ.1 : ℕ) : ℤ) + 0
    change ((W.deg σ + W.deg τ.1 : ℕ) : ℤ) = _ + 0 at *
    omega
  comm := by
    have ht : IsHomog W N (Δ.f *ᵥ z) := fun σ τ h ↦ by
      obtain ⟨ρ, h₁, h₂⟩ := exists_mulVec_ne_zero h
      have := Δ.deg0 (σ, τ) ρ h₁
      have := hz ρ h₂
      change ((W.deg σ + W.deg τ : ℕ) : ℤ) = _ + 0 at *
      omega
    ext σ τ
    change (W.d * slant (Δ.f *ᵥ z)) σ τ.1 =
      ((slant (Δ.f *ᵥ z)).submatrix id Subtype.val *
        ((W.restrict (fun σ ↦ ¬P σ) _).dual N (hW.restrict _ _)).d : Matrix W.X _ ℚ) σ τ
    rw [restrict_dual_d hW, mul_submatrix_apply, ← sub_eq_zero, id, ← Matrix.sub_apply,
      d_mul_slant_sub hW ht,
      slant_apply, mulVec_mulVec, Δ.comm, ← mulVec_mulVec]
    · refine Finset.sum_eq_zero fun ρ _ ↦ by_contra fun h ↦ τ.2 ?_
      exact (hΔ P hP σ τ.1 ρ (left_ne_zero_of_mul h) (hdz ρ (right_ne_zero_of_mul h))).2
    · intro κ hκ hPκ
      refine τ.2 (hP _ _ (fun h₀ ↦ right_ne_zero_of_mul hκ ?_) hPκ)
      rw [dual_d_apply, h₀]; ring

theorem relCap_f_apply (Δ : Diagonal W) (hΔ : IsCellular Δ) {P : W.X → Prop} [DecidablePred P]
    (hP : W.IsSub P) {z : W.X → ℚ} (hz) (hdz) (σ : W.X) (τ : {σ // ¬P σ}) :
    (relCap hW Δ hΔ hP (z := z) hz hdz).f σ τ = (Δ.f *ᵥ z) (σ, τ.1) := rfl

theorem IsCellLocal.tensor_hom {D : BasedComplex} {M : ℕ} {hD : D.DimLE M}
    {P : SymDuality W N hW} {Q : SymDuality D M hD} (hP : IsCellLocal P.hom.f)
    (hQ : IsCellLocal Q.hom.f) : IsCellLocal (P.tensor Q).hom.f := by
  rw [SymDuality.tensor_hom_f]
  exact (hP.kronecker hQ).mul_diagonal _

/-! ### The excision ladder -/

variable (hW) {A B : W.X → Prop} [DecidablePred A] [DecidablePred B]

/-- Left column: `C^{N-*}(W, W_B) → C(W_A)`. -/
def ladderLeft (φ : Hom (W.dual N hW) W) (hA : W.IsSub A) (hB : W.IsSub B)
    (hloc : ∀ σ τ, φ.f σ τ ≠ 0 → ¬B τ → A σ) :
    Hom ((W.restrict (fun σ ↦ ¬B σ) hB.isLocallyClosed_compl).dual N (hW.restrict _ _))
      (W.restrict A hA.isLocallyClosed) :=
  φ.restrictDual hW A (fun σ ↦ ¬B σ) _ _ (fun _ κ τ _ hτ _ h ↦ hloc κ τ h hτ)
    (fun _ _ _ _ hτ _ h hκ ↦ hτ (hB _ _ h hκ))

/-- Right column: the B-pair map `C^{N-*}(W_B) → C(W_B, Σ) = W/A` (absolute cochains to
relative chains). -/
def ladderRight (φ : Hom (W.dual N hW) W) (hA : W.IsSub A) (hB : W.IsSub B)
    (hloc : ∀ σ τ, φ.f σ τ ≠ 0 → ¬B τ → A σ) :
    Hom ((W.restrict B hB.isLocallyClosed).dual N (hW.restrict _ _))
      (W.restrict (fun σ ↦ ¬A σ) hA.isLocallyClosed_compl) :=
  φ.restrictDual hW (fun σ ↦ ¬A σ) B _ _ (fun _ _ _ hσ _ h _ hκ ↦ hσ (hA _ _ h hκ))
    (fun σ κ _ hσ _ h _ ↦ by_contra fun hκ ↦ hσ (hloc σ κ h hκ))

/-- The opposite B-pair map `C^{N-*}(W_B, Σ) → C(W_B)` (relative cochains to absolute chains). -/
def relB (φ : Hom (W.dual N hW) W) (hA : W.IsSub A) (hB : W.IsSub B)
    (hloc' : ∀ σ τ, φ.f σ τ ≠ 0 → ¬A τ → B σ) :
    Hom ((W.restrict (fun σ ↦ ¬A σ) hA.isLocallyClosed_compl).dual N (hW.restrict _ _))
      (W.restrict B hB.isLocallyClosed) :=
  ladderLeft hW φ hB hA hloc'

theorem inclHom_mul_apply {Z : Type*} {P : W.X → Prop} [DecidablePred P] (hP : W.IsSub P)
    (M : Matrix {σ // P σ} Z ℚ) (ρ : W.X) (z : Z) :
    ((inclHom hP).f * M) ρ z = if h : P ρ then M ⟨ρ, h⟩ z else 0 := by
  simp only [inclHom, mul_apply, of_apply, ite_mul, one_mul, zero_mul]
  split_ifs with h
  · rw [Finset.sum_eq_single_of_mem (⟨ρ, h⟩ : {σ // P σ}) (Finset.mem_univ _)
      fun κ _ hκ ↦ ite_eq_right fun h' ↦ hκ (Subtype.ext h'.symm)]
    simp
  · exact Finset.sum_eq_zero fun κ _ ↦ ite_eq_right fun (h' : ρ = κ.1) ↦ h (h' ▸ κ.2)

theorem mul_inclHom_transpose_apply {Z : Type*} {P : W.X → Prop} [DecidablePred P]
    (hP : W.IsSub P) (M : Matrix Z {σ // P σ} ℚ) (z : Z) (ρ : W.X) :
    (M * (inclHom hP).fᵀ) z ρ = if h : P ρ then M z ⟨ρ, h⟩ else 0 := by
  rw [← Matrix.transpose_transpose (M * _), transpose_apply, transpose_mul,
    Matrix.transpose_transpose, inclHom_mul_apply]
  rfl

theorem projHom_mul_apply {Z : Type*} {P : W.X → Prop} [DecidablePred P] (hP : W.IsSub P)
    (M : Matrix W.X Z ℚ) (σ : {σ // ¬P σ}) (z : Z) : ((projHom hP).f * M) σ z = M σ.1 z := by
  simp [projHom, mul_apply]

theorem mul_projHom_transpose_apply {Z : Type*} {P : W.X → Prop} [DecidablePred P]
    (hP : W.IsSub P) (M : Matrix Z W.X ℚ) (z : Z) (σ : {σ // ¬P σ}) :
    (M * (projHom hP).fᵀ) z σ = M z σ.1 := by
  simp [projHom, mul_apply]

/-- The left square commutes strictly: `z∩` on `C^{N-*}(W, W_B)` is `z∩` into `C(W_A)`. -/
theorem ladderLeft_comm (φ : Hom (W.dual N hW) W) (hA : W.IsSub A) (hB : W.IsSub B)
    (hloc : ∀ σ τ, φ.f σ τ ≠ 0 → ¬B τ → A σ) :
    (inclHom hA).comp (ladderLeft hW φ hA hB hloc) =
      φ.comp ((projHom hB).dual N hW (hW.restrict _ _)) := by
  ext ρ τ
  rw [Hom.comp_f, Hom.comp_f, Hom.dual_f, inclHom_mul_apply,
    show (φ.f * (projHom hB).fᵀ) ρ τ = φ.f ρ τ.1 from mul_projHom_transpose_apply hB φ.f ρ τ]
  split_ifs with h
  · rfl
  · exact (by_contra fun h' ↦ h (hloc ρ τ.1 h' τ.2) : φ.f ρ τ.1 = 0).symm

/-- The right square commutes strictly: `(z∩ξ) mod W_A` depends only on `ξ|W_B`. -/
theorem ladderRight_comm (φ : Hom (W.dual N hW) W) (hA : W.IsSub A) (hB : W.IsSub B)
    (hloc : ∀ σ τ, φ.f σ τ ≠ 0 → ¬B τ → A σ) :
    (projHom hA).comp φ =
      (ladderRight hW φ hA hB hloc).comp ((inclHom hB).dual N (hW.restrict _ _) hW) := by
  ext σ τ
  rw [Hom.comp_f, Hom.comp_f, Hom.dual_f, projHom_mul_apply,
    show ((ladderRight hW φ hA hB hloc).f * (inclHom hB).fᵀ) σ τ = _ from
      mul_inclHom_transpose_apply hB (ladderRight hW φ hA hB hloc).f σ τ]
  split_ifs with h
  · rfl
  · exact by_contra fun h' ↦ σ.2 (hloc σ.1 τ h' h)

/-- For symmetric `φ`, the two B-pair maps are transposes of each other. -/
theorem transpose_relB {φ : Hom (W.dual N hW) W} (hφ : IsSymm hW φ) (hA : W.IsSub A)
    (hB : W.IsSub B) (hloc : ∀ σ τ, φ.f σ τ ≠ 0 → ¬B τ → A σ)
    (hloc' : ∀ σ τ, φ.f σ τ ≠ 0 → ¬A τ → B σ) :
    BasedComplex.transpose (hW.restrict _ _) (hW.restrict _ _) (relB hW φ hA hB hloc') =
      ladderRight hW φ hA hB hloc := by
  ext σ τ
  rw [transpose_f_apply]
  exact (isSymm_iff φ).mp hφ σ.1 τ.1

/-- The bottom row is a short exact sequence split by bases: `W/A ∘ W_A = 0` and
`i iᵀ + pᵀ p = 1`. -/
theorem projHom_comp_inclHom (hA : W.IsSub A) : ((projHom hA).comp (inclHom hA)).f = 0 := by
  ext σ τ
  rw [Hom.comp_f, projHom_mul_apply]
  exact ite_eq_right fun (h : σ.1 = τ.1) ↦ σ.2 (h ▸ τ.2)

theorem projHom_transpose_mul_apply {Z : Type*} {P : W.X → Prop} [DecidablePred P]
    (hP : W.IsSub P) (M : Matrix {σ // ¬P σ} Z ℚ) (ρ : W.X) (z : Z) :
    ((projHom hP).fᵀ * M) ρ z = if h : ¬P ρ then M ⟨ρ, h⟩ z else 0 := by
  simp only [projHom, mul_apply, transpose_apply, of_apply, ite_mul, one_mul, zero_mul]
  by_cases h : P ρ
  · rw [dite_eq_right (not_not.mpr h)]
    exact Finset.sum_eq_zero fun κ _ ↦ ite_eq_right fun (h' : κ.1 = ρ) ↦ κ.2 (h' ▸ h)
  · rw [dite_eq_left h, Finset.sum_eq_single_of_mem (⟨ρ, h⟩ : {σ // ¬P σ}) (Finset.mem_univ _)
      fun κ _ hκ ↦ ite_eq_right fun h' ↦ hκ (Subtype.ext h')]
    simp

theorem inclHom_split (hA : W.IsSub A) :
    (inclHom hA).f * (inclHom hA).fᵀ + (projHom hA).fᵀ * (projHom hA).f = 1 := by
  ext ρ ρ'
  rw [Matrix.add_apply, inclHom_mul_apply, projHom_transpose_mul_apply]
  by_cases h : A ρ <;> simp [h, inclHom, projHom, one_apply, eq_comm]

end BasedComplex

end HSFormal.Cubical
