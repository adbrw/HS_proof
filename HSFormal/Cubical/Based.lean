import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Int

/-!
# Based rational chain complexes (cubical chain model, module C1)

A `BasedComplex` is a finite type of cells with degrees and one boundary matrix in the
target-row convention of `HSFormal.prop`: `d σ τ` is the coefficient of `σ` in `∂τ`.  Chain
maps, homotopies and homotopy equivalences are matrices subject to one exact identity each.
The tensor product has the Koszul differential `d ⊗ₖ 1 + sgn ⊗ₖ d` with `sgn = diag (-1)^deg`,
and maps and homotopies tensor with the matching signs.  `restrict` cuts out subcomplexes,
quotients and relative complexes; a `CellEmbedding` is a cellular inclusion onto a subcomplex
(the boxes of a grid).
-/

namespace HSFormal.Cubical

open Matrix
open scoped Kronecker

/-- A finite based rational chain complex in total-matrix form. -/
structure BasedComplex where
  X : Type
  [fin : Fintype X]
  [dec : DecidableEq X]
  deg : X → ℕ
  d : Matrix X X ℚ
  d_deg : ∀ σ τ, d σ τ ≠ 0 → deg τ = deg σ + 1
  d_d : d * d = 0

attribute [instance] BasedComplex.fin BasedComplex.dec

theorem exists_mul_apply_ne_zero {l m n : Type*} [Fintype m] {v : Matrix l m ℚ}
    {u : Matrix m n ℚ} {a : l} {b : n} (h : (v * u) a b ≠ 0) : ∃ c, v a c ≠ 0 ∧ u c b ≠ 0 := by
  obtain ⟨c, -, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨c, left_ne_zero_of_mul hc, right_ne_zero_of_mul hc⟩

theorem exists_mulVec_ne_zero {m n : Type*} [Fintype n] {u : Matrix m n ℚ} {γ : n → ℚ} {a : m}
    (h : (u *ᵥ γ) a ≠ 0) : ∃ c, u a c ≠ 0 ∧ γ c ≠ 0 := by
  obtain ⟨c, -, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨c, left_ne_zero_of_mul hc, right_ne_zero_of_mul hc⟩

namespace BasedComplex

variable {A B C C' C'' D D' D'' : BasedComplex}

/-- The Koszul sign matrix `diag (-1)^deg`. -/
def sgn (C : BasedComplex) : Matrix C.X C.X ℚ := diagonal fun σ ↦ (-1) ^ C.deg σ

/-- `u : C → D` raises degrees by exactly `k` on its support. -/
def HasDeg (C D : BasedComplex) (k : ℤ) (u : Matrix D.X C.X ℚ) : Prop :=
  ∀ σ τ, u σ τ ≠ 0 → (D.deg σ : ℤ) = C.deg τ + k

namespace HasDeg

variable {k l : ℤ} {u v : Matrix D.X C.X ℚ}

theorem zero : HasDeg C D k 0 := fun _ _ h ↦ (h rfl).elim

theorem one : HasDeg C C 0 1 := fun σ τ h ↦ by
  rw [Matrix.one_apply] at h; split_ifs at h with hst
  · simp [hst]
  · exact (h rfl).elim

theorem add (hu : HasDeg C D k u) (hv : HasDeg C D k v) : HasDeg C D k (u + v) := fun σ τ h ↦ by
  by_cases h' : u σ τ = 0
  · exact hv σ τ (by simpa [h'] using h)
  · exact hu σ τ h'

theorem smul (c : ℚ) (hu : HasDeg C D k u) : HasDeg C D k (c • u) :=
  fun σ τ h ↦ hu σ τ (right_ne_zero_of_mul h)

theorem neg (hu : HasDeg C D k u) : HasDeg C D k (-u) := by
  simpa using hu.smul (-1)

theorem sub (hu : HasDeg C D k u) (hv : HasDeg C D k v) : HasDeg C D k (u - v) := by
  rw [sub_eq_add_neg]; exact hu.add hv.neg

theorem mul {w : Matrix A.X D.X ℚ} (hw : HasDeg D A l w) (hu : HasDeg C D k u) :
    HasDeg C A (k + l) (w * u) := fun σ τ h ↦ by
  obtain ⟨c, h₁, h₂⟩ := exists_mul_apply_ne_zero h
  rw [hw σ c h₁, hu c τ h₂]; ring

theorem of_eq {k' : ℤ} (hu : HasDeg C D k u) (h : k = k') : HasDeg C D k' u := h ▸ hu

/-- Koszul signs: `sgn_D u = (-1)^k u sgn_C`. -/
theorem sgn_mul (hu : HasDeg C D k u) : D.sgn * u = ((-1 : ℚ) ^ k) • (u * C.sgn) := by
  ext σ τ
  simp only [sgn, diagonal_mul, mul_diagonal, Matrix.smul_apply, smul_eq_mul]
  by_cases h : u σ τ = 0
  · simp [h]
  · rw [← zpow_natCast, hu σ τ h, zpow_add₀ (by norm_num), zpow_natCast]; ring

end HasDeg

theorem d_hasDeg (C : BasedComplex) : HasDeg C C (-1) C.d := fun σ τ h ↦ by
  rw [C.d_deg σ τ h]; push_cast; ring

/-- The augmentation `ε`: the coefficient sum over vertices. -/
def aug (C : BasedComplex) (σ : C.X) : ℚ := if C.deg σ = 0 then 1 else 0

/-- `i ε` with base vertex `b`: the matrix `σ ↦ ε(σ) b`. -/
def augAt (C : BasedComplex) (b : C.X) : Matrix C.X C.X ℚ :=
  Matrix.of fun σ τ ↦ if σ = b then C.aug τ else 0

theorem d_mul_augAt {b : C.X} (hb : C.deg b = 0) : C.d * C.augAt b = 0 := by
  ext σ τ
  simp only [mul_apply, augAt, of_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, Matrix.zero_apply]
  by_cases h : C.d σ b = 0
  · simp [h]
  · have := C.d_deg σ b h; omega

/-! ### Koszul sign -/

theorem sgn_hasDeg (C : BasedComplex) : HasDeg C C 0 C.sgn := fun σ τ h ↦ by
  by_cases hs : σ = τ
  · simp [hs]
  · exact (h (diagonal_apply_ne _ hs)).elim

theorem sgn_mul_sgn (C : BasedComplex) : C.sgn * C.sgn = 1 := by
  simp only [sgn, diagonal_mul_diagonal, ← pow_add, ← two_mul, pow_mul]; simp

theorem HasDeg.sgn_comm {u : Matrix D.X C.X ℚ} (hu : HasDeg C D 0 u) :
    D.sgn * u = u * C.sgn := by simpa using hu.sgn_mul

theorem HasDeg.sgn_anticomm {u : Matrix D.X C.X ℚ} (hu : HasDeg C D 1 u) :
    D.sgn * u = -(u * C.sgn) := by simpa using hu.sgn_mul

theorem d_sgn (C : BasedComplex) : C.d * C.sgn = -(C.sgn * C.d) := by
  rw [C.d_hasDeg.sgn_mul]; simp

theorem sgn_augAt {b : C.X} (hb : C.deg b = 0) : C.sgn * C.augAt b = C.augAt b := by
  ext σ τ; simp only [sgn, diagonal_mul, augAt, of_apply]; split_ifs with h <;> simp [h, hb]

theorem augAt_sgn (b : C.X) : C.augAt b * C.sgn = C.augAt b := by
  ext σ τ; simp only [sgn, mul_diagonal, augAt, aug, of_apply]; split_ifs with h h' <;> simp_all

/-! ### Chain maps, homotopies, equivalences -/

/-- A chain map `C → D`. -/
@[ext]
structure Hom (C D : BasedComplex) where
  f : Matrix D.X C.X ℚ
  deg0 : HasDeg C D 0 f
  comm : D.d * f = f * C.d

/-- An exact chain homotopy `f - g = d h + h d`. -/
structure Htpy {C D : BasedComplex} (f g : Hom C D) where
  h : Matrix D.X C.X ℚ
  deg1 : HasDeg C D 1 h
  eq : f.f - g.f = D.d * h + h * C.d

namespace Hom

/-- The identity chain map. -/
def id (C : BasedComplex) : Hom C C := ⟨1, HasDeg.one, by simp⟩

/-- Composition `g ∘ f` (matrix product `g.f * f.f`). -/
def comp (g : Hom D D') (f : Hom C D) : Hom C D' :=
  ⟨g.f * f.f, by simpa using g.deg0.mul f.deg0, by
    rw [← Matrix.mul_assoc, g.comm, Matrix.mul_assoc, f.comm, Matrix.mul_assoc]⟩

@[simp] theorem id_f : (id C).f = 1 := rfl
@[simp] theorem comp_f (g : Hom D D') (f : Hom C D) : (g.comp f).f = g.f * f.f := rfl

theorem comp_id (f : Hom C D) : f.comp (id C) = f := Hom.ext (Matrix.mul_one _)
theorem id_comp (f : Hom C D) : (id D).comp f = f := Hom.ext (Matrix.one_mul _)
theorem comp_assoc (h : Hom D' D'') (g : Hom D D') (f : Hom C D) :
    (h.comp g).comp f = h.comp (g.comp f) := Hom.ext (Matrix.mul_assoc _ _ _)

/-- The sum of chain maps. -/
def add (f g : Hom C D) : Hom C D :=
  ⟨f.f + g.f, f.deg0.add g.deg0, by rw [Matrix.mul_add, Matrix.add_mul, f.comm, g.comm]⟩

/-- A scalar multiple of a chain map. -/
def smul (c : ℚ) (f : Hom C D) : Hom C D :=
  ⟨c • f.f, f.deg0.smul c, by rw [Matrix.mul_smul, Matrix.smul_mul, f.comm]⟩

end Hom

namespace Htpy

variable {f g k : Hom C D}

/-- The zero homotopy. -/
def refl (f : Hom C D) : Htpy f f := ⟨0, HasDeg.zero, by simp⟩

/-- Equal maps are homotopic. -/
def ofEq (h : f = g) : Htpy f g := h ▸ refl f

/-- The reversed homotopy `-h`. -/
def symm (H : Htpy f g) : Htpy g f :=
  ⟨-H.h, H.deg1.neg, by rw [Matrix.mul_neg, Matrix.neg_mul, ← neg_add, ← H.eq, neg_sub]⟩

/-- The concatenated homotopy `h + h'`. -/
def trans (H : Htpy f g) (H' : Htpy g k) : Htpy f k :=
  ⟨H.h + H'.h, H.deg1.add H'.deg1, by
    rw [Matrix.mul_add, Matrix.add_mul, ← sub_add_sub_cancel f.f g.f k.f, H.eq, H'.eq]; abel⟩

/-- Postcomposition `p ∘ H`. -/
def compLeft (p : Hom D D') (H : Htpy f g) : Htpy (p.comp f) (p.comp g) :=
  ⟨p.f * H.h, by simpa using p.deg0.mul H.deg1, by
    simp only [Hom.comp_f, ← Matrix.mul_sub, H.eq, Matrix.mul_add, ← Matrix.mul_assoc, p.comm]⟩

/-- Precomposition `H ∘ p`. -/
def compRight (H : Htpy f g) (p : Hom C' C) : Htpy (f.comp p) (g.comp p) :=
  ⟨H.h * p.f, by simpa using H.deg1.mul p.deg0, by
    simp only [Hom.comp_f, ← Matrix.sub_mul, H.eq, Matrix.add_mul, Matrix.mul_assoc, p.comm]⟩

/-- Homotopic maps compose to homotopic maps. -/
def comp {f' g' : Hom D D'} (H' : Htpy f' g') (H : Htpy f g) : Htpy (f'.comp f) (g'.comp g) :=
  (H'.compRight f).trans (H.compLeft g')

/-- Transport a homotopy along equalities of its endpoints. -/
def congr {f' g' : Hom C D} (H : Htpy f g) (hf : f = f') (hg : g = g') : Htpy f' g' :=
  hf ▸ hg ▸ H

end Htpy

/-- A chain homotopy equivalence with explicit homotopies. -/
structure HtpyEquiv (C D : BasedComplex) where
  hom : Hom C D
  inv : Hom D C
  homInv : Htpy (inv.comp hom) (Hom.id C)
  invHom : Htpy (hom.comp inv) (Hom.id D)

namespace HtpyEquiv

/-- The identity equivalence. -/
def refl (C : BasedComplex) : HtpyEquiv C C :=
  ⟨Hom.id C, Hom.id C, Htpy.ofEq (Hom.id_comp _), Htpy.ofEq (Hom.id_comp _)⟩

/-- The inverse equivalence. -/
def symm (e : HtpyEquiv C D) : HtpyEquiv D C := ⟨e.inv, e.hom, e.invHom, e.homInv⟩

/-- Composition of homotopy equivalences. -/
def trans (e : HtpyEquiv C D) (e' : HtpyEquiv D D') : HtpyEquiv C D' where
  hom := e'.hom.comp e.hom
  inv := e.inv.comp e'.inv
  homInv := by
    refine (((e'.homInv.compRight e.hom).compLeft e.inv).congr ?_ ?_).trans e.homInv
    · simp only [Hom.comp_assoc]
    · rw [Hom.id_comp]
  invHom := by
    refine (((e.invHom.compRight e'.inv).compLeft e'.hom).congr ?_ ?_).trans e'.invHom
    · simp only [Hom.comp_assoc]
    · rw [Hom.id_comp]

end HtpyEquiv

/-! ### Tensor products -/

/-- The point: one vertex, `d = 0`. -/
@[reducible]
def point : BasedComplex where
  X := Unit
  deg _ := 0
  d := 0
  d_deg _ _ h := (h rfl).elim
  d_d := by simp

/-- Tensor product, `d(a ⊗ b) = da ⊗ b + (-1)^|a| a ⊗ db`. -/
@[reducible]
def tensor (C D : BasedComplex) : BasedComplex where
  X := C.X × D.X
  deg p := C.deg p.1 + D.deg p.2
  d := C.d ⊗ₖ (1 : Matrix D.X D.X ℚ) + C.sgn ⊗ₖ D.d
  d_deg := by
    rintro ⟨σ, σ'⟩ ⟨τ, τ'⟩ h
    rw [Matrix.add_apply, kronecker_apply, kronecker_apply] at h
    by_cases h₁ : C.d σ τ * (1 : Matrix D.X D.X ℚ) σ' τ' = 0
    · rw [h₁, zero_add] at h
      have hs : σ = τ := by
        by_contra hs; exact h (by simp [sgn, diagonal_apply_ne _ hs])
      have := D.d_deg σ' τ' (right_ne_zero_of_mul h)
      simp only [hs, this]; omega
    · have hs : σ' = τ' := by
        by_contra hs; exact h₁ (by simp [one_apply_ne hs])
      have := C.d_deg σ τ (left_ne_zero_of_mul h₁)
      simp only [hs, this]; omega
  d_d := by
    have hS : C.sgn * C.d + C.d * C.sgn = 0 := by rw [d_sgn]; abel
    simp only [add_mul, mul_add, ← mul_kronecker_mul, C.d_d, D.d_d, Matrix.mul_one,
      Matrix.one_mul, zero_kronecker, kronecker_zero, zero_add, add_zero, sgn_mul_sgn]
    rw [← add_kronecker, hS, zero_kronecker]

theorem tensor_d : (C.tensor D).d = C.d ⊗ₖ (1 : Matrix D.X D.X ℚ) + C.sgn ⊗ₖ D.d := rfl

theorem tensor_sgn : (C.tensor D).sgn = C.sgn ⊗ₖ D.sgn := by
  simp [sgn, diagonal_kronecker_diagonal, pow_add]

theorem tensor_aug (p : (C.tensor D).X) : (C.tensor D).aug p = C.aug p.1 * D.aug p.2 := by
  simp only [aug, Nat.add_eq_zero_iff]; split_ifs <;> simp_all

theorem tensor_augAt (b : C.X) (b' : D.X) :
    (C.tensor D).augAt (b, b') = C.augAt b ⊗ₖ D.augAt b' := by
  ext ⟨σ, σ'⟩ ⟨τ, τ'⟩
  simp only [augAt, of_apply, kronecker_apply, tensor_aug, Prod.mk.injEq]
  split_ifs <;> simp_all

theorem sub_kronecker {l m n p : Type*} (A A' : Matrix l m ℚ) (B : Matrix n p ℚ) :
    (A - A') ⊗ₖ B = A ⊗ₖ B - A' ⊗ₖ B := by ext; simp [sub_mul]

theorem neg_kronecker {l m n p : Type*} (A : Matrix l m ℚ) (B : Matrix n p ℚ) :
    (-A) ⊗ₖ B = -(A ⊗ₖ B) := by ext; simp

theorem kronecker_sub {l m n p : Type*} (A : Matrix l m ℚ) (B B' : Matrix n p ℚ) :
    A ⊗ₖ (B - B') = A ⊗ₖ B - A ⊗ₖ B' := by ext; simp [mul_sub]

theorem HasDeg.kronecker {k l : ℤ} {u : Matrix C'.X C.X ℚ} {v : Matrix D'.X D.X ℚ}
    (hu : HasDeg C C' k u) (hv : HasDeg D D' l v) :
    HasDeg (C.tensor D) (C'.tensor D') (k + l) (u ⊗ₖ v) := by
  rintro ⟨σ, σ'⟩ ⟨τ, τ'⟩ h
  rw [kronecker_apply] at h
  have h₁ := hu σ τ (left_ne_zero_of_mul h)
  have h₂ := hv σ' τ' (right_ne_zero_of_mul h)
  simp only [Nat.cast_add, h₁, h₂]; ring

/-- Tensor product of chain maps. -/
def Hom.tensor (f : Hom C C') (g : Hom D D') : Hom (C.tensor D) (C'.tensor D') where
  f := f.f ⊗ₖ g.f
  deg0 := (f.deg0.kronecker g.deg0).of_eq (by simp)
  comm := by
    simp only [Matrix.add_mul, Matrix.mul_add, ← mul_kronecker_mul, Matrix.mul_one,
      Matrix.one_mul, f.comm, g.comm, f.deg0.sgn_comm]

@[simp] theorem Hom.tensor_f (f : Hom C C') (g : Hom D D') : (f.tensor g).f = f.f ⊗ₖ g.f := rfl

theorem Hom.tensor_comp (f' : Hom C' C'') (f : Hom C C') (g' : Hom D' D'') (g : Hom D D') :
    (f'.comp f).tensor (g'.comp g) = (f'.tensor g').comp (f.tensor g) :=
  Hom.ext (mul_kronecker_mul _ _ _ _)

theorem Hom.tensor_id : (Hom.id C).tensor (Hom.id D) = Hom.id (C.tensor D) :=
  Hom.ext one_kronecker_one

/-- `H ⊗ g : f ⊗ g ≃ f' ⊗ g`. -/
def Htpy.tensorRight {f f' : Hom C C'} (H : Htpy f f') (g : Hom D D') :
    Htpy (f.tensor g) (f'.tensor g) where
  h := H.h ⊗ₖ g.f
  deg1 := (H.deg1.kronecker g.deg0).of_eq (by simp)
  eq := by
    rw [Hom.tensor_f, Hom.tensor_f, ← sub_kronecker, H.eq, tensor_d, tensor_d, Matrix.add_mul,
      Matrix.mul_add,
      ← mul_kronecker_mul, ← mul_kronecker_mul, ← mul_kronecker_mul, ← mul_kronecker_mul, g.comm,
      H.deg1.sgn_anticomm, Matrix.mul_one, Matrix.one_mul, neg_kronecker, add_kronecker]
    abel

/-- `f ⊗ H : f ⊗ g ≃ f ⊗ g'`, with the Koszul sign `(f sgn) ⊗ H`. -/
def Htpy.tensorLeft (f : Hom C C') {g g' : Hom D D'} (H : Htpy g g') :
    Htpy (f.tensor g) (f.tensor g') where
  h := (f.f * C.sgn) ⊗ₖ H.h
  deg1 := by simpa using (f.deg0.mul C.sgn_hasDeg).kronecker H.deg1
  eq := by
    have e₁ : C'.d * (f.f * C.sgn) = -(f.f * C.sgn * C.d) := by
      rw [← Matrix.mul_assoc, f.comm, Matrix.mul_assoc, d_sgn, Matrix.mul_neg, Matrix.mul_assoc]
    have e₂ : C'.sgn * (f.f * C.sgn) = f.f := by
      rw [← Matrix.mul_assoc, f.deg0.sgn_comm, Matrix.mul_assoc, sgn_mul_sgn, Matrix.mul_one]
    have e₃ : f.f * C.sgn * C.sgn = f.f := by rw [Matrix.mul_assoc, sgn_mul_sgn, Matrix.mul_one]
    rw [Hom.tensor_f, Hom.tensor_f, ← kronecker_sub, H.eq, tensor_d, tensor_d, Matrix.add_mul,
      Matrix.mul_add, ← mul_kronecker_mul, ← mul_kronecker_mul, ← mul_kronecker_mul,
      ← mul_kronecker_mul, e₁, e₂, e₃, Matrix.mul_one, Matrix.one_mul, neg_kronecker,
      kronecker_add]
    abel

/-- Tensor product of homotopy equivalences. -/
def HtpyEquiv.tensor (e : HtpyEquiv C C') (e' : HtpyEquiv D D') :
    HtpyEquiv (C.tensor D) (C'.tensor D') where
  hom := e.hom.tensor e'.hom
  inv := e.inv.tensor e'.inv
  homInv := (((e.homInv.tensorRight _).trans (Htpy.tensorLeft _ e'.homInv)).congr
    (Hom.tensor_comp _ _ _ _) Hom.tensor_id)
  invHom := (((e.invHom.tensorRight _).trans (Htpy.tensorLeft _ e'.invHom)).congr
    (Hom.tensor_comp _ _ _ _) Hom.tensor_id)

theorem tensor_d_ne_zero {σ τ : C.X} {σ' τ' : D.X} (h : (C.tensor D).d (σ, σ') (τ, τ') ≠ 0) :
    (C.d σ τ ≠ 0 ∧ σ' = τ') ∨ (σ = τ ∧ D.d σ' τ' ≠ 0) := by
  rw [tensor_d, Matrix.add_apply, kronecker_apply, kronecker_apply] at h
  by_cases h₁ : C.d σ τ * (1 : Matrix D.X D.X ℚ) σ' τ' = 0
  · rw [h₁, zero_add] at h
    refine .inr ⟨by_contra fun hs ↦ h ?_, right_ne_zero_of_mul h⟩
    simp [sgn, diagonal_apply_ne _ hs]
  · exact .inl ⟨left_ne_zero_of_mul h₁, by_contra fun hs ↦ h₁ (by simp [one_apply_ne hs])⟩

/-! ### Subcomplexes, quotients and relative complexes -/

/-- `P` is a subcomplex: closed under faces. -/
def IsSub (C : BasedComplex) (P : C.X → Prop) : Prop := ∀ σ τ, C.d σ τ ≠ 0 → P τ → P σ

/-- `Q` is a difference of subcomplexes: it contains each cell on a boundary path between two
of its cells.  Subcomplexes, quotients and relative complexes all qualify. -/
def IsLocallyClosed (C : BasedComplex) (Q : C.X → Prop) : Prop :=
  ∀ ρ κ τ, Q ρ → Q τ → C.d ρ κ ≠ 0 → C.d κ τ ≠ 0 → Q κ

variable {P P' : C.X → Prop}

theorem IsSub.isLocallyClosed (h : C.IsSub P) : C.IsLocallyClosed P :=
  fun _ _ _ _ hτ _ h₂ ↦ h _ _ h₂ hτ

theorem IsSub.isLocallyClosed_diff (h : C.IsSub P) (h' : C.IsSub P') :
    C.IsLocallyClosed fun σ ↦ P σ ∧ ¬P' σ :=
  fun _ _ _ hρ hτ h₁ h₂ ↦ ⟨h _ _ h₂ hτ.1, fun hκ ↦ hρ.2 (h' _ _ h₁ hκ)⟩

theorem IsSub.isLocallyClosed_compl (h : C.IsSub P) : C.IsLocallyClosed fun σ ↦ ¬P σ :=
  fun _ _ _ hρ _ h₁ _ hκ ↦ hρ (h _ _ h₁ hκ)

/-- The complex spanned by a locally closed set of cells. -/
abbrev restrict (C : BasedComplex) (Q : C.X → Prop) [DecidablePred Q] (hQ : C.IsLocallyClosed Q) :
    BasedComplex where
  X := {σ // Q σ}
  deg σ := C.deg σ
  d := C.d.submatrix Subtype.val Subtype.val
  d_deg σ τ h := C.d_deg _ _ h
  d_d := by
    ext ρ τ
    have h := congr_fun (congr_fun C.d_d ρ.1) τ.1
    rw [mul_apply, ← Fintype.sum_subtype_add_sum_subtype Q] at h
    have h₂ : ∑ κ : {κ // ¬Q κ}, C.d ρ κ * C.d κ τ = 0 := Finset.sum_eq_zero fun κ _ ↦ by
      by_contra hne
      exact κ.2 (hQ _ _ _ ρ.2 τ.2 (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne))
    rw [h₂, add_zero] at h
    simpa [mul_apply] using h

/-- Inclusion of a subcomplex. -/
def inclHom [DecidablePred P] (hP : C.IsSub P) : Hom (C.restrict P hP.isLocallyClosed) C where
  f := Matrix.of fun ρ σ ↦ if ρ = σ.1 then 1 else 0
  deg0 σ τ h := by
    simp only [of_apply, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at h
    simp [h]
  comm := by
    ext ρ σ
    simp only [mul_apply, of_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, ite_mul, one_mul, zero_mul]
    by_cases hρ : P ρ
    · rw [Finset.sum_eq_single_of_mem (⟨ρ, hρ⟩ : {σ // P σ}) (Finset.mem_univ _)
        fun κ _ hκ ↦ ite_eq_right fun (h : ρ = κ.1) ↦ hκ (Subtype.ext h.symm)]
      simp
    · rw [Finset.sum_eq_zero fun κ _ ↦ ite_eq_right fun (h : ρ = κ.1) ↦ hρ (h ▸ κ.2)]
      by_contra h'; exact hρ (hP _ _ h' σ.2)

/-- Projection onto the quotient by a subcomplex. -/
def projHom [DecidablePred P] (hP : C.IsSub P) :
    Hom C (C.restrict (fun σ ↦ ¬P σ) hP.isLocallyClosed_compl) where
  f := Matrix.of fun σ ρ ↦ if σ.1 = ρ then 1 else 0
  deg0 σ τ h := by
    simp only [of_apply, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at h
    simp [h]
  comm := by
    ext σ ρ
    simp only [mul_apply, of_apply, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    by_cases hρ : P ρ
    · rw [Finset.sum_eq_zero fun κ _ ↦ ite_eq_right fun (h : κ.1 = ρ) ↦ κ.2 (h ▸ hρ)]
      by_contra h'; exact σ.2 (hP _ _ (Ne.symm h') hρ)
    · rw [Finset.sum_eq_single_of_mem (⟨ρ, hρ⟩ : {σ // ¬P σ}) (Finset.mem_univ _)
        fun κ _ hκ ↦ ite_eq_right fun (h : κ.1 = ρ) ↦ hκ (Subtype.ext h)]
      simp

/-! ### Cellular embeddings -/

/-- A cellular embedding onto a subcomplex, e.g. a box of a grid. -/
structure CellEmbedding (Y C : BasedComplex) where
  toFun : Y.X → C.X
  inj : Function.Injective toFun
  deg_eq : ∀ σ, C.deg (toFun σ) = Y.deg σ
  d_eq : ∀ σ τ, C.d (toFun σ) (toFun τ) = Y.d σ τ
  closed : ∀ ρ τ, C.d ρ (toFun τ) ≠ 0 → ∃ σ, toFun σ = ρ

namespace CellEmbedding

variable {Y Y' : BasedComplex} (e : CellEmbedding Y C)

/-- The image, a subcomplex. -/
def range (ρ : C.X) : Prop := ∃ σ, e.toFun σ = ρ

theorem isSub_range : C.IsSub e.range := fun ρ _ h ⟨τ', hτ'⟩ ↦ e.closed ρ τ' (hτ' ▸ h)

/-- The inclusion matrix. -/
def mat : Matrix C.X Y.X ℚ := Matrix.of fun ρ σ ↦ if ρ = e.toFun σ then 1 else 0

theorem mul_mat_apply {Z : Type*} (M : Matrix Z C.X ℚ) (z : Z) (σ : Y.X) :
    (M * e.mat) z σ = M z (e.toFun σ) := by
  simp [mat, mul_apply]

theorem transpose_mat_mul_mat : e.matᵀ * e.mat = 1 := by
  ext σ τ; rw [mul_mat_apply]; simp [mat, one_apply, e.inj.eq_iff, eq_comm]

theorem mat_hasDeg : HasDeg Y C 0 e.mat := fun ρ σ h ↦ by
  simp only [mat, of_apply, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at h
  simp [h, e.deg_eq]

theorem transpose_mat_hasDeg : HasDeg C Y 0 e.matᵀ := fun σ ρ h ↦ by
  simp only [mat, transpose_apply, of_apply, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
    not_not] at h
  simp [h, e.deg_eq]

theorem transpose_mat_mul_d_mul_mat : e.matᵀ * C.d * e.mat = Y.d := by
  ext σ τ; rw [mul_mat_apply]; simp [mat, mul_apply, e.d_eq]

theorem d_mul_mat : C.d * e.mat = e.mat * Y.d := by
  ext ρ τ
  rw [mul_mat_apply]
  simp only [mat, mul_apply, of_apply, ite_mul, one_mul, zero_mul]
  by_cases h : ∃ σ, e.toFun σ = ρ
  · obtain ⟨σ, rfl⟩ := h
    rw [Finset.sum_eq_single σ (fun κ _ hκ ↦ ite_eq_right (e.inj.ne (Ne.symm hκ))) (by simp)]
    simp [e.d_eq]
  · rw [Finset.sum_eq_zero fun σ _ ↦ ite_eq_right fun h' ↦ h ⟨σ, h'.symm⟩]
    by_contra h'; exact h (e.closed _ _ h')

theorem mat_mul_augAt (b : Y.X) : e.mat * Y.augAt b = C.augAt (e.toFun b) * e.mat := by
  ext ρ τ
  rw [mul_mat_apply]
  simp only [mat, augAt, aug, mul_apply, of_apply, ite_mul, one_mul, zero_mul, e.deg_eq]
  rw [Finset.sum_eq_single b (fun κ _ hκ ↦ by simp [hκ]) (by simp)]
  simp

/-- The inclusion chain map. -/
def hom : Hom Y C := ⟨e.mat, e.mat_hasDeg, e.d_mul_mat⟩

/-- Products of embeddings embed into the tensor product. -/
def tensor (e : CellEmbedding Y C) (e' : CellEmbedding Y' D) :
    CellEmbedding (Y.tensor Y') (C.tensor D) where
  toFun := Prod.map e.toFun e'.toFun
  inj := e.inj.prodMap e'.inj
  deg_eq p := by simp [e.deg_eq, e'.deg_eq]
  d_eq p q := by
    simp [sgn, diagonal_apply, one_apply, e.d_eq, e'.d_eq, e.inj.eq_iff,
      e'.inj.eq_iff, e.deg_eq]
  closed := by
    rintro ⟨ρ, ρ'⟩ ⟨τ, τ'⟩ h
    rcases tensor_d_ne_zero h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · obtain ⟨σ, rfl⟩ := e.closed _ _ h₁; exact ⟨(σ, τ'), by simp [h₂]⟩
    · obtain ⟨σ', rfl⟩ := e'.closed _ _ h₂; exact ⟨(τ, σ'), by simp [h₁]⟩

/-- Composition of embeddings. -/
def comp (e' : CellEmbedding C D) (e : CellEmbedding Y C) : CellEmbedding Y D where
  toFun := e'.toFun ∘ e.toFun
  inj := e'.inj.comp e.inj
  deg_eq σ := by simp [e'.deg_eq, e.deg_eq]
  d_eq σ τ := by simp [e'.d_eq, e.d_eq]
  closed ρ τ h := by
    obtain ⟨κ, rfl⟩ := e'.closed _ _ h
    obtain ⟨σ, rfl⟩ := e.closed κ τ (by rwa [← e'.d_eq])
    exact ⟨σ, rfl⟩

end CellEmbedding

end BasedComplex

end HSFormal.Cubical
