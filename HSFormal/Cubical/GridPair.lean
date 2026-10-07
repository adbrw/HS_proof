import HSFormal.Cubical.GridFlag

/-!
# Symmetric pair dualities of cubes (cubical module C4, for the B-pairs of C8)

The ladder maps of a cut of `W` are restrictions of the *symmetric* duality `φ = (φ₀ + Tφ₀)/2`,
whereas `interval.relDuality` is the unsymmetrized relative cap `F = λ(Δz)`.  Here:

* `interval.symMat`: the symmetric cap matrix `e_k^* ↦ ½(v_k + v_{k+1})`,
  `v_j^* ↦ ½(e_{j-1} + e_j)` of `I_{m+1}`; it is the restriction of the circle duality to any arc
  of length `m + 1` (`circle.duality_arc`).
* `interval.symRelDuality : C^{1-*}(I, ∂I) ≃ C(I)` with `hom.f = symMat` (relative columns), the
  same inverse `g = e₀^* ε` as `F`, and homotopies corrected by the restricted flip
  `e_k^* ↦ -½ e_k` (`interval.capRel_sub_symMat`); `interval.symAbsDuality` is its transpose
  `C^{1-*}(I) ≃ C(I, ∂I)` (the ladder's right column).
* `cube.symRelDuality`, `cube.symAbsDuality`: the tensor products, the B-pair maps of the box cut.
-/

namespace HSFormal.Cubical

open Matrix
open scoped Kronecker

namespace BasedComplex

variable {C D : BasedComplex}

/-- `f - (d h + h d)`: a chain map minus a null-homotopic map. -/
def Hom.subNull (f : Hom C D) (h : Matrix D.X C.X ℚ) (hh : HasDeg C D 1 h) : Hom C D where
  f := f.f - (D.d * h + h * C.d)
  deg0 := f.deg0.sub (((D.d_hasDeg.mul hh).of_eq (by ring)).add ((hh.mul C.d_hasDeg).of_eq
    (by ring)))
  comm := by
    rw [Matrix.mul_sub, Matrix.sub_mul, f.comm, Matrix.mul_add, Matrix.add_mul,
      ← Matrix.mul_assoc, D.d_d, Matrix.zero_mul, Matrix.mul_assoc h, C.d_d, Matrix.mul_zero,
      Matrix.mul_assoc]
    abel

/-- `f ≃ f - (d h + h d)` by `h`. -/
def Htpy.subNull (f : Hom C D) (h : Matrix D.X C.X ℚ) (hh : HasDeg C D 1 h) :
    Htpy f (f.subNull h hh) :=
  ⟨h, hh, by simp [Hom.subNull]⟩

/-! ### The interval pair -/

section Interval

variable (m : ℕ)

/-- The symmetric cap matrix `½ (λ(Δz) + Tλ(Δz))` of `I_{m+1}`. -/
def interval.symMat : Matrix (interval (m + 1)).X (interval (m + 1)).X ℚ :=
  Matrix.of fun σ τ ↦ match σ, τ with
    | .inl v, .inr e => (if v = e.castSucc then 1 / 2 else 0) + if v = e.succ then 1 / 2 else 0
    | .inr e, .inl v => (if v = e.succ then 1 / 2 else 0) + if v = e.castSucc then 1 / 2 else 0
    | _, _ => 0

/-- Half the flip homotopy on all cells, `e_k^* ↦ -½ e_k`. -/
def interval.halfFlipFull : Matrix (interval (m + 1)).X (interval (m + 1)).X ℚ :=
  Matrix.of fun σ τ ↦ match σ, τ with
    | .inr e, .inr e' => if e = e' then -(1 / 2) else 0
    | _, _ => 0

/-- Half the restricted flip homotopy on relative cochains. -/
def interval.halfFlip : Matrix (interval (m + 1)).X (interval.rel m).X ℚ :=
  (interval.halfFlipFull m).submatrix id Subtype.val

theorem interval.halfFlip_hasDeg :
    HasDeg ((interval.rel m).dual 1 (interval.dimLE_rel m)) (interval (m + 1)) 1
      (interval.halfFlip m) := by
  rintro σ ⟨τ, hτ⟩ h
  rcases σ with v | e <;> rcases τ with w | f <;>
    simp [interval.halfFlip, interval.halfFlipFull] at h
  subst h; rfl

theorem interval.capRel_sub_symMat :
    (interval.capRel m).f - (interval.symMat m).submatrix id Subtype.val =
      (interval (m + 1)).d * interval.halfFlip m +
        interval.halfFlip m * ((interval.rel m).dual 1 (interval.dimLE_rel m)).d := by
  ext σ ⟨τ, hτ⟩
  rw [Matrix.sub_apply, Matrix.add_apply, restrict_dual_d dimLE_oneDim, interval.halfFlip,
    mul_submatrix_apply (P := fun σ ↦ ¬interval.IsEnd m σ)]
  · change _ = ((interval (m + 1)).d * interval.halfFlipFull m) σ τ + _
    rw [interval.capRel_f]
    rcases σ with v | e <;> rcases τ with w | f <;>
      simp [mul_apply, Fintype.sum_sum_type, interval.symMat, interval.halfFlipFull, sgn,
        diagonal_apply]
    all_goals split_ifs <;> simp_all <;> norm_num
  · intro κ hκ
    rcases κ with w | f
    · simp [interval.halfFlipFull] at hκ
    · simp [interval.IsEnd]

/-- **The symmetric relative cap** `C^{1-*}(I, ∂I) → C(I)`: the restriction of the symmetric
duality, `e_k^* ↦ ½(v_k + v_{k+1})`, `v_j^* ↦ ½(e_{j-1} + e_j)`. -/
def interval.symCapRel : Hom ((interval.rel m).dual 1 (interval.dimLE_rel m)) (interval (m + 1)) :=
  (interval.capRel m).subNull (interval.halfFlip m) (interval.halfFlip_hasDeg m)

theorem interval.symCapRel_f :
    (interval.symCapRel m).f = (interval.symMat m).submatrix id Subtype.val := by
  rw [interval.symCapRel, Hom.subNull]
  change (interval.capRel m).f - _ = _
  rw [← interval.capRel_sub_symMat, sub_sub_cancel]

/-- The symmetric pair duality `C^{1-*}(I, ∂I) ≃ C(I)`: hom `symCapRel`, inverse `e₀^* ε`. -/
def interval.symRelDuality :
    HtpyEquiv ((interval.rel m).dual 1 (interval.dimLE_rel m)) (interval (m + 1)) :=
  (interval.relDuality m).ofHtpy (Htpy.subNull _ _ (interval.halfFlip_hasDeg m))

theorem interval.symRelDuality_hom : (interval.symRelDuality m).hom = interval.symCapRel m := rfl

theorem interval.symRelDuality_inv : (interval.symRelDuality m).inv = interval.g m := rfl

/-- The opposite symmetric pair map `C^{1-*}(I) ≃ C(I, ∂I)` (the ladder's right column). -/
def interval.symAbsDuality :
    HtpyEquiv ((interval (m + 1)).dual 1 dimLE_oneDim) (interval.rel m) :=
  (interval.symRelDuality m).transpose (interval.dimLE_rel m) dimLE_oneDim

theorem interval.symAbsDuality_hom_f (σ : (interval.rel m).X) (τ : (interval (m + 1)).X) :
    (interval.symAbsDuality m).hom.f σ τ = interval.symMat m τ σ.1 := by
  rw [interval.symAbsDuality, HtpyEquiv.transpose_hom, transpose_f_apply,
    interval.symRelDuality_hom, interval.symCapRel_f]
  norm_num

end Interval

/-- The symmetric circle duality restricted to an arc of length `m + 1` is the symmetric
interval cap. -/
theorem circle.duality_arc (m M : ℕ) [NeZero M] (a : Fin M) (h : m + 1 < M)
    (x y : (interval (m + 1)).X) :
    (circle.duality M).hom.f ((circle.arc M a (m + 1) h).toFun x)
      ((circle.arc M a (m + 1) h).toFun y) = interval.symMat m x y := by
  have e₁ : ∀ (j : Fin (m + 2)) (i : Fin (m + 1)), a + Fin.castLE (by omega) j =
      a + Fin.castLE (by omega) i ↔ j = i.castSucc := fun j i ↦ by
    rw [add_right_inj, Fin.ext_iff, Fin.ext_iff]; simp
  have e₂ : ∀ (j : Fin (m + 2)) (i : Fin (m + 1)), a + Fin.castLE (by omega) j =
      a + Fin.castLE (by omega) i + 1 ↔ j = i.succ := fun j i ↦ by
    rw [add_assoc, add_right_inj, Fin.ext_iff, Fin.ext_iff, fin_val_add_one,
      ite_eq_left (by simp; omega)]
    simp
  rw [circle.duality_hom]
  simp only [sym, Hom.smul, Hom.add, Matrix.smul_apply, Matrix.add_apply, transpose_f_apply, smul_eq_mul]
  rcases x with j | i <;> rcases y with j' | i'
  · simp [oneDim.cap_f, interval.symMat, circle.arc, oneDimEmb]
  · simp only [circle.arc, oneDimEmb, Sum.map_inl, Sum.map_inr, oneDim.cap_f, id, circle.z,
      Sum.elim_inr, Pi.one_apply, interval.symMat, of_apply, e₁, e₂]
    split_ifs <;> norm_num
  · simp only [circle.arc, oneDimEmb, Sum.map_inl, Sum.map_inr, oneDim.cap_f, id, circle.z,
      Sum.elim_inr, Pi.one_apply, interval.symMat, of_apply, e₁, e₂]
    split_ifs <;> norm_num
  · simp [oneDim.cap_f, interval.symMat, circle.arc, oneDimEmb]

/-! ### Cube pairs -/

section Cube

variable (m n : ℕ)

/-- **Symmetric cube pair duality** `C^{n-*}(Iⁿ, ∂Iⁿ) ≃ C(Iⁿ)`: the tensor product of the
symmetric interval pair dualities. -/
def cube.symRelDuality : HtpyEquiv ((cubeRel m n).dual n (cubeRel.dimLE m n)) (cube (m + 1) n) :=
  HtpyEquiv.dualProd n _ fun _ ↦ interval.symRelDuality m

/-- **Symmetric cube pair duality** `C^{n-*}(Iⁿ) ≃ C(Iⁿ, ∂Iⁿ)` (the B-pair map of the ladder). -/
def cube.symAbsDuality : HtpyEquiv ((cube (m + 1) n).dual n (cube.dimLE n (m + 1))) (cubeRel m n) :=
  HtpyEquiv.dualProd n _ fun _ ↦ interval.symAbsDuality m

end Cube

end BasedComplex

end HSFormal.Cubical
