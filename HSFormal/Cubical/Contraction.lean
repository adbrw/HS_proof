import HSFormal.Cubical.Based

/-!
# Contractions of based complexes and cubical boxes (module C1)

A `Contraction` of `C` is an exact augmented contraction `d s + s d = 1 - i ε` to a base
vertex.  Contractions tensor by `s ⊗ 1 + (i ε) ⊗ s'` (manuscript l.566).  A `SubContraction`
is the same identity on the chains of a subcomplex, written on the ambient complex; it is the
transport of a contraction along a cellular embedding, and fills augmentation-zero cycles of
the subcomplex (`SubContraction.fill`).

The one-dimensional complexes `oneDim` (graphs) give the interval `interval ℓ` with its cone
contraction and the circle `circle m`; sub-paths and arcs are cellular embeddings.  Boxes are
iterated tensor products of intervals (`prodComplex`), contracted by `Contraction.prod`, and
embed into cubes and tori by `CellEmbedding.prod`.
-/

namespace HSFormal.Cubical

open Matrix
open scoped Kronecker

namespace BasedComplex

variable {C D Y : BasedComplex}

theorem augAt_hasDeg {b : C.X} (hb : C.deg b = 0) : HasDeg C C 0 (C.augAt b) := fun σ τ h ↦ by
  simp only [augAt, aug, of_apply] at h
  split_ifs at h with h₁ h₂ <;> simp_all

theorem augAt_mulVec (b : C.X) (γ : C.X → ℚ) :
    C.augAt b *ᵥ γ = fun σ ↦ if σ = b then ∑ τ, C.aug τ * γ τ else 0 := by
  ext σ; simp only [mulVec, dotProduct, augAt, of_apply]; split_ifs <;> simp

theorem sum_aug_mul_eq_zero {γ : C.X → ℚ} (h : ∀ σ, γ σ ≠ 0 → C.deg σ ≠ 0) :
    ∑ σ, C.aug σ * γ σ = 0 :=
  Finset.sum_eq_zero fun σ _ ↦ by
    by_cases hσ : γ σ = 0
    · simp [hσ]
    · simp [aug, h σ hσ]

/-! ### Contractions -/

/-- An exact augmented contraction `d s + s d = 1 - i ε` with base vertex `base`. -/
structure Contraction (C : BasedComplex) where
  s : Matrix C.X C.X ℚ
  deg1 : HasDeg C C 1 s
  base : C.X
  base_deg : C.deg base = 0
  eq : C.d * s + s * C.d = 1 - C.augAt base

namespace Contraction

variable (S : Contraction C)

theorem augAt_mul_d : C.augAt S.base * C.d = 0 := by
  have h : C.augAt S.base = 1 - (C.d * S.s + S.s * C.d) := by rw [S.eq]; abel
  calc C.augAt S.base * C.d = C.d - C.d * S.s * C.d := by
        rw [h, Matrix.sub_mul, Matrix.one_mul, Matrix.add_mul, Matrix.mul_assoc S.s, C.d_d,
          Matrix.mul_zero, add_zero]
    _ = C.d * C.augAt S.base := by
        rw [h, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_add, ← Matrix.mul_assoc C.d C.d, C.d_d,
          Matrix.zero_mul, zero_add, Matrix.mul_assoc]
    _ = 0 := d_mul_augAt S.base_deg

/-- A contractible complex is augmented: `ε ∘ d = 0`. -/
theorem sum_aug_mul_d (S : Contraction C) (τ : C.X) : ∑ σ, C.aug σ * C.d σ τ = 0 := by
  have := congr_fun (congr_fun S.augAt_mul_d S.base) τ
  simpa [augAt, mul_apply] using this

/-- The point is contractible. -/
def point : Contraction BasedComplex.point where
  s := 0
  deg1 := HasDeg.zero
  base := ()
  base_deg := rfl
  eq := by ext ⟨⟩ ⟨⟩; simp [augAt, aug, BasedComplex.point]

/-- The tensor contraction `s ⊗ 1 + (i ε) ⊗ s'`. -/
def tensor (S : Contraction C) (T : Contraction D) : Contraction (C.tensor D) where
  s := S.s ⊗ₖ 1 + C.augAt S.base ⊗ₖ T.s
  deg1 := by
    simpa using (S.deg1.kronecker HasDeg.one).add
      (by simpa using (augAt_hasDeg S.base_deg).kronecker T.deg1)
  base := (S.base, T.base)
  base_deg := by simp [S.base_deg, T.base_deg]
  eq := by
    have hs : C.sgn * S.s + S.s * C.sgn = 0 := by rw [S.deg1.sgn_anticomm]; abel
    rw [tensor_augAt, tensor_d]
    calc _ = (C.d * S.s + S.s * C.d) ⊗ₖ 1 + (C.sgn * S.s + S.s * C.sgn) ⊗ₖ D.d +
          (C.d * C.augAt S.base + C.augAt S.base * C.d) ⊗ₖ T.s +
          C.augAt S.base ⊗ₖ (D.d * T.s + T.s * D.d) := by
          simp only [Matrix.add_mul, Matrix.mul_add, ← mul_kronecker_mul, add_kronecker,
            kronecker_add, Matrix.mul_one, Matrix.one_mul, sgn_augAt S.base_deg, augAt_sgn]
          abel
      _ = 1 - C.augAt S.base ⊗ₖ D.augAt T.base := by
          rw [S.eq, T.eq, hs, S.augAt_mul_d, d_mul_augAt S.base_deg, add_zero, zero_kronecker,
            zero_kronecker, add_zero, add_zero, sub_kronecker, kronecker_sub, one_kronecker_one]
          abel

end Contraction

/-! ### Contractions of subcomplexes -/

/-- An augmented contraction of the subcomplex spanned by `P`, written on `C`: `s` lives on
`P × P` and `d s + s d = 1 - i ε` on every column in `P`. -/
structure SubContraction (C : BasedComplex) (P : C.X → Prop) where
  s : Matrix C.X C.X ℚ
  deg1 : HasDeg C C 1 s
  supp : ∀ σ τ, s σ τ ≠ 0 → P σ ∧ P τ
  base : C.X
  base_mem : P base
  base_deg : C.deg base = 0
  eq : ∀ σ τ, P τ → (C.d * s + s * C.d) σ τ = (1 - C.augAt base) σ τ

namespace SubContraction

variable {P : C.X → Prop} (S : SubContraction C P)

/-- **Filling in a contractible carrier.** An augmentation-zero cycle supported in `P` is the
boundary of `s γ`, which is again supported in `P`. -/
theorem fill {γ : C.X → ℚ} (hsupp : ∀ σ, γ σ ≠ 0 → P σ) (hcyc : C.d *ᵥ γ = 0)
    (haug : ∑ σ, C.aug σ * γ σ = 0) : C.d *ᵥ (S.s *ᵥ γ) = γ := by
  have key : (C.d * S.s) *ᵥ γ = (1 - C.augAt S.base - S.s * C.d) *ᵥ γ := by
    ext σ
    simp only [mulVec, dotProduct]
    refine Finset.sum_congr rfl fun τ _ ↦ ?_
    by_cases hγ : γ τ = 0
    · simp [hγ]
    have := S.eq σ τ (hsupp τ hγ)
    rw [Matrix.add_apply] at this
    rw [Matrix.sub_apply, ← this]; ring
  rw [mulVec_mulVec, key, sub_mulVec, sub_mulVec, one_mulVec, ← mulVec_mulVec, hcyc,
    mulVec_zero, sub_zero, augAt_mulVec]
  ext σ; simp [haug]

theorem mulVec_supp {γ : C.X → ℚ} {σ : C.X} (h : (S.s *ᵥ γ) σ ≠ 0) : P σ := by
  obtain ⟨κ, hκ, -⟩ := exists_mulVec_ne_zero h
  exact (S.supp σ κ hκ).1

/-- `s` vanishes on columns at or above the top degree of the carrier. -/
theorem s_eq_zero {k : ℕ} (hdim : ∀ ρ, P ρ → C.deg ρ ≤ k) {σ τ : C.X} (hτ : k ≤ C.deg τ) :
    S.s σ τ = 0 := by
  by_contra h
  have := S.deg1 σ τ h
  have := hdim σ (S.supp σ τ h).1
  omega

end SubContraction

/-- Transport of a contraction along a cellular embedding: `e s eᵀ` contracts the image. -/
def Contraction.toSub (S : Contraction Y) (e : CellEmbedding Y C) : SubContraction C e.range where
  s := e.mat * S.s * e.matᵀ
  deg1 := by simpa using (e.mat_hasDeg.mul S.deg1).mul e.transpose_mat_hasDeg
  supp σ τ h := by
    obtain ⟨κ, h₁, h₂⟩ := exists_mul_apply_ne_zero h
    obtain ⟨κ', h₃, -⟩ := exists_mul_apply_ne_zero h₁
    simp only [CellEmbedding.mat, transpose_apply, of_apply, ne_eq, ite_eq_right_iff,
      one_ne_zero, imp_false, not_not] at h₂ h₃
    exact ⟨⟨κ', h₃.symm⟩, ⟨κ, h₂.symm⟩⟩
  base := e.toFun S.base
  base_mem := ⟨S.base, rfl⟩
  base_deg := by rw [e.deg_eq, S.base_deg]
  eq σ τ := by
    rintro ⟨τ, rfl⟩
    have h : (C.d * (e.mat * S.s * e.matᵀ) + e.mat * S.s * e.matᵀ * C.d) * e.mat =
        (1 - C.augAt (e.toFun S.base)) * e.mat := by
      have h₁ := e.transpose_mat_mul_mat
      have h₂ := e.transpose_mat_mul_d_mul_mat
      calc _ = C.d * e.mat * S.s * (e.matᵀ * e.mat) + e.mat * S.s * (e.matᵀ * C.d * e.mat) := by
            simp only [Matrix.add_mul, Matrix.mul_assoc]
        _ = e.mat * (Y.d * S.s + S.s * Y.d) := by
            rw [h₁, h₂, e.d_mul_mat]; simp only [Matrix.mul_one, Matrix.mul_add, Matrix.mul_assoc]
        _ = _ := by rw [S.eq, Matrix.mul_sub, Matrix.sub_mul, e.mat_mul_augAt]; simp
    simpa only [e.mul_mat_apply] using congr_fun (congr_fun h σ) τ

/-! ### One-dimensional complexes: intervals, circles, arcs -/

section OneDim

variable (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (src tgt : E → V)

/-- The cellular chains of a finite graph: vertices `inl v`, edges `inr e` with
`∂ e = tgt e - src e`. -/
abbrev oneDim : BasedComplex where
  X := V ⊕ E
  deg := Sum.elim (fun _ ↦ 0) fun _ ↦ 1
  d := Matrix.of fun σ τ ↦ match σ, τ with
    | .inl v, .inr e => (if v = tgt e then 1 else 0) - if v = src e then 1 else 0
    | _, _ => 0
  d_deg := by rintro (v | e) (w | f) h <;> simp_all
  d_d := by ext (v | e) (w | f) <;> simp [mul_apply, Fintype.sum_sum_type]

variable {V E src tgt}

@[simp] theorem oneDim_d_inl_inr (v : V) (e : E) :
    (oneDim V E src tgt).d (.inl v) (.inr e) =
      (if v = tgt e then 1 else 0) - if v = src e then 1 else 0 := rfl
@[simp] theorem oneDim_d_inr (e : E) (τ : V ⊕ E) : (oneDim V E src tgt).d (.inr e) τ = 0 := by
  cases τ <;> rfl
@[simp] theorem oneDim_d_inl_inl (v w : V) : (oneDim V E src tgt).d (.inl v) (.inl w) = 0 := rfl

variable {V' E' : Type} [Fintype V'] [DecidableEq V'] [Fintype E'] [DecidableEq E']
  {src' tgt' : E' → V'}

/-- A graph embedding respecting endpoints is a cellular embedding. -/
def oneDimEmb (fV : V → V') (fE : E → E') (hV : Function.Injective fV)
    (hE : Function.Injective fE) (hs : ∀ e, src' (fE e) = fV (src e))
    (ht : ∀ e, tgt' (fE e) = fV (tgt e)) :
    CellEmbedding (oneDim V E src tgt) (oneDim V' E' src' tgt') where
  toFun := Sum.map fV fE
  inj := hV.sumMap hE
  deg_eq := by rintro (v | e) <;> rfl
  d_eq := by rintro (v | e) (w | f) <;> simp [hs, ht, hV.eq_iff]
  closed := by
    rintro (v | e) (w | f) h
    · simp at h
    · by_cases h₁ : v = fV (tgt f)
      · exact ⟨.inl (tgt f), by simp [h₁]⟩
      · by_cases h₂ : v = fV (src f)
        · exact ⟨.inl (src f), by simp [h₂]⟩
        · simp [h₁, h₂, hs, ht] at h
    · simp at h
    · simp at h

end OneDim

/-- The interval `I_ℓ`: vertices `0, …, ℓ` and edges `[j, j+1]`. -/
abbrev interval (ℓ : ℕ) : BasedComplex := oneDim (Fin (ℓ + 1)) (Fin ℓ) Fin.castSucc Fin.succ

/-- The circle `C_m`: vertices and edges `Fin m`, edge `i` from `i` to `i + 1`. -/
abbrev circle (m : ℕ) [NeZero m] : BasedComplex := oneDim (Fin m) (Fin m) id (· + 1)

private theorem telescope (f : ℕ → ℚ) {j ℓ : ℕ} (h : j ≤ ℓ) :
    ∑ i ∈ Finset.range ℓ, (if i < j then f (i + 1) - f i else 0) = f j - f 0 := by
  induction ℓ with
  | zero => obtain rfl : j = 0 := by omega
            simp
  | succ ℓ ih =>
    rw [Finset.sum_range_succ]
    rcases Nat.lt_or_ge j (ℓ + 1) with hj | hj
    · rw [ih (by omega), ite_eq_right (by omega), add_zero]
    · obtain rfl : j = ℓ + 1 := by omega
      rw [Finset.sum_congr rfl fun i hi ↦ ite_eq_left (by simp at hi; omega), Finset.sum_range_sub,
        ite_eq_left (by omega)]
      ring

private theorem interval_sum_vertex {ℓ : ℕ} (k j : Fin (ℓ + 1)) :
    ∑ x : Fin ℓ, ((if k = x.succ then (1 : ℚ) else 0) - if k = x.castSucc then 1 else 0) *
      (if (x : ℕ) < j then 1 else 0) = (if k = j then 1 else 0) - if k = 0 then 1 else 0 := by
  have h := telescope (fun n : ℕ ↦ if (k : ℕ) = n then (1 : ℚ) else 0) (Nat.lt_succ_iff.mp j.2)
  rw [← Fin.sum_univ_eq_sum_range] at h
  convert h using 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    have e1 : k = i.succ ↔ (k : ℕ) = i + 1 := by rw [Fin.ext_iff, Fin.val_succ]
    have e2 : k = i.castSucc ↔ (k : ℕ) = i := by rw [Fin.ext_iff, Fin.val_castSucc]
    by_cases hi : (i : ℕ) < j
    · simp only [hi, ite_true, mul_one, e1, e2]
    · simp only [hi, ite_false, mul_zero]
  · simp only [Fin.ext_iff, Fin.val_zero]

private theorem interval_sum_edge {ℓ : ℕ} (k j : Fin ℓ) :
    ∑ x : Fin (ℓ + 1), (if (k : ℕ) < x then (1 : ℚ) else 0) *
      ((if x = j.succ then 1 else 0) - if x = j.castSucc then 1 else 0) =
      if k = j then 1 else 0 := by
  simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  simp only [Fin.val_succ, Fin.val_castSucc, Fin.ext_iff]

  split_ifs <;> first | (exfalso; omega) | norm_num

/-- The cone contraction matrix of `I_ℓ`: `s(v_j) = e_0 + ⋯ + e_{j-1}`. -/
def interval.coneMat (ℓ : ℕ) : Matrix (interval ℓ).X (interval ℓ).X ℚ :=
  Matrix.of fun σ τ ↦ match σ, τ with
    | .inr i, .inl j => if (i : ℕ) < j then 1 else 0
    | _, _ => 0

@[simp] theorem interval.coneMat_inr_inl (ℓ : ℕ) (i : Fin ℓ) (j : Fin (ℓ + 1)) :
    interval.coneMat ℓ (.inr i) (.inl j) = if (i : ℕ) < j then 1 else 0 := rfl
@[simp] theorem interval.coneMat_inl (ℓ : ℕ) (k : Fin (ℓ + 1)) (τ : (interval ℓ).X) :
    interval.coneMat ℓ (.inl k) τ = 0 := by cases τ <;> rfl
@[simp] theorem interval.coneMat_inr_inr (ℓ : ℕ) (i j : Fin ℓ) :
    interval.coneMat ℓ (.inr i) (.inr j) = 0 := rfl

/-- The cone contraction of `I_ℓ` to the vertex `0`. -/
def interval.contraction (ℓ : ℕ) : Contraction (interval ℓ) where
  s := interval.coneMat ℓ
  deg1 := by rintro (k | k) (j | j) h <;> simp_all
  base := .inl 0
  base_deg := rfl
  eq := by
    ext (k | k) (j | j) <;>
      simp only [Matrix.add_apply, mul_apply, Fintype.sum_sum_type, Matrix.sub_apply, one_apply, augAt, aug,
        of_apply, interval.coneMat_inl,
        interval.coneMat_inr_inl, interval.coneMat_inr_inr, mul_zero, zero_mul,
        Finset.sum_const_zero, add_zero, zero_add, Sum.inl.injEq, Sum.inr.injEq,
        reduceCtorEq, ite_false, Sum.elim_inl, Sum.elim_inr, one_ne_zero, ite_true, sub_zero]
    all_goals first | exact interval_sum_vertex _ _ | exact interval_sum_edge _ _ | simp

/-- The sub-path `[a, a + ℓ]` of `I_m`. -/
def interval.subpath (m a ℓ : ℕ) (h : a + ℓ ≤ m) : CellEmbedding (interval ℓ) (interval m) :=
  oneDimEmb (fun j ↦ ⟨a + j, by have := j.2; omega⟩) (fun i ↦ ⟨a + i, by have := i.2; omega⟩)
    (fun x y hxy ↦ by simpa [Fin.ext_iff] using hxy)
    (fun x y hxy ↦ by simpa [Fin.ext_iff] using hxy)
    (fun e ↦ by ext; simp) (fun e ↦ by ext; simp; omega)

/-- The arc `[a, a + ℓ]` of `C_m`, for `ℓ < m`. -/
def circle.arc (m : ℕ) [NeZero m] (a : Fin m) (ℓ : ℕ) (h : ℓ < m) :
    CellEmbedding (interval ℓ) (circle m) :=
  oneDimEmb (fun j ↦ a + Fin.castLE (by omega) j) (fun i ↦ a + Fin.castLE (by omega) i)
    (fun x y hxy ↦ Fin.castLE_injective _ (add_left_cancel hxy))
    (fun x y hxy ↦ Fin.castLE_injective _ (add_left_cancel hxy))
    (fun e ↦ by simp only [id]; congr 1)
    (fun e ↦ by
      rw [add_assoc]; congr 1
      ext; simp only [Fin.val_add, Fin.val_castLE, Fin.val_succ, Fin.val_one', Nat.add_mod_mod]
      exact Nat.mod_eq_of_lt (by have := e.2; omega))

/-! ### Boxes, cubes and tori -/

/-- The iterated tensor product `C 0 ⊗ (C 1 ⊗ ⋯ ⊗ point)`. -/
@[reducible]
def prodComplex : (n : ℕ) → (Fin n → BasedComplex) → BasedComplex
  | 0, _ => point
  | n + 1, C => (C 0).tensor (prodComplex n fun i ↦ C i.succ)

/-- Iterated tensor contraction. -/
def Contraction.prod : (n : ℕ) → {C : Fin n → BasedComplex} → (∀ i, Contraction (C i)) →
    Contraction (prodComplex n C)
  | 0, _, _ => Contraction.point
  | n + 1, _, S => (S 0).tensor (Contraction.prod n fun i ↦ S i.succ)

/-- The identity embedding. -/
def CellEmbedding.id (C : BasedComplex) : CellEmbedding C C :=
  ⟨_root_.id, Function.injective_id, fun _ ↦ rfl, fun _ _ ↦ rfl, fun ρ _ _ ↦ ⟨ρ, rfl⟩⟩

/-- Products of embeddings. -/
def CellEmbedding.prod : (n : ℕ) → {Y C : Fin n → BasedComplex} →
    (∀ i, CellEmbedding (Y i) (C i)) → CellEmbedding (prodComplex n Y) (prodComplex n C)
  | 0, _, _, _ => CellEmbedding.id _
  | n + 1, _, _, e => (e 0).tensor (CellEmbedding.prod n fun i ↦ e i.succ)

/-- The cubical grid `I_m^{⊗n}` on `[0, m]^n`. -/
abbrev cube (m n : ℕ) : BasedComplex := prodComplex n fun _ ↦ interval m

/-- The cubical torus `C_m^{⊗n}`. -/
abbrev torus (m n : ℕ) [NeZero m] : BasedComplex := prodComplex n fun _ ↦ circle m

/-- The box `I_{ℓ 0} ⊗ ⋯ ⊗ I_{ℓ (n-1)}`. -/
abbrev box {n : ℕ} (ℓ : Fin n → ℕ) : BasedComplex := prodComplex n fun i ↦ interval (ℓ i)

/-- The product cone contraction of a box. -/
def box.contraction {n : ℕ} (ℓ : Fin n → ℕ) : Contraction (box ℓ) :=
  Contraction.prod n fun i ↦ interval.contraction (ℓ i)

/-- The box `∏ [a i, a i + ℓ i]` in the cube. -/
def cube.boxEmb (m : ℕ) {n : ℕ} (a ℓ : Fin n → ℕ) (h : ∀ i, a i + ℓ i ≤ m) :
    CellEmbedding (box ℓ) (cube m n) :=
  CellEmbedding.prod n fun i ↦ interval.subpath m (a i) (ℓ i) (h i)

/-- The box `∏ [a i, a i + ℓ i]` (arcs) in the torus. -/
def torus.boxEmb (m : ℕ) [NeZero m] {n : ℕ} (a : Fin n → Fin m) (ℓ : Fin n → ℕ)
    (h : ∀ i, ℓ i < m) : CellEmbedding (box ℓ) (torus m n) :=
  CellEmbedding.prod n fun i ↦ circle.arc m (a i) (ℓ i) (h i)

/-- Exact contraction of a box of the cube. -/
def cube.boxContraction (m : ℕ) {n : ℕ} (a ℓ : Fin n → ℕ) (h : ∀ i, a i + ℓ i ≤ m) :
    SubContraction (cube m n) (cube.boxEmb m a ℓ h).range :=
  (box.contraction ℓ).toSub _

/-- Exact contraction of a box of the torus. -/
def torus.boxContraction (m : ℕ) [NeZero m] {n : ℕ} (a : Fin n → Fin m) (ℓ : Fin n → ℕ)
    (h : ∀ i, ℓ i < m) : SubContraction (torus m n) (torus.boxEmb m a ℓ h).range :=
  (box.contraction ℓ).toSub _

/-! ### Augmented complexes -/

/-- `ε ∘ d = 0`. -/
def IsAugmented (C : BasedComplex) : Prop := ∀ σ, ∑ τ, C.aug τ * C.d τ σ = 0

theorem Contraction.isAugmented (S : Contraction C) : C.IsAugmented := S.sum_aug_mul_d

theorem isAugmented_point : point.IsAugmented := fun _ ↦ by simp [point]

theorem isAugmented_oneDim (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (src tgt : E → V) : (oneDim V E src tgt).IsAugmented := by
  rintro (v | e) <;> simp [Fintype.sum_sum_type, aug]

theorem IsAugmented.tensor (hC : C.IsAugmented) (hD : D.IsAugmented) :
    (C.tensor D).IsAugmented := by
  rintro ⟨σ, σ'⟩
  simp only [tensor_aug, Matrix.add_apply, kronecker_apply, Fintype.sum_prod_type, mul_add,
    Finset.sum_add_distrib]
  have e₁ : ∀ τ : C.X, ∑ τ' : D.X, C.aug τ * D.aug τ' * (C.d τ σ * (1 : Matrix D.X D.X ℚ) τ' σ') =
      D.aug σ' * (C.aug τ * C.d τ σ) := fun τ ↦ by
    rw [Finset.sum_eq_single σ' (fun τ' _ h ↦ by simp [one_apply_ne h]) (by simp)]
    simp; ring
  have e₂ : ∀ τ : C.X, ∑ τ' : D.X, C.aug τ * D.aug τ' * (C.sgn τ σ * D.d τ' σ') =
      C.aug τ * C.sgn τ σ * ∑ τ', D.aug τ' * D.d τ' σ' := fun τ ↦ by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
  simp only [e₁, e₂, hD σ', ← Finset.mul_sum, hC σ, mul_zero, Finset.sum_const_zero, add_zero]

theorem IsAugmented.prod : (n : ℕ) → {C : Fin n → BasedComplex} → (∀ i, (C i).IsAugmented) →
    (prodComplex n C).IsAugmented
  | 0, _, _ => isAugmented_point
  | n + 1, _, h => (h 0).tensor (IsAugmented.prod n fun i ↦ h i.succ)

/-! ### Contractible complexes are equivalent to a point -/

/-- The augmentation `C → point`. -/
def augHom (hC : C.IsAugmented) : Hom C point where
  f := Matrix.of fun _ σ ↦ C.aug σ
  deg0 _ σ h := by
    simp only [of_apply, aug, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at h
    simp [h, point]
  comm := by
    ext _ σ
    simp only [point, Matrix.zero_apply, mul_apply, of_apply, zero_mul, Finset.sum_const_zero]
    exact (hC σ).symm

/-- The inclusion of a vertex `point → C`. -/
def vertexHom {b : C.X} (hb : C.deg b = 0) : Hom point C where
  f := Matrix.of fun σ _ ↦ if σ = b then 1 else 0
  deg0 σ _ h := by
    simp only [of_apply, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at h
    simp [h, hb, point]
  comm := by
    ext σ _
    simp only [point, Matrix.zero_apply, mul_apply, of_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const_zero]
    by_contra h
    have := C.d_deg σ b h
    omega

/-- A contraction is a homotopy equivalence with the point. -/
def Contraction.htpyEquivPoint (S : Contraction C) : HtpyEquiv C BasedComplex.point where
  hom := augHom S.isAugmented
  inv := vertexHom S.base_deg
  homInv :=
    { h := -S.s
      deg1 := S.deg1.neg
      eq := by
        have e : (vertexHom S.base_deg).f * (augHom S.isAugmented).f = C.augAt S.base := by
          ext σ τ; simp [vertexHom, augHom, augAt, mul_apply, BasedComplex.point]
        rw [Hom.comp_f, e, Hom.id_f, Matrix.mul_neg, Matrix.neg_mul, ← neg_add, S.eq]; abel }
  invHom := Htpy.ofEq <| Hom.ext <| by
    ext ⟨⟩ ⟨⟩
    simp [vertexHom, augHom, mul_apply, aug, S.base_deg, Hom.id, BasedComplex.point]

end BasedComplex

end HSFormal.Cubical
