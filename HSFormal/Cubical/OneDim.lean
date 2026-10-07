import HSFormal.Cubical.DualLadder
import HSFormal.EquivariantSignature

/-!
# One-dimensional dualities: graphs, circles, interval pairs (cubical module C3)

On a graph (`oneDim`) the Alexander–Whitney diagonal `Δv = v ⊗ v`, `Δe = src e ⊗ e + e ⊗ tgt e`
is a counital cellular chain map.  For a `1`-cycle `z` the cap `φ₀ = z ∩` sends
`e^* ↦ z_e src e` and `v^* ↦ Σ_{tgt e = v} z_e e`, and the flip homotopy `φ₀ ≃ Tφ₀` is the
cellwise `U = -diag(z)` on edges (`oneDim.flip`).

* The circle `C_m` with `z = Σ e`: `φ₀` is a monomial chain isomorphism
  (`e_k^* ↦ v_k`, `v_k^* ↦ e_{k-1}`) with inverse `b` (`v_k ↦ e_k^*`, `e_k ↦ v_{k+1}^*`), and
  `circle.duality` is the symmetric duality `(φ₀ + Tφ₀)/2` with inverse `b` and homotopies
  `-½ U b`, `-½ b U`.
* The interval pair `(I_{m+1}, ∂)`: the relative cap `F : C^{1-*}(I, ∂I) → C(I)`
  (`e_k^* ↦ v_k`, `v_j^* ↦ e_{j-1}`) is a homotopy equivalence with inverse `g = e_0^* ε`,
  homotopies `-s` (the cone contraction) and `k(e_i^*) = -(v_1^* + ⋯ + v_i^*)`
  (`interval.relDuality`); its transpose `C^{1-*}(I) → C(I, ∂I)` is the opposite pair map
  (`interval.absDuality`).
* The cellular `CP²` (`CPcell`: `e₀, e₂, e₄`, `d = 0`) with the diagonal whose `e₂ ⊗ e₂`
  coefficient in `Δe₄` is `+1` (complex orientation, l. 1093) and `z = e₄`: the cap is the
  antidiagonal `e_{2i}^* ↦ e_{4-2i}`, a strictly symmetric isomorphism (`CPcell.duality`), whose
  middle form is `⟨1⟩` (`CPcell.middleForm_eq`), so `σ = 1` (`CPcell.ratSignature_middleForm`).
-/

namespace HSFormal.Cubical

open Matrix
open scoped Kronecker

namespace BasedComplex

/-! ### Graphs -/

section Graph

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] {src tgt : E → V}

theorem dimLE_oneDim : (oneDim V E src tgt).DimLE 1 := by
  rintro (v | e) <;> simp

/-- The Alexander–Whitney diagonal of a graph. -/
def oneDim.aw : Diagonal (oneDim V E src tgt) where
  f := Matrix.of fun p ρ ↦ match ρ with
    | .inl v => if p.1 = .inl v then (if p.2 = .inl v then 1 else 0) else 0
    | .inr e => (if p.1 = .inl (src e) then (if p.2 = .inr e then 1 else 0) else 0) +
        if p.1 = .inr e then (if p.2 = .inl (tgt e) then 1 else 0) else 0
  deg0 := by
    rintro ⟨x, y⟩ (v | e) h
    · simp only [of_apply] at h
      split_ifs at h with h₁ h₂ <;> simp_all
    · simp only [of_apply] at h
      split_ifs at h with h₁ h₂ h₃ h₄ h₃ h₄ <;> simp_all
  comm := by
    ext ⟨x, y⟩ (v | e) <;> rcases x with a | a <;> rcases y with b | b <;>
      simp [mul_apply, Fintype.sum_prod_type, Fintype.sum_sum_type, mul_add, mul_ite,
        Finset.sum_add_distrib, sgn, one_apply, diagonal_apply]
    all_goals split_ifs <;> simp_all

local notation "𝒢" => oneDim V E src tgt

theorem oneDim.isLeftCounital_aw : IsLeftCounital (oneDim.aw : Diagonal 𝒢) := by
  rintro (w | e) (v | e') <;> simp [oneDim.aw, aug, eq_comm]

theorem oneDim.isRightCounital_aw : IsRightCounital (oneDim.aw : Diagonal 𝒢) := by
  rintro (w | e) (v | e') <;> simp [oneDim.aw, aug, eq_comm]

/-- Without loops the diagonal is cellular. -/
theorem oneDim.isCellular_aw (hloop : ∀ e, src e ≠ tgt e) :
    IsCellular (oneDim.aw : Diagonal 𝒢) := by
  intro Q hQ σ τ ρ h hρ
  rcases ρ with v | e
  · simp only [oneDim.aw, of_apply] at h
    split_ifs at h with h₁ h₂
    · exact ⟨h₁ ▸ hρ, h₂ ▸ hρ⟩
    all_goals simp at h
  · have hs : Q (.inl (src e)) := hQ _ _ (by simp [hloop e]) hρ
    have ht : Q (.inl (tgt e)) := hQ _ _ (by simp [(hloop e).symm]) hρ
    simp only [oneDim.aw, of_apply] at h
    split_ifs at h with h₁ h₂ h₃ h₄ h₃ h₄ <;> simp_all

variable {z : (oneDim V E src tgt).X → ℚ}

theorem oneDim.aw_mulVec (h₀ : ∀ v, z (.inl v) = 0) (σ τ : (oneDim V E src tgt).X) :
    ((oneDim.aw : Diagonal 𝒢).f *ᵥ z) (σ, τ) = match σ, τ with
      | .inl v, .inr e => if v = src e then z (.inr e) else 0
      | .inr e, .inl v => if v = tgt e then z (.inr e) else 0
      | _, _ => 0 := by
  rcases σ with a | a <;> rcases τ with b | b <;>
    simp [mulVec, dotProduct, oneDim.aw, Fintype.sum_sum_type, h₀]
  rw [Finset.sum_eq_single b (fun x _ hx ↦ by simp [Ne.symm hx]) (by simp)]
  simp

theorem IsCycle.oneDim_inl {z : (oneDim V E src tgt).X → ℚ} (hz : IsCycle 𝒢 1 z) (v : V) :
    z (.inl v) = 0 :=
  by_contra fun h ↦ by simpa using hz.deg _ h

theorem oneDim.cap_f (hz : IsCycle 𝒢 1 z) (σ τ : (oneDim V E src tgt).X) :
    (cap dimLE_oneDim oneDim.aw hz).f σ τ = match σ, τ with
      | .inl v, .inr e => if v = src e then z (.inr e) else 0
      | .inr e, .inl v => if v = tgt e then z (.inr e) else 0
      | _, _ => 0 :=
  oneDim.aw_mulVec hz.oneDim_inl σ τ

/-- The flip homotopy `U : φ₀ ≃ Tφ₀` of the graph cap, `U(e^*) = -z_e e`. -/
def oneDim.flip (hz : IsCycle 𝒢 1 z) :
    Htpy (cap dimLE_oneDim oneDim.aw hz)
      (transpose dimLE_oneDim dimLE_oneDim (cap dimLE_oneDim oneDim.aw hz)) where
  h := Matrix.of fun σ τ ↦ match σ, τ with
    | .inr e, .inr e' => if e = e' then -z (.inr e) else 0
    | _, _ => 0
  deg1 := by
    rintro (a | a) (b | b) h <;> simp at h
    · obtain rfl := h.1; rfl
  eq := by
    ext σ τ
    rw [Matrix.sub_apply, transpose_f_apply, oneDim.cap_f, oneDim.cap_f]
    rcases σ with a | a <;> rcases τ with b | b <;>
      simp [mul_apply, Fintype.sum_sum_type, sgn, diagonal_apply]
    all_goals split_ifs <;> simp_all

end Graph

/-! ### The circle -/

section Circle

variable (m : ℕ) [NeZero m]

theorem sum_ite_eq_add_one (a : Fin m) (f : Fin m → ℚ) :
    ∑ x, (if a = x + 1 then f x else 0) = f (a - 1) := by
  rw [Finset.sum_eq_single (a - 1)
    (fun x _ hx ↦ ite_eq_right fun h ↦ hx (by rw [h, add_sub_cancel_right])) (by simp)]
  simp

/-- The fundamental cycle `Σ e` of `C_m`. -/
def circle.z : (circle m).X → ℚ := Sum.elim 0 1

theorem circle.isCycle_z : IsCycle (circle m) 1 (circle.z m) where
  deg := by rintro (v | e) h <;> simp_all [circle.z]
  cycle := by
    ext (v | e)
    · have h : ∑ e : Fin m, (if v = e + 1 then (1 : ℚ) else 0) = 1 := by
        rw [Fintype.sum_equiv (Equiv.addRight 1) (fun e ↦ if v = e + 1 then (1 : ℚ) else 0)
          (fun e ↦ if v = e then 1 else 0) fun _ ↦ rfl]
        simp
      simp [mulVec, dotProduct, circle.z, h]
    · simp [mulVec, dotProduct]

/-- The circle cap `φ₀ = z ∩`: `e_k^* ↦ v_k`, `v_k^* ↦ e_{k-1}`. -/
abbrev circle.cap : Hom ((circle m).dual 1 dimLE_oneDim) (circle m) :=
  BasedComplex.cap dimLE_oneDim oneDim.aw (circle.isCycle_z m)

/-- The inverse `b = φ₀⁻¹`: `v_k ↦ e_k^*`, `e_k ↦ v_{k+1}^*`. -/
def circle.bMat : Matrix (circle m).X (circle m).X ℚ := Matrix.of fun σ τ ↦ match σ, τ with
  | .inr e, .inl v => if e = v then 1 else 0
  | .inl v, .inr e => if v = e + 1 then 1 else 0
  | _, _ => 0

/-- `φ₀` is a chain isomorphism with inverse `b`. -/
def circle.capEquiv : HtpyEquiv ((circle m).dual 1 dimLE_oneDim) (circle m) :=
  HtpyEquiv.ofIso (circle.cap m) (circle.bMat m)
    (by rintro (a | a) (b | b) h <;> simp [circle.bMat] at h <;> rfl)
    (by
      ext (a | a) (b | b) <;>
        simp [mul_apply, Fintype.sum_sum_type, oneDim.cap_f, circle.bMat, circle.z, one_apply,
          sum_ite_eq_add_one])
    (by
      ext (a | a) (b | b) <;>
        simp [mul_apply, Fintype.sum_sum_type, oneDim.cap_f, circle.bMat, circle.z, one_apply]
      exact if_congr eq_comm rfl rfl)

/-- The symmetric duality of `C_m`: `φ = (φ₀ + Tφ₀)/2` with inverse `b = φ₀⁻¹`. -/
def circle.duality : SymDuality (circle m) 1 dimLE_oneDim :=
  SymDuality.ofFlip (circle.capEquiv m) (oneDim.flip (circle.isCycle_z m))

theorem circle.duality_hom : (circle.duality m).hom = sym dimLE_oneDim (circle.cap m) := rfl

theorem circle.duality_inv_f : (circle.duality m).inv.f = circle.bMat m := rfl

/-- For `m ≥ 2` the circle duality is cell-local (local for every cover by subcomplexes). -/
theorem circle.isCellLocal_duality (hm : 2 ≤ m) : IsCellLocal (circle.duality m).hom.f := by
  refine (isCellLocal_cap (oneDim.isCellular_aw fun e h ↦ ?_) (circle.isCycle_z m)).sym_f
  have h₁ : (0 : Fin m) = 1 := by simpa using congrArg (· - e) h
  have := congrArg Fin.val h₁
  rw [Fin.val_zero, Fin.val_one', Nat.mod_eq_of_lt (by omega)] at this
  omega

/-- `ε ∘ φ = ⟨-, z⟩`. -/
theorem circle.aug_duality (τ : (circle m).X) :
    ∑ σ, (circle m).aug σ * (circle.duality m).hom.f σ τ = circle.z m τ :=
  aug_sym_cap dimLE_oneDim oneDim.isLeftCounital_aw oneDim.isRightCounital_aw
    (circle.isCycle_z m) τ

end Circle

/-! ### The interval pair `(I, ∂I)` -/

section Interval

theorem sum_ite_succ_eq {n : ℕ} (j : Fin (n + 1)) (f : Fin n → ℚ) :
    ∑ i : Fin n, (if j = i.succ then f i else 0) = if h : j = 0 then 0 else f (j.pred h) := by
  cases j using Fin.cases with
  | zero => simp [(Fin.succ_ne_zero _).symm]
  | succ a => simp [Fin.succ_inj]

theorem sum_ite_castSucc_eq {n : ℕ} (j : Fin (n + 1)) (f : Fin n → ℚ) :
    ∑ i : Fin n, (if j = i.castSucc then f i else 0) =
      if h : j = Fin.last n then 0 else f (j.castPred h) := by
  cases j using Fin.lastCases with
  | last => simp [(Fin.castSucc_ne_last _).symm]
  | cast a => simp [Fin.castSucc_inj, (Fin.castSucc_ne_last a)]

variable (m : ℕ)

/-- The boundary `∂I = {v₀, v_{m+1}}` of `I_{m+1}`. -/
def interval.IsEnd (σ : (interval (m + 1)).X) : Prop :=
  σ = .inl 0 ∨ σ = .inl (Fin.last (m + 1))

instance : DecidablePred (interval.IsEnd m) := fun _ ↦ instDecidableOr

theorem interval.isSub_isEnd : (interval (m + 1)).IsSub (interval.IsEnd m) := by
  intro σ τ h hτ
  rcases hτ with rfl | rfl <;> rcases σ with _ | _ <;> simp at h

/-- The relative complex `C(I, ∂I)`. -/
abbrev interval.rel : BasedComplex :=
  (interval (m + 1)).restrict (fun σ ↦ ¬interval.IsEnd m σ)
    (interval.isSub_isEnd m).isLocallyClosed_compl

theorem interval.dimLE_rel : (interval.rel m).DimLE 1 := dimLE_oneDim.restrict _ _

/-- The chain `Σ e`, with `∂ = v_{m+1} - v_0`. -/
def interval.z : (interval (m + 1)).X → ℚ := Sum.elim 0 1

theorem interval.d_z_supp (σ : (interval (m + 1)).X)
    (h : ((interval (m + 1)).d *ᵥ interval.z m) σ ≠ 0) : interval.IsEnd m σ := by
  rcases σ with v | e
  · by_contra hv
    simp only [interval.IsEnd, not_or, Sum.inl.injEq] at hv
    apply h
    have h₁ := sum_ite_succ_eq v (fun _ ↦ (1 : ℚ))
    have h₂ := sum_ite_castSucc_eq v (fun _ ↦ (1 : ℚ))
    rw [dite_eq_right hv.1] at h₁
    rw [dite_eq_right hv.2] at h₂
    simp only [mulVec, dotProduct, Fintype.sum_sum_type, interval.z, Sum.elim_inl, Sum.elim_inr,
      Pi.zero_apply, Pi.one_apply, mul_zero, mul_one, Finset.sum_const_zero, zero_add, of_apply,
      Finset.sum_sub_distrib, h₁, h₂, sub_self]
  · simp [mulVec, dotProduct] at h

/-- The relative cap `F : C^{1-*}(I, ∂I) → C(I)`: `e_k^* ↦ v_k`, `v_j^* ↦ e_{j-1}`. -/
def interval.capRel : Hom ((interval.rel m).dual 1 (interval.dimLE_rel m)) (interval (m + 1)) :=
  relCap dimLE_oneDim oneDim.aw (oneDim.isCellular_aw fun _ ↦ Fin.castSucc_lt_succ.ne)
    (interval.isSub_isEnd m) (z := interval.z m)
    (by rintro (v | e) h <;> simp_all [interval.z]) (interval.d_z_supp m)

theorem interval.capRel_f (σ : (interval (m + 1)).X) (τ : (interval.rel m).X) :
    (interval.capRel m).f σ τ = match σ, τ.1 with
      | .inl v, .inr e => if v = e.castSucc then 1 else 0
      | .inr e, .inl v => if v = e.succ then 1 else 0
      | _, _ => 0 := by
  rw [interval.capRel, relCap_f_apply, oneDim.aw_mulVec (fun _ ↦ rfl)]
  rcases σ with a | a <;> rcases τ with ⟨b | b, hb⟩ <;> rfl

/-- The inverse `g = e_0^* ε : C(I) → C^{1-*}(I, ∂I)`. -/
def interval.g : Hom (interval (m + 1)) ((interval.rel m).dual 1 (interval.dimLE_rel m)) where
  f := Matrix.of fun τ σ ↦ if τ.1 = .inr 0 then (interval (m + 1)).aug σ else 0
  deg0 τ σ h := by
    simp only [of_apply, ne_eq, ite_eq_right_iff, Classical.not_imp] at h
    obtain ⟨h₁, h₂⟩ := h
    have : (interval (m + 1)).deg σ = 0 := by by_contra h₀; simp [aug, h₀] at h₂
    change ((1 - (interval (m + 1)).deg τ.1 : ℕ) : ℤ) = ((interval (m + 1)).deg σ : ℤ) + 0
    rw [h₁, this]; rfl
  comm := by
    ext τ σ
    rw [mul_apply, mul_apply, Finset.sum_eq_zero]
    · by_cases h : (τ : (interval (m + 1)).X) = .inr 0
      · simp only [of_apply, h, ite_true]
        exact (isAugmented_oneDim _ _ _ _ σ).symm
      · simp [h]
    · intro κ _
      rw [dual_d_apply]
      simp only [of_apply, mul_ite, mul_zero]
      split_ifs with h
      · simp [h]
      · rfl

theorem interval.capRel_mul_g :
    (interval.capRel m).f * (interval.g m).f = (interval (m + 1)).augAt (.inl 0) := by
  ext σ σ'
  rw [mul_apply, Finset.sum_eq_single (⟨.inr 0, by simp [interval.IsEnd]⟩ : (interval.rel m).X)
    (fun κ _ hκ ↦ by
      simp only [interval.g, of_apply, mul_ite, mul_zero]
      exact ite_eq_right fun h ↦ hκ (Subtype.ext h)) (by simp)]
  rcases σ with a | a <;> by_cases ha : a = 0 <;> simp [interval.capRel_f, interval.g, augAt, ha]

/-- The homotopy `k(e_i^*) = -(v_1^* + ⋯ + v_i^*)` on all cells of `I`. -/
def interval.kFull : Matrix (interval (m + 1)).X (interval (m + 1)).X ℚ :=
  Matrix.of fun τ σ ↦ match τ, σ with
    | .inl j, .inr i => if 0 < (j : ℕ) ∧ (j : ℕ) ≤ i then -1 else 0
    | _, _ => 0

theorem interval.kFull_ne_zero {τ σ : (interval (m + 1)).X} (h : interval.kFull m τ σ ≠ 0) :
    ∃ j i, τ = .inl j ∧ σ = .inr i ∧ 0 < (j : ℕ) ∧ (j : ℕ) ≤ i := by
  rcases τ with j | j <;> rcases σ with i | i <;> simp [interval.kFull] at h
  exact ⟨j, i, rfl, rfl, h⟩

theorem interval.not_isEnd_of_kFull {τ σ : (interval (m + 1)).X}
    (h : interval.kFull m τ σ ≠ 0) : ¬interval.IsEnd m τ ∧ ¬interval.IsEnd m σ := by
  obtain ⟨j, i, rfl, rfl, h₁, h₂⟩ := interval.kFull_ne_zero m h
  refine ⟨?_, by simp [interval.IsEnd]⟩
  rintro (h | h) <;> simp only [Sum.inl.injEq, Fin.ext_iff, Fin.val_zero, Fin.val_last] at h
  · omega
  · have := i.2; omega

/-- The pair duality `F : C^{1-*}(I, ∂I) ≃ C(I)` with inverse `g = e_0^* ε`, homotopies `-s`
(the cone contraction) and `k`. -/
def interval.relDuality :
    HtpyEquiv ((interval.rel m).dual 1 (interval.dimLE_rel m)) (interval (m + 1)) where
  hom := interval.capRel m
  inv := interval.g m
  homInv :=
    { h := (interval.kFull m).submatrix Subtype.val Subtype.val
      deg1 := by
        intro τ σ h
        obtain ⟨j, i, h₁, h₂, -⟩ := interval.kFull_ne_zero m h
        change ((1 - (interval (m + 1)).deg τ.1 : ℕ) : ℤ) =
          ((1 - (interval (m + 1)).deg σ.1 : ℕ) : ℤ) + 1
        rw [h₁, h₂]; rfl
      eq := by
        ext ⟨τ, hτ⟩ ⟨σ, hσ⟩
        have e₃ : ((interval.g m).comp (interval.capRel m)).f ⟨τ, hτ⟩ ⟨σ, hσ⟩ =
            if τ = .inr 0 then interval.z m σ else 0 := by
          simp only [Hom.comp_f, mul_apply, interval.g, of_apply, ite_mul, zero_mul]
          split_ifs
          · exact sum_aug_mulVec oneDim.isLeftCounital_aw (interval.z m) σ
          · simp
        rw [Matrix.sub_apply, Matrix.add_apply, e₃, Hom.id_f, restrict_dual_d dimLE_oneDim,
          mul_submatrix_apply, mul_submatrix_apply]
        rotate_left
        · exact fun κ h ↦ (interval.not_isEnd_of_kFull m (left_ne_zero_of_mul h)).2
        · exact fun κ h ↦ (interval.not_isEnd_of_kFull m (right_ne_zero_of_mul h)).1
        simp only [interval.IsEnd, not_or] at hτ hσ
        simp only [mul_apply]
        rcases τ with j | e <;> rcases σ with j' | i <;>
          simp [Fintype.sum_sum_type, interval.kFull, interval.z, one_apply, sgn, mul_diagonal]
        · simp only [Sum.inl.injEq] at hτ hσ
          have hsum : ∀ x : Fin (m + 1), (if 0 < j ∧ (j : ℕ) ≤ x then
              (if j' = x.castSucc then (1 : ℚ) else 0) - (if j' = x.succ then 1 else 0) else 0) =
              (if j' = x.castSucc then (if 0 < j ∧ (j : ℕ) ≤ x then 1 else 0) else 0) -
                (if j' = x.succ then (if 0 < j ∧ (j : ℕ) ≤ x then 1 else 0) else 0) :=
            fun x ↦ by split_ifs <;> simp
          rw [Finset.sum_congr rfl fun x _ ↦ hsum x, Finset.sum_sub_distrib, sum_ite_castSucc_eq,
            sum_ite_succ_eq, dite_eq_right hσ.2, dite_eq_right hσ.1]
          have h₁ : (j : ℕ) ≠ 0 := fun h ↦ hτ.1 (Fin.ext h)
          have h₂ : (j' : ℕ) ≠ 0 := fun h ↦ hσ.1 (Fin.ext h)
          simp only [Fin.coe_castPred, Fin.val_pred, Fin.lt_def, Fin.ext_iff, Fin.val_zero]
          split_ifs <;> first | (exfalso; omega) | norm_num
        · have hsum : ∀ x : Fin (m + 1 + 1), (if 0 < x ∧ (x : ℕ) ≤ i then
              (if x = e.castSucc then (1 : ℚ) else 0) - (if x = e.succ then 1 else 0) else 0) =
              (if x = e.castSucc then (if 0 < x ∧ (x : ℕ) ≤ i then 1 else 0) else 0) -
                (if x = e.succ then (if 0 < x ∧ (x : ℕ) ≤ i then 1 else 0) else 0) :=
            fun x ↦ by split_ifs <;> simp_all
          rw [Finset.sum_congr rfl fun x _ ↦ hsum x, Finset.sum_sub_distrib, Finset.sum_ite_eq',
            Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _), ite_eq_left (Finset.mem_univ _)]
          simp only [Fin.val_castSucc, Fin.val_succ, Fin.lt_def, Fin.ext_iff, Fin.val_zero]
          split_ifs <;> first | (exfalso; omega) | norm_num }
  invHom :=
    { h := -(interval.contraction (m + 1)).s
      deg1 := (interval.contraction (m + 1)).deg1.neg
      eq := by
        rw [Hom.comp_f, interval.capRel_mul_g, Hom.id_f, Matrix.mul_neg, Matrix.neg_mul, ← neg_add,
          (interval.contraction (m + 1)).eq, neg_sub]
        rfl }

theorem interval.relDuality_hom : (interval.relDuality m).hom = interval.capRel m := rfl

/-- The opposite pair map `C^{1-*}(I) → C(I, ∂I)`, the transpose of `F`, with the transposed
inverse and homotopies (review fix 3: both B-pair directions). -/
def interval.absDuality :
    HtpyEquiv ((interval (m + 1)).dual 1 dimLE_oneDim) (interval.rel m) :=
  (interval.relDuality m).transpose (interval.dimLE_rel m) dimLE_oneDim

theorem interval.absDuality_hom_f (σ : (interval.rel m).X) (τ : (interval (m + 1)).X) :
    (interval.absDuality m).hom.f σ τ = (interval.capRel m).f τ σ := by
  rw [interval.absDuality, HtpyEquiv.transpose_hom, transpose_f_apply]
  norm_num
  rfl

end Interval

/-! ### The cellular `CP²` and its signature -/

/-- The cellular `CP²` of l. 1093 (`CP⁰ ⊂ CP¹ ⊂ CP²`): cells `e₀, e₂, e₄` (index `i ↦ e_{2i}`),
zero differential. -/
abbrev CPcell : BasedComplex where
  X := Fin 3
  deg i := 2 * i
  d := 0
  d_deg _ _ h := (h rfl).elim
  d_d := by simp

theorem CPcell.dimLE : CPcell.DimLE 4 := fun i ↦ by
  have := i.2; change 2 * (i : ℕ) ≤ 4; omega

/-- The cellular diagonal `Δ e_{2k} = Σ_{i+j=k} e_{2i} ⊗ e_{2j}`.  The coefficient `+1` of
`e₂ ⊗ e₂` in `Δ e₄` is the complex orientation: `⟨e₂^* ∪ e₂^*, e₄⟩ = +1`, i.e. two projective
lines meet in one positive point (l. 1093). -/
def CPcell.diag : Diagonal CPcell where
  f := Matrix.of fun p k ↦ if (p.1 : ℕ) + p.2 = k then 1 else 0
  deg0 p k h := by
    simp only [of_apply, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at h
    change ((2 * (p.1 : ℕ) + 2 * (p.2 : ℕ) : ℕ) : ℤ) = ((2 * (k : ℕ) : ℕ) : ℤ) + 0
    omega
  comm := by
    rw [tensor_d]
    simp [CPcell]

/-- The complex fundamental class `z = e₄`. -/
def CPcell.z : CPcell.X → ℚ := fun k ↦ if k = 2 then 1 else 0

theorem CPcell.isCycle_z : IsCycle CPcell 4 CPcell.z where
  deg k h := by
    have : k = 2 := by by_contra h'; simp [CPcell.z, h'] at h
    subst this; rfl
  cycle := by simp [CPcell]

/-- The cap `φ = z ∩ : e_{2i}^* ↦ e_{4-2i}`. -/
def CPcell.φ : Hom (CPcell.dual 4 CPcell.dimLE) CPcell :=
  cap CPcell.dimLE CPcell.diag CPcell.isCycle_z

theorem CPcell.φ_f (i j : CPcell.X) : CPcell.φ.f i j = if (i : ℕ) + j = 2 then 1 else 0 := by
  rw [CPcell.φ, cap_f_apply, Finset.sum_eq_single (2 : Fin 3) (fun k _ hk ↦ by simp [CPcell.z, hk])
    (by simp)]
  simp [CPcell.diag, CPcell.z]

theorem CPcell.φ_mul_φ : CPcell.φ.f * CPcell.φ.f = 1 := by
  ext i j
  simp only [mul_apply, CPcell.φ_f, Fin.sum_univ_three, one_apply]
  fin_cases i <;> fin_cases j <;> simp

/-- `T φ = φ`: all cells are even, so `ε = 1` and `φ` is the symmetric antidiagonal. -/
theorem CPcell.isSymm_φ : IsSymm CPcell.dimLE CPcell.φ := by
  rw [isSymm_iff]
  intro i j
  rw [CPcell.φ_f, CPcell.φ_f, show CPcell.deg i = 2 * (i : ℕ) from rfl, pow_mul]
  norm_num [add_comm]

/-- The symmetric `4`-dimensional duality of `CPcell`; `φ` is an isomorphism, its own inverse. -/
def CPcell.duality : SymDuality CPcell 4 CPcell.dimLE where
  toHtpyEquiv := HtpyEquiv.ofIso CPcell.φ CPcell.φ.f
    (fun i j h ↦ by
      have h' := CPcell.φ.deg0 i j h
      change ((2 * (i : ℕ) : ℕ) : ℤ) = ((4 - 2 * (j : ℕ) : ℕ) : ℤ) + 0 at h'
      change ((4 - 2 * (i : ℕ) : ℕ) : ℤ) = ((2 * (j : ℕ) : ℕ) : ℤ) + 0
      have := i.2; have := j.2; omega)
    CPcell.φ_mul_φ CPcell.φ_mul_φ
  symm := CPcell.isSymm_φ

theorem CPcell.duality_hom : CPcell.duality.hom = CPcell.φ := rfl

/-- `ε ∘ φ = ⟨-, e₄⟩`. -/
theorem CPcell.aug_φ (τ : CPcell.X) : ∑ σ, CPcell.aug σ * CPcell.φ.f σ τ = CPcell.z τ := by
  simp only [CPcell.φ_f, Fin.sum_univ_three, CPcell.z, aug]
  fin_cases τ <;> simp

/-- **The middle form of `CPcell` is `⟨1⟩`**: on the middle cochains `C^2 = ℚ e₂^*`,
`b(e₂^*, e₂^*) = ⟨e₂^*, φ e₂^*⟩ = +1`. -/
theorem CPcell.middleForm_eq : middleForm CPcell.φ.f 2 = 1 := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  change 2 * (i : ℕ) = 2 at hi
  change 2 * (j : ℕ) = 2 at hj
  have hi' : i = 1 := Fin.ext (by simp; omega)
  have hj' : j = 1 := Fin.ext (by simp; omega)
  subst hi' hj'
  simp [middleForm, CPcell.φ_f]

theorem ratSignature_toBilin'_one (ι : Type) [Fintype ι] [DecidableEq ι] :
    ratSignature (Matrix.toBilin' (1 : Matrix ι ι ℚ)) = Fintype.card ι := by
  set B := (Pi.basisFun ℚ ι).baseChange ℝ
  set bc := LinearMap.BilinForm.baseChange ℝ (Matrix.toBilin' (1 : Matrix ι ι ℚ))
  have hM : LinearMap.BilinForm.toMatrix B bc = 1 := by
    ext i j
    simp [LinearMap.BilinForm.toMatrix_apply, B, bc, one_apply, Matrix.toBilin'_apply',
      Algebra.smul_def]
  have hb : ∀ x, bc x x = ∑ i, B.repr x i * B.repr x i := fun x ↦ by
    rw [← Matrix.toBilin_toMatrix B bc, hM]
    simp [Matrix.toBilin_apply, one_apply]
  have hpos : PosDefOn bc ⊤ := fun x _ hx ↦ by
    rw [hb]
    obtain ⟨i, hi⟩ : ∃ i, B.repr x i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx (B.repr.injective (Finsupp.ext fun i ↦ by simp [h i]))
    exact lt_of_lt_of_le (mul_self_pos.mpr hi)
      (Finset.single_le_sum (fun j _ ↦ mul_self_nonneg (B.repr x j)) (Finset.mem_univ i))
  have h₁ : posIndex bc = Fintype.card ι := by
    rw [posIndex_eq_finrank isCompl_top_bot hpos
      (fun x hx hx' ↦ (hx' ((Submodule.mem_bot ℝ).mp hx)).elim), finrank_top,
      Module.finrank_eq_card_basis B]
  have h₂ : posIndex (-bc) = 0 := by
    rw [posIndex_eq_finrank isCompl_bot_top
      (fun x hx hx' ↦ (hx' ((Submodule.mem_bot ℝ).mp hx)).elim)
      (fun v hv hv₀ ↦ by simpa using hpos v hv hv₀), finrank_bot]
  simp [ratSignature, signature, h₁, h₂, bc]

/-- **`σ(CPcell) = 1`**: the signature of the middle form, computed over `ℝ` (Sylvester). -/
theorem CPcell.ratSignature_middleForm :
    ratSignature (Matrix.toBilin' (middleForm CPcell.φ.f 2)) = 1 := by
  rw [CPcell.middleForm_eq, ratSignature_toBilin'_one]
  rfl

end BasedComplex

end HSFormal.Cubical
