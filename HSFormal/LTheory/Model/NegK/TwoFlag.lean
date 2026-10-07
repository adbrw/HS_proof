import HSFormal.LTheory.Model.NegK.LineModule
import HSFormal.LTheory.Model.NegK.IntervalDecomp

/-!
# The two-flag splitting of a bounded idempotent (NegK level 1, module 4)

`blueprint/negK-proof.md` §2.1–2.4 and §6, for one fibre, in the abstract setting of
`LineModule`: a ring `R`, modules `V w` (`w : ℤ`) with `𝕍 = Π_w V w` semisimple, and a bounded
(`IsBounded p b`) idempotent (`IsIdem p b`) matrix `p w' w : V w →ₗ V w'` with action
`p̂ = act p b` on `𝕍`.

* `P u v = 𝕍_{[u,v]} ∩ ker (p̂ - 1)` is an interval family (`P_empty`, `P_inf`, rule (H)).
* **Lemma 1** (`P_local`): `P u v ≤ P u (v-1) ⊔ P (u+1) v` when `v - u > 2b`.
* `C` (two-flag complements, `IntervalDecomp.exists_compl`), `Dw v = ⨆_{u ∈ [v-2b, v]} C u v`
  (independent: `iSupIndep_D`; `P c a ≤ ⨆_{v ∈ [c,a]} Dw v`: `P_le_iSup_D`), the projections
  `π v` onto `Dw v` (`IntervalDecomp.proj`) and an idempotent `eproj v` of `𝕍` with image `Dw v`
  (a projection along a complement; semisimplicity).
* The blocks `A v u w x = (π_v (p̂ δ_w x))_u` (`α`) and `Bm w v u y = (e_v δ_u y)_w` (`β`, and
  also the diagonal idempotent `d_v`).
* `exists_blocks`: the bounds (`A v u w = 0` for `|v - w| > b`, `Bm w v u = 0` for
  `w ∉ [v - 2b, v]`) and the three identities `∑ β α = p` (I1), `∑ α β = δ_{v v'} d_v` (I2),
  `d_v² = d_v` (I3), stated blockwise.

**Deviation from blueprint §6.**  `e v` is a projection of all of `𝕍` onto `Dw v` (not of the
finite product `𝕎 v`); only `e v|_{Dw v} = id` and `range (e v) ⊆ Dw v` are used, so no
restriction to `𝕎 v` is needed.  `π v` is a projection of all of `𝕍` (along the other `Dw v'`
and a complement of `⨆ Dw`), so `P_fin` never appears.
-/

namespace HSFormal.LTheory.TwoFlag

open Finset LineModule

variable {R : Type*} [Ring R] {V : ℤ → Type*} [∀ w, AddCommGroup (V w)] [∀ w, Module R (V w)]
  {p : ∀ w' w, V w →ₗ[R] V w'} {b : ℕ}

variable (p b) in
/-- The `p̂`-fixed vectors. -/
def fixed : Submodule R (∀ w, V w) := LinearMap.ker (act p b - LinearMap.id)

lemma mem_fixed {x : ∀ w, V w} : x ∈ fixed p b ↔ act p b x = x := by
  simp [fixed, sub_eq_zero]

variable (p b) in
/-- The interval family `P[u, v] = 𝕍_{[u,v]} ∩ ker (p̂ - 1)`. -/
def P (u v : ℤ) : Submodule R (∀ w, V w) := suppIcc R V u v ⊓ fixed p b

lemma P_empty (u v : ℤ) (h : v < u) : P p b u v = ⊥ := by
  rw [P, suppIcc_eq_bot h, bot_inf_eq]

lemma P_inf (u v u' v' : ℤ) : P p b u v ⊓ P p b u' v' = P p b (max u u') (min v v') := by
  rw [P, P, P, ← suppIcc_inf, inf_inf_inf_comm, inf_idem]

lemma act_mem_P (hb : IsBounded p b) (hp : IsIdem p b) {u v : ℤ} {x : ∀ w, V w}
    (hx : x ∈ suppIcc R V u v) : act p b x ∈ P p b (u - b) (v + b) :=
  ⟨act_mem_suppIcc hx, mem_fixed.2 (act_act hb hp x)⟩

/-- **Lemma 1 (locality).** -/
lemma P_local (hb : IsBounded p b) (hp : IsIdem p b) (u v : ℤ) (h : ((2 * b : ℕ) : ℤ) < v - u) :
    P p b u v ≤ IntervalDecomp.S (P p b) u v := by
  intro y ⟨hys, hyf⟩
  rw [SetLike.mem_coe, mem_fixed] at hyf
  push_cast at h
  set m : ℤ := u + b
  set y' : ∀ w, V w := fun w ↦ if w ≤ m then y w else 0
  have hy's : y' ∈ suppIcc R V u m := fun w hw ↦ by
    simp only [y']
    split_ifs with h'
    · exact hys w (by omega)
    · rfl
  have hy''s : y - y' ∈ suppIcc R V (m + 1) v := fun w hw ↦ by
    simp only [y', Pi.sub_apply]
    split_ifs with h'
    · exact sub_self _
    · rw [hys w (by omega), sub_zero]
  have hsum : act p b y' + act p b (y - y') = y := by
    rw [← map_add, add_sub_cancel, hyf]
  have h₁s := act_mem_suppIcc (p := p) (b := b) hy's
  have h₂s := act_mem_suppIcc (p := p) (b := b) hy''s
  have h₁ : act p b y' ∈ P p b u (v - 1) := by
    refine ⟨fun w hw ↦ ?_, mem_fixed.2 (act_act hb hp _)⟩
    rcases hw with hw | hw
    · rw [eq_sub_of_add_eq hsum, Pi.sub_apply, hys w (Or.inl hw), h₂s w (Or.inl (by omega)),
        sub_zero]
    · exact h₁s w (Or.inr (by omega))
  have h₂ : act p b (y - y') ∈ P p b (u + 1) v := by
    refine ⟨fun w hw ↦ ?_, mem_fixed.2 (act_act hb hp _)⟩
    rcases hw with hw | hw
    · exact h₂s w (Or.inl (by omega))
    · rw [eq_sub_of_add_eq' hsum, Pi.sub_apply, hys w (Or.inr hw), h₁s w (Or.inr (by omega)),
        sub_zero]
  rw [← hsum]
  exact Submodule.add_mem_sup h₁ h₂

/-! ### The two-flag decomposition (semisimple case) -/

section Semisimple

variable [IsSemisimpleModule R (∀ w, V w)]

variable (p b) in
/-- Chosen two-flag complements: `C u v ⊕ (P[u, v-1] + P[u+1, v]) = P[u, v]`. -/
noncomputable def C : ℤ → ℤ → Submodule R (∀ w, V w) :=
  (IntervalDecomp.exists_compl (P_inf (p := p) (b := b))).choose

lemma C_spec₁ (u v : ℤ) : Disjoint (C p b u v) (IntervalDecomp.S (P p b) u v) :=
  ((IntervalDecomp.exists_compl (P_inf (p := p) (b := b))).choose_spec u v).1

lemma C_spec₂ (u v : ℤ) : C p b u v ⊔ IntervalDecomp.S (P p b) u v = P p b u v :=
  ((IntervalDecomp.exists_compl (P_inf (p := p) (b := b))).choose_spec u v).2

variable (p b) in
/-- `Dw v = ⨆_{u ∈ [v - 2b, v]} C u v`. -/
noncomputable def Dw (v : ℤ) : Submodule R (∀ w, V w) := IntervalDecomp.D (C p b) (2 * b) v

lemma Dw_le_P (v : ℤ) : Dw p b v ≤ P p b (v - ((2 * b : ℕ) : ℤ)) v :=
  IntervalDecomp.D_le P_inf C_spec₂ (2 * b) v

lemma Dw_le_supp (v : ℤ) : Dw p b v ≤ suppIcc R V (v - 2 * b) v := by
  have := (Dw_le_P (p := p) (b := b) v).trans inf_le_left
  push_cast at this
  exact this

lemma Dw_le_fixed (v : ℤ) : Dw p b v ≤ fixed p b :=
  (Dw_le_P v).trans inf_le_right

lemma iSupIndep_D : iSupIndep (Dw p b) :=
  IntervalDecomp.iSupIndep_of_supIndep_Icc fun m M ↦
    IntervalDecomp.supIndep_D P_empty P_inf C_spec₁ C_spec₂ m M

lemma P_le_iSup_D (hb : IsBounded p b) (hp : IsIdem p b) (c a : ℤ) :
    P p b c a ≤ ⨆ v ∈ Icc c a, Dw p b v := by
  rw [← Finset.sup_eq_iSup]
  exact IntervalDecomp.P_le_sup_D P_empty P_inf C_spec₁ C_spec₂ (P_local hb hp) c a

variable (p b) in
/-- The projection `π v` onto `Dw v` (along the other `Dw v'`). -/
noncomputable def π (v : ℤ) : (∀ w, V w) →ₗ[R] (∀ w, V w) :=
  IntervalDecomp.proj (iSupIndep_D (p := p) (b := b)) v

lemma π_mem (v : ℤ) (x : ∀ w, V w) : π p b v x ∈ Dw p b v := IntervalDecomp.proj_mem _ v x

variable (p b) in
/-- An idempotent of `𝕍` with image `Dw v`. -/
noncomputable def eproj (v : ℤ) : (∀ w, V w) →ₗ[R] (∀ w, V w) :=
  (Dw p b v).subtype ∘ₗ
    Submodule.projectionOnto _ _ (exists_isCompl (Dw p b v)).choose_spec

lemma eproj_mem (v : ℤ) (x : ∀ w, V w) : eproj p b v x ∈ Dw p b v := by
  simp [eproj]

lemma eproj_of_mem {v : ℤ} {y : ∀ w, V w} (hy : y ∈ Dw p b v) : eproj p b v y = y := by
  exact congrArg Subtype.val
    (Submodule.projectionOnto_apply_left (exists_isCompl (Dw p b v)).choose_spec ⟨y, hy⟩)

variable (p b) in
/-- The blocks of `α`: `A v u w x = (π_v (p̂ δ_w x))_u`. -/
noncomputable def A (v u w : ℤ) : V w →ₗ[R] V u :=
  LinearMap.proj u ∘ₗ π p b v ∘ₗ act p b ∘ₗ LinearMap.single R V w

variable (p b) in
/-- The blocks of `β` (and of the diagonal idempotent): `Bm w v u y = (e_v δ_u y)_w`. -/
noncomputable def Bm (w v u : ℤ) : V u →ₗ[R] V w :=
  LinearMap.proj w ∘ₗ eproj p b v ∘ₗ LinearMap.single R V u

lemma A_apply (v u w : ℤ) (x : V w) : A p b v u w x = π p b v (act p b (Pi.single w x)) u := rfl

lemma Bm_apply (w v u : ℤ) (y : V u) : Bm p b w v u y = eproj p b v (Pi.single u y) w := rfl

/-- (F5): `α` has propagation `≤ b`. -/
lemma A_eq_zero (hb : IsBounded p b) (hp : IsIdem p b) {v u w : ℤ} (h : (b : ℤ) < |v - w|) :
    A p b v u w = 0 := by
  ext x
  rw [A_apply, LinearMap.zero_apply]
  have hmem := P_le_iSup_D hb hp (w - b) (w + b) (act_mem_P hb hp (single_mem_suppIcc w x))
  rw [π, IntervalDecomp.proj_eq_zero_of_mem_iSup _ hmem (by rw [mem_Icc]; rw [lt_abs] at h; omega)]
  rfl

/-- (F4): `β` has propagation `≤ 2b`. -/
lemma Bm_eq_zero {w v u : ℤ} (h : w < v - 2 * b ∨ v < w) : Bm p b w v u = 0 := by
  ext y
  rw [Bm_apply, LinearMap.zero_apply]
  exact Dw_le_supp v (eproj_mem v _) w h

/-- (I1): `∑_v β_{w', v} α_{v, w} = p_{w', w}`. -/
lemma sum_Bm_A (hb : IsBounded p b) (hp : IsIdem p b) (w' w : ℤ) {s : Finset ℤ}
    (hs : win w b ⊆ s) :
    ∑ v ∈ s, ∑ u ∈ Icc (v - 2 * b) v, (Bm p b w' v u).comp (A p b v u w) = p w' w := by
  ext x
  set y := act p b (Pi.single w x) with hy_def
  have hy : y ∈ ⨆ v ∈ Icc (w - b) (w + b), Dw p b v :=
    P_le_iSup_D hb hp (w - b) (w + b) (act_mem_P hb hp (single_mem_suppIcc w x))
  have key : ∀ v : ℤ,
      ∑ u ∈ Icc (v - 2 * b) v, Bm p b w' v u (A p b v u w x) = π p b v y w' := by
    intro v
    simp only [Bm_apply, A_apply, ← hy_def]
    rw [← Finset.sum_apply, ← map_sum,
      sum_single_of_mem (Dw_le_supp v (π_mem v y)) subset_rfl, eproj_of_mem (π_mem v y)]
  have hsum : ∑ v ∈ s, π p b v y = y := by
    rw [sum_congr_of_zero (t := Icc (w - b) (w + b)) fun v hv ↦ ?_]
    · exact IntervalDecomp.sum_proj_of_mem_iSup _ hy
    · refine IntervalDecomp.proj_eq_zero_of_mem_iSup _ hy ?_
      rcases hv with hv | hv
      · exact fun h ↦ hv (hs h)
      · exact hv
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, key]
  rw [← Finset.sum_apply, hsum, hy_def, act_single hb w x w']

/-- (I2): `∑_w α_{v', w} β_{w, v} = δ_{v v'} d_v`. -/
lemma sum_A_Bm (v' v u' u : ℤ) {s : Finset ℤ} (hs : Icc (v - 2 * b) v ⊆ s) :
    ∑ w ∈ s, (A p b v' u' w).comp (Bm p b w v u) = if v' = v then Bm p b u' v u else 0 := by
  ext x
  have hzD : eproj p b v (Pi.single u x) ∈ Dw p b v := eproj_mem v _
  have key : ∑ w ∈ s, A p b v' u' w (Bm p b w v u x) = π p b v' (eproj p b v (Pi.single u x)) u' := by
    simp only [A_apply, Bm_apply]
    rw [← Finset.sum_apply, ← map_sum, ← map_sum, sum_single_of_mem (Dw_le_supp v hzD) hs,
      mem_fixed.1 (Dw_le_fixed v hzD)]
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply]
  rw [key, π, IntervalDecomp.proj_of_mem _ hzD v']
  split_ifs <;> rfl

/-- (I3): `d_v² = d_v`. -/
lemma sum_Bm_Bm (v u'' u : ℤ) :
    ∑ u' ∈ Icc (v - 2 * b) v, (Bm p b u'' v u').comp (Bm p b u' v u) = Bm p b u'' v u := by
  ext x
  have hzD : eproj p b v (Pi.single u x) ∈ Dw p b v := eproj_mem v _
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, Bm_apply]
  rw [← Finset.sum_apply, ← map_sum, sum_single_of_mem (Dw_le_supp v hzD) subset_rfl,
    eproj_of_mem hzD]

/-- **The two-flag blocks** (one fibre of Theorem A): blocks `A` of `α` (propagation `≤ b`) and
`B` of `β` / of the diagonal idempotent (supported in `w ∈ [v - 2b, v]`) with
(I1) `∑_v ∑_u B w' v u ∘ A v u w = p w' w`, (I2) `∑_w A v' u' w ∘ B w v u = δ_{v' v} B u' v u`,
(I3) `∑_{u'} B u'' v u' ∘ B u' v u = B u'' v u`. -/
theorem exists_blocks (hb : IsBounded p b) (hp : IsIdem p b) :
    ∃ (A : ℤ → ∀ u w : ℤ, V w →ₗ[R] V u) (B : ∀ w : ℤ, ℤ → ∀ u : ℤ, V u →ₗ[R] V w),
      (∀ v u w : ℤ, (b : ℤ) < |v - w| → A v u w = 0) ∧
      (∀ w v u : ℤ, w < v - 2 * b ∨ v < w → B w v u = 0) ∧
      (∀ (w' w : ℤ) (s : Finset ℤ), win w b ⊆ s →
        ∑ v ∈ s, ∑ u ∈ Icc (v - 2 * b) v, (B w' v u).comp (A v u w) = p w' w) ∧
      (∀ (v' v u' u : ℤ) (s : Finset ℤ), Icc (v - 2 * b) v ⊆ s →
        ∑ w ∈ s, (A v' u' w).comp (B w v u) = if v' = v then B u' v u else 0) ∧
      (∀ v u'' u : ℤ, ∑ u' ∈ Icc (v - 2 * b) v, (B u'' v u').comp (B u' v u) = B u'' v u) :=
  ⟨A p b, Bm p b, fun _ _ _ h ↦ A_eq_zero hb hp h, fun _ _ _ h ↦ Bm_eq_zero h,
    fun w' w _ hs ↦ sum_Bm_A hb hp w' w hs, fun v' v u' u _ hs ↦ sum_A_Bm v' v u' u hs,
    fun v u'' u ↦ sum_Bm_Bm v u'' u⟩

end Semisimple

end HSFormal.LTheory.TwoFlag
