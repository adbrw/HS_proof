import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Group.Abs

/-!
# The line module of a bounded matrix (NegK level 1, module 3)

`blueprint/negK-proof.md` §2.1 and §6 steps 1–2, in an abstract form independent of the
category `C_ℤ(B)` (the dictionary to `C_ℤ(finSuppFreeQG G T)` is `FreeQGMat`/`KarDiag`).

For a ring `R` and `R`-modules `V w` (`w : ℤ`), `𝕍 = Π_w V w` is the **full** product (no
finiteness).  A *bounded matrix* is a family `p w' w : V w →ₗ V w'` (target index first, as in
`CZ.Mat`) with `p w' w = 0` for `|w' - w| > b` (`IsBounded p b`).  It acts on `𝕍` by the window
sums `(act p b x) w' = ∑_{w ∈ [w' - b, w' + b]} p w' w (x w)` (`act`), a well-defined `R`-linear
map.  If `p` is idempotent as a matrix (`IsIdem p b`, the entrywise form of `p ≫ p = p`), then
`act p b` is idempotent (`act_act`).

Supports: `suppIcc u v` is the submodule of vectors supported in `[u, v]`; `act` widens supports by
`b` (`act_mem_suppIcc`); `act_single` computes `act` on `Pi.single w x`; `sum_single_of_mem`
reconstructs a vector supported in `[u, v]` from its coordinates.
-/

namespace HSFormal.LTheory.LineModule

open Finset

/-- The window `[w - b, w + b]` (equal to `CZ.window w b`). -/
def win (w : ℤ) (b : ℕ) : Finset ℤ := Icc (w - b) (w + b)

lemma mem_win {w w' : ℤ} {b : ℕ} : w' ∈ win w b ↔ w - b ≤ w' ∧ w' ≤ w + b := mem_Icc

/-- Two finite sums agree when the summand vanishes off the intersection of the ranges. -/
lemma sum_congr_of_zero {M : Type*} [AddCommMonoid M] {s t : Finset ℤ} {f : ℤ → M}
    (h : ∀ w, w ∉ s ∨ w ∉ t → f w = 0) : ∑ w ∈ s, f w = ∑ w ∈ t, f w := by
  rw [← sum_subset (inter_subset_left (s₁ := s) (s₂ := t)) fun w hws hw ↦
      h w (Or.inr fun hwt ↦ hw (mem_inter.2 ⟨hws, hwt⟩)),
    ← sum_subset (inter_subset_right (s₁ := s) (s₂ := t)) fun w hwt hw ↦
      h w (Or.inl fun hws ↦ hw (mem_inter.2 ⟨hws, hwt⟩))]

variable {R : Type*} [Ring R] {V : ℤ → Type*} [∀ w, AddCommGroup (V w)] [∀ w, Module R (V w)]

/-! ### Supports -/

variable (R V) in
/-- Vectors of `𝕍 = Π_w V w` supported in `[u, v]`. -/
def suppIcc (u v : ℤ) : Submodule R (∀ w, V w) where
  carrier := {x | ∀ w, w < u ∨ v < w → x w = 0}
  zero_mem' _ _ := rfl
  add_mem' hx hy w hw := by simp [hx w hw, hy w hw]
  smul_mem' c x hx w hw := by simp [hx w hw]

lemma mem_suppIcc {u v : ℤ} {x : ∀ w, V w} :
    x ∈ suppIcc R V u v ↔ ∀ w, w < u ∨ v < w → x w = 0 := Iff.rfl

lemma suppIcc_mono {u v u' v' : ℤ} (hu : u' ≤ u) (hv : v ≤ v') :
    suppIcc R V u v ≤ suppIcc R V u' v' := fun _ hx w hw ↦ hx w (by omega)

lemma suppIcc_inf (u v u' v' : ℤ) :
    suppIcc R V u v ⊓ suppIcc R V u' v' = suppIcc R V (max u u') (min v v') := by
  ext x
  simp only [Submodule.mem_inf, mem_suppIcc]
  constructor
  · rintro ⟨h, h'⟩ w hw
    rcases hw with hw | hw
    · rcases lt_max_iff.1 hw with hw | hw
      · exact h w (Or.inl hw)
      · exact h' w (Or.inl hw)
    · rcases min_lt_iff.1 hw with hw | hw
      · exact h w (Or.inr hw)
      · exact h' w (Or.inr hw)
  · intro h
    exact ⟨fun w hw ↦ h w (by omega), fun w hw ↦ h w (by omega)⟩

lemma suppIcc_eq_bot {u v : ℤ} (h : v < u) : suppIcc R V u v = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  exact (Submodule.mem_bot R).2 (funext fun w ↦ hx w (by omega))

lemma single_mem_suppIcc (w : ℤ) (x : V w) : Pi.single w x ∈ suppIcc R V w w := fun w' hw' ↦
  Pi.single_eq_of_ne (by omega) x

/-- A vector supported in `[u, v]` is the sum of its coordinates over any `s ⊇ [u, v]`. -/
lemma sum_single_of_mem {u v : ℤ} {x : ∀ w, V w} (hx : x ∈ suppIcc R V u v) {s : Finset ℤ}
    (hs : Icc u v ⊆ s) : ∑ w ∈ s, Pi.single w (x w) = x := by
  funext w'
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single w' (fun w _ hw ↦ Pi.single_eq_of_ne' hw _) ?_]
  · exact Pi.single_eq_same w' _
  · intro hw'
    rw [Pi.single_eq_same]
    exact hx w' (by
      by_contra h
      exact hw' (hs (mem_Icc.2 ⟨by omega, by omega⟩)))

/-! ### Bounded matrices and their action -/

/-- `p` has propagation `≤ b`. -/
def IsBounded (p : ∀ w' w, V w →ₗ[R] V w') (b : ℕ) : Prop :=
  ∀ w' w, (b : ℤ) < |w' - w| → p w' w = 0

/-- `p` is idempotent as a matrix: `∑_{w'} p w'' w' ∘ p w' w = p w'' w` (window of `w`). -/
def IsIdem (p : ∀ w' w, V w →ₗ[R] V w') (b : ℕ) : Prop :=
  ∀ w'' w, ∑ w' ∈ win w b, (p w'' w').comp (p w' w) = p w'' w

variable {p : ∀ w' w, V w →ₗ[R] V w'} {b : ℕ}

lemma IsBounded.eq_zero (hb : IsBounded p b) {w' w : ℤ} (h : w ∉ win w' b) : p w' w = 0 :=
  hb w' w (by rw [mem_win] at h; rw [lt_abs]; omega)

lemma IsBounded.eq_zero' (hb : IsBounded p b) {w' w : ℤ} (h : w' ∉ win w b) : p w' w = 0 :=
  hb w' w (by rw [mem_win] at h; rw [lt_abs]; omega)

variable (p b) in
/-- The action `(act p b x) w' = ∑_{w ∈ [w' - b, w' + b]} p w' w (x w)` on the full product. -/
def act : (∀ w, V w) →ₗ[R] (∀ w, V w) :=
  LinearMap.pi fun w' ↦ ∑ w ∈ win w' b, (p w' w).comp (LinearMap.proj w)

lemma act_apply (x : ∀ w, V w) (w' : ℤ) : act p b x w' = ∑ w ∈ win w' b, p w' w (x w) := by
  simp [act]

lemma act_single (hb : IsBounded p b) (w : ℤ) (x : V w) (w' : ℤ) :
    act p b (Pi.single w x) w' = p w' w x := by
  rw [act_apply, Finset.sum_eq_single w (fun w'' _ h ↦ by rw [Pi.single_eq_of_ne h, map_zero])]
  · rw [Pi.single_eq_same]
  · intro hw; rw [hb.eq_zero hw, LinearMap.zero_apply]

lemma act_mem_suppIcc {u v : ℤ} {x : ∀ w, V w} (hx : x ∈ suppIcc R V u v) :
    act p b x ∈ suppIcc R V (u - b) (v + b) := by
  intro w' hw'
  rw [act_apply]
  refine Finset.sum_eq_zero fun w hw ↦ ?_
  rw [mem_win] at hw
  rw [hx w (by omega), map_zero]

lemma act_act (hb : IsBounded p b) (hp : IsIdem p b) (x : ∀ w, V w) :
    act p b (act p b x) = act p b x := by
  funext w''
  simp only [act_apply, map_sum]
  have h1 : ∀ w' ∈ win w'' b, ∑ w ∈ win w' b, p w'' w' (p w' w (x w)) =
      ∑ w ∈ win w'' (2 * b), p w'' w' (p w' w (x w)) := fun w' hw' ↦
    sum_congr_of_zero fun w hw ↦ by
      have : w ∉ win w' b := by
        rcases hw with hw | hw
        · exact hw
        · rw [mem_win] at hw hw' ⊢; push_cast at hw; omega
      rw [hb.eq_zero this, LinearMap.zero_apply, map_zero]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  have h2 : ∀ w ∈ win w'' (2 * b), ∑ w' ∈ win w'' b, p w'' w' (p w' w (x w)) =
      p w'' w (x w) := fun w _ ↦ by
    rw [← hp w'' w, LinearMap.coe_sum, Finset.sum_apply]
    refine sum_congr_of_zero fun w' hw' ↦ ?_
    rcases hw' with hw' | hw'
    · rw [hb.eq_zero hw', LinearMap.zero_apply]
    · rw [hb.eq_zero' hw', LinearMap.zero_apply, map_zero]
  rw [Finset.sum_congr rfl h2]
  refine sum_congr_of_zero fun w hw ↦ ?_
  have : w ∉ win w'' b := by
    rcases hw with hw | hw
    · rw [mem_win] at hw ⊢; push_cast at hw; omega
    · exact hw
  rw [hb.eq_zero this, LinearMap.zero_apply]

end HSFormal.LTheory.LineModule
