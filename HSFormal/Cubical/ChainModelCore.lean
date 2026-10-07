import HSFormal.Cubical.ChainModelMaps

/-!
# The chain models: `a_g`, `B_{g,h}`, `U_g` on the torus grid (cubical module C6, part 2)

For a mesh `m` (`η = 16/m`) satisfying the validity condition `Good m` (all boxes proper), and
`a, b, c ∈ H`:

* `aT a` (`= a_h` of design §2.4, via `ApproxParams.hom`): carrier radius `RA m · η`
  (`aT_dist`), `a_0 = 1` (`aT_zero`), `aT a z = z` (`aT_z`, (8.4)), `ε a = ε` (`aT_aug`).
* `BT a b c : a_a a_b ≃ a_c` (8.5) for every `c`: carried by the box with **per-coordinate**
  radii `⌈ψ_k/η⌉ + SB + deg·sB` around `ĥ_c(centre)`, `ψ_k = d((ĥ_a ĥ_b x)_k, (ĥ_c x)_k)`
  (`BT_dist`).  Per-coordinate radii keep the `ℓ²` size of the carrier `≤ |ĥ_aĥ_b x - ĥ_c x|₂ +
  √n·o(1)`; a sup-ball of radius `ψ_∞` would have `ℓ²` size `√n ψ_∞`, which for large `n`
  reaches the nonconstant locus of `f` from the cutoff annulus.
* `UT a : a φ a^* ≃ φ` (8.6) on `T^{n-*}`, carried in sup boxes around the cell
  (`UT_dist`, radius `TU m · η`; the radius `≥ 2μ + Ω(η) + 2η` of `cubical-review.md` fix 1).

`Good m` holds for all large `m` (`eventually_good`): the radii in metric units tend to `0`
(`RA`, `SB`, `sB`, `TU`) or to `3D < 8` (`TB`).
-/

noncomputable section

set_option linter.unusedSectionVars false

open Filter Metric Topology Set Matrix
open HSFormal.Cubical HSFormal.Cubical.BasedComplex
open scoped Kronecker

namespace HSFormal.FixedData

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {M : Type*} [TopologicalSpace M] [AddAction ℤ_[p] M]
  (d : FixedData p n M)

/-! ### Grid units -/

/-- `x` in grid units, rounded up. -/
def gu (m : ℕ) (x : ℝ) : ℕ := ⌈x / mesh 16 m⌉₊

theorem mesh_nonneg (m : ℕ) : 0 ≤ mesh 16 m := div_nonneg (by norm_num) (Nat.cast_nonneg _)

theorem le_gu_mul (m : ℕ) [NeZero m] (x : ℝ) : x ≤ gu m x * mesh 16 m := by
  have := Nat.le_ceil (x / mesh 16 m)
  rwa [div_le_iff₀ (mesh_pos 16 m)] at this

theorem gu_mul_le (m : ℕ) {x : ℝ} (hx : 0 ≤ x) : (gu m x : ℝ) * mesh 16 m ≤ x + mesh 16 m := by
  rcases (mesh_nonneg m).eq_or_lt with h | h
  · rw [← h]; simp [hx]
  · have := (Nat.ceil_lt_add_one (div_nonneg hx h.le)).le
    rw [gu]
    calc (⌈x / mesh 16 m⌉₊ : ℝ) * mesh 16 m ≤ (x / mesh 16 m + 1) * mesh 16 m :=
          mul_le_mul_of_nonneg_right this h.le
      _ = x + mesh 16 m := by field_simp

theorem gu_mono (m : ℕ) {x y : ℝ} (h : x ≤ y) : gu m x ≤ gu m y :=
  Nat.ceil_mono (div_le_div_of_nonneg_right h (mesh_nonneg m))

theorem lt_of_mul_mesh_lt {m N : ℕ} [NeZero m] (h : (N : ℝ) * mesh 16 m < 16) : N < m := by
  have : (N : ℝ) * mesh 16 m < m * mesh 16 m := by rwa [mul_comm (m : ℝ), mesh_mul]
  exact_mod_cast lt_of_mul_lt_mul_right this (mesh_nonneg m)

/-! ### The radii, in grid units -/

section Radii

variable [ContinuousVAdd ℤ_[p] M] (m : ℕ)

/-- Radius step of `a_g` per degree: `ω(η/2) + η ≤ sA η`. -/
def sA : ℕ := gu m (d.hatModulus (mesh 16 m / 2)) + 1

/-- Carrier radius of `a_g`: `R₀ + n sA + 1` with `R₀ = 2`. -/
def RA : ℕ := 2 + n * d.sA m + 1

/-- Radius of the box `[-2, 2]ⁿ ⊇ B(0, 3/2)` used for (8.4). -/
def RQ : ℕ := gu m 2

/-- Base radius of `B_{g,h}`. -/
def SB : ℕ := d.RA m + gu m (d.hatModulus (d.RA m * mesh 16 m)) + 1

/-- Radius step of `B_{g,h}` per degree. -/
def sB : ℕ := gu m (2 * d.hatModulus (mesh 16 m / 2) + d.hatModulus (d.hatModulus (mesh 16 m / 2))) + 2

/-- Maximal radius of `B_{g,h}` (`ψ ≤ 3D`). -/
def TB : ℕ := gu m (3 * d.D) + d.SB m + n * d.sB m + 1

/-- Base radius of `U_g` (`≥ 2μ + ω(η/2) + 2η`, review fix 1). -/
def SU : ℕ := 2 * d.RA m + gu m (d.hatModulus (mesh 16 m / 2)) + 2

/-- Maximal radius of `U_g`. -/
def TU : ℕ := d.SU m + 2 * n

/-- **Validity of the mesh**: every box is proper, and `[-2,2]ⁿ` contains the moved region. -/
structure Good : Prop where
  hA : 2 * (2 + n * d.sA m) + 1 < m
  hQ : 3 / 2 + d.D + (d.RA m + 2) * mesh 16 m ≤ 2
  hQm : 2 * RQ m + 1 < m
  hB : 2 * d.TB m + 1 < m
  hU : 2 * d.TU m + 1 < m
  hη : mesh 16 m ≤ 1 / 4

end Radii

/-! ### Eventual validity -/

section Eventually

variable [ContinuousVAdd ℤ_[p] M]

theorem tendsto_mesh_atTop : Tendsto (fun m : ℕ ↦ mesh 16 m) atTop (𝓝 0) :=
  tendsto_mesh 16 tendsto_id

theorem hatModulus_nonneg' (m : ℕ) : 0 ≤ d.hatModulus (mesh 16 m / 2) :=
  d.hatModulus_nonneg (by linarith [mesh_nonneg m])

theorem tendsto_ω₁ : Tendsto (fun m : ℕ ↦ d.hatModulus (mesh 16 m / 2)) atTop (𝓝 0) :=
  d.tendsto_hatModulus (fun m ↦ by linarith [mesh_nonneg m]) (by
    simpa using tendsto_mesh_atTop.div_const 2)

theorem sA_mul_le (m : ℕ) :
    (d.sA m : ℝ) * mesh 16 m ≤ d.hatModulus (mesh 16 m / 2) + 2 * mesh 16 m := by
  have := gu_mul_le m (d.hatModulus_nonneg' m)
  rw [sA]; push_cast; linarith

theorem RA_mul_le (m : ℕ) :
    (d.RA m : ℝ) * mesh 16 m ≤ 3 * mesh 16 m + n * (d.hatModulus (mesh 16 m / 2) + 2 * mesh 16 m) := by
  have := d.sA_mul_le m
  rw [RA]; push_cast
  nlinarith [mesh_nonneg m, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem tendsto_RA : Tendsto (fun m : ℕ ↦ 3 * mesh 16 m + n * (d.hatModulus (mesh 16 m / 2) +
    2 * mesh 16 m)) atTop (𝓝 0) := by
  have h := ((tendsto_mesh_atTop.const_mul 3).add (((d.tendsto_ω₁).add
    (tendsto_mesh_atTop.const_mul 2)).const_mul (n : ℝ)))
  simpa using h

theorem RA_mul_nonneg (m : ℕ) : 0 ≤ (d.RA m : ℝ) * mesh 16 m :=
  mul_nonneg (Nat.cast_nonneg _) (mesh_nonneg m)

theorem tendsto_RA_mul : Tendsto (fun m : ℕ ↦ (d.RA m : ℝ) * mesh 16 m) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds d.tendsto_RA d.RA_mul_nonneg
    d.RA_mul_le

theorem SB_mul_le (m : ℕ) : (d.SB m : ℝ) * mesh 16 m ≤
    d.RA m * mesh 16 m + d.hatModulus (d.RA m * mesh 16 m) + 2 * mesh 16 m := by
  have := gu_mul_le m (d.hatModulus_nonneg (d.RA_mul_nonneg m))
  rw [SB]; push_cast; linarith

theorem sB_mul_le (m : ℕ) : (d.sB m : ℝ) * mesh 16 m ≤
    2 * d.hatModulus (mesh 16 m / 2) + d.hatModulus (d.hatModulus (mesh 16 m / 2)) +
      3 * mesh 16 m := by
  have := gu_mul_le m (x := 2 * d.hatModulus (mesh 16 m / 2) +
    d.hatModulus (d.hatModulus (mesh 16 m / 2))) (by
      have := d.hatModulus_nonneg (d.hatModulus_nonneg' m)
      linarith [d.hatModulus_nonneg' m])
  rw [sB]; push_cast; linarith

theorem tendsto_SB : Tendsto (fun m : ℕ ↦ d.RA m * mesh 16 m + d.hatModulus (d.RA m * mesh 16 m) +
    2 * mesh 16 m) atTop (𝓝 0) := by
  simpa using (d.tendsto_RA_mul.add (d.tendsto_hatModulus d.RA_mul_nonneg d.tendsto_RA_mul)).add
    (tendsto_mesh_atTop.const_mul 2)

theorem tendsto_sB : Tendsto (fun m : ℕ ↦ 2 * d.hatModulus (mesh 16 m / 2) +
    d.hatModulus (d.hatModulus (mesh 16 m / 2)) + 3 * mesh 16 m) atTop (𝓝 0) := by
  simpa using ((d.tendsto_ω₁.const_mul 2).add (d.tendsto_hatModulus d.hatModulus_nonneg'
    d.tendsto_ω₁)).add (tendsto_mesh_atTop.const_mul 3)

theorem SU_mul_le (m : ℕ) : (d.SU m : ℝ) * mesh 16 m ≤
    2 * (d.RA m * mesh 16 m) + d.hatModulus (mesh 16 m / 2) + 3 * mesh 16 m := by
  have := gu_mul_le m (d.hatModulus_nonneg' m)
  rw [SU]; push_cast; linarith

/-- The upper bound of `TB η`, tending to `3D`. -/
def TBbound (m : ℕ) : ℝ :=
  3 * d.D + mesh 16 m + (d.RA m * mesh 16 m + d.hatModulus (d.RA m * mesh 16 m) + 2 * mesh 16 m)
    + n * (2 * d.hatModulus (mesh 16 m / 2) + d.hatModulus (d.hatModulus (mesh 16 m / 2)) +
      3 * mesh 16 m) + mesh 16 m

theorem TB_mul_le (m : ℕ) : (d.TB m : ℝ) * mesh 16 m ≤ d.TBbound m := by
  have h₁ := gu_mul_le m (x := 3 * d.D) (by linarith [d.D_nonneg])
  have h₂ := d.SB_mul_le m
  have h₃ := d.sB_mul_le m
  rw [TB, TBbound]; push_cast
  nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem tendsto_TBbound : Tendsto d.TBbound atTop (𝓝 (3 * d.D)) := by
  have := ((((tendsto_const_nhds (x := 3 * d.D)).add tendsto_mesh_atTop).add d.tendsto_SB).add
    (d.tendsto_sB.const_mul (n : ℝ))).add tendsto_mesh_atTop
  simp only [mul_zero, add_zero] at this
  exact this

/-- The upper bound of `TU η`, tending to `0`. -/
def TUbound (m : ℕ) : ℝ :=
  2 * (d.RA m * mesh 16 m) + d.hatModulus (mesh 16 m / 2) + 3 * mesh 16 m + 2 * n * mesh 16 m

theorem TU_mul_le (m : ℕ) : (d.TU m : ℝ) * mesh 16 m ≤ d.TUbound m := by
  have := d.SU_mul_le m
  rw [TU, TUbound]; push_cast; nlinarith

theorem tendsto_TUbound : Tendsto d.TUbound atTop (𝓝 0) := by
  have := (((d.tendsto_RA_mul.const_mul 2).add d.tendsto_ω₁).add
    (tendsto_mesh_atTop.const_mul 3)).add (tendsto_mesh_atTop.const_mul (2 * (n : ℝ)))
  simp only [mul_zero, add_zero] at this
  exact this

theorem eventually_lt_of_mul {N : ℕ → ℕ} {B : ℕ → ℝ} {c : ℝ} (hc : c < 16)
    (hB : Tendsto B atTop (𝓝 c)) (hN : ∀ m, (N m : ℝ) * mesh 16 m ≤ B m) :
    ∀ᶠ m in atTop, N m < m := by
  filter_upwards [hB.eventually (gt_mem_nhds hc), eventually_gt_atTop 0] with m hm hm0
  haveI : NeZero m := ⟨hm0.ne'⟩
  exact lt_of_mul_mesh_lt ((hN m).trans_lt hm)

/-- **`Good m` for all large `m`.** -/
theorem eventually_good : ∀ᶠ m in atTop, d.Good m := by
  have hD := d.D_lt
  have hD0 := d.D_nonneg
  have hA : ∀ᶠ m in atTop, 2 * (2 + n * d.sA m) + 1 < m := by
    refine eventually_lt_of_mul (c := 0) (by norm_num)
      (B := fun m ↦ 5 * mesh 16 m + 2 * n * (d.hatModulus (mesh 16 m / 2) + 2 * mesh 16 m)) ?_
      fun m ↦ ?_
    · simpa using (tendsto_mesh_atTop.const_mul 5).add
        ((d.tendsto_ω₁.add (tendsto_mesh_atTop.const_mul 2)).const_mul (2 * (n : ℝ)))
    · have := d.sA_mul_le m
      push_cast
      nlinarith [mesh_nonneg m, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hQ : ∀ᶠ m in atTop, 3 / 2 + d.D + (d.RA m + 2) * mesh 16 m ≤ 2 := by
    have : Tendsto (fun m : ℕ ↦ (d.RA m : ℝ) * mesh 16 m + 2 * mesh 16 m) atTop (𝓝 0) := by
      simpa using d.tendsto_RA_mul.add (tendsto_mesh_atTop.const_mul 2)
    filter_upwards [this.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 2 - d.D by linarith))]
      with m hm
    nlinarith
  have hQm : ∀ᶠ m in atTop, 2 * RQ m + 1 < m := by
    refine eventually_lt_of_mul (c := 4) (by norm_num) (B := fun m ↦ 4 + 3 * mesh 16 m) ?_
      fun m ↦ ?_
    · simpa using (tendsto_mesh_atTop.const_mul 3).const_add 4
    · have := gu_mul_le m (x := 2) (by norm_num)
      rw [RQ]; push_cast; nlinarith
  have hB : ∀ᶠ m in atTop, 2 * d.TB m + 1 < m := by
    refine eventually_lt_of_mul (c := 6 * d.D) (by linarith)
      (B := fun m ↦ 2 * d.TBbound m + mesh 16 m) ?_ fun m ↦ ?_
    · simpa [show 2 * (3 * d.D) = 6 * d.D by ring] using
        (d.tendsto_TBbound.const_mul 2).add tendsto_mesh_atTop
    · have := d.TB_mul_le m; push_cast; nlinarith
  have hU : ∀ᶠ m in atTop, 2 * d.TU m + 1 < m := by
    refine eventually_lt_of_mul (c := 0) (by norm_num)
      (B := fun m ↦ 2 * d.TUbound m + mesh 16 m) ?_ fun m ↦ ?_
    · simpa using (d.tendsto_TUbound.const_mul 2).add tendsto_mesh_atTop
    · have := d.TU_mul_le m; push_cast; nlinarith
  have hη : ∀ᶠ m in atTop, mesh 16 m ≤ 1 / 4 :=
    tendsto_mesh_atTop.eventually (ge_mem_nhds (by norm_num))
  filter_upwards [hA, hQ, hQm, hB, hU, hη] with m h₁ h₂ h₃ h₄ h₅ h₆
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩

end Eventually


/-! ### Augmentations of products -/

theorem sum_aug_mul {C D E : BasedComplex} (u : Matrix E.X D.X ℚ) (v : Matrix D.X C.X ℚ)
    (w : D.X → ℚ) (hu : ∀ κ, ∑ ρ, E.aug ρ * u ρ κ = w κ) (σ : C.X) :
    ∑ ρ, E.aug ρ * (u * v) ρ σ = ∑ κ, w κ * v κ σ := by
  simp only [mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun κ _ ↦ ?_
  rw [← hu κ, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-! ### The maps and homotopies on `Tⁿ_m` -/

section Torus

variable [ContinuousVAdd ℤ_[p] M] {m : ℕ} [NeZero m] (hG : d.Good m)

/-- The parameters of `a_a`: `R₀ = 2`, `s = sA`. -/
def approxParams {a : ℤ_[p]} (ha : a ∈ d.H) : ApproxParams 16 m n (d.hatT a) where
  R₀ := 2
  s := d.sA m
  two_le := le_rfl
  hs x y hxy := by
    have h₁ := d.dist_hatT_le_hatModulus ha hxy
    have h₂ := le_gu_mul m (d.hatModulus (mesh 16 m / 2))
    rw [sA]; push_cast; linarith
  hm := hG.hA

/-- **`a_a`**, the cellular approximation of `ĥ_a` on `Tⁿ_m` (design §2.4). -/
def aT {a : ℤ_[p]} (ha : a ∈ d.H) : Hom (torus m n) (torus m n) := (d.approxParams hG ha).hom

/-- The carrier bound `μ = RA η` of `a_a`. -/
theorem aT_dist {a : ℤ_[p]} (ha : a ∈ d.H) {ρ σ : (torus m n).X} (h : (d.aT hG ha).f ρ σ ≠ 0) :
    dist (torus.center 16 m n ρ) (d.hatT a (torus.center 16 m n σ)) ≤ d.RA m * mesh 16 m := by
  have := (d.approxParams hG ha).hom_dist h
  simpa [approxParams, RA] using this

/-- **`a_0 = 1` exactly.** -/
theorem aT_zero (h0 : (0 : ℤ_[p]) ∈ d.H) : d.aT hG h0 = Hom.id (torus m n) :=
  (d.approxParams hG h0).hom_eq_id (d.hatT_zero)

theorem aT_aug {a : ℤ_[p]} (ha : a ∈ d.H) (σ : (torus m n).X) :
    ∑ ρ, (torus m n).aug ρ * (d.aT hG ha).f ρ σ = (torus m n).aug σ :=
  (d.approxParams hG ha).hom_aug σ

theorem norm_coord_le_of_norm_liftVec_le {x : Fin n → AddCircle (16 : ℝ)} {r : ℝ}
    (hx : ‖liftVec 16 x‖ ≤ r) (k : Fin n) : dist (x k) 0 ≤ r := by
  rw [dist_zero_right, ← abs_liftHalf]
  exact (abs_coord_le_norm (liftVec 16 x) k).trans hx

/-- **(8.4) `a_a z = z` exactly**, by the local argument (design F18): off `FixCell`, everything
lies in the box `[-2, 2]ⁿ`, where the `n`-cycle `a z - z` must vanish. -/
theorem aT_z {a : ℤ_[p]} (ha : a ∈ d.H) : (d.aT hG ha).f *ᵥ torus.z m n = torus.z m n := by
  have hη := mesh_pos 16 m
  have hQ := hG.hQ
  have hη4 := hG.hη
  have h2 : (2 : ℝ) ≤ RQ m * mesh 16 m := le_gu_mul m 2
  refine (d.approxParams hG ha).hom_mulVec_cycle (torus.isCycle_z m n)
    (torus.ballBoxContraction 16 m n 0 (fun _ ↦ RQ m) fun _ ↦ hG.hQm) fun σ hσ ↦ ?_
  obtain ⟨x, hx, hne⟩ : ∃ x ∈ (torus.geometry 16 m n).carrier σ, d.hatT a x ≠ x := by
    by_contra h; push_neg at h; exact hσ h
  have hx32 : ‖liftVec 16 x‖ < 3 / 2 := by
    by_contra h; exact hne (d.hatT_of_ge (not_lt.mp h))
  have hcx := torus.dist_center_le_of_mem 16 m n hx
  have hσk : ∀ k, dist (torus.center 16 m n σ k) 0 ≤ mesh 16 m / 2 + 3 / 2 := fun k ↦ by
    have := norm_coord_le_of_norm_liftVec_le hx32.le k
    have := dist_le_pi_dist x (torus.center 16 m n σ) k
    linarith [dist_triangle (torus.center 16 m n σ k) (x k) 0, dist_comm (x k)
      (torus.center 16 m n σ k)]
  refine ⟨torus.ballBox_of_dist (fun _ ↦ hG.hQm) fun k ↦ ?_, fun ρ hρ ↦
    torus.ballBox_of_dist (fun _ ↦ hG.hQm) fun k ↦ ?_⟩
  · simp only [Pi.zero_apply] at hσk ⊢
    linarith [hσk k]
  · have h₁ := dist_le_pi_dist _ _ k |>.trans (d.aT_dist hG ha hρ)
    have h₂ := dist_le_pi_dist _ _ k |>.trans (d.dist_hatT_le ha (torus.center 16 m n σ))
    simp only [Pi.zero_apply] at hσk ⊢
    linarith [hσk k, dist_triangle (torus.center 16 m n ρ k)
      (d.hatT a (torus.center 16 m n σ) k) 0, dist_triangle (d.hatT a (torus.center 16 m n σ) k)
      (torus.center 16 m n σ k) 0]

/-! #### `B` -/

/-- The coordinate track lengths `ψ_k(x) = d((ĥ_a ĥ_b x)_k, (ĥ_c x)_k)`. -/
def psi (a b c : ℤ_[p]) (x : Fin n → AddCircle (16 : ℝ)) (k : Fin n) : ℝ :=
  dist (d.hatT a (d.hatT b x) k) (d.hatT c x k)

theorem psi_nonneg (a b c : ℤ_[p]) (x : Fin n → AddCircle (16 : ℝ)) (k : Fin n) :
    0 ≤ d.psi a b c x k := dist_nonneg

theorem dist_hatT_hatT_le {a b c : ℤ_[p]} (ha : a ∈ d.H) (hb : b ∈ d.H) (hc : c ∈ d.H)
    (x : Fin n → AddCircle (16 : ℝ)) : dist (d.hatT a (d.hatT b x)) (d.hatT c x) ≤ 3 * d.D := by
  have := dist_triangle4 (d.hatT a (d.hatT b x)) (d.hatT b x) x (d.hatT c x)
  linarith [d.dist_hatT_le ha (d.hatT b x), d.dist_hatT_le hb x, d.dist_hatT_le hc x,
    dist_comm x (d.hatT c x)]

theorem psi_le {a b c : ℤ_[p]} (ha : a ∈ d.H) (hb : b ∈ d.H) (hc : c ∈ d.H)
    (x : Fin n → AddCircle (16 : ℝ)) (k : Fin n) : d.psi a b c x k ≤ 3 * d.D :=
  (dist_le_pi_dist _ _ k).trans (d.dist_hatT_hatT_le ha hb hc x)

/-- The per-coordinate radii of the box of `B_{a,b;c}` at a cell. -/
def rB (a b c : ℤ_[p]) (σ : (torus m n).X) : Fin n → ℕ :=
  fun k ↦ gu m (d.psi a b c (torus.center 16 m n σ) k) + d.SB m + (torus m n).deg σ * d.sB m

include hG in
theorem rB_lt {a b c : ℤ_[p]} (ha : a ∈ d.H) (hb : b ∈ d.H) (hc : c ∈ d.H) (σ : (torus m n).X)
    (k : Fin n) : 2 * d.rB a b c σ k + 1 < m := by
  have h₁ := gu_mono m (d.psi_le ha hb hc (torus.center 16 m n σ) k)
  have h₂ : (torus m n).deg σ * d.sB m ≤ n * d.sB m := Nat.mul_le_mul_right _ (torus.dimLE m n σ)
  have := hG.hB
  simp only [rB, TB] at *
  omega

theorem rB_nest {a b c : ℤ_[p]} (ha : a ∈ d.H) (hb : b ∈ d.H) (hc : c ∈ d.H)
    {τ σ : (torus m n).X} (h : (torus m n).d τ σ ≠ 0) (k : Fin n) :
    d.rB a b c τ k ≤ d.rB a b c σ k ∧
      dist (d.hatT c (torus.center 16 m n τ) k) (d.hatT c (torus.center 16 m n σ) k) +
        d.rB a b c τ k * mesh 16 m + mesh 16 m ≤ d.rB a b c σ k * mesh 16 m := by
  have hη := mesh_pos 16 m
  have hdeg := (torus m n).d_deg τ σ h
  set x := torus.center 16 m n τ
  set y := torus.center 16 m n σ
  have hxy : dist x y ≤ mesh 16 m / 2 := torus.dist_center_le_of_d h
  set ω₁ := d.hatModulus (mesh 16 m / 2)
  have hb₁ : dist (d.hatT b x) (d.hatT b y) ≤ ω₁ := d.dist_hatT_le_hatModulus hb hxy
  have hc₁ : dist (d.hatT c x) (d.hatT c y) ≤ ω₁ := d.dist_hatT_le_hatModulus hc hxy
  have ha₂ : dist (d.hatT a (d.hatT b x)) (d.hatT a (d.hatT b y)) ≤ d.hatModulus ω₁ :=
    d.dist_hatT_le_hatModulus ha hb₁
  have hψ : d.psi a b c x k ≤ d.psi a b c y k + d.hatModulus ω₁ + ω₁ := by
    have e₁ := dist_le_pi_dist _ _ k |>.trans ha₂
    have e₂ := dist_le_pi_dist _ _ k |>.trans hc₁
    have := dist_triangle4 (d.hatT a (d.hatT b x) k) (d.hatT a (d.hatT b y) k) (d.hatT c y k)
      (d.hatT c x k)
    simp only [psi]
    linarith [dist_comm (d.hatT c y k) (d.hatT c x k)]
  have hsB : 2 * ω₁ + d.hatModulus ω₁ + 2 * mesh 16 m ≤ d.sB m * mesh 16 m := by
    have := le_gu_mul m (2 * ω₁ + d.hatModulus ω₁)
    rw [sB]; push_cast; linarith
  have hg₁ := gu_mul_le m (d.psi_nonneg a b c x k)
  have hg₂ := le_gu_mul m (d.psi a b c y k)
  have hck := dist_le_pi_dist _ _ k |>.trans hc₁
  have key : dist (d.hatT c x k) (d.hatT c y k) + d.rB a b c τ k * mesh 16 m + mesh 16 m ≤
      d.rB a b c σ k * mesh 16 m := by
    simp only [rB, hdeg]
    push_cast
    nlinarith
  refine ⟨?_, key⟩
  have : (d.rB a b c τ k : ℝ) * mesh 16 m < d.rB a b c σ k * mesh 16 m := by
    linarith [dist_nonneg (x := d.hatT c x k) (y := d.hatT c y k)]
  exact_mod_cast (lt_of_mul_lt_mul_right this hη.le).le

/-- **`B_{a,b;c} : a_a a_b ≃ a_c`** (8.5), an exact homotopy carried by the boxes `rB`. -/
def BT {a b c : ℤ_[p]} (ha : a ∈ d.H) (hb : b ∈ d.H) (hc : c ∈ d.H) :
    Htpy ((d.aT hG ha).comp (d.aT hG hb)) (d.aT hG hc) :=
  boxHtpy _ _ (fun σ ↦ d.hatT c (torus.center 16 m n σ)) (d.rB a b c) (d.rB_lt hG ha hb hc)
    (fun τ σ h k ↦ d.rB_nest ha hb hc h k)
    (fun ρ σ h ↦ by
      have hη := mesh_pos 16 m
      obtain ⟨κ, h₁, h₂⟩ := exists_mul_apply_ne_zero h
      have e₁ := d.aT_dist hG hb h₂
      have e₂ := d.aT_dist hG ha h₁
      have e₃ := d.dist_hatT_le_hatModulus ha e₁
      refine torus.ballBox_of_dist (d.rB_lt hG ha hb hc σ) fun k ↦ ?_
      have hSB : d.RA m * mesh 16 m + d.hatModulus (d.RA m * mesh 16 m) + mesh 16 m ≤
          d.SB m * mesh 16 m := by
        have := le_gu_mul m (d.hatModulus (d.RA m * mesh 16 m))
        rw [SB]; push_cast; linarith
      have hg := le_gu_mul m (d.psi a b c (torus.center 16 m n σ) k)
      have hdist := dist_le_pi_dist (torus.center 16 m n ρ)
        (d.hatT a (d.hatT b (torus.center 16 m n σ))) k
      have := dist_triangle (torus.center 16 m n ρ k) (d.hatT a (torus.center 16 m n κ) k)
        (d.hatT a (d.hatT b (torus.center 16 m n σ)) k)
      have := dist_triangle (torus.center 16 m n ρ k)
        (d.hatT a (d.hatT b (torus.center 16 m n σ)) k) (d.hatT c (torus.center 16 m n σ) k)
      have hρκ := dist_le_pi_dist _ _ k |>.trans e₂
      have hκσ := dist_le_pi_dist _ _ k |>.trans e₃
      have hψ : dist (d.hatT a (d.hatT b (torus.center 16 m n σ)) k)
          (d.hatT c (torus.center 16 m n σ) k) = d.psi a b c (torus.center 16 m n σ) k := rfl
      simp only [rB]
      push_cast
      have : (0 : ℝ) ≤ (torus m n).deg σ * d.sB m * mesh 16 m := by positivity
      nlinarith)
    (fun ρ σ h ↦ by
      have hη := mesh_pos 16 m
      have e : ∀ k, dist (torus.center 16 m n ρ k) (d.hatT c (torus.center 16 m n σ) k) ≤
          d.RA m * mesh 16 m := fun k ↦ (dist_le_pi_dist _ _ k).trans (d.aT_dist hG hc h)
      refine torus.ballBox_of_dist (d.rB_lt hG ha hb hc σ) fun k ↦ ?_
      have hg := (Nat.cast_nonneg (gu m (d.psi a b c (torus.center 16 m n σ) k)) : (0 : ℝ) ≤ _)
      have : (d.RA m + 1 : ℝ) ≤ d.SB m := by rw [SB]; push_cast; linarith [(Nat.cast_nonneg
        (gu m (d.hatModulus (d.RA m * mesh 16 m))) : (0 : ℝ) ≤ _)]
      have := e k
      simp only [rB]
      push_cast
      have : (0 : ℝ) ≤ (torus m n).deg σ * d.sB m * mesh 16 m := by positivity
      nlinarith)
    (fun σ _ ↦ by
      rw [Hom.comp_f, sum_aug_mul _ _ _ (d.aT_aug hG ha), d.aT_aug hG hc]
      exact d.aT_aug hG hb σ)

/-- The carrier bound of `B`: within `ψ_k + (SB + n sB + 2) η` of `ĥ_c(centre σ)`, per
coordinate. -/
theorem BT_dist {a b c : ℤ_[p]} (ha : a ∈ d.H) (hb : b ∈ d.H) (hc : c ∈ d.H)
    {ρ σ : (torus m n).X} (h : (d.BT hG ha hb hc).h ρ σ ≠ 0) (k : Fin n) :
    dist (torus.center 16 m n ρ k) (d.hatT c (torus.center 16 m n σ) k) ≤
      d.psi a b c (torus.center 16 m n σ) k + (d.SB m + n * d.sB m + 2) * mesh 16 m := by
  have hη := mesh_pos 16 m
  unfold BT at h
  have h₁ := boxHtpy_dist h k
  have h₂ := gu_mul_le m (d.psi_nonneg a b c (torus.center 16 m n σ) k)
  have h₃ : ((torus m n).deg σ : ℝ) * d.sB m ≤ n * d.sB m := by
    have := torus.dimLE m n σ
    gcongr
  simp only [rB] at h₁
  push_cast at h₁
  nlinarith


/-! #### `U` -/

omit [ContinuousVAdd ℤ_[p] M] in
theorem phiT_dist {ρ σ : (torus m n).X} (h : (torus.duality m n).hom.f ρ σ ≠ 0) :
    dist (torus.center 16 m n ρ) (torus.center 16 m n σ) ≤ mesh 16 m / 2 := by
  have := (edist_le_prop h).trans (torus.propLE 16 m n).hom
  rwa [edist_dist, ENNReal.ofReal_le_ofReal_iff (by linarith [mesh_pos 16 m])] at this

/-- The radii of the boxes of `U`, decreasing with the degree (the source is `T^{n-*}`). -/
def rU (σ : (torus m n).X) : Fin n → ℕ := fun _ ↦ d.SU m + (n - (torus m n).deg σ) * 2

include hG in
theorem rU_lt (σ : (torus m n).X) (k : Fin n) : 2 * d.rU σ k + 1 < m := by
  have := hG.hU
  simp only [rU, TU] at *
  omega

/-- The map `a φ a^*` of (8.6). -/
def aphia {a : ℤ_[p]} (ha : a ∈ d.H) :
    Hom ((torus m n).dual n (torus.dimLE m n)) (torus m n) :=
  ((d.aT hG ha).comp (torus.duality m n).hom).comp
    ((d.aT hG ha).dual n (torus.dimLE m n) (torus.dimLE m n))

theorem aphia_dist {a : ℤ_[p]} (ha : a ∈ d.H) {ρ σ : (torus m n).X}
    (h : (d.aphia hG ha).f ρ σ ≠ 0) :
    dist (torus.center 16 m n ρ) (torus.center 16 m n σ) ≤
      2 * (d.RA m * mesh 16 m) + d.hatModulus (mesh 16 m / 2) := by
  simp only [aphia, Hom.comp_f, Hom.dual_f] at h
  obtain ⟨κ, h₁, h₂⟩ := exists_mul_apply_ne_zero h
  obtain ⟨l₀, h₃, h₄⟩ := exists_mul_apply_ne_zero h₁
  rw [transpose_apply] at h₂
  have e₁ := d.aT_dist hG ha h₃
  have e₂ := phiT_dist h₄
  have e₃ := d.dist_hatT_le_hatModulus ha e₂
  have e₄ := d.aT_dist hG ha h₂
  linarith [dist_triangle4 (torus.center 16 m n ρ) (d.hatT a (torus.center 16 m n l₀))
    (d.hatT a (torus.center 16 m n κ)) (torus.center 16 m n σ),
    dist_comm (d.hatT a (torus.center 16 m n κ)) (torus.center 16 m n σ)]

/-- **`U_a : a φ a^* ≃ φ`** (8.6), an exact homotopy carried in boxes around the cells; the
degree-`0` augmentations agree by `ε φ = ⟨-, z⟩` and (8.4). -/
def UT {a : ℤ_[p]} (ha : a ∈ d.H) : Htpy (d.aphia hG ha) (torus.duality m n).hom :=
  boxHtpy (C := (torus m n).dual n (torus.dimLE m n)) _ _ (fun σ ↦ torus.center 16 m n σ) d.rU
    (d.rU_lt hG)
    (fun τ σ h k ↦ by
      have hη := mesh_pos 16 m
      rw [dual_d_apply] at h
      have h' : (torus m n).d σ τ ≠ 0 := right_ne_zero_of_mul (right_ne_zero_of_mul h)
      have hdeg := (torus m n).d_deg σ τ h'
      have hτ := torus.dimLE m n τ
      have hd := torus.dist_center_le_of_d (L := 16) h'
      have hk := dist_le_pi_dist _ _ k |>.trans hd
      have e : d.rU σ k = d.rU τ k + 2 := by simp only [rU]; omega
      refine ⟨by omega, ?_⟩
      rw [e]; push_cast
      linarith [dist_comm (torus.center 16 m n τ k) (torus.center 16 m n σ k)])
    (fun ρ σ h ↦ by
      have hη := mesh_pos 16 m
      refine torus.ballBox_of_dist (d.rU_lt hG σ) fun k ↦ ?_
      have e := dist_le_pi_dist _ _ k |>.trans (d.aphia_dist hG ha h)
      have hSU := d.SU_mul_le m
      have : (d.SU m : ℝ) ≤ d.rU σ k := by simp only [rU]; push_cast; linarith [(Nat.cast_nonneg
        ((n - (torus m n).deg σ) * 2) : (0 : ℝ) ≤ _)]
      have hSU' : 2 * (d.RA m * mesh 16 m) + d.hatModulus (mesh 16 m / 2) + 2 * mesh 16 m ≤
          d.SU m * mesh 16 m := by
        have := le_gu_mul m (d.hatModulus (mesh 16 m / 2))
        rw [SU]; push_cast; linarith
      nlinarith)
    (fun ρ σ h ↦ by
      have hη := mesh_pos 16 m
      refine torus.ballBox_of_dist (d.rU_lt hG σ) fun k ↦ ?_
      have e := dist_le_pi_dist _ _ k |>.trans (phiT_dist h)
      have : (2 : ℝ) ≤ d.rU σ k := by simp only [rU, SU]; push_cast; linarith [(Nat.cast_nonneg
        ((n - (torus m n).deg σ) * 2) : (0 : ℝ) ≤ _), (Nat.cast_nonneg (2 * d.RA m) : (0 : ℝ) ≤ _),
        (Nat.cast_nonneg (gu m (d.hatModulus (mesh 16 m / 2))) : (0 : ℝ) ≤ _)]
      nlinarith)
    (fun σ _ ↦ by
      rw [torus.aug_duality]
      simp only [aphia, Hom.comp_f, Hom.dual_f]
      rw [sum_aug_mul _ _ (torus.z m n) fun κ ↦ by
        rw [sum_aug_mul _ _ _ (d.aT_aug hG ha), torus.aug_duality]]
      have := congrFun (d.aT_z hG ha) σ
      simp only [mulVec, dotProduct] at this
      rw [← this]
      exact Finset.sum_congr rfl fun κ _ ↦ by rw [transpose_apply, mul_comm])

/-- The carrier bound of `U`: within `(TU + 1) η` of the cell. -/
theorem UT_dist {a : ℤ_[p]} (ha : a ∈ d.H) {ρ σ : (torus m n).X} (h : (d.UT hG ha).h ρ σ ≠ 0) :
    dist (torus.center 16 m n ρ) (torus.center 16 m n σ) ≤ (d.TU m + 1) * mesh 16 m := by
  have hη := mesh_pos 16 m
  unfold UT at h
  refine (dist_pi_le_iff (by positivity)).mpr fun k ↦ ?_
  have h₁ := boxHtpy_dist h k
  have : (d.rU σ k : ℝ) ≤ d.TU m := by
    simp only [rU, TU]; push_cast
    have : ((n - (torus m n).deg σ : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le _ _
    linarith
  nlinarith

end Torus

/-! ### The chain models `W = Tⁿ_m ⊗ CPcell` -/

theorem koszul_comm_kronecker_one {C D : BasedComplex} {N : ℕ} {u : Matrix C.X C.X ℚ}
    (hu : ∀ ρ σ, u ρ σ ≠ 0 → C.deg ρ = C.deg σ) :
    koszul C D N * (u ⊗ₖ (1 : Matrix D.X D.X ℚ)) = (u ⊗ₖ 1) * koszul C D N := by
  ext ⟨a, b⟩ ⟨c, e⟩
  rw [koszul, diagonal_mul, mul_diagonal, kronecker_apply]
  by_cases h : u a c = 0
  · simp [h]
  · by_cases hbe : b = e
    · subst hbe; simp only [hu a c h]; ring
    · simp [one_apply_ne hbe]

theorem transpose_kronecker_one {α β : Type*} [DecidableEq β] (u : Matrix α α ℚ) :
    (u ⊗ₖ (1 : Matrix β β ℚ))ᵀ = uᵀ ⊗ₖ (1 : Matrix β β ℚ) := by
  rw [← transpose_one (n := β), kroneckerMap_transpose, transpose_one]

section W

variable [ContinuousVAdd ℤ_[p] M] {m : ℕ} [NeZero m] (hG : d.Good m)

/-- **`a_a` on `W = Tⁿ ⊗ CPcell`**: `a ⊗ 1` (design §2.1). -/
def aW {a : ℤ_[p]} (ha : a ∈ d.H) : Hom (torusCP m n) (torusCP m n) :=
  (d.aT hG ha).tensor (Hom.id CPcell)

theorem aW_congr {a b : ℤ_[p]} (hab : a = b) (ha : a ∈ d.H) (hb : b ∈ d.H) :
    d.aW hG ha = d.aW hG hb := by subst hab; rfl

/-- `a_0 = 1` exactly. -/
theorem aW_zero (h0 : (0 : ℤ_[p]) ∈ d.H) : d.aW hG h0 = Hom.id (torusCP m n) := by
  rw [aW, aT_zero, Hom.tensor_id]

/-- (8.4) on `W`: `a z = z` exactly. -/
theorem aW_z {a : ℤ_[p]} (ha : a ∈ d.H) :
    (d.aW hG ha).f *ᵥ torusCP.z m n = torusCP.z m n := by
  change ((d.aT hG ha).f ⊗ₖ (1 : Matrix CPcell.X CPcell.X ℚ)) *ᵥ
    (fun q ↦ torus.z m n q.1 * CPcell.z q.2) = fun q ↦ torus.z m n q.1 * CPcell.z q.2
  rw [kronecker_mulVec_tmul, d.aT_z hG ha, one_mulVec]

theorem aW_ne_zero {a : ℤ_[p]} (ha : a ∈ d.H) {ρ σ : (torusCP m n).X}
    (h : (d.aW hG ha).f ρ σ ≠ 0) : (d.aT hG ha).f ρ.1 σ.1 ≠ 0 :=
  left_ne_zero_of_mul (by simpa [aW, kronecker_apply] using h)

/-- **(8.5) on `W`**: `B ⊗ 1 : a_a a_b ≃ a_c`. -/
def BW {a b c : ℤ_[p]} (ha : a ∈ d.H) (hb : b ∈ d.H) (hc : c ∈ d.H) :
    Htpy ((d.aW hG ha).comp (d.aW hG hb)) (d.aW hG hc) :=
  ((d.BT hG ha hb hc).tensorRight (Hom.id CPcell)).congr
    (by rw [aW, aW, ← Hom.tensor_comp, Hom.id_comp]) rfl

theorem BW_h {a b c : ℤ_[p]} (ha : a ∈ d.H) (hb : b ∈ d.H) (hc : c ∈ d.H) :
    (d.BW hG ha hb hc).h = (d.BT hG ha hb hc).h ⊗ₖ (1 : Matrix CPcell.X CPcell.X ℚ) :=
  (Htpy.congr_h _ _ _).trans (Htpy.tensorRight_h _ _)

theorem BW_ne_zero {a b c : ℤ_[p]} (ha : a ∈ d.H) (hb : b ∈ d.H) (hc : c ∈ d.H)
    {ρ σ : (torusCP m n).X} (h : (d.BW hG ha hb hc).h ρ σ ≠ 0) :
    (d.BT hG ha hb hc).h ρ.1 σ.1 ≠ 0 :=
  left_ne_zero_of_mul (by simpa [BW_h, kronecker_apply] using h)

/-- The map `a φ_W a^*` of (8.6) on `W`. -/
def aphiaW {a : ℤ_[p]} (ha : a ∈ d.H) :
    Hom ((torusCP m n).dual (n + 4) (torusCP.dimLE m n)) (torusCP m n) :=
  ((d.aW hG ha).comp (torusCP.duality m n).hom).comp
    ((d.aW hG ha).dual (n + 4) (torusCP.dimLE m n) (torusCP.dimLE m n))

omit [ContinuousVAdd ℤ_[p] M] in
theorem torusCP_duality_hom : (torusCP.duality m n).hom =
    ((torus.duality m n).hom.tensor CPcell.duality.hom).comp
      (dualTensor (torus.dimLE m n) CPcell.dimLE) := rfl

theorem aphiaW_eq {a : ℤ_[p]} (ha : a ∈ d.H) :
    ((d.aphia hG ha).tensor CPcell.duality.hom).comp (dualTensor (torus.dimLE m n) CPcell.dimLE) =
      d.aphiaW hG ha := by
  refine Hom.ext ?_
  have hu : ∀ ρ σ, (d.aT hG ha).fᵀ ρ σ ≠ 0 → (torus m n).deg ρ = (torus m n).deg σ :=
    fun ρ σ h ↦ by have := (d.aT hG ha).deg0 σ ρ h; omega
  simp only [aphiaW, aphia, aW, torusCP_duality_hom, Hom.comp_f, Hom.tensor_f, Hom.dual_f,
    Hom.id_f, dualTensor]
  rw [transpose_kronecker_one]
  simp only [Matrix.mul_assoc]
  rw [koszul_comm_kronecker_one hu]
  simp only [← Matrix.mul_assoc]
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]

/-- **(8.6) on `W`**: `U ⊗ φ_CP : a φ_W a^* ≃ φ_W`, exactly. -/
def UW {a : ℤ_[p]} (ha : a ∈ d.H) : Htpy (d.aphiaW hG ha) (torusCP.duality m n).hom :=
  (((d.UT hG ha).tensorRight CPcell.duality.hom).compRight
    (dualTensor (torus.dimLE m n) CPcell.dimLE)).congr (d.aphiaW_eq hG ha) rfl

theorem UW_h {a : ℤ_[p]} (ha : a ∈ d.H) :
    (d.UW hG ha).h = ((d.UT hG ha).h ⊗ₖ CPcell.duality.hom.f) * koszul (torus m n) CPcell 4 := by
  exact (Htpy.congr_h _ _ _).trans (Htpy.compRight_h _ _)

theorem UW_ne_zero {a : ℤ_[p]} (ha : a ∈ d.H) {ρ σ : (torusCP m n).X}
    (h : (d.UW hG ha).h ρ σ ≠ 0) : (d.UT hG ha).h ρ.1 σ.1 ≠ 0 := by
  rw [UW_h, koszul, mul_diagonal, kronecker_apply] at h
  exact left_ne_zero_of_mul (left_ne_zero_of_mul h)

end W

end HSFormal.FixedData
