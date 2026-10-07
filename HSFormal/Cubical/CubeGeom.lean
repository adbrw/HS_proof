import HSFormal.Cubical.PinchReduction
import HSFormal.Cubical.PinchFlag
import HSFormal.Cubical.PinchControl

/-!
# The box of the cube cut and the labels of its faces (cubical module C8, geometry)

For the mesh `η = 16/M` of the torus `(ℝ/16ℤ)ⁿ` (`M = germMesh i = i + 2`) and the radius
`r = r_Q ∈ (0, 1]` of the cut cube `Q = [-r, r]ⁿ` (chart coordinates), the box of the cut is
`∏ [a, a + m + 1]` with `a = -s`, `s = ⌈r/η⌉`, `m + 1 = min (2s) (M - 1)` (`= 2s` for `M ≥ 3`):
its chart coordinates run from `-sη` to `(m + 1 - s)η`, within `η` of `±r`.

* `CubeGeom.ivVal`: the chart coordinate of a cell of the box side `I_{m+1}` (vertex `v ↦ (v-s)η`,
  edge `e ↦ (e + ½ - s)η`).
* `CubeGeom.cubeCoords n j x`: the chart point of a cell `x` of the `j`-dimensional top face of the
  box (the first `n - j` coordinates at the top vertex, the remaining ones those of `x`), and
  `CubeGeom.cubeLabel = chartV ∘ cubeCoords`: the labels of the face complexes `∂I^j ⊗ CPcell` of
  the cut flag.
* `CubeGeom.clampV`: the coordinatewise projection onto `[-r, r]`.
-/

noncomputable section

namespace HSFormal.Cubical.BasedComplex.CubeGeom

open Filter Metric Topology HSFormal.RoundSphere
open scoped ENNReal

variable (r : ℝ) (M : ℕ)

/-- `s = ⌈r/η⌉`, the half side of the box in mesh steps. -/
def sSteps : ℕ := ⌈r / mesh 16 M⌉₊

/-- `m` with `m + 1 = min (2s) (M - 1)` the number of edges of a side of the box. -/
def mBox : ℕ := min (2 * sSteps r M) (M - 1) - 1

variable {r M}

theorem one_le_sSteps (hr : 0 < r) (hM : M ≠ 0) : 1 ≤ sSteps r M := by
  have : 0 < mesh 16 M := by
    haveI : NeZero M := ⟨hM⟩
    exact mesh_pos 16 M
  exact Nat.one_le_iff_ne_zero.mpr fun h ↦ by
    rw [sSteps, Nat.ceil_eq_zero] at h
    exact absurd h (not_le.mpr (div_pos hr this))

theorem mBox_succ (hr : 0 < r) (hM : 2 ≤ M) :
    mBox r M + 1 = min (2 * sSteps r M) (M - 1) := by
  have := one_le_sSteps hr (by omega : M ≠ 0)
  unfold mBox
  omega

theorem mBox_lt (hr : 0 < r) (hM : 2 ≤ M) : mBox r M + 1 < M := by
  rw [mBox_succ hr hM]; omega

variable (r M)

/-- The chart coordinate of a cell of a side `I_{m+1}` of the box. -/
def ivVal : (interval (mBox r M + 1)).X → ℝ
  | .inl v => ((v : ℝ) - sSteps r M) * mesh 16 M
  | .inr e => ((e : ℝ) + 1 / 2 - sSteps r M) * mesh 16 M

/-- The chart point of a cell of the `j`-dimensional top face of the box in `ℝⁿ`: the first
`n - j` coordinates at the top vertex, the others those of the cell. -/
def cubeCoords (n j : ℕ) (x : (cube (mBox r M + 1) j).X) : Fin n → ℝ := fun t ↦
  if h : n - j ≤ t.val then ivVal r M (coord j x ⟨t.val - (n - j), by have := t.isLt; omega⟩)
  else ivVal r M (.inl (Fin.last _))

/-- The torus point `(ℝ/16ℤ)ⁿ` of a cell of the `j`-dimensional top face of the box. -/
def facePt (n j : ℕ) (x : (cube (mBox r M + 1) j).X) : Fin n → AddCircle (16 : ℝ) :=
  fun t ↦ (cubeCoords r M n j x t : AddCircle (16 : ℝ))

/-- The label of a cell of the `j`-dimensional top face of the box: the germ collapse of its
torus point (the chart point `chartV (cubeCoords …)` for fine meshes, `cubeLabel_eq_chartV`). -/
def cubeLabel (n j : ℕ) (x : (cube (mBox r M + 1) j).X) : RoundSphere n :=
  germCollapse n (facePt r M n j x)

/-- The coordinatewise projection onto `[-r, r]`. -/
def clampV {n : ℕ} (w : Fin n → ℝ) : Fin n → ℝ := fun t ↦ max (-r) (min r (w t))

/-- The first vertex `a = -s` of a side of the box. -/
def aBox [NeZero M] : Fin M := -(Fin.ofNat M (sSteps r M))

variable {r M}

/-! ### Helper lemmas for the geometry of the cut -/

theorem prodLabel_eq_coord {E : Type*} : (n : ℕ) → {C : Fin n → BasedComplex} →
    (a : ∀ i, (C i).X → E) → (σ : (prodComplex n C).X) → (k : Fin n) →
    prodLabel n a σ k = a k (coord n σ k)
  | 0, _, _, _, k => k.elim0
  | n + 1, _, a, σ, k => by
    induction k using Fin.cases with
    | zero => rfl
    | succ k => exact prodLabel_eq_coord n (fun i ↦ a i.succ) σ.2 k

theorem fin_val_add_modEq {N : ℕ} (x y : Fin N) :
    (((x + y : Fin N) : ℕ) : ℤ) ≡ (x : ℤ) + (y : ℤ) [ZMOD N] := by
  rw [Fin.val_add]; push_cast; exact Int.mod_modEq _ _

theorem val_modEq_aBox [NeZero M] (u : Fin M) :
    ((u : ℕ) : ℤ) ≡ (((u - aBox r M : Fin M) : ℕ) : ℤ) - sSteps r M [ZMOD M] := by
  have h1 := fin_val_add_modEq (u - aBox r M) (aBox r M)
  rw [sub_add_cancel] at h1
  have h0 : aBox r M + Fin.ofNat M (sSteps r M) = 0 := neg_add_cancel _
  have h2 := fin_val_add_modEq (aBox r M) (Fin.ofNat M (sSteps r M))
  rw [h0, Fin.val_ofNat] at h2
  have h3 : (((sSteps r M % M : ℕ) : ℤ)) + M * ((sSteps r M / M : ℕ) : ℤ) = sSteps r M := by
    exact_mod_cast Nat.mod_add_div (sSteps r M) M
  rw [Int.modEq_iff_dvd] at h1 h2 ⊢
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  refine ⟨k1 - k2 - ((sSteps r M / M : ℕ) : ℤ), ?_⟩
  simp only [Fin.val_zero, Nat.cast_zero, sub_zero] at hk2
  linear_combination hk1 - hk2 + h3

theorem coe_add_mul_period (z : ℝ) (k : ℤ) :
    (((z + k * 16 : ℝ)) : AddCircle (16 : ℝ)) = (z : AddCircle (16 : ℝ)) := by
  have : (((k * 16 : ℝ)) : AddCircle (16 : ℝ)) = 0 :=
    (AddCircle.coe_eq_zero_iff (16 : ℝ)).mpr ⟨k, by simp [zsmul_eq_mul]⟩
  rw [AddCircle.coe_add, this, add_zero]

theorem coe_center_eq [NeZero M] (u : Fin M) (c : ℝ) :
    ((mesh 16 M * ((u : ℝ) + c) : ℝ) : AddCircle (16 : ℝ)) =
      (((((u - aBox r M : Fin M) : ℕ) : ℝ) - sSteps r M + c) * mesh 16 M : ℝ) := by
  obtain ⟨k, hk⟩ := (val_modEq_aBox (r := r) u).dvd
  have hk' : ((((u - aBox r M : Fin M) : ℕ) : ℝ) - sSteps r M - (u : ℝ)) = M * k := by
    exact_mod_cast hk
  have hmM := mesh_mul 16 M
  have : (((((u - aBox r M : Fin M) : ℕ) : ℝ) - sSteps r M + c) * mesh 16 M) =
      mesh 16 M * ((u : ℝ) + c) + k * 16 := by
    linear_combination (mesh 16 M) * hk' + (k : ℝ) * hmM
  rw [this, coe_add_mul_period]

theorem norm_coe_of_abs_le {t : ℝ} (h : |t| ≤ 8) : ‖(t : AddCircle (16 : ℝ))‖ = |t| :=
  (AddCircle.norm_coe_eq_abs_iff 16 (by norm_num)).mpr (by norm_num; linarith)

theorem le_norm_coe {a t : ℝ} (ha : 0 ≤ a) (h1 : a ≤ t) (h2 : t ≤ 16 - a) :
    a ≤ ‖(t : AddCircle (16 : ℝ))‖ := by
  rcases le_total t 8 with h | h
  · rw [norm_coe_of_abs_le (by rw [abs_le]; constructor <;> linarith), abs_of_nonneg (by linarith)]
    exact h1
  · have : ((t : ℝ) : AddCircle (16 : ℝ)) = ((t - 16 : ℝ) : AddCircle (16 : ℝ)) := by
      rw [← AddCircle.coe_add_period (16 : ℝ) (t - 16), sub_add_cancel]
    rw [this, norm_coe_of_abs_le (by rw [abs_le]; constructor <;> linarith),
      abs_of_nonpos (by linarith)]
    linarith

theorem liftHalf_coe {t : ℝ} (h1 : -8 ≤ t) (h2 : t < 8) :
    liftHalf 16 (t : AddCircle (16 : ℝ)) = t := by
  unfold liftHalf
  rw [AddCircle.equivIco_coe_eq (show t ∈ Set.Ico (-((16 : ℝ) / 2)) (-(16 / 2) + 16) by
    constructor <;> linarith)]

/-- For fine meshes (`M ≥ 32`) the box side is `2s` and `sη ∈ [r, r + η)`. -/
theorem eventually_good (hr : 0 < r) (hr1 : r ≤ 1) :
    ∀ᶠ i in atTop, mBox r (germMesh i) + 1 = 2 * sSteps r (germMesh i) ∧
      r ≤ sSteps r (germMesh i) * mesh 16 (germMesh i) ∧
      sSteps r (germMesh i) * mesh 16 (germMesh i) < r + mesh 16 (germMesh i) ∧
      0 < mesh 16 (germMesh i) ∧ mesh 16 (germMesh i) ≤ 1 / 2 := by
  filter_upwards [eventually_ge_atTop 30] with i hi
  have hM' : 32 ≤ germMesh i := by rw [germMesh]; omega
  have hM : (32 : ℝ) ≤ germMesh i := by exact_mod_cast hM'
  have hη : mesh 16 (germMesh i) = 16 / germMesh i := rfl
  have hηpos : 0 < mesh 16 (germMesh i) := mesh_pos 16 _
  have hηle : mesh 16 (germMesh i) ≤ 1 / 2 := by
    rw [hη, div_le_iff₀ (by linarith)]; linarith
  have hrη : 0 ≤ r / mesh 16 (germMesh i) := (div_pos hr hηpos).le
  have hs1 : r / mesh 16 (germMesh i) ≤ sSteps r (germMesh i) := Nat.le_ceil _
  have hs2 : (sSteps r (germMesh i) : ℝ) < r / mesh 16 (germMesh i) + 1 := Nat.ceil_lt_add_one hrη
  have hsη1 : r ≤ sSteps r (germMesh i) * mesh 16 (germMesh i) := by
    rwa [div_le_iff₀ hηpos] at hs1
  have hsη2 : (sSteps r (germMesh i) : ℝ) * mesh 16 (germMesh i) < r + mesh 16 (germMesh i) := by
    have := mul_lt_mul_of_pos_right hs2 hηpos
    rwa [add_mul, div_mul_cancel₀ _ hηpos.ne', one_mul] at this
  have hrM : r / mesh 16 (germMesh i) = r * germMesh i / 16 := by
    rw [hη]; field_simp
  have h2s : 2 * sSteps r (germMesh i) + 1 < germMesh i := by
    have : (2 * sSteps r (germMesh i) + 1 : ℝ) < germMesh i := by
      rw [hrM] at hs2
      have : r * germMesh i ≤ germMesh i := by nlinarith
      linarith
    exact_mod_cast this
  refine ⟨?_, hsη1, hsη2, hηpos, hηle⟩
  rw [mBox_succ hr (by omega)]
  omega

theorem cubeCoords_of_lt {n j : ℕ} (x : (cube (mBox r M + 1) j).X) (t : Fin n)
    (h : (t : ℕ) < n - j) : cubeCoords r M n j x t = ivVal r M (.inl (Fin.last _)) := by
  unfold cubeCoords; rw [dif_neg (by omega)]

theorem cubeCoords_of_eq {n j : ℕ} (x : (cube (mBox r M + 1) j).X) (t : Fin n) (u : Fin j)
    (h : (t : ℕ) = u + (n - j)) : cubeCoords r M n j x t = ivVal r M (coord j x u) := by
  unfold cubeCoords; rw [dif_pos (by omega)]
  congr 2
  exact Fin.ext (by simp only; omega)

theorem ivVal_last (hm : mBox r M + 1 = 2 * sSteps r M) :
    ivVal r M (.inl (Fin.last _)) = sSteps r M * mesh 16 M := by
  have : ((mBox r M + 1 : ℕ) : ℝ) = 2 * sSteps r M := by exact_mod_cast hm
  show (((Fin.last (mBox r M + 1) : ℕ) : ℝ) - _) * _ = _
  rw [Fin.val_last, this]; ring

theorem ivVal_zero : ivVal r M (.inl 0) = -(sSteps r M * mesh 16 M) := by
  show ((((0 : Fin _) : ℕ) : ℝ) - _) * _ = _
  simp

theorem abs_ivVal_le (hm : mBox r M + 1 ≤ 2 * sSteps r M) (hη : 0 < mesh 16 M)
    (y : (interval (mBox r M + 1)).X) : |ivVal r M y| ≤ sSteps r M * mesh 16 M := by
  rcases y with v | e
  · have hv : (v : ℕ) ≤ 2 * sSteps r M := by have := v.isLt; omega
    have hv' : ((v : ℕ) : ℝ) ≤ 2 * sSteps r M := by exact_mod_cast hv
    show |(((v : ℕ) : ℝ) - sSteps r M) * mesh 16 M| ≤ _
    rw [abs_mul, abs_of_pos hη]
    refine mul_le_mul_of_nonneg_right ?_ hη.le
    rw [abs_le]; constructor <;> linarith [(Nat.cast_nonneg (v : ℕ) : (0 : ℝ) ≤ _)]
  · have he : (e : ℕ) + 1 ≤ 2 * sSteps r M := by have := e.isLt; omega
    have he' : ((e : ℕ) : ℝ) + 1 ≤ 2 * sSteps r M := by exact_mod_cast he
    show |(((e : ℕ) : ℝ) + 1 / 2 - sSteps r M) * mesh 16 M| ≤ _
    rw [abs_mul, abs_of_pos hη]
    refine mul_le_mul_of_nonneg_right ?_ hη.le
    rw [abs_le]; constructor <;> linarith [(Nat.cast_nonneg (e : ℕ) : (0 : ℝ) ≤ _)]

theorem abs_cubeCoords_le (hm : mBox r M + 1 ≤ 2 * sSteps r M) (hη : 0 < mesh 16 M) {n j : ℕ}
    (x : (cube (mBox r M + 1) j).X) (t : Fin n) :
    |cubeCoords r M n j x t| ≤ sSteps r M * mesh 16 M := by
  unfold cubeCoords; split_ifs <;> exact abs_ivVal_le hm hη _

theorem clampV_apply {n : ℕ} (w : Fin n → ℝ) (t : Fin n) :
    clampV r w t = max (-r) (min r (w t)) := rfl

theorem clamp_eq_of_le {a : ℝ} (hr : 0 ≤ r) (h : r ≤ a) : max (-r) (min r a) = r := by
  rw [min_eq_left h, max_eq_right (by linarith)]

theorem clamp_eq_of_le_neg {a : ℝ} (hr : 0 ≤ r) (h : a ≤ -r) : max (-r) (min r a) = -r := by
  rw [min_eq_right (by linarith), max_eq_left h]

theorem abs_clamp_le (hr : 0 ≤ r) (a : ℝ) : |max (-r) (min r a)| ≤ r := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem norm_clampV_le (hr : 0 ≤ r) {n : ℕ} (w : Fin n → ℝ) : ‖clampV r w‖ ≤ r :=
  (pi_norm_le_iff_of_nonneg hr).mpr fun t ↦ by
    rw [Real.norm_eq_abs, clampV_apply]; exact abs_clamp_le hr _

theorem abs_sub_clamp_le {a η : ℝ} (hr : 0 ≤ r) (hη : 0 ≤ η) (h : |a| ≤ r + η) :
    |a - max (-r) (min r a)| ≤ η := by
  rw [abs_le] at h ⊢
  rcases le_total a r with h1 | h1
  · rw [min_eq_right h1]
    rcases le_total (-r) a with h2 | h2
    · rw [max_eq_right h2]; constructor <;> linarith
    · rw [max_eq_left h2]; constructor <;> linarith
  · rw [min_eq_left h1, max_eq_right (by linarith)]; constructor <;> linarith

/-- (G5) for a fixed fine mesh. -/
theorem clampV_mem_face_of (hr : 0 < r) (hm : mBox r M + 1 = 2 * sSteps r M)
    (hs : r ≤ sSteps r M * mesh 16 M) {n j : ℕ} (x : (cube (mBox r M + 1) j).X) :
    clampV r (cubeCoords r M n j x) ∈ cubeFaceV r (n - j) :=
  ⟨norm_clampV_le hr.le _, fun t ht ↦ by
    rw [clampV_apply, cubeCoords_of_lt x t ht, ivVal_last hm]; exact clamp_eq_of_le hr.le hs⟩

theorem clamp_ivVal_end (hr : 0 < r) (hm : mBox r M + 1 = 2 * sSteps r M)
    (hs : r ≤ sSteps r M * mesh 16 M) {y : (interval (mBox r M + 1)).X}
    (hy : interval.IsVEnd _ y) : |max (-r) (min r (ivVal r M y))| = r := by
  rcases hy with rfl | rfl
  · rw [ivVal_zero, clamp_eq_of_le_neg hr.le (by linarith), abs_neg, abs_of_pos hr]
  · rw [ivVal_last hm, clamp_eq_of_le hr.le hs, abs_of_pos hr]

theorem cubeCoords_topEmb {n j : ℕ} (hj : j + 1 ≤ n) (x : (cube (mBox r M + 1) j).X) :
    cubeCoords r M n (j + 1) ((cube.topEmb (mBox r M + 1)).toFun x) = cubeCoords r M n j x := by
  funext t
  have ht := t.isLt
  by_cases h1 : n - j ≤ (t : ℕ)
  · have hu : (t : ℕ) - (n - j) < j := by omega
    rw [cubeCoords_of_eq _ t (⟨t - (n - j), hu⟩ : Fin j).succ (by simp only [Fin.val_succ]; omega),
      cubeCoords_of_eq x t ⟨t - (n - j), hu⟩ (by simp only; omega)]
    rfl
  · rw [cubeCoords_of_lt x t (by omega)]
    by_cases h2 : (t : ℕ) < n - (j + 1)
    · rw [cubeCoords_of_lt _ t h2]
    · rw [cubeCoords_of_eq _ t 0 (by simp only [Fin.val_zero]; omega)]; rfl

/-- (G3) for a fixed fine mesh. -/
theorem le_norm_of_offBox [NeZero M] (hm : mBox r M + 1 = 2 * sSteps r M)
    (hs : r ≤ sSteps r M * mesh 16 M) (hs8 : sSteps r M * mesh 16 M ≤ 8) (hη : 0 < mesh 16 M)
    {n : ℕ} (σ : (torus M n).X)
    (hσ : torus.OffBox M n (fun _ ↦ aBox r M) (fun _ ↦ mBox r M + 1) σ) (v : Fin n → ℝ)
    (hv : chartV v = germCollapse n (torus.center 16 M n σ)) : r ≤ ‖v‖ := by
  have hMη := mesh_mul 16 M
  obtain ⟨t, ht⟩ := hσ
  have hsη0 : 0 ≤ (sSteps r M : ℝ) * mesh 16 M := by positivity
  have key : sSteps r M * mesh 16 M ≤ ‖torus.center 16 M n σ t‖ := by
    rw [torus.center, prodLabel_eq_coord]
    generalize coord n σ t = y at ht ⊢
    rcases y with u | e
    · change ((u - aBox r M : Fin M) : ℕ) = 0 ∨ mBox r M + 1 ≤ ((u - aBox r M : Fin M) : ℕ) at ht
      have hc := coe_center_eq (r := r) u 0
      rw [add_zero, add_zero] at hc
      show _ ≤ ‖((mesh 16 M * (u : ℝ) : ℝ) : AddCircle (16 : ℝ))‖
      rw [hc]
      have hk := (u - aBox r M).isLt
      rcases ht with h | h
      · have habs : |-((sSteps r M : ℝ) * mesh 16 M)| = sSteps r M * mesh 16 M := by
          rw [abs_neg, abs_of_nonneg hsη0]
        rw [h, Nat.cast_zero, zero_sub, neg_mul, norm_coe_of_abs_le (by rw [habs]; exact hs8), habs]
      · have h1 : (2 * sSteps r M : ℝ) ≤ ((u - aBox r M : Fin M) : ℕ) := by exact_mod_cast hm ▸ h
        have h2 : (((u - aBox r M : Fin M) : ℕ) : ℝ) + 1 ≤ M := by exact_mod_cast hk
        apply le_norm_coe hsη0
        · nlinarith
        · nlinarith
    · change mBox r M + 1 ≤ ((e - aBox r M : Fin M) : ℕ) at ht
      have hc := coe_center_eq (r := r) e (1 / 2)
      show _ ≤ ‖((mesh 16 M * ((e : ℝ) + 1 / 2) : ℝ) : AddCircle (16 : ℝ))‖
      rw [hc]
      have hk := (e - aBox r M).isLt
      have h1 : (2 * sSteps r M : ℝ) ≤ ((e - aBox r M : Fin M) : ℕ) := by exact_mod_cast hm ▸ ht
      have h2 : (((e - aBox r M : Fin M) : ℕ) : ℝ) + 1 ≤ M := by exact_mod_cast hk
      apply le_norm_coe hsη0
      · nlinarith
      · nlinarith
  calc r ≤ sSteps r M * mesh 16 M := hs
    _ ≤ ‖torus.center 16 M n σ t‖ := key
    _ ≤ ‖torus.center 16 M n σ‖ := norm_le_pi_norm _ t
    _ ≤ ‖v‖ := by simpa using norm_le_of_germCollapse_eq (w := WithLp.toLp 2 v) hv.symm

/-- (G2') for a fixed fine mesh. -/
theorem cubeLabel_eq_chartV_of (hm : mBox r M + 1 ≤ 2 * sSteps r M) (hη : 0 < mesh 16 M)
    (hs : sSteps r M * mesh 16 M ≤ 2) {n j : ℕ} (x : (cube (mBox r M + 1) j).X) :
    cubeLabel r M n j x = chartV (cubeCoords r M n j x) := by
  have hc : ∀ t, |cubeCoords r M n j x t| ≤ 2 := fun t ↦ (abs_cubeCoords_le hm hη x t).trans hs
  have hl : liftVec 16 (facePt r M n j x) = WithLp.toLp 2 (cubeCoords r M n j x) := by
    unfold liftVec facePt
    congr 1
    funext t
    have := abs_le.mp (hc t)
    exact liftHalf_coe (by linarith) (by linarith)
  unfold cubeLabel
  rw [germCollapse_of_norm_le, hl]
  · rfl
  · refine (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun t ↦ ?_
    unfold facePt
    rw [norm_coe_of_abs_le (by linarith [hc t])]
    linarith [hc t]

/-! ### Statements of the geometry of the cut (to be proved) -/

/-- **(G1)** Labels are compatible with the top-face embedding. -/
theorem cubeLabel_topEmb {n j : ℕ} (hj : j + 1 ≤ n) (x : (cube (mBox r M + 1) j).X) :
    cubeLabel r M n (j + 1) ((cube.topEmb (mBox r M + 1)).toFun x) = cubeLabel r M n j x := by
  unfold cubeLabel facePt
  rw [cubeCoords_topEmb hj]

/-- **(G2)** The torus centres of the box cells are the face points: the arc labels are the
chart coordinates mod `16` (`a = -s`, `M η = 16`). -/
theorem prodLabel_arcLabel_eq (hr : 0 < r) (hM : 2 ≤ M) [NeZero M] {n j : ℕ} (hj : j ≤ n)
    (x : (cube (mBox r M + 1) j).X) (t : Fin j) :
    prodLabel j (fun _ ↦ interval.arcLabel 16 M (mBox r M) (mBox_lt hr hM) (aBox r M)) x t =
      facePt r M n j x ⟨t + (n - j), by omega⟩ := by
  rw [prodLabel_eq_coord]
  unfold facePt
  rw [cubeCoords_of_eq x _ t rfl]
  generalize coord j x t = y
  rcases y with v | e
  · have hc := coe_center_eq (r := r) (aBox r M + Fin.castLE (mBox_lt hr hM) v) 0
    rw [add_sub_cancel_left, add_zero, add_zero, Fin.val_castLE] at hc
    exact hc
  · have hc := coe_center_eq (r := r) (aBox r M + Fin.castLE (mBox_lt hr hM).le e) (1 / 2)
    rw [add_sub_cancel_left, Fin.val_castLE] at hc
    refine hc.trans ?_
    show _ = (((((e : ℕ) : ℝ) + 1 / 2 - sSteps r M) * mesh 16 M : ℝ) : AddCircle (16 : ℝ))
    congr 2; ring

/-- **(G2')** For fine meshes the face labels are the chart points of the face coordinates (the
box lies in the cube `‖·‖_∞ ≤ 4` on which `germCollapse` is the chart lift). -/
theorem cubeLabel_eq_chartV (hr : 0 < r) (hr1 : r ≤ 1) (n j : ℕ) :
    ∀ᶠ i in atTop, ∀ x : (cube (mBox r (germMesh i) + 1) j).X,
      cubeLabel r (germMesh i) n j x = chartV (cubeCoords r (germMesh i) n j x) := by
  filter_upwards [eventually_good hr hr1] with i ⟨hm, _, hs2, hη, hη2⟩ x
  exact cubeLabel_eq_chartV_of hm.le hη (by linarith) x

/-- **(G3)** The cells off the open box are labelled outside the open cube `‖v‖_∞ < r`. -/
theorem germCollapse_center_offBox (hr : 0 < r) (hr1 : r ≤ 1) (n : ℕ) :
    ∀ᶠ i in atTop, ∀ σ : (torus (germMesh i) n).X,
      torus.OffBox (germMesh i) n (fun _ ↦ aBox r (germMesh i)) (fun _ ↦ mBox r (germMesh i) + 1)
        σ → ∀ v, chartV v = germCollapse n (torus.center 16 (germMesh i) n σ) → r ≤ ‖v‖ := by
  filter_upwards [eventually_good hr hr1] with i ⟨hm, hs1, hs2, hη, hη2⟩ σ hσ v hv
  exact le_norm_of_offBox hm hs1 (by linarith) hη σ hσ v hv

/-- **(G4)** Face labels approach a set `T` of chart points when the clamped coordinates of the
cells lie in `T` (the coordinates are within one mesh of their clamps, and `chartV` is uniformly
continuous on bounded sets). -/
theorem tendsto_cubeLabel (hr : 0 < r) (hr1 : r ≤ 1) (n j : ℕ)
    (P : ∀ i, (cube (mBox r (germMesh i) + 1) j).X → Prop) (T : Set (Fin n → ℝ))
    (hT : ∀ᶠ i in atTop, ∀ x, P i x → clampV r (cubeCoords r (germMesh i) n j x) ∈ T) :
    Tendsto (fun i ↦ ⨆ (x) (_ : P i x), infEDist (cubeLabel r (germMesh i) n j x) (chartV '' T))
      atTop (𝓝 0) := by
  have hK : IsCompact (closedBall (0 : Fin n → ℝ) 2) := isCompact_closedBall 0 2
  have hU := EMetric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous continuous_chartV.continuousOn)
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨δ, hδ, hU⟩ := hU ε hε
  have hηδ := (tendsto_ofReal_mesh 16 tendsto_germMesh).eventually_lt_const hδ
  filter_upwards [hT, eventually_good hr hr1, hηδ] with i hTi ⟨hm, hs1, hs2, hη, hη2⟩ hηi
  refine iSup₂_le fun x hx ↦ ?_
  rw [cubeLabel_eq_chartV_of hm.le hη (by linarith) x]
  have hc := abs_cubeCoords_le (n := n) hm.le hη x
  refine (infEDist_le_edist_of_mem (Set.mem_image_of_mem chartV (hTi x hx))).trans
    (hU ?_ ?_ ?_).le
  · rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun t ↦ ?_
    rw [Real.norm_eq_abs]; linarith [hc t]
  · rw [mem_closedBall_zero_iff]; linarith [norm_clampV_le hr.le (cubeCoords r (germMesh i) n j x)]
  · refine lt_of_le_of_lt ?_ hηi
    rw [edist_dist]
    refine ENNReal.ofReal_le_ofReal ((dist_pi_le_iff hη.le).mpr fun t ↦ ?_)
    rw [Real.dist_eq, clampV_apply]
    exact abs_sub_clamp_le hr.le hη.le ((hc t).trans hs2.le)

/-- **(G5)** Clamped face coordinates lie on the face `Φ_j` (first `n - j` coordinates `= r`). -/
theorem clampV_mem_face (hr : 0 < r) (hr1 : r ≤ 1) {n j : ℕ} (hj : j ≤ n) :
    ∀ᶠ i in atTop, ∀ x : (cube (mBox r (germMesh i) + 1) j).X,
      clampV r (cubeCoords r (germMesh i) n j x) ∈ cubeFaceV r (n - j) := by
  filter_upwards [eventually_good hr hr1] with i ⟨hm, hs1, _⟩ x
  exact clampV_mem_face_of hr hm hs1 x

/-- **(G6)** Boundary cells of the face clamp into its boundary `∂Φ_j`. -/
theorem clampV_mem_bdry (hr : 0 < r) (hr1 : r ≤ 1) {n j : ℕ} (hj : j ≤ n) :
    ∀ᶠ i in atTop, ∀ x : (cube (mBox r (germMesh i) + 1) j).X, cube.Bdry _ x →
      clampV r (cubeCoords r (germMesh i) n j x) ∈ cubeBdryV r (n - j) := by
  filter_upwards [eventually_good hr hr1] with i ⟨hm, hs1, _⟩ x hx
  refine ⟨clampV_mem_face_of hr hm hs1 x, ?_⟩
  obtain ⟨u, hu⟩ := hx
  have := u.isLt
  refine ⟨⟨u + (n - j), by omega⟩, by simp, ?_⟩
  rw [clampV_apply, cubeCoords_of_eq x _ u rfl]
  exact clamp_ivVal_end hr hm hs1 hu

/-- **(G7)** In `∂Φ_{k+1}`, the cells of the rest clamp into `cubeRestV`, those of the top face
into the next face. -/
theorem clampV_mem_rest (hr : 0 < r) (hr1 : r ≤ 1) {n k : ℕ} (hk : k + 1 ≤ n) :
    ∀ᶠ i in atTop, ∀ x : (cube (mBox r (germMesh i) + 1) (k + 1)).X, cube.Rest _ x →
      clampV r (cubeCoords r (germMesh i) n (k + 1) x) ∈ cubeRestV r (n - (k + 1)) := by
  filter_upwards [eventually_good hr hr1] with i ⟨hm, hs1, _⟩
  intro (x : (cube (mBox r (germMesh i) + 1) (k + 1)).X) hx
  refine ⟨clampV_mem_face_of hr hm hs1 x, ?_⟩
  rcases hx with h | ⟨u, hu⟩
  · left
    refine ⟨⟨n - (k + 1), by omega⟩, rfl, ?_⟩
    rw [clampV_apply, cubeCoords_of_eq x _ 0 (by simp)]
    rw [show coord (k + 1) x 0 = x.1 from rfl, h, ivVal_zero,
      clamp_eq_of_le_neg hr.le (by linarith)]
  · right
    have := u.isLt
    refine ⟨⟨u.succ + (n - (k + 1)), by simp only [Fin.val_succ]; omega⟩,
      by simp only [Fin.val_succ]; omega, ?_⟩
    rw [clampV_apply, cubeCoords_of_eq x _ u.succ rfl,
      show coord (k + 1) x u.succ = coord k x.2 u from rfl]
    exact clamp_ivVal_end hr hm hs1 hu

theorem clampV_mem_top (hr : 0 < r) (hr1 : r ≤ 1) {n k : ℕ} (hk : k + 1 ≤ n) :
    ∀ᶠ i in atTop, ∀ x : (cube (mBox r (germMesh i) + 1) (k + 1)).X, cube.Top _ x →
      clampV r (cubeCoords r (germMesh i) n (k + 1) x) ∈ cubeFaceV r (n - k) := by
  filter_upwards [eventually_good hr hr1] with i ⟨hm, hs1, _⟩
  intro (x : (cube (mBox r (germMesh i) + 1) (k + 1)).X) hx
  refine ⟨norm_clampV_le hr.le _, fun t ht ↦ ?_⟩
  rw [clampV_apply]
  by_cases h : (t : ℕ) < n - (k + 1)
  · rw [cubeCoords_of_lt x t h, ivVal_last hm, clamp_eq_of_le hr.le hs1]
  · rw [cubeCoords_of_eq x t 0 (by simp only [Fin.val_zero]; omega),
      show coord (k + 1) x 0 = x.1 from rfl, show x.1 = _ from hx, ivVal_last hm,
      clamp_eq_of_le hr.le hs1]

/-- **(G8)** The end points of the last edge `Φ₁`. -/
theorem clampV_mem_end (hr : 0 < r) (hr1 : r ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    ∀ᶠ i in atTop,
      clampV r (cubeCoords r (germMesh i) n 1 (.inl (Fin.last _), ())) ∈ cubeEndV r r ∧
      clampV r (cubeCoords r (germMesh i) n 1 (.inl 0, ())) ∈ cubeEndV r (-r) := by
  filter_upwards [eventually_good hr hr1] with i ⟨hm, hs1, _⟩
  refine ⟨⟨clampV_mem_face_of hr hm hs1 _, ⟨n - 1, by omega⟩, rfl, ?_⟩,
    ⟨clampV_mem_face_of hr hm hs1 _, ⟨n - 1, by omega⟩, rfl, ?_⟩⟩
  · rw [clampV_apply, cubeCoords_of_eq _ _ 0 (by simp only [Fin.val_zero]; omega)]
    show max (-r) (min r (ivVal r (germMesh i) (.inl (Fin.last _)))) = r
    rw [ivVal_last hm]
    exact clamp_eq_of_le hr.le hs1
  · rw [clampV_apply, cubeCoords_of_eq _ _ 0 (by simp only [Fin.val_zero]; omega)]
    show max (-r) (min r (ivVal r (germMesh i) (.inl 0))) = -r
    rw [ivVal_zero]
    exact clamp_eq_of_le_neg hr.le (by linarith)

end HSFormal.Cubical.BasedComplex.CubeGeom
