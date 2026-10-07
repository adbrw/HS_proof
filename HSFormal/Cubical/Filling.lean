import HSFormal.Cubical.GridFlag

/-!
# Filling: cellular approximations and carrier homotopies on the torus grid (cubical module C5)

Design §2.4 (`blueprint/simplicial-design.md`, row C5) on `Tⁿ_m = C_m^{⊗n}`, located on
`E = (ℝ/Lℤ)ⁿ` with the sup metric (`torus.geometry`), mesh `η = L/m`.

* **Boxes.** `torus.ballBox y R`: the grid box with per-coordinate radii `R k` (in grid units)
  around the nearest vertex `torus.near y` of a point `y`.  Membership and nesting are metric:
  `torus.ballBox_of_dist` (centres within `R k η - η`), `torus.dist_of_ballBox` (centres within
  `R k η + η`), `torus.ballBox_mono` (`dist (y' k) (y k) + R' k η + η ≤ R k η`).  The only
  arithmetic input is the exact vertex distance on `C_m` (`circle.dist_inl`,
  `circle.ball_inl_iff`).  Boxes are contracted by `torus.inBoxContraction`.
* **`a_g`** (`approxHom`): for any map `g : E → E` with `dist x y ≤ η/2 → dist (g x) (g y) + η ≤ s η`,
  the chain map that is the identity on the face-closed set `FixCell g` of cells on whose closed
  carrier `g = id`, sends the other vertices to a nearest vertex of `g (centre)`, and fills every
  other cell in `ballBox (g (centre σ)) (R₀ + deg σ · s)`.  Hence `approxHom_eq_id` (`a_1 = 1`
  exactly when `g = id`), the carrier bound `approxHom_dist`, `approxHom_aug` (`ε a = ε`) and
  `approxHom_mulVec_cycle` (`a z = z` for top cycles when the non-fixed cells and their images
  lie in one proper box: the local proof of (8.4), design F18).
* **Carrier homotopies** (`boxHtpy`): chain maps into `Tⁿ` from any based complex, carried in
  nested boxes with equal vertex augmentations, are homotopic by an exact homotopy carried in
  the same boxes (`carrierHtpy`); used for `B_{g,h}` (8.5) and `U_g` (8.6) in `ChainModel`.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace HSFormal.Cubical

open Matrix

namespace BasedComplex

/-! ### Exact vertex distances on `C_m` -/

section CircleArith

variable (L : ℝ) [Fact (0 < L)] (m : ℕ) [NeZero m]

omit [Fact (0 < L)] in
theorem coe_mesh_sub (a b : Fin m) :
    ((mesh L m * a - mesh L m * b : ℝ) : AddCircle L) =
      ((mesh L m * ((a - b : Fin m) : ℕ) : ℝ)) := by
  have hL : mesh L m * m = L := mesh_mul L m
  rw [Fin.val_sub]
  rcases le_or_gt (b : ℕ) a with h | h
  · rw [show m - (b : ℕ) + a = (a - b : ℕ) + m by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega), Nat.cast_sub h]
    ring_nf
  · rw [Nat.mod_eq_of_lt (by omega), Nat.cast_add, Nat.cast_sub (by omega)]
    rw [show mesh L m * ((m : ℝ) - b + a) = (mesh L m * a - mesh L m * b) + L by
      linear_combination hL]
    rw [AddCircle.coe_add_period]

theorem norm_coe_mesh_mul (j : ℕ) (hj : j < m) :
    ‖((mesh L m * j : ℝ) : AddCircle L)‖ = mesh L m * ((min j (m - j) : ℕ) : ℝ) := by
  have hL : mesh L m * m = L := mesh_mul L m
  have hη := mesh_pos L m
  have hL0 : (0 : ℝ) < L := Fact.out
  rcases le_or_gt (2 * j) m with h | h
  · rw [min_eq_left (by omega)]
    have : (2 * j : ℝ) ≤ m := by exact_mod_cast h
    have h1 : |mesh L m * j| ≤ |L| / 2 := by
      rw [abs_of_nonneg (by positivity), abs_of_pos hL0]; nlinarith
    rw [(AddCircle.norm_coe_eq_abs_iff L hL0.ne').mpr h1, abs_of_nonneg (by positivity)]
  · rw [min_eq_right (by omega)]
    have : (m : ℝ) < 2 * j := by exact_mod_cast h
    have hjm : (j : ℝ) < m := by exact_mod_cast hj
    set k : ℝ := ((m - j : ℕ) : ℝ) with hk
    have hk' : k = m - j := by rw [hk, Nat.cast_sub hj.le]
    have e : ((mesh L m * j : ℝ) : AddCircle L) = ((-(mesh L m * k) : ℝ) : AddCircle L) := by
      have : mesh L m * j = -(mesh L m * k) + L := by rw [hk']; linear_combination hL
      rw [this, AddCircle.coe_add_period]
    have hk0 : 0 ≤ k := by positivity
    have h1 : |-(mesh L m * k)| ≤ |L| / 2 := by
      rw [abs_neg, abs_of_nonneg (by positivity), abs_of_pos hL0, hk']; nlinarith
    rw [e, (AddCircle.norm_coe_eq_abs_iff L hL0.ne').mpr h1, abs_neg,
      abs_of_nonneg (by positivity)]

/-- The exact distance of two vertices of `C_m` on `ℝ/Lℤ`. -/
theorem circle.dist_inl (a b : Fin m) :
    dist (circle.center L m (.inl a)) (circle.center L m (.inl b)) =
      mesh L m * ((min ((a - b : Fin m) : ℕ) (m - ((a - b : Fin m) : ℕ)) : ℕ) : ℝ) := by
  simp only [circle.center]
  rw [dist_eq_norm, ← AddCircle.coe_sub, coe_mesh_sub, norm_coe_mesh_mul L m _ (Fin.isLt _)]

/-- The closed arc of radius `R` (grid units) around the vertex `b` of `C_m`. -/
def circle.ball (b : Fin m) (R : ℕ) : (circle m).X → Prop :=
  circle.InArc m (b - Fin.ofNat m R) (2 * R)

/-- **Vertices of an arc**, metrically: `v ∈ [b - R, b + R]` iff `d(v, b) ≤ R η`. -/
theorem circle.ball_inl_iff {b v : Fin m} {R : ℕ} (hR : 2 * R < m) :
    circle.ball m b R (.inl v) ↔
      dist (circle.center L m (.inl v)) (circle.center L m (.inl b)) ≤ R * mesh L m := by
  have hη := mesh_pos L m
  change ((v - (b - Fin.ofNat m R) : Fin m) : ℕ) ≤ 2 * R ↔ _
  rw [show v - (b - Fin.ofNat m R) = (v - b) + Fin.ofNat m R by abel, Fin.val_add,
    Fin.val_ofNat, Nat.mod_eq_of_lt (show R < m by omega), circle.dist_inl, mul_comm (R : ℝ),
    mul_le_mul_iff_right₀ hη, Nat.cast_le]
  have hj := (v - b : Fin m).isLt
  generalize ((v - b : Fin m) : ℕ) = j at hj ⊢
  rcases lt_or_ge (j + R) m with h | h
  · rw [Nat.mod_eq_of_lt h]; omega
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]; omega

/-- An edge lies in an arc iff both endpoints do. -/
theorem circle.ball_inr_iff {b e : Fin m} {R : ℕ} (hR : 2 * R + 1 < m) :
    circle.ball m b R (.inr e) ↔ circle.ball m b R (.inl e) ∧ circle.ball m b R (.inl (e + 1)) := by
  change ((e - _ : Fin m) : ℕ) < 2 * R ↔ ((e - _ : Fin m) : ℕ) ≤ 2 * R ∧
    ((e + 1 - _ : Fin m) : ℕ) ≤ 2 * R
  rw [circle.sub_succ, fin_val_add_one]
  split_ifs with h <;> omega

theorem circle.dist_inr_inl_le (e : Fin m) :
    dist (circle.center L m (.inr e)) (circle.center L m (.inl e)) ≤ mesh L m / 2 := by
  have := circle.edist_center_le L m (σ := .inr e) (τ := .inl e) (.inl rfl)
  rwa [edist_dist, ENNReal.ofReal_le_ofReal_iff (by linarith [mesh_pos L m])] at this

theorem circle.dist_inr_inl_succ_le (e : Fin m) :
    dist (circle.center L m (.inr e)) (circle.center L m (.inl (e + 1))) ≤ mesh L m / 2 := by
  have := circle.edist_center_le L m (σ := .inr e) (τ := .inl (e + 1)) (.inr rfl)
  rwa [edist_dist, ENNReal.ofReal_le_ofReal_iff (by linarith [mesh_pos L m])] at this

/-- Membership from the centre distance. -/
theorem circle.ball_of_dist {b : Fin m} {R : ℕ} (hR : 2 * R + 1 < m) {σ : (circle m).X}
    (h : dist (circle.center L m σ) (circle.center L m (.inl b)) + mesh L m / 2 ≤ R * mesh L m) :
    circle.ball m b R σ := by
  have hη := mesh_pos L m
  rcases σ with v | e
  · exact (circle.ball_inl_iff L m (by omega)).mpr (by linarith)
  · refine (circle.ball_inr_iff m hR).mpr ⟨(circle.ball_inl_iff L m (by omega)).mpr ?_,
      (circle.ball_inl_iff L m (by omega)).mpr ?_⟩
    · have := dist_triangle (circle.center L m (.inl e)) (circle.center L m (.inr e))
        (circle.center L m (.inl b))
      linarith [circle.dist_inr_inl_le L m e, dist_comm (circle.center L m (.inl e))
        (circle.center L m (.inr e))]
    · have := dist_triangle (circle.center L m (.inl (e + 1))) (circle.center L m (.inr e))
        (circle.center L m (.inl b))
      linarith [circle.dist_inr_inl_succ_le L m e, dist_comm (circle.center L m (.inl (e + 1)))
        (circle.center L m (.inr e))]

/-- The centre distance of a cell of an arc. -/
theorem circle.dist_of_ball {b : Fin m} {R : ℕ} (hR : 2 * R + 1 < m) {σ : (circle m).X}
    (h : circle.ball m b R σ) :
    dist (circle.center L m σ) (circle.center L m (.inl b)) ≤ R * mesh L m + mesh L m / 2 := by
  have hη := mesh_pos L m
  rcases σ with v | e
  · linarith [(circle.ball_inl_iff L m (by omega)).mp h]
  · have h₁ := (circle.ball_inl_iff L m (by omega)).mp ((circle.ball_inr_iff m hR).mp h).1
    linarith [dist_triangle (circle.center L m (.inr e)) (circle.center L m (.inl e))
      (circle.center L m (.inl b)), circle.dist_inr_inl_le L m e]

/-- **Nesting of arcs.** -/
theorem circle.ball_mono {b b' : Fin m} {R R' : ℕ} (hR : 2 * R + 1 < m) (hRR : R' ≤ R)
    (h : dist (circle.center L m (.inl b')) (circle.center L m (.inl b)) + R' * mesh L m ≤
      R * mesh L m) {σ : (circle m).X} (hσ : circle.ball m b' R' σ) : circle.ball m b R σ := by
  have key : ∀ v, circle.ball m b' R' (.inl v) → circle.ball m b R (.inl v) := fun v hv ↦ by
    rw [circle.ball_inl_iff L m (by omega)] at hv ⊢
    linarith [dist_triangle (circle.center L m (.inl v)) (circle.center L m (.inl b'))
      (circle.center L m (.inl b))]
  rcases σ with v | e
  · exact key v hσ
  · rw [circle.ball_inr_iff m (by omega)] at hσ ⊢
    exact ⟨key _ hσ.1, key _ hσ.2⟩

end CircleArith

/-! ### Boxes of the torus around points -/

section TorusBox

variable (L : ℝ) [Fact (0 < L)] (m n : ℕ) [NeZero m]

omit [Fact (0 < L)] [NeZero m] in
theorem prodLabel_apply {E : Type*} : (n : ℕ) → {C : Fin n → BasedComplex} →
    (a : ∀ i, (C i).X → E) → (σ : (prodComplex n C).X) → (k : Fin n) →
    prodLabel n a σ k = a k (coord n σ k)
  | 0, _, _, _, k => k.elim0
  | n + 1, _, a, σ, k => by
    induction k using Fin.cases with
    | zero => rfl
    | succ k => exact prodLabel_apply n (fun i ↦ a i.succ) σ.2 k

omit [Fact (0 < L)] in
theorem torus.center_apply (σ : (torus m n).X) (k : Fin n) :
    torus.center L m n σ k = circle.center L m (coord n σ k) :=
  prodLabel_apply n _ σ k

/-- A nearest vertex (coordinatewise) of a point of `(ℝ/Lℤ)ⁿ`. -/
def torus.near (y : Fin n → AddCircle L) : Fin n → Fin m :=
  fun k ↦ Classical.choose (circle.exists_near L m (y k))

theorem torus.dist_near (y : Fin n → AddCircle L) (k : Fin n) :
    dist (y k) (circle.center L m (.inl (torus.near L m n y k))) ≤ mesh L m / 2 :=
  Classical.choose_spec (circle.exists_near L m (y k))

/-- The grid box with per-coordinate radii `R k` around the nearest vertex of `y`. -/
def torus.ballBox (y : Fin n → AddCircle L) (R : Fin n → ℕ) : (torus m n).X → Prop :=
  torus.InBox m n (fun k ↦ torus.near L m n y k - Fin.ofNat m (R k)) (fun k ↦ 2 * R k)

theorem torus.ballBox_iff (y : Fin n → AddCircle L) (R : Fin n → ℕ) (σ : (torus m n).X) :
    torus.ballBox L m n y R σ ↔ ∀ k, circle.ball m (torus.near L m n y k) (R k) (coord n σ k) :=
  Iff.rfl

/-- The exact cone contraction of a ball box. -/
def torus.ballBoxContraction (y : Fin n → AddCircle L) (R : Fin n → ℕ)
    (hR : ∀ k, 2 * R k + 1 < m) : SubContraction (torus m n) (torus.ballBox L m n y R) :=
  torus.inBoxContraction m n _ _ fun k ↦ by have := hR k; omega

variable {L m n}

theorem torus.ballBox_of_dist {y : Fin n → AddCircle L} {R : Fin n → ℕ}
    (hR : ∀ k, 2 * R k + 1 < m) {σ : (torus m n).X}
    (h : ∀ k, dist (torus.center L m n σ k) (y k) + mesh L m ≤ R k * mesh L m) :
    torus.ballBox L m n y R σ := fun k ↦ by
  refine circle.ball_of_dist L m (hR k) ?_
  rw [← torus.center_apply]
  linarith [h k, dist_triangle (torus.center L m n σ k) (y k)
    (circle.center L m (.inl (torus.near L m n y k))), torus.dist_near L m n y k]

theorem torus.dist_of_ballBox {y : Fin n → AddCircle L} {R : Fin n → ℕ}
    (hR : ∀ k, 2 * R k + 1 < m) {σ : (torus m n).X} (h : torus.ballBox L m n y R σ) (k : Fin n) :
    dist (torus.center L m n σ k) (y k) ≤ R k * mesh L m + mesh L m := by
  have h₁ := circle.dist_of_ball L m (hR k) (h k)
  rw [← torus.center_apply] at h₁
  have h₂ := torus.dist_near L m n y k
  rw [dist_comm] at h₂
  linarith [dist_triangle (torus.center L m n σ k)
    (circle.center L m (.inl (torus.near L m n y k))) (y k)]

/-- **Nesting of ball boxes.** -/
theorem torus.ballBox_mono {y y' : Fin n → AddCircle L} {R R' : Fin n → ℕ}
    (hR : ∀ k, 2 * R k + 1 < m) (hRR : ∀ k, R' k ≤ R k)
    (h : ∀ k, dist (y' k) (y k) + R' k * mesh L m + mesh L m ≤ R k * mesh L m)
    {σ : (torus m n).X} (hσ : torus.ballBox L m n y' R' σ) : torus.ballBox L m n y R σ :=
  fun k ↦ circle.ball_mono L m (hR k) (hRR k) (by
    have h₁ := torus.dist_near L m n y k
    have h₂ := torus.dist_near L m n y' k
    rw [dist_comm] at h₂
    linarith [h k, dist_triangle (circle.center L m (.inl (torus.near L m n y' k))) (y' k)
      (circle.center L m (.inl (torus.near L m n y k))),
      dist_triangle (y' k) (y k) (circle.center L m (.inl (torus.near L m n y k)))]) (hσ k)

end TorusBox

end BasedComplex

end HSFormal.Cubical

namespace HSFormal.Cubical

open Matrix

namespace BasedComplex

/-! ### `a_g`: cellular approximation of a map of `(ℝ/Lℤ)ⁿ` -/

section Approx

variable {L : ℝ} [Fact (0 < L)] {m n : ℕ} [NeZero m]

theorem torus.dist_center_le_of_d {σ τ : (torus m n).X} (h : (torus m n).d τ σ ≠ 0) :
    dist (torus.center L m n τ) (torus.center L m n σ) ≤ mesh L m / 2 := by
  have := (edist_le_prop h).trans (torus.prop_d_le L m n)
  rwa [edist_dist, ENNReal.ofReal_le_ofReal_iff (by linarith [mesh_pos L m])] at this

theorem torus.isAugmented : (torus m n).IsAugmented :=
  IsAugmented.prod n fun _ ↦ isAugmented_oneDim _ _ _ _

theorem torus.center_mem (σ : (torus m n).X) :
    torus.center L m n σ ∈ (torus.geometry L m n).carrier σ := by
  rw [← torus.geometry_center]; exact (torus.geometry L m n).center_mem σ

/-- Cells on whose closed carrier `g` is the identity (`E_h` of design §2.4); face-closed. -/
def FixCell (g : (Fin n → AddCircle L) → Fin n → AddCircle L) (σ : (torus m n).X) : Prop :=
  ∀ x ∈ (torus.geometry L m n).carrier σ, g x = x

theorem FixCell.of_face {g : (Fin n → AddCircle L) → Fin n → AddCircle L} {σ τ : (torus m n).X}
    (h : (torus m n).d τ σ ≠ 0) (hσ : FixCell g σ) : FixCell g τ :=
  fun x hx ↦ hσ x ((torus.geometry L m n).face_sub τ σ h hx)

variable (L m n) in
/-- Parameters of `a_g`: the base radius `R₀ ≥ 2` and the radius step `s` per degree, with the
nesting condition `dist x y ≤ η/2 → dist (g x) (g y) + η ≤ s η` and properness of the boxes. -/
structure ApproxParams (g : (Fin n → AddCircle L) → Fin n → AddCircle L) where
  R₀ : ℕ
  s : ℕ
  two_le : 2 ≤ R₀
  hs : ∀ x y, dist x y ≤ mesh L m / 2 → dist (g x) (g y) + mesh L m ≤ s * mesh L m
  hm : 2 * (R₀ + n * s) + 1 < m

/-- The vertex nearest to `y`. -/
def torus.nearVertex (y : Fin n → AddCircle L) : (torus m n).X := torus.vertex m n (torus.near L m n y)

theorem torus.deg_nearVertex (y : Fin n → AddCircle L) : (torus m n).deg (torus.nearVertex y) = 0 :=
  torus.deg_vertex m n _

open scoped Classical in
/-- The prescribed columns of `a_g`: identity on `FixCell g`, nearest vertices of `g` elsewhere. -/
def approxPre (g : (Fin n → AddCircle L) → Fin n → AddCircle L) :
    Matrix (torus m n).X (torus m n).X ℚ := fun ρ σ ↦
  if FixCell g σ then (if ρ = σ then 1 else 0)
  else (if ρ = torus.nearVertex (g (torus.center L m n σ)) then 1 else 0)

/-- The prescribed set of `a_g`: `FixCell g` and all vertices. -/
def ApproxFixed (g : (Fin n → AddCircle L) → Fin n → AddCircle L) (σ : (torus m n).X) : Prop :=
  FixCell g σ ∨ (torus m n).deg σ = 0

theorem approxPre_of_fix {g : (Fin n → AddCircle L) → Fin n → AddCircle L} {σ : (torus m n).X}
    (hf : FixCell g σ) (ρ : (torus m n).X) : approxPre g ρ σ = if ρ = σ then 1 else 0 := by
  simp [approxPre, hf]

theorem approxPre_of_not_fix {g : (Fin n → AddCircle L) → Fin n → AddCircle L}
    {σ : (torus m n).X} (hf : ¬FixCell g σ) (ρ : (torus m n).X) :
    approxPre g ρ σ = if ρ = torus.nearVertex (g (torus.center L m n σ)) then 1 else 0 := by
  simp [approxPre, hf]

theorem approxPre_col_vertex {g : (Fin n → AddCircle L) → Fin n → AddCircle L}
    {σ : (torus m n).X} (h0 : (torus m n).deg σ = 0) :
    ∃ v, (torus m n).deg v = 0 ∧ ∀ ρ, approxPre g ρ σ = if ρ = v then 1 else 0 := by
  by_cases hf : FixCell g σ
  · exact ⟨σ, h0, approxPre_of_fix hf⟩
  · exact ⟨_, torus.deg_nearVertex _, approxPre_of_not_fix hf⟩

theorem sum_aug_single {v : (torus m n).X} (hv : (torus m n).deg v = 0) :
    ∑ ρ, (torus m n).aug ρ * (if ρ = v then (1 : ℚ) else 0) = 1 := by
  rw [Finset.sum_eq_single v (fun κ _ hκ ↦ by simp [hκ]) (by simp)]
  simp [aug, hv]

namespace ApproxParams

variable {g : (Fin n → AddCircle L) → Fin n → AddCircle L} (P : ApproxParams L m n g)

/-- The radius of the box of a cell of degree `r`: `R₀ + r s`. -/
def rad (σ : (torus m n).X) : Fin n → ℕ := fun _ ↦ P.R₀ + (torus m n).deg σ * P.s

omit [Fact (0 < L)] in
theorem rad_le (σ : (torus m n).X) (k : Fin n) : P.rad σ k ≤ P.R₀ + n * P.s := by
  have := torus.dimLE m n σ
  simp only [rad]
  gcongr

omit [Fact (0 < L)] in
theorem rad_lt (σ : (torus m n).X) (k : Fin n) : 2 * P.rad σ k + 1 < m := by
  have := P.rad_le σ k; have := P.hm; omega

omit [Fact (0 < L)] in
theorem two_le_rad (σ : (torus m n).X) (k : Fin n) : (2 : ℝ) ≤ P.rad σ k := by
  have : 2 ≤ P.rad σ k := le_trans P.two_le (Nat.le_add_right _ _)
  exact_mod_cast this

/-- The box of `σ`: around `g (centre σ)`. -/
def box (σ : (torus m n).X) : (torus m n).X → Prop :=
  torus.ballBox L m n (g (torus.center L m n σ)) (P.rad σ)

theorem box_nest (τ σ : (torus m n).X) (h : (torus m n).d τ σ ≠ 0) (ρ : (torus m n).X)
    (hρ : P.box τ ρ) : P.box σ ρ := by
  have hdeg := (torus m n).d_deg τ σ h
  have hd := P.hs _ _ (torus.dist_center_le_of_d (L := L) h)
  have hRR : ∀ k, P.rad τ k ≤ P.rad σ k := fun k ↦ by
    simp only [rad, hdeg]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ _)) _
  refine torus.ballBox_mono (P.rad_lt σ) hRR (fun k ↦ ?_) hρ
  have := dist_le_pi_dist (g (torus.center L m n τ)) (g (torus.center L m n σ)) k
  simp only [rad, hdeg]
  push_cast
  nlinarith

theorem pre_supp (ρ σ : (torus m n).X) (h : approxPre g ρ σ ≠ 0) : P.box σ ρ := by
  have hη := mesh_pos L m
  have hrad : ∀ k, (2 : ℝ) * mesh L m ≤ P.rad σ k * mesh L m := fun k ↦
    mul_le_mul_of_nonneg_right (P.two_le_rad σ k) hη.le
  by_cases hf : FixCell g σ
  · rw [approxPre_of_fix hf] at h
    obtain rfl : ρ = σ := by by_contra h'; simp [h'] at h
    refine torus.ballBox_of_dist (P.rad_lt ρ) fun k ↦ ?_
    rw [hf _ (torus.center_mem ρ), dist_self]
    linarith [hrad k]
  · rw [approxPre_of_not_fix hf] at h
    obtain rfl : ρ = torus.nearVertex (g (torus.center L m n σ)) := by
      by_contra h'; simp [h'] at h
    refine torus.ballBox_of_dist (P.rad_lt σ) fun k ↦ ?_
    rw [torus.nearVertex, torus.center_vertex, dist_comm]
    linarith [hrad k, torus.dist_near L m n (g (torus.center L m n σ)) k]

theorem pre_comm (ρ σ : (torus m n).X) (hσ : ApproxFixed g σ) :
    ((torus m n).d * approxPre (m := m) g) ρ σ = (approxPre (m := m) g * (torus m n).d) ρ σ := by
  by_cases hf : FixCell g σ
  · have e₁ : ((torus m n).d * approxPre (m := m) g) ρ σ = (torus m n).d ρ σ := by
      rw [mul_apply, Finset.sum_eq_single σ (fun κ _ hκ ↦ by simp [approxPre_of_fix hf, hκ])
        (by simp)]
      simp [approxPre_of_fix hf]
    have e₂ : (approxPre (m := m) g * (torus m n).d) ρ σ = (torus m n).d ρ σ := by
      rw [mul_apply, Finset.sum_eq_single ρ (fun τ _ hτ ↦ by
        by_cases h : (torus m n).d τ σ = 0
        · simp [h]
        · simp [approxPre_of_fix (FixCell.of_face h hf), Ne.symm hτ]) (by simp)]
      by_cases h : (torus m n).d ρ σ = 0
      · simp [h]
      · simp [approxPre_of_fix (FixCell.of_face h hf)]
    rw [e₁, e₂]
  · have h0 : (torus m n).deg σ = 0 := hσ.resolve_left hf
    set v := torus.nearVertex (L := L) (m := m) (g (torus.center L m n σ))
    have e₁ : ((torus m n).d * approxPre (m := m) g) ρ σ = (torus m n).d ρ v := by
      rw [mul_apply, Finset.sum_eq_single v (fun κ _ hκ ↦ by simp [approxPre_of_not_fix hf, hκ, v])
        (by simp)]
      simp [approxPre_of_not_fix hf, v]
    have e₂ : (approxPre (m := m) g * (torus m n).d) ρ σ = 0 :=
      Finset.sum_eq_zero fun τ _ ↦ by
        by_cases h : (torus m n).d τ σ = 0
        · simp [h]
        · have := (torus m n).d_deg τ σ h; omega
    rw [e₁, e₂]
    by_contra h
    have := (torus m n).d_deg ρ v h
    rw [torus.deg_nearVertex] at this
    omega

open scoped Classical in
/-- **The cellular approximation `a_g`** (design §2.4): identity on `FixCell g`, nearest
vertices of `g` on the other vertices, and filled in the box `ballBox (g (centre σ)) (R₀ + rs)`
on every other cell. -/
def hom : Hom (torus m n) (torus m n) :=
  carrierHom (fun σ ↦ torus.ballBoxContraction L m n _ _ (P.rad_lt σ)) (ApproxFixed g)
    (approxPre g) (fun τ σ h ρ hρ ↦ P.box_nest τ σ h ρ hρ)
    (fun τ σ h hσ ↦ hσ.elim (fun hf ↦ .inl (FixCell.of_face h hf)) fun h0 ↦ by
      have := (torus m n).d_deg τ σ h; omega)
    (fun σ h ↦ .inr h)
    (fun ρ σ hσ h ↦ by
      by_cases hf : FixCell g σ
      · rw [approxPre_of_fix hf] at h
        obtain rfl : ρ = σ := by by_contra h'; simp [h'] at h
        rfl
      · rw [approxPre_of_not_fix hf] at h
        obtain rfl : ρ = torus.nearVertex (g (torus.center L m n σ)) := by
          by_contra h'; simp [h'] at h
        rw [torus.deg_nearVertex, hσ.resolve_left hf])
    (fun ρ σ _ h ↦ P.pre_supp ρ σ h) (fun ρ σ hσ ↦ pre_comm ρ σ hσ)
    (fun σ hσ ↦ by
      obtain ⟨v, hv, hcol⟩ := approxPre_col_vertex (g := g) (L := L) hσ
      simp_rw [hcol]
      exact sum_aug_single hv)
    torus.isAugmented

theorem hom_supp {ρ σ : (torus m n).X} (h : P.hom.f ρ σ ≠ 0) : P.box σ ρ := by
  classical
  exact carrierHom_supp _ _ _ _ _ _ _ _ _ _ _ h

theorem hom_of_fixed {σ : (torus m n).X} (hσ : ApproxFixed g σ) (ρ : (torus m n).X) :
    P.hom.f ρ σ = approxPre g ρ σ := by
  classical
  rw [hom]
  exact carrierHom_f_of_fixed _ _ _ _ _ _ _ _ _ _ _ hσ ρ

theorem hom_of_fix {σ : (torus m n).X} (hσ : FixCell g σ) (ρ : (torus m n).X) :
    P.hom.f ρ σ = if ρ = σ then 1 else 0 := by
  rw [P.hom_of_fixed (.inl hσ), approxPre_of_fix hσ]

/-- **Carrier bound** `μ`: every cell of `a_g σ` has centre within `(R₀ + n s + 1) η` of
`g (centre σ)` (sup metric). -/
theorem hom_dist {ρ σ : (torus m n).X} (h : P.hom.f ρ σ ≠ 0) :
    dist (torus.center L m n ρ) (g (torus.center L m n σ)) ≤
      (P.R₀ + n * P.s + 1 : ℕ) * mesh L m := by
  have hη := mesh_pos L m
  refine (dist_pi_le_iff (by positivity)).mpr fun k ↦ ?_
  refine (torus.dist_of_ballBox (P.rad_lt σ) (P.hom_supp h) k).trans ?_
  have : (P.rad σ k : ℝ) ≤ (P.R₀ + n * P.s : ℕ) := by exact_mod_cast P.rad_le σ k
  push_cast at this ⊢
  nlinarith

/-- **`a_1 = 1` exactly**: the approximation of the identity is the identity. -/
theorem hom_eq_id (hg : ∀ x, g x = x) : P.hom = Hom.id (torus m n) :=
  Hom.ext <| by
    ext ρ σ
    rw [P.hom_of_fix (fun x _ ↦ hg x)]
    simp [Hom.id, one_apply]

/-- `ε ∘ a_g = ε`. -/
theorem hom_aug (σ : (torus m n).X) :
    ∑ ρ, (torus m n).aug ρ * P.hom.f ρ σ = (torus m n).aug σ := by
  by_cases h0 : (torus m n).deg σ = 0
  · simp_rw [P.hom_of_fixed (.inr h0)]
    obtain ⟨v, hv, hcol⟩ := approxPre_col_vertex (g := g) (L := L) h0
    simp_rw [hcol]
    rw [sum_aug_single hv]
    simp [aug, h0]
  · rw [show (torus m n).aug σ = 0 by simp [aug, h0]]
    refine Finset.sum_eq_zero fun ρ _ ↦ ?_
    by_cases h : P.hom.f ρ σ = 0
    · simp [h]
    · have := P.hom.deg0 ρ σ h
      simp [aug, show (torus m n).deg ρ ≠ 0 by omega]

/-- **`a_g z = z`** (8.4), the local proof of design F18: if every cell off `FixCell g`, and
each of its images, lies in one contractible subcomplex `Q`, then `a_g` fixes every top cycle `z`
(`a_g z - z` is an `n`-cycle in `Q`; it bounds there, but `Tⁿ` has no `(n+1)`-cells). -/
theorem hom_mulVec_cycle {z : (torus m n).X → ℚ} (hz : IsCycle (torus m n) n z)
    {Q : (torus m n).X → Prop} (SQ : SubContraction (torus m n) Q)
    (hQ : ∀ σ, ¬FixCell g σ → Q σ ∧ ∀ ρ, P.hom.f ρ σ ≠ 0 → Q ρ) : P.hom.f *ᵥ z = z := by
  set γ : (torus m n).X → ℚ := P.hom.f *ᵥ z - z with hγ
  have hγ' : ∀ ρ, γ ρ = ∑ σ, (P.hom.f - 1) ρ σ * z σ := fun ρ ↦ by
    simp only [hγ, Pi.sub_apply, mulVec, dotProduct, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib,
      one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hsupp : ∀ ρ, γ ρ ≠ 0 → Q ρ := fun ρ h ↦ by
    rw [hγ'] at h
    obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have h₁ := left_ne_zero_of_mul hσ
    have hf : ¬FixCell g σ := fun hf ↦ h₁ (by
      rw [Matrix.sub_apply, P.hom_of_fix hf, one_apply]; simp)
    obtain ⟨hQσ, hQρ⟩ := hQ σ hf
    by_cases hρ : P.hom.f ρ σ = 0
    · rw [Matrix.sub_apply, hρ, one_apply] at h₁
      by_cases e : ρ = σ
      · exact e ▸ hQσ
      · simp [e] at h₁
    · exact hQρ ρ hρ
  have hcyc : (torus m n).d *ᵥ γ = 0 := by
    rw [hγ, mulVec_sub, mulVec_mulVec, P.hom.comm, ← mulVec_mulVec, hz.cycle, mulVec_zero,
      sub_zero]
  have haug : ∑ ρ, (torus m n).aug ρ * γ ρ = 0 := by
    simp only [hγ, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, mulVec, dotProduct,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Finset.sum_mul, P.hom_aug]
    ring
  have hdeg : ∀ κ, γ κ ≠ 0 → (torus m n).deg κ = n := fun κ h ↦ by
    rw [hγ'] at h
    obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have hzσ := hz.deg σ (right_ne_zero_of_mul hσ)
    have h₁ := left_ne_zero_of_mul hσ
    by_cases hρ : P.hom.f κ σ = 0
    · rw [Matrix.sub_apply, hρ, one_apply] at h₁
      by_cases e : κ = σ
      · rw [e, hzσ]
      · simp [e] at h₁
    · have := P.hom.deg0 κ σ hρ; omega
  have hs : SQ.s *ᵥ γ = 0 := by
    ext ρ
    simp only [mulVec, dotProduct, Pi.zero_apply]
    refine Finset.sum_eq_zero fun κ _ ↦ ?_
    by_cases h : γ κ = 0
    · rw [h, mul_zero]
    · rw [SQ.s_eq_zero (k := n) (fun ρ _ ↦ torus.dimLE m n ρ) (hdeg κ h).ge, zero_mul]
  have := SQ.fill hsupp hcyc haug
  rw [hs, mulVec_zero] at this
  exact (sub_eq_zero.mp this.symm)

end ApproxParams

/-! ### Carrier homotopies in ball boxes -/

/-- **Carrier homotopy in boxes** (`B_{g,h}` (8.5), `U_g` (8.6)): chain maps `F, G : C → Tⁿ`
carried in ball boxes `ballBox (p σ) (r σ)`, nested along the faces of `C`, with equal vertex
augmentations, are homotopic by the exact homotopy `carrierHtpy` carried in the same boxes. -/
def boxHtpy {C : BasedComplex} (F G : Hom C (torus m n)) (p : C.X → Fin n → AddCircle L)
    (r : C.X → Fin n → ℕ) (hr : ∀ σ k, 2 * r σ k + 1 < m)
    (hnest : ∀ τ σ, C.d τ σ ≠ 0 → ∀ k, r τ k ≤ r σ k ∧
      dist (p τ k) (p σ k) + r τ k * mesh L m + mesh L m ≤ r σ k * mesh L m)
    (hF : ∀ ρ σ, F.f ρ σ ≠ 0 → torus.ballBox L m n (p σ) (r σ) ρ)
    (hG : ∀ ρ σ, G.f ρ σ ≠ 0 → torus.ballBox L m n (p σ) (r σ) ρ)
    (haug : ∀ σ, C.deg σ = 0 →
      ∑ ρ, (torus m n).aug ρ * F.f ρ σ = ∑ ρ, (torus m n).aug ρ * G.f ρ σ) : Htpy F G :=
  carrierHtpy (fun σ ↦ torus.ballBoxContraction L m n (p σ) (r σ) (hr σ)) F G
    (fun τ σ h _ hρ ↦ torus.ballBox_mono (hr σ) (fun k ↦ (hnest τ σ h k).1)
      (fun k ↦ (hnest τ σ h k).2) hρ) hF hG haug

theorem boxHtpy_supp {C : BasedComplex} {F G : Hom C (torus m n)}
    {p : C.X → Fin n → AddCircle L} {r : C.X → Fin n → ℕ} {hr hnest hF hG haug}
    {ρ : (torus m n).X} {σ : C.X} (h : (boxHtpy F G p r hr hnest hF hG haug).h ρ σ ≠ 0) :
    torus.ballBox L m n (p σ) (r σ) ρ :=
  carrierHtpy_supp _ _ _ _ _ _ _ h

/-- The carrier bound of a box homotopy, coordinatewise. -/
theorem boxHtpy_dist {C : BasedComplex} {F G : Hom C (torus m n)}
    {p : C.X → Fin n → AddCircle L} {r : C.X → Fin n → ℕ} {hr hnest hF hG haug}
    {ρ : (torus m n).X} {σ : C.X} (h : (boxHtpy F G p r hr hnest hF hG haug).h ρ σ ≠ 0)
    (k : Fin n) : dist (torus.center L m n ρ k) (p σ k) ≤ r σ k * mesh L m + mesh L m :=
  torus.dist_of_ballBox (hr σ) (boxHtpy_supp h) k

/-- The box homotopy vanishes on a face-closed set where `F = G`. -/
theorem boxHtpy_eq_zero {C : BasedComplex} {F G : Hom C (torus m n)}
    {p : C.X → Fin n → AddCircle L} {r : C.X → Fin n → ℕ} {hr hnest hF hG haug}
    {Z : C.X → Prop} (hZ : ∀ τ σ, C.d τ σ ≠ 0 → Z σ → Z τ)
    (hFG : ∀ ρ σ, Z σ → F.f ρ σ = G.f ρ σ) {σ : C.X} (hσ : Z σ) (ρ : (torus m n).X) :
    (boxHtpy F G p r hr hnest hF hG haug).h ρ σ = 0 :=
  carrierHtpy_eq_zero _ _ _ _ _ _ _ hZ hFG hσ ρ

end Approx

end BasedComplex

end HSFormal.Cubical
