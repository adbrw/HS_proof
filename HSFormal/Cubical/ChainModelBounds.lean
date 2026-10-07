import HSFormal.Cubical.ChainModelCore
import HSFormal.Cubical.GraphBridge
import HSFormal.Germ

/-!
# The chain models along the index: meshes and `f`-control (cubical module C6, part 3)

**Meshes and choice order** (manuscript (7.9), `cubical-review.md` fix 6): the meshes are the
germ meshes `m_i = i + 2` of `HSFormal.manifoldGerm` (`η_i = 16/(i+2) → 0`), so that `D_i` is
literally the germ complex.  The fixed data `d` (chart, `H`, `D`, `f`, `ρ̃`, radii) come first; the
groups `K_i = H_{j+i+1}` (`TailGroups`) and the meshes are both fixed sequences, chosen
independently: the constructions need only that all boxes be proper (`Good m_i`, true for all
large `i`, `eventually_good_germ`; at the finitely many coarse indices `a = 1`, `B = 0`, `U = 0`),
and the errors depend only on `η_i → 0` and the cocycle displacement `d_i → 0`.  No coupling of
`η_i` with `K_i` is needed.  (The dyadic constraint of fix 6, `[-2^{-k₀}, 2^{-k₀}]ⁿ` a grid
subcomplex, is not used here; it concerns the cut flag of §11.)

* `aI`, `BI`, `UI`, `VI`: `a_g`, `B_{g,h}`, `U_g`, `V_g` at index `i` on `W_i = Tⁿ_{i+2} ⊗ CPcell`,
  with
  `aI_one : a_1 = 1`, `aI_z : a_g z = z`, and the exact equations (8.5)–(8.7) by construction.
* Global `f`-control (`f`-labels `f̂ ∘ lift ∘ centre`, `C_p` acting trivially on `Sⁿ`):
  `graphTendsto_aI`, `graphTendsto_BI`, `graphTendsto_UI`, `graphTendsto_VI`, uniformly in
  `g, h ∈ G_i`.  For `B` the inner region `|x| ≤ 3/8` uses the cocycle displacement `d_i → 0`,
  the outer region the exact equality `f = ∞` on both ends (margin `3/8 - ρ - 6D > 1/32`, in
  `ℓ²`, `BT_l2`).
-/

noncomputable section

set_option linter.unusedSectionVars false

open Filter Metric Topology Set Matrix
open HSFormal.Cubical HSFormal.Cubical.BasedComplex
open scoped Kronecker ENNReal

namespace HSFormal.FixedData

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {M : Type*} [TopologicalSpace M] [AddAction ℤ_[p] M]
  (d : FixedData p n M)

/-! ### Metric bounds for `B` at a fixed mesh -/

section MeshBounds

variable [ContinuousVAdd ℤ_[p] M] {m : ℕ} [NeZero m] (hG : d.Good m)

/-- The error `δ_B = (SB + n sB + 2) η` of the boxes of `B`. -/
def δB (m : ℕ) : ℝ := (d.SB m + n * d.sB m + 2) * mesh 16 m

theorem δB_nonneg (m : ℕ) : 0 ≤ d.δB m := mul_nonneg (by positivity) (mesh_nonneg m)

/-- **`B` on the inner region**: for `|x| ≤ 1/2` and `a + b = c + k`, the carrier of `B` lies
within `ω(|k v - v|) + δ_B` of `ĥ_c x`. -/
theorem BT_inner {a b c k : ℤ_[p]} (ha : a ∈ d.H) (hb : b ∈ d.H) (hc : c ∈ d.H) (hk : k ∈ d.H)
    (habc : a + b = c + k) {ρ σ : (torus m n).X} (h : (d.BT hG ha hb hc).h ρ σ ≠ 0)
    (hσ : ‖liftVec 16 (torus.center 16 m n σ)‖ ≤ 1 / 2) :
    dist (torus.center 16 m n ρ) (d.hatT c (torus.center 16 m n σ)) ≤
      d.hatModulus ‖d.chartAct k (liftVec 16 (torus.center 16 m n σ)) -
        liftVec 16 (torus.center 16 m n σ)‖ + d.δB m := by
  have hη := mesh_pos 16 m
  set x := torus.center 16 m n σ
  have hcomp := d.hatT_hatT_of_le ha hb hk habc hσ
  have hψ : ∀ j, d.psi a b c x j ≤ d.hatModulus ‖d.chartAct k (liftVec 16 x) - liftVec 16 x‖ :=
    fun j ↦ by
      refine (dist_le_pi_dist _ _ j).trans ?_
      rw [hcomp]
      exact d.dist_hatT_le_hatModulus hc (d.dist_toTorus_chartAct_le k x)
  refine (dist_pi_le_iff (by linarith [d.hatModulus_nonneg (norm_nonneg
    (d.chartAct k (liftVec 16 x) - liftVec 16 x)), d.δB_nonneg m])).mpr fun j ↦ ?_
  have := d.BT_dist hG ha hb hc h j
  rw [δB]
  linarith [hψ j]

/-- **`B` in `ℓ²`**: the carrier of `B` lies within `4D + √n δ_B` of the cell, in the `ℓ²`
distance of the lifts (the cubical-route replacement of the convex hull of the track). -/
theorem BT_l2 {a b c : ℤ_[p]} (ha : a ∈ d.H) (hb : b ∈ d.H) (hc : c ∈ d.H)
    {ρ σ : (torus m n).X} (h : (d.BT hG ha hb hc).h ρ σ ≠ 0) :
    l2 (torus.center 16 m n ρ) (torus.center 16 m n σ) ≤ 4 * d.D + √n * d.δB m := by
  set x := torus.center 16 m n σ
  have h₁ : l2 (torus.center 16 m n ρ) (d.hatT c x) ≤
      ‖(WithLp.toLp 2 (d.psi a b c x) : EuclideanSpace ℝ (Fin n))‖ + √n * d.δB m :=
    l2_le_of_coord_le (d.δB_nonneg m) fun j ↦ by
      have := d.BT_dist hG ha hb hc h j; rw [δB]; linarith
  have h₂ : ‖(WithLp.toLp 2 (d.psi a b c x) : EuclideanSpace ℝ (Fin n))‖ ≤
      l2 (d.hatT a (d.hatT b x)) (d.hatT c x) :=
    norm_toLp_le_l2 fun j ↦ ⟨d.psi_nonneg a b c x j, le_rfl⟩
  have h₃ := l2_triangle (d.hatT a (d.hatT b x)) (d.hatT b x) (d.hatT c x)
  have h₄ := l2_triangle (d.hatT b x) x (d.hatT c x)
  have h₅ := l2_triangle (torus.center 16 m n ρ) (d.hatT c x) x
  linarith [d.l2_hatT_le ha (d.hatT b x), d.l2_hatT_le hb x, d.l2_hatT_le hc x,
    l2_comm x (d.hatT c x)]

theorem torusLabel_eq_infty {x : Fin n → AddCircle (16 : ℝ)}
    [LocallyCompactSpace M] [FirstCountableTopology M]
    (hx : d.ρ + 2 * d.D < l2 x 0) : d.torusLabel x = RoundSphere.infty := by
  change d.fhat (liftVec 16 x) = OnePoint.infty
  exact d.fhat_eq_infty (by rwa [norm_liftVec_eq])

/-- **`B` in the outer region**: if `|x| > 3/8` and `√n δ_B < 1/32`, both ends of every entry of
`B` have `f = ∞` (margin `3/8 - ρ - 6D > 1/32`, `cubical-review.md` fix 5). -/
theorem BT_outer [LocallyCompactSpace M] [FirstCountableTopology M] {a b c : ℤ_[p]}
    (ha : a ∈ d.H) (hb : b ∈ d.H) (hc : c ∈ d.H) {ρ σ : (torus m n).X}
    (h : (d.BT hG ha hb hc).h ρ σ ≠ 0) (hσ : 3 / 8 < l2 (torus.center 16 m n σ) 0)
    (hδ : √n * d.δB m < 1 / 32) :
    d.torusLabel (torus.center 16 m n ρ) = d.torusLabel (torus.center 16 m n σ) := by
  have hρ := d.ρ_lt.trans d.ρplus_lt
  have hD := d.D_lt
  have h₁ := d.BT_l2 hG ha hb hc h
  have h₂ := l2_triangle (torus.center 16 m n σ) (torus.center 16 m n ρ) 0
  have h₃ := l2_comm (torus.center 16 m n σ) (torus.center 16 m n ρ)
  rw [d.torusLabel_eq_infty (by linarith), d.torusLabel_eq_infty (by linarith)]

end MeshBounds

/-! ### The germ meshes and the maps at index `i` -/

section Index

open scoped Classical

variable [ContinuousVAdd ℤ_[p] M]

/-- All boxes are proper at the germ meshes `m_i = i + 2` (`HSFormal.germMesh`), for large `i`. -/
theorem eventually_good_germ : ∀ᶠ i in atTop, d.Good (germMesh i) :=
  tendsto_germMesh.eventually d.eventually_good

theorem tendsto_comp_germ {f : ℕ → ℝ} {c : ℝ} (hf : Tendsto f atTop (𝓝 c)) :
    Tendsto (fun i ↦ f (germMesh i)) atTop (𝓝 c) :=
  hf.comp tendsto_germMesh

/-- `W_i = Tⁿ_{m_i} ⊗ CPcell` at the germ mesh `m_i = i + 2`. -/
abbrev W (n i : ℕ) : BasedComplex := torusCP (germMesh i) n

/-- **`a_g` at index `i`**: the approximation of `ĥ_{h_g}`, `h_g = rep i g` (l.610), once the mesh
is valid; the identity at the finitely many coarse indices. -/
def aI (i : ℕ) (g : d.G i) : Hom (W n i) (W n i) :=
  if hG : d.Good (germMesh i) then d.aW hG (d.rep i g).val_mem else Hom.id _

theorem aI_of_good {i : ℕ} (hG : d.Good (germMesh i)) (g : d.G i) :
    d.aI i g = d.aW hG (d.rep i g).val_mem := by
  simp only [aI, dif_pos hG]

theorem aI_of_not_good {i : ℕ} (hG : ¬d.Good (germMesh i)) (g : d.G i) :
    d.aI i g = Hom.id _ := by
  simp only [aI, dif_neg hG]

/-- **`a_1 = 1` exactly.** -/
theorem aI_one (i : ℕ) : d.aI i 1 = Hom.id (W n i) := by
  by_cases hG : d.Good (germMesh i)
  · rw [aI_of_good d hG, d.aW_congr _ (by rw [rep_one, PadicTail.val_one]) _ (zero_mem _),
      aW_zero]
  · exact d.aI_of_not_good hG 1

/-- **(8.4) `a_g z = z` exactly.** -/
theorem aI_z (i : ℕ) (g : d.G i) :
    (d.aI i g).f *ᵥ torusCP.z (germMesh i) n = torusCP.z (germMesh i) n := by
  by_cases hG : d.Good (germMesh i)
  · rw [aI_of_good d hG]; exact d.aW_z _ _
  · rw [aI_of_not_good d hG, Hom.id_f, one_mulVec]

/-- **(8.5)** `B_{g,h} : a_g a_h ≃ a_{gh}` at index `i`, for the pair `q = (g, h)`. -/
def BI (i : ℕ) (q : d.G i × d.G i) :
    Htpy ((d.aI i q.1).comp (d.aI i q.2)) (d.aI i (q.1 * q.2)) :=
  if hG : d.Good (germMesh i) then
    (d.BW hG (d.rep i q.1).val_mem (d.rep i q.2).val_mem (d.rep i (q.1 * q.2)).val_mem).congr
      (by rw [aI_of_good d hG, aI_of_good d hG]) (by rw [aI_of_good d hG])
  else Htpy.ofEq (by rw [aI_of_not_good d hG, aI_of_not_good d hG, aI_of_not_good d hG,
    Hom.id_comp])

theorem BI_h_of_good {i : ℕ} (hG : d.Good (germMesh i)) (q : d.G i × d.G i) :
    (d.BI i q).h = (d.BW hG (d.rep i q.1).val_mem (d.rep i q.2).val_mem
      (d.rep i (q.1 * q.2)).val_mem).h := by
  simp only [BI, dif_pos hG, Htpy.congr_h]

/-- The duality `φ_i` of `W_i` (`torusCP.duality`, as in the germ). -/
abbrev phiI (n i : ℕ) : Hom ((W n i).dual (n + 4) (torusCP.dimLE _ n)) (W n i) :=
  (torusCP.duality (germMesh i) n).hom

/-- `a_g φ a_g^*`. -/
abbrev aphiaI (i : ℕ) (g : d.G i) : Hom ((W n i).dual (n + 4) (torusCP.dimLE _ n)) (W n i) :=
  ((d.aI i g).comp (phiI n i)).comp ((d.aI i g).dual (n + 4) (torusCP.dimLE _ n) (torusCP.dimLE _ n))

/-- **(8.6)** `U_g : a_g φ a_g^* ≃ φ` at index `i`. -/
def UI (i : ℕ) (g : d.G i) : Htpy (d.aphiaI i g) (phiI n i) :=
  if hG : d.Good (germMesh i) then
    (d.UW hG (d.rep i g).val_mem).congr (by rw [aphiaI, aI_of_good d hG]; rfl) rfl
  else Htpy.ofEq (by rw [aphiaI, aI_of_not_good d hG, Hom.dual_id, Hom.comp_id, Hom.id_comp])

theorem UI_h_of_good {i : ℕ} (hG : d.Good (germMesh i)) (g : d.G i) :
    (d.UI i g).h = (d.UW hG (d.rep i g).val_mem).h := by
  simp only [UI, dif_pos hG, Htpy.congr_h]

/-- `T_g : a_{g⁻¹} a_g ≃ 1` (`B_{g⁻¹,g}` and `a_1 = 1`), the input of (8.7). -/
def TI (i : ℕ) (g : d.G i) : Htpy ((d.aI i g⁻¹).comp (d.aI i g)) (Hom.id (W n i)) :=
  (d.BI i (g⁻¹, g)).congr rfl (by rw [inv_mul_cancel, aI_one])

theorem TI_h (i : ℕ) (g : d.G i) : (d.TI i g).h = (d.BI i (g⁻¹, g)).h := by
  simp [TI]

/-- **(8.7)** `V_g = -a φ K + U b^* : a_g φ ≃ φ a_{g⁻¹}^*` at index `i`, `K` the shifted dual of
`T_g` (`K_r = (-1)^{r+1} T^*_{N-r-1}`, l.700). -/
def VI (i : ℕ) (g : d.G i) : Htpy ((d.aI i g).comp (phiI n i))
    ((phiI n i).comp ((d.aI i g⁻¹).dual (n + 4) (torusCP.dimLE _ n) (torusCP.dimLE _ n))) :=
  let K : Htpy (((d.aI i g).dual (n + 4) (torusCP.dimLE _ n) (torusCP.dimLE _ n)).comp
      ((d.aI i g⁻¹).dual (n + 4) (torusCP.dimLE _ n) (torusCP.dimLE _ n))) (Hom.id _) :=
    ((d.TI i g).dual (torusCP.dimLE _ n) (torusCP.dimLE _ n)).congr
      (Hom.dual_comp _ _ _ _ _) (Hom.dual_id _)
  ((K.symm.compLeft ((d.aI i g).comp (phiI n i))).congr (Hom.comp_id _)
    (Hom.comp_assoc _ _ _).symm).trans
    ((d.UI i g).compRight ((d.aI i g⁻¹).dual (n + 4) (torusCP.dimLE _ n) (torusCP.dimLE _ n)))

theorem VI_h (i : ℕ) (g : d.G i) : (d.VI i g).h =
    ((d.aI i g).f * (phiI n i).f) * (-(((-(-1 : ℚ) ^ (n + 4)) •
      ((d.TI i g).hᵀ * (W n i).sgn)))) + (d.UI i g).h * ((d.aI i g⁻¹).f)ᵀ := by
  simp only [VI, Htpy.trans_h, Htpy.congr_h, Htpy.compLeft_h, Htpy.symm_h, Htpy.compRight_h,
    Hom.dual_f, Hom.comp_f]
  rfl

/-- The cocycle relation of the representatives, `h_g + h_h = h_{gh} + k_{g,h}` (l.610). -/
theorem rep_add_rep (i : ℕ) (g h : d.G i) :
    (d.rep i g).val + (d.rep i h).val = (d.rep i (g * h)).val + (d.cocycle i g h).val :=
  d.val_rep_add_val_rep i g h

theorem rep_inv_add_rep (i : ℕ) (g : d.G i) :
    (d.rep i g⁻¹).val + (d.rep i g).val = 0 + (d.cocycle i g⁻¹ g).val := by
  rw [d.rep_add_rep, inv_mul_cancel, rep_one, PadicTail.val_one]

end Index

/-! ### Global `f`-control -/

theorem exists_real_le {ε : ℝ≥0∞} (hε : 0 < ε) : ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r ≤ ε := by
  obtain ⟨r, -, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
  exact ⟨r, ENNReal.ofReal_pos.mp hr1, hr2.le⟩

/-- `C_p` acts trivially on `Sⁿ`: the graph type is irrelevant for `f`-labels. -/
theorem graphTendsto_retype {J α β : ℕ → Type*} {buf : ∀ i, α i → Prop} {θ θ' : ∀ i, J i → d.Cp}
    {u : ∀ i, J i → Matrix (β i) (α i) ℚ} {a : ∀ i, α i → RoundSphere n}
    {b : ∀ i, β i → RoundSphere n} (hu : GraphTendsto buf θ u a b) :
    GraphTendsto buf θ' u a b := by
  have : graphErr buf θ' u a b = graphErr buf θ u a b :=
    funext fun i ↦ by first | rfl | (simp [graphErr, graphPropOn]; rfl)
  rwa [GraphTendsto, this]

section FLabels

variable [ContinuousVAdd ℤ_[p] M] [LocallyCompactSpace M] [FirstCountableTopology M]

theorem uniformContinuous_torusLabel : UniformContinuous d.torusLabel :=
  CompactSpace.uniformContinuous_of_continuous d.continuous_torusLabel

/-- **`f`-control from carrier bounds**: if every entry `y ← x` has `y` within `δ` of a point
with the same `f`-label as `x`, eventually for every `δ > 0`, the family is `f`-controlled. -/
theorem graphTendsto_f {J α β : ℕ → Type*} {θ : ∀ i, J i → d.Cp}
    (src : ∀ i, α i → Fin n → AddCircle (16 : ℝ)) (tgt : ∀ i, β i → Fin n → AddCircle (16 : ℝ))
    (u : ∀ i, J i → Matrix (β i) (α i) ℚ)
    (h : ∀ δ > 0, ∀ᶠ i in atTop, ∀ j y x, u i j y x ≠ 0 →
      ∃ z, dist (tgt i y) z < δ ∧ d.torusLabel z = d.torusLabel (src i x)) :
    GraphTendsto (fun _ _ ↦ True) θ u (fun i ↦ d.torusLabel ∘ src i)
      (fun i ↦ d.torusLabel ∘ tgt i) := by
  refine ENNReal.tendsto_nhds_zero.mpr fun ε hε ↦ ?_
  obtain ⟨δ, hδ, hδε⟩ := EMetric.uniformContinuous_iff.mp d.uniformContinuous_torusLabel ε hε
  obtain ⟨r, hr, hrδ⟩ := exists_real_le hδ
  filter_upwards [h r hr] with i hi
  refine graphErr_le_iff.mpr fun j y x _ hu ↦ ?_
  obtain ⟨z, hz, hlab⟩ := hi j y x hu
  change edist ((d.torusLabel ∘ tgt i) y) ((d.torusLabel ∘ src i) x) ≤ ε
  simp only [Function.comp_apply]
  rw [← hlab]
  refine (hδε ?_).le
  rw [edist_dist]
  exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mpr hz).trans_le hrδ

/-- **The chain models** `D_i = W_i`, `f`-labelled: exactly the germ complex of
`HSFormal.manifoldGerm` for `c = f̂` (`FixedData.fhatS_germCollapse`), mesh `16/(i+2)`. -/
abbrev seqW : ControlledSeq (RoundSphere n) :=
  torusCP.controlledSeq 16 n germMesh tendsto_germMesh d.torusLabel d.continuous_torusLabel

/-- The torus centre of a cell of `W_i`. -/
abbrev cW (i : ℕ) (q : (W n i).X) : Fin n → AddCircle (16 : ℝ) :=
  torus.center 16 (germMesh i) n q.1

theorem seqW_label (i : ℕ) : d.seqW.label i = d.torusLabel ∘ cW i := rfl

/-- The dual sequence `D^{N-*}` (same cells and labels). -/
abbrev seqWdual : ControlledSeq (RoundSphere n) :=
  d.seqW.dual (n + 4) fun i ↦ torusCP.dimLE (germMesh i) n

theorem tendsto_RA_germ :
    Tendsto (fun i ↦ (d.RA (germMesh i) : ℝ) * mesh 16 (germMesh i)) atTop (𝓝 0) :=
  tendsto_comp_germ d.tendsto_RA_mul

theorem tendsto_δB : Tendsto (fun m ↦ d.δB m) atTop (𝓝 0) := by
  have hlim := (d.tendsto_SB.add (d.tendsto_sB.const_mul (n : ℝ))).add
    (tendsto_mesh_atTop.const_mul 2)
  simp only [mul_zero, add_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim d.δB_nonneg fun m ↦ ?_
  have h₁ := d.SB_mul_le m
  have h₂ := d.sB_mul_le m
  simp only [δB]
  nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem tendsto_TU_germ : Tendsto (fun i ↦ ((d.TU (germMesh i) : ℝ) + 1) *
    mesh 16 (germMesh i)) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_comp_germ (by simpa using d.tendsto_TUbound.add tendsto_mesh_atTop))
    (fun i ↦ mul_nonneg (by positivity) (mesh_nonneg _)) fun i ↦ ?_
  have := d.TU_mul_le (germMesh i)
  simp only
  linarith

/-- The carrier bound of `a_g` at index `i` (for valid meshes). -/
theorem aI_dist {i : ℕ} (hG : d.Good (germMesh i)) {g : d.G i} {y x : (W n i).X}
    (hu : (d.aI i g).f y x ≠ 0) :
    dist (cW i y) (d.hatT (d.rep i g).val (cW i x)) ≤ d.RA (germMesh i) * mesh 16 (germMesh i) := by
  rw [aI_of_good d hG] at hu
  exact d.aT_dist hG (d.rep i g).val_mem (d.aW_ne_zero hG (d.rep i g).val_mem hu)

/-- **`a_g` is `f`-controlled uniformly in `g`** (carrier `RA η → 0` and `f ĥ = f`). -/
theorem graphTendsto_aI :
    GraphTendsto (fun _ _ ↦ True) (fun i g ↦ d.π i g) (fun i g ↦ (d.aI i g).f)
      d.seqW.label d.seqW.label := by
  refine d.graphTendsto_f cW cW _ fun δ hδ ↦ ?_
  filter_upwards [d.tendsto_RA_germ.eventually (gt_mem_nhds hδ), d.eventually_good_germ]
    with i hi hG g y x hu
  exact ⟨_, (d.aI_dist hG hu).trans_lt hi, d.torusLabel_hatT (d.rep i g).val_mem _⟩

/-- **`B` at a mesh, `f`-control on one entry**: inner region by the cocycle displacement, outer
region by `f = ∞`. -/
theorem B_entry_f {m : ℕ} [NeZero m] (hG : d.Good m) {a b c k : ℤ_[p]} (ha : a ∈ d.H)
    (hb : b ∈ d.H) (hc : c ∈ d.H) (hk : k ∈ d.H) (habc : a + b = c + k) {δ δ₁ : ℝ}
    (hδ₁ : d.hatModulus δ₁ + d.δB m < δ) (hδB : √n * d.δB m < 1 / 32)
    (hdisp : ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ ≤ 2 → ‖d.chartAct k v - v‖ ≤ δ₁)
    {ρ σ : (torus m n).X} (h : (d.BT hG ha hb hc).h ρ σ ≠ 0) :
    ∃ z, dist (torus.center 16 m n ρ) z < δ ∧
      d.torusLabel z = d.torusLabel (torus.center 16 m n σ) := by
  by_cases hσ : l2 (torus.center 16 m n σ) 0 ≤ 3 / 8
  · have hσ' : ‖liftVec 16 (torus.center 16 m n σ)‖ ≤ 1 / 2 := by
      rw [norm_liftVec_eq]; linarith
    refine ⟨_, (d.BT_inner hG ha hb hc hk habc h hσ').trans_lt ?_, d.torusLabel_hatT hc _⟩
    have := d.hatModulus_mono (norm_nonneg _) (hdisp _ (by linarith))
    linarith
  · push_neg at hσ
    refine ⟨_, ?_, d.BT_outer hG ha hb hc h hσ hδB⟩
    rw [dist_self]
    linarith [d.hatModulus_nonneg (le_trans (norm_nonneg _) (hdisp 0 (by simp))), d.δB_nonneg m]

theorem eventually_B_params {δ : ℝ} (hδ : 0 < δ) : ∃ δ₁ > 0,
    ∀ᶠ i in atTop, d.Good (germMesh i) ∧ d.hatModulus δ₁ + d.δB (germMesh i) < δ ∧
      √n * d.δB (germMesh i) < 1 / 32 ∧
      ∀ g h : d.G i, ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ ≤ 2 →
        ‖d.chartAct (d.cocycle i g h).val v - v‖ ≤ δ₁ := by
  obtain ⟨δ₁, hδ₁, hω⟩ := d.exists_hatModulus_le (half_pos hδ)
  refine ⟨δ₁, hδ₁, ?_⟩
  have hB := tendsto_comp_germ d.tendsto_δB
  filter_upwards [d.eventually_good_germ, hB.eventually (gt_mem_nhds (half_pos hδ)),
    (hB.const_mul √n).eventually (gt_mem_nhds (by simp : (√n * 0 : ℝ) < 1 / 32)),
    d.eventually_cocycle_chartAct_lt hδ₁] with i hG h₁ h₂ h₃
  exact ⟨hG, by linarith, h₂, fun g h v hv ↦ (h₃ g h v hv).le⟩

theorem BI_ne_zero {i : ℕ} (hG : d.Good (germMesh i)) {q : d.G i × d.G i}
    {y x : (W n i).X} (hu : (d.BI i q).h y x ≠ 0) :
    (d.BT hG (d.rep i q.1).val_mem (d.rep i q.2).val_mem (d.rep i (q.1 * q.2)).val_mem).h
      y.1 x.1 ≠ 0 := by
  rw [BI_h_of_good d hG] at hu
  exact d.BW_ne_zero _ _ _ _ hu

/-- **`B_{g,h}` is `f`-controlled uniformly in `g, h`** (Lemma 8.2). -/
theorem graphTendsto_BI :
    GraphTendsto (fun _ _ ↦ True) (fun i q ↦ d.π i (q.1 * q.2)) (fun i q ↦ (d.BI i q).h)
      d.seqW.label d.seqW.label := by
  refine d.graphTendsto_f cW cW _ fun δ hδ ↦ ?_
  obtain ⟨δ₁, -, hev⟩ := d.eventually_B_params hδ
  filter_upwards [hev] with i ⟨hG, h₁, h₂, h₃⟩ q y x hu
  exact d.B_entry_f hG _ _ _ (d.cocycle i q.1 q.2).val_mem (d.rep_add_rep i q.1 q.2) h₁ h₂
    (h₃ q.1 q.2) (d.BI_ne_zero hG hu)

/-- The carrier bound of `U_g` at index `i` (for valid meshes). -/
theorem UI_dist {i : ℕ} (hG : d.Good (germMesh i)) {g : d.G i} {y x : (W n i).X}
    (hu : (d.UI i g).h y x ≠ 0) :
    dist (cW i y) (cW i x) ≤ (d.TU (germMesh i) + 1) * mesh 16 (germMesh i) := by
  rw [UI_h_of_good d hG] at hu
  exact d.UT_dist _ _ (d.UW_ne_zero _ _ hu)

/-- **`U_g` is `f`-controlled (local) uniformly in `g`.** -/
theorem graphTendsto_UI :
    GraphTendsto (fun _ _ ↦ True) (fun _ (_ : d.G _) ↦ (1 : d.Cp)) (fun i g ↦ (d.UI i g).h)
      d.seqWdual.label d.seqW.label := by
  refine d.graphTendsto_f cW cW _ fun δ hδ ↦ ?_
  filter_upwards [d.tendsto_TU_germ.eventually (gt_mem_nhds hδ), d.eventually_good_germ]
    with i hi hG g y x hu
  exact ⟨_, (d.UI_dist hG hu).trans_lt hi, rfl⟩

/-- `T_g` is `f`-controlled uniformly in `g`. -/
theorem graphTendsto_TI :
    GraphTendsto (fun _ _ ↦ True) (fun _ (_ : d.G _) ↦ (1 : d.Cp)) (fun i g ↦ (d.TI i g).h)
      d.seqW.label d.seqW.label := by
  refine d.graphTendsto_f cW cW _ fun δ hδ ↦ ?_
  obtain ⟨δ₁, -, hev⟩ := d.eventually_B_params hδ
  filter_upwards [hev] with i ⟨hG, h₁, h₂, h₃⟩ g y x hu
  rw [TI_h] at hu
  exact d.B_entry_f hG _ _ _ (d.cocycle i g⁻¹ g).val_mem (d.rep_add_rep i g⁻¹ g) h₁ h₂
    (h₃ g⁻¹ g) (d.BI_ne_zero (q := (g⁻¹, g)) hG hu)

/-- **`V_g` is `f`-controlled uniformly in `g`**: `V = -a φ K + U b^*` with `K` the shifted dual
of `T_g`; transposes keep `f`-control. -/
theorem graphTendsto_VI :
    GraphTendsto (fun _ _ ↦ True) (fun _ (_ : d.G _) ↦ (1 : d.Cp)) (fun i g ↦ (d.VI i g).h)
      d.seqWdual.label d.seqW.label := by
  have hA := d.graphTendsto_retype (θ' := fun _ _ ↦ (1 : d.Cp)) d.graphTendsto_aI
  have hφ : PropTendstoOn (fun _ _ ↦ True) (fun i ↦ (phiI n i).f) d.seqW.label
      d.seqW.label :=
    ((torusCP.controlledDuality 16 n germMesh tendsto_germMesh d.torusLabel
      d.continuous_torusLabel).hom.tendsto).on _
  have hAφ := (hφ.graphTendsto (J := d.G) (H := d.Cp)).mul hA
    (Eventually.of_forall fun _ _ _ _ _ _ ↦ trivial)
  have hT := d.graphTendsto_TI.transpose
  have hsgn : PropTendstoOn (fun _ _ ↦ True) (fun i ↦ (W n i).sgn) d.seqW.label
      d.seqW.label := (BasedComplex.PropTendsto.sgn).on _
  have hK := ((hT.mul_right hsgn (Eventually.of_forall fun _ _ _ _ _ ↦ trivial)).smul
    (fun _ _ ↦ -(-1 : ℚ) ^ (n + 4))).neg
  have h₁ := d.graphTendsto_retype (θ' := fun _ _ ↦ (1 : d.Cp))
    (hK.mul hAφ (Eventually.of_forall fun _ _ _ _ _ _ ↦ trivial))
  have hb := (hA.reindex fun i g ↦ g⁻¹).transpose
  have h₂ := d.graphTendsto_retype (θ' := fun _ _ ↦ (1 : d.Cp))
    (hb.mul d.graphTendsto_UI (Eventually.of_forall fun _ _ _ _ _ _ ↦ trivial))
  exact (h₁.add h₂).congr rfl (funext₂ fun i g ↦ (d.VI_h i g).symm)

end FLabels

end HSFormal.FixedData
