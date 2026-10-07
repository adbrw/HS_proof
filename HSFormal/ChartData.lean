import HSFormal.FreePoint
import HSFormal.SpherePinch
import HSFormal.CharacterDetector
import HSFormal.PadicDisplacement
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Topology.Metrizable.Urysohn

/-!
# Section 7: the chart, the subgroup `H`, the averaged coordinate and the sphere map

Fixed data of Section 7 of `fullHS_final.md` (L456–517) for an effective jointly continuous
`ℤ_[p]`-action on a manifold without boundary; the package is completed in `HSFormal.FixedData`.

* `HSFormal.PadicTail`: `H_j` as a compact multiplicative group, with normalized Haar measure.
* `HSFormal.padicChar`: the quotient character `χ : H_j → H_j/H_{j+1} ≅ C_p ⊆ S¹` (L517).
* `HSFormal.ChartData`: the free point `x₀`, a chart `φ` with `φ x₀ = 0`, `B(0,4) ⊆ φ(U)`, and
  `H = H_j` with displacement `≤ D < 1/64` on `φ⁻¹ B̄(0,2)` (7.1). Derived: `Ω = H · φ⁻¹ B(0,2)`
  (L468), the Haar average `F₀` (7.2) with (7.3), and the carrier `Z⁺ = F₀⁻¹ B̄(0,ρ₊)` (7.4).
* `HSFormal.exists_equivariant_sphere_map`: the equivariant map `ρ̃ : Z⁺ → T = S^{2m-1}` (7.7).
  It is obtained from the repo's character detector (`exists_finite_character_detector`), with
  the stabilizer hypothesis supplied by `padicStabilizer_le_nextPower_of_not_fixed`, instead of the
  paper's partition of unity on the free `C_p`-space `Z⁺/H'`. Both give a continuous map
  `Z⁺ → S^{2m-1} ⊆ ℂ^m` with `ρ̃(hx) = χ(h) ρ̃(x)`; here `ρ̃` is even defined and continuous on an
  open neighbourhood of `Z⁺`, and equivariant on all of `M`.
-/

noncomputable section

open Set Filter Metric MeasureTheory OnePoint Topology
open scoped unitInterval

namespace HSFormal

/-! ### The tail `H_j` as a compact multiplicative group, and the quotient character -/

/-- The tail `H_j = p^j ℤ_[p]`, written multiplicatively (for Haar averages and characters). -/
def PadicTail (p : ℕ) [Fact p.Prime] (j : ℕ) : Type :=
  Multiplicative (padicPowerSubgroup p j)

namespace PadicTail

variable {p : ℕ} [Fact p.Prime] {j : ℕ}

instance : CommGroup (PadicTail p j) := inferInstanceAs (CommGroup (Multiplicative _))

instance : TopologicalSpace (PadicTail p j) :=
  inferInstanceAs (TopologicalSpace (Multiplicative _))

instance : IsTopologicalGroup (PadicTail p j) :=
  inferInstanceAs (IsTopologicalGroup (Multiplicative (padicPowerSubgroup p j)))

instance : CompactSpace (PadicTail p j) :=
  haveI : CompactSpace (padicPowerSubgroup p j) :=
    isCompact_iff_compactSpace.1 (padicPowerSubgroup_isClosed j).isCompact
  inferInstanceAs (CompactSpace (Multiplicative (padicPowerSubgroup p j)))

instance : T2Space (PadicTail p j) :=
  inferInstanceAs (T2Space (Multiplicative (padicPowerSubgroup p j)))

instance : MeasurableSpace (PadicTail p j) := borel _

instance : BorelSpace (PadicTail p j) := ⟨rfl⟩

/-- The underlying p-adic integer. -/
def val (g : PadicTail p j) : ℤ_[p] :=
  ((Multiplicative.toAdd g : padicPowerSubgroup p j) : ℤ_[p])

/-- The element of the tail given by `a ∈ H_j`. -/
def mk (a : ℤ_[p]) (ha : a ∈ padicPowerSubgroup p j) : PadicTail p j :=
  Multiplicative.ofAdd ⟨a, ha⟩

@[simp]
theorem val_mk (a : ℤ_[p]) (ha : a ∈ padicPowerSubgroup p j) : (mk a ha).val = a := rfl

theorem val_mem (g : PadicTail p j) : g.val ∈ padicPowerSubgroup p j :=
  (Multiplicative.toAdd g).2

@[simp]
theorem val_mul (g h : PadicTail p j) : (g * h).val = g.val + h.val := rfl

@[simp]
theorem val_one : (1 : PadicTail p j).val = 0 := rfl

theorem continuous_val : Continuous (val : PadicTail p j → ℤ_[p]) := continuous_subtype_val

instance {X : Type*} [AddAction ℤ_[p] X] : MulAction (PadicTail p j) X where
  smul g x := g.val +ᵥ x
  one_smul := zero_vadd ℤ_[p]
  mul_smul g h x := add_vadd g.val h.val x

theorem smul_def {X : Type*} [AddAction ℤ_[p] X] (g : PadicTail p j) (x : X) :
    g • x = g.val +ᵥ x := rfl

instance {X : Type*} [TopologicalSpace X] [AddAction ℤ_[p] X] [ContinuousVAdd ℤ_[p] X] :
    ContinuousSMul (PadicTail p j) X :=
  ⟨(continuous_val.comp continuous_fst).vadd continuous_snd⟩

end PadicTail

section Character

variable {p : ℕ} [Fact p.Prime] {j : ℕ}

instance (p : ℕ) [Fact p.Prime] (k : ℕ) : NeZero (p ^ k) :=
  ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩

/-- The character `ℤ_[p] → ℤ/p^{j+1} → S¹`. On `H_j` it is the quotient character
`χ : H_j → H_j/H_{j+1} ≅ C_p ⊆ S¹` of (7.7), see `padicChar_eq_one_iff` and
`padicChar_pow_eq_one`. -/
def padicChar (p : ℕ) [Fact p.Prime] (j : ℕ) : AddChar ℤ_[p] Circle :=
  ZMod.toCircle.compAddMonoidHom (PadicInt.toZModPow (j + 1)).toAddMonoidHom

theorem padicChar_eq_one_iff {a : ℤ_[p]} :
    padicChar p j a = 1 ↔ a ∈ padicPowerSubgroup p (j + 1) := by
  have h : padicChar p j a = ZMod.toCircle (PadicInt.toZModPow (j + 1) a) := rfl
  rw [h, ← AddChar.map_zero_eq_one (ZMod.toCircle (N := p ^ (j + 1))),
    (ZMod.injective_toCircle (N := p ^ (j + 1))).eq_iff,
    ← RingHom.mem_ker, PadicInt.ker_toZModPow]
  rfl

/-- On `H_j` the character takes values in the `p`-th roots of unity. -/
theorem padicChar_pow_eq_one {a : ℤ_[p]} (ha : a ∈ padicPowerSubgroup p j) :
    padicChar p j a ^ p = 1 := by
  rw [← AddChar.map_nsmul_eq_pow, padicChar_eq_one_iff]
  change a ∈ Ideal.span _ at ha
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  change _ ∈ Ideal.span _
  refine Ideal.mem_span_singleton'.2 ⟨c, ?_⟩
  rw [nsmul_eq_mul]
  ring

theorem continuous_padicChar : Continuous (padicChar p j) := by
  refine continuous_iff_continuousAt.2 fun a => ?_
  have hU : {b : ℤ_[p] | b - a ∈ padicPowerSubgroup p (j + 1)} ∈ 𝓝 a :=
    ((padicPowerSubgroup_isOpen (j + 1)).preimage (continuous_id.sub continuous_const)).mem_nhds
      (by simp [(padicPowerSubgroup p (j + 1)).zero_mem])
  refine (continuousAt_const (y := padicChar p j a)).congr
    (Filter.eventuallyEq_of_mem hU fun b hb => ?_)
  change padicChar p j a = padicChar p j b
  rw [show b = a + (b - a) by abel, AddChar.map_add_eq_mul, padicChar_eq_one_iff.2 hb, mul_one]

/-- `C_p` acts freely on `T` by scalars: `χ(h) v = v` with `v ≠ 0` forces `h ∈ H_{j+1}`. -/
theorem mem_of_padicChar_smul_eq {m : ℕ} {a : ℤ_[p]} {v : EuclideanSpace ℂ (Fin m)}
    (hv : v ≠ 0) (h : (padicChar p j a : ℂ) • v = v) : a ∈ padicPowerSubgroup p (j + 1) := by
  rw [← padicChar_eq_one_iff]
  have h1 : ((padicChar p j a : ℂ) - 1) • v = 0 := by rw [sub_smul, h, one_smul, sub_self]
  rcases smul_eq_zero.1 h1 with h2 | h2
  · exact Circle.coe_injective (by rw [Circle.coe_one]; exact sub_eq_zero.1 h2)
  · exact absurd h2 hv

/-- The quotient character on the multiplicative tail, for the character detector. -/
def tailChar (p : ℕ) [Fact p.Prime] (j : ℕ) : PadicTail p j →* Circle where
  toFun g := padicChar p j g.val
  map_one' := by rw [PadicTail.val_one, AddChar.map_zero_eq_one]
  map_mul' g h := by rw [PadicTail.val_mul, AddChar.map_add_eq_mul]

theorem continuous_tailChar : Continuous (tailChar p j) :=
  continuous_padicChar.comp PadicTail.continuous_val

end Character

/-! ### Charts and uniform chart displacement -/

section Chart

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {M : Type*} [TopologicalSpace M]

/-- A chart centred at `x₀` whose target contains `B(0,4)` (L460). -/
theorem exists_chart_ball [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (x₀ : M) :
    ∃ φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
      x₀ ∈ φ.source ∧ φ x₀ = 0 ∧ ball 0 4 ⊆ φ.target := by
  set φ₀ := chartAt (EuclideanSpace ℝ (Fin n)) x₀
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.1 φ₀.open_target (φ₀ x₀) (φ₀.map_source (mem_chart_source _ x₀))
  have hc : (4 / ε : ℝ) ≠ 0 := by positivity
  let A : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n) :=
    (Homeomorph.addRight (-φ₀ x₀)).trans (Homeomorph.smulOfNeZero (4 / ε) hc)
  have hA : ∀ w, A w = (4 / ε) • (w - φ₀ x₀) := fun w => by
    simp [A, sub_eq_add_neg]
  refine ⟨φ₀.transHomeomorph A, mem_chart_source _ x₀, by simp [hA], fun v hv => ?_⟩
  change A.symm v ∈ φ₀.target
  apply hball
  have h1 := hA (A.symm v)
  rw [Homeomorph.apply_symm_apply] at h1
  have h2 := congrArg norm h1
  rw [norm_smul, Real.norm_of_nonneg (by positivity)] at h2
  rw [mem_ball, dist_eq_norm]
  rw [mem_ball_zero_iff, h2] at hv
  have : 4 / ε * ‖A.symm v - φ₀ x₀‖ = 4 * (‖A.symm v - φ₀ x₀‖ / ε) := by ring
  rw [this] at hv
  have h3 : ‖A.symm v - φ₀ x₀‖ / ε < 1 := by linarith
  rwa [div_lt_one hε] at h3

/-- Joint continuity in a chart: on a compact subset of the chart domain, small group elements
keep points in the chart and move them less than `ε` in chart coordinates. -/
theorem exists_nhds_chart_displacement [AddAction ℤ_[p] M] [ContinuousVAdd ℤ_[p] M]
    (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) {K : Set M} (hK : IsCompact K)
    (hKs : K ⊆ φ.source) {ε : ℝ} (hε : 0 < ε) :
    ∃ V ∈ 𝓝 (0 : ℤ_[p]), ∀ g ∈ V, ∀ x ∈ K,
      g +ᵥ x ∈ φ.source ∧ ‖φ (g +ᵥ x) - φ x‖ < ε := by
  set W : Set (ℤ_[p] × M) := {q | q.2 ∈ φ.source ∧ q.1 +ᵥ q.2 ∈ φ.source}
  have hW : IsOpen W :=
    (φ.open_source.preimage continuous_snd).inter (φ.open_source.preimage continuous_vadd)
  have hcont : ContinuousOn (fun q : ℤ_[p] × M => φ (q.1 +ᵥ q.2) - φ q.2) W :=
    (φ.continuousOn.comp continuous_vadd.continuousOn fun q hq => hq.2).sub
      (φ.continuousOn.comp continuous_snd.continuousOn fun q hq => hq.1)
  have hS := hcont.isOpen_inter_preimage hW (isOpen_ball (x := 0) (ε := ε))
  have hsub : ({0} : Set ℤ_[p]) ×ˢ K ⊆
      W ∩ (fun q : ℤ_[p] × M => φ (q.1 +ᵥ q.2) - φ q.2) ⁻¹' ball 0 ε := by
    rintro ⟨g, x⟩ ⟨hg, hx⟩
    rw [mem_singleton_iff] at hg
    subst hg
    simp [W, hKs hx, hε]
  obtain ⟨V, U, hV, -, hV0, hKU, hVU⟩ := generalized_tube_lemma isCompact_singleton hK hS hsub
  refine ⟨V, hV.mem_nhds (hV0 rfl), fun g hg x hx => ?_⟩
  have h := hVU (mk_mem_prod hg (hKU hx))
  exact ⟨h.1.2, by simpa using h.2⟩

end Chart

/-! ### The chart, the subgroup `H` and the averaged coordinate (7.1)–(7.3) -/

/-- The data `(x₀, φ, H = H_j, D)` of L458–466. -/
structure ChartData (p : ℕ) [Fact p.Prime] (n : ℕ) (M : Type*) [TopologicalSpace M]
    [AddAction ℤ_[p] M] where
  /-- A free point (L458). -/
  x₀ : M
  stabilizer_x₀ : AddAction.stabilizer ℤ_[p] x₀ = ⊥
  /-- A chart centred at `x₀` whose image contains `B(0,4)` (L460). -/
  φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))
  x₀_mem_source : x₀ ∈ φ.source
  φ_x₀ : φ x₀ = 0
  ball_subset_target : ball 0 4 ⊆ φ.target
  /-- `H = H_j` and the displacement bound `D` of (7.1). -/
  j : ℕ
  D : ℝ
  D_nonneg : 0 ≤ D
  D_lt : D < 1 / 64
  vadd_mem_source : ∀ h ∈ padicPowerSubgroup p j, ∀ x ∈ φ.source, ‖φ x‖ ≤ 2 →
    h +ᵥ x ∈ φ.source
  displacement_le : ∀ h ∈ padicPowerSubgroup p j, ∀ x ∈ φ.source, ‖φ x‖ ≤ 2 →
    ‖φ (h +ᵥ x) - φ x‖ ≤ D

namespace ChartData

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {M : Type*} [TopologicalSpace M] [AddAction ℤ_[p] M]
  (c : ChartData p n M)

/-- `H = H_j = p^j ℤ_[p]`. -/
abbrev H : AddSubgroup ℤ_[p] := padicPowerSubgroup p c.j

/-- `H' = H_{j+1}`. -/
abbrev H' : AddSubgroup ℤ_[p] := padicPowerSubgroup p (c.j + 1)

/-- The fixed set `Fix(H)`. -/
abbrev fixH : Set M := AddAction.fixedPoints (padicPowerSubgroup p c.j) M

/-- `Ω = H · φ⁻¹ B(0,2)` (L468). -/
def Ω : Set M := {x | ∃ h ∈ c.H, h +ᵥ x ∈ c.φ.source ∧ ‖c.φ (h +ᵥ x)‖ < 2}

/-- The averaged coordinate `F₀(x) = ∫_H φ(hx) dμ(h)` for normalized Haar measure (7.2). -/
def F₀ (x : M) : EuclideanSpace ℝ (Fin n) :=
  ∫ g, c.φ (g • x) ∂normalizedCompactHaar (PadicTail p c.j)

/-- The fixed compact chart saturation `H · φ⁻¹ B̄(0,2)` (L538). -/
def Q : Set M :=
  (fun q : ℤ_[p] × M => q.1 +ᵥ q.2) '' ((c.H : Set ℤ_[p]) ×ˢ (c.φ.source ∩ c.φ ⁻¹' closedBall 0 2))

/-- The carrier `Z⁺ = F₀⁻¹ B̄(0,ρ₊)` (7.4), `F₀` being defined on `Ω`. -/
def carrier (ρplus : ℝ) : Set M := c.Ω ∩ c.F₀ ⁻¹' closedBall 0 ρplus

theorem mem_target_of_norm_lt {v : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hv : ‖v‖ ≤ r)
    (hr : r < 4) : v ∈ c.φ.target :=
  c.ball_subset_target (mem_ball_zero_iff.2 (hv.trans_lt hr))

theorem isCompact_chartBall {r : ℝ} (hr : r < 4) :
    IsCompact (c.φ.source ∩ c.φ ⁻¹' closedBall 0 r) := by
  have hsub : closedBall (0 : EuclideanSpace ℝ (Fin n)) r ⊆ c.φ.target := fun v hv =>
    c.mem_target_of_norm_lt (mem_closedBall_zero_iff.1 hv) hr
  rw [← c.φ.symm_image_eq_source_inter_preimage hsub]
  exact (isCompact_closedBall 0 r).image_of_continuousOn (c.φ.continuousOn_symm.mono hsub)

/-- Every point of `Ω` lies, together with its whole `H`-orbit, within `D` of one point of
`φ⁻¹ B(0,2)`. -/
theorem exists_near {x : M} (hx : x ∈ c.Ω) :
    ∃ x₁ ∈ c.φ.source, ‖c.φ x₁‖ < 2 ∧
      ∀ h ∈ c.H, h +ᵥ x ∈ c.φ.source ∧ ‖c.φ (h +ᵥ x) - c.φ x₁‖ ≤ c.D := by
  obtain ⟨h₁, hh₁, hs, hlt⟩ := hx
  refine ⟨h₁ +ᵥ x, hs, hlt, fun h hh => ?_⟩
  have he : h +ᵥ x = (h - h₁) +ᵥ (h₁ +ᵥ x) := by rw [vadd_vadd, sub_add_cancel]
  have hmem : h - h₁ ∈ c.H := c.H.sub_mem hh hh₁
  rw [he]
  exact ⟨c.vadd_mem_source _ hmem _ hs hlt.le, c.displacement_le _ hmem _ hs hlt.le⟩

theorem vadd_mem_source_of_mem_Ω {x : M} (hx : x ∈ c.Ω) {h : ℤ_[p]} (hh : h ∈ c.H) :
    h +ᵥ x ∈ c.φ.source := by
  obtain ⟨x₁, -, -, hx₁⟩ := c.exists_near hx
  exact (hx₁ h hh).1

theorem Ω_subset_source : c.Ω ⊆ c.φ.source := fun x hx => by
  simpa using c.vadd_mem_source_of_mem_Ω hx c.H.zero_mem

/-- On `Ω` the displacement of `H` is at most `2D` (L468). -/
theorem displacement_Ω {x : M} (hx : x ∈ c.Ω) {h : ℤ_[p]} (hh : h ∈ c.H) :
    ‖c.φ (h +ᵥ x) - c.φ x‖ ≤ 2 * c.D := by
  obtain ⟨x₁, -, -, hx₁⟩ := c.exists_near hx
  have h1 := (hx₁ h hh).2
  have h2 := (hx₁ 0 c.H.zero_mem).2
  rw [zero_vadd] at h2
  calc ‖c.φ (h +ᵥ x) - c.φ x‖ = ‖(c.φ (h +ᵥ x) - c.φ x₁) - (c.φ x - c.φ x₁)‖ := by
        congr 1; abel
    _ ≤ ‖c.φ (h +ᵥ x) - c.φ x₁‖ + ‖c.φ x - c.φ x₁‖ := norm_sub_le _ _
    _ ≤ 2 * c.D := by linarith

/-- `φ(Ω) ⊆ B(0, 2 + D)` (L468). -/
theorem norm_lt_of_mem_Ω {x : M} (hx : x ∈ c.Ω) : ‖c.φ x‖ < 2 + c.D := by
  obtain ⟨x₁, -, hx₁2, hx₁⟩ := c.exists_near hx
  have h2 := (hx₁ 0 c.H.zero_mem).2
  rw [zero_vadd] at h2
  calc ‖c.φ x‖ = ‖(c.φ x - c.φ x₁) + c.φ x₁‖ := by rw [sub_add_cancel]
    _ ≤ ‖c.φ x - c.φ x₁‖ + ‖c.φ x₁‖ := norm_add_le _ _
    _ < 2 + c.D := by linarith

theorem mem_Ω_of_norm_lt {x : M} (hx : x ∈ c.φ.source) (h2 : ‖c.φ x‖ < 2) : x ∈ c.Ω :=
  ⟨0, c.H.zero_mem, by rwa [zero_vadd], by rwa [zero_vadd]⟩

/-- `Ω` is `H`-invariant. -/
theorem vadd_mem_Ω_iff {h : ℤ_[p]} (hh : h ∈ c.H) {x : M} : h +ᵥ x ∈ c.Ω ↔ x ∈ c.Ω := by
  constructor
  · rintro ⟨h₁, hh₁, hs, hlt⟩
    refine ⟨h₁ + h, c.H.add_mem hh₁ hh, ?_, ?_⟩ <;> rwa [← vadd_vadd]
  · rintro ⟨h₁, hh₁, hs, hlt⟩
    refine ⟨h₁ - h, c.H.sub_mem hh₁ hh, ?_, ?_⟩ <;> rwa [vadd_vadd, sub_add_cancel]

theorem isOpen_Ω [ContinuousVAdd ℤ_[p] M] : IsOpen c.Ω := by
  have he : c.Ω = ⋃ h ∈ c.H, (h +ᵥ ·) ⁻¹' (c.φ.source ∩ c.φ ⁻¹' ball 0 2) := by
    ext x
    simp only [Ω, mem_ofPred_eq, mem_iUnion, mem_preimage, mem_inter_iff, mem_ball_zero_iff,
      exists_prop]
  rw [he]
  exact isOpen_biUnion fun h _ =>
    (c.φ.isOpen_inter_preimage isOpen_ball).preimage (continuous_const_vadd h)

theorem Ω_subset_Q : c.Ω ⊆ c.Q := by
  rintro x ⟨h, hh, hs, hlt⟩
  exact ⟨(-h, h +ᵥ x), ⟨c.H.neg_mem hh, hs, mem_closedBall_zero_iff.2 hlt.le⟩,
    by simp [vadd_vadd]⟩

theorem Q_subset_source : c.Q ⊆ c.φ.source := by
  rintro _ ⟨⟨h, x⟩, ⟨hh, hs, hx⟩, rfl⟩
  exact c.vadd_mem_source h hh x hs (mem_closedBall_zero_iff.1 hx)

theorem isCompact_Q [ContinuousVAdd ℤ_[p] M] : IsCompact c.Q :=
  ((padicPowerSubgroup_isClosed c.j).isCompact.prod
    (c.isCompact_chartBall (by norm_num))).image continuous_vadd

theorem symm_mem_Ω {v : EuclideanSpace ℝ (Fin n)} (hv : ‖v‖ < 2) : c.φ.symm v ∈ c.Ω := by
  have ht := c.mem_target_of_norm_lt hv.le (by norm_num)
  exact c.mem_Ω_of_norm_lt (c.φ.map_target ht) (by rwa [c.φ.right_inv ht])

/-- The free point is not fixed by `H`. -/
theorem x₀_notMem_fixH : c.x₀ ∉ c.fixH := by
  intro hfix
  have hp : ((p : ℤ_[p]) ^ c.j) ∈ c.H := Ideal.mem_span_singleton_self _
  have hmem : ((p : ℤ_[p]) ^ c.j) ∈ AddAction.stabilizer ℤ_[p] c.x₀ :=
    AddAction.mem_fixedPoints.1 hfix ⟨_, hp⟩
  rw [c.stabilizer_x₀, AddSubgroup.mem_bot] at hmem
  exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) hmem

theorem isClosed_fixH [T2Space M] [ContinuousVAdd ℤ_[p] M] : IsClosed c.fixH := by
  have he : c.fixH = ⋂ h : c.H, {x : M | (h : ℤ_[p]) +ᵥ x = x} := by
    ext x
    simp only [AddAction.mem_fixedPoints, mem_iInter, mem_ofPred_eq]
    rfl
  rw [he]
  exact isClosed_iInter fun h => isClosed_eq (continuous_const_vadd _) continuous_id

/-! #### The averaged coordinate -/

theorem continuous_φ_smul [ContinuousVAdd ℤ_[p] M] {x : M} (hx : x ∈ c.Ω) :
    Continuous fun g : PadicTail p c.j => c.φ (g • x) :=
  c.φ.continuousOn.comp_continuous (continuous_id.smul continuous_const) fun g =>
    c.vadd_mem_source_of_mem_Ω hx g.val_mem

theorem integrable_φ_smul [ContinuousVAdd ℤ_[p] M] {x : M} (hx : x ∈ c.Ω) :
    Integrable (fun g : PadicTail p c.j => c.φ (g • x)) (normalizedCompactHaar _) := by
  have hi := ContinuousOn.integrableOn_compact (μ := normalizedCompactHaar (PadicTail p c.j))
    isCompact_univ (c.continuous_φ_smul hx).continuousOn
  simpa only [IntegrableOn, Measure.restrict_univ] using hi

/-- Haar invariance: `F₀(h₀ x) = F₀(x)` for `h₀ ∈ H` (L479). -/
theorem F₀_vadd {h : ℤ_[p]} (hh : h ∈ c.H) (x : M) : c.F₀ (h +ᵥ x) = c.F₀ x := by
  have hx : h +ᵥ x = PadicTail.mk h hh • x := rfl
  simp only [F₀, hx, smul_smul]
  exact integral_mul_right_eq_self (fun g => c.φ (g • x)) (PadicTail.mk h hh)

/-- `F₀(x) = φ(x)` on `Fix(H)` (7.3). -/
theorem F₀_of_mem_fixH {x : M} (hx : x ∈ c.fixH) : c.F₀ x = c.φ x := by
  have h : ∀ g : PadicTail p c.j, c.φ (g • x) = c.φ x := fun g =>
    congrArg c.φ (AddAction.mem_fixedPoints.1 hx (Multiplicative.toAdd g))
  simp [F₀, h]

/-- `|F₀(x) - x| ≤ 2D` on `Ω` (7.3). -/
theorem norm_F₀_sub_le [ContinuousVAdd ℤ_[p] M] {x : M} (hx : x ∈ c.Ω) :
    ‖c.F₀ x - c.φ x‖ ≤ 2 * c.D := by
  have he : c.F₀ x - c.φ x =
      ∫ g, (c.φ (g • x) - c.φ x) ∂normalizedCompactHaar (PadicTail p c.j) := by
    rw [integral_sub (c.integrable_φ_smul hx) (integrable_const _)]
    simp [F₀]
  rw [he]
  calc _ ≤ 2 * c.D * (normalizedCompactHaar (PadicTail p c.j)).real univ :=
        norm_integral_le_of_norm_le_const
          (Eventually.of_forall fun g => c.displacement_Ω hx g.val_mem)
    _ = 2 * c.D := by simp

/-- `F₀` is continuous on `Ω` (L477). -/
theorem continuousOn_F₀ [ContinuousVAdd ℤ_[p] M] [LocallyCompactSpace M]
    [FirstCountableTopology M] : ContinuousOn c.F₀ c.Ω := by
  rw [continuousOn_iff_continuous_domRestrict]
  haveI : LocallyCompactSpace c.Ω := c.isOpen_Ω.locallyCompactSpace
  have hf : Continuous fun q : c.Ω × PadicTail p c.j => c.φ (q.2 • (q.1 : M)) :=
    c.φ.continuousOn.comp_continuous
      (continuous_snd.smul (continuous_subtype_val.comp continuous_fst)) fun q =>
        c.vadd_mem_source_of_mem_Ω q.1.2 q.2.val_mem
  have h := continuous_parametric_integral_of_continuous
    (μ := normalizedCompactHaar (PadicTail p c.j))
    (f := fun (x : c.Ω) (g : PadicTail p c.j) => c.φ (g • (x : M))) hf isCompact_univ
  exact (by simpa only [Measure.restrict_univ] using h :
    Continuous fun x : c.Ω => ∫ g, c.φ (g • (x : M)) ∂normalizedCompactHaar (PadicTail p c.j))

theorem norm_le_of_mem_carrier [ContinuousVAdd ℤ_[p] M] {ρplus : ℝ} {x : M}
    (hx : x ∈ c.carrier ρplus) : ‖c.φ x‖ ≤ ρplus + 2 * c.D := by
  have h1 := c.norm_F₀_sub_le hx.1
  have h2 := mem_closedBall_zero_iff.1 hx.2
  calc ‖c.φ x‖ = ‖c.F₀ x - (c.F₀ x - c.φ x)‖ := by rw [sub_sub_cancel]
    _ ≤ ‖c.F₀ x‖ + ‖c.F₀ x - c.φ x‖ := norm_sub_le _ _
    _ ≤ ρplus + 2 * c.D := by linarith

/-- `Z⁺` is compact (L488). -/
theorem isCompact_carrier [T2Space M] [ContinuousVAdd ℤ_[p] M] [LocallyCompactSpace M]
    [FirstCountableTopology M] {ρplus : ℝ} (hρ : ρplus < 1 / 4) :
    IsCompact (c.carrier ρplus) := by
  have hD := c.D_lt
  have hD0 := c.D_nonneg
  set K := c.φ.source ∩ c.φ ⁻¹' closedBall 0 (ρplus + 2 * c.D)
  have hK : IsCompact K := c.isCompact_chartBall (by linarith)
  have hKΩ : K ⊆ c.Ω := fun x hx =>
    c.mem_Ω_of_norm_lt hx.1 ((mem_closedBall_zero_iff.1 hx.2).trans_lt (by linarith))
  have he : c.carrier ρplus = K ∩ c.F₀ ⁻¹' closedBall 0 ρplus := by
    ext x
    refine ⟨fun hx => ⟨⟨c.Ω_subset_source hx.1, mem_closedBall_zero_iff.2
      (c.norm_le_of_mem_carrier hx)⟩, hx.2⟩, fun hx => ⟨hKΩ hx.1, hx.2⟩⟩
  rw [he]
  exact hK.of_isClosed_subset ((c.continuousOn_F₀.mono hKΩ).preimage_isClosed_of_isClosed
    hK.isClosed isClosed_closedBall) inter_subset_left

/-- `Z⁺` is `H`-invariant (L488). -/
theorem vadd_mem_carrier_iff {ρplus : ℝ} {h : ℤ_[p]} (hh : h ∈ c.H) {x : M} :
    h +ᵥ x ∈ c.carrier ρplus ↔ x ∈ c.carrier ρplus := by
  simp only [carrier, mem_inter_iff, mem_preimage, c.vadd_mem_Ω_iff hh, c.F₀_vadd hh]

/-- `Z⁺` misses `Fix(H)` once `B̄(0,ρ₊)` misses `φ(Fix H)` (L488). -/
theorem notMem_fixH_of_mem_carrier {ρplus : ℝ}
    (hρ : ∀ x ∈ c.φ.source, ‖c.φ x‖ ≤ ρplus → x ∉ c.fixH) {x : M}
    (hx : x ∈ c.carrier ρplus) : x ∉ c.fixH := fun hfix =>
  hρ x (c.Ω_subset_source hx.1)
    (by rw [← c.F₀_of_mem_fixH hfix]; exact mem_closedBall_zero_iff.1 hx.2) hfix

/-- A radius `ρ₊ < 1/4` with `B̄(0,ρ₊)` missing `φ(Fix H)` (L483). -/
theorem exists_ρplus [T2Space M] [ContinuousVAdd ℤ_[p] M] :
    ∃ ρplus : ℝ, 0 < ρplus ∧ ρplus < 1 / 4 ∧
      ∀ x ∈ c.φ.source, ‖c.φ x‖ ≤ ρplus → x ∉ c.fixH := by
  have h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ c.φ.target :=
    c.mem_target_of_norm_lt (by simp) (by norm_num : (0 : ℝ) < 4)
  have hU : c.φ.symm ⁻¹' (c.fixH)ᶜ ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n)) := by
    apply (c.φ.continuousAt_symm h0).preimage_mem_nhds
    rw [← c.φ_x₀, c.φ.left_inv c.x₀_mem_source]
    exact c.isClosed_fixH.isOpen_compl.mem_nhds c.x₀_notMem_fixH
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  refine ⟨min (ε / 2) (1 / 8), by positivity,
    (min_le_right _ _).trans_lt (by norm_num), fun x hx hxρ hfix => ?_⟩
  have hxε : c.φ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) ε :=
    mem_ball_zero_iff.2 (hxρ.trans_lt ((min_le_left _ _).trans_lt (half_lt_self hε)))
  have h := hball hxε
  rw [mem_preimage, c.φ.left_inv hx] at h
  exact h hfix

end ChartData

/-! ### The equivariant sphere map (7.7) -/

section SphereMap

variable {p : ℕ} [Fact p.Prime] {M : Type*} [TopologicalSpace M] [AddAction ℤ_[p] M]

/-- **(7.7)**: on a compact set missing `Fix(H_j)`, there is a continuous map to the unit sphere
`T = S^{2m-1} ⊆ ℂ^m` with `ρ̃(hx) = χ(h) ρ̃(x)`, defined and continuous on an open neighbourhood.
Stabilizers on the set lie in `H_{j+1}` (L509, `padicStabilizer_le_nextPower_of_not_fixed`), so the
repo's character detector applies; normalizing its coordinates gives `ρ̃`. -/
theorem exists_equivariant_sphere_map [T2Space M] [SecondCountableTopology M]
    [LocallyCompactSpace M] [ContinuousVAdd ℤ_[p] M] (j : ℕ) {K : Set M} (hK : IsCompact K)
    (hfix : ∀ x ∈ K, x ∉ AddAction.fixedPoints (padicPowerSubgroup p j) M) :
    ∃ (m : ℕ) (ρt : M → EuclideanSpace ℂ (Fin m)),
      (∃ U, IsOpen U ∧ K ⊆ U ∧ ContinuousOn ρt U ∧ ∀ x ∈ U, ‖ρt x‖ = 1) ∧
      ∀ h ∈ padicPowerSubgroup p j, ∀ x, ρt (h +ᵥ x) = (padicChar p j h : ℂ) • ρt x := by
  classical
  letI : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  have hstab : ∀ x ∈ K, ∀ g : PadicTail p j, g • x = x → tailChar p j g = 1 := fun x hx g hg =>
    padicChar_eq_one_iff.2 (padicStabilizer_le_nextPower_of_not_fixed j x (hfix x hx)
      (show g.val +ᵥ x = x from hg))
  obtain ⟨Fs, hequiv, hnz⟩ :=
    exists_finite_character_detector (tailChar p j) continuous_tailChar hK hstab
  let e := Fs.equivFin
  let Fv : M → EuclideanSpace ℂ (Fin Fs.card) := fun x =>
    WithLp.toLp 2 fun i => ((e.symm i : Fs) : C(M, ℂ)) x
  have hFv : Continuous Fv := (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun i => ((e.symm i : Fs) : C(M, ℂ)).continuous)
  have hFv_vadd : ∀ h ∈ padicPowerSubgroup p j, ∀ x, Fv (h +ᵥ x) = (padicChar p j h : ℂ) • Fv x := by
    intro h hh x
    ext i
    exact hequiv _ (e.symm i).2 (PadicTail.mk h hh) x
  have hnorm : ∀ h ∈ padicPowerSubgroup p j, ∀ x, ‖Fv (h +ᵥ x)‖ = ‖Fv x‖ := fun h hh x => by
    rw [hFv_vadd h hh x, norm_smul, Circle.norm_coe, one_mul]
  refine ⟨Fs.card, fun x => ((‖Fv x‖⁻¹ : ℝ) : ℂ) • Fv x,
    ⟨{x | Fv x ≠ 0}, isOpen_ne_fun hFv continuous_const, fun x hx => ?_, ?_, fun x hx => ?_⟩,
    fun h hh x => ?_⟩
  · obtain ⟨F, hF, hFx⟩ := hnz x hx
    intro h0
    apply hFx
    have := congrArg (fun w : EuclideanSpace ℂ (Fin Fs.card) => w (e ⟨F, hF⟩)) h0
    simpa [Fv] using this
  · exact (Complex.continuous_ofReal.comp_continuousOn
      (hFv.norm.continuousOn.inv₀ fun x hx => norm_ne_zero_iff.2 hx)).smul hFv.continuousOn
  · rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hx)]
  · beta_reduce
    rw [hnorm h hh x, hFv_vadd h hh x, smul_comm]

end SphereMap

end HSFormal
