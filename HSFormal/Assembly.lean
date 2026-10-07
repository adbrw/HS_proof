import HSFormal.AlgebraicReduction
import HSFormal.BoundaryReduction
import HSFormal.Integration
import HSFormal.LTheory.ConcreteL
import HSFormal.Montgomery
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.GroupTheory.PGroup

/-!
# Assembly: the top-down skeleton of the proof of `PadicExclusion`

* Part 1 (proved): the tail group `Tail = ℤ^ℕ/ℤ^(ℕ)` of (3.5) as `Filter.Germ atTop ℤ`,
  `divTail p = ∏ pℤ / ⊕ pℤ` of (12.2), sign tails (eventually `±1`, absorbing the boundary
  signs `bsign`), and the contradiction of §12 (`notMem_divTail_of_isSignTail`,
  `false_of_section12`).
* Part 2: `ControlData` (the data `T, C_p, Sⁿ, y, r, R` of §7 used by §§8–12), the categories
  `ℬ_{1,Z}(T × Sⁿ)`, `ℬ_{G,Z}(T × Sⁿ)`, `𝒜_1(Sⁿ)`, `ℬ_{1,Z₀}(Sⁿ)` with `Ind`, `Res`, `push`,
  `proj`, `TailGroups`, and `SheetData`, the hypotheses of the crux (★).
* Part 3: the remaining steps as `Prop`s; Part 4 (proved): `padicExclusion_of_steps`,
  `hilbertSmith_of_steps`.

L-theory enters through two interfaces, kept abstract so that nothing depends on the uncommitted
`LTheory.LowerLTheory`: `FibreSignature` (intended `σ_tail ∘ Δ_1 ∘ 𝕃.cls`) and `ManifoldGerm`
(intended: the class of the cubical torus model `Tⁿ ⊗ CPcell` of `W = Sⁿ × ℂP²`). All steps except
`ClassConstruction`, `ClassConstruction'` quantify over arbitrary control data with `p` prime,
which exist (`ControlData`, `TailGroups.const`), so they are not vacuous; `ClassConstruction` is
about the hypothetical action. Degenerate interfaces do not discharge all steps: `σ = 0` satisfies
`TransferDivisibility` and `CruxStar` (`transferDivisibility_zero`, `cruxStar_zero`) but not
`PinchSignature` (`not_pinchSignature_zero`), nor does the germ `0`
(`not_pinchSignature_zero_germ`).

| Step | Paper | assembly-plan steps / tasks |
|---|---|---|
| `ClassConstruction` (`ClassConstruction'`) | §§7–9, Prop. 9.2 | S1–S3 / 2, 7, then C5–C6 |
| `InducedClass` (`InducedClassWeak`) | Lemmas 5.1–5.2, (10.1)–(10.4) | S4–S6 / 3, 9 |
| `TransferDivisibility` | (11.2), (3.2), Prop. 3.2, Thm. 6.3 | S7–S9, S12b / 4, 5, 6, 8, 10 |
| `GermHomotopyInvariance` | Lemma 11.1, (11.3) | S10 / C7 |
| `PinchSignature` | Lemma 11.2, (11.4)–(11.5) | S11, S12a / C8, 4 |
| `FibreSignature`, `ManifoldGerm` | (11.1), (3.5); §8 | 6, 8; 7, C5 |

The glue uses the weak forms: `cruxStar_of_steps` and `padicExclusion_of_fine_steps` need only
`InducedClassWeak` (implied by `InducedClass`, `InducedClass.toWeak`), and
`padicExclusion_of_steps'` needs only `ClassConstruction'` (implied by `ClassConstruction`,
`classConstruction'_of`).
-/

noncomputable section

namespace HSFormal

open Filter

/-! ### Part 1: the tail group and the contradiction of §12 -/

/-- The tail group `ℤ^ℕ/ℤ^(ℕ)` of (3.5): integer sequences modulo eventual equality. -/
abbrev Tail : Type := Germ (atTop : Filter ℕ) ℤ

/-- `∏ pℤ / ⊕ pℤ ⊆ ℤ^ℕ/ℤ^(ℕ)` of (12.2): tails divisible by `p` at every large index. -/
def divTail (p : ℕ) : AddSubgroup Tail where
  carrier := {s | s.LiftPred fun z ↦ (p : ℤ) ∣ z}
  zero_mem' := Germ.liftPred_coe.mpr (Eventually.of_forall fun _ ↦ dvd_zero _)
  add_mem' {a b} := Germ.inductionOn₂ a b fun _ _ hf hg ↦ Germ.liftPred_coe.mpr <|
    (Germ.liftPred_coe.mp hf).and (Germ.liftPred_coe.mp hg) |>.mono fun _ h ↦ dvd_add h.1 h.2
  neg_mem' {a} := Germ.inductionOn a fun _ hf ↦ Germ.liftPred_coe.mpr <|
    (Germ.liftPred_coe.mp hf).mono fun _ h ↦ (dvd_neg).mpr h

theorem coe_mem_divTail {p : ℕ} {s : ℕ → ℤ} :
    (s : Tail) ∈ divTail p ↔ ∀ᶠ i in atTop, (p : ℤ) ∣ s i :=
  Germ.liftPred_coe

/-- A sign tail: eventually `±1` (the value (11.5) up to the boundary signs `bsign`). -/
def IsSignTail (s : Tail) : Prop :=
  s.LiftPred IsUnit

theorem isSignTail_coe {s : ℕ → ℤ} : IsSignTail (s : Tail) ↔ ∀ᶠ i in atTop, IsUnit (s i) :=
  Germ.liftPred_coe

/-- **§12** (l.1124–1128): a tail that is eventually `±1` is not divisible by `p`. -/
theorem notMem_divTail_of_isSignTail {p : ℕ} (hp : p.Prime) {s : Tail} (hs : IsSignTail s) :
    s ∉ divTail p := by
  induction s using Germ.inductionOn with
  | h s =>
  intro hdiv
  refine tail_divisibility_excludes_eventual_one p hp (fun i ↦ s i * s i) ?_ ?_
  · filter_upwards [coe_mem_divTail.mp hdiv] with i hi using dvd_mul_of_dvd_left hi _
  · filter_upwards [isSignTail_coe.mp hs] with i hi
    rcases Int.isUnit_iff.mp hi with h | h <;> simp [h]

/-- **§12 in abstract form** (blueprint s10-11 T1): `U_*𝔡 = [𝔪]` (10.4), `U_*Δ_T = Δ_1U_*`
(11.2), the trace convention `σ_tail = σ_tail ∘ U_*` ((3.2), Prop. 3.2), a sign tail
`σ_tail(Δ_1[𝔪])` ((11.3)–(11.5)) and Theorem 6.3 are contradictory. -/
theorem false_of_section12 {Ld Ls LG L1 : Type*} [AddCommGroup Ld] [AddCommGroup Ls]
    [AddCommGroup LG] [AddCommGroup L1] {p : ℕ} (hp : p.Prime) (U : Ld →+ Ls) (ΔT : Ld →+ LG)
    (Δ1 : Ls →+ L1) (U4 : LG →+ L1) (σG : LG →+ Tail) (σ1 : L1 →+ Tail)
    (h11_2 : ∀ x, U4 (ΔT x) = Δ1 (U x)) (htrace : ∀ a, σG a = σ1 (U4 a)) (𝔡 : Ld) (𝔪 : Ls)
    (h10_4 : U 𝔡 = 𝔪) (h11_5 : IsSignTail (σ1 (Δ1 𝔪))) (h6_3 : ∀ a, σG a ∈ divTail p) :
    False :=
  notMem_divTail_of_isSignTail hp h11_5 <| by
    simpa [htrace, h11_2, h10_4] using h6_3 (ΔT 𝔡)

/-! ### Part 2: control data and categories -/

open CategoryTheory LTheory AsymptoticObject Compression
open scoped Pointwise

/-- The control data of §7 on which §§8–12 depend (l.517–527): `T = S^{2m-1} ⊆ ℂ^m` with the
free scalar action of a subgroup `C_p ⊆ S¹` of order `p`, the round sphere `Sⁿ`, `n ≥ 1`, with
`y` antipodal to `∞`, and radii `0 < r < R < 2`: the cut ball `B(y, r)` of §11 and the exterior
`Z₀ = {d(y, ·) ≥ R}` of (7.8). The field `y` is redundant: `d(y, ∞) = 2` forces `y = 0`, the
antipode of `∞` for the round metric (`RoundSphere.dist_zero_infty`); it is kept to match the
paper's notation. -/
structure ControlData (p : ℕ) where
  m : ℕ
  n : ℕ
  n_pos : 0 < n
  Cp : Subgroup Circle
  card_Cp : Nat.card Cp = p
  y : RoundSphere n
  dist_y_infty : dist y RoundSphere.infty = 2
  r : ℝ
  R : ℝ
  r_pos : 0 < r
  r_lt_R : r < R
  R_lt : R < 2

namespace ControlData

variable {p : ℕ} (cd : ControlData p)

/-- The dimension `N = n + 4` of `W = Sⁿ × ℂP²` (§8). -/
abbrev N : ℤ := cd.n + 4

/-- The label space `T × Sⁿ`. -/
abbrev X : Type := LabelSpace cd.m cd.n

/-- `Z₀ = {z : d(y, z) ≥ R}` (7.8). -/
def Z₀ : Set (RoundSphere cd.n) := {z | cd.R ≤ dist cd.y z}

/-- `Z = T × Z₀` (7.8). -/
@[implicit_reducible] def Z : Set cd.X := Set.univ ×ˢ cd.Z₀

theorem smul_Z (h : cd.Cp) : h • cd.Z = cd.Z :=
  smul_univ_prod h _

variable {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)] (π : ∀ i, G i →* cd.Cp)

/-- `ℬ_{1,Z}(T × Sⁿ)`. -/
abbrev B1 : InvCat := exteriorInvCat (scalarHom cd.Cp) cd.Z

/-- `ℬ_{G,Z}(T × Sⁿ)`. -/
abbrev BG : InvCat := exteriorInvCat π cd.Z

/-- `𝒜_1(Sⁿ)`. -/
abbrev A1S : InvCat := asymptoticInvCat (scalarHom cd.Cp) (RoundSphere cd.n)

/-- `ℬ_{1,Z₀}(Sⁿ)`. -/
abbrev B1S : InvCat := exteriorInvCat (scalarHom cd.Cp) cd.Z₀

/-- Free sheets `Ind : ℬ_{1,Z} → ℬ_{G,Z}` (l.849). -/
@[implicit_reducible] def ind : cd.B1 ⟶ cd.BG π :=
  (freeSheetFiltrationHom (π := π) (X := cd.X) fun h ↦ cd.smul_Z h).quot

/-- Forgetting the action `Res : ℬ_{G,Z} → ℬ_{1,Z}` (l.70, l.129). -/
@[implicit_reducible] def res : cd.BG π ⟶ cd.B1 :=
  (forgetFiltrationHom π cd.Z).quot

/-- Forgetting `T`, `ℬ_{1,Z}(T × Sⁿ) → ℬ_{1,Z₀}(Sⁿ)` (l.873). -/
@[implicit_reducible] def push : cd.B1 ⟶ cd.B1S :=
  (pushFiltrationHom (j := Prod.snd) (fun _ _ ↦ rfl) uniformContinuous_snd
    fun _ hx ↦ hx.2).quot

/-- The exterior quotient `𝒜_1(Sⁿ) → ℬ_{1,Z₀}(Sⁿ)`. -/
def proj : cd.A1S ⟶ cd.B1S :=
  (supportKaroubiFiltration (scalarHom cd.Cp) cd.Z₀).proj

/-- `U = Res ≫ push` is the functor `U` of l.873. -/
theorem res_push_F : (cd.res π ≫ cd.push).F = ExteriorCategory.forget π cd.Z ⋙
    ExteriorCategory.push (j := Prod.snd) (fun _ _ ↦ rfl) uniformContinuous_snd
      fun _ hx ↦ hx.2 :=
  rfl

/-- The orbit representatives of the free-sheet object `Ind(A)` over a scalar object `A`. -/
abbrev sheetObj (A : cd.B1) : AsymptoticObject π cd.X :=
  freeSheetObj π A.as.as

/-- The sheet shift `u ⊗ R_{g⁻¹}` of a graph-type-`g` sequence as a morphism of `ℬ_{G,Z}`. -/
def shift {A A' : cd.B1} (g : ∀ i, G i) (u : ScalarFamily (cd.sheetObj π A) (cd.sheetObj π A'))
    (hu : IsGraphType g u) : (cd.ind π).F.obj A ⟶ (cd.ind π).F.obj A' :=
  ExteriorCategory.functor.map (AsymptoticCategory.functor.map
    (sheetHom (M := cd.sheetObj π A) (N := cd.sheetObj π A') g u hu))

/-- The scalar complex `(C, φ̂)` of the hypotheses of (★) with the chain maps `A_g` of (5.1),
(9.3): an honest (`p = 1`) Poincaré complex of `ℬ_{1,Z}(T × Sⁿ)` and, in each degree `r`, a
family `A_{g,i}` of matrices on the orbit representatives, of graph type `g` uniformly in
`g ∈ G_i` (§8, l.544–548), with `A_1 = 1` exactly, which after the sheet shift `s ↦ s g⁻¹`
commute with `d̂` in `ℬ_{G,Z}(T × Sⁿ)`, i.e. modulo actual exterior factorizations
((9.5), Lemma 9.1, l.746–749). Uniformity in `g` is the uniform graph type of the fixed family;
the equations are imposed for every sequence `g ∈ ∏ G_i`. -/
structure SheetAction where
  C : SymPoincare cd.B1.inv cd.N
  p_eq : C.p = 𝟙 C.C
  A : ∀ r : ℤ, GraphFamily G (cd.sheetObj π (C.C.X r)) (cd.sheetObj π (C.C.X r))
  hA : ∀ r, HasGraphType (fun _ ↦ id) (A r)
  A_one : ∀ r i, A r i 1 = 1
  comm : ∀ (g : ∀ i, G i) (r r' : ℤ),
    cd.shift π g (fun i ↦ A r i (g i)) ((hA r).apply g) ≫ ((cd.ind π).mapC C.C).d r r' =
      ((cd.ind π).mapC C.C).d r r' ≫ cd.shift π g (fun i ↦ A r' i (g i)) ((hA r').apply g)

namespace SheetAction

variable {cd π} (S : SheetAction cd π)

/-- `Ind C = C ⊗ ℚ[G]` with the sheet labels (10.1). -/
abbrev CG : ChainComplex (cd.BG π) ℤ := (cd.ind π).mapC S.C.C

/-- `Φ = φ̂ ⊗ 1` (10.2). -/
abbrev φG : dualComplex (cd.BG π).inv cd.N S.CG ⟶ S.CG := (cd.ind π).mapDual S.C.φ

/-- The chain map `A_g ⊗ R_{g⁻¹}` of `ℬ_{G,Z}(T × Sⁿ)`. -/
def act (g : ∀ i, G i) : S.CG ⟶ S.CG where
  f r := cd.shift π g (fun i ↦ S.A r i (g i)) ((S.hA r).apply g)
  comm' r r' _ := S.comm g r r'

end SheetAction

/-- **The hypotheses of (★)** (crux-review, end; Proposition 9.2, l.746–825): the scalar complex
and chain maps of `SheetAction`, with the first-order coherence of (5.1) in the form produced by
§§8–9: homotopies `B̂_{g,h} : A_g A_h ≃ A_{gh}` ((8.5), (9.4)) of graph type `gh` and
`V̂_g : A_g φ̂ ≃ φ̂ A_{g⁻¹}^*` (l.804–815) of graph type `g`, uniformly in `g, h ∈ G_i`, which
become homotopies of `ℬ_{G,Z}(T × Sⁿ)` after the sheet shift (actual exterior factorizations,
Lemma 9.1). No equivariance, no strict action and no control over `T` of the individual `A_g`
is assumed: they are morphisms over `T` only after the compensating sheet translation (l.548). -/
structure SheetData where
  toAction : SheetAction cd π
  B : ∀ r : ℤ, GraphFamily (fun i ↦ G i × G i) (cd.sheetObj π (toAction.C.C.X r))
    (cd.sheetObj π (toAction.C.C.X (r + 1)))
  hB : ∀ r, HasGraphType (fun _ gh ↦ gh.1 * gh.2) (B r)
  mul : ∀ g h : ∀ i, G i,
    ∃ H : Homotopy (toAction.act h ≫ toAction.act g) (toAction.act (g * h)),
      ∀ r, H.hom r (r + 1) =
        cd.shift π (g * h) (fun i ↦ B r i (g i, h i)) ((hB r).apply fun i ↦ (g i, h i))
  V : ∀ r : ℤ, GraphFamily G (cd.sheetObj π (toAction.C.C.X (cd.N - r)))
    (cd.sheetObj π (toAction.C.C.X (r + 1)))
  hV : ∀ r, HasGraphType (fun _ ↦ id) (V r)
  adj : ∀ g : ∀ i, G i,
    ∃ H : Homotopy (toAction.φG ≫ toAction.act g)
      (dualHom (cd.BG π).inv cd.N (toAction.act g⁻¹) ≫ toAction.φG),
      ∀ r, H.hom r (r + 1) = cd.shift π g (fun i ↦ V r i (g i)) ((hV r).apply g)

end ControlData

/-- The tail groups (l.45, (7.9)): finite cyclic `p`-groups `G_i = C_{p^{a_i}}` with
`π_i : G_i → C_p` onto, so that `P_i = ker π_i` has index `p`. -/
structure TailGroups (p : ℕ) (Cp : Subgroup Circle) where
  G : ℕ → Type
  [group : ∀ i, Group (G i)]
  [fintype : ∀ i, Fintype (G i)]
  π : ∀ i, G i →* Cp
  isCyclic : ∀ i, IsCyclic (G i)
  isPGroup : ∀ i, IsPGroup p (G i)
  surjective : ∀ i, Function.Surjective (π i)

attribute [instance] TailGroups.group TailGroups.fintype

/-! #### Non-vacuity of the generic steps -/

/-- The `p`-th roots of unity in `S¹`. -/
def circleRoots (p : ℕ) [NeZero p] : Subgroup Circle :=
  (ZMod.toCircle (N := p)).toMonoidHom.range

theorem card_circleRoots (p : ℕ) [NeZero p] : Nat.card (circleRoots p) = p := by
  rw [circleRoots, ← Nat.card_congr (MonoidHom.ofInjective
    (f := (ZMod.toCircle (N := p)).toMonoidHom) ZMod.injective_toCircle).toEquiv]
  exact (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod p)

instance (p : ℕ) [NeZero p] : Nonempty (ControlData p) :=
  ⟨{ m := 1, n := 1, n_pos := one_pos, Cp := circleRoots p, card_Cp := card_circleRoots p
     y := _, dist_y_infty := RoundSphere.dist_zero_infty (n := 1), r := 1 / 2, R := 1
     r_pos := by norm_num, r_lt_R := by norm_num, R_lt := by norm_num }⟩

/-- `G_i = C_p` with `π_i = id` are tail groups. -/
def TailGroups.const {p : ℕ} [hp : Fact p.Prime] {Cp : Subgroup Circle}
    (h : Nat.card Cp = p) : TailGroups p Cp :=
  haveI : Finite Cp := Nat.finite_of_card_ne_zero (h ▸ hp.out.ne_zero)
  haveI : Fintype Cp := Fintype.ofFinite _
  { G := fun _ ↦ Cp
    π := fun _ ↦ MonoidHom.id _
    isCyclic := fun _ ↦ isCyclic_of_prime_card h
    isPGroup := fun _ ↦ IsPGroup.of_card (n := 1) (by rw [h, pow_one])
    surjective := fun _ ↦ Function.surjective_id }

/-! ### The control data of an effective action -/

namespace ChartData

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {M : Type*} [TopologicalSpace M] [AddAction ℤ_[p] M]

/-- The connected zero-dimensional case is immediate (l.456): in `ℝ⁰` the chart forces
`H_j` to fix the free point `x₀`. -/
theorem n_pos (c : ChartData p n M) : 0 < n := by
  refine Nat.pos_of_ne_zero fun hn ↦ ?_
  subst hn
  have hmem : (p : ℤ_[p]) ^ c.j ∈ padicPowerSubgroup p c.j :=
    show (p : ℤ_[p]) ^ c.j ∈ (Ideal.span {(p : ℤ_[p]) ^ c.j} : Ideal ℤ_[p]) from
      Ideal.mem_span_singleton_self _
  have hstab : (p : ℤ_[p]) ^ c.j ∈ AddAction.stabilizer ℤ_[p] c.x₀ :=
    c.φ.injOn (c.vadd_mem_source _ hmem _ c.x₀_mem_source (by simp [c.φ_x₀])) c.x₀_mem_source
      (Subsingleton.elim _ _)
  rw [c.stabilizer_x₀, AddSubgroup.mem_bot] at hstab
  exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) hstab

end ChartData

namespace FixedData

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {M : Type*} [TopologicalSpace M] [AddAction ℤ_[p] M]
  (d : FixedData p n M)

/-- The control data `(T, C_p, Sⁿ, y, r, R)` of the fixed data (l.517–527). -/
def control : ControlData p where
  m := d.m
  n := n
  n_pos := d.n_pos
  Cp := d.Cp
  card_Cp := d.card_Cp
  y := d.yS
  dist_y_infty := d.dist_yS_infty
  r := d.r
  R := d.R
  r_pos := d.r_pos
  r_lt_R := d.r_lt_R
  R_lt := d.R_lt_t.trans (d.t_lt_u.trans (d.u_lt.trans_eq d.roundDist_y_infty))

theorem control_Z₀ : d.control.Z₀ = d.Z₀S := rfl

theorem control_Z : d.control.Z = d.ZS := rfl

/-- The functor `U` of l.873 is `Res ≫ push`. -/
theorem U_eq_res_push {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
    (π : ∀ i, G i →* d.Cp) : (d.U π).F = (d.control.res π ≫ d.control.push).F := by
  rw [U_eq, FiltrationHom.comp_quot]
  rfl

variable [ContinuousVAdd ℤ_[p] M] [LocallyCompactSpace M] [FirstCountableTopology M]

/-- The compactified control map `f̂ : Sⁿ → Sⁿ` (7.5)–(7.6). -/
def fhatS : C(RoundSphere n, RoundSphere n) := d.fhat

/-- `f̂` has degree one: it is homotopic to the identity (7.6), via the pinch. -/
theorem fhatS_homotopic : d.fhatS.Homotopic (ContinuousMap.id _) :=
  d.fhat_homotopicRel_id.homotopic

end FixedData

/-! ### Part 3: the remaining steps -/

/-- **Interface: the fibre tail signature.** For control data `cd`, the homomorphism
`Lconc_N(ℬ_{1,Z₀}(Sⁿ)) → ℤ^ℕ/ℤ^(ℕ)`; intended: `σ_tail ∘ Δ_1 ∘ 𝕃.cls`, the decoration map
`𝕃.cls` of `LTheory.LowerLTheory` (H3), the `n` successive localization boundaries `Δ_1` of
(11.1) (l.885–905, scalar version), and `σ_tail` of (3.5) on `L_4(𝒜_1(pt))` (Prop. 3.2,
l.146–179). The cuts are the paper's balls `B(y, r)` or, in the cubical route, the cube
`Q_n = [−r_Q, r_Q]ⁿ ⊂ {d(0, ·) < R}` and its iterated top faces (blueprint
`simplicial-design.md` §2.5); here `y = 0` (see `ControlData`). Since `σ cd` sees only `cd`, these
cut sets are functions of `cd` alone: any choice depending on the action (such as `r_Q` through
the pinch radius) must be made through `cd`, and the same cuts define `Δ_T` in
`TransferDivisibility` ((11.2) needs identical cuts, l.900). -/
abbrev FibreSignature : Type :=
  ∀ ⦃p : ℕ⦄ (cd : ControlData p), Lconc cd.B1S cd.N →+ Tail

/-- **Interface: the manifold germ.** For control data `cd` and a control map `c : Sⁿ → Sⁿ`, the
class in `Lconc_N(𝒜_1(Sⁿ))` of the closed scalar Poincaré complex of the **cubical torus model**
`W_i = Tⁿ_{m_i} ⊗ CPcell` (blueprint `simplicial-design.md` §§1, 2.3; `cubical-review.md`),
which replaces the paper's fine triangulations `Y_i` of `Sⁿ × ℂP²` (l.542–584):
`Tⁿ_m = (C_m)^{⊗n}` is the cubical grid of mesh `η_i = 16/m_i → 0` on the torus
`(ℝ/16ℤ)ⁿ ⊃ [−8,8]ⁿ`, `CPcell = (ℚe₀ ⊕ ℚe₂ ⊕ ℚe₄, d = 0, φ = antidiagonal 1)` is the cellular
`ℂP²` of l.1093 (never subdivided, ignored by the control), and the duality is the torus Serre cap
tensored with that of `CPcell`. A cell `σ ⊗ e` is labelled by `(c ∘ q)(centre σ)`, where
`q : Tⁿ → Sⁿ` is a fixed continuous degree-one collapse equal to the chart lift `v ↦ v` on
`{‖v‖_∞ ≤ 4} ⊂ [−8,8]ⁿ`; so the labels are continuous for every `c`, as Lemma 11.1 on `Tⁿ`
(`GermHomotopyInvariance`) needs. If `q` maps `{‖v‖_∞ ≥ 4}` into `{‖w‖_∞ ≥ 4} ∪ {∞}`, then for
the control maps used (`f̂`, the pinch and the homotopies between them, all `∞` on `‖v‖_∞ ≥ 4`)
the label is `c(lift centre σ)`, as in `cubical-review.md`. `𝔪_f` (l.824) is the image in
`ℬ_{1,Z₀}(Sⁿ)` for `c = f̂`; only consistency within §§10–12 is needed, not equality with the
paper's triangulated germ (cubical-review Q2). -/
abbrev ManifoldGerm : Type :=
  ∀ ⦃p : ℕ⦄ (cd : ControlData p), C(RoundSphere cd.n, RoundSphere cd.n) → Lconc cd.A1S cd.N

/-- **S1–S3: realization (Proposition 9.2).** For the fixed data of an action on a manifold,
there are tail groups `G_i = H/K_i → C_p` ((7.9), l.531–539) and a scalar Poincaré complex with
coherent sheet action satisfying the hypotheses of (★), namely the compressed chain models
`(C_i, d̂_i, φ̂_i)` with `A_g = π a_g σ`, `B̂_{g,h}`, `V̂_g` of §§8–9 (Lemmas 8.1, 8.2, 9.1,
(9.3)–(9.8), l.540–825), whose image after forgetting `T` is the manifold germ `𝔪_f` of `f̂`
(last paragraph of the proof of Proposition 9.2, l.824). -/
def ClassConstruction (germ : ManifoldGerm) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [LocallyCompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ConnectedSpace M] [AddAction ℤ_[p] M] [ContinuousVAdd ℤ_[p] M] (d : FixedData p n M),
    ∃ (Γ : TailGroups p d.Cp) (S : d.control.SheetData Γ.π),
      Lconc.map d.control.push (Lconc.cls S.toAction.C) =
        Lconc.map d.control.proj (germ d.control d.fhatS)

/-- **S1–S3, existential form**: all that §12 uses of `ClassConstruction`. For the fixed data of an
action on a manifold, there are control data, tail groups, sheet data and a control map `c`
homotopic to the identity whose scalar class after forgetting `T` is the manifold germ of `c`;
neither `cd = d.control` nor `c = f̂` is required. -/
def ClassConstruction' (germ : ManifoldGerm) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [LocallyCompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ConnectedSpace M] [AddAction ℤ_[p] M] [ContinuousVAdd ℤ_[p] M] (_d : FixedData p n M),
    ∃ (cd : ControlData p) (Γ : TailGroups p cd.Cp) (S : cd.SheetData Γ.π)
      (c : C(RoundSphere cd.n, RoundSphere cd.n)), c.Homotopic (ContinuousMap.id _) ∧
      Lconc.map cd.push (Lconc.cls S.toAction.C) = Lconc.map cd.proj (germ cd c)

theorem classConstruction'_of {germ : ManifoldGerm} (h : ClassConstruction germ) :
    ClassConstruction' germ := by
  intro p _ n M _ _ _ _ _ _ _ _ d
  obtain ⟨Γ, S, hS⟩ := h p n M d
  exact ⟨d.control, Γ, S, d.fhatS, d.fhatS_homotopic, hS⟩

/-- **S4–S6: the equivariant corner class and its scalar image** (Lemmas 5.1–5.2, (10.1)–(10.4),
l.274–398, 826–881). The averaged projector `E = q⁻¹ ∑_g A_g ⊗ R_{g⁻¹}` (10.2) on `Ind C` is a
homotopy idempotent compatible with `Φ` in `ℬ_{G,Z}(T × Sⁿ)`; its normalized corner
`(D, q⁻¹ r Φ r^*)` of the Balmer–Schlichting splitting is a class `𝔡` (10.3) with
`Res 𝔡 = [C]` already over `T × Sⁿ`, since the row and column maps `u_b = A_b`,
`v_a = q⁻¹ A_{a⁻¹}` are `T`-controlled after forgetting `G` (crux-review §0, R4). -/
def InducedClass : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cd : ControlData p) (Γ : TailGroups p cd.Cp)
    (S : cd.SheetData Γ.π),
    ∃ 𝔡 : Lconc (cd.BG Γ.π) cd.N, Lconc.map (cd.res Γ.π) 𝔡 = Lconc.cls S.toAction.C

/-- **S4–S6, weak form** ((10.4), l.873–881): the scalar image `U_*𝔡 = [𝔪]` only after forgetting
`T`, which is all that (★) uses (`cruxStar_of_steps`); implied by `InducedClass`
(`InducedClass.toWeak`). -/
def InducedClassWeak : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cd : ControlData p) (Γ : TailGroups p cd.Cp)
    (S : cd.SheetData Γ.π),
    ∃ 𝔡 : Lconc (cd.BG Γ.π) cd.N,
      Lconc.map (cd.res Γ.π ≫ cd.push) 𝔡 = Lconc.map cd.push (Lconc.cls S.toAction.C)

theorem InducedClass.toWeak (h : InducedClass) : InducedClassWeak := by
  intro p _ cd Γ S
  obtain ⟨𝔡, h𝔡⟩ := h p cd Γ S
  exact ⟨𝔡, by rw [Lconc.map_comp, AddMonoidHom.comp_apply, h𝔡]⟩

/-- **S7–S9, S12b: Theorem 6.3 on the sphere side.** For every class `x` over
`ℬ_{G,Z}(T × Sⁿ)`, the fibre tail signature of `U_* x` is divisible by `p`: by naturality
`U_*Δ_T = Δ_1U_*` (11.2) (l.885–912), the trace convention `σ_tail(α) = σ_tail(U_*α)`
((3.2), Prop. 3.2, l.119–131, 156) and Theorem 6.3 for `α = Δ_T x ∈ L_4(𝒜_G(T))` (Lemmas 6.1,
6.2, l.400–452), i.e. (12.2). -/
def TransferDivisibility (σ : FibreSignature) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cd : ControlData p) (Γ : TailGroups p cd.Cp)
    (x : Lconc (cd.BG Γ.π) cd.N), σ cd (Lconc.map (cd.res Γ.π ≫ cd.push) x) ∈ divTail p

/-- **(★)** (crux-review, end; R1): a scalar Poincaré complex over `T × Sⁿ` carrying a
first-order coherent graph-type homotopy action of cyclic `p`-groups `G_i → C_p`, with `T` a
free `C_p`-space, has fibre tail signature in `∏ pℤ / ⊕ pℤ`. -/
def CruxStar (σ : FibreSignature) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cd : ControlData p) (Γ : TailGroups p cd.Cp)
    (S : cd.SheetData Γ.π), σ cd (Lconc.map cd.push (Lconc.cls S.toAction.C)) ∈ divTail p

/-- **S10: Lemma 11.1 and (11.3)** (l.914–927): homotopic control maps give cobordant
manifold germs. -/
def GermHomotopyInvariance (germ : ManifoldGerm) : Prop :=
  ∀ ⦃p : ℕ⦄ [Fact p.Prime] (cd : ControlData p) (c₀ c₁ : C(RoundSphere cd.n, RoundSphere cd.n)),
    c₀.Homotopic c₁ → germ cd c₀ = germ cd c₁

/-- **S11–S12a: Lemma 11.2 and (11.5)** (l.932–1098): the iterated boundary of the germ of a
degree-one control map is `±[ℂP²]` at every index, and `σ(ℂP²) = 1`; the sign is the product of
the boundary signs (`bsign`). -/
def PinchSignature (σ : FibreSignature) (germ : ManifoldGerm) : Prop :=
  ∀ ⦃p : ℕ⦄ [Fact p.Prime] (cd : ControlData p),
    IsSignTail (σ cd (Lconc.map cd.proj (germ cd (ContinuousMap.id _))))

/-- **§§10–11: the scalar value** ((11.3)–(11.5), (12.1)): every control map homotopic to the
identity has fibre tail signature `±1`. -/
def ScalarSignatureOne (σ : FibreSignature) (germ : ManifoldGerm) : Prop :=
  ∀ ⦃p : ℕ⦄ [Fact p.Prime] (cd : ControlData p) (c : C(RoundSphere cd.n, RoundSphere cd.n)),
    c.Homotopic (ContinuousMap.id _) → IsSignTail (σ cd (Lconc.map cd.proj (germ cd c)))

/-! #### Degenerate interfaces do not discharge all steps -/

theorem not_isSignTail_zero : ¬ IsSignTail (0 : Tail) := fun h ↦ by
  obtain ⟨i, hi⟩ :=
    (isSignTail_coe.mp (show IsSignTail ((fun _ : ℕ ↦ (0 : ℤ)) : Tail) from h)).exists
  simp at hi

/-- The zero fibre signature satisfies the transfer step trivially. -/
theorem transferDivisibility_zero : TransferDivisibility 0 :=
  fun _ _ _ _ _ ↦ zero_mem _

/-- The zero fibre signature satisfies (★) trivially. -/
theorem cruxStar_zero : CruxStar 0 :=
  fun _ _ _ _ _ ↦ zero_mem _

/-- ... but not the pinch step, for any germ. -/
theorem not_pinchSignature_zero (germ : ManifoldGerm) : ¬ PinchSignature 0 germ := fun h ↦ by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨cd⟩ := (inferInstance : Nonempty (ControlData 2))
  exact not_isSignTail_zero (h cd)

/-- The zero germ fails the pinch step for every fibre signature. -/
theorem not_pinchSignature_zero_germ (σ : FibreSignature) : ¬ PinchSignature σ 0 := fun h ↦ by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨cd⟩ := (inferInstance : Nonempty (ControlData 2))
  exact not_isSignTail_zero (by simpa using h cd)

/-! ### Part 4: the glue -/

variable {σ : FibreSignature} {germ : ManifoldGerm}

/-- (★) from Lemma 5.2 and Theorem 6.3 (crux-review §0: `Δ_T^{sc}[C] ∈ Res L_4(𝒜_G(T))`). -/
theorem cruxStar_of_steps (h₁ : InducedClassWeak) (h₂ : TransferDivisibility σ) :
    CruxStar σ := by
  intro p _ cd Γ S
  obtain ⟨𝔡, h𝔡⟩ := h₁ p cd Γ S
  have := h₂ p cd Γ 𝔡
  rwa [h𝔡] at this

theorem scalarSignatureOne_of_steps (h₁ : GermHomotopyInvariance germ)
    (h₂ : PinchSignature σ germ) : ScalarSignatureOne σ germ := by
  intro p _ cd c hc
  rw [h₁ cd c _ hc]
  exact h₂ cd

/-- **§12** (l.1103–1128) for the fixed data of a hypothetical effective action. -/
theorem FixedData.false_of_steps (hcons : ClassConstruction germ) (hcrux : CruxStar σ)
    (hone : ScalarSignatureOne σ germ) {p : ℕ} [hp : Fact p.Prime] {n : ℕ} {M : Type}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [LocallyCompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ConnectedSpace M] [AddAction ℤ_[p] M]
    [ContinuousVAdd ℤ_[p] M] (d : FixedData p n M) : False := by
  obtain ⟨Γ, S, hS⟩ := hcons p n M d
  have hdiv := hcrux p d.control Γ S
  rw [hS] at hdiv
  exact notMem_divTail_of_isSignTail hp.out (hone d.control _ d.fhatS_homotopic) hdiv

/-- **The p-adic exclusion from the remaining steps**, given Montgomery's theorem (for the free
point of §7, l.456–466). -/
theorem padicExclusion_of_steps (hMon : PointwisePeriodicIsPeriodic) (σ : FibreSignature)
    (germ : ManifoldGerm) (hcons : ClassConstruction germ) (hcrux : CruxStar σ)
    (hone : ScalarSignatureOne σ germ) : PadicExclusion := by
  intro p _ n M _ _ _ _ _ _ _ _
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  obtain ⟨d⟩ := exists_fixedData (p := p) (n := n) (M := M) hMon
  exact d.false_of_steps hcons hcrux hone

/-- **The p-adic exclusion from the existential class construction** `ClassConstruction'`. -/
theorem padicExclusion_of_steps' (hMon : PointwisePeriodicIsPeriodic) (σ : FibreSignature)
    (germ : ManifoldGerm) (hcons : ClassConstruction' germ) (hcrux : CruxStar σ)
    (hone : ScalarSignatureOne σ germ) : PadicExclusion := by
  intro p hp n M _ _ _ _ _ _ _ _
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  obtain ⟨d⟩ := exists_fixedData (p := p) (n := n) (M := M) hMon
  obtain ⟨cd, Γ, S, c, hc, hS⟩ := hcons p n M d
  have hdiv := hcrux p cd Γ S
  rw [hS] at hdiv
  exact notMem_divTail_of_isSignTail hp.out (hone cd c hc) hdiv

/-- The same with (★) and the scalar value split into their paper steps (`InducedClass` enters
through `InducedClass.toWeak`). -/
theorem padicExclusion_of_fine_steps (hMon : PointwisePeriodicIsPeriodic) (σ : FibreSignature)
    (germ : ManifoldGerm) (hcons : ClassConstruction germ) (hind : InducedClassWeak)
    (htrans : TransferDivisibility σ) (hhtpy : GermHomotopyInvariance germ)
    (hpinch : PinchSignature σ germ) : PadicExclusion :=
  padicExclusion_of_steps hMon σ germ hcons (cruxStar_of_steps hind htrans)
    (scalarSignatureOne_of_steps hhtpy hpinch)

/-- **Hilbert–Smith from the remaining steps and the published inputs** (Montgomery's theorem is
derived from uniform Newman, `pointwisePeriodicIsPeriodic_of_uniformNewman`). -/
theorem hilbertSmith_of_steps (hNSS : NSSIsLie) (hLee : CompactNonLieContainsPadic)
    (hNew : UniformNewman) (σ : FibreSignature) (germ : ManifoldGerm)
    (hcons : ClassConstruction germ) (hcrux : CruxStar σ) (hone : ScalarSignatureOne σ germ) :
    HilbertSmith ∧ HilbertSmithWithBoundary ∧ PadicExclusionWithBoundary :=
  hilbertSmith_all_of_padicExclusion hNSS hLee hNew <|
    padicExclusion_of_steps (pointwisePeriodicIsPeriodic_of_uniformNewman hNew) σ germ hcons
      hcrux hone

end HSFormal
