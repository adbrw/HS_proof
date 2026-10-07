import HSFormal.FixedData
import Mathlib.Topology.MetricSpace.IsometricSMul

/-!
# The control target of Section 7 as a compact metric `C_p`-space

* `HSFormal.RoundSphere n`: the target sphere `Sⁿ = OnePoint ℝⁿ` with the round metric
  `HSFormal.roundDist` as a `MetricSpace`. Its topology is the `OnePoint` topology by construction
  (`RoundSphere.topology_eq`); it is compact, and every monoid acts trivially on it.
* `Circle` acts on `T = S^{2m-1} ⊆ ℂ^m` (and on `ℂ^m`) by scalars, freely and isometrically;
  subgroups of isometric actions are isometric.
* `HSFormal.LabelSpace m n = T × Sⁿ` with the maximum product metric (L70) is the compact
  isometric label space of §§8–11.
* `FixedData.Cp ⊆ S¹`, the image of the quotient character `FixedData.χ : H → C_p` (L517), has
  order `p`; `Z₀`, `Z = T × Z₀`, `f` and `ρ̃` are transported to `Sⁿ` and `T × Sⁿ`.

The stereographic identification `roundSphere` uses an arbitrary linear `hyperplaneEquiv`. Only
its being a homeomorphism and `roundDist_zero_infty` are used downstream (L519–527); the cube
`Q_n ⊆ {d(y,·) < R}` of §11 needs only continuity (`exists_norm_lt_roundDist_lt`).
-/

noncomputable section

open Set Metric OnePoint Topology Pointwise

namespace HSFormal

/-! ### The round sphere -/

/-- The target sphere `Sⁿ = OnePoint ℝⁿ`, to be equipped with the round metric. -/
def RoundSphere (n : ℕ) : Type := OnePoint (EuclideanSpace ℝ (Fin n))

namespace RoundSphere

variable {n : ℕ}

instance : TopologicalSpace (RoundSphere n) := inferInstanceAs (TopologicalSpace (OnePoint _))

/-- The identity `Sⁿ → OnePoint ℝⁿ`. -/
def toOnePoint : RoundSphere n ≃ₜ OnePoint (EuclideanSpace ℝ (Fin n)) := Homeomorph.refl _

/-- The round metric, pulled back from the unit sphere of `ℝⁿ⁺¹`, with the `OnePoint` topology. -/
instance : MetricSpace (RoundSphere n) :=
  ((roundSphere n).isEmbedding.comp toOnePoint.isEmbedding).comapMetricSpace _

theorem dist_eq (z z' : RoundSphere n) : dist z z' = roundDist (toOnePoint z) (toOnePoint z') :=
  rfl

/-- The round metric induces the `OnePoint` topology. -/
theorem topology_eq :
    (UniformSpace.toTopologicalSpace : TopologicalSpace (RoundSphere n)) =
      (inferInstance : TopologicalSpace (OnePoint (EuclideanSpace ℝ (Fin n)))) :=
  rfl

theorem isometry_roundSphere : Isometry fun z : RoundSphere n ↦ roundSphere n (toOnePoint z) :=
  Isometry.of_dist_eq fun _ _ ↦ rfl

instance : CompactSpace (RoundSphere n) := inferInstanceAs (CompactSpace (OnePoint _))

/-- `∞`. -/
def infty : RoundSphere n := toOnePoint.symm ∞

/-- `0` and `∞` are antipodal. -/
theorem dist_zero_infty :
    dist (toOnePoint.symm ((0 : EuclideanSpace ℝ (Fin n)) : OnePoint (EuclideanSpace ℝ (Fin n))))
      infty = 2 :=
  roundDist_zero_infty n

/-- The control coordinate `Sⁿ` carries the trivial action (`C_p` acts on `T` only, L546). -/
instance (priority := high) {G : Type*} [Monoid G] : SMul G (RoundSphere n) where
  smul _ z := z

instance {G : Type*} [Monoid G] : MulAction G (RoundSphere n) where
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
theorem smul_eq {G : Type*} [Monoid G] (g : G) (z : RoundSphere n) : g • z = z := rfl

instance {G : Type*} [Monoid G] : IsIsometricSMul G (RoundSphere n) :=
  ⟨fun _ ↦ isometry_id⟩

end RoundSphere

/-- Points near `0` are round-close to `0` (used for the cube `Q_n` of §11). -/
theorem exists_norm_lt_roundDist_lt {n : ℕ} {R : ℝ} (hR : 0 < R) :
    ∃ δ > 0, ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ < δ →
      roundDist ((0 : EuclideanSpace ℝ (Fin n)) : OnePoint (EuclideanSpace ℝ (Fin n)))
        (v : OnePoint (EuclideanSpace ℝ (Fin n))) < R := by
  have hc : Continuous fun v : EuclideanSpace ℝ (Fin n) ↦
      roundDist ((0 : EuclideanSpace ℝ (Fin n)) : OnePoint (EuclideanSpace ℝ (Fin n)))
        (v : OnePoint (EuclideanSpace ℝ (Fin n))) :=
    (continuous_roundDist_left _).comp OnePoint.continuous_coe
  obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 hc.continuousAt R hR
  refine ⟨δ, hδ, fun v hv ↦ ?_⟩
  have := h (x := v) (by rwa [dist_zero_right])
  simpa [roundDist, Real.dist_eq] using (le_abs_self _).trans_lt this

/-! ### Isometric scalar actions of the circle -/

section Circle

/-- A subgroup of an isometric action acts isometrically. -/
instance subgroup_isIsometricSMul {G X : Type*} [Group G] [PseudoEMetricSpace X] [MulAction G X]
    [IsIsometricSMul G X] (S : Subgroup G) : IsIsometricSMul S X :=
  ⟨fun c ↦ isometry_smul X (c : G)⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

instance circle_isIsometricSMul : IsIsometricSMul Circle E :=
  ⟨fun z ↦ Isometry.of_dist_eq fun a b ↦ by rw [dist_eq_norm, ← smul_sub, Circle.norm_smul,
    dist_eq_norm]⟩

/-- `S¹` acts on the unit sphere by scalars. -/
instance circleSphereAction : MulAction Circle (sphere (0 : E) 1) where
  smul z v := ⟨z • (v : E), by rw [mem_sphere_zero_iff_norm, Circle.norm_smul,
    norm_eq_of_mem_sphere]⟩
  one_smul v := Subtype.ext (one_smul Circle (v : E))
  mul_smul z w v := Subtype.ext (mul_smul z w (v : E))

@[simp]
theorem coe_circle_smul_sphere (z : Circle) (v : sphere (0 : E) 1) :
    ((z • v : sphere (0 : E) 1) : E) = z • (v : E) :=
  rfl

instance circle_isIsometricSMul_sphere : IsIsometricSMul Circle (sphere (0 : E) 1) :=
  ⟨fun z ↦ Isometry.of_dist_eq fun a b ↦ by
    rw [Subtype.dist_eq, Subtype.dist_eq, coe_circle_smul_sphere, coe_circle_smul_sphere,
      dist_smul]⟩

/-- Scalars act freely off zero. -/
theorem circle_smul_eq_self_iff {z : Circle} {v : E} (hv : v ≠ 0) : z • v = v ↔ z = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ one_smul _ v⟩
  have h1 : ((z : ℂ) - 1) • v = 0 := by rw [sub_smul, one_smul, ← Circle.smul_def, h, sub_self]
  exact Circle.coe_injective (by
    rw [Circle.coe_one]; exact sub_eq_zero.1 ((smul_eq_zero.1 h1).resolve_right hv))

/-- `S¹` acts freely on the unit sphere (L517). -/
theorem eq_one_of_smul_sphere_eq {z : Circle} {v : sphere (0 : E) 1} (h : z • v = v) : z = 1 :=
  (circle_smul_eq_self_iff (ne_zero_of_mem_unit_sphere v)).1 (congrArg Subtype.val h)

/-- The unit sphere is invariant under the circle. -/
theorem circle_smul_sphere (z : Circle) : z • sphere (0 : E) 1 = sphere (0 : E) 1 := by
  ext v
  simp only [Set.mem_smul_set, mem_sphere_zero_iff_norm]
  refine ⟨?_, fun hv ↦ ⟨z⁻¹ • v, by rwa [mem_sphere_zero_iff_norm, Circle.norm_smul],
    smul_inv_smul z v⟩⟩
  rintro ⟨w, hw, rfl⟩
  rw [mem_sphere_zero_iff_norm] at hw
  exact (Circle.norm_smul z w).trans hw

end Circle

/-! ### The label space `T × Sⁿ` -/

/-- The compact label space `T × Sⁿ`, `T = S^{2m-1} ⊆ ℂ^m`, with the maximum product metric (L70)
and `S¹` acting on `T` by scalars. -/
abbrev LabelSpace (m n : ℕ) := sphere (0 : EuclideanSpace ℂ (Fin m)) 1 × RoundSphere n

section Label

variable {m n : ℕ}

example : CompactSpace (LabelSpace m n) := inferInstance
example : IsIsometricSMul Circle (LabelSpace m n) := inferInstance

instance (S : Subgroup Circle) : MulAction S (RoundSphere n) := RoundSphere.instMulAction

/-- `IsIsometricSMul` for the scalar action induced by the `MulAction` instance above (it agrees
with the trivial `SMul` instance, but only up to unfolding instance definitions). -/
instance isIsometricSMul_subgroup_roundSphere (S : Subgroup Circle) :
    @IsIsometricSMul S (RoundSphere n) _ (@SemigroupAction.toSMul _ _ _ MulAction.toSemigroupAction) :=
  ⟨fun _ ↦ isometry_id⟩

instance (S : Subgroup Circle) : MulAction S (LabelSpace m n) := inferInstance

instance (S : Subgroup Circle) : IsIsometricSMul S (LabelSpace m n) := inferInstance

/-- The same instance for the scalar action induced by the `MulAction` instance above (the two
`SMul` instances agree, but only up to unfolding `inferInstanceAs`-generated definitions). -/
instance isIsometricSMul_subgroup_labelSpace (S : Subgroup Circle) :
    @IsIsometricSMul S (LabelSpace m n) _ (@SemigroupAction.toSMul _ _ _ MulAction.toSemigroupAction) :=
  ⟨fun c ↦ isometry_smul (LabelSpace m n) (c : Circle)⟩

/-- Products `T × S` are invariant under any action trivial on `Sⁿ`. -/
theorem smul_univ_prod {G T : Type*} [Group G] [MulAction G T] (g : G) (S : Set (RoundSphere n)) :
    g • ((univ : Set T) ×ˢ S) = univ ×ˢ S := by
  ext ⟨t, z⟩
  refine ⟨?_, fun h ↦ ⟨(g⁻¹ • t, z), ⟨mem_univ _, h.2⟩, by simp⟩⟩
  rintro ⟨⟨t', z'⟩, ⟨-, hz⟩, h⟩
  simp only [Prod.smul_mk, RoundSphere.smul_eq, Prod.mk.injEq] at h
  exact ⟨mem_univ _, h.2 ▸ hz⟩

/-- The sphere coordinate `T × Sⁿ → Sⁿ` is `1`-Lipschitz and invariant. -/
theorem lipschitzWith_snd : LipschitzWith 1 (Prod.snd : LabelSpace m n → RoundSphere n) :=
  LipschitzWith.prod_snd

theorem snd_smul {G : Type*} [Monoid G] [MulAction G (sphere (0 : EuclideanSpace ℂ (Fin m)) 1)]
    (g : G) (x : LabelSpace m n) : (g • x).2 = x.2 :=
  rfl

end Label

/-! ### Transport of the fixed data -/

namespace FixedData

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {M : Type*} [TopologicalSpace M] [AddAction ℤ_[p] M]
  (d : FixedData p n M)

/-- `C_p = χ(H) ⊆ S¹`, the image of the quotient character (L517). -/
def Cp : Subgroup Circle := (tailChar p d.j).range

/-- The quotient character `χ : H → C_p` (L517). -/
def χ : PadicTail p d.j →* d.Cp := (tailChar p d.j).rangeRestrict

@[simp]
theorem coe_χ (g : PadicTail p d.j) : (d.χ g : Circle) = padicChar p d.j g.val := rfl

theorem χ_surjective : Function.Surjective d.χ := MonoidHom.rangeRestrict_surjective _

/-- `ker χ = H'` (L509). -/
theorem χ_eq_one_iff {g : PadicTail p d.j} : d.χ g = 1 ↔ g.val ∈ d.H' := by
  rw [← padicChar_eq_one_iff, ← coe_χ, OneMemClass.coe_eq_one]

theorem pow_eq_one_of_mem_Cp {z : Circle} (hz : z ∈ d.Cp) : z ^ p = 1 := by
  obtain ⟨g, rfl⟩ := hz
  exact padicChar_pow_eq_one g.val_mem

theorem exists_χ_ne_one : ∃ g : PadicTail p d.j, d.χ g ≠ 1 := by
  by_contra! h
  have hle : padicPowerSubgroup p d.j ≤ d.H' := fun a ha ↦
    d.χ_eq_one_iff.1 (h (PadicTail.mk a ha))
  exact absurd ((padicPowerSubgroup_le_iff _ _).1 hle) (by omega)

instance : Finite d.Cp := by
  refine Set.finite_coe_iff.2 ((Set.finite_range fun a : ZMod (p ^ (d.j + 1)) ↦
    ZMod.toCircle a).subset ?_)
  rintro _ ⟨g, rfl⟩
  exact ⟨_, rfl⟩

/-- `|C_p| = p`. -/
theorem card_Cp : Nat.card d.Cp = p := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨g, hg⟩ := d.exists_χ_ne_one
  refine le_antisymm ?_ ?_
  · have hinj : Function.Injective fun z : d.Cp ↦ ((z : Circle) : ℂ) :=
      Circle.coe_injective.comp Subtype.val_injective
    calc Nat.card d.Cp ≤ Nat.card (Polynomial.nthRoots p (1 : ℂ)).toFinset := by
          refine Nat.card_le_card_of_injective (fun z ↦ ⟨((z : Circle) : ℂ), ?_⟩) fun a b h ↦
            hinj (by simpa using h)
          rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hp.pos, ← Circle.coe_one,
            ← d.pow_eq_one_of_mem_Cp z.2]
          exact (map_pow Circle.coeHom _ p).symm
      _ = (Polynomial.nthRoots p (1 : ℂ)).toFinset.card := Nat.card_eq_finsetCard _
      _ ≤ Multiset.card (Polynomial.nthRoots p (1 : ℂ)) := Multiset.toFinset_card_le _
      _ ≤ p := Polynomial.card_nthRoots p 1
  · have hpow : d.χ g ^ p = 1 := Subtype.ext (d.pow_eq_one_of_mem_Cp (d.χ g).2)
    calc p = orderOf (d.χ g) := (orderOf_eq_prime hpow hg).symm
      _ ≤ Nat.card d.Cp := orderOf_le_card

/-- `C_p` acts freely on `T` (L517). -/
theorem Cp_smul_eq_iff {c : d.Cp} {v : sphere (0 : EuclideanSpace ℂ (Fin d.m)) 1} :
    c • v = v ↔ c = 1 :=
  ⟨fun h ↦ Subtype.ext (eq_one_of_smul_sphere_eq h), fun h ↦ h ▸ one_smul _ v⟩

/-- `y = s_ρ(0)` on the round sphere. -/
def yS : RoundSphere n := RoundSphere.toOnePoint.symm d.y

theorem dist_yS_infty : dist d.yS RoundSphere.infty = 2 := d.roundDist_y_infty

/-- `Z₀ = {z : d(y,z) ≥ R}` (7.8) for the round metric. -/
def Z₀S : Set (RoundSphere n) := {z | d.R ≤ dist d.yS z}

theorem Z₀S_eq : d.Z₀S = RoundSphere.toOnePoint ⁻¹' d.Z₀ := rfl

theorem Z₀S_eq_compl_ball : d.Z₀S = (ball d.yS d.R)ᶜ := by
  ext z
  simp [Z₀S, dist_comm]

theorem isClosed_Z₀S : IsClosed d.Z₀S := by
  rw [Z₀S_eq_compl_ball]
  exact isOpen_ball.isClosed_compl

theorem infty_mem_Z₀S : RoundSphere.infty ∈ d.Z₀S := by
  change d.R ≤ dist d.yS RoundSphere.infty
  rw [dist_yS_infty]
  linarith [d.R_lt_t, d.t_lt_u, d.u_lt.trans_eq d.roundDist_y_infty]

/-- The fixed exterior `Z = T × Z₀` (7.8) in the label space. -/
def ZS : Set (LabelSpace d.m n) := univ ×ˢ d.Z₀S

theorem isClosed_ZS : IsClosed d.ZS := isClosed_univ.prod d.isClosed_Z₀S

theorem smul_ZS {G : Type*} [Group G] [MulAction G (sphere (0 : EuclideanSpace ℂ (Fin d.m)) 1)]
    (g : G) : g • d.ZS = d.ZS :=
  smul_univ_prod g _

/-- The fixed exterior `Z = T × Z₀ ⊆ ℂ^m × Sⁿ` of FixedData, for the round metric. -/
def Zamb : Set (EuclideanSpace ℂ (Fin d.m) × RoundSphere n) := d.T ×ˢ d.Z₀S

theorem Zamb_eq : d.Zamb = Prod.map id RoundSphere.toOnePoint ⁻¹' d.Z := rfl

theorem isCompact_T : IsCompact d.T := isCompact_sphere 0 1

theorem isClosed_Zamb : IsClosed d.Zamb := isClosed_sphere.prod d.isClosed_Z₀S

theorem smul_Zamb (z : Circle) : z • d.Zamb = d.Zamb := by
  ext ⟨v, w⟩
  refine ⟨?_, fun h ↦ ⟨(z⁻¹ • v, w), ⟨?_, h.2⟩, Prod.ext (smul_inv_smul z v) rfl⟩⟩
  · rintro ⟨⟨v', w'⟩, ⟨hv, hw⟩, h⟩
    simp only [Prod.smul_mk, RoundSphere.smul_eq, Prod.mk.injEq] at h
    exact ⟨h.1 ▸ (circle_smul_sphere z).subset (smul_mem_smul_set hv), h.2 ▸ hw⟩
  · have := (circle_smul_sphere z⁻¹).subset (smul_mem_smul_set (a := z⁻¹) h.1)
    exact this

/-- `Z⁺` as an `H`-invariant subset. -/
def ZplusAction : SubMulAction (PadicTail p d.j) M where
  carrier := d.Zplus
  smul_mem' g _ hx := (d.vadd_mem_carrier_iff g.val_mem).2 hx

/-- `f : M → Sⁿ` (7.5) with the round metric on the target. -/
def fS (x : M) : RoundSphere n := RoundSphere.toOnePoint.symm (d.f x)

theorem fS_smul (g : PadicTail p d.j) (x : M) : d.fS (g • x) = d.fS x :=
  congrArg RoundSphere.toOnePoint.symm (d.f_vadd g.val_mem x)

/-- `ρ̃ : Z⁺ → T` (7.7). -/
def ρS (x : d.ZplusAction) : sphere (0 : EuclideanSpace ℂ (Fin d.m)) 1 :=
  ⟨d.ρtilde x, d.ρtilde_mem_T x.2⟩

theorem continuous_ρS : Continuous d.ρS :=
  (continuousOn_iff_continuous_domRestrict.1 d.continuousOn_ρtilde).subtype_mk _

/-- (7.7): `ρ̃(hx) = χ(h) ρ̃(x)`. -/
theorem ρS_smul (g : PadicTail p d.j) (x : d.ZplusAction) : d.ρS (g • x) = d.χ g • d.ρS x :=
  Subtype.ext (d.ρtilde_vadd _ g.val_mem x)

/-- The labels `(ρ̃, f) : Z⁺ → T × Sⁿ` of §§8–10, equivariant through `χ`. -/
def labelMap (x : d.ZplusAction) : LabelSpace d.m n := (d.ρS x, d.fS x)

theorem labelMap_smul (g : PadicTail p d.j) (x : d.ZplusAction) :
    d.labelMap (g • x) = d.χ g • d.labelMap x :=
  Prod.ext (d.ρS_smul g x) (d.fS_smul g x)

section Continuity

variable [ContinuousVAdd ℤ_[p] M] [LocallyCompactSpace M] [FirstCountableTopology M] [T2Space M]

theorem continuous_fS : Continuous d.fS :=
  RoundSphere.toOnePoint.symm.continuous.comp d.continuous_f

theorem continuous_labelMap : Continuous d.labelMap :=
  d.continuous_ρS.prodMk (d.continuous_fS.comp continuous_subtype_val)

/-- (7.8): `f⁻¹ B̄(y,u)` is compact and lies in `int Z⁺` (L527). -/
theorem label_preimage_closedBall :
    IsCompact (d.fS ⁻¹' closedBall d.yS d.u) ∧ d.fS ⁻¹' closedBall d.yS d.u ⊆ interior d.Zplus := by
  have h : d.fS ⁻¹' closedBall d.yS d.u = d.f ⁻¹' {z | roundDist d.y z ≤ d.u} := by
    ext x
    change roundDist (d.f x) d.y ≤ d.u ↔ roundDist d.y (d.f x) ≤ d.u
    rw [roundDist, roundDist, dist_comm]
  rw [h]
  exact d.label_preimage

end Continuity

end FixedData

end HSFormal
