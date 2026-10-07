import HSFormal.IntegrationControl
import Mathlib.Algebra.Group.Pi.Units

/-!
# Section 7: the finite groups `G_i = H/K_i`

The sequence of finite groups of (7.9) (`fullHS_final.md` L531–535), as multiplicative groups for
the asymptotic categories of §§2–6, from `d : FixedData p n M`. The depths are
`ℓ_i = j + (i + 1)`, so `K_i = H_{ℓ_i} ⊆ H'` and `G_i = H/K_i ≅ C_{p^{i+1}}`.

* `PadicTail.subgroup`: an additive subgroup `A ≤ ℤ_[p]` as a subgroup of the tail `H_j`.
* `FixedData.K`, `FixedData.G`, `FixedData.toG : H →* G_i`.
* `FixedData.π i : G_i →* C_p` induced by `χ`; `FixedData.P i = ker π_i = H'/K_i` (`P_eq_map`).
* `FixedData.gen i`, the class of `p^j`: it generates `G_i` and lies outside `P_i` (§6, L450).
* `FixedData.card_G : Fintype.card (G i) = p ^ (i + 1)`; `FixedData.q i = |G_i|` (10.2).
* `FixedData.rep`: representatives `h_g ∈ H` with `h_1 = 1`, `h_g h_h = h_{gh} k_{g,h}`,
  `k_{g,h} ∈ K_i` (L610) and `χ(h_g) = π_i(g)`.
* `FixedData.eventually_K_displacement_lt`: the displacement of `K_i` on `Q` tends to zero
  (L536, L612).
-/

noncomputable section

open Filter

namespace HSFormal

variable {p : ℕ} [Fact p.Prime]

theorem pow_mem_padicPowerSubgroup_iff {l m : ℕ} :
    (p : ℤ_[p]) ^ m ∈ padicPowerSubgroup p l ↔ l ≤ m := by
  rw [← padicPowerSubgroup_le_iff (p := p)]
  exact ((Submodule.toAddSubgroup_le _ _).trans (Ideal.span_singleton_le_iff_mem _)).symm

namespace PadicTail

variable {j : ℕ}

@[simp]
theorem val_inv (g : PadicTail p j) : (g⁻¹).val = -g.val := rfl

@[simp]
theorem val_pow (g : PadicTail p j) (m : ℕ) : (g ^ m).val = m • g.val := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, val_mul, ih, succ_nsmul]

/-- An additive subgroup `A ≤ ℤ_[p]` as a subgroup of the multiplicative tail (it is `A ∩ H_j`). -/
def subgroup (A : AddSubgroup ℤ_[p]) : Subgroup (PadicTail p j) where
  carrier := {g | g.val ∈ A}
  one_mem' := A.zero_mem
  mul_mem' ha hb := A.add_mem ha hb
  inv_mem' ha := A.neg_mem ha

@[simp]
theorem mem_subgroup {A : AddSubgroup ℤ_[p]} {g : PadicTail p j} : g ∈ subgroup A ↔ g.val ∈ A :=
  Iff.rfl

theorem subgroup_mono {A B : AddSubgroup ℤ_[p]} (h : A ≤ B) :
    subgroup (j := j) A ≤ subgroup B := fun _ hg => h hg

/-- The generator `p^j` of `H_j`. -/
def gen (p : ℕ) [Fact p.Prime] (j : ℕ) : PadicTail p j :=
  mk ((p : ℤ_[p]) ^ j) (Ideal.mem_span_singleton_self _)

@[simp]
theorem val_gen : (gen p j).val = (p : ℤ_[p]) ^ j := rfl

theorem val_gen_pow (m : ℕ) : (gen p j ^ m).val = (m : ℤ_[p]) * (p : ℤ_[p]) ^ j := by
  rw [val_pow, val_gen, nsmul_eq_mul]

theorem gen_pow_pow_mem_iff {l k : ℕ} :
    gen p j ^ (p ^ k) ∈ subgroup (padicPowerSubgroup p l) ↔ l ≤ j + k := by
  rw [mem_subgroup, val_gen_pow, Nat.cast_pow, ← pow_add, add_comm k,
    pow_mem_padicPowerSubgroup_iff]

/-- Every `h ∈ H_j` is `m p^j` modulo `H_{j+a}`, with `m < p^a`. -/
theorem exists_gen_pow (a : ℕ) (g : PadicTail p j) :
    ∃ m < p ^ a, (g⁻¹ * gen p j ^ m) ∈ subgroup (padicPowerSubgroup p (j + a)) := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 g.val_mem
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec a c)
  refine ⟨c.appr a, PadicInt.appr_lt c a, ?_⟩
  rw [mem_subgroup, val_mul, val_inv, val_gen_pow, ← hc]
  refine Ideal.mem_span_singleton'.2 ⟨-e, ?_⟩
  rw [pow_add, show -(c * (p : ℤ_[p]) ^ j) + (c.appr a : ℤ_[p]) * (p : ℤ_[p]) ^ j =
    -((c - c.appr a) * (p : ℤ_[p]) ^ j) by ring, ← he]
  ring

end PadicTail

namespace FixedData

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [AddAction ℤ_[p] M] (d : FixedData p n M)

/-! ### `K_i`, `G_i = H/K_i`, `π_i` and `P_i` (7.9) -/

/-- The depth `ℓ_i = j + (i + 1)` of `K_i = H_{ℓ_i}` (7.9). -/
def depth (i : ℕ) : ℕ := d.j + (i + 1)

theorem tendsto_depth : Tendsto d.depth atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨b, fun i hi => by simp only [depth]; omega⟩

/-- `K_i = H_{ℓ_i}`, a subgroup of `H = H_j` (7.9). -/
def K (i : ℕ) : Subgroup (PadicTail p d.j) := PadicTail.subgroup (padicPowerSubgroup p (d.depth i))

theorem mem_K {i : ℕ} {g : PadicTail p d.j} :
    g ∈ d.K i ↔ g.val ∈ padicPowerSubgroup p (d.depth i) :=
  Iff.rfl

/-- `K_i ⊆ H'` (7.9). -/
theorem K_le_H' (i : ℕ) : d.K i ≤ PadicTail.subgroup d.H' :=
  PadicTail.subgroup_mono (d.tail_le_H' (by simp [depth]))

theorem ker_χ : d.χ.ker = PadicTail.subgroup d.H' := by
  ext g
  exact d.χ_eq_one_iff

theorem K_le_ker_χ (i : ℕ) : d.K i ≤ d.χ.ker := d.ker_χ ▸ d.K_le_H' i

/-- `G_i = H/K_i` (7.9). -/
def G (i : ℕ) : Type := PadicTail p d.j ⧸ d.K i

instance (i : ℕ) : CommGroup (d.G i) := inferInstanceAs (CommGroup (PadicTail p d.j ⧸ d.K i))

/-- The quotient map `H → G_i = H/K_i`. -/
def toG (i : ℕ) : PadicTail p d.j →* d.G i := QuotientGroup.mk' (d.K i)

theorem toG_surjective (i : ℕ) : Function.Surjective (d.toG i) := QuotientGroup.mk'_surjective _

theorem toG_eq_one_iff {i : ℕ} {g : PadicTail p d.j} : d.toG i g = 1 ↔ g ∈ d.K i :=
  QuotientGroup.eq_one_iff g

theorem toG_eq_toG_iff {i : ℕ} {g h : PadicTail p d.j} :
    d.toG i g = d.toG i h ↔ g⁻¹ * h ∈ d.K i :=
  QuotientGroup.eq

/-- `π_i : G_i → C_p`, induced by the quotient character `χ` (L45, L531–535). -/
def π (i : ℕ) : d.G i →* d.Cp := QuotientGroup.lift (d.K i) d.χ (d.K_le_ker_χ i)

@[simp]
theorem π_toG (i : ℕ) (g : PadicTail p d.j) : d.π i (d.toG i g) = d.χ g := rfl

theorem π_comp_toG (i : ℕ) : (d.π i).comp (d.toG i) = d.χ := rfl

theorem π_surjective (i : ℕ) : Function.Surjective (d.π i) := fun c => by
  obtain ⟨g, rfl⟩ := d.χ_surjective c
  exact ⟨d.toG i g, rfl⟩

/-- `P_i = ker π_i` (L45, L531–535); it is `H'/K_i` by `P_eq_map`. -/
def P (i : ℕ) : Subgroup (d.G i) := (d.π i).ker

instance (i : ℕ) : (d.P i).Normal := MonoidHom.normal_ker _

theorem mem_P {i : ℕ} {g : d.G i} : g ∈ d.P i ↔ d.π i g = 1 := Iff.rfl

theorem toG_mem_P {i : ℕ} {g : PadicTail p d.j} : d.toG i g ∈ d.P i ↔ g.val ∈ d.H' :=
  d.χ_eq_one_iff

/-- `P_i = H'/K_i` (7.9). -/
theorem P_eq_map (i : ℕ) : d.P i = (PadicTail.subgroup d.H').map (d.toG i) := by
  have := QuotientGroup.ker_lift (d.K i) d.χ (d.K_le_ker_χ i)
  rw [ker_χ] at this
  exact this

/-! ### `G_i` is cyclic of order `p^(i+1)` -/

/-- The generator of `G_i`: the class of `p^j`. -/
def gen (i : ℕ) : d.G i := d.toG i (PadicTail.gen p d.j)

theorem exists_gen_pow (i : ℕ) (g : d.G i) : ∃ m < p ^ (i + 1), d.gen i ^ m = g := by
  obtain ⟨g, rfl⟩ := d.toG_surjective i g
  obtain ⟨m, hm, hK⟩ := PadicTail.exists_gen_pow (i + 1) g
  exact ⟨m, hm, (map_pow _ _ m).symm.trans (d.toG_eq_toG_iff.2 hK).symm⟩

theorem mem_zpowers_gen {i : ℕ} (g : d.G i) : g ∈ Subgroup.zpowers (d.gen i) := by
  obtain ⟨m, -, rfl⟩ := d.exists_gen_pow i g
  exact Subgroup.npow_mem_zpowers _ m

theorem zpowers_gen (i : ℕ) : Subgroup.zpowers (d.gen i) = ⊤ :=
  eq_top_iff.2 fun g _ => d.mem_zpowers_gen g

instance (i : ℕ) : IsCyclic (d.G i) := ⟨⟨d.gen i, fun g => d.mem_zpowers_gen g⟩⟩

theorem gen_pow_pow_eq_one_iff {i k : ℕ} : d.gen i ^ (p ^ k) = 1 ↔ i + 1 ≤ k := by
  rw [gen, ← map_pow, toG_eq_one_iff, K, PadicTail.gen_pow_pow_mem_iff, depth]
  omega

theorem orderOf_gen (i : ℕ) : orderOf (d.gen i) = p ^ (i + 1) :=
  orderOf_eq_prime_pow (by rw [gen_pow_pow_eq_one_iff]; omega) (by rw [gen_pow_pow_eq_one_iff])

theorem natCard_G (i : ℕ) : Nat.card (d.G i) = p ^ (i + 1) :=
  (orderOf_eq_card_of_forall_mem_zpowers d.mem_zpowers_gen).symm.trans (d.orderOf_gen i)

instance (i : ℕ) : Finite (d.G i) :=
  Nat.finite_of_card_ne_zero (by rw [natCard_G]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)

instance (i : ℕ) : Fintype (d.G i) := Fintype.ofFinite _

instance (i : ℕ) : DecidableEq (d.G i) := Classical.decEq _

instance (i : ℕ) : Fintype (d.G i ⧸ d.P i) := Fintype.ofFinite _

/-- `|G_i| = p^(i+1)`, the form used in Theorem 6.3 (`prime_dvd_ratSignature_of_annihilation`). -/
theorem card_G (i : ℕ) : Fintype.card (d.G i) = p ^ (i + 1) := by
  rw [← Nat.card_eq_fintype_card, natCard_G]

/-- `G_i = C_{p^{a_i}}` with `a_i = i + 1` (L45). -/
def mulEquivZMod (i : ℕ) : d.G i ≃* Multiplicative (ZMod (p ^ (i + 1))) :=
  mulEquivOfCyclicCardEq (by rw [natCard_G, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
    ZMod.card])

/-- The generator lies outside `P_i` (§6, L444–450). -/
theorem gen_notMem_P (i : ℕ) : d.gen i ∉ d.P i := by
  rw [gen, toG_mem_P, PadicTail.val_gen, pow_mem_padicPowerSubgroup_iff]
  omega

theorem π_gen_ne_one (i : ℕ) : d.π i (d.gen i) ≠ 1 := d.gen_notMem_P i

/-- `[G_i : P_i] = p` (L45). -/
theorem index_P (i : ℕ) : (d.P i).index = p := by
  rw [P, Subgroup.index_ker, MonoidHom.range_eq_top.2 (d.π_surjective i), Subgroup.card_top,
    card_Cp]

/-- `G_i/P_i ≅ C_p` (L45). -/
def quotientPEquiv (i : ℕ) : d.G i ⧸ d.P i ≃* d.Cp :=
  QuotientGroup.quotientKerEquivOfSurjective _ (d.π_surjective i)

/-! ### The central sequence `q_i = |G_i|` (10.2) -/

/-- `q_i = |G_i|` (10.2), as a rational sequence. -/
def q (i : ℕ) : ℚ := Fintype.card (d.G i)

theorem q_eq (i : ℕ) : d.q i = (p : ℚ) ^ (i + 1) := by
  rw [q, card_G, Nat.cast_pow]

theorem q_pos (i : ℕ) : 0 < d.q i := by
  rw [q_eq]
  exact pow_pos (Nat.cast_pos.2 (Fact.out : p.Prime).pos) _

theorem q_ne_zero (i : ℕ) : d.q i ≠ 0 := (d.q_pos i).ne'

theorem isUnit_q : IsUnit d.q := Pi.isUnit_iff.2 fun i => (d.q_ne_zero i).isUnit

/-! ### Coset representatives `h_g ∈ H` (L610) -/

open Classical in
/-- Representatives `h_g ∈ H` of `g ∈ G_i`, with `h_1 = 1` (L610). -/
def rep (i : ℕ) (g : d.G i) : PadicTail p d.j :=
  if g = 1 then 1 else Function.surjInv (d.toG_surjective i) g

@[simp]
theorem toG_rep (i : ℕ) (g : d.G i) : d.toG i (d.rep i g) = g := by
  unfold rep
  split_ifs with h
  · rw [h, map_one]
  · exact Function.surjInv_eq _ g

@[simp]
theorem rep_one (i : ℕ) : d.rep i 1 = 1 := ite_eq_left rfl

/-- `χ(h_g) = π_i(g)`. -/
@[simp]
theorem χ_rep (i : ℕ) (g : d.G i) : d.χ (d.rep i g) = d.π i g := by
  rw [← π_toG, toG_rep]

/-- `k_{g,h} = h_{gh}⁻¹ h_g h_h` (L610). -/
def cocycle (i : ℕ) (g h : d.G i) : PadicTail p d.j := (d.rep i (g * h))⁻¹ * (d.rep i g * d.rep i h)

/-- `k_{g,h} ∈ K_i` (L610). -/
theorem cocycle_mem_K (i : ℕ) (g h : d.G i) : d.cocycle i g h ∈ d.K i := by
  rw [cocycle, ← toG_eq_toG_iff, map_mul, toG_rep, toG_rep, toG_rep]

/-- `h_g h_h = h_{gh} k_{g,h}` (L610). -/
theorem rep_mul_rep (i : ℕ) (g h : d.G i) :
    d.rep i g * d.rep i h = d.rep i (g * h) * d.cocycle i g h := by
  rw [cocycle, mul_inv_cancel_left]

theorem val_rep_add_val_rep (i : ℕ) (g h : d.G i) :
    (d.rep i g).val + (d.rep i h).val = (d.rep i (g * h)).val + (d.cocycle i g h).val := by
  rw [← PadicTail.val_mul, ← PadicTail.val_mul, rep_mul_rep]

theorem rep_smul_rep_smul (i : ℕ) (g h : d.G i) (x : M) :
    d.rep i g • d.rep i h • x = d.rep i (g * h) • d.cocycle i g h • x := by
  rw [← mul_smul, ← mul_smul, rep_mul_rep]

theorem rep_eq_of_toG (i : ℕ) {g : d.G i} {h : PadicTail p d.j} (hg : d.toG i h = g) :
    (d.rep i g)⁻¹ * h ∈ d.K i := by
  rw [← toG_eq_toG_iff, toG_rep, hg]

theorem fS_rep_smul (i : ℕ) (g : d.G i) (x : M) : d.fS (d.rep i g • x) = d.fS x :=
  d.fS_smul _ x

/-- The labels `(ρ̃, f)` move by `π_i(g)` under `h_g` (L547, L735, (10.1)). -/
theorem labelMap_rep_smul (i : ℕ) (g : d.G i) (x : d.ZplusAction) :
    d.labelMap (d.rep i g • x) = d.π i g • d.labelMap x := by
  rw [labelMap_smul, χ_rep]

/-! ### Displacement of `K_i` (L536, L612) -/

section Displacement

variable [ContinuousVAdd ℤ_[p] M]

/-- `d_i = sup_{k ∈ K_i, x ∈ Q} |kx - x| → 0` on the fixed compact chart saturation `Q`
(L536, L612). -/
theorem eventually_K_displacement_lt {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∀ k ∈ d.K i, ∀ x ∈ d.Q,
      k • x ∈ d.φ.source ∧ ‖d.φ (k • x) - d.φ x‖ < ε :=
  (d.eventually_displacement_lt d.tendsto_depth hε).mono fun _ hi k hk x hx => hi k.val hk x hx

/-- The cocycles `k_{g,h}` have uniformly small displacement on `Q` (L612). -/
theorem eventually_cocycle_displacement_lt {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∀ g h : d.G i, ∀ x ∈ d.Q,
      d.cocycle i g h • x ∈ d.φ.source ∧ ‖d.φ (d.cocycle i g h • x) - d.φ x‖ < ε :=
  (d.eventually_K_displacement_lt hε).mono fun i hi g h => hi _ (d.cocycle_mem_K i g h)

end Displacement

end FixedData

end HSFormal
