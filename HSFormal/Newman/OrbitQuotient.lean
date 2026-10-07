import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.ZMod.QuotientGroup

/-!
# N6. The orbit space of a free periodic map

Setting (blueprint `newman.md` §2.3): `W` is a subset of a metric space `E` (in the application
`E = EuclideanSpace ℝ (Fin (m + 1))` and `W` is open), and `g : E → E` maps `W` to itself, is
continuous on `W`, and satisfies `g^[p] = id` on `W`.

* `orbitPerm`, `orbitHomeo`: `g` restricted to `W`, as a permutation / homeomorphism of `W`
  (inverse `g^[p-1]`).
* `OrbitGroup = ⟨orbitHomeo⟩ ≤ (W ≃ₜ W)`, finite, acting continuously on `W`.
* `OrbitQuot = W / OrbitGroup` with quotient map `orbitMk`; it is `T2` (instance),
  locally compact if `W` is open in a locally compact `E`, and `orbitMk` is an open quotient map,
  and a local homeomorphism when the action is free.
* For `p` prime and `g` without fixed points on `W`: `isCancelSMul_of_free`, `exists_slice`,
  `sliceChart` (a chart of `OrbitQuot` with target a slice ball), and the orbit lemmas used in the
  transfer argument (§2.4, T1–T5).
* `descend`: an invariant map continuous on `W` descends to `C(OrbitQuot, Y)`.
* Invariant subsets (used in §2.5, §2.6): `iterate`-saturations, removal of fixed points.
-/

open Set Function Topology Metric Filter

namespace HSFormal.Newman

/-! ### Generalities -/

/-- A finite group acting by homeomorphisms on a Hausdorff space has a Hausdorff orbit space.
(Mathlib's `t2Space_of_properlyDiscontinuousSMul_of_t2Space` also asks for local compactness.) -/
theorem t2Space_quotient_of_finite {Γ T : Type*} [Group Γ] [Finite Γ] [TopologicalSpace T]
    [MulAction Γ T] [ContinuousConstSMul Γ T] [T2Space T] :
    T2Space (Quotient (MulAction.orbitRel Γ T)) := by
  let := MulAction.orbitRel Γ T
  let f : T → Quotient (MulAction.orbitRel Γ T) := Quotient.mk'
  have f_op : IsOpenMap f := isOpenMap_quotient_mk'_mul
  refine ⟨fun a b hab => ?_⟩
  induction a using Quotient.inductionOn' with | h x => ?_
  induction b using Quotient.inductionOn' with | h y => ?_
  have hγ : ∀ γ : Γ, γ • x ≠ y := fun γ h =>
    hab (Quotient.sound' (MulAction.mem_orbit_iff.2 ⟨γ, h⟩ : MulAction.orbitRel Γ T y x)).symm
  choose u v hu hv hxu hyv huv using fun γ : Γ => t2_separation (hγ γ)
  let U₀ := ⋂ γ : Γ, (γ • ·) ⁻¹' u γ
  let V₀ := ⋂ γ : Γ, v γ
  have hU₀ : IsOpen U₀ := isOpen_iInter_of_finite fun γ => (hu γ).preimage (continuous_const_smul γ)
  have hV₀ : IsOpen V₀ := isOpen_iInter_of_finite hv
  refine ⟨f '' U₀, f '' V₀, f_op _ hU₀, f_op _ hV₀, ⟨x, mem_iInter.2 hxu, rfl⟩,
    ⟨y, mem_iInter.2 hyv, rfl⟩, ?_⟩
  rw [Set.disjoint_left]
  rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
  obtain ⟨γ, hγa⟩ := MulAction.mem_orbit_iff.1 (Quotient.exact' hba : MulAction.orbitRel Γ T b a)
  refine Set.disjoint_left.1 (huv γ) (mem_iInter.1 ha γ) ?_
  change γ • a ∈ v γ
  rw [hγa]
  exact mem_iInter.1 hb γ

/-! ### Iterates on an invariant set -/

section Iterate

variable {E : Type*} {p : ℕ} {W : Set E} {g : E → E}

theorem iterate_sub_iterate (hper : ∀ w ∈ W, g^[p] w = w) {k : ℕ} (hk : k ≤ p) {w : E}
    (hw : w ∈ W) : g^[p - k] (g^[k] w) = w := by
  rw [← iterate_add_apply, Nat.sub_add_cancel hk, hper w hw]

theorem iterate_iterate_sub (hper : ∀ w ∈ W, g^[p] w = w) {k : ℕ} (hk : k ≤ p) {w : E}
    (hw : w ∈ W) : g^[k] (g^[p - k] w) = w := by
  rw [← iterate_add_apply, Nat.add_sub_cancel' hk, hper w hw]

theorem image_iterate_subset (hgW : MapsTo g W W) {S : Set E} (hS : S ⊆ W) (k : ℕ) :
    g^[k] '' S ⊆ W := by
  rintro _ ⟨s, hs, rfl⟩
  exact hgW.iterate k (hS hs)

/-- `g^[p-k]` undoes `g^[k]` on subsets of `W`. -/
theorem image_iterate_sub_image (hper : ∀ w ∈ W, g^[p] w = w) {k : ℕ} (hk : k ≤ p) {S : Set E}
    (hS : S ⊆ W) : g^[p - k] '' (g^[k] '' S) = S := by
  rw [image_image]
  exact (image_congr fun s hs => iterate_sub_iterate hper hk (hS hs)).trans (image_id' S)

/-- An invariant map is invariant under all iterates. -/
theorem apply_iterate_eq_of_invariant {Y : Type*} {A : E → Y} (hgW : MapsTo g W W)
    (hAg : ∀ w ∈ W, A (g w) = A w) (k : ℕ) {w : E} (hw : w ∈ W) : A (g^[k] w) = A w := by
  induction k generalizing w with
  | zero => rfl
  | succ k ih => rw [iterate_succ_apply, ih (hgW hw), hAg w hw]

/-- Every iterate of `g` is injective on `W` (`g^[p] = id` on `W`, `p ≠ 0`). -/
theorem injOn_iterate [NeZero p] (hgW : MapsTo g W W) (hper : ∀ w ∈ W, g^[p] w = w) (j : ℕ) :
    InjOn g^[j] W := by
  have h1 : InjOn g W := fun w hw w' hw' h => by
    rw [← iterate_sub_iterate hper (k := 1) NeZero.one_le hw,
      ← iterate_sub_iterate hper (k := 1) NeZero.one_le hw', iterate_one, h]
  induction j with
  | zero => rw [iterate_zero]; exact injOn_id W
  | succ j ih => rw [iterate_succ]; exact ih.comp h1 hgW

/-- `g` restricted to `W`, as a permutation of `W`; its inverse is `g^[p-1]`. -/
def orbitPerm [NeZero p] (hgW : MapsTo g W W) (hper : ∀ w ∈ W, g^[p] w = w) : Equiv.Perm W where
  toFun := hgW.restrict
  invFun := (hgW.iterate (p - 1)).restrict
  left_inv w := Subtype.ext <| by
    simpa using iterate_sub_iterate hper (k := 1) NeZero.one_le w.2
  right_inv w := Subtype.ext <| by
    simpa using iterate_iterate_sub hper (k := 1) NeZero.one_le w.2

@[simp]
theorem coe_orbitPerm_apply [NeZero p] (hgW : MapsTo g W W) (hper : ∀ w ∈ W, g^[p] w = w)
    (w : W) : (orbitPerm hgW hper w : E) = g w :=
  rfl

/-! #### Prime period, no fixed points -/

theorem minimalPeriod_eq_of_free [hp : Fact p.Prime] (hper : ∀ w ∈ W, g^[p] w = w)
    (hfree : ∀ w ∈ W, g w ≠ w) {w : E} (hw : w ∈ W) : minimalPeriod g w = p := by
  rcases hp.out.eq_one_or_self_of_dvd _
      (IsPeriodicPt.minimalPeriod_dvd (show IsPeriodicPt g p w from hper w hw)) with h | h
  · exact absurd (minimalPeriod_eq_one_iff_isFixedPt.1 h) (hfree w hw)
  · exact h

/-- For `p` prime and `g` fixed-point free on `W`, the `p` points `g^[k] w`, `k < p`, are
distinct. -/
theorem iterate_injOn_Iio_of_free [Fact p.Prime] (hper : ∀ w ∈ W, g^[p] w = w)
    (hfree : ∀ w ∈ W, g w ≠ w) {w : E} (hw : w ∈ W) : InjOn (fun k => g^[k] w) (Iio p) := by
  have := iterate_injOn_Iio_minimalPeriod (f := g) (x := w)
  rwa [minimalPeriod_eq_of_free hper hfree hw] at this

theorem iterate_ne_self_of_free [hp : Fact p.Prime] (hper : ∀ w ∈ W, g^[p] w = w)
    (hfree : ∀ w ∈ W, g w ≠ w) {w : E} (hw : w ∈ W) {k : ℕ} (hk0 : 0 < k) (hkp : k < p) :
    g^[k] w ≠ w := fun h =>
  hk0.ne' (iterate_injOn_Iio_of_free hper hfree hw hkp hp.out.pos (show g^[k] w = g^[0] w from h))

end Iterate

/-! ### The orbit group and the orbit space -/

section Quot

variable {E : Type*} [TopologicalSpace E] {p : ℕ} [NeZero p] {W : Set E} {g : E → E}
variable (hgW : MapsTo g W W) (hgc : ContinuousOn g W) (hper : ∀ w ∈ W, g^[p] w = w)

/-- `g` restricted to `W`, as a homeomorphism of `W`; its inverse is `g^[p-1]`. -/
def orbitHomeo : W ≃ₜ W where
  toEquiv := orbitPerm hgW hper
  continuous_toFun := hgc.mapsToRestrict hgW
  continuous_invFun := (hgc.iterate hgW (p - 1)).mapsToRestrict (hgW.iterate (p - 1))

/-- The group `⟨g⟩ ≤ Homeo(W)`. -/
abbrev OrbitGroup : Subgroup (W ≃ₜ W) :=
  Subgroup.zpowers (orbitHomeo hgW hgc hper)

/-- The orbit space `W / ⟨g⟩`. -/
abbrev OrbitQuot : Type _ :=
  MulAction.orbitRel.Quotient (OrbitGroup hgW hgc hper) W

/-- The quotient map `π : W → W / ⟨g⟩`. -/
def orbitMk : W → OrbitQuot hgW hgc hper :=
  Quotient.mk _

variable {hgW hgc hper}

@[simp]
theorem coe_orbitHomeo_apply (w : W) : (orbitHomeo hgW hgc hper w : E) = g w :=
  rfl

theorem coe_orbitHomeo_pow_apply (k : ℕ) (w : W) :
    ((orbitHomeo hgW hgc hper ^ k) w : E) = g^[k] w := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Homeomorph.mul_apply, coe_orbitHomeo_apply, ih, iterate_succ_apply']

theorem orbitHomeo_pow_self : orbitHomeo hgW hgc hper ^ p = 1 := by
  ext w
  rw [coe_orbitHomeo_pow_apply, Homeomorph.one_apply]
  exact hper w w.2

theorem mem_orbitGroup_iff {σ : W ≃ₜ W} :
    σ ∈ OrbitGroup hgW hgc hper ↔ ∃ k < p, orbitHomeo hgW hgc hper ^ k = σ := by
  constructor
  · intro hσ
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hσ
    have hp : (0 : ℤ) < p := by exact_mod_cast Nat.pos_of_neZero p
    have h0 := Int.emod_nonneg k hp.ne'
    have h1 := Int.emod_lt_of_pos k hp
    refine ⟨(k % p).toNat, by omega, ?_⟩
    rw [zpow_eq_zpow_emod' k orbitHomeo_pow_self, ← zpow_natCast, Int.toNat_of_nonneg h0]
  · rintro ⟨k, -, rfl⟩
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) k

instance : Finite (OrbitGroup hgW hgc hper) :=
  finite_zpowers.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨p, Nat.pos_of_neZero p, orbitHomeo_pow_self⟩)

theorem orbitGroup_smul_def (σ : OrbitGroup hgW hgc hper) (w : W) :
    σ • w = (σ : W ≃ₜ W) w :=
  rfl

instance : ContinuousConstSMul (OrbitGroup hgW hgc hper) W :=
  ⟨fun σ => (σ : W ≃ₜ W).continuous⟩

instance [T2Space E] : T2Space (OrbitQuot hgW hgc hper) :=
  t2Space_quotient_of_finite

theorem continuous_orbitMk : Continuous (orbitMk hgW hgc hper) :=
  continuous_quot_mk

theorem isOpenMap_orbitMk : IsOpenMap (orbitMk hgW hgc hper) :=
  isOpenMap_quotient_mk'_mul

theorem surjective_orbitMk : Surjective (orbitMk hgW hgc hper) :=
  Quotient.mk_surjective

theorem isOpenQuotientMap_orbitMk : IsOpenQuotientMap (orbitMk hgW hgc hper) :=
  MulAction.isOpenQuotientMap_quotientMk

/-- The orbit space of an open subset of a locally compact space is locally compact. -/
theorem locallyCompactSpace_orbitQuot [LocallyCompactSpace E] (hW : IsOpen W) :
    LocallyCompactSpace (OrbitQuot hgW hgc hper) := by
  have := hW.locallyCompactSpace
  exact isOpenQuotientMap_orbitMk.locallyCompactSpace

/-- Two points have the same image in `W / ⟨g⟩` iff one is `g^[k]` of the other, `k < p`. -/
theorem orbitMk_eq_orbitMk_iff {w w' : W} :
    orbitMk hgW hgc hper w = orbitMk hgW hgc hper w' ↔ ∃ k < p, (w : E) = g^[k] w' := by
  unfold orbitMk
  rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨σ, hσ⟩
    obtain ⟨k, hk, hk'⟩ := mem_orbitGroup_iff.1 σ.2
    refine ⟨k, hk, ?_⟩
    rw [← hσ, orbitGroup_smul_def, ← hk', coe_orbitHomeo_pow_apply]
  · rintro ⟨k, hk, h⟩
    refine ⟨⟨_, mem_orbitGroup_iff.2 ⟨k, hk, rfl⟩⟩, Subtype.ext ?_⟩
    rw [orbitGroup_smul_def, coe_orbitHomeo_pow_apply, h]

theorem orbitMk_iterate (k : ℕ) (w : W) (hk : g^[k] w ∈ W) :
    orbitMk hgW hgc hper ⟨g^[k] w, hk⟩ = orbitMk hgW hgc hper w := by
  unfold orbitMk
  apply Quotient.sound
  exact MulAction.orbitRel_apply.2
    ⟨⟨_, Subgroup.pow_mem _ (Subgroup.mem_zpowers _) k⟩, Subtype.ext (coe_orbitHomeo_pow_apply k w)⟩

theorem orbitMk_apply_eq (w : W) (hw : g w ∈ W) :
    orbitMk hgW hgc hper ⟨g w, hw⟩ = orbitMk hgW hgc hper w :=
  orbitMk_iterate 1 w hw

/-- The fibre of `π` through `x` is the orbit `{g^[k] x | k < p}`. -/
theorem orbitMk_preimage_singleton (x : W) :
    orbitMk hgW hgc hper ⁻¹' {orbitMk hgW hgc hper x} =
      Subtype.val ⁻¹' ((fun k => g^[k] (x : E)) '' Iio p) := by
  ext w
  simp only [mem_preimage, mem_singleton_iff, mem_image, mem_Iio, orbitMk_eq_orbitMk_iff]
  exact ⟨fun ⟨k, hk, h⟩ => ⟨k, hk, h.symm⟩, fun ⟨k, hk, h⟩ => ⟨k, hk, h.symm⟩⟩

/-- The saturation of `S ⊆ W` is `⋃_{k<p} g^[k] S`. -/
theorem orbitMk_preimage_image {S : Set E} (hS : S ⊆ W) :
    orbitMk hgW hgc hper ⁻¹' (orbitMk hgW hgc hper '' (Subtype.val ⁻¹' S)) =
      Subtype.val ⁻¹' (⋃ k ∈ Iio p, g^[k] '' S) := by
  ext w
  simp only [mem_preimage, mem_image, mem_iUnion, mem_Iio, exists_prop]
  constructor
  · rintro ⟨w', hw'S, hw'⟩
    obtain ⟨k, hk, h⟩ := orbitMk_eq_orbitMk_iff.1 hw'.symm
    exact ⟨k, hk, w', hw'S, h.symm⟩
  · rintro ⟨k, hk, s, hs, hsw⟩
    exact ⟨⟨s, hS hs⟩, hs, (orbitMk_eq_orbitMk_iff.2 ⟨k, hk, hsw.symm⟩).symm⟩

/-- `π (g^[k] S) = π S` for `S ⊆ W`. -/
theorem image_orbitMk_image_iterate {S : Set E} (hS : S ⊆ W) (k : ℕ) :
    orbitMk hgW hgc hper '' (Subtype.val ⁻¹' (g^[k] '' S)) =
      orbitMk hgW hgc hper '' (Subtype.val ⁻¹' S) := by
  ext q
  constructor
  · rintro ⟨w, ⟨s, hs, hsw⟩, rfl⟩
    refine ⟨⟨s, hS hs⟩, hs, ?_⟩
    have hw : w = ⟨g^[k] s, hsw ▸ w.2⟩ := Subtype.ext hsw.symm
    rw [hw, orbitMk_iterate k ⟨s, hS hs⟩]
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨g^[k] w, hgW.iterate k w.2⟩, ⟨w, hw, rfl⟩, orbitMk_iterate k w _⟩

/-- `π (⋃_{k<p} g^[k] S) = π S` for `S ⊆ W` (§2.4 T1: `π K' = ⋃_j π C_j`). -/
theorem image_orbitMk_iUnion_image_iterate {S : Set E} (hS : S ⊆ W) :
    orbitMk hgW hgc hper '' (Subtype.val ⁻¹' (⋃ k ∈ Iio p, g^[k] '' S)) =
      orbitMk hgW hgc hper '' (Subtype.val ⁻¹' S) := by
  rw [← orbitMk_preimage_image hS, image_preimage_eq _ surjective_orbitMk]

/-- `g^[k]` maps open subsets of an open `W` to open sets. -/
theorem isOpen_image_iterate (hgW : MapsTo g W W) (hgc : ContinuousOn g W)
    (hper : ∀ w ∈ W, g^[p] w = w) (hW : IsOpen W) {S : Set E} (hS : IsOpen S) (hSW : S ⊆ W)
    (k : ℕ) : IsOpen (g^[k] '' S) := by
  have : g^[k] '' S =
      Subtype.val '' ((orbitHomeo hgW hgc hper ^ k) '' (Subtype.val ⁻¹' S)) := by
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨_, ⟨⟨s, hSW hs⟩, hs, rfl⟩, coe_orbitHomeo_pow_apply k _⟩
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨w, hw, (coe_orbitHomeo_pow_apply k w).symm⟩
  rw [this]
  exact hW.isOpenMap_subtype_val _
    ((orbitHomeo hgW hgc hper ^ k).isOpenMap _ (hS.preimage continuous_subtype_val))

/-! #### Descending invariant maps -/

variable (hgW hgc hper) in
/-- A `g`-invariant map, continuous on `W`, descends to the orbit space. -/
def descend {Y : Type*} [TopologicalSpace Y] (A : E → Y) (hA : ContinuousOn A W)
    (hAg : ∀ w ∈ W, A (g w) = A w) : C(OrbitQuot hgW hgc hper, Y) where
  toFun := Quotient.lift (W.domRestrict A) fun a b hab => by
    obtain ⟨k, -, hk⟩ := orbitMk_eq_orbitMk_iff.1
      (Quotient.sound hab : orbitMk hgW hgc hper a = orbitMk hgW hgc hper b)
    change A a = A b
    rw [hk, apply_iterate_eq_of_invariant hgW hAg k b.2]
  continuous_toFun := hA.domRestrict.quotient_lift _

section Descend

variable {Y : Type*} [TopologicalSpace Y] {A : E → Y} {hA : ContinuousOn A W}
  {hAg : ∀ w ∈ W, A (g w) = A w}

@[simp]
theorem descend_orbitMk (w : W) :
    descend hgW hgc hper A hA hAg (orbitMk hgW hgc hper w) = A w :=
  rfl

theorem descend_comp_orbitMk :
    descend hgW hgc hper A hA hAg ∘ orbitMk hgW hgc hper = W.domRestrict A :=
  rfl

theorem preimage_descend (S : Set Y) :
    descend hgW hgc hper A hA hAg ⁻¹' S = orbitMk hgW hgc hper '' (W.domRestrict A ⁻¹' S) := by
  ext q
  obtain ⟨w, rfl⟩ := surjective_orbitMk q
  constructor
  · intro h
    exact ⟨w, h, rfl⟩
  · rintro ⟨w', hw', hw'w⟩
    rw [mem_preimage, ← hw'w, descend_orbitMk]
    exact hw'

end Descend

/-! #### Free actions (`p` prime) -/

section Free

variable [hp : Fact p.Prime]

variable (hgW hgc hper) in
/-- For `p` prime and `g` fixed-point free on `W`, `⟨g⟩` acts freely on `W`. -/
theorem isCancelSMul_of_free (hfree : ∀ w ∈ W, g w ≠ w) :
    IsCancelSMul (OrbitGroup hgW hgc hper) W := by
  rw [isCancelSMul_iff_stabilizer_eq_bot]
  intro w
  rw [Subgroup.eq_bot_iff_forall]
  intro σ hσ
  obtain ⟨k, hk, hσk⟩ := mem_orbitGroup_iff.1 σ.2
  rw [MulAction.mem_stabilizer_iff, orbitGroup_smul_def] at hσ
  have h1 : g^[k] (w : E) = g^[0] w := by
    rw [← coe_orbitHomeo_pow_apply (hgW := hgW) (hgc := hgc) (hper := hper), hσk]
    exact congrArg Subtype.val hσ
  obtain rfl : k = 0 := iterate_injOn_Iio_of_free hper hfree w.2 hk hp.out.pos h1
  exact Subtype.ext (by rw [← hσk, pow_zero]; rfl)

/-- For a free action on an open `W ⊆ E` (`E` locally compact Hausdorff), `π` is a local
homeomorphism. -/
theorem isLocalHomeomorph_orbitMk [T2Space E] [LocallyCompactSpace E] (hW : IsOpen W)
    (hfree : ∀ w ∈ W, g w ≠ w) : IsLocalHomeomorph (orbitMk hgW hgc hper) := by
  have := hW.locallyCompactSpace
  have := isCancelSMul_of_free hgW hgc hper hfree
  have : ProperlyDiscontinuousSMul (OrbitGroup hgW hgc hper) W :=
    Finite.to_properlyDiscontinuousSMul
  exact isLocalHomeomorph_quotientMk_of_properlyDiscontinuousSMul

end Free

end Quot

/-! ### Slices and charts of the orbit space -/

section Slice

variable {E : Type*} [MetricSpace E] {p : ℕ} {W : Set E} {g : E → E}

/-- **Slices.** For `p` prime and `g` fixed-point free on the open set `W`, every `x ∈ W` has a
ball `B(x,δ)`, with `B̄(x,δ) ⊆ W`, whose translates `g^[k] B(x,δ)`, `k < p`, are pairwise
disjoint. -/
theorem exists_slice [Fact p.Prime] (hW : IsOpen W) (hgW : MapsTo g W W)
    (hgc : ContinuousOn g W) (hper : ∀ w ∈ W, g^[p] w = w) (hfree : ∀ w ∈ W, g w ≠ w) {x : E}
    (hx : x ∈ W) :
    ∃ δ > 0, closedBall x δ ⊆ W ∧
      ∀ k < p, ∀ j < p, k ≠ j → Disjoint (g^[k] '' ball x δ) (g^[j] '' ball x δ) := by
  have hcont : ∀ k, ContinuousAt g^[k] x := fun k =>
    (hgc.iterate hgW k).continuousAt (hW.mem_nhds hx)
  have hev : ∀ᶠ w in 𝓝 x, w ∈ W ∧ ∀ k ∈ Iio p, ∀ j ∈ Iio p, k ≠ j →
      dist (g^[k] w) (g^[k] x) < dist (g^[k] x) (g^[j] x) / 2 ∧
      dist (g^[j] w) (g^[j] x) < dist (g^[k] x) (g^[j] x) / 2 := by
    refine Filter.Eventually.and (hW.mem_nhds hx) ?_
    rw [(finite_Iio p).eventually_all]
    intro k hk
    rw [(finite_Iio p).eventually_all]
    intro j hj
    by_cases hkj : k = j
    · exact Eventually.of_forall fun _ h => absurd hkj h
    · have hpos : 0 < dist (g^[k] x) (g^[j] x) / 2 :=
        half_pos (dist_pos.2 fun h => hkj (iterate_injOn_Iio_of_free hper hfree hx hk hj h))
      filter_upwards [Metric.tendsto_nhds.1 (hcont k) _ hpos,
        Metric.tendsto_nhds.1 (hcont j) _ hpos] with w h1 h2 _
      exact ⟨h1, h2⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine ⟨ε / 2, half_pos hε, fun z hz => (hball z (closedBall_subset_ball (half_lt_self hε) hz)).1,
    ?_⟩
  intro k hk j hj hkj
  rw [Set.disjoint_left]
  rintro _ ⟨w, hw, rfl⟩ ⟨w', hw', hw'w⟩
  have h1 := ((hball w (ball_subset_ball (half_le_self hε.le) hw)).2 k hk j hj hkj).1
  have h2 := ((hball w' (ball_subset_ball (half_le_self hε.le) hw')).2 k hk j hj hkj).2
  have key : dist (g^[k] x) (g^[j] x) ≤ dist (g^[k] w) (g^[k] x) + dist (g^[j] w') (g^[j] x) := by
    rw [hw'w, dist_comm (g^[k] w)]
    exact dist_triangle _ _ _
  linarith

/-- In a slice, the translate `g^[k] B(x,δ)` meets the orbit of `x` only in `g^[k] x`. -/
theorem image_iterate_ball_inter_orbit {x : E} {δ : ℝ} (hδ : 0 < δ)
    (hdisj : ∀ k < p, ∀ j < p, k ≠ j → Disjoint (g^[k] '' ball x δ) (g^[j] '' ball x δ))
    {k : ℕ} (hk : k < p) :
    g^[k] '' ball x δ ∩ (fun j => g^[j] x) '' Iio p = {g^[k] x} := by
  ext z
  constructor
  · rintro ⟨hz, j, hj, rfl⟩
    by_cases hjk : j = k
    · subst hjk
      rfl
    · exact absurd (hdisj k hk j hj (Ne.symm hjk))
        (Set.not_disjoint_iff.2 ⟨_, hz, x, mem_ball_self hδ, rfl⟩)
  · rintro rfl
    exact ⟨⟨x, mem_ball_self hδ, rfl⟩, k, hk, rfl⟩

variable [NeZero p] {hgW : MapsTo g W W} {hgc : ContinuousOn g W} {hper : ∀ w ∈ W, g^[p] w = w}

/-- `π` is injective on a slice ball. -/
theorem orbitMk_injOn_ball {x : E} {δ : ℝ}
    (hdisj : ∀ k < p, ∀ j < p, k ≠ j → Disjoint (g^[k] '' ball x δ) (g^[j] '' ball x δ)) :
    InjOn (orbitMk hgW hgc hper) (Subtype.val ⁻¹' ball x δ) := by
  intro w hw w' hw' h
  obtain ⟨k, hk, hkw⟩ := orbitMk_eq_orbitMk_iff.1 h
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exact Subtype.ext hkw
  · exact absurd (hdisj k hk 0 (Nat.pos_of_neZero p) hk0.ne')
      (Set.not_disjoint_iff.2 ⟨w, ⟨w', hw', hkw.symm⟩, ⟨w, hw, rfl⟩⟩)

open scoped Classical in
variable (hgW hgc hper) in
/-- The chart map of `sliceChart`: `[w] ↦ w` for `w` in the ball `B(x,δ)`
(junk value `x` elsewhere). -/
noncomputable def sliceChartFun (x : E) (δ : ℝ) (q : OrbitQuot hgW hgc hper) : E :=
  if h : ∃ w : W, (w : E) ∈ ball x δ ∧ orbitMk hgW hgc hper w = q then (h.choose : E) else x

theorem sliceChartFun_orbitMk {x : E} {δ : ℝ}
    (hdisj : ∀ k < p, ∀ j < p, k ≠ j → Disjoint (g^[k] '' ball x δ) (g^[j] '' ball x δ))
    {w : W} (hw : (w : E) ∈ ball x δ) :
    sliceChartFun hgW hgc hper x δ (orbitMk hgW hgc hper w) = w := by
  have h : ∃ w' : W, (w' : E) ∈ ball x δ ∧ orbitMk hgW hgc hper w' = orbitMk hgW hgc hper w :=
    ⟨w, hw, rfl⟩
  rw [sliceChartFun, dite_eq_left h]
  exact congrArg Subtype.val (orbitMk_injOn_ball hdisj h.choose_spec.1 hw h.choose_spec.2)

open scoped Classical in
variable (hgW hgc hper) in
/-- **Slice chart.** For a slice ball `B(x,δ)` (as produced by `exists_slice`), the orbit space
`W / ⟨g⟩` has the chart `π(B(x,δ)) → B(x,δ)`, inverse to `π|B(x,δ)`. Its target is `B(x,δ)`,
its source is `π(B(x,δ))`, and its inverse is `z ↦ π z` on `W`. -/
noncomputable def sliceChart {x : E} {δ : ℝ} (hδ : 0 < δ) (hcb : closedBall x δ ⊆ W)
    (hdisj : ∀ k < p, ∀ j < p, k ≠ j → Disjoint (g^[k] '' ball x δ) (g^[j] '' ball x δ)) :
    OpenPartialHomeomorph (OrbitQuot hgW hgc hper) E where
  toFun := sliceChartFun hgW hgc hper x δ
  invFun z := if h : z ∈ W then orbitMk hgW hgc hper ⟨z, h⟩
    else orbitMk hgW hgc hper ⟨x, hcb (mem_closedBall_self hδ.le)⟩
  source := orbitMk hgW hgc hper '' (Subtype.val ⁻¹' ball x δ)
  target := ball x δ
  map_source' := by
    rintro _ ⟨w, hw, rfl⟩
    rw [sliceChartFun_orbitMk hdisj hw]
    exact hw
  map_target' z hz := by
    have hzW : z ∈ W := hcb (ball_subset_closedBall hz)
    simp only [dite_eq_left hzW]
    exact ⟨⟨z, hzW⟩, hz, rfl⟩
  left_inv' := by
    rintro _ ⟨w, hw, rfl⟩
    simp only [sliceChartFun_orbitMk hdisj hw, dite_eq_left w.2]
  right_inv' z hz := by
    have hzW : z ∈ W := hcb (ball_subset_closedBall hz)
    simp only [dite_eq_left hzW]
    exact sliceChartFun_orbitMk (w := ⟨z, hzW⟩) hdisj hz
  open_source := isOpenMap_orbitMk _ (isOpen_ball.preimage continuous_subtype_val)
  open_target := isOpen_ball
  continuousOn_toFun := by
    rw [_root_.continuousOn_iff']
    intro t ht
    refine ⟨orbitMk hgW hgc hper '' (Subtype.val ⁻¹' (t ∩ ball x δ)),
      isOpenMap_orbitMk _ ((ht.inter isOpen_ball).preimage continuous_subtype_val), ?_⟩
    ext q
    constructor
    · rintro ⟨hq, w, hw, rfl⟩
      rw [mem_preimage, sliceChartFun_orbitMk hdisj hw] at hq
      exact ⟨⟨w, ⟨hq, hw⟩, rfl⟩, w, hw, rfl⟩
    · rintro ⟨⟨w, ⟨hwt, hw⟩, rfl⟩, -⟩
      refine ⟨?_, w, hw, rfl⟩
      rw [mem_preimage, sliceChartFun_orbitMk hdisj hw]
      exact hwt
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : (ball x δ).domRestrict (fun z => if h : z ∈ W then orbitMk hgW hgc hper ⟨z, h⟩
        else orbitMk hgW hgc hper ⟨x, hcb (mem_closedBall_self hδ.le)⟩) =
        fun z : ball x δ => orbitMk hgW hgc hper ⟨z, hcb (ball_subset_closedBall z.2)⟩ :=
      funext fun z => dite_eq_left _
    rw [this]
    exact continuous_orbitMk.comp (continuous_subtype_val.subtype_mk _)

section SliceChart

variable {x : E} {δ : ℝ} {hδ : 0 < δ} {hcb : closedBall x δ ⊆ W}
  {hdisj : ∀ k < p, ∀ j < p, k ≠ j → Disjoint (g^[k] '' ball x δ) (g^[j] '' ball x δ)}

@[simp]
theorem sliceChart_source :
    (sliceChart hgW hgc hper hδ hcb hdisj).source =
      orbitMk hgW hgc hper '' (Subtype.val ⁻¹' ball x δ) :=
  rfl

@[simp]
theorem sliceChart_target : (sliceChart hgW hgc hper hδ hcb hdisj).target = ball x δ :=
  rfl

open scoped Classical in
theorem sliceChart_symm_apply {z : E} (hz : z ∈ W) :
    (sliceChart hgW hgc hper hδ hcb hdisj).symm z = orbitMk hgW hgc hper ⟨z, hz⟩ :=
  dite_eq_left hz

theorem sliceChart_apply_orbitMk {w : W} (hw : (w : E) ∈ ball x δ) :
    sliceChart hgW hgc hper hδ hcb hdisj (orbitMk hgW hgc hper w) = w :=
  sliceChartFun_orbitMk hdisj hw

/-- The pieces `e.symm '' C` of the transfer argument (§5, step 2) are `π`-images. -/
theorem sliceChart_symm_image {S : Set E} (hS : S ⊆ ball x δ) :
    (sliceChart hgW hgc hper hδ hcb hdisj).symm '' S =
      orbitMk hgW hgc hper '' (Subtype.val ⁻¹' S) := by
  have hSW : S ⊆ W := hS.trans (ball_subset_closedBall.trans hcb)
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, hSW hz⟩, hz, (sliceChart_symm_apply (hSW hz)).symm⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, sliceChart_symm_apply w.2⟩

end SliceChart

end Slice

/-! ### Invariant subsets (used in §2.5 and §2.6) -/

section Invariant

variable {E : Type*} {q : ℕ} {V : Set E} {g : E → E}

/-- The points of `V` whose first `q` iterates lie in `S` form a `g`-invariant set. -/
theorem mapsTo_setOf_iterate_mem (hgV : MapsTo g V V) (hper : ∀ z ∈ V, g^[q] z = z)
    (hq : 0 < q) (S : Set E) :
    MapsTo g {z | z ∈ V ∧ ∀ k < q, g^[k] z ∈ S} {z | z ∈ V ∧ ∀ k < q, g^[k] z ∈ S} := by
  rintro z ⟨hzV, hzS⟩
  refine ⟨hgV hzV, fun k hk => ?_⟩
  rw [← iterate_succ_apply]
  rcases Nat.lt_or_ge (k + 1) q with h | h
  · exact hzS _ h
  · rw [show k.succ = q by omega, hper z hzV]
    exact hzS 0 hq

/-- `⋃_{k<q} g^[k] S` is `g`-invariant for `S ⊆ V`. -/
theorem mapsTo_iUnion_image_iterate (hper : ∀ z ∈ V, g^[q] z = z) {S : Set E} (hS : S ⊆ V) :
    MapsTo g (⋃ k ∈ Iio q, g^[k] '' S) (⋃ k ∈ Iio q, g^[k] '' S) := by
  intro z hz
  simp only [mem_iUnion, mem_Iio, mem_image, exists_prop] at hz ⊢
  obtain ⟨k, hk, s, hs, rfl⟩ := hz
  rcases Nat.lt_or_ge (k + 1) q with h | h
  · exact ⟨k + 1, h, s, hs, iterate_succ_apply' g k s⟩
  · refine ⟨0, by omega, s, hs, ?_⟩
    rw [← iterate_succ_apply' g k s, show k.succ = q by omega, hper s (hS hs)]
    rfl

/-- Removing the fixed points of an injective `g` leaves a `g`-invariant set. -/
theorem mapsTo_diff_fixedPoints (hgV : MapsTo g V V) (hinj : InjOn g V) :
    MapsTo g (V \ {z | g z = z}) (V \ {z | g z = z}) := by
  rintro z ⟨hzV, hz⟩
  exact ⟨hgV hzV, fun h => hz (hinj (hgV hzV) hzV h)⟩

variable [TopologicalSpace E]

theorem isOpen_setOf_iterate_mem (hV : IsOpen V) (hgV : MapsTo g V V) (hgc : ContinuousOn g V)
    {S : Set E} (hS : IsOpen S) (q : ℕ) :
    IsOpen {z | z ∈ V ∧ ∀ k < q, g^[k] z ∈ S} := by
  have : {z | z ∈ V ∧ ∀ k < q, g^[k] z ∈ S} = V ∩ ⋂ k ∈ Iio q, (V ∩ g^[k] ⁻¹' S) := by
    ext z
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_Iio, mem_preimage]
    exact ⟨fun h => ⟨h.1, fun k hk => ⟨h.1, h.2 k hk⟩⟩, fun h => ⟨h.1, fun k hk => (h.2 k hk).2⟩⟩
  rw [this]
  exact hV.inter ((finite_Iio q).isOpen_biInter fun k _ =>
    (hgc.iterate hgV k).isOpen_inter_preimage hV hS)

theorem isOpen_diff_fixedPoints [T2Space E] (hV : IsOpen V) (hgc : ContinuousOn g V) :
    IsOpen (V \ {z | g z = z}) := by
  have : V \ {z | g z = z} = V ∩ (fun z => (g z, z)) ⁻¹' (diagonal E)ᶜ := by
    ext z
    simp [mem_diagonal_iff]
  rw [this]
  exact (hgc.prodMk continuousOn_id).isOpen_inter_preimage hV isClosed_diagonal.isOpen_compl

end Invariant

end HSFormal.Newman
