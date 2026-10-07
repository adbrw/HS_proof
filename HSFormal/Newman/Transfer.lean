import HSFormal.Newman.TransferStatement

/-!
# N7. Transfer vanishing (Newman blueprint, module N7; §2.4, §5)

Main result: `degree_eq_zero_of_free` (statement frozen in `TransferStatement.lean` as
`DegreeEqZeroOfFree`, proved by `degreeEqZeroOfFree`): for `p` prime, `g` of period `p` and
fixed-point free on the open `W ⊆ 𝔼 = ℝ^{m+1}`, with `ldeg(g^[j]) = 1` on `W` for `0 < j < p`,
and `A` continuous, `g`-invariant, with compact fibre over `y`, `deg(A, W, y) = 0` in `ZMod p`.
It is the `R = ZMod p` case of `degree_eq_zero_of_free_of_natCast_eq_zero` (any commutative
ring `R` with `(p : R) = 0`).

Proof (blueprint T1–T5):
* **T5, local part** `push_restrictMapsTo_orientOn`: for `φ` continuous injective on `W` mapping
  an open `V ⊆ W` into an open `U`, `φ_*(o^V_u) = ldeg_u(φ) • o^U_{φ u}` (excision injectivity
  `push_incl_injective_of_iff` + `degree_spec` + `push_openIncl_orientOn`).
* **T4** `orientOn_orbit_eq_sum`: for a slice `B(x, δ)` (from N6 `exists_slice`), with
  `U_k = g^[k] B(x, δ)`, `o^W_O = Σ_{k : Fin p} (U_k ⊆ W)_*(o^{U_k}_{g^k x})`, `O = π⁻¹(π x)`
  (`orbitSet`), by `pointInj_of_isOpen_of_finite` (N5) and `push_eq_zero_of_forall_notMem` for
  the off-diagonal terms.
* **T5** `push_orbitHom_orientOn_orbitSet`: `π_*(o^W_O) = 0` in `H_{m+1}(W/⟨g⟩ | π x)`: on `U_k`,
  `π = π|U ∘ g^[p-k]`, every term equals `(π|U)_*(o^U_x)` (using `hldeg`, and
  `ldeg_iterate_period_eq_one` for `k = 0`), and `p = 0` in `R`.
* **T1–T3** in `degree_eq_zero_of_free_of_natCast_eq_zero`: half slices `B̄(x_j, δ_j / 2)` cover
  the fibre; `M = π(⋃_j B̄(x_j, δ_j / 2))` is the union of the chart-convex pieces
  `(sliceChart_j).symm '' B̄(x_j, δ_j / 2)`, so `PointInj (W/⟨g⟩) M` (N4); `K' = π⁻¹ M` is
  compact, saturated and contains the fibre; `A = Ā ∘ π` (`descend`), and every pointwise
  restriction of `π_*(o^W_{K'})` is `π_*(o^W_O) = 0`.

## Deviations from the blueprint

* `π` is N6's `orbitMk` packaged as `orbitHom : TopCat.of W ⟶ TopCat.of (OrbitQuot …)`; the orbit
  is the fibre `orbitSet … x = π⁻¹ {π x}`, and T4 sums over `Fin p`.
* The ring is general (`(p : R) = 0`) in the auxiliary results; only `degree_eq_zero_of_free`
  fixes `R = ZMod p`.
-/

open CategoryTheory Limits Topology Metric Set Function

namespace HSFormal.Newman

variable {R : Type} [CommRing R] {m : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin (m + 1))

section LocalTransfer

omit [CommRing R] in
lemma isCompact_setOf_val_eq (V : Set (EuclideanSpace ℝ (Fin (m + 1))))
    (t : EuclideanSpace ℝ (Fin (m + 1))) : IsCompact {v : V | (v : 𝔼) = t} :=
  Set.Subsingleton.isCompact fun _ ha _ hb => Subtype.ext (ha.trans hb.symm)

/-- Excision injectivity `H_i(V | K) ⟶ H_i(𝔼 | L')` for `K = V ∩ L'`, `L'` closed in `V`. -/
lemma push_incl_injective_of_iff {V : Set 𝔼} (hV : IsOpen V) {K : Set V} {L' : Set 𝔼}
    (hL'c : IsClosed L') (hsub : L' ⊆ V) (hiff : ∀ v : V, (v : 𝔼) ∈ L' ↔ v ∈ K) (i : ℕ) :
    Function.Injective (push R (incl (X := TopCat.of 𝔼) V) (L := K) (L' := L')
      (fun v hv => (hiff v).1 hv) i) := by
  have hrange : L' ⊆ Set.range (incl (X := TopCat.of 𝔼) V) := fun z hz => ⟨⟨z, hsub hz⟩, rfl⟩
  have := isIso_push_of_isOpenEmbedding (R := R) (f := incl (X := TopCat.of 𝔼) V)
    (isOpenEmbedding_incl hV) (L := K) (L' := L')
    (fun v hv => (hiff v).1 hv) (fun v hv => (hiff v).2 hv) hL'c hrange i
  exact injective_of_isIso _

/-- `φ|V : V ⟶ U` as a morphism of `TopCat`, for `φ` mapping `V` into `U`. -/
noncomputable def restrictMapsTo {V U : Set (EuclideanSpace ℝ (Fin (m + 1)))}
    (φ : EuclideanSpace ℝ (Fin (m + 1)) → EuclideanSpace ℝ (Fin (m + 1)))
    (hφ : ContinuousOn φ V) (hVU : MapsTo φ V U) : TopCat.of V ⟶ TopCat.of U :=
  TopCat.ofHom ⟨hVU.restrict, hφ.mapsToRestrict hVU⟩

omit [CommRing R] in
lemma restrictMapsTo_cond {W V U : Set 𝔼} (hVW : V ⊆ W) {φ : 𝔼 → 𝔼} (hφc : ContinuousOn φ V)
    (hφi : InjOn φ W) (hVU : MapsTo φ V U) {u t : 𝔼} (hu : u ∈ V) (ht : φ u = t) :
    ∀ v, restrictMapsTo φ hφc hVU v ∈ {w : U | (w : 𝔼) = t} → v ∈ {v : V | (v : 𝔼) = u} :=
  fun v hv => hφi (hVW v.2) (hVW hu) (hv.trans ht.symm)

/-- **Local transfer (T5).** For `φ` continuous and injective on `W`, mapping the open `V ⊆ W`
into the open `U`, and `u ∈ V` with `φ u = t`, the map `H(V | u) ⟶ H(U | t)` induced by `φ`
sends `o^V_u` to `ldeg_u(φ) • o^U_t`. -/
theorem push_restrictMapsTo_orientOn {W V U : Set 𝔼} (hW : IsOpen W) (hV : IsOpen V)
    (hU : IsOpen U) (hVW : V ⊆ W) {φ : 𝔼 → 𝔼} (hφc : ContinuousOn φ W) (hφi : InjOn φ W)
    (hVU : MapsTo φ V U) {u t : 𝔼} (hu : u ∈ V) (ht : φ u = t) :
    push R (restrictMapsTo φ (hφc.mono hVW) hVU)
        (restrictMapsTo_cond hVW (hφc.mono hVW) hφi hVU hu ht) (m + 1)
        (orientOn R hV (isCompact_setOf_val_eq V u)) =
      ldeg R hW φ hφc hφi u (hVW hu) • orientOn R hU (isCompact_setOf_val_eq U t) := by
  subst ht
  have hmem : φ u ∈ U := hVU hu
  apply push_incl_injective_of_iff (R := R) hU (K := {w : U | (w : 𝔼) = φ u}) (L' := {φ u})
    isClosed_singleton (singleton_subset_iff.2 hmem) (fun w => Iff.rfl) (m + 1)
  have hK := isCompact_fibre_of_injOn hφi (hVW hu)
  have himg : Subtype.val '' {v : V | (v : 𝔼) = u} = Subtype.val '' {w : W | φ w = φ u} := by
    ext z
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨⟨v, hVW v.2⟩, congrArg φ hv, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      have : (w : 𝔼) = u := hφi w.2 (hVW hu) hw
      exact ⟨⟨u, hu⟩, rfl, this.symm⟩
  have h1 := push_openIncl_orientOn (R := R) hV hW hVW (isCompact_setOf_val_eq V u) hK himg
    (fun v hv => hφi (hVW v.2) (hVW hu) hv)
  have h2 := degree_spec (R := R) (hW := hW) (A := φ) (hA := hφc) (y := φ u) hK
  -- left-hand side
  refine (push_push_apply (L' := {w : U | (w : 𝔼) = φ u}) (L'' := {φ u})
    (restrictMapsTo φ (hφc.mono hVW) hVU) (incl (X := TopCat.of 𝔼) U)
    (openIncl hVW ≫ restrictHom φ hφc) rfl _ _
    (fun v hv => hφi (hVW v.2) (hVW hu) hv) (m + 1) _).trans ?_
  refine (push_push_apply (L' := {w : W | φ w = φ u}) (L'' := {φ u}) (openIncl hVW)
    (restrictHom φ hφc) (openIncl hVW ≫ restrictHom φ hφc) rfl
    (fun v hv => hφi (hVW v.2) (hVW hu) hv) (fun _ hw => Set.mem_singleton_iff.1 hw)
    (fun v hv => hφi (hVW v.2) (hVW hu) hv) (m + 1) _).symm.trans ?_
  rw [h1, h2, map_smul]
  congr 1
  exact (push_incl_orientOn_of_subset hU (isCompact_setOf_val_eq U (φ u)) _
    (singleton_subset_iff.2 ⟨⟨φ u, hmem⟩, rfl, rfl⟩)).symm

end LocalTransfer

section Orbit

variable {p : ℕ} [NeZero p] {W : Set (EuclideanSpace ℝ (Fin (m + 1)))}
  {g : EuclideanSpace ℝ (Fin (m + 1)) → EuclideanSpace ℝ (Fin (m + 1))}

/-- The quotient map `π : W ⟶ W / ⟨g⟩`, as a morphism of `TopCat`. -/
noncomputable def orbitHom (hgW : MapsTo g W W) (hgc : ContinuousOn g W)
    (hper : ∀ w ∈ W, g^[p] w = w) : TopCat.of W ⟶ TopCat.of (OrbitQuot hgW hgc hper) :=
  TopCat.ofHom ⟨orbitMk hgW hgc hper, continuous_orbitMk⟩

/-- The orbit of `x`, as the fibre `π⁻¹ (π x) ⊆ W`. -/
def orbitSet (hgW : MapsTo g W W) (hgc : ContinuousOn g W) (hper : ∀ w ∈ W, g^[p] w = w)
    (x : W) : Set W :=
  orbitMk hgW hgc hper ⁻¹' {orbitMk hgW hgc hper x}

variable {hgW : MapsTo g W W} {hgc : ContinuousOn g W} {hper : ∀ w ∈ W, g^[p] w = w}

omit [CommRing R] in
lemma mem_orbitSet_iff {x w : W} :
    w ∈ orbitSet hgW hgc hper x ↔ ∃ k < p, (w : 𝔼) = g^[k] x :=
  orbitMk_eq_orbitMk_iff

omit [CommRing R] in
lemma orbitSet_finite (x : W) : (orbitSet hgW hgc hper x).Finite := by
  have : orbitSet hgW hgc hper x = Subtype.val ⁻¹' ((fun k => g^[k] (x : 𝔼)) '' Iio p) :=
    orbitMk_preimage_singleton x
  rw [this]
  exact ((finite_Iio p).image _).preimage Subtype.val_injective.injOn

omit [CommRing R] in
lemma isCompact_orbitSet (x : W) : IsCompact (orbitSet hgW hgc hper x) :=
  (orbitSet_finite x).isCompact

omit [CommRing R] [NeZero p] in
lemma image_iterate_ball_subset (hgW : MapsTo g W W) {x : 𝔼} {δ : ℝ}
    (hcb : closedBall x δ ⊆ W) (k : ℕ) : g^[k] '' ball x δ ⊆ W :=
  image_iterate_subset hgW (ball_subset_closedBall.trans hcb) k

omit [CommRing R] in
lemma isOpen_image_iterate_ball (hW : IsOpen W) (hgW : MapsTo g W W) (hgc : ContinuousOn g W)
    (hper : ∀ w ∈ W, g^[p] w = w) {x : 𝔼} {δ : ℝ} (hcb : closedBall x δ ⊆ W) (k : ℕ) :
    IsOpen (g^[k] '' ball x δ) :=
  isOpen_image_iterate hgW hgc hper hW isOpen_ball (ball_subset_closedBall.trans hcb) k

omit [CommRing R] in
/-- In a slice, a point of `g^[k] B(x, δ)` lying on the orbit of `x` is `g^[k] x`. -/
lemma eq_of_mem_slice_of_mem_orbit {x : W} {δ : ℝ} (hδ : 0 < δ)
    (hdisj : ∀ k < p, ∀ j < p, k ≠ j →
      Disjoint (g^[k] '' ball (x : 𝔼) δ) (g^[j] '' ball (x : 𝔼) δ))
    {k : ℕ} (hk : k < p) {z : 𝔼} (hz : z ∈ g^[k] '' ball (x : 𝔼) δ) {w : W}
    (hw : w ∈ orbitSet hgW hgc hper x) (hzw : z = w) : z = g^[k] x := by
  obtain ⟨j, hj, hwj⟩ := mem_orbitSet_iff.1 hw
  have : z ∈ g^[k] '' ball (x : 𝔼) δ ∩ (fun j => g^[j] (x : 𝔼)) '' Iio p :=
    ⟨hz, j, hj, (hzw.trans hwj).symm⟩
  rw [image_iterate_ball_inter_orbit hδ hdisj hk] at this
  exact this

/-- **(T4) Orbit decomposition.** For a slice `B(x, δ)` with translates `U_k = g^[k] B(x, δ)`,
`o^W_O = Σ_k e_k (o^{U_k}_{g^k x})` in `H_{m+1}(W | O)`, `O` the orbit of `x`. -/
theorem orientOn_orbit_eq_sum (hW : IsOpen W) (x : W) {δ : ℝ} (hδ : 0 < δ)
    (hcb : closedBall (x : 𝔼) δ ⊆ W)
    (hdisj : ∀ k < p, ∀ j < p, k ≠ j →
      Disjoint (g^[k] '' ball (x : 𝔼) δ) (g^[j] '' ball (x : 𝔼) δ)) :
    orientOn R hW (isCompact_orbitSet (hgW := hgW) (hgc := hgc) (hper := hper) x) =
      ∑ k : Fin p, push R (openIncl (image_iterate_ball_subset hgW hcb k))
        (L := {u : g^[k] '' ball (x : 𝔼) δ | (u : 𝔼) = g^[k] x})
        (L' := orbitSet hgW hgc hper x)
        (fun u hu => eq_of_mem_slice_of_mem_orbit hδ hdisj k.2 u.2 hu rfl) (m + 1)
        (orientOn R (isOpen_image_iterate_ball hW hgW hgc hper hcb k)
          (isCompact_setOf_val_eq _ _)) := by
  classical
  have hPI := pointInj_of_isOpen_of_finite (R := R) hW
    (orbitSet_finite (hgW := hgW) (hgc := hgc) (hper := hper) x)
  rw [← sub_eq_zero]
  refine hPI _ fun w hw => ?_
  obtain ⟨k₀, hk₀, hwk₀⟩ := mem_orbitSet_iff.1 hw
  have hxb : (x : 𝔼) ∈ ball (x : 𝔼) δ := mem_ball_self hδ
  have hw1 : res R (singleton_subset_iff.2 hw) (m + 1)
      (orientOn R hW (isCompact_orbitSet (hgW := hgW) (hgc := hgc) (hper := hper) x)) =
      orientOn R hW (isCompact_singleton (x := w)) :=
    res_orientOn hW _ _ _
  have hterm : ∀ k : Fin p, res R (singleton_subset_iff.2 hw) (m + 1)
      (push R (openIncl (image_iterate_ball_subset hgW hcb k))
        (L := {u : g^[k] '' ball (x : 𝔼) δ | (u : 𝔼) = g^[k] x})
        (L' := orbitSet hgW hgc hper x)
        (fun u hu => eq_of_mem_slice_of_mem_orbit hδ hdisj k.2 u.2 hu rfl) (m + 1)
        (orientOn R (isOpen_image_iterate_ball hW hgW hgc hper hcb k)
          (isCompact_setOf_val_eq _ _))) =
      if k = ⟨k₀, hk₀⟩ then orientOn R hW (isCompact_singleton (x := w)) else 0 := by
    intro k
    have hc : ∀ u : TopCat.of (g^[k] '' ball (x : 𝔼) δ),
        openIncl (image_iterate_ball_subset hgW hcb k) u ∈ ({w} : Set W) →
          u ∈ {u : g^[k] '' ball (x : 𝔼) δ | (u : 𝔼) = g^[k] x} := fun u hu =>
      eq_of_mem_slice_of_mem_orbit hδ hdisj k.2 u.2 hw (congrArg Subtype.val hu)
    refine (push_push_apply (L' := orbitSet hgW hgc hper x) (L'' := ({w} : Set W))
      (openIncl (image_iterate_ball_subset hgW hcb k)) (𝟙 _)
      (openIncl (image_iterate_ball_subset hgW hcb k)) (Category.comp_id _)
      (fun u hu => eq_of_mem_slice_of_mem_orbit hδ hdisj k.2 u.2 hu rfl)
      (fun _ hu => singleton_subset_iff.2 hw hu) hc (m + 1) _).trans ?_
    split_ifs with hk
    · subst hk
      refine push_openIncl_orientOn (R := R) _ hW _ _ _ ?_ hc
      ext z
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨w, rfl, (hu.trans hwk₀.symm).symm⟩
      · rintro ⟨w', hw', rfl⟩
        rw [mem_singleton_iff.1 hw']
        exact ⟨⟨g^[k₀] x, ⟨x, hxb, rfl⟩⟩, rfl, hwk₀.symm⟩
    · have hz : push R (openIncl (image_iterate_ball_subset hgW hcb k)) hc (m + 1) = 0 := by
        refine push_eq_zero_of_forall_notMem hc (fun u hu => ?_) (m + 1)
        have h1 : (u : 𝔼) = g^[k] x :=
        eq_of_mem_slice_of_mem_orbit hδ hdisj k.2 u.2 hw (congrArg Subtype.val hu)
        have h2 : (u : 𝔼) = g^[k₀] x := (congrArg Subtype.val hu).trans hwk₀
        have hne : (k : ℕ) ≠ k₀ := fun h => hk (Fin.ext h)
        exact Set.disjoint_left.1 (hdisj k k.2 k₀ hk₀ hne) ⟨x, hxb, rfl⟩
          ⟨x, hxb, (h1.symm.trans h2).symm⟩
      rw [hz]; rfl
  rw [map_sub, map_sum, hw1]
  simp_rw [hterm]
  simp

omit [NeZero p] in
/-- `ldeg(g^[p]) = 1` when `g^[p] = id` on `W`. -/
lemma ldeg_iterate_period_eq_one [NeZero p] (hW : IsOpen W) {w : 𝔼} (hw : w ∈ W) :
    ldeg R hW (g^[p]) (hgc.iterate hgW p) (injOn_iterate hgW hper p) w hw = 1 := by
  have hK : IsCompact {v : W | (v : 𝔼) = w} := isCompact_setOf_val_eq W w
  refine degree_eq_one_of_straightLine (R := R) (hW := hW) (A := g^[p])
    (hA := hgc.iterate hgW p) (y := g^[p] w) _ hK ⟨⟨w, hw⟩, rfl, (hper w hw).symm⟩ ?_
  intro t _ z hz
  rw [hper z z.2, hper w hw, ← add_smul, sub_add_cancel, one_smul] at hz
  exact hz

/-- The restriction `π|U : U ⟶ W / ⟨g⟩` of the quotient map to an open `U ⊆ W`. -/
noncomputable abbrev orbitHomOn {U : Set 𝔼} (hUW : U ⊆ W) :
    TopCat.of U ⟶ TopCat.of (OrbitQuot hgW hgc hper) :=
  openIncl hUW ≫ orbitHom hgW hgc hper

omit [CommRing R] [NeZero p] in
lemma mapsTo_iterate_sub_slice (hper : ∀ w ∈ W, g^[p] w = w) {x : 𝔼} {δ : ℝ} (hcb : closedBall x δ ⊆ W) {k : ℕ} (hk : k ≤ p) :
    MapsTo g^[p - k] (g^[k] '' ball x δ) (ball x δ) := by
  rintro _ ⟨b, hb, rfl⟩
  rw [iterate_sub_iterate hper hk (ball_subset_closedBall.trans hcb hb)]
  exact hb

omit [CommRing R] in
lemma orbitHomOn_cond {x : W} {δ : ℝ} (hδ : 0 < δ) (hcb : closedBall (x : 𝔼) δ ⊆ W)
    (hdisj : ∀ k < p, ∀ j < p, k ≠ j →
      Disjoint (g^[k] '' ball (x : 𝔼) δ) (g^[j] '' ball (x : 𝔼) δ)) :
    ∀ u, orbitHomOn (hgW := hgW) (hgc := hgc) (hper := hper) (ball_subset_closedBall.trans hcb) u ∈
      ({orbitMk hgW hgc hper x} : Set (OrbitQuot hgW hgc hper)) →
      u ∈ {u : ball (x : 𝔼) δ | (u : 𝔼) = x} := fun u hu =>
  eq_of_mem_slice_of_mem_orbit (hgW := hgW) (hgc := hgc) (hper := hper) hδ hdisj
    (Nat.pos_of_neZero p) ⟨u, u.2, rfl⟩ (w := ⟨u, ball_subset_closedBall.trans hcb u.2⟩) hu rfl

/-- **(T5) The orbit class dies in the quotient.** With `ldeg(g^[j]) = 1` for `0 < j < p` and
`p = 0` in `R`, the image of `o^W_O`, `O` the orbit of `x`, in `H_{m+1}(W/⟨g⟩ | π x)` is `0`. -/
theorem push_orbitHom_orientOn_orbitSet [Fact p.Prime] (hW : IsOpen W)
    (hfree : ∀ w ∈ W, g w ≠ w)
    (hldeg : ∀ j, 0 < j → j < p → ∀ w (hw : w ∈ W),
      ldeg R hW (g^[j]) (hgc.iterate hgW j) (injOn_iterate hgW hper j) w hw = 1)
    (hpR : (p : R) = 0) (x : W) :
    push R (orbitHom hgW hgc hper) (L := orbitSet hgW hgc hper x)
      (L' := {orbitMk hgW hgc hper x}) (fun _ h => h) (m + 1)
      (orientOn R hW (isCompact_orbitSet x)) = 0 := by
  obtain ⟨δ, hδ, hcb, hdisj⟩ := exists_slice hW hgW hgc hper hfree x.2
  have hUW : ball (x : 𝔼) δ ⊆ W := ball_subset_closedBall.trans hcb
  set c := push R (orbitHomOn (hgW := hgW) (hgc := hgc) (hper := hper) hUW)
    (L := {u : ball (x : 𝔼) δ | (u : 𝔼) = x}) (L' := {orbitMk hgW hgc hper x})
    (orbitHomOn_cond hδ hcb hdisj) (m + 1)
    (orientOn R isOpen_ball (isCompact_setOf_val_eq _ (x : 𝔼))) with hc_def
  have hterm : ∀ k : Fin p,
      push R (orbitHom hgW hgc hper) (L := orbitSet hgW hgc hper x)
        (L' := {orbitMk hgW hgc hper x}) (fun _ h => h) (m + 1)
        (push R (openIncl (image_iterate_ball_subset hgW hcb k))
          (L := {u : g^[k] '' ball (x : 𝔼) δ | (u : 𝔼) = g^[k] x})
          (L' := orbitSet hgW hgc hper x)
          (fun u hu => eq_of_mem_slice_of_mem_orbit hδ hdisj k.2 u.2 hu rfl) (m + 1)
          (orientOn R (isOpen_image_iterate_ball hW hgW hgc hper hcb k)
            (isCompact_setOf_val_eq _ _))) = c := by
    intro k
    have hkp : (k : ℕ) ≤ p := k.2.le
    have hVU := mapsTo_iterate_sub_slice hper hcb hkp
    have hVW := image_iterate_ball_subset hgW hcb k
    have hfac : openIncl hVW ≫ orbitHom hgW hgc hper =
        restrictMapsTo (g^[p - k]) ((hgc.iterate hgW (p - k)).mono hVW) hVU ≫
          orbitHomOn (hgW := hgW) (hgc := hgc) (hper := hper) hUW := by
      ext u
      exact (orbitMk_iterate (hgW := hgW) (hgc := hgc) (hper := hper) (p - k) ⟨u, hVW u.2⟩
        (hUW (hVU u.2))).symm
    have hu : g^[k] (x : 𝔼) ∈ g^[k] '' ball (x : 𝔼) δ := ⟨x, mem_ball_self hδ, rfl⟩
    have ht : g^[p - k] (g^[k] (x : 𝔼)) = x := iterate_sub_iterate hper hkp x.2
    have h5 := push_restrictMapsTo_orientOn (R := R) hW
      (isOpen_image_iterate_ball hW hgW hgc hper hcb k) isOpen_ball hVW
      (hgc.iterate hgW (p - k)) (injOn_iterate hgW hper (p - k)) hVU hu ht
    have hld : ldeg R hW (g^[p - k]) (hgc.iterate hgW (p - k)) (injOn_iterate hgW hper (p - k))
        (g^[k] x) (hVW hu) = 1 := by
      rcases Nat.eq_zero_or_pos (k : ℕ) with h0 | hpos
      · simp only [h0, Nat.sub_zero]
        exact ldeg_iterate_period_eq_one (hgW := hgW) (hgc := hgc) (hper := hper) hW _
      · exact hldeg _ (by omega) (by omega) _ _
    rw [hld, one_smul] at h5
    have hKcond : ∀ u : TopCat.of (g^[k] '' ball (x : 𝔼) δ),
        (restrictMapsTo (g^[p - k]) ((hgc.iterate hgW (p - k)).mono hVW) hVU ≫
          orbitHomOn (hgW := hgW) (hgc := hgc) (hper := hper) hUW) u ∈
            ({orbitMk hgW hgc hper x} : Set (OrbitQuot hgW hgc hper)) →
        u ∈ {u : g^[k] '' ball (x : 𝔼) δ | (u : 𝔼) = g^[k] x} := by
      intro u hu
      have e := ConcreteCategory.congr_hom hfac u
      have hu' : (openIncl hVW ≫ orbitHom hgW hgc hper) u ∈
          ({orbitMk hgW hgc hper x} : Set (OrbitQuot hgW hgc hper)) := by
        rw [e]; exact hu
      exact eq_of_mem_slice_of_mem_orbit hδ hdisj k.2 u.2 hu' rfl
    refine (push_push_apply (L' := orbitSet hgW hgc hper x)
      (L'' := {orbitMk hgW hgc hper x}) (openIncl hVW) (orbitHom hgW hgc hper)
      (restrictMapsTo (g^[p - k]) ((hgc.iterate hgW (p - k)).mono hVW) hVU ≫
          orbitHomOn (hgW := hgW) (hgc := hgc) (hper := hper) hUW) hfac
      (fun u hu => eq_of_mem_slice_of_mem_orbit hδ hdisj k.2 u.2 hu rfl) (fun _ h => h)
      hKcond (m + 1) _).trans ?_
    refine (push_push_apply (L' := {w : ball (x : 𝔼) δ | (w : 𝔼) = x})
      (L'' := {orbitMk hgW hgc hper x})
      (restrictMapsTo (g^[p - k]) ((hgc.iterate hgW (p - k)).mono hVW) hVU)
      (orbitHomOn (hgW := hgW) (hgc := hgc) (hper := hper) hUW)
      (restrictMapsTo (g^[p - k]) ((hgc.iterate hgW (p - k)).mono hVW) hVU ≫
          orbitHomOn (hgW := hgW) (hgc := hgc) (hper := hper) hUW) rfl
      (restrictMapsTo_cond hVW _ (injOn_iterate hgW hper (p - k)) hVU hu ht)
      (orbitHomOn_cond hδ hcb hdisj) hKcond (m + 1) _).symm.trans ?_
    rw [h5]
  rw [orientOn_orbit_eq_sum hW x hδ hcb hdisj, map_sum]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul R, hpR,
    zero_smul]

end Orbit

section Main

/-- **Transfer vanishing** (blueprint §2.4), for any coefficient ring in which `p = 0`. -/
theorem degree_eq_zero_of_free_of_natCast_eq_zero {p : ℕ} [Fact p.Prime]
    {W : Set (EuclideanSpace ℝ (Fin (m + 1)))} (hW : IsOpen W)
    {g : EuclideanSpace ℝ (Fin (m + 1)) → EuclideanSpace ℝ (Fin (m + 1))}
    (hgW : MapsTo g W W) (hgc : ContinuousOn g W) (hper : ∀ w ∈ W, g^[p] w = w)
    (hfree : ∀ w ∈ W, g w ≠ w)
    (hldeg : ∀ j, 0 < j → j < p → ∀ w (hw : w ∈ W),
      ldeg R hW (g^[j]) (hgc.iterate hgW j) (injOn_iterate hgW hper j) w hw = 1)
    (hpR : (p : R) = 0)
    {A : EuclideanSpace ℝ (Fin (m + 1)) → EuclideanSpace ℝ (Fin (m + 1))}
    (hA : ContinuousOn A W) (hAg : ∀ w ∈ W, A (g w) = A w) {y : EuclideanSpace ℝ (Fin (m + 1))}
    (hK : IsCompact {w : W | A w = y}) : degree R hW A hA y hK = 0 := by
  classical
  -- (T1) a nice cover of the fibre by half slices
  have hsl : ∀ w : W, ∃ δ > 0, closedBall (w : 𝔼) δ ⊆ W ∧ ∀ k < p, ∀ j < p, k ≠ j →
      Disjoint (g^[k] '' ball (w : 𝔼) δ) (g^[j] '' ball (w : 𝔼) δ) :=
    fun w => exists_slice hW hgW hgc hper hfree w.2
  choose δ hδ hcb hdisj using hsl
  obtain ⟨t, -, htK⟩ := hK.elim_nhds_subcover
    (fun w : W => (Subtype.val ⁻¹' ball (w : 𝔼) (δ w / 2) : Set W))
    (fun w _ => (isOpen_ball.preimage continuous_subtype_val).mem_nhds
      (mem_ball_self (half_pos (hδ w))))
  set S : Set 𝔼 := ⋃ w ∈ t, closedBall (w : 𝔼) (δ w / 2) with hS_def
  have hSW : S ⊆ W := iUnion₂_subset fun w _ =>
    (closedBall_subset_closedBall (half_le_self (hδ w).le)).trans (hcb w)
  have hSc : IsCompact S := t.isCompact_biUnion fun w _ => isCompact_closedBall _ _
  set π := orbitMk hgW hgc hper
  set M : Set (OrbitQuot hgW hgc hper) := π '' (Subtype.val ⁻¹' S) with hM_def
  set K' : Set W := π ⁻¹' M with hK'_def
  have hK'c : IsCompact K' := by
    have e : K' = Subtype.val ⁻¹' (⋃ k ∈ Iio p, g^[k] '' S) := orbitMk_preimage_image hSW
    have hT : IsCompact (⋃ k ∈ Iio p, g^[k] '' S) :=
      (finite_Iio p).isCompact_biUnion fun k _ =>
        hSc.image_of_continuousOn ((hgc.iterate hgW k).mono hSW)
    have hTW : (⋃ k ∈ Iio p, g^[k] '' S) ⊆ W :=
      iUnion₂_subset fun k _ => image_iterate_subset hgW hSW k
    rw [e, Topology.IsInducing.subtypeVal.isCompact_iff, Subtype.image_preimage_coe,
      Set.inter_eq_right.2 hTW]
    exact hT
  have hfib : ∀ w : W, A w = y → w ∈ K' := by
    intro w hw
    have hw' := htK hw
    simp only [mem_iUnion, mem_preimage, exists_prop] at hw'
    obtain ⟨j, hj, hwj⟩ := hw'
    refine ⟨w, ?_, rfl⟩
    show (w : 𝔼) ∈ S
    exact mem_iUnion₂.2 ⟨j, hj, ball_subset_closedBall hwj⟩
  -- (T2) factorisation `A = Ā ∘ π`
  let Abar : TopCat.of (OrbitQuot hgW hgc hper) ⟶ TopCat.of 𝔼 :=
    TopCat.ofHom (descend hgW hgc hper A hA hAg)
  have hfac : orbitHom hgW hgc hper ≫ Abar = restrictHom A hA := rfl
  have hAbar : ∀ q, Abar q ∈ ({y} : Set 𝔼) → q ∈ M := by
    intro q hq
    obtain ⟨w, rfl⟩ := surjective_orbitMk (hgW := hgW) (hgc := hgc) (hper := hper) q
    exact hfib w hq
  have hdeg := push_orientOn_eq_degree_smul (R := R) (hW := hW) (hA := hA) hK hK'c hfib
  have hdeg2 := (push_push_apply (R := R) (L := K') (L' := M) (L'' := {y})
    (orbitHom hgW hgc hper) Abar (restrictHom A hA) hfac (fun _ h => h) hAbar
    (fun w hw => hfib w hw) (m + 1) (orientOn R hW hK'c)).trans hdeg
  -- (T3–T5) the class `π_* o_{K'}` vanishes
  have hzero : push R (orbitHom hgW hgc hper) (L := K') (L' := M) (fun _ h => h) (m + 1)
      (orientOn R hW hK'c) = 0 := by
    -- `P(π K')` from the chart-convex pieces `π (B̄(x_j, δ_j / 2))`
    let P : W → ConvexPiece (TopCat.of (OrbitQuot hgW hgc hper)) m := fun j =>
      { e := sliceChart hgW hgc hper (hδ j) (hcb j) (hdisj j)
        C := closedBall (j : 𝔼) (δ j / 2)
        convex := convex_closedBall _ _
        compact := isCompact_closedBall _ _
        subset := closedBall_subset_ball (half_lt_self (hδ j)) }
    have hT2 : T2Space (TopCat.of (OrbitQuot hgW hgc hper)) :=
      inferInstanceAs (T2Space (OrbitQuot hgW hgc hper))
    have hPI := (vanishAbove_pointInj_biUnion_pieces (R := R) t P).2
    have hMU : (⋃ j ∈ t, (P j).carrier) = M := by
      rw [hM_def, hS_def, preimage_iUnion₂, image_iUnion₂]
      refine iUnion₂_congr fun j _ => ?_
      exact sliceChart_symm_image (hδ := hδ j) (hcb := hcb j) (hdisj := hdisj j)
        (closedBall_subset_ball (half_lt_self (hδ j)))
    rw [hMU] at hPI
    -- (T3) pointwise reduction to orbits
    refine hPI _ fun z hz => ?_
    obtain ⟨x, rfl⟩ := surjective_orbitMk (hgW := hgW) (hgc := hgc) (hper := hper) z
    have hOK : orbitSet hgW hgc hper x ⊆ K' := fun w hw => by
      show π w ∈ M
      rw [show π w = π x from hw]
      exact hz
    refine (push_res_apply (orbitHom hgW hgc hper) (L₂' := {π x}) hOK
      (singleton_subset_iff.2 hz) (fun _ h => h) (fun _ h => h) (m + 1) _).trans ?_
    rw [res_orientOn hW hK'c (isCompact_orbitSet x) hOK]
    exact push_orbitHom_orientOn_orbitSet hW hfree hldeg hpR x
  rw [hzero, map_zero] at hdeg2
  exact (smul_orient_eq_zero_iff (convex_singleton y) Bornology.isBounded_singleton
    (singleton_nonempty y) _).1 hdeg2.symm

end Main

end HSFormal.Newman

namespace HSFormal.Newman

/-- **Transfer vanishing** (blueprint §2.4, the hardest lemma): the degree, in `ZMod p`, of a
`⟨g⟩`-invariant map over a value whose fibre is acted on freely by `g` (of prime period `p`) is
`0`, provided every iterate `g^[j]`, `0 < j < p`, has local degree `1` everywhere on `W`. -/
theorem degree_eq_zero_of_free (p : ℕ) [Fact p.Prime] {m : ℕ}
    {W : Set (EuclideanSpace ℝ (Fin (m + 1)))} (hW : IsOpen W)
    {g : EuclideanSpace ℝ (Fin (m + 1)) → EuclideanSpace ℝ (Fin (m + 1))}
    (hgW : Set.MapsTo g W W) (hgc : ContinuousOn g W) (hper : ∀ w ∈ W, g^[p] w = w)
    (hfree : ∀ w ∈ W, g w ≠ w)
    (hldeg : ∀ j, 0 < j → j < p → ∀ w (hw : w ∈ W),
      ldeg (ZMod p) hW (g^[j]) (hgc.iterate hgW j) (injOn_iterate hgW hper j) w hw = 1)
    {A : EuclideanSpace ℝ (Fin (m + 1)) → EuclideanSpace ℝ (Fin (m + 1))}
    (hA : ContinuousOn A W) (hAg : ∀ w ∈ W, A (g w) = A w)
    {y : EuclideanSpace ℝ (Fin (m + 1))} (hK : IsCompact {w : W | A w = y}) :
    degree (ZMod p) hW A hA y hK = 0 :=
  degree_eq_zero_of_free_of_natCast_eq_zero hW hgW hgc hper hfree hldeg (ZMod.natCast_self p)
    hA hAg hK

/-- The frozen statement `DegreeEqZeroOfFree` holds. -/
theorem degreeEqZeroOfFree : DegreeEqZeroOfFree := by
  intro p _ m W hW g hgW hgc hper hfree hldeg A hA hAg y hK
  exact degree_eq_zero_of_free p hW hgW hgc hper hfree hldeg hA hAg hK

end HSFormal.Newman
