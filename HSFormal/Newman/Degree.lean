import HSFormal.Newman.CompactSupport
import Mathlib.Topology.LocallyConstant.Basic

/-!
# N5. Local degree (Newman blueprint, module N5)

Throughout, `𝔼 = EuclideanSpace ℝ (Fin (m + 1))`, `W ⊆ 𝔼` is open and coefficients are a
commutative ring `R` (`R = ZMod p` in the application).

* `orientOn R hW hK ∈ H_{m+1}(W | K)` for compact `K ⊆ W`: the preimage of `o_K` under the
  excision isomorphism (`isIso_push_incl_image`); `push_incl_orientOn(_of_subset)`,
  `res_orientOn`, and naturality in `W` (`push_openIncl_orientOn`); `vanishAbove_of_isOpen`
  (`V` for compacta of `W`) and `pointInj_of_isOpen_of_finite` (`P` for finite subsets of `W`,
  e.g. orbits in step T4).
* `degree R hW A hA y hK ∈ R` (`hK : IsCompact {w : W | A w = y}`), characterised by
  `degree_spec : A_*(o^W_K) = deg • o_y`; it can be computed on any compact `K ⊇ A⁻¹ y`
  (`push_orientOn_eq_degree_smul`, `degree_eq_of_push`).
* **(D-loc)** `degree_congr_open` (with `isCompact_fibre_of_subset` for the compactness side
  condition), **(D-id)** `degree_id`, `degree_eq_one_of_straightLine` (degree one through the
  straight-line homotopy, via `push_eq_of_homotopy`), **(DEG1)** `degree_eq_one_of_segment`,
  **(SEG)** `degree_eq_of_segment`.
* `ldeg R hW h hc hinj w hw = deg(h, W, h w)` for `h` continuous and injective on `W`;
  **(LD1)** `ldeg_eq_one_of_dist_le`, local constancy `ldeg_eventually_eq` and **(LOC)**
  `ldeg_eq_of_isPreconnected`.

## Deviations from the blueprint

* `ldeg_eq_of_isPreconnected` does not need `S` open; `ldeg_eq_one_of_dist_le` takes the
  membership `hw : w ∈ W` explicitly.
* `degree_congr_open` takes the compactness of the smaller fibre as an argument (any proof; see
  `isCompact_fibre_of_subset`), so that both sides are stated with the blueprint's `degree`.
* Engineering note: never write the local notation `𝔼` inside a `variable` command (the binder
  silently elaborates to error-typed terms, causing timeouts); spell out
  `EuclideanSpace ℝ (Fin (m + 1))` there. Avoid defeq checks that unfold `closedBall` membership
  on `𝔼` (use `Set.mem_preimage.2` and `mem_closedBall.2` explicitly).
-/

open CategoryTheory Limits Topology Metric

namespace HSFormal.Newman

variable {R : Type} [CommRing R] {m : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin (m + 1))

section OrientOn

variable {W : Set (EuclideanSpace ℝ (Fin (m + 1)))}

lemma incl_mem_image_iff {K : Set W} (x : TopCat.of W) :
    incl (X := TopCat.of 𝔼) W x ∈ Subtype.val '' K ↔ x ∈ K :=
  ⟨fun ⟨k, hk, hkx⟩ => (Subtype.ext hkx : k = x) ▸ hk, fun hx => ⟨x, hx, rfl⟩⟩

/-- For `K ⊆ W` compact, `W` open, the inclusion induces `H_i(W | K) ≅ H_i(𝔼 | K)` (excision). -/
lemma isIso_push_incl_image (hW : IsOpen W) {K : Set W} (hK : IsCompact K) (i : ℕ) :
    IsIso (push R (incl (X := TopCat.of 𝔼) W) (L := K) (L' := Subtype.val '' K)
      (fun x => (incl_mem_image_iff x).1) i) :=
  isIso_push_of_isOpenEmbedding (isOpenEmbedding_incl hW) _ (fun x => (incl_mem_image_iff x).2)
    (hK.image continuous_subtype_val).isClosed (by rintro _ ⟨k, -, rfl⟩; exact ⟨k, rfl⟩) i

variable (R) in
/-- `o^W_K ∈ H_{m+1}(W | K)`, the class corresponding to `o_K` under excision. -/
noncomputable def orientOn (hW : IsOpen W) {K : Set W} (hK : IsCompact K) :
    relH R (TopCat.of W) K (m + 1) :=
  have := isIso_push_incl_image (R := R) hW hK (m + 1)
  inv (push R (incl (X := TopCat.of 𝔼) W) (L := K) (L' := Subtype.val '' K)
      (fun x => (incl_mem_image_iff x).1) (m + 1)) (orient R m (Subtype.val '' K))

lemma push_incl_orientOn (hW : IsOpen W) {K : Set W} (hK : IsCompact K) :
    push R (incl (X := TopCat.of 𝔼) W) (L := K) (L' := Subtype.val '' K)
      (fun x => (incl_mem_image_iff x).1) (m + 1) (orientOn R hW hK) =
      orient R m (Subtype.val '' K) := by
  have := isIso_push_incl_image (R := R) hW hK (m + 1)
  rw [orientOn, ← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply]

/-- The image of `o^W_K` in `H_{m+1}(𝔼 | L')`, for `L' ⊆ K`, is `o_{L'}`. -/
lemma push_incl_orientOn_of_subset (hW : IsOpen W) {K : Set W} (hK : IsCompact K)
    {L' : Set 𝔼} (h : ∀ x : TopCat.of W, incl (X := TopCat.of 𝔼) W x ∈ L' → x ∈ K)
    (hL' : L' ⊆ Subtype.val '' K) :
    push R (incl (X := TopCat.of 𝔼) W) h (m + 1) (orientOn R hW hK) = orient R m L' := by
  calc push R (incl (X := TopCat.of 𝔼) W) h (m + 1) (orientOn R hW hK)
      = res R hL' (m + 1) (push R (incl (X := TopCat.of 𝔼) W) (L := K)
          (L' := Subtype.val '' K) (fun x => (incl_mem_image_iff x).1) (m + 1)
          (orientOn R hW hK)) :=
        (push_push_apply (L' := Subtype.val '' K) (L'' := L') (incl (X := TopCat.of 𝔼) W)
          (𝟙 (TopCat.of 𝔼)) (incl (X := TopCat.of 𝔼) W) (Category.comp_id _)
          (fun x => (incl_mem_image_iff x).1) (fun _ hy => hL' hy) h (m + 1)
          (orientOn R hW hK)).symm
    _ = res R hL' (m + 1) (orient R m (Subtype.val '' K)) := by rw [push_incl_orientOn]
    _ = orient R m L' := res_orient (hK.image continuous_subtype_val).isBounded hL'

/-- Injectivity of the excision map, in the form used to identify classes on `W`. -/
lemma push_incl_image_injective (hW : IsOpen W) {K : Set W} (hK : IsCompact K) (i : ℕ) :
    Function.Injective (push R (incl (X := TopCat.of 𝔼) W) (L := K) (L' := Subtype.val '' K)
      (fun x => (incl_mem_image_iff x).1) i) :=
  have := isIso_push_incl_image (R := R) hW hK i
  injective_of_isIso _

/-- `res o^W_K = o^W_{K'}` for `K' ⊆ K`. -/
lemma res_orientOn (hW : IsOpen W) {K K' : Set W} (hK : IsCompact K) (hK' : IsCompact K')
    (h : K' ⊆ K) : res R h (m + 1) (orientOn R hW hK) = orientOn R hW hK' := by
  apply push_incl_image_injective (R := R) hW hK' (m + 1)
  rw [push_incl_orientOn hW hK']
  refine (push_push_apply (L' := K') (L'' := Subtype.val '' K') (𝟙 (TopCat.of W))
    (incl (X := TopCat.of 𝔼) W) (incl (X := TopCat.of 𝔼) W) (Category.id_comp _)
    (fun _ hx => h hx) (fun x => (incl_mem_image_iff x).1)
    (fun x hx => h ((incl_mem_image_iff x).1 hx)) (m + 1) (orientOn R hW hK)).trans ?_
  exact push_incl_orientOn_of_subset hW hK _ (Set.image_mono h)

/-- `V` in degree `m + 1` for compacta in an open `W ⊆ 𝔼`. -/
theorem vanishAbove_of_isOpen (hW : IsOpen W) {K : Set W} (hK : IsCompact K) :
    VanishAbove R (TopCat.of W) K (m + 1) :=
  (vanishAbove_iff_of_isOpenEmbedding (f := incl (X := TopCat.of 𝔼) W) (L := K)
    (L' := Subtype.val '' K) (isOpenEmbedding_incl hW) incl_mem_image_iff
    (hK.image continuous_subtype_val).isClosed
    (by rintro _ ⟨k, -, rfl⟩; exact ⟨k, rfl⟩)).2
    (vanishAbove_of_isCompact (hK.image continuous_subtype_val))

/-- `P` in degree `m + 1` for finite subsets of an open `W ⊆ 𝔼` (used for orbits, T4). -/
theorem pointInj_of_isOpen_of_finite (hW : IsOpen W) {K : Set W} (hK : K.Finite) :
    PointInj R (TopCat.of W) K (m + 1) := by
  classical
  have hKi : (Subtype.val '' K).Finite := hK.image _
  have hP := (vanishAbove_pointInj_biUnion (R := R) (hKi.toFinset.image fun x => {x})
    (by
      intro s hs
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hs
      exact ⟨convex_singleton x, isCompact_singleton⟩)).2
  have hU : (⋃ s ∈ hKi.toFinset.image (fun x : 𝔼 => ({x} : Set 𝔼)), s) = Subtype.val '' K := by
    rw [Finset.set_biUnion_finset_image]
    ext z
    simp
  rw [hU] at hP
  exact (pointInj_iff_of_isOpenEmbedding (f := incl (X := TopCat.of 𝔼) W) (L := K)
    (L' := Subtype.val '' K) (isOpenEmbedding_incl hW) incl_mem_image_iff
    (hK.isCompact.image continuous_subtype_val).isClosed
    (by rintro _ ⟨k, -, rfl⟩; exact ⟨k, rfl⟩)).2 hP

end OrientOn

section Degree

variable {W : Set (EuclideanSpace ℝ (Fin (m + 1)))}

/-- `A|W` as a morphism `W ⟶ 𝔼` of `TopCat`. -/
noncomputable def restrictHom (A : 𝔼 → 𝔼) (hA : ContinuousOn A W) :
    TopCat.of W ⟶ TopCat.of 𝔼 :=
  TopCat.ofHom ⟨W.domRestrict A, hA.domRestrict⟩

@[simp]
lemma restrictHom_apply {A : 𝔼 → 𝔼} {hA : ContinuousOn A W} (x : TopCat.of W) :
    restrictHom A hA x = A x.1 := rfl

variable (R) in
/-- **The local degree** `deg(A, W, y) ∈ R`, defined by `A_*(o^W_K) = deg • o_y` in
`H_{m+1}(𝔼 | y)`, where `K = A⁻¹(y) ∩ W` is assumed compact. -/
noncomputable def degree (hW : IsOpen W) (A : 𝔼 → 𝔼) (hA : ContinuousOn A W) (y : 𝔼)
    (hK : IsCompact {w : W | A w = y}) : R :=
  (exists_eq_smul_orient_convex (R := R) (convex_singleton y) Bornology.isBounded_singleton
    (Set.singleton_nonempty y) (push R (restrictHom A hA) (L := {w : W | A w = y}) (L' := {y})
      (fun _ hw => Set.mem_singleton_iff.1 hw) (m + 1) (orientOn R hW hK))).choose

variable {hW : IsOpen W} {A : EuclideanSpace ℝ (Fin (m + 1)) → EuclideanSpace ℝ (Fin (m + 1))}
  {hA : ContinuousOn A W} {y : EuclideanSpace ℝ (Fin (m + 1))}

theorem degree_spec (hK : IsCompact {w : W | A w = y}) :
    push R (restrictHom A hA) (L := {w : W | A w = y}) (L' := {y})
      (fun _ hw => Set.mem_singleton_iff.1 hw) (m + 1) (orientOn R hW hK) =
      degree R hW A hA y hK • orient R m {y} :=
  (exists_eq_smul_orient_convex (R := R) (convex_singleton y) Bornology.isBounded_singleton
    (Set.singleton_nonempty y) (push R (restrictHom A hA) (L := {w : W | A w = y}) (L' := {y})
      (fun _ hw => Set.mem_singleton_iff.1 hw) (m + 1) (orientOn R hW hK))).choose_spec

lemma smul_orient_singleton_injective {c c' : R} (y : 𝔼)
    (h : c • orient R m {y} = c' • orient R m {y}) : c = c' := by
  rw [← sub_eq_zero, ← smul_orient_eq_zero_iff (convex_singleton y) Bornology.isBounded_singleton
    (Set.singleton_nonempty y), sub_smul, h, sub_self]

/-- The degree can be computed from any compact `K ⊇ A⁻¹(y) ∩ W`. -/
theorem push_orientOn_eq_degree_smul (hK : IsCompact {w : W | A w = y}) {K : Set W}
    (hK' : IsCompact K) (hsub : ∀ w : W, A w = y → w ∈ K) :
    push R (restrictHom A hA) (L := K) (L' := {y}) (fun w hw => hsub w hw) (m + 1)
      (orientOn R hW hK') = degree R hW A hA y hK • orient R m {y} := by
  rw [← degree_spec hK, ← res_orientOn hW hK' hK (fun w hw => hsub w hw)]
  exact (push_push_apply (L' := {w : W | A w = y}) (L'' := {y}) (𝟙 (TopCat.of W))
    (restrictHom A hA) (restrictHom A hA) (Category.id_comp _) (fun w hw => hsub w hw)
    (fun _ hw => Set.mem_singleton_iff.1 hw) (fun w hw => hsub w hw) (m + 1)
    (orientOn R hW hK')).symm

/-- Characterisation of the degree through any compact `K ⊇ A⁻¹(y) ∩ W`. -/
theorem degree_eq_of_push (hK : IsCompact {w : W | A w = y}) {K : Set W} (hK' : IsCompact K)
    (hsub : ∀ w : W, A w = y → w ∈ K) {c : R}
    (h : push R (restrictHom A hA) (L := K) (L' := {y}) (fun w hw => hsub w hw) (m + 1)
      (orientOn R hW hK') = c • orient R m {y}) : degree R hW A hA y hK = c :=
  smul_orient_singleton_injective y ((push_orientOn_eq_degree_smul hK hK' hsub).symm.trans h)

/-- The inclusion `W' ⟶ W` of open subsets of `𝔼`. -/
abbrev openIncl {W' W : Set (EuclideanSpace ℝ (Fin (m + 1)))} (h : W' ⊆ W) :
    TopCat.of W' ⟶ TopCat.of W :=
  TopCat.ofHom (ContinuousMap.inclusion h)

omit [CommRing R] in
lemma openIncl_comp_incl {W' : Set 𝔼} (h : W' ⊆ W) :
    openIncl h ≫ incl (X := TopCat.of 𝔼) W = incl (X := TopCat.of 𝔼) W' := rfl

omit [CommRing R] in
lemma openIncl_comp_restrictHom {W' : Set 𝔼} (h : W' ⊆ W) :
    openIncl h ≫ restrictHom A hA = restrictHom A (hA.mono h) := rfl

/-- Naturality of `o^W_K` in `W`: the inclusion `W' ⊆ W` carries `o^{W'}_{K'}` to `o^W_K` when
`K'` and `K` are the same subset of `𝔼`. -/
lemma push_openIncl_orientOn {W' : Set 𝔼} (hW' : IsOpen W') (hW : IsOpen W) (hWW : W' ⊆ W)
    {K' : Set W'} {K : Set W} (hK' : IsCompact K') (hK : IsCompact K)
    (himg : Subtype.val '' K' = Subtype.val '' K) (h : ∀ x, openIncl hWW x ∈ K → x ∈ K') :
    push R (openIncl hWW) h (m + 1) (orientOn R hW' hK') = orientOn R hW hK := by
  apply push_incl_image_injective (R := R) hW hK (m + 1)
  rw [push_incl_orientOn hW hK]
  refine (push_push_apply (L' := K) (L'' := Subtype.val '' K) (openIncl hWW)
    (incl (X := TopCat.of 𝔼) W) (incl (X := TopCat.of 𝔼) W') (openIncl_comp_incl hWW) h
    (fun x => (incl_mem_image_iff x).1) (fun x hx => h x ((incl_mem_image_iff _).1 hx)) (m + 1)
    (orientOn R hW' hK')).trans ?_
  exact push_incl_orientOn_of_subset hW' hK' _ himg.symm.le

/-- Fibres over `y` in an open `W' ⊆ W` containing the fibre in `W` are compact. -/
lemma isCompact_fibre_of_subset {W' : Set 𝔼} (hWW : W' ⊆ W)
    (hfib : ∀ w ∈ W, A w = y → w ∈ W') (hK : IsCompact {w : W | A w = y}) :
    IsCompact {w : W' | A w = y} := by
  have hemb : IsEmbedding (Set.inclusion hWW) := IsEmbedding.inclusion hWW
  rw [hemb.isCompact_iff]
  convert hK using 1
  ext w
  constructor
  · rintro ⟨w', hw', rfl⟩; exact hw'
  · intro hw; exact ⟨⟨w.1, hfib w.1 w.2 hw⟩, hw, rfl⟩

/-- **(D-loc)** The degree only depends on a neighbourhood of the fibre. -/
theorem degree_congr_open {W' : Set 𝔼} (hW' : IsOpen W') (hWW : W' ⊆ W)
    (hK : IsCompact {w : W | A w = y}) (hK' : IsCompact {w : W' | A w = y})
    (hfib : ∀ w ∈ W, A w = y → w ∈ W') :
    degree R hW' A (hA.mono hWW) y hK' = degree R hW A hA y hK := by
  refine degree_eq_of_push hK' hK' (fun _ hw => hw) ?_
  refine (push_push_apply (L' := {w : W | A w = y}) (L'' := {y}) (openIncl hWW)
    (restrictHom A hA) (restrictHom A (hA.mono hWW)) (openIncl_comp_restrictHom hWW)
    (fun _ hw => hw) (fun _ hw => Set.mem_singleton_iff.1 hw)
    (fun _ hw => Set.mem_singleton_iff.1 hw) (m + 1) (orientOn R hW' hK')).symm.trans ?_
  have himg : Subtype.val '' {w : W' | A w = y} = Subtype.val '' {w : W | A w = y} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩; exact ⟨⟨w.1, hWW w.2⟩, hw, rfl⟩
    · rintro ⟨w, hw, rfl⟩; exact ⟨⟨w.1, hfib w.1 w.2 hw⟩, hw, rfl⟩
  have e := push_openIncl_orientOn (R := R) hW' hW hWW hK' hK himg (fun _ hw => hw)
  exact (congrArg (push R (restrictHom A hA) (L := {w : W | A w = y}) (L' := {y})
    (fun _ hw => Set.mem_singleton_iff.1 hw) (m + 1)) e).trans (degree_spec hK)

omit [CommRing R] in
lemma restrictHom_id : restrictHom (W := W) id continuousOn_id = incl (X := TopCat.of 𝔼) W := rfl

/-- **(D-id)** `deg(id, W, y) = 1` for `y ∈ W`. -/
theorem degree_id (hy : y ∈ W) (hK : IsCompact {w : W | id w.1 = y}) :
    degree R hW id continuousOn_id y hK = 1 := by
  refine degree_eq_of_push hK hK (fun _ hw => hw) ?_
  rw [one_smul]
  refine (ConcreteCategory.congr_hom (push_congr (R := R) restrictHom_id _
    (fun _ hw => Set.mem_singleton_iff.1 hw) (m + 1)) _).trans ?_
  exact push_incl_orientOn_of_subset hW hK _
    (Set.singleton_subset_iff.2 ⟨⟨y, hy⟩, rfl, rfl⟩)

omit [CommRing R] in
/-- The straight-line homotopy `(1 - t) z + t A z` from the inclusion `W ⟶ 𝔼` to `A|W`. -/
noncomputable def straightHomotopy (hA : ContinuousOn A W) :
    ContinuousMap.Homotopy (incl (X := TopCat.of 𝔼) W).hom (restrictHom A hA).hom where
  toFun p := (1 - (p.1 : ℝ)) • (p.2 : 𝔼) + (p.1 : ℝ) • A p.2
  continuous_toFun := by
    have h1 : Continuous fun p : unitInterval × W => A p.2 :=
      hA.domRestrict.comp continuous_snd
    have h2 : Continuous fun p : unitInterval × W => (p.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    have h3 : Continuous fun p : unitInterval × W => (p.2 : 𝔼) :=
      continuous_subtype_val.comp continuous_snd
    exact ((continuous_const.sub h2).smul h3).add (h2.smul h1)
  map_zero_left z := by
    change (1 - (0 : ℝ)) • (z : 𝔼) + (0 : ℝ) • A z = z
    simp
  map_one_left z := by
    change (1 - (1 : ℝ)) • (z : 𝔼) + (1 : ℝ) • A z = A z
    simp

/-- **Degree one by a straight-line homotopy.** If every point `z` of `W` with
`(1 - t) z + t A z = y` for some `t ∈ [0, 1]` lies in the compact `K ⊆ W`, and `y ∈ K`, then
`deg(A, W, y) = 1`. -/
theorem degree_eq_one_of_straightLine (hK : IsCompact {w : W | A w = y}) {K : Set W}
    (hKc : IsCompact K) (hyK : y ∈ Subtype.val '' K)
    (hline : ∀ (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 → ∀ z : W, (1 - t) • (z : 𝔼) + t • A z = y → z ∈ K) :
    degree R hW A hA y hK = 1 := by
  have hsub : ∀ w : W, A w = y → w ∈ K := fun w hw =>
    hline 1 ⟨zero_le_one, le_rfl⟩ w (by simpa using hw)
  refine degree_eq_of_push hK hKc hsub ?_
  rw [one_smul]
  have h0 : ∀ x : TopCat.of W, incl (X := TopCat.of 𝔼) W x ∈ ({y} : Set 𝔼) → x ∈ K :=
    fun x hx => hline 0 ⟨le_rfl, zero_le_one⟩ x (by simpa using hx)
  have hh := push_eq_of_homotopy (R := R) (straightHomotopy hA) (L := K) (L' := {y})
    (fun t x hx => hline t t.2 x hx) h0 (fun w hw => hsub w hw) (m + 1)
  have h1 := ConcreteCategory.congr_hom hh (orientOn R hW hKc)
  have h2 := push_incl_orientOn_of_subset (R := R) hW hKc h0 (Set.singleton_subset_iff.2 hyK)
  exact h1.symm.trans h2

/-- **(DEG1) Near-identity.** On `W = ball c r`, if `|y - c| < r'` and the segments
`[z, A z]` for `r' ≤ |z - c| < r` avoid `y`, then `deg(A, ball c r, y) = 1`. -/
theorem degree_eq_one_of_segment {c : 𝔼} {r r' : ℝ} (hrr : r' < r) (hy : dist y c < r')
    {hA : ContinuousOn A (ball c r)}
    (hseg : ∀ z, r' ≤ dist z c → dist z c < r → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (1 - t) • z + t • A z ≠ y)
    (hK : IsCompact {w : ball c r | A w = y}) :
    degree R isOpen_ball A hA y hK = 1 := by
  have hKc : IsCompact (Subtype.val ⁻¹' closedBall c r' : Set (ball c r)) := by
    rw [Topology.IsInducing.subtypeVal.isCompact_iff, Subtype.image_preimage_coe,
      Set.inter_eq_right.2 (closedBall_subset_ball hrr)]
    exact isCompact_closedBall c r'
  have hyb : y ∈ ball c r := mem_ball.2 (hy.trans hrr)
  have hyc : y ∈ closedBall c r' := mem_closedBall.2 hy.le
  have hyK : y ∈ Subtype.val '' (Subtype.val ⁻¹' closedBall c r' : Set (ball c r)) :=
    ⟨⟨y, hyb⟩, Set.mem_preimage.2 hyc, rfl⟩
  refine degree_eq_one_of_straightLine (R := R) (W := ball c r) (hW := isOpen_ball) (A := A)
    (hA := hA) (y := y) hK hKc hyK fun t ht z hz => ?_
  by_contra hzK
  exact hseg z (le_of_lt (not_le.1 hzK)) z.2 t ht hz

/-- **(SEG)** The degree is constant along a segment `[y, y']` whose preimage in `W` is
compact. -/
theorem degree_eq_of_segment {y y' : 𝔼} (hL : IsCompact {w : W | A w ∈ segment ℝ y y'})
    (hK : IsCompact {w : W | A w = y}) (hK' : IsCompact {w : W | A w = y'}) :
    degree R hW A hA y hK = degree R hW A hA y' hK' := by
  have hb : Bornology.IsBounded (segment ℝ y y') :=
    isBounded_closedBall.subset (segment_subset_closedBall_left y y')
  obtain ⟨c, hc⟩ := exists_eq_smul_orient_convex (R := R) (convex_segment y y') hb
    ⟨y, left_mem_segment ℝ y y'⟩
    (push R (restrictHom A hA) (L := {w : W | A w ∈ segment ℝ y y'}) (L' := segment ℝ y y')
      (fun _ hw => hw) (m + 1) (orientOn R hW hL))
  have key : ∀ (z : 𝔼) (hz : z ∈ segment ℝ y y') (hKz : IsCompact {w : W | A w = z}),
      degree R hW A hA z hKz = c := by
    intro z hz hKz
    have hsub : ∀ w : W, A w = z → w ∈ {w : W | A w ∈ segment ℝ y y'} :=
      fun w hw => show A w ∈ segment ℝ y y' from hw ▸ hz
    refine degree_eq_of_push hKz hL hsub ?_
    have hzs : ({z} : Set 𝔼) ⊆ segment ℝ y y' := Set.singleton_subset_iff.2 hz
    refine (push_push_apply (L' := segment ℝ y y') (L'' := {z}) (restrictHom A hA)
      (𝟙 (TopCat.of 𝔼)) (restrictHom A hA) (Category.comp_id _) (fun _ hw => hw)
      (fun _ hw => hzs hw) (fun w hw => hsub w (Set.mem_singleton_iff.1 hw)) (m + 1)
      (orientOn R hW hL)).symm.trans ?_
    have e1 := congrArg (fun a => res R hzs (m + 1) a) hc
    refine e1.trans ?_
    simp only
    rw [map_smul, res_orient hb hzs]
  exact (key y (left_mem_segment ℝ y y') hK).trans (key y' (right_mem_segment ℝ y y') hK').symm

end Degree

section LocalDegree

variable {W : Set (EuclideanSpace ℝ (Fin (m + 1)))} {hW : IsOpen W}
  {h : EuclideanSpace ℝ (Fin (m + 1)) → EuclideanSpace ℝ (Fin (m + 1))} {hc : ContinuousOn h W}
  {hinj : Set.InjOn h W}

omit [CommRing R] in
lemma isCompact_fibre_of_injOn (hinj : Set.InjOn h W) {w : 𝔼} (hw : w ∈ W) :
    IsCompact {z : W | h z = h w} := by
  have : {z : W | h z = h w} = {⟨w, hw⟩} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact ⟨fun hz => Subtype.ext (hinj z.2 hw hz), fun hz => hz ▸ rfl⟩
  rw [this]
  exact isCompact_singleton

variable (R) in
/-- **The local degree** `ldeg_w(h) = deg(h, W, h w)` of a continuous injective `h` on `W` at
`w ∈ W` (the fibre is `{w}`). -/
noncomputable def ldeg (hW : IsOpen W) (h : 𝔼 → 𝔼) (hc : ContinuousOn h W)
    (hinj : Set.InjOn h W) (w : 𝔼) (hw : w ∈ W) : R :=
  degree R hW h hc (h w) (isCompact_fibre_of_injOn hinj hw)

/-- **(LD1)** If `h` moves the points of `B̄(w, ρ) ⊆ W` by at most `ρ / 8`, then
`ldeg_w(h) = 1`. -/
theorem ldeg_eq_one_of_dist_le {w : 𝔼} {ρ : ℝ} (hρ : 0 < ρ) (hball : closedBall w ρ ⊆ W)
    (hnear : ∀ z ∈ closedBall w ρ, dist (h z) z ≤ ρ / 8) (hw : w ∈ W) :
    ldeg R hW h hc hinj w hw = 1 := by
  have hbW : ball w ρ ⊆ W := ball_subset_closedBall.trans hball
  have hfib : ∀ z ∈ W, h z = h w → z ∈ ball w ρ := fun z hz hzw =>
    (hinj hz hw hzw) ▸ mem_ball_self hρ
  have hK := isCompact_fibre_of_injOn hinj hw
  have hK' := isCompact_fibre_of_subset (A := h) (y := h w) hbW hfib hK
  rw [ldeg, ← degree_congr_open (hW := hW) (hA := hc) isOpen_ball hbW hK hK' hfib]
  have hww : dist (h w) w ≤ ρ / 8 := hnear w (mem_closedBall_self hρ.le)
  refine degree_eq_one_of_segment (r' := ρ / 3) (by linarith) (by linarith) ?_ hK'
  intro z hz1 hz2 t ht heq
  have hzn : dist (h z) z ≤ ρ / 8 := hnear z (mem_closedBall.2 hz2.le)
  rw [dist_eq_norm] at hz1 hzn hww
  have hzw : z - w = (h w - w) - t • (h z - z) := by
    rw [← heq]; module
  have : ‖z - w‖ ≤ ρ / 8 + ρ / 8 := by
    rw [hzw]
    refine (norm_sub_le _ _).trans (add_le_add hww ?_)
    rw [norm_smul, Real.norm_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans hzn
  linarith

/-- The local degree is locally constant. -/
theorem ldeg_eventually_eq {w₀ : 𝔼} (hw₀ : w₀ ∈ W) :
    ∀ᶠ w in 𝓝 w₀, ∀ hw : w ∈ W, ldeg R hW h hc hinj w hw = ldeg R hW h hc hinj w₀ hw₀ := by
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.1 hW w₀ hw₀
  set r := ε / 2 with hr
  have hr0 : 0 < r := by positivity
  have hcbW : closedBall w₀ r ⊆ W := (closedBall_subset_ball (by linarith)).trans hεW
  -- the compact `D = B̄(w₀, r)`, in `W` and its image in `𝔼`
  let D : Set W := Subtype.val ⁻¹' closedBall w₀ r
  have hD : IsCompact D := by
    rw [Topology.IsInducing.subtypeVal.isCompact_iff, Subtype.image_preimage_coe,
      Set.inter_eq_right.2 hcbW]
    exact isCompact_closedBall w₀ r
  have hE : IsCompact (h '' closedBall w₀ r) :=
    (isCompact_closedBall w₀ r).image_of_continuousOn (hc.mono hcbW)
  have hcond : ∀ x : TopCat.of W, restrictHom h hc x ∈ h '' closedBall w₀ r → x ∈ D := by
    rintro x ⟨z, hz, hzx⟩
    have : z = x.1 := hinj (hcbW hz) x.2 hzx
    show x.1 ∈ closedBall w₀ r
    exact this ▸ hz
  let β := push R (restrictHom h hc) (L := D) (L' := h '' closedBall w₀ r) hcond (m + 1)
    (orientOn R hW hD)
  have hw₀E : h w₀ ∈ h '' closedBall w₀ r := ⟨w₀, mem_closedBall_self hr0.le, rfl⟩
  obtain ⟨t, ht, c, hct⟩ := exists_locallyConstant_res hE β hw₀E
  -- every `w ∈ ball w₀ r` with `h w` close to `h w₀` has local degree `c`
  have key : ∀ w (hw : w ∈ W), w ∈ ball w₀ r → dist (h w) (h w₀) < t →
      ldeg R hW h hc hinj w hw = c := by
    intro w hw hwb hwt
    have hwE : h w ∈ h '' closedBall w₀ r := ⟨w, ball_subset_closedBall hwb, rfl⟩
    have hsub : ∀ z : W, h z = h w → z ∈ D := fun z hz => by
      show z.1 ∈ closedBall w₀ r
      rw [hinj z.2 hw hz]
      exact ball_subset_closedBall hwb
    refine degree_eq_of_push (isCompact_fibre_of_injOn hinj hw) hD hsub ?_
    have hsing : ({h w} : Set 𝔼) ⊆ h '' closedBall w₀ r := Set.singleton_subset_iff.2 hwE
    refine (push_push_apply (L' := h '' closedBall w₀ r) (L'' := {h w}) (restrictHom h hc)
      (𝟙 (TopCat.of 𝔼)) (restrictHom h hc) (Category.comp_id _) hcond
      (fun _ hv => hsing hv) (fun z hz => hsub z (Set.mem_singleton_iff.1 hz)) (m + 1)
      (orientOn R hW hD)).symm.trans ?_
    exact hct (h w) hwE hwt
  have hev : ∀ᶠ w in 𝓝 w₀, w ∈ ball w₀ r ∧ dist (h w) (h w₀) < t :=
    (show ∀ᶠ w in 𝓝 w₀, w ∈ ball w₀ r from ball_mem_nhds w₀ hr0).and ((hc.continuousAt (hW.mem_nhds hw₀)).eventually
      (ball_mem_nhds (h w₀) ht))
  filter_upwards [hev] with w hw hwW
  rw [key w hwW hw.1 hw.2, key w₀ hw₀ (mem_ball_self hr0) (by simpa using ht)]

/-- **(LOC)** The local degree is constant on preconnected subsets of `W`. -/
theorem ldeg_eq_of_isPreconnected {S : Set 𝔼} (hS : IsPreconnected S) (hSW : S ⊆ W)
    {w₁ w₂ : 𝔼} (h₁ : w₁ ∈ S) (h₂ : w₂ ∈ S) :
    ldeg R hW h hc hinj w₁ (hSW h₁) = ldeg R hW h hc hinj w₂ (hSW h₂) := by
  let f : W → R := fun w => ldeg R hW h hc hinj w.1 w.2
  have hf : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have := (continuous_subtype_val.continuousAt (x := x)).eventually
      (ldeg_eventually_eq (R := R) (hW := hW) (hc := hc) (hinj := hinj) x.2)
    filter_upwards [this] with y hy
    exact hy y.2
  have hT : IsPreconnected (Subtype.val ⁻¹' S : Set W) := by
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
      Set.inter_eq_right.2 hSW]
    exact hS
  exact hf.apply_eq_of_isPreconnected hT (x := ⟨w₁, hSW h₁⟩) (y := ⟨w₂, hSW h₂⟩) h₁ h₂

end LocalDegree

end HSFormal.Newman
