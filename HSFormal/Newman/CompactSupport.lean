import HSFormal.Newman.EuclidLocal
import TauCeti.AlgebraicTopology.Singular.DirectedUnion

/-!
# N4. Compact supports (Newman blueprint, module N4)

Throughout, `𝔼 = EuclideanSpace ℝ (Fin (m + 1))`.

* `exists_singularHomologyMap_inclusion_eq`: every singular homology class of `V` comes from a
  member of an increasing cover of `V` by relatively open sets (from TauCeti's
  `isColimitMapCoconeSingularHomology` and `Concrete.isColimit_exists_rep`).
* `ConvexCover L`: finite families of compact convex sets whose union is a neighbourhood of `L`,
  directed by reverse inclusion of the unions (`ConvexCover.isDirected`), nonempty for compact `L`,
  and exhausting `𝔼 ∖ L` (`ConvexCover.exists_notMem`).
* **(E4)** `exists_res_eq_of_isCompact`: every `α ∈ H_{i+1}(𝔼 | L)`, `L` compact, is the
  restriction of a class on a finite union of compact convex sets whose interior contains `L`.
* **(V-all)** `vanishAbove_of_isCompact`: `H_i(𝔼 | L) = 0` for `i > m + 1`, `L` compact.
* **(LCS)** `exists_locallyConstant_res`: near `w₀ ∈ L`, the restrictions of
  `β ∈ H_{m+1}(𝔼 | L)` to points are `c • o_w` for one `c`.
* `ConvexPiece X m` (chart `e`, compact convex `C ⊆ e.target`, carrier `e.symm '' C`),
  `vanishAbove_of_subset_chart` (`V` for compacta inside one chart of a Hausdorff `X`) and
  `vanishAbove_pointInj_biUnion_pieces` / `vanishAbove_pointInj_iUnion_pieces`: `V ∧ P` in degree
  `m + 1` for finite unions of chart-convex pieces of a Hausdorff space.

## Deviations from the blueprint

* (E4) is proved with the *unreduced* long exact sequence of the pair `(𝔼, 𝔼 ∖ L)`: the
  connecting map `H_{i+1}(𝔼 | L) ⟶ H_i(𝔼 ∖ L)` is injective (`singularHomologyδ_injective`, `𝔼`
  contractible), and a class `y` of `H_i(𝔼 ∖ L')` with `δ α = ι y` dies in `H_i(𝔼)`, hence comes
  from `H_{i+1}(𝔼 | L')`. This treats degree `0` uniformly, so the blueprint's separate
  "kernel of `ε`" argument is not needed.
* `ConvexPiece.carrier` names the set `e.symm '' C`; the union lemma is stated for a `Finset` of
  indices (the `Fintype` form is the corollary `vanishAbove_pointInj_iUnion_pieces`).
-/

open CategoryTheory Limits Topology Metric AlgebraicTopology

namespace HSFormal.Newman

section DirectedUnion

variable {R : Type} [CommRing R]

/-- **Compact supports, surjectivity.** For an increasing family `U j` of subsets of `V`, open in
`V` and covering `V`, every singular homology class of `V` comes from some `U j`. -/
theorem exists_singularHomologyMap_inclusion_eq (n : ℕ) {Y : TopCat.{0}} {J : Type} [Preorder J]
    [IsDirected J (· ≤ ·)] [Nonempty J] {U : J → Set Y} (hU : Monotone U) {V : Set Y}
    (hUV : ∀ j, U j ⊆ V) (hopen : ∀ j, IsOpen (Subtype.val ⁻¹' U j : Set V))
    (hcover : V ⊆ ⋃ j, U j)
    (x : ((singularHomologyFunctor (ModuleCat.{0} R) n).obj (coef R)).obj (TopCat.of V)) :
    ∃ j, ∃ y : ((singularHomologyFunctor (ModuleCat.{0} R) n).obj (coef R)).obj
        (TopCat.of (U j)),
      ((singularHomologyFunctor _ n).obj (coef R)).map
        (TopCat.ofHom (ContinuousMap.inclusion (hUV j))) y = x := by
  have : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{0} R)) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  let c : Cocone ({ obj j := TopCat.of (U j)
                    map f := TopCat.ofHom (ContinuousMap.inclusion (hU f.le)) } : J ⥤ TopCat.{0}) :=
    { pt := TopCat.of V, ι := { app j := TopCat.ofHom (ContinuousMap.inclusion (hUV j)) } }
  have hK (K : Set c.pt) (hK : IsCompact K) : ∃ j, K ⊆ Set.range (c.ι.app j) := by
    obtain ⟨j, hj⟩ := hK.elim_directed_cover (fun j ↦ (Subtype.val ⁻¹' U j : Set V)) hopen
      (fun x _ ↦ Set.mem_iUnion.2 (Set.mem_iUnion.1 (hcover x.2) : ∃ j, x.1 ∈ U j))
      (Monotone.directed_le fun _ _ h ↦ Set.preimage_mono (hU h))
    exact ⟨j, fun x hx ↦ ⟨⟨x.1, hj hx⟩, rfl⟩⟩
  exact Concrete.isColimit_exists_rep _
    (TauCeti.isColimitMapCoconeSingularHomology (coef R) n c
      (fun j ↦ IsEmbedding.inclusion (hUV j)) hK) x

end DirectedUnion

section Covers

variable {m : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin (m + 1))

/-- Finite families of compact convex sets whose union is a neighbourhood of `L`. -/
def ConvexCover (L : Set 𝔼) : Type :=
  {S : Finset (Set 𝔼) // (∀ s ∈ S, Convex ℝ s ∧ IsCompact s) ∧ L ⊆ interior (⋃ s ∈ S, s)}

variable {L : Set (EuclideanSpace ℝ (Fin (m + 1)))}

/-- The union of a convex cover. -/
def ConvexCover.carrier (S : ConvexCover L) : Set 𝔼 := ⋃ s ∈ S.1, s

/-- Ordered by reverse inclusion of the unions. -/
instance ConvexCover.instPreorder : Preorder (ConvexCover L) := Preorder.lift fun S => OrderDual.toDual S.carrier

lemma ConvexCover.le_iff {S T : ConvexCover L} : S ≤ T ↔ T.carrier ⊆ S.carrier := Iff.rfl

lemma ConvexCover.isClosed_carrier (S : ConvexCover L) : IsClosed S.carrier :=
  isClosed_biUnion_finset fun s hs => (S.2.1 s hs).2.isClosed

lemma ConvexCover.subset_carrier (S : ConvexCover L) : L ⊆ S.carrier :=
  S.2.2.trans interior_subset

lemma ConvexCover.nonempty (hL : IsCompact L) : Nonempty (ConvexCover L) := by
  obtain ⟨r, hr⟩ := hL.isBounded.subset_ball (0 : 𝔼)
  refine ⟨⟨{closedBall 0 r}, by simpa using ⟨convex_closedBall _ _, isCompact_closedBall _ _⟩, ?_⟩⟩
  simp only [Finset.mem_singleton, Set.iUnion_iUnion_eq_left]
  exact hr.trans (interior_maximal ball_subset_closedBall isOpen_ball)

instance ConvexCover.isDirected : IsDirected (ConvexCover L) (· ≤ ·) := by
  classical
  refine ⟨fun S T => ?_⟩
  let W : Finset (Set 𝔼) := (S.1 ×ˢ T.1).image fun p => p.1 ∩ p.2
  have hW : (⋃ w ∈ W, w) = S.carrier ∩ T.carrier := by
    ext z
    simp only [W, ConvexCover.carrier, Set.mem_iUnion, Finset.mem_image, Finset.mem_product, Set.mem_inter_iff,
      exists_prop]
    constructor
    · rintro ⟨w, ⟨⟨s, t⟩, ⟨hs, ht⟩, rfl⟩, hzs, hzt⟩
      exact ⟨⟨s, hs, hzs⟩, ⟨t, ht, hzt⟩⟩
    · rintro ⟨⟨s, hs, hzs⟩, ⟨t, ht, hzt⟩⟩
      exact ⟨s ∩ t, ⟨⟨s, t⟩, ⟨hs, ht⟩, rfl⟩, hzs, hzt⟩
  have hWc : ∀ w ∈ W, Convex ℝ w ∧ IsCompact w := by
    intro w hw
    obtain ⟨⟨s, t⟩, hst, rfl⟩ := Finset.mem_image.1 hw
    obtain ⟨hs, ht⟩ := Finset.mem_product.1 hst
    exact ⟨(S.2.1 s hs).1.inter (T.2.1 t ht).1, (S.2.1 s hs).2.inter_right (T.2.1 t ht).2.isClosed⟩
  refine ⟨⟨W, hWc, ?_⟩, ?_, ?_⟩
  · rw [hW]
    exact interior_maximal (Set.inter_subset_inter interior_subset interior_subset)
      (isOpen_interior.inter isOpen_interior) |>.trans' fun z hz => ⟨S.2.2 hz, T.2.2 hz⟩
  · show (⋃ w ∈ W, w) ⊆ S.carrier
    rw [hW]; exact Set.inter_subset_left
  · show (⋃ w ∈ W, w) ⊆ T.carrier
    rw [hW]; exact Set.inter_subset_right

/-- Every point outside the compact set `L` lies outside some convex cover of `L`. -/
lemma ConvexCover.exists_notMem (hL : IsCompact L) {z : 𝔼} (hz : z ∉ L) :
    ∃ S : ConvexCover L, z ∉ S.carrier := by
  classical
  rcases L.eq_empty_or_nonempty with rfl | hne
  · exact ⟨⟨∅, by simp, by simp⟩, by simp [ConvexCover.carrier]⟩
  have hd : 0 < infDist z L := (hL.isClosed.notMem_iff_infDist_pos hne).1 hz
  set r := infDist z L / 2 with hr
  have hr0 : 0 < r := by positivity
  obtain ⟨t, htL, hcov⟩ := hL.elim_nhds_subcover (fun x => ball x r)
    (fun x _ => ball_mem_nhds x hr0)
  refine ⟨⟨t.image fun x => closedBall x r, ?_, ?_⟩, ?_⟩
  · intro s hs
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hs
    exact ⟨convex_closedBall _ _, isCompact_closedBall _ _⟩
  · refine hcov.trans (interior_maximal ?_ (isOpen_biUnion fun _ _ => isOpen_ball))
    rw [Finset.set_biUnion_finset_image]
    exact Set.iUnion₂_mono fun x _ => ball_subset_closedBall
  · simp only [ConvexCover.carrier, Finset.set_biUnion_finset_image, Set.mem_iUnion, mem_closedBall,
      not_exists, not_le]
    intro x hx
    have := infDist_le_dist_of_mem (htL x hx) (x := z)
    linarith

end Covers

section E4

variable {R : Type} [CommRing R] {m : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin (m + 1))

/-- The connecting map `H_{i+1}(𝔼 | L) ⟶ H_i(𝔼 ∖ L)` is injective (`𝔼` is contractible). -/
lemma singularHomologyδ_injective (L : Set 𝔼) (i : ℕ) :
    Function.Injective ((TopPair.ofSubset (X := TopCat.of 𝔼) Lᶜ).singularHomologyδ
      (coef R) (i + 1) i) := by
  let P := TopPair.ofSubset (X := TopCat.of 𝔼) Lᶜ
  have hex := P.singularHomology_exact_relative (coef R) (i + 1) i
  have hZ : IsZero ((TopPair.toSSetPair.obj P).right.homology (coef R) (i + 1)) :=
    TauCeti.isZero_singularHomologyFunctor_of_contractibleSpace (coef R) (TopCat.of 𝔼)
      (Nat.succ_ne_zero i)
  have : Mono (P.singularHomologyδ (coef R) (i + 1) i) := hex.mono_g (hZ.eq_of_src _ _)
  exact (ModuleCat.mono_iff_injective _).1 this

/-- **(E4) Compact supports.** Every class of `H_{i+1}(𝔼 | L)`, `L` compact, is the restriction
of a class of `H_{i+1}(𝔼 | L')` for a finite union `L'` of compact convex sets with
`L ⊆ interior L'`. -/
theorem exists_res_eq_of_isCompact {L : Set 𝔼} (hL : IsCompact L) {i : ℕ}
    (α : relH R (TopCat.of 𝔼) L (i + 1)) :
    ∃ S : Finset (Set 𝔼), ∃ _ : ∀ s ∈ S, Convex ℝ s ∧ IsCompact s,
      ∃ hLS : L ⊆ interior (⋃ s ∈ S, s), ∃ β : relH R (TopCat.of 𝔼) (⋃ s ∈ S, s) (i + 1),
        res R (hLS.trans interior_subset) (i + 1) β = α := by
  have := ConvexCover.nonempty hL
  let F := (singularHomologyFunctor (ModuleCat.{0} R) i).obj (coef R)
  let P := TopPair.ofSubset (X := TopCat.of 𝔼) Lᶜ
  have hmono : Monotone fun S : ConvexCover L => S.carrierᶜ :=
    fun S T hST => Set.compl_subset_compl.2 hST
  have hUV : ∀ S : ConvexCover L, S.carrierᶜ ⊆ Lᶜ := fun S =>
    Set.compl_subset_compl.2 S.subset_carrier
  have hopen : ∀ S : ConvexCover L, IsOpen (Subtype.val ⁻¹' S.carrierᶜ : Set ↥Lᶜ) := fun S =>
    S.isClosed_carrier.isOpen_compl.preimage continuous_subtype_val
  have hcover : Lᶜ ⊆ ⋃ S : ConvexCover L, S.carrierᶜ := fun z hz => by
    obtain ⟨S, hS⟩ := ConvexCover.exists_notMem hL hz
    exact Set.mem_iUnion.2 ⟨S, hS⟩
  let δL := P.singularHomologyδ (coef R) (i + 1) i rfl
  let x := δL α
  let x' : F.obj (TopCat.of ↥Lᶜ) := x
  obtain ⟨S, y, hy⟩ := exists_singularHomologyMap_inclusion_eq (R := R) i (Y := TopCat.of 𝔼)
    (V := Lᶜ) hmono hUV hopen hcover x'
  let PS := TopPair.ofSubset (X := TopCat.of 𝔼) S.carrierᶜ
  -- `y` dies in `𝔼`, hence comes from `H_{i+1}(𝔼 | S.carrier)`.
  have hfac : TopCat.ofHom (ContinuousMap.inclusion (hUV S)) ≫ P.map = PS.map := rfl
  have hPx : F.map P.map x' = 0 := by
    have h0 : δL ≫ F.map P.map = 0 := P.singularHomologyδ_comp (coef R) (i + 1) i
    exact ConcreteCategory.congr_hom h0 α
  have hy0 : F.map PS.map y = 0 := by
    have e : F.map PS.map = F.map (TopCat.ofHom (ContinuousMap.inclusion (hUV S))) ≫
        F.map P.map :=
      F.map_comp (TopCat.ofHom (ContinuousMap.inclusion (hUV S))) P.map
    refine (ConcreteCategory.congr_hom e y).trans ?_
    change F.map P.map (F.map (TopCat.ofHom (ContinuousMap.inclusion (hUV S))) y) = 0
    rw [hy]
    exact hPx
  have hexS := PS.singularHomology_exact_subspace (coef R) (i + 1) i
  obtain ⟨β, hβ⟩ := (ShortComplex.moduleCat_exact_iff _).1 hexS y hy0
  refine ⟨S.1, S.2.1, S.2.2, β, ?_⟩
  -- naturality of `δ` along `(𝔼, 𝔼 ∖ S.carrier) ⟶ (𝔼, 𝔼 ∖ L)`
  apply singularHomologyδ_injective (R := R) L i
  have hnat := TopPair.singularHomologyδ_naturality (coef R)
    (TopPair.ofSubsetMap (𝟙 (TopCat.of 𝔼)) (mapsTo_compl_of (𝟙 (TopCat.of 𝔼))
      (L := S.carrier) (L' := L) fun _ hx => S.subset_carrier hx)) (i + 1) i
  refine (ConcreteCategory.congr_hom hnat β).symm.trans ?_
  change F.map (TopCat.ofHom (ContinuousMap.inclusion (hUV S)))
    (PS.singularHomologyδ (coef R) (i + 1) i rfl β) = x'
  have hβ' : PS.singularHomologyδ (coef R) (i + 1) i rfl β = y := hβ
  rw [hβ']
  exact hy

/-- **(V-all)** `H_i(𝔼 | L) = 0` for `i > m + 1` and every compact `L`. -/
theorem vanishAbove_of_isCompact {L : Set 𝔼} (hL : IsCompact L) :
    VanishAbove R (TopCat.of 𝔼) L (m + 1) := by
  intro i hi
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  refine isZero_of_forall_eq_zero fun α => ?_
  obtain ⟨S, hS, hLS, β, rfl⟩ := exists_res_eq_of_isCompact hL α
  rw [eq_zero_of_isZero ((vanishAbove_pointInj_biUnion S hS).1 (k + 1) hi) β, map_zero]

/-- **(LCS) Local constancy of sections.** For `β ∈ H_{m+1}(𝔼 | L)`, `L` compact, and `w₀ ∈ L`,
the restrictions of `β` to the points of `L` near `w₀` are a common multiple of the orientation
classes. -/
theorem exists_locallyConstant_res {L : Set 𝔼} (hL : IsCompact L)
    (β : relH R (TopCat.of 𝔼) L (m + 1)) {w₀ : 𝔼} (hw₀ : w₀ ∈ L) :
    ∃ t > 0, ∃ c : R, ∀ w (hw : w ∈ L), dist w w₀ < t →
      res R (Set.singleton_subset_iff.2 hw) (m + 1) β = c • orient R m {w} := by
  obtain ⟨S, hS, hLS, β', rfl⟩ := exists_res_eq_of_isCompact hL β
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior w₀ (hLS hw₀)
  have hD : closedBall w₀ (ε / 2) ⊆ ⋃ s ∈ S, s :=
    (closedBall_subset_ball (by linarith)).trans (hball.trans interior_subset)
  obtain ⟨c, hc⟩ := exists_eq_smul_orient_convex (R := R) (convex_closedBall w₀ (ε / 2))
    isBounded_closedBall (nonempty_closedBall.2 (by linarith)) (res R hD (m + 1) β')
  refine ⟨ε / 2, by linarith, c, fun w hw hww => ?_⟩
  have hwD : {w} ⊆ closedBall w₀ (ε / 2) := Set.singleton_subset_iff.2 (le_of_lt hww)
  calc res R _ (m + 1) (res R _ (m + 1) β')
      = res R (hwD.trans hD) (m + 1) β' := res_res_apply _ _ _ _
    _ = res R hwD (m + 1) (res R hD (m + 1) β') := (res_res_apply hD hwD _ β').symm
    _ = c • orient R m {w} := by rw [hc, map_smul, res_orient isBounded_closedBall]

end E4

section Pieces

variable {R : Type} [CommRing R] {m : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin (m + 1))

/-- `V` for compacta inside a chart (by (V-all) and chart transport). -/
theorem vanishAbove_of_subset_chart {X : TopCat.{0}} [T2Space X]
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin (m + 1)))) {K : Set X} (hK : IsCompact K)
    (hKs : K ⊆ e.source) : VanishAbove R X K (m + 1) := by
  have hC : IsCompact (e '' K) := hK.image_of_continuousOn (e.continuousOn.mono hKs)
  have hCt : e '' K ⊆ e.target := e.mapsTo.image_subset.trans' (Set.image_mono hKs)
  have := (vanishAbove_chart_iff (R := R) e hC hCt).1 (vanishAbove_of_isCompact hC)
  have hKK : e.symm '' (e '' K) = K := e.toPartialEquiv.symm_image_image_of_subset_source hKs
  rwa [hKK] at this

/-- A *chart-convex piece* of `X`: the image `e.symm '' C` of a compact convex `C ⊆ e.target`
under the inverse of a chart `e`. -/
structure ConvexPiece (X : TopCat.{0}) (m : ℕ) where
  /-- the chart -/
  e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin (m + 1)))
  /-- the convex set, in chart coordinates -/
  C : Set (EuclideanSpace ℝ (Fin (m + 1)))
  convex : Convex ℝ C
  compact : IsCompact C
  subset : C ⊆ e.target

/-- The subset `e.symm '' C` of `X` carried by a chart-convex piece. -/
def ConvexPiece.carrier {X : TopCat.{0}} (P : ConvexPiece X m) : Set X := P.e.symm '' P.C

lemma ConvexPiece.isCompact_carrier {X : TopCat.{0}} (P : ConvexPiece X m) :
    IsCompact P.carrier :=
  P.compact.image_of_continuousOn (P.e.continuousOn_symm.mono P.subset)

lemma ConvexPiece.carrier_subset_source {X : TopCat.{0}} (P : ConvexPiece X m) :
    P.carrier ⊆ P.e.source := by
  rintro _ ⟨c, hc, rfl⟩
  exact P.e.map_target (P.subset hc)

/-- **(CT) `V ∧ P` for finite unions of chart-convex pieces** of a Hausdorff space. -/
theorem vanishAbove_pointInj_biUnion_pieces {X : TopCat.{0}} [T2Space X] {ι : Type*}
    (S : Finset ι) (P : ι → ConvexPiece X m) :
    VanishAbove R X (⋃ j ∈ S, (P j).carrier) (m + 1) ∧
      PointInj R X (⋃ j ∈ S, (P j).carrier) (m + 1) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty]
    exact ⟨vanishAbove_empty _, pointInj_empty _⟩
  | insert a S ha ih =>
    rw [Finset.set_biUnion_insert]
    have hV₁ : VanishAbove R X (P a).carrier (m + 1) :=
      (vanishAbove_chart_iff (P a).e (P a).compact (P a).subset).1
        (vanishAbove_convex (P a).convex (P a).compact.isBounded)
    have hP₁ : PointInj R X (P a).carrier (m + 1) :=
      (pointInj_chart_iff (P a).e (P a).compact (P a).subset).1
        (pointInj_convex (P a).convex (P a).compact.isBounded)
    have hc₁ : IsClosed (P a).carrier := (P a).isCompact_carrier.isClosed
    have hc₂ : IsClosed (⋃ j ∈ S, (P j).carrier) :=
      isClosed_biUnion_finset fun j _ => (P j).isCompact_carrier.isClosed
    have hVI : VanishAbove R X ((P a).carrier ∩ ⋃ j ∈ S, (P j).carrier) (m + 1) :=
      vanishAbove_of_subset_chart (P a).e ((P a).isCompact_carrier.inter_right hc₂)
        (Set.inter_subset_left.trans (P a).carrier_subset_source)
    exact ⟨hV₁.union hc₁ hc₂ ih.1 hVI, hP₁.union hc₁ hc₂ ih.2 (hVI _ (by omega))⟩

/-- The `Fintype`-indexed form of `vanishAbove_pointInj_biUnion_pieces`. -/
theorem vanishAbove_pointInj_iUnion_pieces {X : TopCat.{0}} [T2Space X] {ι : Type*} [Fintype ι]
    (P : ι → ConvexPiece X m) :
    VanishAbove R X (⋃ j, (P j).carrier) (m + 1) ∧ PointInj R X (⋃ j, (P j).carrier) (m + 1) := by
  have := vanishAbove_pointInj_biUnion_pieces (R := R) Finset.univ P
  simpa only [Finset.mem_univ, Set.iUnion_true] using this

end Pieces

end HSFormal.Newman
