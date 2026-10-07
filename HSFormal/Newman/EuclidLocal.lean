import HSFormal.Newman.Glue
import TauCeti.AlgebraicTopology.Singular.ReducedRelative
import TauCeti.AlgebraicTopology.Singular.Contractible
import TauCeti.AlgebraicTopology.Singular.Sphere
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# N3. Local homology of `𝔼 = ℝ^{m+1}` at bounded convex sets (Newman blueprint, module N3)

Throughout, `𝔼 = EuclideanSpace ℝ (Fin (m + 1))` and coefficients are a commutative ring `R`.

* `complConvexHomotopyEquiv`: for `C` convex in a real normed space with `x ∈ C ⊆ ball x ρ`, the
  complement `Cᶜ` is homotopy equivalent to the unit sphere (`u ↦ x + ρ u`, radial projection;
  the straight-line homotopy avoids `C` by `add_smul_sub_notMem`). No closedness is needed.
* `isZero_relH_zero`: `H_0(X | L) = 0` for path-connected `X` and `L ≠ X`.
* `relHSuccIsoReduced`: `H_{k+1}(𝔼 | L) ≅ H̃_k(𝔼 ∖ L)` (connecting map; `𝔼` contractible), natural
  in `L` (`relHSuccIsoReduced_naturality`).
* **(E1)** `isZero_relH_convex`: `H_i(𝔼 | C) = 0` for `i ≠ m + 1`; `isIso_res_convex`:
  `res : H_i(𝔼 | C) ⟶ H_i(𝔼 | C')` is an isomorphism for convex `C' ⊆ C`, `C` bounded, `C'`
  nonempty (all `i`); `relHConvexIso : H_{m+1}(𝔼 | C) ≅ R`.
* **(E2)** `orient R m L ∈ H_{m+1}(𝔼 | L)` (junk `0` for unbounded `L`), with `res_orient`
  (compatibility with restriction), `orientIso` (`R ≅ H_{m+1}(𝔼 | C)`, `1 ↦ o_C`, for `C`
  bounded convex nonempty), `exists_eq_smul_orient_convex`, `smul_orient_eq_zero_iff`,
  `orient_convex_ne_zero`, `orient_point_ne_zero`.
* **(E3)** `vanishAbove_convex`, `pointInj_convex` and `vanishAbove_pointInj_biUnion`: `V ∧ P` in
  degree `m + 1` for every finite union of compact convex sets.

## Deviations from the blueprint

* (E1) is proved for *bounded* convex sets (not only compact ones), and `isIso_res_convex` covers
  any nested pair of convex sets, not only a point inside `C`. `orient` is built from the classes
  `ω_N` on the balls `B̄(0, N)`, `N : ℕ`.
* The coefficient ring is a general commutative ring `R` (`R = ZMod p` in the application);
  `orient_point_ne_zero` needs `[Nontrivial R]`, and `smul_orient_eq_zero_iff` replaces the use of
  "`𝔽` is a field" in the blueprint.
-/

open CategoryTheory Limits Topology Metric

namespace HSFormal.Newman

section SphereEquiv

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {C : Set E} {x : E} {ρ : ℝ}

/-- The key estimate for the radial homotopy: for `C` convex, `x ∈ C ⊆ ball x ρ`, `z ∉ C`,
the points `x + ((1 - t) a + t) (z - x)`, `a = ρ / ‖z - x‖`, `t ∈ [0,1]`, avoid `C`. -/
lemma add_smul_sub_notMem (hC : Convex ℝ C) (hx : x ∈ C) (hCb : C ⊆ ball x ρ) {z : E}
    (hz : z ∉ C) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    x + ((1 - t) * (ρ / ‖z - x‖) + t) • (z - x) ∉ C := by
  have hzx : z ≠ x := fun h => hz (h ▸ hx)
  have hn : 0 < ‖z - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hzx)
  have hρ : 0 < ρ := by simpa using (hCb hx)
  set a := ρ / ‖z - x‖ with ha_def
  have ha : 0 < a := div_pos hρ hn
  set l := (1 - t) * a + t with hl_def
  intro hp
  have hpb := hCb hp
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul] at hpb
  have hl0 : 0 < l := by
    rcases eq_or_lt_of_le ht0 with h | h
    · rw [hl_def, ← h]; simpa using ha
    · have : 0 ≤ (1 - t) * a := mul_nonneg (by linarith) ha.le
      linarith
  rw [Real.norm_of_nonneg hl0.le] at hpb
  have hla : l < a := by
    rw [ha_def, lt_div_iff₀ hn]; exact hpb
  -- hence `l ≥ 1`
  have hl1 : 1 ≤ l := by
    by_contra hcon
    replace hcon := not_le.1 hcon
    have : a ≤ l := by
      have : 0 ≤ t * (1 - a) := by
        rcases le_or_gt a 1 with h | h
        · exact mul_nonneg ht0 (by linarith)
        · exfalso
          have : 1 ≤ l := by
            rw [hl_def]; nlinarith
          linarith
      nlinarith
    linarith
  -- convexity: `z` is a convex combination of `x` and the point `p ∈ C`
  apply hz
  have hcomb := hC hx hp (a := 1 - l⁻¹) (b := l⁻¹) (sub_nonneg.2 (inv_le_one_of_one_le₀ hl1))
    (inv_nonneg.2 hl0.le) (by ring)
  convert hcomb using 1
  rw [smul_add, smul_smul, inv_mul_cancel₀ hl0.ne', one_smul, sub_smul, one_smul]
  abel

omit [NormedSpace ℝ E] in
lemma norm_sub_pos_of_notMem (hx : x ∈ C) {z : E} (hz : z ∉ C) : 0 < ‖z - x‖ :=
  norm_pos_iff.2 (sub_ne_zero.2 fun h => hz (h ▸ hx))

omit [NormedSpace ℝ E] in
lemma pos_of_subset_ball (hx : x ∈ C) (hCb : C ⊆ ball x ρ) : 0 < ρ := by
  simpa using hCb hx

variable (C x ρ) in
/-- `u ↦ x + ρ u`, from the unit sphere into the complement of `C ⊆ ball x ρ`. -/
noncomputable def sphereToCompl (hCb : C ⊆ ball x ρ) : C(sphere (0 : E) 1, ↥Cᶜ) where
  toFun u := ⟨x + ρ • (u : E), fun h => by
    have hb := hCb h
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_eq_of_mem_sphere u,
      mul_one, Real.norm_eq_abs] at hb
    exact (lt_irrefl _ (hb.trans_le (le_abs_self ρ)))⟩
  continuous_toFun := by fun_prop

variable (C x) in
/-- Radial projection `z ↦ (z - x) / ‖z - x‖` from the complement of `C ∋ x` to the unit sphere. -/
noncomputable def complToSphere (hx : x ∈ C) : C(↥Cᶜ, sphere (0 : E) 1) where
  toFun z := ⟨‖(z : E) - x‖⁻¹ • ((z : E) - x), by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_sub_pos_of_notMem hx z.2).ne']⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.smul ?_ (by fun_prop)) _
    exact (continuous_norm.comp (by fun_prop)).inv₀ fun z => (norm_sub_pos_of_notMem hx z.2).ne'

/-- **`Cᶜ ≃ₕ S`**: for `C` convex with `x ∈ C ⊆ ball x ρ`, the complement of `C` is homotopy
equivalent to the unit sphere, through `u ↦ x + ρ u` and the radial projection from `x`. -/
noncomputable def complConvexHomotopyEquiv (hC : Convex ℝ C) (hx : x ∈ C)
    (hCb : C ⊆ ball x ρ) : ContinuousMap.HomotopyEquiv (sphere (0 : E) 1) ↥Cᶜ where
  toFun := sphereToCompl C x ρ hCb
  invFun := complToSphere C x hx
  left_inv := by
    have hρ := pos_of_subset_ball hx hCb
    have : (complToSphere C x hx).comp (sphereToCompl C x ρ hCb) = ContinuousMap.id _ := by
      ext u
      simp only [complToSphere, sphereToCompl, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
        add_sub_cancel_left, norm_smul, norm_eq_of_mem_sphere u, mul_one, Real.norm_eq_abs,
        abs_of_pos hρ, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul, ContinuousMap.id_apply]
    rw [this]
  right_inv := by
    have hd : Continuous fun p : unitInterval × ↥Cᶜ => ρ / ‖(p.2 : E) - x‖ :=
      continuous_const.div (by fun_prop) fun p => (norm_sub_pos_of_notMem hx p.2.2).ne'
    refine ⟨{ toFun := fun p => ⟨x + ((1 - (p.1 : ℝ)) * (ρ / ‖(p.2 : E) - x‖) + p.1) •
                ((p.2 : E) - x), add_smul_sub_notMem hC hx hCb p.2.2 p.1.2.1 p.1.2.2⟩
              continuous_toFun := Continuous.subtype_mk (by fun_prop) _
              map_zero_left := fun z => ?_
              map_one_left := fun z => ?_ }⟩
    · apply Subtype.ext
      simp [sphereToCompl, complToSphere, smul_smul, div_eq_mul_inv]
    · apply Subtype.ext
      simp

end SphereEquiv

section ZeroDegree

variable {R : Type} [CommRing R]

/-- `H_0(X | L) = 0` for `X` path-connected and `L ≠ X`. -/
theorem isZero_relH_zero (X : TopCat.{0}) [PathConnectedSpace X] {L : Set X}
    (hL : Lᶜ.Nonempty) : IsZero (relH R X L 0) := by
  obtain ⟨a, ha⟩ := hL
  let P := TopPair.ofSubset (X := X) Lᶜ
  let a' : P.snd := ⟨a, ha⟩
  have : PathConnectedSpace P.fst := ‹PathConnectedSpace X›
  let f := ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) 0).obj
      (coef R)).map P.map
  have hεA : Epi (P.snd.singularHomology₀ε (coef R)) :=
    epi_of_epi_fac (TauCeti.singularHomology₀Section_singularHomology₀ε (coef R) a')
  have hfε : f ≫ P.fst.singularHomology₀ε (coef R) = P.snd.singularHomology₀ε (coef R) := by
    exact TauCeti.singularHomologyMap_singularHomology₀ε (coef R) P.map
  have hf : Epi f := by
    have : Epi (f ≫ P.fst.singularHomology₀ε (coef R)) := by rw [hfε]; exact hεA
    have h2 : f = (f ≫ P.fst.singularHomology₀ε (coef R)) ≫ inv (P.fst.singularHomology₀ε (coef R)) := by
      simp
    rw [h2]; exact epi_comp _ _
  have hπ : P.singularHomologyπ (coef R) 0 = 0 :=
    zero_of_epi_comp f (show f ≫ P.singularHomologyπ (coef R) 0 = 0 from
      P.homologyMap_comp_singularHomologyπ (coef R) 0)
  have : Epi (0 : (TopPair.toSSetPair.obj P).right.homology (coef R) 0 ⟶ relH R X L 0) := by
    rw [← hπ]; infer_instance
  exact IsZero.of_epi_zero ((TopPair.toSSetPair.obj P).right.homology (coef R) 0) _

end ZeroDegree

section Convex

variable (R : Type) [CommRing R] (m : ℕ)

local notation "𝔼" => EuclideanSpace ℝ (Fin (m + 1))

/-- `H_{k+1}(𝔼 | L) ≅ H̃_k(𝔼 ∖ L)`, by the connecting map (`𝔼` is contractible). -/
noncomputable def relHSuccIsoReduced (L : Set 𝔼) (k : ℕ) :
    relH R (TopCat.of 𝔼) L (k + 1) ≅
      (TauCeti.reducedSingularHomologyFunctor (coef R) k).obj (TopCat.of ↥Lᶜ) :=
  have : ContractibleSpace (TopPair.ofSubset (X := TopCat.of 𝔼) Lᶜ).fst :=
    (inferInstance : ContractibleSpace 𝔼)
  @asIso _ _ _ _ ((TopPair.ofSubset (X := TopCat.of 𝔼) Lᶜ).reducedSingularHomologyδ (coef R) k)
    (TopPair.isIso_reducedSingularHomologyδ_of_contractibleSpace _ (coef R) k)

lemma relHSuccIsoReduced_hom (L : Set 𝔼) (k : ℕ) :
    (relHSuccIsoReduced R m L k).hom =
      (TopPair.ofSubset (X := TopCat.of 𝔼) Lᶜ).reducedSingularHomologyδ (coef R) k := rfl

variable {R m}

/-- The inclusion `X ∖ L ⟶ X ∖ L'` for `L' ⊆ L`. -/
abbrev complIncl {X : TopCat.{0}} {L L' : Set X} (h : L' ⊆ L) :
    TopCat.of ↥Lᶜ ⟶ TopCat.of ↥L'ᶜ :=
  TopCat.ofHom (ContinuousMap.inclusion (Set.compl_subset_compl.2 h))

lemma relHSuccIsoReduced_naturality {L L' : Set 𝔼} (h : L' ⊆ L) (k : ℕ) :
    res R h (k + 1) ≫ (relHSuccIsoReduced R m L' k).hom =
      (relHSuccIsoReduced R m L k).hom ≫
        (TauCeti.reducedSingularHomologyFunctor (coef R) k).map
          (complIncl (X := TopCat.of 𝔼) h) :=
  (TopPair.reducedSingularHomologyδ_naturality (coef R)
    (TopPair.ofSubsetMap (𝟙 (TopCat.of 𝔼)) (mapsTo_compl_of _ fun _ hx => h hx)) k).symm

lemma hom_snd_ofSubsetMap_id {X : TopCat.{0}} {L L' : Set X} (h : L' ⊆ L) :
    TopPair.Hom.snd (TopPair.ofSubsetMap (𝟙 X) (mapsTo_compl_of _ fun _ hx => h hx)) =
      complIncl h := rfl

lemma compl_nonempty_of_isBounded {L : Set 𝔼} (hL : Bornology.IsBounded L) : Lᶜ.Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at h
  exact NormedSpace.unbounded_univ ℝ 𝔼 (h ▸ hL)

variable (R) in
/-- `H̃_k(S^m) ≅ H̃_k(𝔼 ∖ C)` for `C` convex with `x ∈ C ⊆ ball x ρ`. -/
noncomputable def reducedSphereComplIso {C : Set 𝔼} (hC : Convex ℝ C) {x : 𝔼} (hx : x ∈ C)
    {ρ : ℝ} (hCb : C ⊆ ball x ρ) (k : ℕ) :
    (TauCeti.reducedSingularHomologyFunctor (coef R) k).obj (TopCat.of (sphere (0 : 𝔼) 1)) ≅
      (TauCeti.reducedSingularHomologyFunctor (coef R) k).obj (TopCat.of ↥Cᶜ) :=
  (complConvexHomotopyEquiv hC hx hCb).reducedSingularHomologyIso (coef R) k

lemma reducedSphereComplIso_hom {C : Set 𝔼} (hC : Convex ℝ C) {x : 𝔼} (hx : x ∈ C)
    {ρ : ℝ} (hCb : C ⊆ ball x ρ) (k : ℕ) :
    (reducedSphereComplIso R hC hx hCb k).hom =
      (TauCeti.reducedSingularHomologyFunctor (coef R) k).map
        (TopCat.ofHom (sphereToCompl C x ρ hCb)) := rfl

/-- For convex `C' ⊆ C` sharing a point `x`, with `C ⊆ ball x ρ`, the inclusion
`𝔼 ∖ C ⟶ 𝔼 ∖ C'` induces isomorphisms on reduced homology. -/
lemma isIso_reduced_complIncl {C C' : Set 𝔼} (hC : Convex ℝ C) (hC' : Convex ℝ C') {x : 𝔼}
    (hx : x ∈ C') (h : C' ⊆ C) {ρ : ℝ} (hCb : C ⊆ ball x ρ) (k : ℕ) :
    IsIso ((TauCeti.reducedSingularHomologyFunctor (coef R) k).map
      (complIncl (X := TopCat.of 𝔼) h)) := by
  have hfac : (reducedSphereComplIso R hC (h hx) hCb k).hom ≫
      (TauCeti.reducedSingularHomologyFunctor (coef R) k).map (complIncl (X := TopCat.of 𝔼) h) =
        (reducedSphereComplIso R hC' hx (h.trans hCb) k).hom := by
    rw [reducedSphereComplIso_hom, reducedSphereComplIso_hom, ← Functor.map_comp]
    rfl
  have : IsIso ((reducedSphereComplIso R hC (h hx) hCb k).hom ≫
      (TauCeti.reducedSingularHomologyFunctor (coef R) k).map
        (complIncl (X := TopCat.of 𝔼) h)) := by
    rw [hfac]; infer_instance
  exact IsIso.of_isIso_comp_left (reducedSphereComplIso R hC (h hx) hCb k).hom _

/-- **(E1), vanishing.** For `C` bounded, convex and nonempty, `H_i(𝔼 | C) = 0` for `i ≠ m + 1`. -/
theorem isZero_relH_convex {C : Set 𝔼} (hC : Convex ℝ C) (hb : Bornology.IsBounded C)
    (hne : C.Nonempty) {i : ℕ} (hi : i ≠ m + 1) : IsZero (relH R (TopCat.of 𝔼) C i) := by
  cases i with
  | zero => exact isZero_relH_zero _ (compl_nonempty_of_isBounded hb)
  | succ k =>
    obtain ⟨x, hx⟩ := hne
    obtain ⟨ρ, hρ⟩ := hb.subset_ball x
    have hk : k ≠ m := fun h => hi (by rw [h])
    exact (TauCeti.isZero_reducedSingularHomologyFunctor_sphere_of_ne (coef R)
      finrank_euclideanSpace_fin hk).of_iso
      ((relHSuccIsoReduced R m C k) ≪≫ (reducedSphereComplIso R hC hx hρ k).symm)

/-- **(E1), restriction.** For convex `C' ⊆ C`, `C` bounded and `C'` nonempty, restriction
`H_i(𝔼 | C) ⟶ H_i(𝔼 | C')` is an isomorphism in every degree. -/
theorem isIso_res_convex {C C' : Set 𝔼} (hC : Convex ℝ C) (hC' : Convex ℝ C')
    (hb : Bornology.IsBounded C) (hne : C'.Nonempty) (h : C' ⊆ C) (i : ℕ) :
    IsIso (res R h i : relH R (TopCat.of 𝔼) C i ⟶ _) := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨ρ, hρ⟩ := hb.subset_ball x
  cases i with
  | zero =>
    exact isIso_of_source_target_iso_zero _
      (isZero_relH_zero _ (compl_nonempty_of_isBounded hb)).isoZero
      (isZero_relH_zero _ (compl_nonempty_of_isBounded (hb.subset h))).isoZero
  | succ k =>
    have := isIso_reduced_complIncl (R := R) hC hC' hx h hρ k
    have : IsIso (res R h (k + 1) ≫ (relHSuccIsoReduced R m C' k).hom) := by
      rw [relHSuccIsoReduced_naturality]; infer_instance
    exact IsIso.of_isIso_comp_right _ (relHSuccIsoReduced R m C' k).hom

/-- `H_{m+1}(𝔼 | C) ≅ R` for `C` bounded, convex and nonempty. -/
noncomputable def relHConvexIso {C : Set 𝔼} (hC : Convex ℝ C) (hb : Bornology.IsBounded C)
    (hne : C.Nonempty) : relH R (TopCat.of 𝔼) C (m + 1) ≅ coef R :=
  relHSuccIsoReduced R m C m ≪≫
    (reducedSphereComplIso R hC hne.some_mem (hb.subset_ball hne.some).choose_spec m).symm ≪≫
    TauCeti.reducedSingularHomologySphereIso (coef R) finrank_euclideanSpace_fin

end Convex

section Orientation

variable {R : Type} [CommRing R] {m : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin (m + 1))

/-- Every element of a module isomorphic to `R` is a multiple of the image of `1`. -/
lemma eq_smul_of_iso {M : ModuleCat.{0} R} (ψ : coef R ≅ M) (a : M) :
    a = (ψ.inv a : R) • ψ.hom (1 : R) := by
  rw [← map_smul, smul_eq_mul, mul_one, ← ConcreteCategory.comp_apply, Iso.inv_hom_id,
    ConcreteCategory.id_apply]

lemma iso_hom_one_ne_zero [Nontrivial R] {M : ModuleCat.{0} R} (ψ : coef R ≅ M) :
    ψ.hom (1 : R) ≠ 0 := by
  intro h
  have : ψ.inv (ψ.hom (1 : R)) = (1 : R) := by
    rw [← ConcreteCategory.comp_apply, Iso.hom_inv_id, ConcreteCategory.id_apply]
  rw [h, map_zero] at this
  exact zero_ne_one this

lemma convex_closedBall_nat (N : ℕ) : Convex ℝ (closedBall (0 : 𝔼) N) := convex_closedBall _ _

lemma zero_mem_closedBall_nat (N : ℕ) : (0 : 𝔼) ∈ closedBall (0 : 𝔼) N :=
  mem_closedBall_self (Nat.cast_nonneg N)

lemma singleton_zero_subset_closedBall_nat (N : ℕ) : ({0} : Set 𝔼) ⊆ closedBall (0 : 𝔼) N :=
  Set.singleton_subset_iff.2 (zero_mem_closedBall_nat N)

variable (R m) in
/-- The chosen generator `o₀ ∈ H_{m+1}(𝔼 | 0)`. -/
noncomputable def orientZero : relH R (TopCat.of 𝔼) {0} (m + 1) :=
  (relHConvexIso (convex_singleton (0 : 𝔼)) Bornology.isBounded_singleton
    (Set.singleton_nonempty 0)).inv (1 : R)

variable (R m) in
/-- `ω_N ∈ H_{m+1}(𝔼 | B̄(0, N))`, the unique class restricting to `o₀`. -/
noncomputable def orientBall (N : ℕ) : relH R (TopCat.of 𝔼) (closedBall (0 : 𝔼) N) (m + 1) :=
  have := isIso_res_convex (R := R) (convex_closedBall_nat N) (convex_singleton (0 : 𝔼))
    isBounded_closedBall (Set.singleton_nonempty 0) (singleton_zero_subset_closedBall_nat N) (m + 1)
  inv (res R (singleton_zero_subset_closedBall_nat N) (m + 1)) (orientZero R m)

lemma res_orientBall (N : ℕ) :
    res R (singleton_zero_subset_closedBall_nat N) (m + 1) (orientBall R m N) = orientZero R m := by
  rw [orientBall, ← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply]

lemma res_orientBall_le {N N' : ℕ} (hN : N ≤ N') :
    res R (closedBall_subset_closedBall (Nat.cast_le.2 hN) : closedBall (0 : 𝔼) N ⊆ _) (m + 1)
      (orientBall R m N') = orientBall R m N := by
  have := isIso_res_convex (R := R) (convex_closedBall_nat N) (convex_singleton (0 : 𝔼))
    isBounded_closedBall (Set.singleton_nonempty 0) (singleton_zero_subset_closedBall_nat N) (m + 1)
  apply injective_of_isIso (res R (singleton_zero_subset_closedBall_nat (m := m) N) (m + 1))
  rw [res_orientBall, res_res_apply]
  exact res_orientBall N'

lemma exists_nat_subset_closedBall {L : Set 𝔼} (hL : Bornology.IsBounded L) :
    ∃ N : ℕ, L ⊆ closedBall (0 : 𝔼) N := by
  obtain ⟨r, hr⟩ := hL.subset_closedBall 0
  obtain ⟨N, hN⟩ := exists_nat_ge r
  exact ⟨N, hr.trans (closedBall_subset_closedBall hN)⟩

variable (R m) in
/-- **The orientation class** `o_L ∈ H_{m+1}(𝔼 | L)` of a bounded set `L`: the restriction of
`ω_N` for any `N` with `L ⊆ B̄(0, N)`. It is `0` (a junk value) for unbounded `L`. -/
noncomputable def orient (L : Set 𝔼) : relH R (TopCat.of 𝔼) L (m + 1) := by
  classical
  exact if hL : Bornology.IsBounded L then
    res R (Nat.find_spec (exists_nat_subset_closedBall hL)) (m + 1)
      (orientBall R m (Nat.find (exists_nat_subset_closedBall hL)))
  else 0

/-- `o_L` is the restriction of `ω_N` for every `N` with `L ⊆ B̄(0, N)`. -/
lemma orient_eq_res {L : Set 𝔼} {N : ℕ} (hN : L ⊆ closedBall (0 : 𝔼) N) :
    orient R m L = res R hN (m + 1) (orientBall R m N) := by
  classical
  have hL : Bornology.IsBounded L := isBounded_closedBall.subset hN
  have hle : Nat.find (exists_nat_subset_closedBall hL) ≤ N := Nat.find_min' _ hN
  rw [orient, dite_eq_left hL, ← res_orientBall_le hle, res_res_apply]

/-- `res o_L = o_{L'}` for `L' ⊆ L`, `L` bounded. -/
theorem res_orient {L L' : Set 𝔼} (hL : Bornology.IsBounded L) (h : L' ⊆ L) :
    res R h (m + 1) (orient R m L) = orient R m L' := by
  obtain ⟨N, hN⟩ := exists_nat_subset_closedBall hL
  rw [orient_eq_res hN, orient_eq_res (h.trans hN), res_res_apply]

/-- For `C` bounded, convex and nonempty, `H_{m+1}(𝔼 | C) ≅ R` with `1 ↦ o_C`. -/
noncomputable def orientIso {C : Set 𝔼} (hC : Convex ℝ C) (hb : Bornology.IsBounded C)
    (hne : C.Nonempty) : coef R ≅ relH R (TopCat.of 𝔼) C (m + 1) := by
  let N := (exists_nat_subset_closedBall hb).choose
  have hN : C ⊆ closedBall (0 : 𝔼) N := (exists_nat_subset_closedBall hb).choose_spec
  have h0 := isIso_res_convex (R := R) (convex_closedBall_nat N) (convex_singleton (0 : 𝔼))
    isBounded_closedBall (Set.singleton_nonempty 0) (singleton_zero_subset_closedBall_nat N) (m + 1)
  have hC' := isIso_res_convex (R := R) (convex_closedBall_nat N) hC isBounded_closedBall hne hN
    (m + 1)
  exact (relHConvexIso (convex_singleton (0 : 𝔼)) Bornology.isBounded_singleton
    (Set.singleton_nonempty 0)).symm ≪≫
    (asIso (res R (singleton_zero_subset_closedBall_nat N) (m + 1))).symm ≪≫
    asIso (res R hN (m + 1))

lemma orientIso_hom_one {C : Set 𝔼} (hC : Convex ℝ C) (hb : Bornology.IsBounded C)
    (hne : C.Nonempty) : (orientIso (R := R) hC hb hne).hom (1 : R) = orient R m C := by
  rw [orient_eq_res (exists_nat_subset_closedBall hb).choose_spec]
  rfl

/-- **(E2)** Every class in `H_{m+1}(𝔼 | C)`, `C` bounded convex nonempty, is a multiple of
`o_C`. -/
theorem exists_eq_smul_orient_convex {C : Set 𝔼} (hC : Convex ℝ C) (hb : Bornology.IsBounded C)
    (hne : C.Nonempty) (α : relH R (TopCat.of 𝔼) C (m + 1)) : ∃ c : R, α = c • orient R m C :=
  ⟨_, (eq_smul_of_iso (orientIso hC hb hne) α).trans (by rw [orientIso_hom_one])⟩

/-- `o_C ≠ 0` for `C` bounded convex nonempty (over a nontrivial ring). -/
theorem orient_convex_ne_zero [Nontrivial R] {C : Set 𝔼} (hC : Convex ℝ C)
    (hb : Bornology.IsBounded C) (hne : C.Nonempty) : orient R m C ≠ 0 := by
  rw [← orientIso_hom_one hC hb hne]
  exact iso_hom_one_ne_zero _

/-- `c • o_C = 0` forces `c = 0`, for `C` bounded convex nonempty. -/
theorem smul_orient_eq_zero_iff {C : Set 𝔼} (hC : Convex ℝ C) (hb : Bornology.IsBounded C)
    (hne : C.Nonempty) (c : R) : c • orient R m C = 0 ↔ c = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, zero_smul]⟩
  have := congrArg (orientIso (R := R) hC hb hne).inv h
  rw [← orientIso_hom_one hC hb hne, ← map_smul, ← ConcreteCategory.comp_apply, Iso.hom_inv_id,
    ConcreteCategory.id_apply, map_zero, smul_eq_mul, mul_one] at this
  exact this

theorem orient_point_ne_zero [Nontrivial R] (x : 𝔼) : orient R m {x} ≠ 0 :=
  orient_convex_ne_zero (convex_singleton x) Bornology.isBounded_singleton
    (Set.singleton_nonempty x)

end Orientation

section FiniteUnions

variable {R : Type} [CommRing R] {m : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin (m + 1))

/-- `V` for a bounded convex set. -/
theorem vanishAbove_convex {C : Set 𝔼} (hC : Convex ℝ C) (hb : Bornology.IsBounded C) :
    VanishAbove R (TopCat.of 𝔼) C (m + 1) := by
  rcases C.eq_empty_or_nonempty with rfl | hne
  · exact vanishAbove_empty _
  · exact fun i hi => isZero_relH_convex hC hb hne (by omega)

/-- `P` for a bounded convex set. -/
theorem pointInj_convex {C : Set 𝔼} (hC : Convex ℝ C) (hb : Bornology.IsBounded C) :
    PointInj R (TopCat.of 𝔼) C (m + 1) := by
  rcases C.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact pointInj_empty _
  · intro α hα
    have := isIso_res_convex (R := R) hC (convex_singleton x) hb (Set.singleton_nonempty x)
      (Set.singleton_subset_iff.2 hx) (m + 1)
    exact injective_of_isIso _ ((hα x hx).trans (map_zero _).symm)

/-- **(E3)** `V` and `P` for finite unions of compact convex sets in `𝔼`. -/
theorem vanishAbove_pointInj_biUnion (S : Finset (Set 𝔼))
    (hS : ∀ s ∈ S, Convex ℝ s ∧ IsCompact s) :
    VanishAbove R (TopCat.of 𝔼) (⋃ s ∈ S, s) (m + 1) ∧
      PointInj R (TopCat.of 𝔼) (⋃ s ∈ S, s) (m + 1) := by
  classical
  suffices H : ∀ n : ℕ, ∀ S : Finset (Set 𝔼), S.card ≤ n → (∀ s ∈ S, Convex ℝ s ∧ IsCompact s) →
      VanishAbove R (TopCat.of 𝔼) (⋃ s ∈ S, s) (m + 1) ∧
        PointInj R (TopCat.of 𝔼) (⋃ s ∈ S, s) (m + 1) from H _ S le_rfl hS
  intro n
  induction n with
  | zero =>
    intro S hS _
    rw [Finset.card_eq_zero.1 (Nat.le_zero.1 hS)]
    simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty]
    exact ⟨vanishAbove_empty _, pointInj_empty _⟩
  | succ n ih =>
    intro S hcard hS
    rcases S.eq_empty_or_nonempty with rfl | ⟨t, ht⟩
    · simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty]
      exact ⟨vanishAbove_empty _, pointInj_empty _⟩
    set S' := S.erase t with hS'
    have hcard' : S'.card ≤ n := by
      rw [Finset.card_erase_of_mem ht]; omega
    have hS'' : ∀ s ∈ S', Convex ℝ s ∧ IsCompact s := fun s hs => hS s (Finset.mem_of_mem_erase hs)
    have hU : (⋃ s ∈ S, s) = t ∪ ⋃ s ∈ S', s := by
      have := Finset.set_biUnion_insert t S' (fun s => s)
      rw [hS', Finset.insert_erase ht] at this
      exact this
    have hI : t ∩ (⋃ s ∈ S', s) = ⋃ s ∈ S'.image (fun s => t ∩ s), s := by
      rw [Finset.set_biUnion_finset_image, Set.inter_iUnion₂]
    have hIcard : (S'.image (fun s => t ∩ s)).card ≤ n :=
      Finset.card_image_le.trans hcard'
    have hIS : ∀ s ∈ S'.image (fun s => t ∩ s), Convex ℝ s ∧ IsCompact s := by
      intro s hs
      obtain ⟨s', hs', rfl⟩ := Finset.mem_image.1 hs
      exact ⟨(hS t ht).1.inter (hS'' s' hs').1, (hS t ht).2.inter_right (hS'' s' hs').2.isClosed⟩
    obtain ⟨hV', hP'⟩ := ih S' hcard' hS''
    obtain ⟨hVI, -⟩ := ih _ hIcard hIS
    rw [← hI] at hVI
    have htc : IsClosed t := (hS t ht).2.isClosed
    have hUc : IsClosed (⋃ s ∈ S', s) :=
      isClosed_biUnion_finset fun s hs => (hS'' s hs).2.isClosed
    have hVt := vanishAbove_convex (R := R) (hS t ht).1 (hS t ht).2.isBounded
    have hPt := pointInj_convex (R := R) (hS t ht).1 (hS t ht).2.isBounded
    rw [hU]
    exact ⟨hVt.union htc hUc hV' hVI, hPt.union htc hUc hP' (hVI _ (by omega))⟩

end FiniteUnions

end HSFormal.Newman
