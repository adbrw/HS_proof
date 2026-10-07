import HSFormal.LTheory.Interface
import HSFormal.Integration

/-!
# The point category `V_G = ∏ᵢ Free(ℚ[Gᵢ]) / ⊕ᵢ Free(ℚ[Gᵢ])` (manuscript (3.3)–(3.5))

* `finSuppFiltration G`: the finite-support subcategory `⊕ᵢ Free(ℚ[Gᵢ]) ⊂ ∏ᵢ Free(ℚ[Gᵢ])` is a
  Karoubi filtration (manuscript l. 156), split at the initial index segments; its `sub` is
  `finSuppFreeQG G univ`.
* `pointIso G π`: its quotient is isomorphic (strictly, as `InvCat`s) to `𝒜_G(pt) =
  asymptoticInvCat π PUnit` for every `π : Gᵢ →* H` (H-change included), since a map factors
  through a finite-support object iff it is eventually zero; `LowerLTheory.pointEquiv` is the
  induced isomorphism of L-groups and `toPoint G π : ∏ → V_G` the projection.
* `LowerLTheory.finSupp_incl_injective`: `L_n(⊕) → L_n(∏)` is injective for `n ≥ 0`, through the
  coordinate projections `evalQG i` and `dec_bij` (blueprint s04-06, E8; design I3).  Hence every
  class of `L_{n+1}(V_G)` lifts to `L_{n+1}(∏)` (`toPoint_surjective`), uniquely modulo the image
  of `L_{n+1}(⊕)` (`toPoint_eq_toPoint_iff`).
* `LowerLTheory.tail`: the resulting homomorphism `L_{n+1}(V_G) → ∏ᵢ L^p_{n+1}(ℚ[Gᵢ]) / ⊕`
  (Prop. 3.2 in the form used by Theorem 6.3 and §12), computed by the coordinates
  `LowerLTheory.coord` of any lift (`tail_toPoint`, `tail_cls`), natural for index-wise functors
  (`tail_natural`), in particular for forgetting the group (`tail_forget`) and H-change
  (`tail_pointChange`).

The full isomorphism (3.4) needs the product theorem for `L(∏ᵢ Free(ℚ[Gᵢ]))`, which is not used.
-/

/-! ### Index-wise restriction in the prequotient -/

namespace HSFormal.AsymptoticObject

open CategoryTheory Category Limits

noncomputable section

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  {π : ∀ i, G i →* H} {X : Type} [MulAction H X] [PseudoEMetricSpace X]
  {M N : AsymptoticObject π X} {s t : Set ℕ}

open scoped Classical

/-- The central idempotent keeping the indices in `s`. -/
abbrev idxProj (M : AsymptoticObject π X) (s : Set ℕ) : M ⟶ M := M.diagProj fun j _ ↦ j ∈ s

lemma idxProj_val (M : AsymptoticObject π X) (s : Set ℕ) (j : ℕ) :
    (M.idxProj s).1 j = if j ∈ s then 1 else 0 := by
  by_cases h : j ∈ s <;> simp [h]

lemma idxProj_comm (f : M ⟶ N) (s : Set ℕ) : M.idxProj s ≫ f = f ≫ N.idxProj s :=
  hom_ext fun j ↦ by by_cases h : j ∈ s <;> simp [h]

lemma idxProj_idemLE (M : AsymptoticObject π X) (h : s ⊆ t) :
    IdemLE (M.idxProj s) (M.idxProj t) :=
  M.diagProj_comp_diagProj _ _ fun _ _ hj ↦ h hj

lemma idxProj_add_compl (M : AsymptoticObject π X) (s : Set ℕ) :
    M.idxProj s + M.idxProj sᶜ = 𝟙 M :=
  hom_ext fun j ↦ by by_cases h : j ∈ s <;> simp [h]

lemma sum_idxProj (M : AsymptoticObject π X) (S : Finset ℕ) :
    ∑ i ∈ S, M.idxProj {i} = M.idxProj ↑S := by
  induction S using Finset.induction_on with
  | empty => exact hom_ext fun j ↦ by simp
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, ih]
    refine hom_ext fun j ↦ ?_
    rcases eq_or_ne j a with rfl | h
    · simp [ha]
    · simp [h]

/-- The based summand on the indices in `s`. -/
abbrev idxRestrict (M : AsymptoticObject π X) (s : Set ℕ) : AsymptoticObject π X :=
  M.restrict fun j _ ↦ j ∈ s

/-- Its orbit embedding. -/
abbrev idxEmb (M : AsymptoticObject π X) (s : Set ℕ) : OrbitEmbedding (M.idxRestrict s) M :=
  M.restrictEmb _

lemma idxEmb_proj_incl (M : AsymptoticObject π X) (s : Set ℕ) :
    (M.idxEmb s).proj ≫ (M.idxEmb s).incl = M.idxProj s :=
  M.restrict_proj_incl _

omit [MulAction H X] [PseudoEMetricSpace X] [∀ i, Fintype (G i)] in
lemma idxRestrict_rank_le (M : AsymptoticObject π X) (s : Set ℕ) (j : ℕ) :
    (M.idxRestrict s).rank j ≤ M.rank j := by
  change Fintype.card {k : Fin (M.rank j) // j ∈ s} ≤ _
  exact (Fintype.card_subtype_le _).trans (Fintype.card_fin _).le

omit [MulAction H X] [PseudoEMetricSpace X] [∀ i, Fintype (G i)] in
lemma idxRestrict_rank_eq_zero (M : AsymptoticObject π X) {j : ℕ} (h : j ∉ s) :
    (M.idxRestrict s).rank j = 0 := by
  change Fintype.card {k : Fin (M.rank j) // j ∈ s} = 0
  exact Fintype.card_eq_zero_iff.mpr ⟨fun k ↦ h k.2⟩

lemma rank_eq_zero_of_idxProj (h : M.idxProj s = 𝟙 M) {j : ℕ} (hj : j ∉ s) : M.rank j = 0 := by
  by_contra hM
  have : Nonempty (Fin (M.rank j)) := ⟨⟨0, by omega⟩⟩
  have := congrArg (fun f : M ⟶ M ↦ f.1 j) h
  simp only [idxProj_val, hj, ite_false, id_val] at this
  exact one_ne_zero this.symm

lemma idxProj_eq_id (h : ∀ j ∉ s, M.rank j = 0) : M.idxProj s = 𝟙 M :=
  hom_ext fun j ↦ by
    by_cases hj : j ∈ s
    · simp [hj]
    · ext a; have := a.1.2; have := h j hj; omega

lemma idxEmb_incl_proj_eq_zero (M : AsymptoticObject π X) (h : Disjoint s t) :
    (M.idxEmb s).incl ≫ (M.idxEmb t).proj = 0 :=
  OrbitEmbedding.incl_proj_eq_zero _ _ fun j k k' hk ↦ by
    have h₁ := (M.mem_range_restrictEmb (fun j _ ↦ j ∈ s) j _).mp ⟨k, rfl⟩
    have h₂ := (M.mem_range_restrictEmb (fun j _ ↦ j ∈ t) j _).mp ⟨k', hk.symm⟩
    exact h.ne_of_mem h₁ h₂ rfl

end

end HSFormal.AsymptoticObject

namespace HSFormal.LTheory

open CategoryTheory Category Limits HSFormal.Compression Filter

noncomputable section

/-! ### Consequences of the localization sequence -/

namespace LowerLTheory

variable (𝕃 : LowerLTheory) {A : InvCat} (F : KaroubiFiltration A) {n : ℤ}

lemma map_map {B C : InvCat} (Φ : A ⟶ B) (Ψ : B ⟶ C) (x : 𝕃.L A n) :
    𝕃.map Ψ n (𝕃.map Φ n x) = 𝕃.map (Φ ≫ Ψ) n x := by
  rw [𝕃.map_comp]
  rfl

lemma bdry_eq_zero_of_injective (h : Function.Injective (𝕃.map F.incl n))
    (x : 𝕃.L F.quot (n + 1)) : 𝕃.bdry F n x = 0 :=
  h (by rw [incl_bdry, map_zero])

lemma proj_surjective_of_injective (h : Function.Injective (𝕃.map F.incl n)) :
    Function.Surjective (𝕃.map F.proj (n + 1)) :=
  fun x ↦ (𝕃.exact_Q F n x).mp (𝕃.bdry_eq_zero_of_injective F h x)

lemma proj_eq_proj_iff {y y' : 𝕃.L A n} :
    𝕃.map F.proj n y = 𝕃.map F.proj n y' ↔ y - y' ∈ (𝕃.map F.incl n).range := by
  rw [← sub_eq_zero, ← map_sub, 𝕃.exact_A F n]
  rfl

/-- A homomorphism on `L_{n+1}(A)` killing `L_{n+1}(U)` descends to `L_{n+1}(A/U)` when
`L_n(U) → L_n(A)` is injective. -/
def quotLift (h : Function.Injective (𝕃.map F.incl n)) {Q : Type*} [AddCommGroup Q]
    (c : 𝕃.L A (n + 1) →+ Q) (hc : ∀ x, c (𝕃.map F.incl (n + 1) x) = 0) :
    𝕃.L F.quot (n + 1) →+ Q :=
  (QuotientAddGroup.lift _ c fun y hy ↦ by
      obtain ⟨x, rfl⟩ := (𝕃.exact_A F (n + 1) y).mp hy
      exact hc x).comp
    (QuotientAddGroup.quotientKerEquivOfSurjective _
      (𝕃.proj_surjective_of_injective F h)).symm.toAddMonoidHom

@[simp]
lemma quotLift_proj (h : Function.Injective (𝕃.map F.incl n)) {Q : Type*} [AddCommGroup Q]
    (c : 𝕃.L A (n + 1) →+ Q) (hc : ∀ x, c (𝕃.map F.incl (n + 1) x) = 0) (y : 𝕃.L A (n + 1)) :
    𝕃.quotLift F h c hc (𝕃.map F.proj (n + 1) y) = c y := by
  have : (QuotientAddGroup.quotientKerEquivOfSurjective _
      (𝕃.proj_surjective_of_injective F h)).symm (𝕃.map F.proj (n + 1) y) = (y : _ ⧸ _) :=
    (AddEquiv.symm_apply_eq _).mpr rfl
  simp [quotLift, this]

end LowerLTheory

/-! ### Index-wise summands in `∏ᵢ Free(ℚ[Gᵢ])` -/

namespace FreeQG

open AsymptoticObject

variable {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)] {M N : prodFreeQG G}
  {s t : Set ℕ}

/-- The based summand of `M` on the indices in `s`. -/
abbrev res (M : prodFreeQG G) (s : Set ℕ) : prodFreeQG G := M.idxRestrict s

/-- The inclusion of `res M s`. -/
def inc (M : prodFreeQG G) (s : Set ℕ) : res M s ⟶ M := (M.idxEmb s).incl

/-- The projection onto `res M s`. -/
def prj (M : prodFreeQG G) (s : Set ℕ) : M ⟶ res M s := (M.idxEmb s).proj

/-- The central idempotent `prj ≫ inc`. -/
def idem (M : prodFreeQG G) (s : Set ℕ) : M ⟶ M := M.idxProj s

open scoped Classical in
lemma idem_val (M : prodFreeQG G) (s : Set ℕ) (j : ℕ) :
    (idem M s).1 j = if j ∈ s then 1 else 0 :=
  idxProj_val M s j

@[reassoc (attr := simp)]
lemma inc_prj : inc M s ≫ prj M s = 𝟙 _ := OrbitEmbedding.incl_proj _

@[reassoc (attr := simp)]
lemma prj_inc : prj M s ≫ inc M s = idem M s := idxEmb_proj_incl M s

@[reassoc]
lemma idem_comm (f : M ⟶ N) (s : Set ℕ) : idem M s ≫ f = f ≫ idem N s := idxProj_comm f s

@[simp] lemma star_inc : (prodFreeQG G).inv.star (inc M s) = prj M s := rfl

@[simp] lemma star_prj : (prodFreeQG G).inv.star (prj M s) = inc M s :=
  OrbitEmbedding.transpose_proj _

@[reassoc (attr := simp)]
lemma inc_idem : inc M s ≫ idem M s = inc M s := by rw [← prj_inc, inc_prj_assoc]

@[reassoc (attr := simp)]
lemma idem_prj : idem M s ≫ prj M s = prj M s := by rw [← prj_inc, assoc, inc_prj, comp_id]

lemma idem_idemLE (h : s ⊆ t) : IdemLE (idem M s) (idem M t) := idxProj_idemLE M h

lemma idem_add_compl : idem M s + idem M sᶜ = 𝟙 M := idxProj_add_compl M s

lemma idem_eq_id (h : ∀ j ∉ s, M.rank j = 0) : idem M s = 𝟙 M := idxProj_eq_id h

lemma rank_eq_zero_of_idem (h : idem M s = 𝟙 M) {j : ℕ} (hj : j ∉ s) : M.rank j = 0 :=
  rank_eq_zero_of_idxProj h hj

lemma inc_prj_eq_zero (h : Disjoint s t) : inc M s ≫ prj M t = 0 :=
  idxEmb_incl_proj_eq_zero M h

lemma sum_idem (S : Finset ℕ) : ∑ i ∈ S, idem M {i} = idem M ↑S := sum_idxProj M S

/-- The splitting `M = M|_s ⊕ M|_{sᶜ}`. -/
def splitting (M : prodFreeQG G) (s : Set ℕ) : Splitting M where
  E := res M s
  U := res M sᶜ
  ιE := inc M s
  πE := prj M s
  ιU := inc M sᶜ
  πU := prj M sᶜ
  ιE_πE := inc_prj
  ιU_πU := inc_prj
  ιE_πU := inc_prj_eq_zero disjoint_compl_right
  ιU_πE := inc_prj_eq_zero disjoint_compl_left
  total := by rw [prj_inc, prj_inc, idem_add_compl]

@[simp] lemma splitting_idem : (splitting M s).idem = idem M s := prj_inc

end FreeQG

/-! ### `⊕ᵢ Free(ℚ[Gᵢ]) ⊂ ∏ᵢ Free(ℚ[Gᵢ])` is a Karoubi filtration -/

section FinSupp

open AsymptoticObject FreeQG

variable {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]

lemma finSuppIn_iff_eventually {M : prodFreeQG G} :
    finSuppIn G Set.univ M ↔ ∃ m, ∀ j, m ≤ j → M.rank j = 0 := by
  refine ⟨fun h ↦ ?_, fun ⟨m, hm⟩ ↦ ⟨(Set.finite_Iio m).subset fun j hj ↦ ?_, fun _ h ↦
    absurd (Set.mem_univ _) h⟩⟩
  · obtain ⟨m, hm⟩ := h.1.bddAbove
    exact ⟨m + 1, fun j hj ↦ by_contra fun h' ↦ by have := hm h'; omega⟩
  · by_contra h'
    exact hj (hm j (not_lt.mp h'))

lemma finSuppIn_res (M : prodFreeQG G) (m : ℕ) : finSuppIn G Set.univ (res M (Set.Iio m)) :=
  finSuppIn_iff_eventually.mpr ⟨m, fun _ hj ↦ idxRestrict_rank_eq_zero M (by simpa using hj)⟩

variable (G) in
/-- **Manuscript l. 156**: the finite-support subcategory is a Karoubi filtration, split at the
initial index segments `[0, m)`; the splittings are fixed by transpose. -/
def finSuppFiltration : KaroubiFiltration (prodFreeQG G) where
  U := finSuppIn G Set.univ
  filt :=
    { splittings M := Set.range fun m : ℕ ↦ splitting M (Set.Iio m)
      mem := by
        rintro M _ ⟨m, rfl⟩
        exact finSuppIn_res M m
      nonempty M := ⟨_, 0, rfl⟩
      directed := by
        rintro M _ ⟨m, rfl⟩ _ ⟨m', rfl⟩
        refine ⟨_, ⟨max m m', rfl⟩, ?_, ?_⟩ <;> rw [splitting_idem, splitting_idem]
        · exact idem_idemLE (Set.Iio_subset_Iio (le_max_left _ _))
        · exact idem_idemLE (Set.Iio_subset_Iio (le_max_right _ _))
      factor_to := by
        intro V M hV f
        obtain ⟨m, hm⟩ := finSuppIn_iff_eventually.mp hV
        refine ⟨_, ⟨m, rfl⟩, f ≫ prj M (Set.Iio m), ?_⟩
        change f = (f ≫ prj M _) ≫ inc M _
        rw [assoc, prj_inc, ← idem_comm, idem_eq_id fun j hj ↦ hm j (by simpa using hj), id_comp]
      factor_from := by
        intro M V hV f
        obtain ⟨m, hm⟩ := finSuppIn_iff_eventually.mp hV
        refine ⟨_, ⟨m, rfl⟩, inc M (Set.Iio m) ≫ f, ?_⟩
        change f = prj M _ ≫ inc M _ ≫ f
        rw [prj_inc_assoc, idem_comm, idem_eq_id fun j hj ↦ hm j (by simpa using hj), comp_id]
      sum := by
        intro M M' b hb
        have key (s t : Set ℕ) : b.fst ≫ (splitting M s).idem ≫ b.inl +
            b.snd ≫ (splitting M' t).idem ≫ b.inr =
              idem b.pt s ≫ b.fst ≫ b.inl + idem b.pt t ≫ b.snd ≫ b.inr := by
          rw [splitting_idem, splitting_idem, ← idem_comm_assoc b.fst, ← idem_comm_assoc b.snd]
        have htot := IsBilimit.binary_total hb
        constructor
        · rintro _ ⟨m, rfl⟩
          refine ⟨_, ⟨m, rfl⟩, _, ⟨m, rfl⟩, ?_⟩
          rw [key, ← Preadditive.comp_add, htot, comp_id, splitting_idem]
          exact idem_idemLE le_rfl
        · rintro _ ⟨m, rfl⟩ _ ⟨m', rfl⟩
          refine ⟨_, ⟨max m m', rfl⟩, ?_⟩
          rw [key, splitting_idem]
          have h₁ := idem_idemLE (M := b.pt) (Set.Iio_subset_Iio (le_max_left m m'))
          have h₂ := idem_idemLE (M := b.pt) (Set.Iio_subset_Iio (le_max_right m m'))
          constructor
          · rw [Preadditive.add_comp, assoc, assoc, assoc, assoc, ← idem_comm b.inl,
              ← idem_comm b.inr, ← idem_comm_assoc b.fst, ← idem_comm_assoc b.snd,
              reassoc_of% h₁.1, reassoc_of% h₂.1]
          · rw [Preadditive.comp_add, reassoc_of% h₁.2, reassoc_of% h₂.2] }
  star_ιE := by rintro M _ ⟨m, rfl⟩; exact star_inc
  star_ιU := by rintro M _ ⟨m, rfl⟩; exact star_inc

lemma finSuppFiltration_sub : (finSuppFiltration G).sub = finSuppFreeQG G Set.univ := rfl

end FinSupp

/-! ### `∏/⊕` is the asymptotic category over a point -/

section Point

open AsymptoticObject AsymptoticCategory FreeQG

variable {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  {H : Type*} [Group H] {H' : Type*} [Group H']

lemma prop_punit {A B : Type*} (u : Matrix B A ℚ) (s : A → PUnit) (t : B → PUnit) :
    prop u s t = 0 :=
  le_antisymm (prop_le_iff.mpr fun _ _ _ ↦ by simp) bot_le

variable (π : ∀ i, G i →* H) (π' : ∀ i, G i →* H')

/-- Over a point the control condition is vacuous, so `π` can be changed (H-change). -/
@[simps]
def pointChangeFunctor : AsymptoticObject π PUnit.{1} ⥤ AsymptoticObject π' PUnit.{1} where
  obj M := ⟨M.rank, M.label⟩
  map f := ⟨f.1, ⟨AsymptoticObject.equivariant f,
    tendsto_zero_of_forall_eq_zero fun _ ↦ prop_punit _ _ _⟩⟩

lemma factorsThrough_finSupp_iff {M N : prodFreeQG G} (f : M ⟶ N) :
    FactorsThrough (finSuppIn G Set.univ) f ↔ ∀ᶠ j in atTop, f.1 j = 0 := by
  constructor
  · rintro ⟨W, hW, u, v, rfl⟩
    obtain ⟨m, hm⟩ := finSuppIn_iff_eventually.mp hW
    exact eventually_atTop.mpr ⟨m, fun j hj ↦ by
      erw [AsymptoticObject.comp_val]; exact mul_eq_zero_of_rank (hm j hj) _ _⟩
  · intro h
    obtain ⟨m, hm⟩ := eventually_atTop.mp h
    have : f = (f ≫ prj N (Set.Iio m)) ≫ inc N (Set.Iio m) := by
      rw [assoc, prj_inc]
      refine AsymptoticObject.hom_ext fun j ↦ ?_
      erw [AsymptoticObject.comp_val, idem_val]
      by_cases hj : j < m
      · simp [hj]
      · simp [hj, hm j (not_lt.mp hj)]
    rw [this]
    exact FactorsThrough.of_mem (finSuppIn_res N m) _ _

lemma factorRel_finSupp_iff {M N : prodFreeQG G} (f g : M ⟶ N) :
    factorRel (finSuppIn G Set.univ) f g ↔ ∀ᶠ j in atTop, f.1 j = g.1 j := by
  refine (factorsThrough_finSupp_iff _).trans (eventually_congr (.of_forall fun j ↦ ?_))
  erw [AsymptoticObject.sub_val, sub_eq_zero]

variable (G) in
/-- **(3.3)**: `(∏ᵢ Free(ℚ[Gᵢ]))/(⊕ᵢ Free(ℚ[Gᵢ])) ≅ V_G = 𝒜_G(pt)`, for every `π : Gᵢ →* H`
(H-change included); both are the same matrix sequences modulo eventual equality. -/
def pointIso : (finSuppFiltration G).quot ≅ asymptoticInvCat π PUnit where
  hom :=
    { F := CategoryTheory.Quotient.lift _ (pointChangeFunctor _ π ⋙ functor) fun _ _ f g h ↦
        (functor_map_eq_iff _ _).mpr ((factorRel_finSupp_iff f g).mp h)
      additive := ⟨by rintro _ _ ⟨f⟩ ⟨g⟩; rfl⟩
      map_star := by rintro _ _ ⟨f⟩; rfl }
  inv :=
    { F := CategoryTheory.Quotient.lift _ (pointChangeFunctor π (fun i ↦ (1 : G i →* Unit)) ⋙
          Quotient.functor (factorRel (finSuppIn G Set.univ))) fun _ _ f g h ↦
        (quot_map_eq_iff _ _).mpr ((factorRel_finSupp_iff _ _).mpr h)
      additive := ⟨by rintro _ _ ⟨f⟩ ⟨g⟩; rfl⟩
      map_star := by rintro _ _ ⟨f⟩; rfl }
  hom_inv_id := InvCat.hom_ext (Quotient.lift_unique' _ _ _ rfl)
  inv_hom_id := InvCat.hom_ext (Quotient.lift_unique' _ _ _ rfl)

variable (G) in
/-- `∏ᵢ Free(ℚ[Gᵢ]) → V_G`: a sequence of matrices modulo eventual equality. -/
def toPoint : prodFreeQG G ⟶ asymptoticInvCat π PUnit :=
  (finSuppFiltration G).proj ≫ (pointIso G π).hom

lemma toPoint_map {M N : prodFreeQG G} (f : M ⟶ N) :
    (toPoint G π).F.map f = functor.map ((pointChangeFunctor _ π).map f) := rfl

/-- H-change `𝒜_G(pt) → 𝒜_G(pt)` from `π` to `π'`: the identity on matrices. -/
def pointChange : asymptoticInvCat π PUnit ⟶ asymptoticInvCat π' PUnit :=
  (pointIso G π).inv ≫ (pointIso G π').hom

lemma toPoint_pointChange : toPoint G π ≫ pointChange π π' = toPoint G π' := by
  simp [toPoint, pointChange]

end Point

/-! ### Sums of orthogonal retracts in `Lconc` -/

namespace Lconc

variable {A : InvCat} {N : ℤ}

/-- If the isometric embeddings `incᵢ : Φᵢ ⟶ 𝟙` (`i ∈ s`) are mutually orthogonal and exhaust
`P`, then `[P] = ∑ᵢ Φᵢ [P]`. -/
lemma cls_eq_sum_map {ι : Type*} (s : Finset ι) {Φ : ι → (A ⟶ A)}
    (inc : ∀ i, (Φ i).F ⟶ (𝟙 A : A ⟶ A).F)
    (hself : ∀ i X, (inc i).app X ≫ A.inv.star ((inc i).app X) = 𝟙 _)
    (hne : ∀ i j, i ≠ j → ∀ X, (inc i).app X ≫ A.inv.star ((inc j).app X) = 0)
    (P : SymPoincare A.inv N)
    (htot : ∀ r, P.p.f r ≫ ∑ i ∈ s, A.inv.star ((inc i).app (P.C.X r)) ≫ (inc i).app (P.C.X r) =
      P.p.f r) :
    cls P = ∑ i ∈ s, map (Φ i) (cls P) := by
  classical
  have he i := isReducing_retractIdem P (hself i)
  have horth : ∀ i j, i ≠ j → retractIdem (inc i) P ≫ retractIdem (inc j) P = 0 :=
    fun i j hij ↦ by
      ext
      simp
      erw [NatTrans.comp_app, NatTrans.comp_app]
      simp only [Category.assoc]
      erw [reassoc_of% (hne i j hij), zero_comp, comp_zero]
      rfl
  have hsum : (P.map (𝟙 A : A ⟶ A)).p ≫ ∑ i ∈ s, retractIdem (inc i) P =
      (P.map (𝟙 A : A ⟶ A)).p := by
    ext r : 1
    rw [HomologicalComplex.comp_f, hom_sum_f]
    exact htot r
  change cls (P.map (𝟙 A : A ⟶ A)) = _
  rw [← cls_cut_of_eq _ (SymPoincare.IsReducing.sum s he horth) hsum, cls_cut_sum _ _ _ he horth]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [map_cls, map_retract _ (hself i) P]

end Lconc

/-! ### Coordinate projections and `L_n(⊕) → L_n(∏)` -/

section Coord

open AsymptoticObject FreeQG

variable {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)] {n : ℤ}

lemma finSuppIn_res_singleton (M : prodFreeQG G) (i : ℕ) : finSuppIn G {i} (res M {i}) :=
  ⟨(Set.finite_singleton i).subset fun _ hj ↦ by_contra fun h ↦ hj (idxRestrict_rank_eq_zero M h),
    fun _ hj ↦ idxRestrict_rank_eq_zero M hj⟩

variable (G) in
/-- The coordinate projection `∏ⱼ Free(ℚ[Gⱼ]) → Free(ℚ[Gᵢ])`. -/
@[implicit_reducible] def evalQG (i : ℕ) : prodFreeQG G ⟶ finSuppFreeQG G {i} where
  F :=
    { obj M := ⟨res M {i}, finSuppIn_res_singleton M i⟩
      map {M N} f := ObjectProperty.homMk (inc M {i} ≫ f ≫ prj N {i})
      map_id M := ObjectProperty.hom_ext _ <| by
        change inc M {i} ≫ 𝟙 M ≫ prj M {i} = 𝟙 _
        simp
      map_comp {M N P} f g := ObjectProperty.hom_ext _ <| by
        change inc M {i} ≫ (f ≫ g) ≫ prj P {i} =
          (inc M {i} ≫ f ≫ prj N {i}) ≫ inc N {i} ≫ g ≫ prj P {i}
        rw [assoc, assoc, assoc, prj_inc_assoc, idem_comm_assoc, idem_prj] }
  additive := ⟨fun {M N f g} ↦ ObjectProperty.hom_ext _ <| by
    change inc M {i} ≫ (f + g) ≫ prj N {i} = inc M {i} ≫ f ≫ prj N {i} + inc M {i} ≫ g ≫ prj N {i}
    simp⟩
  map_star f := ObjectProperty.hom_ext _ (by
    change inc _ _ ≫ (prodFreeQG G).inv.star f ≫ prj _ _ =
      (prodFreeQG G).inv.star (inc _ _ ≫ f ≫ prj _ _)
    simp [(prodFreeQG G).inv.star_comp])

@[simp] lemma evalQG_obj (i : ℕ) (M : prodFreeQG G) : ((evalQG G i).F.obj M).obj = res M {i} := rfl

@[simp] lemma evalQG_map_hom (i : ℕ) {M N : prodFreeQG G} (f : M ⟶ N) :
    ((evalQG G i).F.map f).hom = inc M {i} ≫ f ≫ prj N {i} := rfl

variable (G) in
/-- `⊕_{i ∈ T} Free(ℚ[Gᵢ]) ⊂ ⊕_{i ∈ T'} Free(ℚ[Gᵢ])` for `T ⊆ T'`. -/
def finSuppIncl {T T' : Set ℕ} (h : T ⊆ T') : finSuppFreeQG G T ⟶ finSuppFreeQG G T' where
  F := (finSuppIn G T').lift (finSuppIn G T).ι fun X ↦ ⟨X.2.1, fun j hj ↦ X.2.2 j fun h' ↦ hj (h h')⟩
  additive := ⟨ObjectProperty.hom_ext _ rfl⟩
  map_star _ := ObjectProperty.hom_ext _ rfl

/-- The coordinate endofunctor `⊕ → Free(ℚ[Gᵢ]) → ⊕`. -/
abbrev coordEndo (i : ℕ) : finSuppFreeQG G Set.univ ⟶ finSuppFreeQG G Set.univ :=
  ((finSuppFiltration G).incl ≫ evalQG G i) ≫ finSuppIncl G (Set.subset_univ _)

/-- Its isometric inclusion into the identity. -/
def coordInc (i : ℕ) :
    (coordEndo (G := G) i).F ⟶ (𝟙 (finSuppFreeQG G Set.univ) : _ ⟶ _).F where
  app M := ObjectProperty.homMk (inc M.obj {i})
  naturality M N f := ObjectProperty.hom_ext _ <| by
    change (inc M.obj {i} ≫ f.hom ≫ prj N.obj {i}) ≫ inc N.obj {i} = inc M.obj {i} ≫ f.hom
    rw [assoc, assoc, prj_inc, ← idem_comm, inc_idem_assoc]

lemma exists_finset_support (P : SymPoincare (finSuppFreeQG G Set.univ).inv n) :
    ∃ s : Finset ℕ, ∀ r, P.p.f r = 0 ∨ ∀ j ∉ s, (P.C.X r).obj.rank j = 0 := by
  classical
  refine ⟨(Finset.Icc 0 n).biUnion fun r ↦ (P.C.X r).property.1.toFinset, fun r ↦ ?_⟩
  by_cases hr : r ∈ Finset.Icc 0 n
  · exact Or.inr fun j hj ↦ by_contra fun h ↦ hj (Finset.mem_biUnion.mpr ⟨r, hr, by simpa using h⟩)
  · exact Or.inl (P.support r (by simp at hr; omega))

lemma Lconc.cls_eq_sum_coordEndo (P : SymPoincare (finSuppFreeQG G Set.univ).inv n)
    (s : Finset ℕ) (hs : ∀ r, P.p.f r = 0 ∨ ∀ j ∉ s, (P.C.X r).obj.rank j = 0) :
    Lconc.cls P = ∑ i ∈ s, Lconc.map (coordEndo i) (Lconc.cls P) := by
  refine Lconc.cls_eq_sum_map s coordInc (fun i X ↦ ObjectProperty.hom_ext _ inc_prj)
    (fun i j hij X ↦ ObjectProperty.hom_ext _ (inc_prj_eq_zero (by simpa using hij))) P
    fun r ↦ ?_
  rcases hs r with h | h
  · rw [h, zero_comp]; rfl
  · have : ∑ i ∈ s, (finSuppFreeQG G Set.univ).inv.star ((coordInc i).app (P.C.X r)) ≫
        (coordInc i).app (P.C.X r) = 𝟙 _ := ObjectProperty.hom_ext _ <| by
      erw [← ObjectProperty.ι_map, Functor.map_sum]
      change ∑ i ∈ s, prj _ {i} ≫ inc _ {i} = 𝟙 _
      simp only [prj_inc]
      rw [sum_idem]
      exact idem_eq_id fun j hj ↦ h j (by simpa using hj)
    erw [this]
    exact comp_id _

theorem Lconc.eq_zero_of_map_evalQG {y : Lconc (finSuppFreeQG G Set.univ) n}
    (h : ∀ i, Lconc.map ((finSuppFiltration G).incl ≫ evalQG G i) y = 0) : y = 0 := by
  obtain ⟨P, rfl⟩ := Lconc.cls_surjective y
  obtain ⟨s, hs⟩ := exists_finset_support P
  rw [Lconc.cls_eq_sum_coordEndo P s hs]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [Lconc.map_comp, AddMonoidHom.comp_apply]
  exact (congrArg _ (h i)).trans (map_zero _)

theorem Lconc.eventually_map_evalQG (y : Lconc (finSuppFreeQG G Set.univ) n) :
    ∀ᶠ i in atTop, Lconc.map ((finSuppFiltration G).incl ≫ evalQG G i) y = 0 := by
  obtain ⟨P, rfl⟩ := Lconc.cls_surjective y
  obtain ⟨s, hs⟩ := exists_finset_support P
  refine eventually_atTop.mpr ⟨s.sup id + 1, fun i hi ↦ ?_⟩
  have hi' : i ∉ s := fun h ↦ by have := Finset.le_sup (f := id) h; simp at this; omega
  erw [Lconc.map_cls]
  refine Lconc.cls_eq_zero_of_p_eq_zero (HomologicalComplex.hom_ext _ _ fun r ↦ ?_)
  rcases hs r with h | h
  · change ((finSuppFiltration G).incl ≫ evalQG G i).F.map (P.p.f r) = 0
    erw [h, Functor.map_zero]
  · refine ObjectProperty.hom_ext _ (AsymptoticObject.hom_ext fun j ↦ ?_)
    ext a b
    have h₁ : (a.1 : ℕ) < (res (P.C.X r).obj {i}).rank j := a.1.2
    have h₂ : (res (P.C.X r).obj {i}).rank j = 0 := by
      by_cases hj : j = i
      · subst hj; exact Nat.le_zero.mp ((idxRestrict_rank_le _ _ _).trans (h j hi').le)
      · exact idxRestrict_rank_eq_zero _ hj
    omega

end Coord

/-! ### Index-wise functors -/

section Indexwise

open AsymptoticObject FreeQG

variable {G G' : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)] [∀ i, Group (G' i)]
  [∀ i, Fintype (G' i)]

/-- `Φ : ∏ᵢ Free(ℚ[Gᵢ]) → ∏ᵢ Free(ℚ[G'ᵢ])` acts index by index: it commutes with the central
idempotents `idem M s`. -/
def IsIndexwise (Φ : prodFreeQG G ⟶ prodFreeQG G') : Prop :=
  ∀ (M : prodFreeQG G) (s : Set ℕ), Φ.F.map (idem M s) = idem (Φ.F.obj M) s

namespace IsIndexwise

variable {Φ : prodFreeQG G ⟶ prodFreeQG G'} (hΦ : IsIndexwise Φ)
include hΦ

lemma map_finSuppIn {T : Set ℕ} {M : prodFreeQG G} (hM : finSuppIn G T M) :
    finSuppIn G' T (Φ.F.obj M) := by
  have h : idem (Φ.F.obj M) {j | M.rank j ≠ 0} = 𝟙 _ := by
    rw [← hΦ, idem_eq_id fun j hj ↦ by simpa using hj, Φ.F.map_id]
  exact ⟨hM.1.subset fun j hj ↦ by_contra fun h' ↦ hj (rank_eq_zero_of_idem h h'),
    fun j hj ↦ rank_eq_zero_of_idem h fun h' ↦ h' (hM.2 j hj)⟩

/-- The restriction `⊕_{i ∈ T} Free(ℚ[Gᵢ]) → ⊕_{i ∈ T} Free(ℚ[G'ᵢ])`. -/
def restrict (T : Set ℕ) : finSuppFreeQG G T ⟶ finSuppFreeQG G' T where
  F := (finSuppIn G' T).lift ((finSuppIn G T).ι ⋙ Φ.F) fun X ↦ hΦ.map_finSuppIn X.2
  additive := { map_add := ObjectProperty.hom_ext _ Φ.F.map_add }
  map_star f := ObjectProperty.hom_ext _ (Φ.map_star f.hom)

/-- An index-wise functor commutes with the coordinate projections. -/
def evalIso (i : ℕ) : InvCat.UnitaryIso (Φ ≫ evalQG G' i) (evalQG G i ≫ hΦ.restrict {i}) where
  iso := NatIso.ofComponents (fun M ↦
    { hom := ObjectProperty.homMk (inc (Φ.F.obj M) {i} ≫ Φ.F.map (prj M {i}))
      inv := ObjectProperty.homMk (Φ.F.map (inc M {i}) ≫ prj (Φ.F.obj M) {i})
      hom_inv_id := ObjectProperty.hom_ext _ <| by
        change (inc _ _ ≫ Φ.F.map (prj M {i})) ≫ Φ.F.map (inc M {i}) ≫ prj _ _ = 𝟙 _
        rw [assoc, ← Φ.F.map_comp_assoc, prj_inc, hΦ, idem_prj, inc_prj]
      inv_hom_id := ObjectProperty.hom_ext _ <| by
        change (Φ.F.map (inc M {i}) ≫ prj _ _) ≫ inc _ _ ≫ Φ.F.map (prj M {i}) = 𝟙 _
        rw [assoc, prj_inc_assoc, ← hΦ, ← Φ.F.map_comp, ← Φ.F.map_comp, idem_prj, inc_prj,
          Φ.F.map_id] }) fun {M N} f ↦ ObjectProperty.hom_ext _ <| by
    change (inc _ _ ≫ Φ.F.map f ≫ prj _ _) ≫ inc _ _ ≫ Φ.F.map (prj N {i}) =
      (inc _ _ ≫ Φ.F.map (prj M {i})) ≫ Φ.F.map (inc M {i} ≫ f ≫ prj N {i})
    simp only [Functor.map_comp, assoc, prj_inc_assoc]
    rw [← Φ.F.map_comp_assoc (prj M {i}), prj_inc, hΦ, idem_comm_assoc]
  star_hom M := ObjectProperty.hom_ext _ <| by
    change (prodFreeQG G').inv.star (inc _ _ ≫ Φ.F.map (prj M {i})) =
      Φ.F.map (inc M {i}) ≫ prj _ _
    rw [(prodFreeQG G').inv.star_comp, ← Φ.map_star, star_prj, star_inc]

end IsIndexwise

variable (G) in
/-- Forgetting the group, `∏ᵢ Free(ℚ[Gᵢ]) → ∏ᵢ Free(ℚ)`, with no factor `1/|Gᵢ|` (l. 129). -/
def forgetQG : prodFreeQG G ⟶ prodFreeQG fun _ : ℕ ↦ Unit where
  F := AsymptoticObject.forgetFunctor _ PUnit
  additive := forgetFunctor_additive
  map_star := forgetHom_transpose

lemma isIndexwise_forgetQG : IsIndexwise (forgetQG G) := fun M s ↦
  AsymptoticObject.hom_ext fun j ↦ by
    change (forgetHom (idem M s)).1 j = (idem (forgetObj M) s).1 j
    erw [forgetHom_val, idem_val, idem_val]
    split_ifs
    · convert Matrix.submatrix_one_equiv _
    · simp

lemma toPoint_forget {H : Type*} [Group H] (π : ∀ i, G i →* H) :
    toPoint G π ≫ (AsymptoticCategory.forgetInv : asymptoticInvCat π PUnit ⟶ _) =
      forgetQG G ≫ toPoint _ (scalarHom H) :=
  rfl

end Indexwise

/-! ### Prop. 3.2: lifts to `L(∏)` and the tail homomorphism -/

/-- Eventually zero families, `⊕ᵢ Mᵢ ⊂ ∏ᵢ Mᵢ`. -/
def tailSubgroup (M : ℕ → Type*) [∀ i, AddCommGroup (M i)] : AddSubgroup (∀ i, M i) where
  carrier := {x | ∀ᶠ i in atTop, x i = 0}
  add_mem' hx hy := (hx.and hy).mono fun i h ↦ by simp [h.1, h.2]
  zero_mem' := .of_forall fun _ ↦ rfl
  neg_mem' hx := hx.mono fun i h ↦ by simp [h]

/-- `∏ᵢ Mᵢ / ⊕ᵢ Mᵢ`. -/
abbrev Tail (M : ℕ → Type*) [∀ i, AddCommGroup (M i)] : Type _ := (∀ i, M i) ⧸ tailSubgroup M

namespace Tail

variable {M M' : ℕ → Type*} [∀ i, AddCommGroup (M i)] [∀ i, AddCommGroup (M' i)]

/-- The map of tails induced by maps of the factors. -/
def map (f : ∀ i, M i →+ M' i) : Tail M →+ Tail M' :=
  QuotientAddGroup.map _ _ (AddMonoidHom.pi fun i ↦ (f i).comp (Pi.evalAddMonoidHom M i))
    fun x (hx : ∀ᶠ i in atTop, x i = 0) ↦ show ∀ᶠ i in atTop, f i (x i) = 0 from
      hx.mono fun i h ↦ by simp [h]

@[simp]
lemma map_mk (f : ∀ i, M i →+ M' i) (x : ∀ i, M i) :
    map f (QuotientAddGroup.mk x) = QuotientAddGroup.mk fun i ↦ f i (x i) :=
  rfl

end Tail

namespace LowerLTheory

open AsymptoticObject FreeQG

variable (𝕃 : LowerLTheory) {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)] {n : ℤ}
  {H : Type*} [Group H] (π : ∀ i, G i →* H)

variable (G) in
/-- **H5** as an isomorphism `L^p_n(⊕_{i ∈ T} Free(ℚ[Gᵢ])) ≅ L_n(⊕_{i ∈ T} Free(ℚ[Gᵢ]))`,
`n ≥ 0`. -/
def decEquiv (T : Set ℕ) (hn : 0 ≤ n) :
    Lconc (finSuppFreeQG G T) n ≃+ 𝕃.L (finSuppFreeQG G T) n :=
  AddEquiv.ofBijective (𝕃.cls _ n) (𝕃.dec_bij G T n hn)

@[simp]
lemma decEquiv_apply (T : Set ℕ) (hn : 0 ≤ n) (x : Lconc (finSuppFreeQG G T) n) :
    𝕃.decEquiv G T hn x = 𝕃.cls _ n x :=
  rfl

/-- `L_n(⊕ᵢ Free(ℚ[Gᵢ])) → L_n(∏ᵢ Free(ℚ[Gᵢ]))` is injective for `n ≥ 0`: by `dec_bij`, an element
is a projective class, which is detected by the coordinate projections (blueprint s04-06, E8). -/
theorem finSupp_incl_injective (hn : 0 ≤ n) :
    Function.Injective (𝕃.map (finSuppFiltration G).incl n) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
  obtain ⟨y, rfl⟩ := (𝕃.dec_bij G Set.univ n hn).2 x
  have : y = 0 := Lconc.eq_zero_of_map_evalQG fun i ↦ (𝕃.dec_bij G {i} n hn).1 <| by
    have := congrArg (𝕃.map (evalQG G i) n) hx
    erw [map_zero, map_map] at this
    exact ((𝕃.cls_map _ _ y).trans this).trans (map_zero _).symm
  rw [this, map_zero]; rfl

/-- The boundary `L_{n+1}(V_G) → L_n(⊕ᵢ Free(ℚ[Gᵢ]))` of the localization sequence of
`⊕ ⊂ ∏`. -/
def pointBdry (n : ℤ) :
    𝕃.L (asymptoticInvCat π PUnit) (n + 1) →+ 𝕃.L (finSuppFreeQG G Set.univ) n :=
  (𝕃.bdry (finSuppFiltration G) n).comp (𝕃.map (pointIso G π).inv (n + 1))

/-- `L(∏/⊕) ≅ L(V_G)`. -/
def pointEquiv (n : ℤ) : 𝕃.L (finSuppFiltration G).quot n ≃+ 𝕃.L (asymptoticInvCat π PUnit) n :=
  𝕃.mapAddEquiv (pointIso G π).hom (pointIso G π).inv
    (by rw [Iso.hom_inv_id]; exact .refl _) (by rw [Iso.inv_hom_id]; exact .refl _) n

lemma map_pointIso_hom_inv (x : 𝕃.L (asymptoticInvCat π PUnit) n) :
    𝕃.map (pointIso G π).hom n (𝕃.map (pointIso G π).inv n x) = x := by
  rw [map_map, Iso.inv_hom_id, 𝕃.map_id, AddMonoidHom.id_apply]

lemma map_pointIso_inv_hom (x : 𝕃.L (finSuppFiltration G).quot n) :
    𝕃.map (pointIso G π).inv n (𝕃.map (pointIso G π).hom n x) = x := by
  rw [map_map, Iso.hom_inv_id, 𝕃.map_id, AddMonoidHom.id_apply]

lemma map_toPoint (y : 𝕃.L (prodFreeQG G) n) :
    𝕃.map (toPoint G π) n y = 𝕃.map (pointIso G π).hom n (𝕃.map (finSuppFiltration G).proj n y) :=
  by rw [toPoint, 𝕃.map_comp, AddMonoidHom.comp_apply]

theorem exact_incl_toPoint :
    Function.Exact (𝕃.map (finSuppFiltration G).incl n) (𝕃.map (toPoint G π) n) := fun y ↦ by
  rw [← 𝕃.exact_A (finSuppFiltration G) n y, map_toPoint]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, map_zero]⟩
  rw [← 𝕃.map_pointIso_inv_hom π (𝕃.map _ n y), h, map_zero]

theorem exact_toPoint_pointBdry :
    Function.Exact (𝕃.map (toPoint G π) (n + 1)) (𝕃.pointBdry π n) := fun x ↦ by
  change 𝕃.bdry _ n (𝕃.map (pointIso G π).inv (n + 1) x) = 0 ↔ _
  rw [𝕃.exact_Q (finSuppFiltration G) n]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, by rw [map_toPoint, hy, map_pointIso_hom_inv]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, by rw [map_toPoint, map_pointIso_inv_hom]⟩

theorem exact_pointBdry_incl :
    Function.Exact (𝕃.pointBdry π n) (𝕃.map (finSuppFiltration G).incl n) := fun x ↦ by
  erw [𝕃.exact_U (finSuppFiltration G) n]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨𝕃.map (pointIso G π).hom (n + 1) y, by
      change 𝕃.bdry _ n (𝕃.map (pointIso G π).inv (n + 1) _) = _
      rw [map_pointIso_inv_hom]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨_, rfl⟩

/-- For `n ≥ 0` the boundary `L_{n+1}(V_G) → L_n(⊕)` vanishes. -/
theorem pointBdry_eq_zero (hn : 0 ≤ n) (x : 𝕃.L (asymptoticInvCat π PUnit) (n + 1)) :
    𝕃.pointBdry π n x = 0 :=
  𝕃.bdry_eq_zero_of_injective _ (𝕃.finSupp_incl_injective hn) _

/-- **Lifting** (Prop. 3.2, form used): for `n ≥ 0` every class of `L_{n+1}(V_G)` comes from
`L_{n+1}(∏ᵢ Free(ℚ[Gᵢ]))`. -/
theorem toPoint_surjective (hn : 0 ≤ n) :
    Function.Surjective (𝕃.map (toPoint G π) (n + 1)) := fun x ↦
  (𝕃.exact_toPoint_pointBdry π x).mp (𝕃.pointBdry_eq_zero π hn x)

/-- Lifts are unique modulo the image of `L(⊕ᵢ Free(ℚ[Gᵢ]))`. -/
theorem toPoint_eq_toPoint_iff {y y' : 𝕃.L (prodFreeQG G) n} :
    𝕃.map (toPoint G π) n y = 𝕃.map (toPoint G π) n y' ↔
      y - y' ∈ (𝕃.map (finSuppFiltration G).incl n).range := by
  rw [← sub_eq_zero, ← map_sub, 𝕃.exact_incl_toPoint π]
  rfl

/-- The coordinates `L_n(∏ⱼ Free(ℚ[Gⱼ])) → ∏ᵢ L^p_n(ℚ[Gᵢ])` (`n ≥ 0`): the coordinate
projections followed by `dec_bij⁻¹`. -/
def coord (hn : 0 ≤ n) : 𝕃.L (prodFreeQG G) n →+ ∀ i, Lconc (finSuppFreeQG G {i}) n :=
  AddMonoidHom.pi fun i ↦ (𝕃.decEquiv G {i} hn).symm.toAddMonoidHom.comp (𝕃.map (evalQG G i) n)

lemma cls_coord (hn : 0 ≤ n) (y : 𝕃.L (prodFreeQG G) n) (i : ℕ) :
    𝕃.cls _ n (𝕃.coord hn y i) = 𝕃.map (evalQG G i) n y :=
  (𝕃.decEquiv G {i} hn).apply_symm_apply _

lemma coord_cls (hn : 0 ≤ n) (y : Lconc (prodFreeQG G) n) (i : ℕ) :
    𝕃.coord hn (𝕃.cls _ n y) i = Lconc.map (evalQG G i) y :=
  (𝕃.decEquiv G {i} hn).symm_apply_eq.mpr (𝕃.cls_map _ _ _).symm

lemma coord_incl_mem (hn : 0 ≤ n) (x : 𝕃.L (finSuppFreeQG G Set.univ) n) :
    𝕃.coord hn (𝕃.map (finSuppFiltration G).incl n x) ∈ tailSubgroup _ := by
  obtain ⟨y, rfl⟩ := (𝕃.dec_bij G Set.univ n hn).2 x
  refine (Lconc.eventually_map_evalQG y).mono fun i hi ↦ ?_
  erw [show 𝕃.map (finSuppFiltration G).incl n (𝕃.cls (finSuppFreeQG G Set.univ) n y) =
    𝕃.cls _ n (Lconc.map (finSuppFiltration G).incl y) from (𝕃.cls_map _ _ _).symm, coord_cls,
    ← AddMonoidHom.comp_apply, ← Lconc.map_comp]
  exact hi

/-- The coordinates are natural for index-wise functors. -/
lemma coord_map {G' : ℕ → Type} [∀ i, Group (G' i)] [∀ i, Fintype (G' i)]
    {Φ : prodFreeQG G ⟶ prodFreeQG G'} (hΦ : IsIndexwise Φ) (hn : 0 ≤ n)
    (y : 𝕃.L (prodFreeQG G) n) (i : ℕ) :
    𝕃.coord hn (𝕃.map Φ n y) i = Lconc.map (hΦ.restrict {i}) (𝕃.coord hn y i) := by
  apply (𝕃.decEquiv G' {i} hn).injective
  rw [decEquiv_apply, decEquiv_apply, 𝕃.cls_map, cls_coord, cls_coord, map_map, map_map,
    𝕃.map_unitaryIso (hΦ.evalIso i)]

/-- **Prop. 3.2, (3.4)–(3.5) in the form used** (design I3): for `n ≥ 0`, the homomorphism
`L_{n+1}(V_G) → ∏ᵢ L^p_{n+1}(ℚ[Gᵢ]) / ⊕ᵢ L^p_{n+1}(ℚ[Gᵢ])`, lift to `L_{n+1}(∏ᵢ Free(ℚ[Gᵢ]))` and
take coordinates; well defined since the image of `L_{n+1}(⊕)` has finitely supported
coordinates. -/
def tail (hn : 0 ≤ n) :
    𝕃.L (asymptoticInvCat π PUnit) (n + 1) →+ Tail fun i ↦ Lconc (finSuppFreeQG G {i}) (n + 1) :=
  (𝕃.quotLift (finSuppFiltration G) (𝕃.finSupp_incl_injective hn)
    ((QuotientAddGroup.mk' _).comp (𝕃.coord (Int.le_add_one hn)))
    fun x ↦ (QuotientAddGroup.eq_zero_iff _).mpr (𝕃.coord_incl_mem _ x)).comp
    (𝕃.map (pointIso G π).inv (n + 1))

theorem tail_toPoint (hn : 0 ≤ n) (y : 𝕃.L (prodFreeQG G) (n + 1)) :
    𝕃.tail π hn (𝕃.map (toPoint G π) (n + 1) y) =
      QuotientAddGroup.mk (𝕃.coord (Int.le_add_one hn) y) := by
  erw [tail, AddMonoidHom.comp_apply, map_toPoint, map_pointIso_inv_hom, quotLift_proj]
  rfl

/-- The tail of the class of a sequence of complexes is the sequence of its coordinate classes. -/
theorem tail_cls (hn : 0 ≤ n) (P : SymPoincare (prodFreeQG G).inv (n + 1)) :
    𝕃.tail π hn (𝕃.cls _ (n + 1) (Lconc.cls (P.map (toPoint G π)))) =
      QuotientAddGroup.mk fun i ↦ Lconc.cls (P.map (evalQG G i)) := by
  rw [← Lconc.map_cls, 𝕃.cls_map, tail_toPoint]
  congr 1
  funext i
  rw [coord_cls, Lconc.map_cls]

/-- **Naturality** of the tail for index-wise functors (e.g. forgetting the group, tensoring
index-wise with forms), compatible with a functor `Ψ` on `V_G`. -/
theorem tail_natural {G' : ℕ → Type} [∀ i, Group (G' i)] [∀ i, Fintype (G' i)]
    {H' : Type*} [Group H'] {π' : ∀ i, G' i →* H'} {Φ : prodFreeQG G ⟶ prodFreeQG G'}
    (hΦ : IsIndexwise Φ) (Ψ : asymptoticInvCat π PUnit ⟶ asymptoticInvCat π' PUnit)
    (hΨ : toPoint G π ≫ Ψ = Φ ≫ toPoint G' π') (hn : 0 ≤ n)
    (x : 𝕃.L (asymptoticInvCat π PUnit) (n + 1)) :
    𝕃.tail π' hn (𝕃.map Ψ (n + 1) x) =
      Tail.map (fun i ↦ Lconc.map (hΦ.restrict {i})) (𝕃.tail π hn x) := by
  obtain ⟨y, rfl⟩ := 𝕃.toPoint_surjective π hn x
  rw [map_map, hΨ, ← map_map, tail_toPoint, tail_toPoint, Tail.map_mk]
  exact congrArg _ (funext (𝕃.coord_map hΦ _ y))

/-- **Forgetting the group** commutes with the tail (Prop. 3.2; S12b). -/
theorem tail_forget (hn : 0 ≤ n) (x : 𝕃.L (asymptoticInvCat π PUnit) (n + 1)) :
    𝕃.tail (scalarHom H) hn
        (𝕃.map (AsymptoticCategory.forgetInv : asymptoticInvCat π PUnit ⟶ _) (n + 1) x) =
      Tail.map (fun i ↦ Lconc.map (isIndexwise_forgetQG.restrict {i})) (𝕃.tail π hn x) :=
  𝕃.tail_natural π isIndexwise_forgetQG _ (toPoint_forget π) hn x

/-- **H-change**: the tail does not depend on `π`. -/
theorem tail_pointChange {H' : Type*} [Group H'] (π' : ∀ i, G i →* H') (hn : 0 ≤ n)
    (x : 𝕃.L (asymptoticInvCat π PUnit) (n + 1)) :
    𝕃.tail π' hn (𝕃.map (pointChange π π') (n + 1) x) = 𝕃.tail π hn x := by
  obtain ⟨y, rfl⟩ := 𝕃.toPoint_surjective π hn x
  rw [map_map, toPoint_pointChange, tail_toPoint, tail_toPoint]

end LowerLTheory

end

end HSFormal.LTheory
