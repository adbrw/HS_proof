import Mathlib.Order.SupIndep
import Mathlib.Data.Int.Interval
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Projection
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# The interval decomposition lemma (NegK level 1, module 2)

`blueprint/negK-proof.md` §2.3, Lemmas 2 and 3.  Pure lattice theory.

**Setting.**  `P : ℤ → ℤ → α` is an *interval family* in a complete modular lattice: `P u v = ⊥`
for `v < u` (`hP₀`) and the intersection rule (H) `P u v ⊓ P u' v' = P (max u u') (min v v')`
(`hP`).  `S P u v = P u (v - 1) ⊔ P (u + 1) v` is the "boundary" of `[u, v]`, and `C` is a family
of relative complements: `Disjoint (C u v) (S P u v)` and `C u v ⊔ S P u v = P u v`
(`exists_compl` provides one in a complemented lattice).

**Lemma 2** (`supIndep_box`, `sup_box`): for all `u, v`, the family `(C J)_{J ⊆ [u, v]}` over the
intervals `J = [a, c]`, `u ≤ a ≤ c ≤ v` (`box u v`) is independent with supremum `P u v`.  No
dimension count is used.  `C_eq_bot`: `C u v = ⊥` whenever `P u v ≤ S P u v`.

**Lemma 3** (window form).  If `P u v ≤ S P u v` whenever `v - u > L` (locality, Lemma 1 with
`L = 2b`), then `D v := ⨆_{u ∈ [v - L, v]} C u v` satisfies `D v ≤ P (v - L) v` (`D_le`),
`P c a ≤ ⨆_{v ∈ [c, a]} D v` (`P_le_sup_D`), and `(D v)_v` is independent on every finite
window (`supIndep_D`), hence (for submodules) independent (`iSupIndep_of_supIndep_Icc`).

**Projections** (`proj`): for an independent family `D : ℤ → Submodule R M` in a semisimple
module, `proj hD v` is a linear projection onto `D v` with (F3) `proj_of_mem`
(`y ∈ D v → proj v' y = if v' = v then y else 0`) and (F1)/(F2) `proj_eq_zero_of_mem_iSup`,
`sum_proj_of_mem_iSup` (for `x ∈ ⨆_{v ∈ s} D v`: `proj v x = 0` off `s`, `x = ∑_{v ∈ s} proj v x`).
-/

namespace HSFormal.LTheory.IntervalDecomp

open Finset

/-! ### Two-block independence -/

lemma supIndep_union {ι α : Type*} [Lattice α] [OrderBot α] [IsModularLattice α]
    [DecidableEq ι] {s t : Finset ι} {f : ι → α} (hs : s.SupIndep f) (ht : t.SupIndep f)
    (hst : Disjoint (s.sup f) (t.sup f)) : (s ∪ t).SupIndep f := by
  have h : (univ : Finset Bool).biUnion (fun b ↦ if b then s else t) = s ∪ t := by
    ext x; simp
  rw [← h]
  refine SupIndep.biUnion ?_ fun b _ ↦ ?_
  · rw [supIndep_univ_bool]; simpa using hst.symm
  · cases b <;> simpa

/-! ### Lemma 2 -/

section Lattice

variable {α : Type*} [CompleteLattice α] [IsModularLattice α]

/-- The boundary `S[u,v] = P[u, v-1] ⊔ P[u+1, v]` of the interval `[u, v]`. -/
def S (P : ℤ → ℤ → α) (u v : ℤ) : α := P u (v - 1) ⊔ P (u + 1) v

/-- The intervals `[a, c]` with `u ≤ a ≤ c ≤ v`, as pairs `(a, c)`. -/
def box (u v : ℤ) : Finset (ℤ × ℤ) := (Icc u v ×ˢ Icc u v).filter fun j ↦ j.1 ≤ j.2

lemma mem_box {u v : ℤ} {j : ℤ × ℤ} : j ∈ box u v ↔ u ≤ j.1 ∧ j.1 ≤ j.2 ∧ j.2 ≤ v := by
  simp only [box, mem_filter, mem_product, mem_Icc]; omega

variable {P : ℤ → ℤ → α} (hP₀ : ∀ u v, v < u → P u v = ⊥)
  (hP : ∀ u v u' v', P u v ⊓ P u' v' = P (max u u') (min v v'))

omit [IsModularLattice α] in
include hP in
lemma P_mono {u v u' v' : ℤ} (hu : u' ≤ u) (hv : v ≤ v') : P u v ≤ P u' v' := by
  rw [← inf_eq_left, hP, max_eq_left hu, min_eq_left hv]

omit [IsModularLattice α] in
include hP in
lemma S_le (u v : ℤ) : S P u v ≤ P u v :=
  sup_le (P_mono hP le_rfl (by omega)) (P_mono hP (by omega) le_rfl)

include hP in
/-- Relative complements of the boundaries exist in a complemented modular lattice. -/
lemma exists_compl [ComplementedLattice α] :
    ∃ C : ℤ → ℤ → α, ∀ u v, Disjoint (C u v) (S P u v) ∧ C u v ⊔ S P u v = P u v := by
  choose T hT using fun j : ℤ × ℤ ↦ exists_isCompl (S P j.1 j.2)
  refine ⟨fun u v ↦ P u v ⊓ T (u, v), fun u v ↦ ⟨?_, ?_⟩⟩
  · exact (hT (u, v)).disjoint.symm.mono_left inf_le_right
  · show P u v ⊓ T (u, v) ⊔ S P u v = P u v
    rw [sup_comm, inf_comm, ← sup_inf_assoc_of_le _ (S_le hP u v), (hT (u, v)).sup_eq_top,
      top_inf_eq]

variable {C : ℤ → ℤ → α} (hC₁ : ∀ u v, Disjoint (C u v) (S P u v))
  (hC₂ : ∀ u v, C u v ⊔ S P u v = P u v)

omit [IsModularLattice α] in
include hC₂ in
lemma C_le (u v : ℤ) : C u v ≤ P u v := hC₂ u v ▸ le_sup_left

omit [IsModularLattice α] in
include hC₁ hC₂ in
/-- **Lemma 2(b)**: `C u v = ⊥` when `P u v = S u v`. -/
lemma C_eq_bot {u v : ℤ} (h : P u v ≤ S P u v) : C u v = ⊥ :=
  (hC₁ u v).eq_bot_of_le ((C_le hC₂ u v).trans h)

omit [IsModularLattice α] in
include hP₀ in
lemma box_spec_empty {u v : ℤ} (h : v < u) :
    (box u v).SupIndep (fun j ↦ C j.1 j.2) ∧ (box u v).sup (fun j ↦ C j.1 j.2) = P u v := by
  have : box u v = ∅ := eq_empty_of_forall_notMem fun j hj ↦ by
    have := mem_box.1 hj; omega
  rw [this, hP₀ u v h]
  exact ⟨supIndep_empty _, sup_empty⟩

include hP₀ hP hC₁ hC₂ in
/-- **Lemma 2(a)**, by induction on the length of `[u, v]`. -/
theorem box_spec (n : ℕ) : ∀ u v : ℤ, v + 1 - u ≤ n →
    (box u v).SupIndep (fun j ↦ C j.1 j.2) ∧ (box u v).sup (fun j ↦ C j.1 j.2) = P u v := by
  classical
  induction n with
  | zero => intro u v h; exact box_spec_empty hP₀ (by omega)
  | succ n ih =>
    intro u v h
    rcases lt_trichotomy u v with huv | rfl | huv
    · set f : ℤ × ℤ → α := fun j ↦ C j.1 j.2
      set A := box u (v - 1)
      set A' := box (u + 1) (v - 1)
      set Bv := (Icc (u + 1) v).image fun a ↦ (a, v)
      obtain ⟨hAi, hAs⟩ := ih u (v - 1) (by omega)
      obtain ⟨hA'i, hA's⟩ := ih (u + 1) (v - 1) (by omega)
      obtain ⟨hBi, hBs⟩ := ih (u + 1) v (by omega)
      have h1 : box (u + 1) v = A' ∪ Bv := by
        ext j; simp only [mem_union, mem_box, A', Bv, mem_image, mem_Icc]
        constructor
        · intro hj
          by_cases hjv : j.2 = v
          · exact Or.inr ⟨j.1, ⟨hj.1, by omega⟩, by rw [← hjv]⟩
          · exact Or.inl ⟨hj.1, hj.2.1, by omega⟩
        · rintro (hj | ⟨a, ha, rfl⟩)
          · exact ⟨hj.1, hj.2.1, by omega⟩
          · exact ⟨ha.1, ha.2, le_rfl⟩
      have h2 : box u v = {(u, v)} ∪ (A ∪ Bv) := by
        ext j; simp only [mem_union, mem_singleton, mem_box, A, Bv, mem_image, mem_Icc]
        constructor
        · intro hj
          by_cases hjv : j.2 = v
          · by_cases hju : j.1 = u
            · exact Or.inl (Prod.ext hju hjv)
            · exact Or.inr (Or.inr ⟨j.1, ⟨by omega, by omega⟩, by rw [← hjv]⟩)
          · exact Or.inr (Or.inl ⟨hj.1, hj.2.1, by omega⟩)
        · rintro (rfl | hj | ⟨a, ha, rfl⟩)
          · exact ⟨le_rfl, huv.le, le_rfl⟩
          · exact ⟨hj.1, hj.2.1, by omega⟩
          · exact ⟨by omega, ha.2, le_rfl⟩
      have hd : Disjoint A' Bv := by
        rw [disjoint_left]
        intro j hjA hjB
        obtain ⟨a, -, rfl⟩ := mem_image.1 hjB
        have := mem_box.1 hjA; dsimp only at this; omega
      have hBsub : Bv ⊆ box (u + 1) v := h1 ▸ subset_union_right
      have hA'sub : A' ⊆ box (u + 1) v := h1 ▸ subset_union_left
      have hBind : Bv.SupIndep f := hBi.subset hBsub
      have hdisj1 : Disjoint (A'.sup f) (Bv.sup f) := hBi.disjoint_sup_sup hA'sub hBsub hd
      have hBle : Bv.sup f ≤ P (u + 1) v := hBs ▸ sup_mono hBsub
      have hPsplit : P (u + 1) v = A'.sup f ⊔ Bv.sup f := by rw [← hBs, h1, sup_union]
      have hdisj2 : Disjoint (A.sup f) (Bv.sup f) := by
        rw [hAs, disjoint_iff, ← inf_eq_right.mpr hBle, ← inf_assoc, hP,
          max_eq_right (by omega : u ≤ u + 1), min_eq_left (by omega : v - 1 ≤ v), ← hA's]
        exact disjoint_iff.mp hdisj1
      have hAB : (A ∪ Bv).SupIndep f := supIndep_union hAi hBind hdisj2
      have hABs : (A ∪ Bv).sup f = S P u v := by
        rw [sup_union, hAs, S, hPsplit, ← sup_assoc, hA's,
          sup_eq_left.mpr (P_mono hP (by omega : u ≤ u + 1) le_rfl)]
      rw [h2]
      refine ⟨supIndep_union (supIndep_singleton _ _) hAB ?_, ?_⟩
      · rw [sup_singleton, hABs]; exact hC₁ u v
      · rw [sup_union, sup_singleton, hABs, hC₂]
    · have hb : box u u = {(u, u)} := by
        ext j; simp only [mem_box, mem_singleton]
        constructor
        · intro hj; exact Prod.ext (by omega) (by omega)
        · rintro rfl; exact ⟨le_rfl, le_rfl, le_rfl⟩
      rw [hb, sup_singleton]
      refine ⟨supIndep_singleton _ _, ?_⟩
      have := hC₂ u u
      rwa [S, hP₀ u (u - 1) (by omega), hP₀ (u + 1) u (by omega), sup_bot_eq, sup_bot_eq] at this
    · exact box_spec_empty hP₀ huv

include hP₀ hP hC₁ hC₂ in
theorem supIndep_box (u v : ℤ) : (box u v).SupIndep (fun j ↦ C j.1 j.2) :=
  (box_spec hP₀ hP hC₁ hC₂ (v + 1 - u).toNat u v (by omega)).1

include hP₀ hP hC₁ hC₂ in
theorem sup_box (u v : ℤ) : (box u v).sup (fun j ↦ C j.1 j.2) = P u v :=
  (box_spec hP₀ hP hC₁ hC₂ (v + 1 - u).toNat u v (by omega)).2

/-! ### Lemma 3: the window sums `D v` -/

/-- `D v = ⨆_{u ∈ [v - L, v]} C u v`. -/
def D (C : ℤ → ℤ → α) (L : ℕ) (v : ℤ) : α := (Icc (v - L) v).sup fun u ↦ C u v

omit [IsModularLattice α] in
include hP hC₂ in
lemma D_le (L : ℕ) (v : ℤ) : D C L v ≤ P (v - L) v :=
  Finset.sup_le fun u hu ↦ (C_le hC₂ u v).trans (P_mono hP (mem_Icc.1 hu).1 le_rfl)

variable {L : ℕ} (hloc : ∀ u v, (L : ℤ) < v - u → P u v ≤ S P u v)

include hP₀ hP hC₁ hC₂ hloc in
lemma P_le_sup_D (c a : ℤ) : P c a ≤ (Icc c a).sup (D C L) := by
  rw [← sup_box hP₀ hP hC₁ hC₂]
  refine Finset.sup_le fun j hj ↦ ?_
  obtain ⟨h1, h2, h3⟩ := mem_box.1 hj
  by_cases hj' : (L : ℤ) < j.2 - j.1
  · rw [C_eq_bot hC₁ hC₂ (hloc _ _ hj')]; exact bot_le
  · exact le_trans (Finset.le_sup (f := fun u ↦ C u j.2) (mem_Icc.2 ⟨by omega, h2⟩))
      (Finset.le_sup (f := D C L) (mem_Icc.2 ⟨by omega, h3⟩))

include hP₀ hP hC₁ hC₂ in
lemma supIndep_D (m M : ℤ) : (Icc m M).SupIndep (D C L) := by
  classical
  intro t ht v hv hvt
  set Bl : ℤ → Finset (ℤ × ℤ) := fun v ↦ (Icc (v - L) v).image fun u ↦ (u, v)
  have hD : ∀ v, D C L v = (Bl v).sup fun j ↦ C j.1 j.2 := fun v ↦ by
    simp only [D, Bl, sup_image]; rfl
  have hsub : ∀ v ∈ Icc m M, Bl v ⊆ box (m - L) M := fun v hv j hj ↦ by
    obtain ⟨u, hu, rfl⟩ := mem_image.1 hj
    rw [mem_Icc] at hu hv
    exact mem_box.2 ⟨by omega, hu.2, hv.2⟩
  rw [hD, show t.sup (D C L) = (t.biUnion Bl).sup fun j ↦ C j.1 j.2 by
    rw [sup_biUnion]; exact sup_congr rfl fun v _ ↦ hD v]
  refine (supIndep_box hP₀ hP hC₁ hC₂ _ _).disjoint_sup_sup (hsub v hv) ?_ ?_
  · intro j hj
    obtain ⟨v', hv', hj⟩ := mem_biUnion.1 hj
    exact hsub v' (ht hv') hj
  · rw [disjoint_left]
    intro j hj hj'
    obtain ⟨v', hv', hj'⟩ := mem_biUnion.1 hj'
    obtain ⟨u, -, rfl⟩ := mem_image.1 hj
    obtain ⟨u', -, h⟩ := mem_image.1 hj'
    rw [Prod.ext_iff] at h
    dsimp only at h
    exact hvt (h.2 ▸ hv')

end Lattice

/-! ### Independence and projections for submodules -/

section Module

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

lemma exists_subset_Icc (s : Finset ℤ) : ∃ N : ℤ, s ⊆ Icc (-N) N := by
  refine ⟨∑ j ∈ s, |j|, fun j hj ↦ ?_⟩
  have := Finset.single_le_sum (f := fun j : ℤ ↦ |j|) (fun j _ ↦ abs_nonneg j) hj
  rw [mem_Icc]
  exact ⟨by linarith [neg_abs_le j], by linarith [le_abs_self j]⟩

lemma iSupIndep_of_supIndep_Icc {D : ℤ → Submodule R M}
    (h : ∀ m M' : ℤ, (Icc m M').SupIndep D) : iSupIndep D := by
  classical
  rw [iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero]
  intro s x hx hsum i hi
  obtain ⟨N, hs⟩ := exists_subset_Icc s
  have hdisj := h (-N) N ((erase_subset i s).trans hs) (hs hi) (notMem_erase i s)
  have hmem : x i ∈ (s.erase i).sup D := by
    have : x i = -∑ j ∈ s.erase i, x j := by
      rw [← add_sum_erase s x hi] at hsum; exact eq_neg_of_add_eq_zero_left hsum
    rw [this, Finset.sup_eq_iSup]
    exact neg_mem (Submodule.sum_mem_biSup fun j hj ↦ hx j (mem_of_mem_erase hj))
  exact (Submodule.disjoint_def.mp hdisj) _ (hx i hi) hmem

variable [IsSemisimpleModule R M] {D : ℤ → Submodule R M} (hD : iSupIndep D)

/-- A chosen complement of `⨆ v, D v`. -/
noncomputable def compl (D : ℤ → Submodule R M) : Submodule R M :=
  (exists_isCompl (⨆ v, D v)).choose

lemma isCompl_compl (D : ℤ → Submodule R M) : IsCompl (⨆ v, D v) (compl D) :=
  (exists_isCompl (⨆ v, D v)).choose_spec

include hD in
lemma isCompl_D (v : ℤ) : IsCompl (D v) ((⨆ (j) (_ : j ≠ v), D j) ⊔ compl D) := by
  refine Disjoint.isCompl_sup_right_of_isCompl_sup_left (hD v) ?_
  rw [← iSup_split_single]
  exact isCompl_compl D

/-- The projection onto `D v` along all other `D v'` and the complement of `⨆ D`. -/
noncomputable def proj (v : ℤ) : M →ₗ[R] M :=
  (D v).subtype ∘ₗ Submodule.projectionOnto _ _ (isCompl_D hD v)

lemma proj_mem (v : ℤ) (x : M) : proj hD v x ∈ D v := by
  simp [proj]

/-- (F3) -/
lemma proj_of_mem {v : ℤ} {y : M} (hy : y ∈ D v) (v' : ℤ) :
    proj hD v' y = if v' = v then y else 0 := by
  split_ifs with h
  · subst h
    exact congrArg Subtype.val (Submodule.projectionOnto_apply_left (isCompl_D hD v') ⟨y, hy⟩)
  · have : y ∈ (⨆ (j) (_ : j ≠ v'), D j) ⊔ compl D :=
      Submodule.mem_sup_left (Submodule.mem_iSup_of_mem v (Submodule.mem_iSup_of_mem (Ne.symm h) hy))
    simp [proj, Submodule.projectionOnto_apply_of_mem_right _ this]

/-- (F1) and (F2) for `x ∈ ⨆_{v ∈ s} D v`. -/
lemma proj_of_mem_iSup {s : Finset ℤ} {x : M} (hx : x ∈ ⨆ v ∈ s, D v) :
    (∀ v ∉ s, proj hD v x = 0) ∧ x = ∑ v ∈ s, proj hD v x := by
  classical
  obtain ⟨μ, rfl⟩ := (Submodule.mem_iSup_finset_iff_exists_sum D x).1 hx
  have key : ∀ v', proj hD v' (∑ v ∈ s, (μ v : M)) = if v' ∈ s then (μ v' : M) else 0 := by
    intro v'
    rw [map_sum]
    simp_rw [proj_of_mem hD (μ _).2 v']
    rw [Finset.sum_ite_eq]
  refine ⟨fun v hv ↦ by rw [key, if_neg hv], ?_⟩
  exact (Finset.sum_congr rfl fun v hv ↦ by rw [key, if_pos hv]).symm

lemma proj_eq_zero_of_mem_iSup {s : Finset ℤ} {x : M} (hx : x ∈ ⨆ v ∈ s, D v) {v : ℤ}
    (hv : v ∉ s) : proj hD v x = 0 :=
  (proj_of_mem_iSup hD hx).1 v hv

lemma sum_proj_of_mem_iSup {s : Finset ℤ} {x : M} (hx : x ∈ ⨆ v ∈ s, D v) :
    ∑ v ∈ s, proj hD v x = x :=
  (proj_of_mem_iSup hD hx).2.symm

end Module

end HSFormal.LTheory.IntervalDecomp
