import HSFormal.Cubical.GridSeam

/-!
# Cuts and face flags of cubical grids (cubical module C4, for C8)

* `coord`: the coordinates of a cell of `prodComplex n C`; a face changes exactly one coordinate
  to a face (`prodComplex_d_ne_zero`), so coordinatewise conditions on subcomplexes define
  subcomplexes (`isSub_coord`, `isSub_coord_forall`, `isSub_coord_exists`).
* **Hyperplane cut of a cube** `I_ℓ^{⊗n}` along `x_i = a`: `cube.Below`, `cube.Above` are
  subcomplexes covering the cube, meeting in the vertex level `x_i = a`.
* **Box cut of the torus** (design §2.5, first cut of §11): `B` = the closed box
  `∏ [a_i, a_i + ℓ_i]`, `A` = the closure of its complement; both are subcomplexes covering `Tⁿ`,
  meeting in `∂B` (`torus.boxCut_inter`).  `B` is the image of `torus.boxEmb`
  (`torus.boxEmb_range_iff`), contracted by `torus.inBoxContraction`.  Pulled back to
  `W = Tⁿ ⊗ CPcell` they satisfy the locality hypotheses of the excision ladder in both
  directions, so the ladder squares commute strictly (`torusCP.boxCut_ladderLeft_comm`,
  `torusCP.boxCut_ladderRight_comm`).
* **Top-face flag** of `Q = I_ℓ^{⊗(n+1)}`: `∂Q = F ∪ R` with `F = cube.Top` (first coordinate at
  the top vertex) and `R = cube.Rest`; `F ∩ R` is the image of `∂I_ℓ^{⊗n}` under the top-face
  embedding `cube.topEmb : I_ℓ^{⊗n} → F` (`cube.rest_topEmb_iff`), so the flag iterates down to
  `n = 0`, where `F` is the single vertex `+a` and `W` becomes `pt ⊗ CPcell`
  (`torusCP.duality_zero_hom_f`).
-/

namespace HSFormal.Cubical

open Matrix
open scoped Kronecker

namespace BasedComplex

variable {C D : BasedComplex}

/-! ### Coordinates -/

/-- The coordinates of a cell of an iterated tensor product. -/
def coord : (n : ℕ) → {C : Fin n → BasedComplex} → (prodComplex n C).X → (i : Fin n) → (C i).X
  | 0, _, _ => fun i ↦ i.elim0
  | n + 1, _, p => Fin.cons p.1 (coord n p.2)

@[simp] theorem coord_zero {n : ℕ} {C : Fin (n + 1) → BasedComplex}
    (p : (prodComplex (n + 1) C).X) : coord (n + 1) p 0 = p.1 := rfl

@[simp] theorem coord_succ {n : ℕ} {C : Fin (n + 1) → BasedComplex}
    (p : (prodComplex (n + 1) C).X) (i : Fin n) : coord (n + 1) p i.succ = coord n p.2 i := rfl

/-- A face of a cell of `⊗ C i` replaces exactly one coordinate by a face. -/
theorem prodComplex_d_ne_zero : (n : ℕ) → {C : Fin n → BasedComplex} →
    {σ τ : (prodComplex n C).X} → (prodComplex n C).d σ τ ≠ 0 →
    ∃ i, (C i).d (coord n σ i) (coord n τ i) ≠ 0 ∧ ∀ j, j ≠ i → coord n σ j = coord n τ j
  | 0, _, _, _, h => (h rfl).elim
  | n + 1, _, ⟨σ, σ'⟩, ⟨τ, τ'⟩, h => by
    rcases tensor_d_ne_zero h with ⟨h₁, rfl⟩ | ⟨rfl, h₂⟩
    · refine ⟨0, h₁, fun j hj ↦ ?_⟩
      obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hj
      rfl
    · obtain ⟨i, hi, hj⟩ := prodComplex_d_ne_zero n h₂
      refine ⟨i.succ, hi, fun j hj' ↦ ?_⟩
      induction j using Fin.cases with
      | zero => rfl
      | succ j => exact hj j fun h ↦ hj' (h ▸ rfl)

variable {n : ℕ} {C' : Fin n → BasedComplex}

theorem isSub_coord_forall {P : ∀ i, (C' i).X → Prop} (hP : ∀ i, (C' i).IsSub (P i)) :
    (prodComplex n C').IsSub fun σ ↦ ∀ i, P i (coord n σ i) := by
  intro σ τ h hτ i
  obtain ⟨k, hk, hj⟩ := prodComplex_d_ne_zero n h
  by_cases hik : i = k
  · subst hik; exact hP i _ _ hk (hτ i)
  · rw [hj i hik]; exact hτ i

theorem isSub_coord_exists {P : ∀ i, (C' i).X → Prop} (hP : ∀ i, (C' i).IsSub (P i)) :
    (prodComplex n C').IsSub fun σ ↦ ∃ i, P i (coord n σ i) := by
  rintro σ τ h ⟨i, hi⟩
  obtain ⟨k, hk, hj⟩ := prodComplex_d_ne_zero n h
  refine ⟨i, ?_⟩
  by_cases hik : i = k
  · subst hik; exact hP i _ _ hk hi
  · rw [hj i hik]; exact hi

theorem isSub_coord (i : Fin n) {P : (C' i).X → Prop} (hP : (C' i).IsSub P) :
    (prodComplex n C').IsSub fun σ ↦ P (coord n σ i) := by
  intro σ τ h hτ
  obtain ⟨k, hk, hj⟩ := prodComplex_d_ne_zero n h
  by_cases hik : i = k
  · subst hik; exact hP _ _ hk hτ
  · rw [hj i hik]; exact hτ

theorem isSub_snd {B : D.X → Prop} (hB : D.IsSub B) : (C.tensor D).IsSub fun p ↦ B p.2 := by
  rintro ⟨σ, σ'⟩ ⟨τ, τ'⟩ h hτ
  rcases tensor_d_ne_zero h with ⟨-, rfl⟩ | ⟨-, h₂⟩
  · exact hτ
  · exact hB _ _ h₂ hτ

theorem IsSub.or {P Q : C.X → Prop} (hP : C.IsSub P) (hQ : C.IsSub Q) :
    C.IsSub fun σ ↦ P σ ∨ Q σ :=
  fun σ τ h ↦ Or.imp (hP σ τ h) (hQ σ τ h)

/-- A vertex predicate (no faces below vertices) is a subcomplex. -/
theorem isSub_of_deg_zero {P : C.X → Prop} (hP : ∀ σ, P σ → C.deg σ = 0) : C.IsSub P :=
  fun σ τ h hτ ↦ by have := C.d_deg σ τ h; have := hP τ hτ; omega

/-! ### Arcs of the circle and the box cut of the torus -/

section Torus

variable (m : ℕ) [NeZero m]

theorem fin_val_add_one {x : Fin m} :
    ((x + 1 : Fin m) : ℕ) = if (x : ℕ) + 1 < m then (x : ℕ) + 1 else 0 := by
  rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [show (x : ℕ) + 1 = m by have := x.2; omega, Nat.mod_self]

/-- The closed arc `[a, a + ℓ]` of `C_m`: vertices at offset `≤ ℓ`, edges at offset `< ℓ`. -/
def circle.InArc (a : Fin m) (ℓ : ℕ) : (circle m).X → Prop
  | .inl v => ((v - a : Fin m) : ℕ) ≤ ℓ
  | .inr e => ((e - a : Fin m) : ℕ) < ℓ

/-- The cells off the open arc `(a, a + ℓ)`. -/
def circle.OffArc (a : Fin m) (ℓ : ℕ) : (circle m).X → Prop
  | .inl v => ((v - a : Fin m) : ℕ) = 0 ∨ ℓ ≤ ((v - a : Fin m) : ℕ)
  | .inr e => ℓ ≤ ((e - a : Fin m) : ℕ)

theorem circle.face_cases {σ τ : (circle m).X} (h : (circle m).d σ τ ≠ 0) :
    ∃ v e, σ = .inl v ∧ τ = .inr e ∧ (v = e ∨ v = e + 1) := by
  have := circle.adj_of_d m h
  rcases σ with v | e <;> rcases τ with w | f <;> simp only [circle.Adj] at this
  · exact ⟨v, f, rfl, rfl, this⟩
  · simp at h

theorem circle.sub_succ (e a : Fin m) : e + 1 - a = (e - a) + 1 := by abel

theorem circle.isSub_inArc (a : Fin m) {ℓ : ℕ} (hℓ : ℓ < m) :
    (circle m).IsSub (circle.InArc m a ℓ) := by
  intro σ τ h hτ
  obtain ⟨v, e, rfl, rfl, rfl | rfl⟩ := circle.face_cases m h
  · exact le_of_lt hτ
  · change ((e + 1 - a : Fin m) : ℕ) ≤ ℓ
    change ((e - a : Fin m) : ℕ) < ℓ at hτ
    rw [circle.sub_succ, fin_val_add_one, ite_eq_left (by omega)]
    omega

theorem circle.isSub_offArc (a : Fin m) (ℓ : ℕ) : (circle m).IsSub (circle.OffArc m a ℓ) := by
  intro σ τ h hτ
  obtain ⟨v, e, rfl, rfl, rfl | rfl⟩ := circle.face_cases m h
  · exact .inr hτ
  · change ((e + 1 - a : Fin m) : ℕ) = 0 ∨ ℓ ≤ ((e + 1 - a : Fin m) : ℕ)
    change ℓ ≤ ((e - a : Fin m) : ℕ) at hτ
    rw [circle.sub_succ, fin_val_add_one]
    split_ifs
    · exact .inr (by omega)
    · exact .inl rfl

theorem circle.offArc_or_inArc (a : Fin m) (ℓ : ℕ) (σ : (circle m).X) :
    circle.OffArc m a ℓ σ ∨ circle.InArc m a ℓ σ := by
  rcases σ with v | e
  · by_cases h : ((v - a : Fin m) : ℕ) ≤ ℓ
    · exact .inr h
    · exact .inl (.inr (by omega))
  · exact (le_or_gt ℓ _).imp id id

variable (n : ℕ) (a : Fin n → Fin m) (ℓ : Fin n → ℕ)

/-- The closed box `∏ [a_i, a_i + ℓ_i]` of `Tⁿ` (the B-side of the first cut of §11). -/
def torus.InBox (σ : (torus m n).X) : Prop := ∀ i, circle.InArc m (a i) (ℓ i) (coord n σ i)

/-- The closure of the complement of the open box (the A-side). -/
def torus.OffBox (σ : (torus m n).X) : Prop := ∃ i, circle.OffArc m (a i) (ℓ i) (coord n σ i)

theorem torus.isSub_inBox (hℓ : ∀ i, ℓ i < m) : (torus m n).IsSub (torus.InBox m n a ℓ) :=
  isSub_coord_forall fun i ↦ circle.isSub_inArc m (a i) (hℓ i)

theorem torus.isSub_offBox : (torus m n).IsSub (torus.OffBox m n a ℓ) :=
  isSub_coord_exists fun i ↦ circle.isSub_offArc m (a i) (ℓ i)

theorem torus.offBox_or_inBox (σ : (torus m n).X) :
    torus.OffBox m n a ℓ σ ∨ torus.InBox m n a ℓ σ := by
  by_cases h : ∃ i, circle.OffArc m (a i) (ℓ i) (coord n σ i)
  · exact .inl h
  · push_neg at h
    exact .inr fun i ↦ (circle.offArc_or_inArc m (a i) (ℓ i) _).resolve_left (h i)

/-- The interface `Σ = A ∩ B = ∂B`: all coordinates in the closed arcs, one at an end vertex. -/
theorem torus.boxCut_inter (σ : (torus m n).X) :
    torus.OffBox m n a ℓ σ ∧ torus.InBox m n a ℓ σ ↔ torus.InBox m n a ℓ σ ∧
      ∃ i v, coord n σ i = .inl v ∧
        (((v - a i : Fin m) : ℕ) = 0 ∨ ((v - a i : Fin m) : ℕ) = ℓ i) := by
  constructor
  · rintro ⟨⟨i, hi⟩, hB⟩
    refine ⟨hB, i, ?_⟩
    have hBi := hB i
    generalize coord n σ i = x at hi hBi ⊢
    rcases x with v | e
    · rcases hi with h | h
      · exact ⟨v, rfl, .inl h⟩
      · exact ⟨v, rfl, .inr (le_antisymm hBi h)⟩
    · exact absurd hi (not_le.mpr hBi)
  · rintro ⟨hB, i, v, hv, h⟩
    refine ⟨⟨i, ?_⟩, hB⟩
    rw [hv]
    exact h.imp id ge_of_eq

/-! ### Boxes are the boxes of `Contraction` -/

theorem CellEmbedding.prod_range_iff : (n : ℕ) → {Y C : Fin n → BasedComplex} →
    (e : ∀ i, CellEmbedding (Y i) (C i)) → (σ : (prodComplex n C).X) →
    (CellEmbedding.prod n e).range σ ↔ ∀ i, (e i).range (coord n σ i)
  | 0, _, _, _, _ => ⟨fun _ i ↦ i.elim0, fun _ ↦ ⟨(), rfl⟩⟩
  | n + 1, _, _, e, ⟨σ, σ'⟩ => by
    constructor
    · rintro ⟨⟨τ, τ'⟩, h⟩ i
      obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
      induction i using Fin.cases with
      | zero => exact ⟨τ, h₁⟩
      | succ i => exact (CellEmbedding.prod_range_iff n (fun i ↦ e i.succ) σ').mp ⟨τ', h₂⟩ i
    · intro h
      obtain ⟨τ, hτ⟩ := h 0
      obtain ⟨τ', hτ'⟩ := (CellEmbedding.prod_range_iff n (fun i ↦ e i.succ) σ').mpr
        fun i ↦ h i.succ
      exact ⟨(τ, τ'), Prod.ext hτ hτ'⟩

theorem circle.arc_range_iff (a : Fin m) (ℓ : ℕ) (h : ℓ < m) (σ : (circle m).X) :
    (circle.arc m a ℓ h).range σ ↔ circle.InArc m a ℓ σ := by
  constructor
  · rintro ⟨τ | τ, rfl⟩
    · change ((a + Fin.castLE _ τ - a : Fin m) : ℕ) ≤ ℓ
      rw [add_sub_cancel_left, Fin.val_castLE]; omega
    · change ((a + Fin.castLE _ τ - a : Fin m) : ℕ) < ℓ
      rw [add_sub_cancel_left, Fin.val_castLE]; exact τ.2
  · rcases σ with v | e
    · intro hv
      refine ⟨.inl ⟨((v - a : Fin m) : ℕ), by change _ ≤ ℓ at hv; omega⟩, ?_⟩
      change Sum.inl (a + Fin.castLE _ _) = Sum.inl v
      rw [show Fin.castLE _ _ = v - a from Fin.ext rfl, add_sub_cancel]
    · intro he
      refine ⟨.inr ⟨((e - a : Fin m) : ℕ), he⟩, ?_⟩
      change Sum.inr (a + Fin.castLE _ _) = Sum.inr e
      rw [show Fin.castLE _ _ = e - a from Fin.ext rfl, add_sub_cancel]

/-- `torus.InBox` is the image of the box embedding `torus.boxEmb` of `Contraction`. -/
theorem torus.boxEmb_range_iff (h : ∀ i, ℓ i < m) (σ : (torus m n).X) :
    (torus.boxEmb m a ℓ h).range σ ↔ torus.InBox m n a ℓ σ :=
  (CellEmbedding.prod_range_iff n _ σ).trans
    (forall_congr' fun i ↦ circle.arc_range_iff m (a i) (ℓ i) (h i) _)

/-- Transport a contraction of a subcomplex along an equivalence of predicates. -/
def SubContraction.congr {P Q : C.X → Prop} (S : SubContraction C P) (h : ∀ σ, P σ ↔ Q σ) :
    SubContraction C Q where
  s := S.s
  deg1 := S.deg1
  supp σ τ hs := ⟨(h σ).mp (S.supp σ τ hs).1, (h τ).mp (S.supp σ τ hs).2⟩
  base := S.base
  base_mem := (h _).mp S.base_mem
  base_deg := S.base_deg
  eq σ τ hτ := S.eq σ τ ((h τ).mpr hτ)

/-- The exact cone contraction of the box `∏ [a_i, a_i + ℓ_i]` of `Tⁿ` (the B-side). -/
def torus.inBoxContraction (h : ∀ i, ℓ i < m) : SubContraction (torus m n) (torus.InBox m n a ℓ) :=
  (torus.boxContraction m a ℓ h).congr (torus.boxEmb_range_iff m n a ℓ h)

/-! ### Ladder compatibility for `W = Tⁿ ⊗ CPcell` -/

/-- The pullback `W_A = A ⊗ CP` of the box cut. -/
abbrev torusCP.WA (σ : (torusCP m n).X) : Prop := torus.OffBox m n a ℓ σ.1

/-- The pullback `W_B = B ⊗ CP` of the box cut. -/
abbrev torusCP.WB (σ : (torusCP m n).X) : Prop := torus.InBox m n a ℓ σ.1

theorem torusCP.isSub_WA : (torusCP m n).IsSub (torusCP.WA m n a ℓ) :=
  isSub_fst (torus.isSub_offBox m n a ℓ)

theorem torusCP.isSub_WB (hℓ : ∀ i, ℓ i < m) : (torusCP m n).IsSub (torusCP.WB m n a ℓ) :=
  isSub_fst (torus.isSub_inBox m n a ℓ hℓ)

variable {m n a ℓ}

/-- Locality of `φ_W` for the box cut, in both directions of the ladder (`m ≥ 2`). -/
theorem torusCP.boxCut_local (hm : 2 ≤ m) (hℓ : ∀ i, ℓ i < m) (σ τ : (torusCP m n).X)
    (h : (torusCP.duality m n).hom.f σ τ ≠ 0) :
    (¬torusCP.WB m n a ℓ τ → torusCP.WA m n a ℓ σ) ∧
      (¬torusCP.WA m n a ℓ τ → torusCP.WB m n a ℓ σ) :=
  ⟨torusCP.local m n hm (torus.isSub_offBox m n a ℓ) (torus.isSub_inBox m n a ℓ hℓ)
      (torus.offBox_or_inBox m n a ℓ) σ τ h,
    torusCP.local m n hm (torus.isSub_inBox m n a ℓ hℓ) (torus.isSub_offBox m n a ℓ)
      (fun σ ↦ (torus.offBox_or_inBox m n a ℓ σ).symm) σ τ h⟩

open Classical in
/-- **Strict excision ladder for the box cut, left square**: `z ∩` on `C^{N-*}(W, W_B)` lands in
`C(W_A)`. -/
theorem torusCP.boxCut_ladderLeft_comm (hm : 2 ≤ m) (hℓ : ∀ i, ℓ i < m) :
    (inclHom (torusCP.isSub_WA m n a ℓ)).comp (ladderLeft (torusCP.dimLE m n)
      (torusCP.duality m n).hom (torusCP.isSub_WA m n a ℓ) (torusCP.isSub_WB m n a ℓ hℓ)
        fun σ τ h ↦ (torusCP.boxCut_local hm hℓ σ τ h).1) =
    (torusCP.duality m n).hom.comp ((projHom (torusCP.isSub_WB m n a ℓ hℓ)).dual (n + 4)
      (torusCP.dimLE m n) ((torusCP.dimLE m n).restrict _ _)) :=
  ladderLeft_comm _ _ _ _ _

open Classical in
/-- **Strict excision ladder for the box cut, right square**: `(z ∩ ξ) mod W_A` depends only on
`ξ | W_B`; the right column is the B-pair map `C^{N-*}(W_B) → C(W_B, Σ)`. -/
theorem torusCP.boxCut_ladderRight_comm (hm : 2 ≤ m) (hℓ : ∀ i, ℓ i < m) :
    (projHom (torusCP.isSub_WA m n a ℓ)).comp (torusCP.duality m n).hom =
    (ladderRight (torusCP.dimLE m n) (torusCP.duality m n).hom (torusCP.isSub_WA m n a ℓ)
      (torusCP.isSub_WB m n a ℓ hℓ) fun σ τ h ↦ (torusCP.boxCut_local hm hℓ σ τ h).1).comp
      ((inclHom (torusCP.isSub_WB m n a ℓ hℓ)).dual (n + 4) ((torusCP.dimLE m n).restrict _ _)
        (torusCP.dimLE m n)) :=
  ladderRight_comm _ _ _ _ _

end Torus

/-! ### The interval: positions, ends and the hyperplane cut of a cube -/

section Cube

variable {ℓ : ℕ}

/-- The left end of a cell of `I_ℓ`. -/
def interval.lo : (interval ℓ).X → ℕ
  | .inl v => v
  | .inr e => e

/-- The right end of a cell of `I_ℓ`. -/
def interval.hi : (interval ℓ).X → ℕ
  | .inl v => v
  | .inr e => e + 1

theorem interval.face_le {σ τ : (interval ℓ).X} (h : (interval ℓ).d σ τ ≠ 0) :
    interval.lo τ ≤ interval.lo σ ∧ interval.hi σ ≤ interval.hi τ := by
  rcases σ with v | e <;> rcases τ with w | f <;> simp at h
  have : v = f.succ ∨ v = f.castSucc := by
    by_contra h'; push_neg at h'; exact h (by simp [h'.1, h'.2])
  rcases this with rfl | rfl <;> simp [interval.lo, interval.hi]

theorem interval.isSub_hi_le (a : ℕ) : (interval ℓ).IsSub fun σ ↦ interval.hi σ ≤ a :=
  fun _ _ h hτ ↦ (interval.face_le h).2.trans hτ

theorem interval.isSub_le_lo (a : ℕ) : (interval ℓ).IsSub fun σ ↦ a ≤ interval.lo σ :=
  fun _ _ h hτ ↦ hτ.trans (interval.face_le h).1

variable (ℓ) {n : ℕ}

/-- The half-cube `x_i ≤ a` of `I_ℓ^{⊗n}`. -/
def cube.Below (i : Fin n) (a : ℕ) (σ : (cube ℓ n).X) : Prop := interval.hi (coord n σ i) ≤ a

/-- The half-cube `x_i ≥ a` of `I_ℓ^{⊗n}`. -/
def cube.Above (i : Fin n) (a : ℕ) (σ : (cube ℓ n).X) : Prop := a ≤ interval.lo (coord n σ i)

theorem cube.isSub_below (i : Fin n) (a : ℕ) : (cube ℓ n).IsSub (cube.Below ℓ i a) :=
  isSub_coord (C' := fun _ ↦ interval ℓ) (P := fun x ↦ interval.hi x ≤ a) i
    (interval.isSub_hi_le a)

theorem cube.isSub_above (i : Fin n) (a : ℕ) : (cube ℓ n).IsSub (cube.Above ℓ i a) :=
  isSub_coord (C' := fun _ ↦ interval ℓ) (P := fun x ↦ a ≤ interval.lo x) i
    (interval.isSub_le_lo a)

/-- **Hyperplane cut**: the half-cubes cover the cube. -/
theorem cube.below_or_above (i : Fin n) (a : ℕ) (σ : (cube ℓ n).X) :
    cube.Below ℓ i a σ ∨ cube.Above ℓ i a σ := by
  unfold cube.Below cube.Above
  rcases coord n σ i with v | e <;> simp only [interval.lo, interval.hi] <;> omega

/-- The half-cubes meet in the vertex level `x_i = a`. -/
theorem cube.below_and_above_iff (i : Fin n) (a : ℕ) (σ : (cube ℓ n).X) :
    cube.Below ℓ i a σ ∧ cube.Above ℓ i a σ ↔ ∃ v, coord n σ i = .inl v ∧ (v : ℕ) = a := by
  unfold cube.Below cube.Above
  rcases coord n σ i with v | e
  · simp only [interval.lo, interval.hi, Sum.inl.injEq, exists_eq_left']
    omega
  · simp only [interval.lo, interval.hi, reduceCtorEq, false_and, exists_false, iff_false]
    omega

/-! ### The top-face flag -/

/-- The end vertices `∂I_ℓ = {v₀, v_ℓ}`. -/
def interval.IsVEnd (σ : (interval ℓ).X) : Prop := σ = .inl 0 ∨ σ = .inl (Fin.last ℓ)

theorem interval.isSub_isVEnd : (interval ℓ).IsSub (interval.IsVEnd ℓ) :=
  isSub_of_deg_zero fun σ h ↦ by rcases h with rfl | rfl <;> rfl

/-- The boundary `∂Q` of `Q = I_ℓ^{⊗n}`: some coordinate at an end vertex. -/
def cube.Bdry (σ : (cube ℓ n).X) : Prop := ∃ i, interval.IsVEnd ℓ (coord n σ i)

theorem cube.isSub_bdry : (cube ℓ n).IsSub (cube.Bdry ℓ (n := n)) :=
  isSub_coord_exists fun _ ↦ interval.isSub_isVEnd ℓ

theorem cube.bdry_succ_iff (σ : (cube ℓ (n + 1)).X) :
    cube.Bdry ℓ σ ↔ interval.IsVEnd ℓ σ.1 ∨ cube.Bdry ℓ σ.2 := by
  constructor
  · rintro ⟨i, hi⟩
    induction i using Fin.cases with
    | zero => exact .inl hi
    | succ i => exact .inr ⟨i, hi⟩
  · rintro (h | ⟨i, hi⟩)
    · exact ⟨0, h⟩
    · exact ⟨i.succ, hi⟩

/-- The top face `F = {x_0 = ℓ}` of `I_ℓ^{⊗(n+1)}`. -/
def cube.Top (σ : (cube ℓ (n + 1)).X) : Prop := σ.1 = .inl (Fin.last ℓ)

/-- The rest `R` of `∂Q`: the bottom face `x_0 = 0` and the faces of the other coordinates. -/
def cube.Rest (σ : (cube ℓ (n + 1)).X) : Prop := σ.1 = .inl 0 ∨ cube.Bdry ℓ σ.2

theorem interval.isSub_eq_inl (v : Fin (ℓ + 1)) : (interval ℓ).IsSub fun σ ↦ σ = .inl v :=
  isSub_of_deg_zero fun σ h ↦ by rw [h]; rfl

theorem cube.isSub_top : (cube ℓ (n + 1)).IsSub (cube.Top ℓ (n := n)) :=
  isSub_fst (C := interval ℓ) (D := cube ℓ n) (interval.isSub_eq_inl ℓ (Fin.last ℓ))

theorem cube.isSub_rest : (cube ℓ (n + 1)).IsSub (cube.Rest ℓ (n := n)) :=
  IsSub.or (isSub_fst (C := interval ℓ) (D := cube ℓ n) (interval.isSub_eq_inl ℓ 0))
    (isSub_snd (C := interval ℓ) (D := cube ℓ n) (cube.isSub_bdry ℓ))

/-- `∂Q = F ∪ R`. -/
theorem cube.bdry_iff_top_or_rest (σ : (cube ℓ (n + 1)).X) :
    cube.Bdry ℓ σ ↔ cube.Top ℓ σ ∨ cube.Rest ℓ σ := by
  rw [cube.bdry_succ_iff]
  unfold interval.IsVEnd cube.Top cube.Rest
  tauto

/-- `F ∩ R = ∂F`: the top face with another coordinate at an end vertex (`ℓ ≥ 1`). -/
theorem cube.top_and_rest_iff (hℓ : 1 ≤ ℓ) (σ : (cube ℓ (n + 1)).X) :
    cube.Top ℓ σ ∧ cube.Rest ℓ σ ↔ cube.Top ℓ σ ∧ cube.Bdry ℓ σ.2 := by
  unfold cube.Top cube.Rest
  constructor
  · rintro ⟨h, h' | h'⟩
    · rw [h] at h'
      exact absurd (congrArg Fin.val (Sum.inl_injective h')) (by simp; omega)
    · exact ⟨h, h'⟩
  · rintro ⟨h, h'⟩; exact ⟨h, .inr h'⟩

/-- The top-face embedding `I_ℓ^{⊗n} ≅ F ⊆ I_ℓ^{⊗(n+1)}`, `σ ↦ v_ℓ ⊗ σ`. -/
def cube.topEmb : CellEmbedding (cube ℓ n) (cube ℓ (n + 1)) where
  toFun σ := (.inl (Fin.last ℓ), σ)
  inj _ _ h := (Prod.mk.inj h).2
  deg_eq _ := by simp [prodComplex]
  d_eq σ τ := by
    change (interval ℓ).d _ _ * (1 : Matrix _ _ ℚ) σ τ +
      (interval ℓ).sgn (.inl (Fin.last ℓ)) (.inl (Fin.last ℓ)) * (cube ℓ n).d σ τ = _
    simp [sgn]
  closed := by
    rintro ⟨ρ, ρ'⟩ τ h
    rcases tensor_d_ne_zero h with ⟨h₁, rfl⟩ | ⟨rfl, -⟩
    · exact absurd h₁ (by rcases ρ with _ | _ <;> simp)
    · exact ⟨ρ', rfl⟩

theorem cube.top_iff_range (σ : (cube ℓ (n + 1)).X) : cube.Top ℓ σ ↔ (cube.topEmb ℓ).range σ :=
  ⟨fun h ↦ ⟨σ.2, by obtain ⟨σ₁, σ₂⟩ := σ; change σ₁ = _ at h; subst h; rfl⟩,
    by rintro ⟨τ, rfl⟩; rfl⟩

/-- **The flag iterates**: `R ∩ F` pulls back to `∂I_ℓ^{⊗n}` under the top-face embedding, so
`(F, F ∩ R) ≅ (I_ℓ^{⊗n}, ∂I_ℓ^{⊗n})` (`ℓ ≥ 1`). -/
theorem cube.rest_topEmb_iff (hℓ : 1 ≤ ℓ) (σ : (cube ℓ n).X) :
    cube.Rest ℓ ((cube.topEmb ℓ).toFun σ) ↔ cube.Bdry ℓ σ := by
  have h := (cube.top_and_rest_iff ℓ hℓ ((cube.topEmb ℓ).toFun σ))
  exact ⟨fun h' ↦ (h.mp ⟨rfl, h'⟩).2, fun h' ↦ (h.mpr ⟨rfl, h'⟩).2⟩

/-- At the bottom of the flag (`n = 0`), the top face of `∂I_ℓ` is the single vertex `v_ℓ`. -/
theorem cube.top_zero_iff (σ : (cube ℓ 1).X) : cube.Top ℓ σ ↔ σ = (.inl (Fin.last ℓ), ()) := by
  obtain ⟨σ, ⟨⟩⟩ := σ
  exact ⟨fun h ↦ by change σ = _ at h; rw [h], fun h ↦ congrArg Prod.fst h⟩

end Cube

theorem torus.duality_zero_hom_f (m : ℕ) [NeZero m] : (torus.duality m 0).hom.f = 1 := rfl

/-- `W` for `n = 0` is `pt ⊗ CPcell`, with duality `(1 ⊗ φ_CP) Θ`: the end of the flag. -/
theorem torusCP.duality_zero_hom_f (m : ℕ) [NeZero m] :
    (torusCP.duality m 0).hom.f = (1 ⊗ₖ CPcell.φ.f) * koszul (torus m 0) CPcell 4 := by
  rw [torusCP.duality, SymDuality.tensor_hom_f, torus.duality_zero_hom_f]; rfl

end BasedComplex

end HSFormal.Cubical
