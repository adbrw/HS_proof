import HSFormal.Cubical.PinchLocal
import HSFormal.Cubical.GridSeam

/-!
# Propagation of the local cube pair dualities (cubical module C8, controlled B-pairs)

Radii of homotopy equivalences (`HtpyEquiv.PropLE` of `GridSeam`) survive Ranicki
transposition (`HtpyEquiv.PropLE.transpose`) and changing the map along a homotopy
(`HtpyEquiv.PropLE.ofHtpy`).  For the arc `[a, a + m + 1]` of `C_M` on `ℝ/Lℤ` with centre labels
the local interval pair duality has radii `η/2` (maps) and `η` (homotopies), `η = L/M` the mesh
(`interval.symAbsDualityLoc_propLE`), and so do the tensor products
(`cube.symAbsDualityLoc_propLE`, `cubeCP.symAbsDualityLoc_propLE`): **the B-pair duality of a
box cut is controlled**, with radii tending to `0` with the mesh, uniformly in the side length of
the box.
-/

noncomputable section

namespace HSFormal.Cubical

open Matrix
open scoped Kronecker ENNReal

namespace BasedComplex

section Transport

variable {E : Type*} [PseudoEMetricSpace E]

/-- Radii survive Ranicki transposition (the labels swap sides). -/
theorem HtpyEquiv.PropLE.transpose {C D : BasedComplex} {N : ℕ} {hC : C.DimLE N}
    {hD : D.DimLE N} {e : HtpyEquiv (C.dual N hC) D} {a : C.X → E} {b : D.X → E}
    {r s : ℝ≥0∞} (he : e.PropLE a b r s) : (e.transpose hC hD).PropLE b a r s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change prop (C.eps N * e.hom.fᵀ) b a ≤ r
    exact prop_mul_le_of_le (prop_transpose.trans_le he.hom) (prop_diagonal_le _ _)
      (by rw [add_zero])
  · change prop (e.inv.fᵀ * C.eps N) a b ≤ r
    exact prop_mul_le_of_le (prop_diagonal_le _ _) (prop_transpose.trans_le he.inv)
      (by rw [zero_add])
  · rw [HtpyEquiv.transpose, HtpyEquiv.trans_homInv_h]
    simp [bidualEquiv, HtpyEquiv.dual]
    change prop ((-(-1 : ℚ) ^ N) • (e.invHom.hᵀ * D.sgn)) b b ≤ s
    exact (prop_smul_le _).trans (prop_mul_le_of_le (prop_diagonal_le _ _)
      (prop_transpose.trans_le he.invHom) (by rw [zero_add]))
  · rw [HtpyEquiv.transpose, HtpyEquiv.trans_invHom_h]
    simp [bidualEquiv, HtpyEquiv.dual]
    change prop (C.eps N * (((-(-1 : ℚ) ^ N) • (e.homInv.hᵀ * (C.dual N hC).sgn)) * C.eps N))
      a a ≤ s
    refine prop_mul_le_of_le (prop_mul_le_of_le (prop_diagonal_le _ _) ((prop_smul_le _).trans
      (prop_mul_le_of_le (prop_diagonal_le _ _) (prop_transpose.trans_le he.homInv)
        (by rw [zero_add]))) (by rw [zero_add])) (prop_diagonal_le _ _) (by rw [add_zero])

/-- Radii survive replacing the map by a homotopic one (`HtpyEquiv.ofHtpy`). -/
theorem HtpyEquiv.PropLE.ofHtpy {A B : BasedComplex} {e : HtpyEquiv A B} {f : Hom A B}
    (H : Htpy e.hom f) {a : A.X → E} {b : B.X → E} {r s t : ℝ≥0∞} (he : e.PropLE a b r s)
    (hf : prop f.f a b ≤ r) (hH : prop H.h a b ≤ t) (hrt : r + t ≤ s) :
    (e.ofHtpy H).PropLE a b r s := by
  refine ⟨hf, he.inv, ?_, ?_⟩
  · change prop (e.inv.f * -H.h + e.homInv.h) a a ≤ s
    exact prop_add_le.trans (max_le (prop_mul_le_of_le (prop_neg.trans_le hH) he.inv
      (by rw [add_comm]; exact hrt)) he.homInv)
  · change prop (-H.h * e.inv.f + e.invHom.h) b b ≤ s
    exact prop_add_le.trans (max_le (prop_mul_le_of_le he.inv (prop_neg.trans_le hH) hrt)
      he.invHom)

end Transport

/-! ### The interval inside an arc -/

section Arc

variable (L : ℝ) [Fact (0 < L)] (M m : ℕ) [NeZero M] (h : m + 1 < M) (a : Fin M)

/-- Cells of `I_{m+1}` that are faces of each other. -/
def interval.Adj : (interval (m + 1)).X → (interval (m + 1)).X → Prop
  | .inl v, .inr e => v = e.castSucc ∨ v = e.succ
  | .inr e, .inl v => v = e.castSucc ∨ v = e.succ
  | _, _ => False

theorem circle.arc_adj {x y : (interval (m + 1)).X} (hxy : interval.Adj m x y) :
    circle.Adj M ((circle.arc M a (m + 1) h).toFun x) ((circle.arc M a (m + 1) h).toFun y) := by
  have key : ∀ (v : Fin (m + 2)) (e : Fin (m + 1)), v = e.castSucc ∨ v = e.succ →
      (a + Fin.castLE (by omega) v : Fin M) = a + Fin.castLE (by omega) e ∨
        (a + Fin.castLE (by omega) v : Fin M) = a + Fin.castLE (by omega) e + 1 := by
    rintro v e (rfl | rfl)
    · exact .inl (congrArg (a + ·) (Fin.ext rfl))
    · refine .inr ?_
      rw [add_assoc]
      congr 1
      ext
      simp only [Fin.val_add, Fin.val_castLE, Fin.val_succ, Fin.val_one', Nat.add_mod_mod]
      exact (Nat.mod_eq_of_lt (by have := e.2; omega)).symm
  rcases x with v | e <;> rcases y with w | f <;> simp only [interval.Adj] at hxy
  · exact key v f hxy
  · exact key w e hxy

/-- The centre labels of the arc. -/
def interval.arcLabel : (interval (m + 1)).X → AddCircle L :=
  circle.center L M ∘ (circle.arc M a (m + 1) h).toFun

variable {L M m h a}

/-- Matrices supported on faces have radius `η/2`. -/
theorem interval.prop_le_of_adj {A B : Type*} {α : A → (interval (m + 1)).X}
    {β : B → (interval (m + 1)).X} {u : Matrix B A ℚ}
    (hu : ∀ b a', u b a' ≠ 0 → interval.Adj m (β b) (α a')) :
    prop u (interval.arcLabel L M m h a ∘ α) (interval.arcLabel L M m h a ∘ β) ≤
      ENNReal.ofReal (mesh L M / 2) :=
  prop_le_iff.mpr fun b a' hba ↦ circle.edist_center_le L M (circle.arc_adj M m h a (hu b a' hba))

omit [Fact (0 < L)] in
/-- Matrices supported on the diagonal have radius `0`. -/
theorem interval.prop_le_of_eq {A B : Type*} {α : A → (interval (m + 1)).X}
    {β : B → (interval (m + 1)).X} {u : Matrix B A ℚ} (hu : ∀ b a', u b a' ≠ 0 → β b = α a')
    {r : ℝ≥0∞} : prop u (interval.arcLabel L M m h a ∘ α) (interval.arcLabel L M m h a ∘ β) ≤ r :=
  prop_le_iff.mpr fun b a' hba ↦ by
    rw [Function.comp_apply, Function.comp_apply, hu b a' hba, edist_self]
    exact zero_le

theorem interval.half_le_mesh : ENNReal.ofReal (mesh L M / 2) ≤ ENNReal.ofReal (mesh L M) :=
  ENNReal.ofReal_le_ofReal (by linarith [mesh_pos L M])

theorem interval.half_add_half :
    ENNReal.ofReal (mesh L M / 2) + ENNReal.ofReal (mesh L M / 2) ≤ ENNReal.ofReal (mesh L M) := by
  rw [← ENNReal.ofReal_add (by linarith [mesh_pos L M]) (by linarith [mesh_pos L M])]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **Radii of the local relative cap**: `F`, `g` and the homotopy `h` join faces. -/
theorem interval.relDualityLoc_propLE :
    (interval.relDualityLoc m).PropLE (interval.arcLabel L M m h a ∘ Subtype.val)
      (interval.arcLabel L M m h a) (ENNReal.ofReal (mesh L M / 2))
      (ENNReal.ofReal (mesh L M)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine interval.prop_le_of_adj (β := id) fun σ τ hστ ↦ ?_
    change (interval.capRel m).f σ τ ≠ 0 at hστ
    rw [interval.capRel_f_eq] at hστ
    rcases σ with v | e <;> rcases τ with ⟨w | f, hτ⟩ <;>
      simp [interval.capFull] at hστ <;> simp [interval.Adj, hστ]
  · refine interval.prop_le_of_adj (α := id) fun τ σ hστ ↦ ?_
    change interval.locG m τ.1 σ ≠ 0 at hστ
    obtain ⟨τ, hτ⟩ := τ
    rcases τ with v | e <;> rcases σ with w | f <;> simp [interval.locG] at hστ
    · simp [interval.Adj, hστ.1]
    · by_cases h₁ : w = e.castSucc
      · simp [interval.Adj, h₁]
      · rw [if_neg h₁, zero_add] at hστ
        have := (ite_ne_right_iff.mp hστ).1
        simp [interval.Adj, this.2, this.1]
  · change prop (Htpy.ofEq _).h _ _ ≤ _
    erw [Htpy.ofEq_h, prop_zero]
    exact zero_le
  · refine (interval.prop_le_of_adj (α := id) (β := id) fun τ σ hστ ↦ ?_).trans
      interval.half_le_mesh
    change interval.locH m τ σ ≠ 0 at hστ
    rcases τ with v | e <;> rcases σ with w | f <;> simp [interval.locH] at hστ
    simp [interval.Adj, hστ.1, hστ.2]

/-- Radii of the symmetric local pair duality. -/
theorem interval.symRelDualityLoc_propLE :
    (interval.symRelDualityLoc m).PropLE (interval.arcLabel L M m h a ∘ Subtype.val)
      (interval.arcLabel L M m h a) (ENNReal.ofReal (mesh L M / 2))
      (ENNReal.ofReal (mesh L M)) := by
  refine HtpyEquiv.PropLE.ofHtpy (t := 0) _ interval.relDualityLoc_propLE ?_ ?_ ?_
  · refine interval.prop_le_of_adj (β := id) fun σ τ hστ ↦ ?_
    change (interval.symCapRel m).f σ τ ≠ 0 at hστ
    rw [interval.symCapRel_f, submatrix_apply] at hστ
    obtain ⟨τ, hτ⟩ := τ
    rcases σ with v | e <;> rcases τ with w | f <;> simp [interval.symMat] at hστ
    · by_cases h₁ : v = f.castSucc
      · simp [interval.Adj, h₁]
      · simp [h₁] at hστ; simp [interval.Adj, hστ]
    · by_cases h₁ : w = e.succ
      · simp [interval.Adj, h₁]
      · simp [h₁] at hστ; simp [interval.Adj, hστ]
  · refine interval.prop_le_of_eq (β := id) fun σ τ hστ ↦ ?_
    change interval.halfFlip m σ τ ≠ 0 at hστ
    obtain ⟨τ, hτ⟩ := τ
    rcases σ with v | e <;> rcases τ with w | f <;>
      simp [interval.halfFlip, interval.halfFlipFull] at hστ
    simp [hστ]
  · rw [add_zero]; exact interval.half_le_mesh

/-- **Radii of the controlled interval B-pair duality** `C^{1-*}(I) ≃ C(I, ∂I)`. -/
theorem interval.symAbsDualityLoc_propLE :
    (interval.symAbsDualityLoc m).PropLE (interval.arcLabel L M m h a)
      (interval.arcLabel L M m h a ∘ Subtype.val) (ENNReal.ofReal (mesh L M / 2))
      (ENNReal.ofReal (mesh L M)) :=
  interval.symRelDualityLoc_propLE.transpose

end Arc

/-! ### Cubes in the torus -/

section Cube

variable (L : ℝ) [Fact (0 < L)] (M m : ℕ) [NeZero M] (h : m + 1 < M)

/-- **The B-pair duality of a box is controlled**: radii `η/2` and `η` for the product labels
of the arcs `[a_i, a_i + m + 1]` (the torus centres of the box, `torus.prodLabel_boxInj`). -/
theorem cube.symAbsDualityLoc_propLE (n : ℕ) (a : Fin n → Fin M) :
    (cube.symAbsDualityLoc m n).PropLE (prodLabel n fun i ↦ interval.arcLabel L M m h (a i))
      (prodLabel n fun i ↦ interval.arcLabel L M m h (a i) ∘ Subtype.val)
      (ENNReal.ofReal (mesh L M / 2)) (ENNReal.ofReal (mesh L M)) :=
  HtpyEquiv.PropLE.dualProd interval.half_add_half n fun _ ↦ interval.symAbsDualityLoc_propLE

/-- The same with `CPcell` (labels on the cube factor). -/
theorem cubeCP.symAbsDualityLoc_propLE (n : ℕ) (a : Fin n → Fin M) :
    (cubeCP.symAbsDualityLoc m n).PropLE
      (fun q ↦ prodLabel n (fun i ↦ interval.arcLabel L M m h (a i)) q.1)
      (fun q ↦ prodLabel n (fun i ↦ interval.arcLabel L M m h (a i) ∘ Subtype.val) q.1)
      (ENNReal.ofReal (mesh L M / 2)) (ENNReal.ofReal (mesh L M)) :=
  (cube.symAbsDualityLoc_propLE L M m h n a).dualTensor_fst _

omit [Fact (0 < L)] in
/-- The product labels of the arcs are the torus centres of the box cells. -/
theorem torus.prodLabel_boxInj : (n : ℕ) → (a : Fin n → Fin M) → (x : (cube (m + 1) n).X) →
    prodLabel n (fun i ↦ interval.arcLabel L M m h (a i)) x =
      torus.center L M n ((torus.boxInj M m h a).toFun x)
  | 0, _, _ => funext fun i ↦ i.elim0
  | n + 1, a, ⟨x₀, x'⟩ => by
    change (Fin.cons _ _ : Fin (n + 1) → AddCircle L) = Fin.cons _ _
    rw [torus.prodLabel_boxInj n (fun i ↦ a i.succ) x']
    rfl

end Cube

end BasedComplex

end HSFormal.Cubical
