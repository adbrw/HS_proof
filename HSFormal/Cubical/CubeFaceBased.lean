import HSFormal.Cubical.CutStep
import HSFormal.Cubical.PinchControl

/-!
# Based cube-face pairs (cubical module C8, the faces of Lemma 11.2)

`K j = I_{m+1}^{⊗j} ⊗ CPcell` with the cube top `cubeTop m j` (`PinchFace`), and its boundary
`∂K j = ∂I^j ⊗ CPcell` (`cubeCP.bdry`).

* (a) `cubeTop_deg`, `cubeTop_symm`: the top has total degree `j + 4` and is `(j+4)`-symmetric;
  `cubeTop_defect_supp`: its defect is carried by `∂K × ∂K`.  So `ψ_j := bdHomB` of the defect is
  a chain map `(∂K)^{j+3-*} → ∂K` (`cubeCP.bdHom`).
* (b) `cubePair_relEquiv`: the relative cap `C^{j+4-*}(K, ∂K) → C(K)` of the based pair, with map
  `cubeTop` on relative cochains, is a homotopy equivalence with radii `η/2`, `η`
  (`cubePair_relEquiv_propLE`): the transpose of `cubeCP.symAbsDualityLoc`.
* (c) For `j = k + 2`, the cover `∂K = R ∪ F` (rest and top face) of `∂K` is local for `ψ_j` in
  both directions (`cubeCP.bdHom_loc`, `cubeCP.bdHom_loc'`), and the right column of the
  excision ladder (the B-pair map of the top face) is a homotopy equivalence with radii `η/2`, `η`
  (`cubeFace_ladderEquiv`, `cubeFace_ladderEquiv_hom`, `cubeFace_ladderEquiv_propLE`).
* (d) The interface `F ∩ R ≅ ∂K (j - 1)` (`cubeFace_sigIso`, via `cube.topEmb`) carries the B-side
  boundary structure `cutBd ψ_j F` to `ψ_{j-1}` (`cubeFace_sigIso_bdHom`): the flag iterates.
-/

noncomputable section

namespace HSFormal.Cubical

open Matrix
open scoped Kronecker ENNReal

namespace BasedComplex

/-! ### Decidability of the face predicates -/

instance interval.decIsVEnd (ℓ : ℕ) : DecidablePred (interval.IsVEnd ℓ) := fun σ ↦
  inferInstanceAs (Decidable (σ = .inl 0 ∨ σ = .inl (Fin.last ℓ)))

instance cube.decBdry (ℓ n : ℕ) : DecidablePred (cube.Bdry ℓ (n := n)) := fun σ ↦
  inferInstanceAs (Decidable (∃ i, interval.IsVEnd ℓ (coord n σ i)))

instance cube.decTop (ℓ n : ℕ) : DecidablePred (cube.Top ℓ (n := n)) := fun σ ↦
  inferInstanceAs (Decidable (σ.1 = .inl (Fin.last ℓ)))

instance cube.decRest (ℓ n : ℕ) : DecidablePred (cube.Rest ℓ (n := n)) := fun σ ↦
  inferInstanceAs (Decidable (σ.1 = .inl 0 ∨ cube.Bdry ℓ σ.2))

/-! ### General facts -/

/-- Rows of a matrix that agree on the cells off a subcomplex with a chain map into the quotient
carry no defect. -/
theorem defect_eq_zero_of_rows {C : BasedComplex} {N : ℕ} (hC : C.DimLE N)
    {T : Matrix C.X C.X ℚ} {P : C.X → Prop} [DecidablePred P] (hP : C.IsSub P)
    (H : Hom (C.dual N hC) (C.restrict (fun σ ↦ ¬P σ) hP.isLocallyClosed_compl))
    (hH : ∀ σ y, H.f σ y = T σ.1 y) {x : C.X} (hx : ¬P x) (y : C.X) :
    defect C N hC T x y = 0 := by
  have hc := congr_fun (congr_fun H.comm ⟨x, hx⟩) y
  simp only [mul_apply] at hc
  rw [defect, Matrix.sub_apply, sub_eq_zero, mul_apply, mul_apply,
    ← sum_subtype_eq (P := fun σ ↦ ¬P σ) (fun κ ↦ C.d x κ * T κ y)
      (fun κ h hκ ↦ hx (hP _ _ (left_ne_zero_of_mul h) hκ))]
  simp only [hH] at hc
  exact hc

theorem prodLabel_cellInj {E : Type*} : (n : ℕ) → {C D : Fin n → BasedComplex} →
    (f : ∀ i, CellInj (C i) (D i)) → (b : ∀ i, (D i).X → E) → (p : (prodComplex n C).X) →
    prodLabel n b ((CellInj.prod n f).toFun p) = prodLabel n (fun i ↦ b i ∘ (f i).toFun) p
  | 0, _, _, _, _, _ => funext fun i ↦ i.elim0
  | n + 1, _, _, f, b, ⟨p, p'⟩ => by
    change (Fin.cons (b 0 ((f 0).toFun p)) (prodLabel n (fun i ↦ b i.succ)
      ((CellInj.prod n fun i ↦ f i.succ).toFun p')) : Fin (n + 1) → E) = Fin.cons _ _
    rw [prodLabel_cellInj n (fun i ↦ f i.succ) (fun i ↦ b i.succ) p']
    rfl

/-! ### Propagation of transported equivalences -/

section Transport

variable {E E' : Type*} [PseudoEMetricSpace E] [PseudoEMetricSpace E'] {C C' D D' : BasedComplex}
  {r s : ℝ≥0∞}

theorem prop_map_le {A B : Type*} {u : Matrix B A ℚ} {a : A → E} {b : B → E} (F : E → E')
    (hF : ∀ x y, edist (F x) (F y) ≤ edist x y) : prop u (F ∘ a) (F ∘ b) ≤ prop u a b :=
  prop_le_iff.mpr fun _ _ h ↦ (hF _ _).trans (edist_le_prop h)

/-- Radii survive `1`-Lipschitz maps of the labels. -/
theorem HtpyEquiv.PropLE.map {e : HtpyEquiv C D} {a : C.X → E} {b : D.X → E}
    (he : e.PropLE a b r s) (F : E → E') (hF : ∀ x y, edist (F x) (F y) ≤ edist x y) :
    e.PropLE (F ∘ a) (F ∘ b) r s :=
  ⟨(prop_map_le F hF).trans he.hom, (prop_map_le F hF).trans he.inv,
    (prop_map_le F hF).trans he.homInv, (prop_map_le F hF).trans he.invHom⟩

theorem CellIso.prop_mat {e : CellIso C D} {a : C.X → E} {b : D.X → E}
    (h : ∀ σ, b (e.toEquiv σ) = a σ) {r : ℝ≥0∞} : prop e.mat a b ≤ r :=
  prop_le_iff.mpr fun ρ σ hρσ ↦ by
    have : ρ = e.toEquiv σ := by
      by_contra h'; exact hρσ (by simp [CellIso.mat, h'])
    rw [this, h, edist_self]
    exact zero_le

/-- Radii survive transport along cell isomorphisms matching the labels. -/
theorem HtpyEquiv.PropLE.transport {N : ℕ} {hC : C.DimLE N} {f : HtpyEquiv (C.dual N hC) D}
    {a : C.X → E} {b : D.X → E} (hf : f.PropLE a b r s) (eC : CellIso C C') (eD : CellIso D D')
    (hC' : C'.DimLE N) {a' : C'.X → E} {b' : D'.X → E} (ha : ∀ σ, a' (eC.toEquiv σ) = a σ)
    (hb : ∀ σ, b' (eD.toEquiv σ) = b σ) : (f.transport eC eD hC').PropLE a' b' r s := by
  have h₁ : prop (eC.symm.dual hC' hC).mat a' a ≤ 0 :=
    CellIso.prop_mat fun σ ↦ by rw [← ha, CellIso.dual_apply, CellIso.apply_symm_apply]
  have h₂ : prop (eC.symm.dual hC' hC).symm.mat a a' ≤ 0 :=
    CellIso.prop_mat fun σ ↦ ha σ
  have h₃ : prop eD.mat b b' ≤ 0 := CellIso.prop_mat hb
  have h₄ : prop eD.symm.mat b' b ≤ 0 :=
    CellIso.prop_mat fun σ ↦ by rw [← hb, CellIso.apply_symm_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change prop (eD.mat * (f.hom.f * (eC.symm.dual hC' hC).mat)) a' b' ≤ r
    exact prop_mul_le_of_le (prop_mul_le_of_le h₁ hf.hom (by rw [zero_add])) h₃
      (by rw [add_zero])
  · change prop (((eC.symm.dual hC' hC).symm.mat * f.inv.f) * eD.symm.mat) b' a' ≤ r
    exact prop_mul_le_of_le h₄ (prop_mul_le_of_le hf.inv h₂ (by rw [add_zero]))
      (by rw [zero_add])
  · rw [HtpyEquiv.transport, HtpyEquiv.trans_homInv_h, HtpyEquiv.trans_homInv_h]
    simp only [CellIso.htpyEquiv, HtpyEquiv.ofIso, Htpy.ofEq_h, Matrix.zero_mul,
      Matrix.mul_zero, add_zero, zero_add]
    exact prop_mul_le_of_le (prop_mul_le_of_le h₁ hf.homInv (by rw [zero_add])) h₂
      (by rw [add_zero])
  · rw [HtpyEquiv.transport, HtpyEquiv.trans_invHom_h, HtpyEquiv.trans_invHom_h]
    simp only [CellIso.htpyEquiv, HtpyEquiv.ofIso, Htpy.ofEq_h, Matrix.zero_mul,
      Matrix.mul_zero, add_zero, zero_add]
    exact prop_mul_le_of_le (prop_mul_le_of_le h₄ hf.invHom (by rw [zero_add])) h₃
      (by rw [add_zero])

end Transport

/-! ### Cube faces -/

section CubeFaces

variable {ℓ : ℕ}

/-- A boundary cell of `I_ℓ^{⊗n}` has a vertex coordinate, so degree `< n`. -/
theorem cube.deg_lt_of_bdry : (n : ℕ) → {σ : (cube ℓ n).X} → cube.Bdry ℓ σ →
    (cube ℓ n).deg σ + 1 ≤ n
  | 0, _, ⟨i, _⟩ => i.elim0
  | n + 1, ⟨σ₀, σ'⟩, h => by
    change (interval ℓ).deg σ₀ + (cube ℓ n).deg σ' + 1 ≤ n + 1
    rcases (cube.bdry_succ_iff ℓ _).mp h with h₀ | h'
    · have h₁ : (interval ℓ).deg σ₀ = 0 := by rcases h₀ with rfl | rfl <;> rfl
      have h₂ : (cube ℓ n).deg σ' ≤ n := cube.dimLE n ℓ σ'
      omega
    · have h₁ : (cube ℓ n).deg σ' + 1 ≤ n := cube.deg_lt_of_bdry n h'
      have h₂ : (interval ℓ).deg σ₀ ≤ 1 := dimLE_oneDim σ₀
      omega

variable (m : ℕ)

/-- The relative cells `C(Iⁿ, ∂Iⁿ)` are the non-boundary cells of the cube. -/
theorem cube.not_bdry_iff (n : ℕ) (y : (cube (m + 1) n).X) :
    ¬cube.Bdry (m + 1) y ↔ ∃ x, (cubeRelInj m n).toFun x = y := by
  rw [cubeRelInj, CellInj.prod_range_iff, cube.Bdry, not_exists]
  refine forall_congr' fun i ↦ ⟨fun h ↦ ⟨⟨_, h⟩, rfl⟩, ?_⟩
  rintro ⟨x, hx⟩
  rw [← hx]
  exact x.2

end CubeFaces

/-! ### (a) The cube top: degree, symmetry and the support of its defect -/

section CubeTop

variable (m : ℕ)

theorem cubeTop_dimLE (j : ℕ) : ((cube (m + 1) j).tensor CPcell).DimLE (j + 3 + 1) :=
  (cube.dimLE j (m + 1)).tensor CPcell.dimLE

theorem cubeCP.isSub_bdry (j : ℕ) :
    ((cube (m + 1) j).tensor CPcell).IsSub fun x ↦ cube.Bdry (m + 1) x.1 :=
  isSub_fst (cube.isSub_bdry (m + 1))

/-- The top has total degree `j + 4`. -/
theorem cubeTop_deg (j : ℕ) {σ τ : ((cube (m + 1) j).tensor CPcell).X}
    (h : cubeTop m j σ τ ≠ 0) :
    ((cube (m + 1) j).tensor CPcell).deg σ + ((cube (m + 1) j).tensor CPcell).deg τ =
      j + 3 + 1 := by
  obtain ⟨x, c⟩ := σ
  obtain ⟨y, c'⟩ := τ
  rw [cubeTop, koszul, mul_diagonal, kronecker_apply] at h
  have h₁ := cubeSym_deg m j (left_ne_zero_of_mul (left_ne_zero_of_mul h))
  have h₂ := CPcell.φ.deg0 c c' (right_ne_zero_of_mul (left_ne_zero_of_mul h))
  have h₃ := CPcell.dimLE c'
  change ((CPcell.deg c : ℕ) : ℤ) = ((4 - CPcell.deg c' : ℕ) : ℤ) + 0 at h₂
  change (cube (m + 1) j).deg x + CPcell.deg c + ((cube (m + 1) j).deg y + CPcell.deg c') =
    j + 3 + 1
  omega

/-- **The top is `(j+4)`-symmetric** (it is the restriction of the torus duality to a box). -/
theorem cubeTop_symm (j : ℕ) (σ τ : ((cube (m + 1) j).tensor CPcell).X) :
    ((-1 : ℚ) ^ (j + 3 + 1 + 1)) ^ ((cube (m + 1) j).tensor CPcell).deg σ * cubeTop m j τ σ =
      cubeTop m j σ τ := by
  classical
  have h : m + 1 < m + 2 := Nat.lt_succ_self _
  have hP := (torusCP.isSub_WB (m + 2) j (fun _ ↦ 0) (fun _ ↦ m + 1) fun _ ↦ h).isLocallyClosed
  rw [← torusCP.cutTop_boxIso m (m + 2) h (fun _ ↦ 0) hP,
    ← torusCP.cutTop_boxIso m (m + 2) h (fun _ ↦ 0) hP,
    ← (torusCP.boxIso (m + 2) m h (fun _ ↦ 0) hP).deg_eq σ]
  simp only [cutTop, submatrix_apply]
  exact (isSymm_iff _).mp (torusCP.duality (m + 2) j).symm _ _

/-- On relative rows the top is the symmetric B-pair duality `cubeCP.symAbsDuality`. -/
theorem cubeTop_relInj (j : ℕ) (x : ((cubeRel m j).tensor CPcell).X)
    (y : ((cube (m + 1) j).tensor CPcell).X) :
    cubeTop m j ((cubeRelInj m j).toFun x.1, x.2) y = (cubeCP.symAbsDuality m j).hom.f x y := by
  obtain ⟨x, c⟩ := x
  obtain ⟨y, c'⟩ := y
  simp only [cubeTop, cubeCP.symAbsDuality, HtpyEquiv.dualTensor_hom_f, koszul, mul_diagonal,
    kronecker_apply]
  rw [cubeSym_relInj]
  rfl

/-- The relative cells `C(K, ∂K) ≅ C(Iʲ, ∂Iʲ) ⊗ CPcell`. -/
def cubeCP.relIso (j : ℕ) : CellIso ((cubeRel m j).tensor CPcell)
    (((cube (m + 1) j).tensor CPcell).restrict (fun x ↦ ¬cube.Bdry (m + 1) x.1)
      (cubeCP.isSub_bdry m j).isLocallyClosed_compl) :=
  ((cubeRelInj m j).tensor (CellInj.id CPcell)).toIso _ _ fun σ ↦ by
    constructor
    · intro hσ
      obtain ⟨p, hp⟩ := (cube.not_bdry_iff m j σ.1).mp hσ
      exact ⟨(p, σ.2), Prod.ext hp rfl⟩
    · rintro ⟨p, rfl⟩
      exact (cube.not_bdry_iff m j _).mpr ⟨p.1, rfl⟩

@[simp] theorem cubeCP.relIso_apply (j : ℕ) (x : ((cubeRel m j).tensor CPcell).X) :
    ((cubeCP.relIso m j).toEquiv x).1 = ((cubeRelInj m j).toFun x.1, x.2) := rfl

/-- **The controlled absolute B-pair duality** `C^{j+4-*}(K) ≃ C(K, ∂K)` (local inverse). -/
def cubeCP.absEquiv (j : ℕ) :
    HtpyEquiv (((cube (m + 1) j).tensor CPcell).dual (j + 3 + 1) (cubeTop_dimLE m j))
      (((cube (m + 1) j).tensor CPcell).restrict (fun x ↦ ¬cube.Bdry (m + 1) x.1)
        (cubeCP.isSub_bdry m j).isLocallyClosed_compl) :=
  (cubeCP.symAbsDualityLoc m j).transport (CellIso.refl _) (cubeCP.relIso m j) (cubeTop_dimLE m j)

theorem cubeCP.absEquiv_hom_f (j : ℕ) (σ : {x : ((cube (m + 1) j).tensor CPcell).X //
    ¬cube.Bdry (m + 1) x.1}) (y : ((cube (m + 1) j).tensor CPcell).X) :
    (cubeCP.absEquiv m j).hom.f σ y = cubeTop m j σ.1 y := by
  obtain ⟨x, rfl⟩ := (cubeCP.relIso m j).toEquiv.surjective σ
  rw [cubeCP.absEquiv]
  rw [show y = (CellIso.refl _).toEquiv y from rfl, HtpyEquiv.transport_hom_f_apply,
    cubeCP.symAbsDualityLoc_hom_f, cubeCP.relIso_apply, cubeTop_relInj]
  rfl

/-- **(a) The defect of the cube top is carried by `∂K × ∂K`.** -/
theorem cubeTop_defect_supp (j : ℕ) {x y : ((cube (m + 1) j).tensor CPcell).X}
    (h : defect ((cube (m + 1) j).tensor CPcell) (j + 3 + 1)
      ((cube.dimLE j (m + 1)).tensor CPcell.dimLE) (cubeTop m j) x y ≠ 0) :
    cube.Bdry (m + 1) x.1 ∧ cube.Bdry (m + 1) y.1 := by
  have rows : ∀ x, ¬cube.Bdry (m + 1) x.1 → ∀ y, defect ((cube (m + 1) j).tensor CPcell)
      (j + 3 + 1) ((cube.dimLE j (m + 1)).tensor CPcell.dimLE) (cubeTop m j) x y = 0 :=
    fun x hx y ↦ defect_eq_zero_of_rows _ (cubeCP.isSub_bdry m j) (cubeCP.absEquiv m j).hom
      (cubeCP.absEquiv_hom_f m j) hx y
  refine ⟨by_contra fun hx ↦ h (rows x hx y), by_contra fun hy ↦ h ?_⟩
  rw [← defect_symm (cubeTop_dimLE m j) (fun σ τ h ↦ cubeTop_deg m j h) (cubeTop_symm m j),
    rows y hy x, mul_zero]

end CubeTop

/-! ### (b) The relative cap of the based cube pair -/

section RelCap

variable (m : ℕ)

/-- **(b) The relative cap `C^{j+4-*}(K, ∂K) ≃ C(K)` of the based cube pair**: the transpose of
the controlled absolute B-pair duality; its map is the top on relative cochains
(`cubePair_relEquiv_hom_f`). -/
def cubePair_relEquiv (j : ℕ) :
    HtpyEquiv ((((cube (m + 1) j).tensor CPcell).restrict (fun x ↦ ¬cube.Bdry (m + 1) x.1)
        (cubeCP.isSub_bdry m j).isLocallyClosed_compl).dual (j + 3 + 1)
        ((cubeTop_dimLE m j).restrict _ _))
      ((cube (m + 1) j).tensor CPcell) :=
  (cubeCP.absEquiv m j).transpose (cubeTop_dimLE m j) ((cubeTop_dimLE m j).restrict _ _)

theorem cubePair_relEquiv_hom_f (j : ℕ) :
    (cubePair_relEquiv m j).hom.f = (cubeTop m j).submatrix id Subtype.val := by
  ext σ τ
  rw [cubePair_relEquiv, HtpyEquiv.transpose_hom, transpose_f_apply, cubeCP.absEquiv_hom_f,
    submatrix_apply]
  exact cubeTop_symm m j σ τ.1

/-- The map of `cubePair_relEquiv` is the relative cap `relHomB` of the based pair. -/
theorem cubePair_relEquiv_hom (j : ℕ) :
    (cubePair_relEquiv m j).hom = relHomB (cubeTop_dimLE m j) (fun _ _ h ↦ cubeTop_deg m j h)
      (cubeCP.isSub_bdry m j) (fun _ _ h ↦ cubeTop_defect_supp m j h) :=
  Hom.ext (by rw [cubePair_relEquiv_hom_f, relHomB_f])

variable (L : ℝ) [Fact (0 < L)] (M : ℕ) [NeZero M] (h : m + 1 < M)

theorem cubeCP.absEquiv_propLE (j : ℕ) (a : Fin j → Fin M) :
    (cubeCP.absEquiv m j).PropLE
      (fun q ↦ prodLabel j (fun i ↦ interval.arcLabel L M m h (a i)) q.1)
      (fun q ↦ prodLabel j (fun i ↦ interval.arcLabel L M m h (a i)) q.1.1)
      (ENNReal.ofReal (mesh L M / 2)) (ENNReal.ofReal (mesh L M)) :=
  (cubeCP.symAbsDualityLoc_propLE L M m h j a).transport _ _ _ (fun _ ↦ rfl)
    fun x ↦ prodLabel_cellInj j _ _ x.1

/-- **(b) Radii of the relative cap**: `η/2` (maps) and `η` (homotopies) for the product labels
of the arcs (cells of `K` and, through `Subtype.val`, of `C(K, ∂K)`). -/
theorem cubePair_relEquiv_propLE (j : ℕ) (a : Fin j → Fin M) :
    (cubePair_relEquiv m j).PropLE
      (fun q ↦ prodLabel j (fun i ↦ interval.arcLabel L M m h (a i)) q.1.1)
      (fun q ↦ prodLabel j (fun i ↦ interval.arcLabel L M m h (a i)) q.1)
      (ENNReal.ofReal (mesh L M / 2)) (ENNReal.ofReal (mesh L M)) :=
  (cubeCP.absEquiv_propLE m L M h j a).transpose

end RelCap

/-! ### The boundary structure `ψ_j` on `∂K` -/

section BdHom

variable (m : ℕ)

/-- `∂K = ∂Iʲ ⊗ CPcell`. -/
abbrev cubeCP.bdry (j : ℕ) : BasedComplex :=
  ((cube (m + 1) j).tensor CPcell).restrict (fun x ↦ cube.Bdry (m + 1) x.1)
    (cubeCP.isSub_bdry m j).isLocallyClosed

theorem cubeCP.dimLE_bdry (j : ℕ) : (cubeCP.bdry m j).DimLE (j + 3) := fun σ ↦ by
  have h₁ : (cube (m + 1) j).deg σ.1.1 + 1 ≤ j := cube.deg_lt_of_bdry j σ.2
  have h₂ : CPcell.deg σ.1.2 ≤ 4 := CPcell.dimLE σ.1.2
  change (cube (m + 1) j).deg σ.1.1 + CPcell.deg σ.1.2 ≤ j + 3
  omega

/-- **The boundary structure** `ψ_j : (∂K)^{j+3-*} → ∂K` of the based cube pair: the defect of
the top on `∂K` (`bdHomB`). -/
def cubeCP.bdHom (j : ℕ) :
    Hom ((cubeCP.bdry m j).dual (j + 3) (cubeCP.dimLE_bdry m j)) (cubeCP.bdry m j) :=
  bdHomB (cubeTop_dimLE m j) (fun _ _ h ↦ cubeTop_deg m j h) (cubeCP.isSub_bdry m j)
    (fun _ _ h ↦ cubeTop_defect_supp m j h) (cubeCP.dimLE_bdry m j)

theorem cubeCP.bdHom_f (j : ℕ) (σ τ : (cubeCP.bdry m j).X) :
    (cubeCP.bdHom m j).f σ τ = defect ((cube (m + 1) j).tensor CPcell) (j + 3 + 1)
      ((cube.dimLE j (m + 1)).tensor CPcell.dimLE) (cubeTop m j) σ.1 τ.1 := rfl

theorem cubeCP.isSymm_bdHom (j : ℕ) : IsSymm (cubeCP.dimLE_bdry m j) (cubeCP.bdHom m j) :=
  isSymm_bdHomB (cubeTop_dimLE m j) (fun _ _ h ↦ cubeTop_deg m j h) (cubeTop_symm m j)
    (cubeCP.isSub_bdry m j) (fun _ _ h ↦ cubeTop_defect_supp m j h) (cubeCP.dimLE_bdry m j)

/-- The defect of the cube top is the defect of `cubeSym` tensored with `φ_CP`. -/
theorem defect_cubeTop_apply (j : ℕ) (x y : (cube (m + 1) j).X) (c c' : CPcell.X) :
    defect ((cube (m + 1) j).tensor CPcell) (j + 3 + 1)
      ((cube.dimLE j (m + 1)).tensor CPcell.dimLE) (cubeTop m j) (x, c) (y, c') =
    defect (cube (m + 1) j) j (cube.dimLE j (m + 1)) (cubeSym m j) x y * CPcell.φ.f c c' *
      (-1) ^ ((cube (m + 1) j).deg y * (CPcell.deg c' + 4)) := by
  rw [cubeTop, defect_kronecker (cube.dimLE j (m + 1)) CPcell.dimLE _ _
      (fun σ τ h ↦ cubeSym_deg m j h),
    defect_hom CPcell.φ, kronecker_zero, add_zero, koszul, mul_diagonal, kronecker_apply]

/-- The defect of `cubeSym` is carried by `∂Iʲ × ∂Iʲ`. -/
theorem cubeSym_defect_supp (j : ℕ) {x y : (cube (m + 1) j).X}
    (h : defect (cube (m + 1) j) j (cube.dimLE j (m + 1)) (cubeSym m j) x y ≠ 0) :
    cube.Bdry (m + 1) x ∧ cube.Bdry (m + 1) y :=
  cubeTop_defect_supp m j (x := (x, 1)) (y := (y, 1)) (by
    rw [defect_cubeTop_apply, CPcell.φ_f]
    simp [h])

/-- The defect of the interval top `symMat` is diagonal. -/
theorem interval.defect_symMat_eq {x y : (interval (m + 1)).X}
    (h : defect (interval (m + 1)) 1 dimLE_oneDim (interval.symMat m) x y ≠ 0) : x = y := by
  have hd := defect_deg (N := 0) dimLE_oneDim (fun _ _ h ↦ interval.symMat_deg m h) h
  rcases x with v | e
  · rcases y with w | f
    · by_contra hvw
      have hvw' : v ≠ w := fun h' ↦ hvw (by rw [h'])
      apply h
      rw [defect, Matrix.sub_apply, mul_apply, mul_apply, sub_eq_zero]
      simp [Fintype.sum_sum_type, interval.symMat, sgn, mul_diagonal]
      rw [← sub_eq_zero, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun e _ ↦ ?_
      split_ifs <;> subst_vars <;> simp_all
    · simp at hd
  · simp at hd

end BdHom

/-! ### (c) The top-face cut of `∂K (k + 2)` -/

section Cut

variable (m k : ℕ)

/-- **Locality of the boundary structure** for the cover `∂K = R ∪ F` (rest and top face). -/
theorem cubeTop_defect_local {x y : ((cube (m + 1) (k + 2)).tensor CPcell).X}
    (h : defect ((cube (m + 1) (k + 2)).tensor CPcell) (k + 2 + 3 + 1)
      ((cube.dimLE (k + 2) (m + 1)).tensor CPcell.dimLE) (cubeTop m (k + 2)) x y ≠ 0) :
    (¬cube.Top (m + 1) y.1 → cube.Rest (m + 1) x.1) ∧
      (¬cube.Rest (m + 1) y.1 → cube.Top (m + 1) x.1) := by
  obtain ⟨hx, hy⟩ := cubeTop_defect_supp m (k + 2) h
  obtain ⟨⟨x₀, x'⟩, c⟩ := x
  obtain ⟨⟨y₀, y'⟩, c'⟩ := y
  rw [defect_cubeTop_apply] at h
  have hs := left_ne_zero_of_mul (left_ne_zero_of_mul h)
  rw [defect_congr (C := cube (m + 1) (k + 2)) _ (show k + 2 = 1 + (k + 1) by omega)
    (dimLE_oneDim.tensor (cube.dimLE (k + 1) (m + 1)))] at hs
  change defect ((interval (m + 1)).tensor (cube (m + 1) (k + 1))) (1 + (k + 1)) _
    ((interval.symMat m ⊗ₖ cubeSym m (k + 1)) * koszul _ _ (k + 1)) (x₀, x') (y₀, y') ≠ 0 at hs
  rw [defect_kronecker dimLE_oneDim (cube.dimLE (k + 1) (m + 1)) _ _
      (fun σ τ h ↦ interval.symMat_deg m h), koszul, mul_diagonal, Matrix.add_apply, kronecker_apply,
    kronecker_apply] at hs
  have hs' := left_ne_zero_of_mul hs
  by_cases h₁ : defect (interval (m + 1)) 1 dimLE_oneDim (interval.symMat m) x₀ y₀ = 0
  · rw [h₁, zero_mul, zero_add] at hs'
    obtain ⟨hx', hy'⟩ := cubeSym_defect_supp m (k + 1) (right_ne_zero_of_mul hs')
    exact ⟨fun _ ↦ Or.inr hx', fun hr ↦ (hr (Or.inr hy')).elim⟩
  · obtain rfl := interval.defect_symMat_eq m h₁
    replace hx := (cube.bdry_succ_iff _ _).1 hx
    replace hy := (cube.bdry_succ_iff _ _).1 hy
    simp only [cube.Top, cube.Rest, interval.IsVEnd, cube.bdry_succ_iff] at hx hy ⊢
    tauto

/-- The rest `R` of `∂K`, as a subcomplex of `∂K`. -/
theorem cubeFace.isSub_rest :
    (cubeCP.bdry m (k + 2)).IsSub fun x ↦ cube.Rest (m + 1) x.1.1 :=
  IsSub.restrict_pred (cubeCP.isSub_bdry m (k + 2)).isLocallyClosed
    (isSub_fst (D := CPcell) (cube.isSub_rest (m + 1)))

/-- The top face `F` of `∂K`, as a subcomplex of `∂K`. -/
theorem cubeFace.isSub_top :
    (cubeCP.bdry m (k + 2)).IsSub fun x ↦ cube.Top (m + 1) x.1.1 :=
  IsSub.restrict_pred (cubeCP.isSub_bdry m (k + 2)).isLocallyClosed
    (isSub_fst (D := CPcell) (cube.isSub_top (m + 1)))

theorem cubeFace.cover (σ : (cubeCP.bdry m (k + 2)).X) :
    cube.Rest (m + 1) σ.1.1 ∨ cube.Top (m + 1) σ.1.1 :=
  ((cube.bdry_iff_top_or_rest (m + 1) σ.1.1).mp σ.2).symm

theorem cubeCP.bdHom_loc (σ τ : (cubeCP.bdry m (k + 2)).X)
    (h : (cubeCP.bdHom m (k + 2)).f σ τ ≠ 0) (hτ : ¬cube.Top (m + 1) τ.1.1) :
    cube.Rest (m + 1) σ.1.1 :=
  (cubeTop_defect_local m k h).1 hτ

theorem cubeCP.bdHom_loc' (σ τ : (cubeCP.bdry m (k + 2)).X)
    (h : (cubeCP.bdHom m (k + 2)).f σ τ ≠ 0) (hτ : ¬cube.Rest (m + 1) τ.1.1) :
    cube.Top (m + 1) σ.1.1 :=
  (cubeTop_defect_local m k h).2 hτ

/-- The interface `R ∩ F` has dimension `≤ k + 4`. -/
theorem cubeFace.hSig (σ : (cubeCP.bdry m (k + 2)).X) (hA : cube.Rest (m + 1) σ.1.1)
    (hB : cube.Top (m + 1) σ.1.1) : (cubeCP.bdry m (k + 2)).deg σ ≤ k + 4 := by
  obtain ⟨⟨⟨x₀, x'⟩, c⟩, hσ⟩ := σ
  have hx' := ((cube.top_and_rest_iff (m + 1) (by omega) _).mp ⟨hB, hA⟩).2
  change x₀ = _ at hB
  subst hB
  have h₁ : (cube (m + 1) (k + 1)).deg x' + 1 ≤ k + 1 := cube.deg_lt_of_bdry (k + 1) hx'
  have h₂ : CPcell.deg c ≤ 4 := CPcell.dimLE c
  change (0 + (cube (m + 1) (k + 1)).deg x') + CPcell.deg c ≤ k + 4
  omega

end Cut

/-- Corestriction of a cellular injection to a locally closed set containing its image. -/
def CellInj.codRestrict {C D : BasedComplex} (f : CellInj C D) (P : D.X → Prop) [DecidablePred P]
    (hP : D.IsLocallyClosed P) (h : ∀ x, P (f.toFun x)) : CellInj C (D.restrict P hP) where
  toFun x := ⟨f.toFun x, h x⟩
  inj _ _ hxy := f.inj (congrArg Subtype.val hxy)
  deg_eq := f.deg_eq
  d_eq := f.d_eq

section FaceIso

variable (m k : ℕ)

/-- The top-face embedding `K (k+1) → ∂K (k+2)`, `x ↦ (v_{m+1}, x)`. -/
def cubeFace.topInj : CellInj ((cube (m + 1) (k + 1)).tensor CPcell) (cubeCP.bdry m (k + 2)) :=
  ((CellInj.ofEmb (cube.topEmb (m + 1) (n := k + 1))).tensor (CellInj.id CPcell)).codRestrict _ _
    fun _ ↦ ⟨0, Or.inr rfl⟩

theorem cubeFace.topInj_apply (p : ((cube (m + 1) (k + 1)).tensor CPcell).X) :
    ((cubeFace.topInj m k).toFun p).1 = ((Sum.inl (Fin.last (m + 1)), p.1), p.2) := rfl

/-- **The top face** `F ≅ K (k+1)`. -/
def cubeFace.topIso : CellIso ((cube (m + 1) (k + 1)).tensor CPcell)
    ((cubeCP.bdry m (k + 2)).restrict (fun x ↦ cube.Top (m + 1) x.1.1)
      (cubeFace.isSub_top m k).isLocallyClosed) :=
  (cubeFace.topInj m k).toIso _ _ fun σ ↦ by
    obtain ⟨⟨⟨x₀, x'⟩, c⟩, hσ⟩ := σ
    constructor
    · intro h
      change x₀ = _ at h
      subst h
      exact ⟨(x', c), rfl⟩
    · rintro ⟨p, hp⟩
      rw [← hp]
      rfl

/-- **The interior of the top face** `F ∖ R ≅ C(Iᵏ⁺¹, ∂) ⊗ CPcell`. -/
def cubeFace.relIso : CellIso ((cubeRel m (k + 1)).tensor CPcell)
    ((cubeCP.bdry m (k + 2)).restrict (fun x ↦ ¬cube.Rest (m + 1) x.1.1)
      (cubeFace.isSub_rest m k).isLocallyClosed_compl) :=
  ((cubeFace.topInj m k).comp ((cubeRelInj m (k + 1)).tensor (CellInj.id CPcell))).toIso _ _
    fun σ ↦ by
    obtain ⟨⟨⟨x₀, x'⟩, c⟩, hσ⟩ := σ
    constructor
    · intro h
      have hT := (cubeFace.cover m k ⟨((x₀, x'), c), hσ⟩).resolve_left h
      change x₀ = _ at hT
      subst hT
      have hb : ¬cube.Bdry (m + 1) x' := fun hb ↦ h (.inr hb)
      obtain ⟨p, rfl⟩ := (cube.not_bdry_iff m (k + 1) x').mp hb
      exact ⟨(p, c), rfl⟩
    · rintro ⟨⟨p, c'⟩, hp⟩
      rw [← hp]
      rintro (h | h)
      · have := congrArg Fin.val (Sum.inl_injective h)
        simp at this
      · exact (cube.not_bdry_iff m (k + 1) _).mpr ⟨p, rfl⟩ h

/-- The interface `R ∩ F ≅ ∂K (k+1)` (the flag iterates, `cube.rest_topEmb_iff`). -/
def cubeFace.sigIsoInv : CellIso (cubeCP.bdry m (k + 1))
    ((cubeCP.bdry m (k + 2)).restrict
      (fun x ↦ cube.Rest (m + 1) x.1.1 ∧ cube.Top (m + 1) x.1.1)
      ((cubeFace.isSub_rest m k).and (cubeFace.isSub_top m k)).isLocallyClosed) :=
  ((cubeFace.topInj m k).comp (CellInj.subtype _ _)).toIso _ _ fun σ ↦ by
    obtain ⟨⟨⟨x₀, x'⟩, c⟩, hσ⟩ := σ
    constructor
    · rintro ⟨hR, hT⟩
      have hx' := ((cube.top_and_rest_iff (m + 1) (by omega) _).mp ⟨hT, hR⟩).2
      change x₀ = _ at hT
      subst hT
      exact ⟨⟨(x', c), hx'⟩, rfl⟩
    · rintro ⟨⟨⟨p, c'⟩, hp'⟩, hp⟩
      rw [← hp]
      exact ⟨.inr hp', rfl⟩

end FaceIso

section Ladder

variable (m k : ℕ)

/-- **(c) The B-pair of the top-face cut** `C^{k+5-*}(F) ≃ C(F, F ∩ R)`, with map the right column
`ladderRight ψ_{k+2}` of the excision ladder (`cubeFace_ladderEquiv_hom`): the transport of the
controlled B-pair duality of `K (k+1)` along `F ≅ K (k+1)`. -/
def cubeFace_ladderEquiv :
    HtpyEquiv (((cubeCP.bdry m (k + 2)).restrict (fun x ↦ cube.Top (m + 1) x.1.1)
        (cubeFace.isSub_top m k).isLocallyClosed).dual (k + 2 + 3)
        ((cubeCP.dimLE_bdry m (k + 2)).restrict _ _))
      ((cubeCP.bdry m (k + 2)).restrict (fun x ↦ ¬cube.Rest (m + 1) x.1.1)
        (cubeFace.isSub_rest m k).isLocallyClosed_compl) :=
  (cubeCP.symAbsDualityLoc m (k + 1)).transport (cubeFace.topIso m k) (cubeFace.relIso m k)
    ((cubeCP.dimLE_bdry m (k + 2)).restrict _ _)

theorem cubeFace_ladderEquiv_hom :
    (cubeFace_ladderEquiv m k).hom = ladderRight (cubeCP.dimLE_bdry m (k + 2))
      (cubeCP.bdHom m (k + 2)) (cubeFace.isSub_rest m k) (cubeFace.isSub_top m k)
      (cubeCP.bdHom_loc m k) := by
  refine Hom.ext (Matrix.ext fun ρ σ ↦ ?_)
  obtain ⟨x, rfl⟩ := (cubeFace.relIso m k).toEquiv.surjective ρ
  obtain ⟨y, rfl⟩ := (cubeFace.topIso m k).toEquiv.surjective σ
  rw [cubeFace_ladderEquiv, HtpyEquiv.transport_hom_f_apply, cubeCP.symAbsDualityLoc_hom_f,
    ladderRight, Hom.restrictDual_f, submatrix_apply, cubeCP.bdHom_f, ← cubeTop_relInj]
  exact (defect_cubeTop_top m (k + 1) _ _ _ _).symm

variable (L : ℝ) [Fact (0 < L)] (M : ℕ) [NeZero M] (h : m + 1 < M)

/-- **(c) Radii of the B-pair of the top-face cut**: `η/2` and `η` for the product labels of the
arcs (cells through `Subtype.val`). -/
theorem cubeFace_ladderEquiv_propLE (a : Fin (k + 2) → Fin M) :
    (cubeFace_ladderEquiv m k).PropLE
      (fun q ↦ prodLabel (k + 2) (fun i ↦ interval.arcLabel L M m h (a i)) q.1.1.1)
      (fun q ↦ prodLabel (k + 2) (fun i ↦ interval.arcLabel L M m h (a i)) q.1.1.1)
      (ENNReal.ofReal (mesh L M / 2)) (ENNReal.ofReal (mesh L M)) := by
  let F : (Fin (k + 1) → AddCircle L) → Fin (k + 2) → AddCircle L := fun u ↦
    Fin.cons (α := fun _ ↦ AddCircle L) (interval.arcLabel L M m h (a 0) (.inl (Fin.last (m + 1))))
      u
  have hF : ∀ u v, edist (F u) (F v) ≤ edist u v := fun u v ↦
    (edist_cons_le _ _ u v).trans (by rw [edist_self, max_eq_right (zero_le)])
  refine ((cubeCP.symAbsDualityLoc_propLE L M m h (k + 1) fun i ↦ a i.succ).map F hF).transport
    _ _ _ (fun _ ↦ rfl) fun x ↦ ?_
  change F (prodLabel (k + 1) (fun i ↦ interval.arcLabel L M m h (a i.succ))
    ((cubeRelInj m (k + 1)).toFun x.1)) = F _
  exact congrArg F (prodLabel_cellInj (k + 1) _ _ x.1)

end Ladder

/-! ### (d) The interface carries the next boundary structure -/

section Interface

variable (m k : ℕ)

/-- **(d) The interface `R ∩ F ≅ ∂K (k+1)`** (via `cube.topEmb`). -/
def cubeFace_sigIso : CellIso ((cubeCP.bdry m (k + 2)).restrict
      (fun x ↦ cube.Rest (m + 1) x.1.1 ∧ cube.Top (m + 1) x.1.1)
      ((cubeFace.isSub_rest m k).and (cubeFace.isSub_top m k)).isLocallyClosed)
    (cubeCP.bdry m (k + 1)) :=
  (cubeFace.sigIsoInv m k).symm

theorem cubeFace_sigIso_label (σ) :
    ((cubeFace_sigIso m k).toEquiv σ).1.1 = σ.1.1.1.2 := by
  obtain ⟨x, rfl⟩ := (cubeFace.sigIsoInv m k).toEquiv.surjective σ
  rw [cubeFace_sigIso, CellIso.symm_apply_apply]
  rfl

/-- The top of the B-side on the top face is the next cube top (`defect_cubeTop_top`). -/
theorem cubeFace.cutTop_topIso :
    (cutTop (N := k + 4) (cubeCP.dimLE_bdry m (k + 2)) (cubeCP.bdHom m (k + 2))
      (fun x ↦ cube.Top (m + 1) x.1.1)).submatrix (cubeFace.topIso m k).toEquiv
      (cubeFace.topIso m k).toEquiv = cubeTop m (k + 1) := by
  ext p q
  exact defect_cubeTop_top m (k + 1) p.1 q.1 p.2 q.2

/-- **(d) The flag iterates**: the interface isomorphism carries the B-side boundary structure
`cutBd ψ_{k+2} F` of the top-face cut to `ψ_{k+1}`. -/
theorem cubeFace_sigIso_bdHom (σ τ) :
    (cubeCP.bdHom m (k + 1)).f ((cubeFace_sigIso m k).toEquiv σ)
      ((cubeFace_sigIso m k).toEquiv τ) =
    cutBd (N := k + 4) (cubeCP.dimLE_bdry m (k + 2)) (cubeCP.bdHom m (k + 2))
      (fun x ↦ cube.Top (m + 1) x.1.1)
      (fun x ↦ cube.Rest (m + 1) x.1.1 ∧ cube.Top (m + 1) x.1.1)
      (cubeFace.isSub_top m k).isLocallyClosed (fun _ h ↦ h.2) σ τ := by
  obtain ⟨x, rfl⟩ := (cubeFace.sigIsoInv m k).toEquiv.surjective σ
  obtain ⟨y, rfl⟩ := (cubeFace.sigIsoInv m k).toEquiv.surjective τ
  rw [cubeFace_sigIso, CellIso.symm_apply_apply, CellIso.symm_apply_apply, cubeCP.bdHom_f,
    cutBd, submatrix_apply, cutDefect_eq_defect]
  have := congr_fun (congr_fun (defect_submatrix (cubeFace.topIso m k) (cubeTop_dimLE m (k + 1))
    ((cubeCP.dimLE_bdry m (k + 2)).restrict _ (cubeFace.isSub_top m k).isLocallyClosed)
    (cutTop (N := k + 4) (cubeCP.dimLE_bdry m (k + 2)) (cubeCP.bdHom m (k + 2))
      (fun x ↦ cube.Top (m + 1) x.1.1))) x.1) y.1
  rw [cubeFace.cutTop_topIso, submatrix_apply] at this
  exact this

end Interface

end BasedComplex

end HSFormal.Cubical
