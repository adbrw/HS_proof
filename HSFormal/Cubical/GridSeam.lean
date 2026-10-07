import HSFormal.Cubical.Grid
import HSFormal.IntegrationControl

/-!
# The seam: the torus grid on `(ℝ/Lℤ)ⁿ` and control labels (cubical module C4)

Review fix 2: boxes lifted to `[-L/2, L/2]ⁿ` violate `face_sub` at the seam, so the geometry of
`Tⁿ = C_m^{⊗n}` lives on `(ℝ/Lℤ)ⁿ` with the sup metric (`torus.geometry`): vertex `k` sits at
`k η`, edge `k` at `(k + 1/2) η` with carrier the image of `[k η, (k+1) η]`, where `η = L/m`
(`mesh`); `face_sub` holds everywhere.

* Radii (`torus.propLE`, `torus.prop_d_le`): the boundary, `φ` and `b` propagate `≤ η/2`, the
  homotopies `≤ η`; this holds for every iterated tensor product of `1`-dimensional duality
  equivalences with these bounds (`HtpyEquiv.PropLE.dualProd`), and for `W = Tⁿ ⊗ CPcell` with
  labels on the torus factor (`torusCP.propLE`).
* Carriers lie in the `η/2`-ball around their centres and every point is within `η/2` of a
  vertex (`torus.dist_center_le_of_mem`, `torus.exists_vertex_near`: the nearest-vertex step of
  `a_h`).
* Propagation is measured only through labels `λ ∘ center`, `λ` continuous on the compact
  `(ℝ/Lℤ)ⁿ` (`PropTendsto.of_uniformContinuous`); with mesh `η_i = L/m_i → 0` this gives the
  controlled sequences `torus.controlledSeq`, `torusCP.controlledSeq` and the controlled duality
  `torusCP.controlledDuality` (`φ`, `b`, `H`, `H'` all controlled).
* The chart label: lift to `[-L/2, L/2)ⁿ ⊆ ℝⁿ` (`liftVec`) and apply a map that is constant on
  `‖v‖ ≥ r`, `r < L/2`; it is continuous across the seam (`continuous_comp_liftVec`).  For the
  fixed data, `f̂ = ∞` on `‖v‖ ≥ 2 < 8` (`L = 16`), so `FixedData.torusLabel` is continuous.
-/

noncomputable section

namespace HSFormal.Cubical

open Matrix Filter Topology
open scoped Kronecker ENNReal

universe u

/-! ### Labels of iterated tensor products -/

section Labels

variable {E : Type*} [PseudoEMetricSpace E]

theorem edist_cons_le {n : ℕ} (x y : E) (f g : Fin n → E) :
    edist (Fin.cons x f : Fin (n + 1) → E) (Fin.cons y g) ≤ max (edist x y) (edist f g) := by
  refine edist_pi_le_iff.mpr fun i ↦ ?_
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp
  · simpa using (edist_le_pi_edist f g j).trans (le_max_right _ _)

theorem prop_kronecker_cons_le {n : ℕ} {l k p q : Type*} (A : Matrix l k ℚ) (B : Matrix p q ℚ)
    (a : k → E) (a' : l → E) (b : q → Fin n → E) (b' : p → Fin n → E) :
    prop (A ⊗ₖ B) (fun x ↦ (Fin.cons (a x.1) (b x.2) : Fin (n + 1) → E))
      (fun x ↦ (Fin.cons (a' x.1) (b' x.2) : Fin (n + 1) → E)) ≤
        max (prop A a a') (prop B b b') := by
  refine prop_le_iff.mpr fun x y h ↦ ?_
  rw [kronecker_apply] at h
  exact (edist_cons_le _ _ _ _).trans (max_le_max (edist_le_prop (left_ne_zero_of_mul h))
    (edist_le_prop (right_ne_zero_of_mul h)))

theorem prop_kronecker_fst_le {l k p q : Type*} (A : Matrix l k ℚ) (B : Matrix p q ℚ)
    (a : k → E) (a' : l → E) :
    prop (A ⊗ₖ B) (fun x : k × q ↦ a x.1) (fun x : l × p ↦ a' x.1) ≤ prop A a a' :=
  prop_le_iff.mpr fun _ _ h ↦ edist_le_prop (left_ne_zero_of_mul (by rwa [kronecker_apply] at h))

theorem prop_fin_zero {k l : Type*} (u : Matrix l k ℚ) (a : k → Fin 0 → E) (b : l → Fin 0 → E) :
    prop u a b = 0 :=
  le_antisymm (prop_le_iff.mpr fun x y _ ↦ by rw [Subsingleton.elim (b x) (a y), edist_self])
    bot_le

theorem prop_diagonal_le {k : Type*} [DecidableEq k] (v : k → ℚ) (a : k → E) {r : ℝ≥0∞} :
    prop (diagonal v) a a ≤ r := by
  rw [prop_diagonal]; exact zero_le

namespace BasedComplex

/-- Labels of an iterated tensor product: the coordinates are the factors' labels. -/
def prodLabel : (n : ℕ) → {C : Fin n → BasedComplex} → (∀ i, (C i).X → E) →
    (prodComplex n C).X → Fin n → E
  | 0, _, _ => fun _ ↦ Fin.elim0
  | n + 1, _, a => fun p ↦ Fin.cons (a 0 p.1) (prodLabel n (fun i ↦ a i.succ) p.2)

omit [PseudoEMetricSpace E] in
theorem Geometry.pi_center : (n : ℕ) → {C : Fin n → BasedComplex} → (g : ∀ i, Geometry (C i) E) →
    (Geometry.pi n g).center = prodLabel n fun i ↦ (g i).center
  | 0, _, _ => rfl
  | n + 1, _, g => by
    funext p
    change (Fin.cons _ ((Geometry.pi n fun i ↦ g i.succ).center p.2) : Fin (n + 1) → E) = _
    rw [Geometry.pi_center n]
    rfl

theorem prop_tensor_d_cons_le {C D : BasedComplex} {n : ℕ} (a : C.X → E) (b : D.X → Fin n → E) :
    prop (C.tensor D).d (fun q ↦ (Fin.cons (a q.1) (b q.2) : Fin (n + 1) → E))
      (fun q ↦ (Fin.cons (a q.1) (b q.2) : Fin (n + 1) → E)) ≤
        max (prop C.d a a) (prop D.d b b) := by
  refine (prop_add_le).trans (max_le ?_ ?_)
  · refine (prop_kronecker_cons_le _ _ _ _ _ _).trans ?_
    rw [prop_one]; simp
  · refine (prop_kronecker_cons_le _ _ _ _ _ _).trans ?_
    rw [sgn, prop_diagonal]; simp

theorem prop_prod_d_le {r : ℝ≥0∞} : (n : ℕ) → {C : Fin n → BasedComplex} → {a : ∀ i, (C i).X → E} →
    (∀ i, prop (C i).d (a i) (a i) ≤ r) →
    prop (prodComplex n C).d (prodLabel n a) (prodLabel n a) ≤ r
  | 0, _, _, _ => by rw [prop_fin_zero]; exact zero_le
  | n + 1, _, _, h => (prop_tensor_d_cons_le _ _).trans
      (max_le (h 0) (prop_prod_d_le n fun i ↦ h i.succ))

/-! ### Propagation bounds for duality equivalences -/

/-- Propagation bounds for a homotopy equivalence: `r` for the maps, `s` for the homotopies. -/
structure HtpyEquiv.PropLE {A B : BasedComplex} (e : HtpyEquiv A B) (a : A.X → E) (b : B.X → E)
    (r s : ℝ≥0∞) : Prop where
  hom : prop e.hom.f a b ≤ r
  inv : prop e.inv.f b a ≤ r
  homInv : prop e.homInv.h a a ≤ s
  invHom : prop e.invHom.h b b ≤ s

variable {C C' D D' : BasedComplex} {N N' M : ℕ} {r s : ℝ≥0∞}

theorem HtpyEquiv.PropLE.castDim {hN : C.DimLE N} {e : HtpyEquiv (C.dual N hN) D} {a : C.X → E}
    {b : D.X → E} (he : e.PropLE a b r s) (h : N = N') (hN' : C.DimLE N') :
    (e.castDim h hN').PropLE a b r s :=
  ⟨by simpa using he.hom, by simpa using he.inv, by simpa using he.homInv,
    by simpa using he.invHom⟩

theorem prop_mul_le_of_le {A B C : Type*} [Fintype B] {u : Matrix B A ℚ} {w : Matrix C B ℚ}
    {a : A → E} {b : B → E} {c : C → E} {r r' t : ℝ≥0∞} (hu : prop u a b ≤ r)
    (hw : prop w b c ≤ r') (h : r + r' ≤ t) : prop (w * u) a c ≤ t :=
  (prop_mul_le w b c u).trans ((add_le_add hu hw).trans h)

theorem HtpyEquiv.PropLE.dualTensor {n : ℕ} {hC : C.DimLE N} {hC' : C'.DimLE M}
    {e : HtpyEquiv (C.dual N hC) D} {e' : HtpyEquiv (C'.dual M hC') D'} {a : C.X → E}
    {b : D.X → E} {a' : C'.X → Fin n → E} {b' : D'.X → Fin n → E} (he : e.PropLE a b r s)
    (he' : e'.PropLE a' b' r s) (hrs : r + r ≤ s) :
    (e.dualTensor e').PropLE (fun q ↦ (Fin.cons (a q.1) (a' q.2) : Fin (n + 1) → E))
      (fun q ↦ (Fin.cons (b q.1) (b' q.2) : Fin (n + 1) → E)) r s := by
  have hb : prop (e'.inv.f * e'.hom.f) a' a' ≤ s := prop_mul_le_of_le he'.hom he'.inv hrs
  have hb' : prop (e'.hom.f * e'.inv.f) b' b' ≤ s := prop_mul_le_of_le he'.inv he'.hom hrs
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [HtpyEquiv.dualTensor_hom_f]
    exact prop_mul_le_of_le (prop_diagonal_le _ _) ((prop_kronecker_cons_le _ _ _ _ _ _).trans
      (max_le he.hom he'.hom)) (by rw [zero_add])
  · rw [HtpyEquiv.dualTensor_inv_f]
    exact prop_mul_le_of_le ((prop_kronecker_cons_le _ _ _ _ _ _).trans (max_le he.inv he'.inv))
      (prop_diagonal_le _ _) (by rw [add_zero])
  · rw [HtpyEquiv.dualTensor_homInv_h]
    refine prop_mul_le_of_le (prop_mul_le_of_le (prop_diagonal_le _ _) (prop_add_le.trans
      (max_le ((prop_kronecker_cons_le _ _ _ _ _ _).trans (max_le he.homInv hb))
        ((prop_kronecker_cons_le _ _ _ _ _ _).trans
          (max_le (prop_diagonal_le _ _) he'.homInv)))) (by rw [zero_add]))
      (prop_diagonal_le _ _) (by rw [add_zero])
  · rw [HtpyEquiv.dualTensor_invHom_h]
    exact prop_add_le.trans (max_le ((prop_kronecker_cons_le _ _ _ _ _ _).trans
      (max_le he.invHom hb')) ((prop_kronecker_cons_le _ _ _ _ _ _).trans
        (max_le (prop_diagonal_le _ _) he'.invHom)))

/-- Labels on the first factor only (e.g. `W = Tⁿ ⊗ CPcell`, control ignores `CP²`). -/
theorem HtpyEquiv.PropLE.dualTensor_fst {hC : C.DimLE N} {hC' : C'.DimLE M}
    {e : HtpyEquiv (C.dual N hC) D} {a : C.X → E} {b : D.X → E} (he : e.PropLE a b r s)
    (e' : HtpyEquiv (C'.dual M hC') D') :
    (e.dualTensor e').PropLE (fun q ↦ a q.1) (fun q ↦ b q.1) r s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [HtpyEquiv.dualTensor_hom_f]
    exact prop_mul_le_of_le (prop_diagonal_le _ _)
      ((prop_kronecker_fst_le _ _ _ _).trans he.hom) (by rw [zero_add])
  · rw [HtpyEquiv.dualTensor_inv_f]
    exact prop_mul_le_of_le ((prop_kronecker_fst_le _ _ _ _).trans he.inv)
      (prop_diagonal_le _ _) (by rw [add_zero])
  · rw [HtpyEquiv.dualTensor_homInv_h]
    refine prop_mul_le_of_le (prop_mul_le_of_le (prop_diagonal_le _ _) (prop_add_le.trans
      (max_le ((prop_kronecker_fst_le _ _ _ _).trans he.homInv)
        ((prop_kronecker_fst_le _ _ _ _).trans (prop_diagonal_le _ _)))) (by rw [zero_add]))
      (prop_diagonal_le _ _) (by rw [add_zero])
  · rw [HtpyEquiv.dualTensor_invHom_h]
    exact prop_add_le.trans (max_le ((prop_kronecker_fst_le _ _ _ _).trans he.invHom)
      ((prop_kronecker_fst_le _ _ _ _).trans (prop_diagonal_le _ _)))

/-- Radii of iterated tensor products: maps `≤ r`, homotopies `≤ s` if `2r ≤ s`. -/
theorem HtpyEquiv.PropLE.dualProd (hrs : r + r ≤ s) : (n : ℕ) → {C D : Fin n → BasedComplex} →
    {hC : ∀ i, (C i).DimLE 1} → {e : ∀ i, HtpyEquiv ((C i).dual 1 (hC i)) (D i)} →
    {a : ∀ i, (C i).X → E} → {b : ∀ i, (D i).X → E} → (∀ i, (e i).PropLE (a i) (b i) r s) →
    (HtpyEquiv.dualProd n hC e).PropLE (prodLabel n a) (prodLabel n b) r s
  | 0, _, _, _, _, _, _, _ => ⟨by rw [prop_fin_zero]; exact zero_le,
      by rw [prop_fin_zero]; exact zero_le, by rw [prop_fin_zero]; exact zero_le,
      by rw [prop_fin_zero]; exact zero_le⟩
  | n + 1, _, _, _, _, _, _, h =>
    ((h 0).dualTensor (HtpyEquiv.PropLE.dualProd hrs n fun i ↦ h i.succ) hrs).castDim _ _

end BasedComplex

end Labels

/-! ### Controlled sequences through uniformly continuous labels -/

namespace BasedComplex

section Control

variable {X : Type u} [PseudoEMetricSpace X] {Y : Type*} [PseudoEMetricSpace Y]

/-- **Propagation through labels**: if propagation in `Y` tends to `0`, so does propagation of
the labels `λ ∘ a` for uniformly continuous `λ : Y → X`. -/
theorem PropTendsto.of_uniformContinuous {lab : Y → X} (hlab : UniformContinuous lab)
    {C D : ℕ → BasedComplex} {u : ∀ i, Matrix (D i).X (C i).X ℚ} {a : ∀ i, (C i).X → Y}
    {b : ∀ i, (D i).X → Y} (hu : Tendsto (fun i ↦ prop (u i) (a i) (b i)) atTop (𝓝 0)) :
    PropTendsto u (fun i ↦ lab ∘ a i) (fun i ↦ lab ∘ b i) := by
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε ↦ ?_
  obtain ⟨δ, hδ, hlabδ⟩ := EMetric.uniformContinuous_iff.1 hlab ε hε
  filter_upwards [(tendsto_order.1 hu).2 δ hδ] with i hi
  exact prop_le_iff.mpr fun ρ σ h ↦ (hlabδ ((edist_le_prop h).trans_lt hi)).le

theorem PropTendsto.congr_label {C D : ℕ → BasedComplex} {u : ∀ i, Matrix (D i).X (C i).X ℚ}
    {a a' : ∀ i, (C i).X → X} {b b' : ∀ i, (D i).X → X} (h : PropTendsto u a b) (ha : a = a')
    (hb : b = b') : PropTendsto u a' b' := by
  subst ha hb; exact h

/-- Bounds `r i, s i → 0` give a controlled homotopy equivalence through labels. -/
def ControlledSeq.HtpyEquiv.ofPropLE {A B : ControlledSeq X}
    (e : ∀ i, BasedComplex.HtpyEquiv (A.C i) (B.C i)) {lab : Y → X} (hlab : UniformContinuous lab)
    {a : ∀ i, (A.C i).X → Y} {b : ∀ i, (B.C i).X → Y} (ha : ∀ i, A.label i = lab ∘ a i)
    (hb : ∀ i, B.label i = lab ∘ b i) {r s : ℕ → ℝ≥0∞} (hr : Tendsto r atTop (𝓝 0))
    (hs : Tendsto s atTop (𝓝 0)) (he : ∀ i, (e i).PropLE (a i) (b i) (r i) (s i)) :
    ControlledSeq.HtpyEquiv A B :=
  have ha' : A.label = fun i ↦ lab ∘ a i := funext ha
  have hb' : B.label = fun i ↦ lab ∘ b i := funext hb
  { hom := ⟨fun i ↦ (e i).hom, (PropTendsto.of_uniformContinuous hlab
      (tendsto_zero_of_le hr fun i ↦ (he i).hom)).congr_label ha'.symm hb'.symm⟩
    inv := ⟨fun i ↦ (e i).inv, (PropTendsto.of_uniformContinuous hlab
      (tendsto_zero_of_le hr fun i ↦ (he i).inv)).congr_label hb'.symm ha'.symm⟩
    homInv := ⟨fun i ↦ (e i).homInv, (PropTendsto.of_uniformContinuous hlab
      (tendsto_zero_of_le hs fun i ↦ (he i).homInv)).congr_label ha'.symm ha'.symm⟩
    invHom := ⟨fun i ↦ (e i).invHom, (PropTendsto.of_uniformContinuous hlab
      (tendsto_zero_of_le hs fun i ↦ (he i).invHom)).congr_label hb'.symm hb'.symm⟩ }

/-- The `N`-dual of a controlled sequence, with the same labels. -/
@[reducible]
def ControlledSeq.dual (A : ControlledSeq X) (N : ℕ) (hN : ∀ i, (A.C i).DimLE N) :
    ControlledSeq X where
  C i := (A.C i).dual N (hN i)
  label := A.label
  tendsto_d := tendsto_zero_of_le A.tendsto_d fun i ↦ by
    refine (prop_smul_le _).trans (prop_mul_le_of_le (prop_diagonal_le _ _) ?_ (zero_add _).le)
    rw [prop_transpose]

end Control

/-! ### The circle on `ℝ/Lℤ` -/

variable (L : ℝ) [Fact (0 < L)]

/-- The mesh `η = L / m`. -/
def mesh (m : ℕ) : ℝ := L / m

section Circle

variable (m : ℕ) [NeZero m]

theorem mesh_pos : 0 < mesh L m :=
  div_pos Fact.out (Nat.cast_pos.mpr (NeZero.pos m))

omit [Fact (0 < L)] in
theorem mesh_mul : mesh L m * m = L :=
  div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (NeZero.ne m))

omit [Fact (0 < L)] in
theorem tendsto_mesh {m : ℕ → ℕ} (hm : Tendsto m atTop atTop) :
    Tendsto (fun i ↦ mesh L (m i)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hm)

omit [Fact (0 < L)] in
theorem tendsto_ofReal_mesh {m : ℕ → ℕ} (hm : Tendsto m atTop atTop) :
    Tendsto (fun i ↦ ENNReal.ofReal (mesh L (m i))) atTop (𝓝 0) := by
  simpa using ENNReal.tendsto_ofReal (tendsto_mesh L hm)

/-- Cell centres of `C_m` on `ℝ/Lℤ`: vertex `k ↦ k η`, edge `k ↦ (k + 1/2) η`. -/
def circle.center : (circle m).X → AddCircle L
  | .inl v => ((mesh L m * v : ℝ) : AddCircle L)
  | .inr e => ((mesh L m * (e + 1 / 2) : ℝ) : AddCircle L)

omit [Fact (0 < L)] in
theorem coe_mesh_mul_succ (e : Fin m) :
    ((mesh L m * ((e + 1 : Fin m) : ℕ) : ℝ) : AddCircle L) = ((mesh L m * (e + 1) : ℝ)) := by
  rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  rcases Nat.lt_or_ge ((e : ℕ) + 1) m with h | h
  · rw [Nat.mod_eq_of_lt h]; push_cast; rfl
  · have h' : (e : ℕ) + 1 = m := by have := e.2; omega
    rw [h', Nat.mod_self, show ((e : ℝ) + 1) = m by exact_mod_cast h', mesh_mul]
    simp [AddCircle.coe_period]

omit [Fact (0 < L)] in
theorem dist_coe_le (x y : ℝ) : dist (x : AddCircle L) (y : AddCircle L) ≤ |x - y| := by
  rw [dist_eq_norm, ← AddCircle.coe_sub, ← Real.norm_eq_abs]
  exact QuotientAddGroup.norm_mk_le_norm

/-- Cells that are faces of each other in `C_m`. -/
def circle.Adj : (circle m).X → (circle m).X → Prop
  | .inl v, .inr e => v = e ∨ v = e + 1
  | .inr e, .inl v => v = e ∨ v = e + 1
  | _, _ => False

theorem circle.edist_center_le {σ τ : (circle m).X} (h : circle.Adj m σ τ) :
    edist (circle.center L m σ) (circle.center L m τ) ≤ ENNReal.ofReal (mesh L m / 2) := by
  have hη := (mesh_pos L m).le
  have key : ∀ (v e : Fin m), v = e ∨ v = e + 1 →
      dist (circle.center L m (.inl v)) (circle.center L m (.inr e)) ≤ mesh L m / 2 := by
    rintro v e (rfl | rfl)
    · refine (dist_coe_le L _ _).trans_eq ?_
      rw [show mesh L m * v - mesh L m * (v + 1 / 2) = -(mesh L m / 2) by ring, abs_neg,
        abs_of_nonneg (by linarith)]
    · change dist ((mesh L m * ((e + 1 : Fin m) : ℕ) : ℝ) : AddCircle L) _ ≤ _
      rw [coe_mesh_mul_succ]
      refine (dist_coe_le L _ _).trans_eq ?_
      rw [show mesh L m * (e + 1) - mesh L m * (e + 1 / 2) = mesh L m / 2 by ring,
        abs_of_nonneg (by linarith)]
  rw [edist_dist]
  refine ENNReal.ofReal_le_ofReal ?_
  rcases σ with v | e <;> rcases τ with w | f <;> simp only [circle.Adj] at h
  · exact key v f h
  · rw [dist_comm]; exact key w e h

theorem circle.adj_symm {σ τ : (circle m).X} (h : circle.Adj m σ τ) : circle.Adj m τ σ := by
  rcases σ with v | e <;> rcases τ with w | f <;> exact h

theorem circle.prop_le {u : Matrix (circle m).X (circle m).X ℚ}
    (h : ∀ σ τ, u σ τ ≠ 0 → circle.Adj m σ τ) :
    prop u (circle.center L m) (circle.center L m) ≤ ENNReal.ofReal (mesh L m / 2) :=
  prop_le_iff.mpr fun σ τ hu ↦ circle.edist_center_le L m (h σ τ hu)

theorem circle.adj_of_d {σ τ : (circle m).X} (h : (circle m).d σ τ ≠ 0) : circle.Adj m σ τ := by
  rcases σ with v | e <;> rcases τ with w | f <;> simp at h
  simp only [circle.Adj]
  by_contra h'
  push_neg at h'
  exact h (by simp [h'.1, h'.2])

theorem circle.adj_of_cap {σ τ : (circle m).X} (h : (circle.cap m).f σ τ ≠ 0) :
    circle.Adj m σ τ := by
  rw [oneDim.cap_f] at h
  rcases σ with v | e <;> rcases τ with w | f <;> simp at h
  · exact .inl h.1
  · exact .inr h.1

theorem circle.adj_of_duality {σ τ : (circle m).X} (h : (circle.duality m).hom.f σ τ ≠ 0) :
    circle.Adj m σ τ := by
  rw [circle.duality_hom] at h
  simp only [sym, Hom.smul, Hom.add, Matrix.smul_apply, Matrix.add_apply, transpose_f_apply, smul_eq_mul] at h
  by_cases h₁ : (circle.cap m).f σ τ = 0
  · rw [h₁, zero_add] at h
    exact circle.adj_symm m (circle.adj_of_cap m (right_ne_zero_of_mul (right_ne_zero_of_mul h)))
  · exact circle.adj_of_cap m h₁

theorem circle.adj_of_bMat {σ τ : (circle m).X} (h : circle.bMat m σ τ ≠ 0) :
    circle.Adj m σ τ := by
  rcases σ with v | e <;> rcases τ with w | f <;> simp [circle.bMat] at h
  · exact .inr h
  · exact .inl h.symm

omit [Fact (0 < L)] in
theorem circle.prop_flip :
    prop (oneDim.flip (circle.isCycle_z m)).h (circle.center L m) (circle.center L m) = 0 := by
  refine le_antisymm (prop_le_iff.mpr fun σ τ h ↦ ?_) bot_le
  rcases σ with v | e <;> rcases τ with w | f <;> simp [oneDim.flip] at h
  rw [h.1, edist_self]

/-- Radii of the circle duality: `φ`, `b ≤ η/2`; homotopies `-½ b U`, `-½ U b ≤ η/2 ≤ η`. -/
theorem circle.propLE : (circle.duality m).toHtpyEquiv.PropLE (circle.center L m)
    (circle.center L m) (ENNReal.ofReal (mesh L m / 2)) (ENNReal.ofReal (mesh L m)) := by
  have hle : ENNReal.ofReal (mesh L m / 2) ≤ ENNReal.ofReal (mesh L m) :=
    ENNReal.ofReal_le_ofReal (by linarith [mesh_pos L m])
  have hU : prop (-((1 / 2 : ℚ) • (oneDim.flip (circle.isCycle_z m)).h)) (circle.center L m)
      (circle.center L m) ≤ 0 := by
    rw [prop_neg]; exact (prop_smul_le _).trans (circle.prop_flip L m).le
  have hb : prop (circle.bMat m) (circle.center L m) (circle.center L m) ≤
      ENNReal.ofReal (mesh L m / 2) := circle.prop_le L m fun _ _ ↦ circle.adj_of_bMat m
  refine ⟨circle.prop_le L m fun _ _ ↦ circle.adj_of_duality m, hb, ?_, ?_⟩
  · change prop (circle.duality m).homInv.h _ _ ≤ _
    rw [circle.duality_homInv_h]
    exact prop_mul_le_of_le hU hb (by rw [zero_add]; exact hle)
  · change prop (circle.duality m).invHom.h _ _ ≤ _
    rw [circle.duality_invHom_h]
    exact prop_mul_le_of_le hb hU (by rw [add_zero]; exact hle)

/-- The closed carriers: a vertex, or the image of `[k η, (k+1) η]`. -/
def circle.carrier : (circle m).X → Set (AddCircle L)
  | .inl v => {circle.center L m (.inl v)}
  | .inr e => (fun t : ℝ ↦ (t : AddCircle L)) '' Set.Icc (mesh L m * e) (mesh L m * (e + 1))

/-- The geometry of `C_m` on `ℝ/Lℤ`: nested carriers with no seam. -/
def circle.geometry : Geometry (circle m) (AddCircle L) where
  center := circle.center L m
  carrier := circle.carrier L m
  center_mem := by
    have hη := (mesh_pos L m).le
    rintro (v | e)
    · rfl
    · exact ⟨mesh L m * (e + 1 / 2), ⟨by nlinarith, by nlinarith⟩, rfl⟩
  face_sub := by
    have hη := (mesh_pos L m).le
    intro σ τ h
    have h' := circle.adj_of_d m h
    rcases σ with v | e <;> rcases τ with w | f <;> simp only [circle.Adj] at h'
    · rintro x rfl
      rcases h' with rfl | rfl
      · exact ⟨mesh L m * v, ⟨le_rfl, by nlinarith⟩, rfl⟩
      · refine ⟨mesh L m * (f + 1), ⟨by nlinarith, le_rfl⟩, ?_⟩
        exact (coe_mesh_mul_succ L m f).symm
    · simp at h

end Circle

/-! ### The torus on `(ℝ/Lℤ)ⁿ` -/

section Torus

variable (m n : ℕ) [NeZero m]

/-- Cell centres of `Tⁿ` in `(ℝ/Lℤ)ⁿ`. -/
def torus.center : (torus m n).X → Fin n → AddCircle L := prodLabel n fun _ ↦ circle.center L m

/-- The geometry of `Tⁿ` on `(ℝ/Lℤ)ⁿ`: product carriers, `face_sub` everywhere (no seam). -/
def torus.geometry : Geometry (torus m n) (Fin n → AddCircle L) :=
  Geometry.pi n fun _ ↦ circle.geometry L m

theorem torus.geometry_center : (torus.geometry L m n).center = torus.center L m n :=
  Geometry.pi_center n _

/-- The boundary of `Tⁿ` propagates `≤ η/2`. -/
theorem torus.prop_d_le :
    prop (torus m n).d (torus.center L m n) (torus.center L m n) ≤
      ENNReal.ofReal (mesh L m / 2) :=
  prop_prod_d_le n fun _ ↦ circle.prop_le L m fun _ _ ↦ circle.adj_of_d m

theorem ofReal_half_add_half :
    ENNReal.ofReal (mesh L m / 2) + ENNReal.ofReal (mesh L m / 2) ≤ ENNReal.ofReal (mesh L m) := by
  have := (mesh_pos L m).le
  rw [← ENNReal.ofReal_add (by linarith) (by linarith), add_halves]

/-- **Radii of the torus duality** (sup metric on `(ℝ/Lℤ)ⁿ`, `η = L/m`): `φ` and `b` propagate
`≤ η/2`, the homotopies `H`, `H'` `≤ η`. -/
theorem torus.propLE : (torus.duality m n).toHtpyEquiv.PropLE (torus.center L m n)
    (torus.center L m n) (ENNReal.ofReal (mesh L m / 2)) (ENNReal.ofReal (mesh L m)) := by
  rw [torus.duality, SymDuality.prod_toHtpyEquiv]
  exact HtpyEquiv.PropLE.dualProd (ofReal_half_add_half L m) n fun _ ↦ circle.propLE L m

/-- The same radii for `W = Tⁿ ⊗ CPcell`, labelled through the torus factor. -/
theorem torusCP.propLE : (torusCP.duality m n).toHtpyEquiv.PropLE
    (fun q ↦ torus.center L m n q.1) (fun q ↦ torus.center L m n q.1)
    (ENNReal.ofReal (mesh L m / 2)) (ENNReal.ofReal (mesh L m)) :=
  (torus.propLE L m n).dualTensor_fst _

theorem torusCP.prop_d_le :
    prop (torusCP m n).d (fun q ↦ torus.center L m n q.1) (fun q ↦ torus.center L m n q.1) ≤
      ENNReal.ofReal (mesh L m / 2) :=
  prop_add_le.trans (max_le ((prop_kronecker_fst_le _ _ _ _).trans (torus.prop_d_le L m n))
    ((prop_kronecker_fst_le _ _ _ _).trans (prop_diagonal_le _ _)))

/-! ### Carriers and nearest vertices -/

theorem circle.dist_center_le_of_mem {σ : (circle m).X} {x : AddCircle L}
    (hx : x ∈ (circle.geometry L m).carrier σ) : dist x (circle.center L m σ) ≤ mesh L m / 2 := by
  have hη := (mesh_pos L m).le
  rcases σ with v | e
  · rw [hx, dist_self]; linarith
  · obtain ⟨t, ⟨h₁, h₂⟩, rfl⟩ := hx
    refine (dist_coe_le L _ _).trans ?_
    rw [abs_le]; constructor <;> linarith

omit [Fact (0 < L)] in
theorem Geometry.pi_dist_le {E : Type*} [PseudoMetricSpace E] {r : ℝ} (hr : 0 ≤ r) :
    (n : ℕ) → {C : Fin n → BasedComplex} → (g : ∀ i, Geometry (C i) E) →
    (∀ i σ x, x ∈ (g i).carrier σ → dist x ((g i).center σ) ≤ r) →
    ∀ σ x, x ∈ (Geometry.pi n g).carrier σ → dist x ((Geometry.pi n g).center σ) ≤ r
  | 0, _, _, _, σ, x, _ => by
    rw [Subsingleton.elim x ((Geometry.pi 0 _).center σ), dist_self]; exact hr
  | n + 1, _, g, h, σ, x, ⟨hx₀, hx⟩ => by
    refine (dist_pi_le_iff hr).mpr fun i ↦ ?_
    induction i using Fin.cases with
    | zero => exact h 0 _ _ hx₀
    | succ i =>
      exact (dist_le_pi_dist (Fin.tail x) _ i).trans
        (Geometry.pi_dist_le hr n (fun i ↦ g i.succ) (fun i ↦ h i.succ) σ.2 _ hx)

/-- Every carrier of `Tⁿ` lies in the `η/2`-ball (sup metric) around the cell's centre. -/
theorem torus.dist_center_le_of_mem (n : ℕ) {σ : (torus m n).X} {x : Fin n → AddCircle L}
    (hx : x ∈ (torus.geometry L m n).carrier σ) : dist x (torus.center L m n σ) ≤ mesh L m / 2 := by
  rw [← torus.geometry_center]
  exact Geometry.pi_dist_le (by linarith [mesh_pos L m]) n _
    (fun _ _ _ h ↦ circle.dist_center_le_of_mem L m h) σ x hx

/-- The vertex of `Tⁿ` with coordinates `v`. -/
def torus.vertex : (n : ℕ) → (Fin n → Fin m) → (torus m n).X
  | 0, _ => ()
  | n + 1, v => (.inl (v 0), torus.vertex n (Fin.tail v))

omit [Fact (0 < L)] in
theorem torus.deg_vertex : (n : ℕ) → (v : Fin n → Fin m) → (torus m n).deg (torus.vertex m n v) = 0
  | 0, _ => rfl
  | n + 1, v => by
    change 0 + (torus m n).deg (torus.vertex m n (Fin.tail v)) = 0
    rw [torus.deg_vertex n]

omit [Fact (0 < L)] in
theorem torus.center_vertex : (n : ℕ) → (v : Fin n → Fin m) →
    torus.center L m n (torus.vertex m n v) = fun i ↦ circle.center L m (.inl (v i))
  | 0, _ => funext fun i ↦ i.elim0
  | n + 1, v => by
    change (Fin.cons _ (torus.center L m n (torus.vertex m n (Fin.tail v))) :
      Fin (n + 1) → AddCircle L) = _
    rw [torus.center_vertex n]
    exact Fin.cons_self_tail (fun i ↦ circle.center L m (.inl (v i)))

omit [Fact (0 < L)] in
theorem coe_mesh_mul_mod {k : ℕ} (hk : k ≤ m) :
    ((mesh L m * (Fin.ofNat m k : ℕ) : ℝ) : AddCircle L) = ((mesh L m * k : ℝ)) := by
  rw [Fin.val_ofNat]
  rcases hk.lt_or_eq with h | rfl
  · rw [Nat.mod_eq_of_lt h]
  · rw [Nat.mod_self, mesh_mul]; simp [AddCircle.coe_period]

/-- Every point of `ℝ/Lℤ` is within `η/2` of a vertex of `C_m`. -/
theorem circle.exists_near (y : AddCircle L) :
    ∃ v : Fin m, dist y (circle.center L m (.inl v)) ≤ mesh L m / 2 := by
  have hη := mesh_pos L m
  obtain ⟨t, ⟨ht₀, htL⟩, rfl⟩ : ∃ t : ℝ, t ∈ Set.Ico 0 L ∧ (t : AddCircle L) = y :=
    ⟨_, by simpa using (AddCircle.equivIco L 0 y).2, (AddCircle.equivIco L 0).symm_apply_apply y⟩
  set s := t / mesh L m
  have hs : t = s * mesh L m := (div_mul_cancel₀ t hη.ne').symm
  have hs₀ : 0 ≤ s + 1 / 2 := by positivity
  set k := ⌊s + 1 / 2⌋₊
  have hk₁ : (k : ℝ) ≤ s + 1 / 2 := Nat.floor_le hs₀
  have hk₂ : s + 1 / 2 < k + 1 := Nat.lt_floor_add_one _
  have hkm : k ≤ m := by
    have : s < m := by
      rw [show s = t / mesh L m from rfl, div_lt_iff₀ hη, mul_comm, mesh_mul]; exact htL
    exact Nat.lt_succ_iff.mp ((Nat.floor_lt hs₀).mpr (by push_cast; linarith))
  refine ⟨Fin.ofNat m k, ?_⟩
  change dist _ ((mesh L m * (Fin.ofNat m k : ℕ) : ℝ) : AddCircle L) ≤ _
  rw [coe_mesh_mul_mod L m hkm]
  refine (dist_coe_le L _ _).trans ?_
  rw [abs_le, hs]
  constructor <;> nlinarith

/-- **Nearest vertex**: every point of `(ℝ/Lℤ)ⁿ` is within `η/2` of a vertex of `Tⁿ`. -/
theorem torus.exists_vertex_near (n : ℕ) (y : Fin n → AddCircle L) :
    ∃ σ, (torus m n).deg σ = 0 ∧ dist y (torus.center L m n σ) ≤ mesh L m / 2 := by
  choose v hv using fun i ↦ circle.exists_near L m (y i)
  refine ⟨torus.vertex m n v, torus.deg_vertex m n v, ?_⟩
  rw [torus.center_vertex]
  exact (dist_pi_le_iff (by linarith [mesh_pos L m])).mpr hv

end Torus

/-! ### Controlled sequences of tori -/

section Sequences

variable {X : Type u} [PseudoEMetricSpace X] (n : ℕ) (m : ℕ → ℕ) [∀ i, NeZero (m i)]

theorem torus.le_mesh (k : ℕ) [NeZero k] :
    ENNReal.ofReal (mesh L k / 2) ≤ ENNReal.ofReal (mesh L k) :=
  ENNReal.ofReal_le_ofReal (by linarith [mesh_pos L k])

/-- The tori `T^n_{m_i}`, labelled by `λ ∘ center` with `λ` continuous on `(ℝ/Lℤ)ⁿ`. -/
def torus.controlledSeq (hm : Tendsto m atTop atTop) (lab : (Fin n → AddCircle L) → X)
    (hlab : Continuous lab) : ControlledSeq X where
  C i := torus (m i) n
  label i := lab ∘ torus.center L (m i) n
  tendsto_d := .of_uniformContinuous (CompactSpace.uniformContinuous_of_continuous hlab)
    (tendsto_zero_of_le (tendsto_ofReal_mesh L hm) fun i ↦
      (torus.prop_d_le L (m i) n).trans (torus.le_mesh L (m i)))

/-- The chain models `W_i = T^n_{m_i} ⊗ CPcell`, labelled through the torus factor. -/
def torusCP.controlledSeq (hm : Tendsto m atTop atTop) (lab : (Fin n → AddCircle L) → X)
    (hlab : Continuous lab) : ControlledSeq X where
  C i := torusCP (m i) n
  label i := fun q ↦ lab (torus.center L (m i) n q.1)
  tendsto_d := .of_uniformContinuous (lab := lab)
    (CompactSpace.uniformContinuous_of_continuous hlab)
    (a := fun i (q : (torusCP (m i) n).X) ↦ torus.center L (m i) n q.1)
    (b := fun i (q : (torusCP (m i) n).X) ↦ torus.center L (m i) n q.1)
    (tendsto_zero_of_le (tendsto_ofReal_mesh L hm) fun i ↦
      (torusCP.prop_d_le L (m i) n).trans (torus.le_mesh L (m i)))

/-- **The controlled duality of `W_i`**: `φ_i`, `b_i`, `H_i`, `H'_i` are all controlled. -/
def torusCP.controlledDuality (hm : Tendsto m atTop atTop) (lab : (Fin n → AddCircle L) → X)
    (hlab : Continuous lab) :
    ControlledSeq.HtpyEquiv ((torusCP.controlledSeq L n m hm lab hlab).dual (n + 4)
      fun i ↦ torusCP.dimLE (m i) n) (torusCP.controlledSeq L n m hm lab hlab) :=
  ControlledSeq.HtpyEquiv.ofPropLE (fun i ↦ (torusCP.duality (m i) n).toHtpyEquiv)
    (CompactSpace.uniformContinuous_of_continuous hlab)
    (a := fun i (q : (torusCP (m i) n).X) ↦ torus.center L (m i) n q.1)
    (b := fun i (q : (torusCP (m i) n).X) ↦ torus.center L (m i) n q.1) (fun _ ↦ rfl)
    (fun _ ↦ rfl) (tendsto_zero_of_le (tendsto_ofReal_mesh L hm) fun i ↦ torus.le_mesh L (m i))
    (tendsto_ofReal_mesh L hm) fun i ↦ torusCP.propLE L (m i) n

theorem torusCP.controlledDuality_hom (hm : Tendsto m atTop atTop)
    (lab : (Fin n → AddCircle L) → X) (hlab : Continuous lab) (i : ℕ) :
    (torusCP.controlledDuality L n m hm lab hlab).hom.f i = (torusCP.duality (m i) n).hom :=
  rfl

end Sequences

/-! ### Chart labels across the seam -/

section Lift

/-- The lift `ℝ/Lℤ → [-L/2, L/2)`. -/
def liftHalf (x : AddCircle L) : ℝ := (AddCircle.equivIco L (-(L / 2)) x : ℝ)

theorem coe_liftHalf (x : AddCircle L) : ((liftHalf L x : ℝ) : AddCircle L) = x := by
  conv_rhs => rw [← (AddCircle.equivIco L (-(L / 2))).symm_apply_apply x]
  rfl

theorem abs_liftHalf (x : AddCircle L) : |liftHalf L x| = ‖x‖ := by
  have hL : (0 : ℝ) < L := Fact.out
  have h : liftHalf L x ∈ Set.Ico (-(L / 2)) (-(L / 2) + L) := (AddCircle.equivIco L _ x).2
  conv_rhs => rw [← coe_liftHalf L x]
  refine ((AddCircle.norm_coe_eq_abs_iff L hL.ne').mpr ?_).symm
  rw [abs_of_pos hL, abs_le]
  exact ⟨h.1, by linarith [h.2]⟩

variable {n : ℕ}

/-- The lift `(ℝ/Lℤ)ⁿ → [-L/2, L/2)ⁿ ⊆ ℝⁿ` (the chart coordinates; `B(0, 4) ⊆ [-8, 8)ⁿ` for
`L = 16`). -/
def liftVec (x : Fin n → AddCircle L) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i ↦ liftHalf L (x i)

/-- **Labels across the seam**: a continuous map on `Sⁿ = OnePoint ℝⁿ` that is constant on
`‖v‖ ≥ r` with `r < L/2` gives a continuous label on `(ℝ/Lℤ)ⁿ` through the lift. -/
theorem continuous_comp_liftVec {Z : Type*} [TopologicalSpace Z]
    {F : OnePoint (EuclideanSpace ℝ (Fin n)) → Z} (hF : Continuous F) {r : ℝ} (hr : r < L / 2)
    (hconst : ∀ v : EuclideanSpace ℝ (Fin n), r ≤ ‖v‖ → F v = F OnePoint.infty) :
    Continuous fun x ↦ F (liftVec L x : EuclideanSpace ℝ (Fin n)) := by
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  by_cases hx : ∀ i, x i ≠ ((-(L / 2) : ℝ) : AddCircle L)
  · have h₁ : ∀ i, ContinuousAt (fun y : Fin n → AddCircle L ↦ liftHalf L (y i)) x := fun i ↦
      (continuous_subtype_val.continuousAt.comp (AddCircle.continuousAt_equivIco L _ (hx i))).comp
        (f := fun y : Fin n → AddCircle L ↦ y i) (continuous_apply i).continuousAt
    have h : ContinuousAt (liftVec L) x :=
      (PiLp.continuous_toLp 2 _).continuousAt.comp (continuousAt_pi.mpr h₁)
    exact hF.continuousAt.comp (OnePoint.continuous_coe.continuousAt.comp h)
  · push_neg at hx
    obtain ⟨i, hi⟩ := hx
    have hL : (0 : ℝ) < L := Fact.out
    have hnorm : ‖x i‖ = L / 2 := by
      rw [hi, (AddCircle.norm_coe_eq_abs_iff L hL.ne').mpr (by
        rw [abs_neg, abs_of_pos hL, abs_of_pos (by linarith)]), abs_neg,
        abs_of_pos (by linarith)]
    have hev : ∀ᶠ y in 𝓝 x, F (liftVec L y : EuclideanSpace ℝ (Fin n)) = F OnePoint.infty := by
      filter_upwards [((continuous_apply i).tendsto x).eventually
        (Metric.ball_mem_nhds (x i) (show 0 < L / 2 - r by linarith))] with y hy
      refine hconst _ ?_
      have h₁ : r < ‖y i‖ := by
        have := norm_sub_norm_le (x i) (y i)
        rw [← dist_eq_norm, dist_comm] at this
        have hy' : dist (y i) (x i) < L / 2 - r := hy
        linarith
      have h₂ : ‖y i‖ ≤ ‖liftVec L y‖ := by
        rw [← abs_liftHalf, ← Real.norm_eq_abs]
        exact PiLp.norm_apply_le (liftVec L y) i
      linarith
    exact (continuousAt_const (y := F OnePoint.infty)).congr (hev.mono fun _ h ↦ h.symm)

end Lift

end BasedComplex

end HSFormal.Cubical

/-! ### The `Sⁿ`-label of the fixed data -/

namespace HSFormal.FixedData

open HSFormal.Cubical HSFormal.Cubical.BasedComplex

instance : Fact (0 < (16 : ℝ)) := ⟨by norm_num⟩

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {M : Type*} [TopologicalSpace M] [AddAction ℤ_[p] M]
  [ContinuousVAdd ℤ_[p] M] [LocallyCompactSpace M] [FirstCountableTopology M] (d : FixedData p n M)

/-- The `Sⁿ`-label of a point of the torus `(ℝ/16ℤ)ⁿ ⊇ [-8, 8)ⁿ ⊇ B(0, 4)`: `f̂` of its lift
(`f̂ = ∞` off `B(0, 2)`, so it is well defined across the seam). -/
def torusLabel (x : Fin n → AddCircle (16 : ℝ)) : RoundSphere n := d.fhat (liftVec 16 x)

theorem continuous_torusLabel : Continuous d.torusLabel :=
  continuous_comp_liftVec 16 d.fhat.continuous (r := 2) (by norm_num) fun v hv ↦ by
    rw [d.fhat_coe, ite_eq_right (not_lt.mpr hv)]; rfl

end HSFormal.FixedData
