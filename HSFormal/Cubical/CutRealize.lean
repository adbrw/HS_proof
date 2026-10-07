import HSFormal.Cubical.SeqDual
import HSFormal.Cubical.PinchFace
import HSFormal.LTheory.BoundaryPoincare

/-!
# Realized cut pairs of controlled sequences (cubical module C8, the pairs of Lemma 11.2)

Restrictions of a controlled sequence to locally closed cells (`ControlledSeq.restrict`), the
controlled inclusions and projections of subcomplexes and the realized degreewise split
sequences `0 → A_S → A → A/A_S → 0` over the prequotient `AsymptoticObject π X`.

**Based pairs** (`SeqPair`): a controlled sequence `D` of dimension `N + 1`, a subcomplex `Σ` of
dimension `N`, and a controlled `(N+1)`-symmetric top matrix `T` whose defect `d T - T δ` is
carried by `Σ × Σ`.  Then the defect restricted to `Σ` is a strictly symmetric chain map
`φ : Σ^{N-*} → Σ` (`SeqPair.bdHom`), `T` is a symmetric relative boundary
`j φ j^* = d T + T δ` in the prequotient (`SeqPair.δφ`), and the relative duality map `Ψ` of
the realized pair, precomposed with `(Cone(j) → D/Σ)^*`, is the realized relative cap
`T|_{D/Σ}` (`SeqPair.dualHom_coneToCoker_comp_relDuality`).  So if the relative cap is an
equivalence, the pair is a `SymPair` (`SeqPair.toSymPair`, by R1 and
`isKarEquiv_relDuality_of_split`).
-/

noncomputable section

namespace HSFormal.Cubical

open Filter Matrix CategoryTheory CategoryTheory.Limits HSFormal.LTheory HSFormal.Compression
open scoped ENNReal Topology

namespace BasedComplex

/-! ### Based pairs from symmetric tops -/

section BasedPair

variable {C : BasedComplex} {N : ℕ} (hC : C.DimLE (N + 1)) (T : Matrix C.X C.X ℚ)

/-- `d 𝒟 = -𝒟 δ` for the defect of any matrix. -/
theorem d_mul_defect : C.d * defect C (N + 1) hC T = -(defect C (N + 1) hC T * (C.dual (N + 1) hC).d) := by
  rw [defect, Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, C.d_d, Matrix.zero_mul,
    Matrix.mul_assoc T, (C.dual (N + 1) hC).d_d, Matrix.mul_zero, Matrix.mul_assoc]
  abel

variable {T}
variable (hTdeg : ∀ σ τ, T σ τ ≠ 0 → C.deg σ + C.deg τ = N + 1)
  (hT : ∀ σ τ, ((-1 : ℚ) ^ (N + 1 + 1)) ^ C.deg σ * T τ σ = T σ τ)

include hTdeg in
/-- The degrees of a nonzero defect entry add up to `N`. -/
theorem defect_deg {σ τ : C.X} (h : defect C (N + 1) hC T σ τ ≠ 0) :
    C.deg σ + C.deg τ = N := by
  rw [defect, Matrix.sub_apply] at h
  by_cases h₁ : (C.d * T) σ τ = 0
  · rw [h₁, zero_sub, neg_ne_zero] at h
    obtain ⟨κ, hκ⟩ := exists_mul_apply_ne_zero h
    have e₁ := hTdeg _ _ hκ.1
    have e₂ := (C.dual (N + 1) hC).d_deg _ _ hκ.2
    have := hC τ
    have := hC κ
    change N + 1 - C.deg τ = N + 1 - C.deg κ + 1 at e₂
    omega
  · obtain ⟨κ, hκ⟩ := exists_mul_apply_ne_zero h₁
    have e₁ := C.d_deg _ _ hκ.1
    have e₂ := hTdeg _ _ hκ.2
    omega

include hTdeg hT in
theorem defect_term₁ (σ τ κ : C.X) :
    ((-1 : ℚ) ^ (N + 1)) ^ C.deg σ * (C.d τ κ * T κ σ) =
      -(T σ κ * (C.dual (N + 1) hC).d κ τ) := by
  rw [dual_d_apply]
  by_cases hd : C.d τ κ = 0
  · simp [hd]
  by_cases h0 : T σ κ = 0
  · rw [← hT κ σ, h0]; simp
  have e₁ := C.d_deg _ _ hd
  have e₂ := hTdeg _ _ h0
  rw [← hT κ σ, e₁]
  have hs := cut_sign₂ (a := C.deg σ) (b := C.deg τ) (N := N) (by omega)
  linear_combination (C.d τ κ * T σ κ) * hs

include hTdeg hT in
theorem defect_term₂ (σ τ κ : C.X) :
    ((-1 : ℚ) ^ (N + 1)) ^ C.deg σ * (T τ κ * (C.dual (N + 1) hC).d κ σ) =
      -(C.d σ κ * T κ τ) := by
  rw [dual_d_apply]
  by_cases hd : C.d σ κ = 0
  · simp [hd]
  by_cases h0 : T κ τ = 0
  · rw [← hT τ κ, h0]; simp
  have e₁ := C.d_deg _ _ hd
  have e₂ := hTdeg _ _ h0
  rw [← hT τ κ]
  have hs := cut_sign₁ (a := C.deg σ) (b := C.deg τ) (N := N) (by omega)
  linear_combination (C.d σ κ * T κ τ) * hs

include hTdeg hT in
/-- **The defect of an `(N+1)`-symmetric top is `N`-symmetric.** -/
theorem defect_symm (σ τ : C.X) :
    ((-1 : ℚ) ^ (N + 1)) ^ C.deg σ * defect C (N + 1) hC T τ σ = defect C (N + 1) hC T σ τ := by
  simp only [defect, Matrix.sub_apply, mul_apply, mul_sub, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun κ _ ↦ defect_term₁ hC hTdeg hT σ τ κ,
    Finset.sum_congr rfl fun κ _ ↦ defect_term₂ hC hTdeg hT σ τ κ, Finset.sum_neg_distrib,
    Finset.sum_neg_distrib]
  ring

variable {S : C.X → Prop} [DecidablePred S] (hS : C.IsSub S)
  (hsupp : ∀ σ τ, defect C (N + 1) hC T σ τ ≠ 0 → S σ ∧ S τ)

include hTdeg hsupp in
/-- **The boundary structure** of a based pair: the defect of the top on the boundary
subcomplex, a chain map `Σ^{N-*} → Σ`. -/
def bdHomB (hSN : (C.restrict S hS.isLocallyClosed).DimLE N) :
    Hom ((C.restrict S hS.isLocallyClosed).dual N hSN) (C.restrict S hS.isLocallyClosed) where
  f := (defect C (N + 1) hC T).submatrix Subtype.val Subtype.val
  deg0 σ τ h := by
    have := defect_deg hC hTdeg h
    have h' : C.deg τ.1 ≤ N := hSN τ
    change (C.deg σ.1 : ℤ) = ((N - C.deg τ.1 : ℕ) : ℤ) + 0
    omega
  comm := by
    ext σ τ
    have hd := congr_fun (congr_fun (d_mul_defect hC T) σ.1) τ.1
    rw [Matrix.neg_apply, mul_apply, mul_apply] at hd
    have key : ∀ x : {σ // S σ}, ((C.restrict S hS.isLocallyClosed).dual N hSN).d x τ =
        (-1) ^ N * ((-1) ^ C.deg τ.1 * C.d τ.1 x.1) := fun x ↦ dual_d_apply hSN x τ
    rw [mul_apply, mul_apply, Finset.sum_congr rfl fun x _ ↦ congrArg _ (key x)]
    change ∑ x : {σ // S σ}, C.d σ.1 x.1 * defect C (N + 1) hC T x.1 τ.1 =
      ∑ x : {σ // S σ}, defect C (N + 1) hC T σ.1 x.1 * ((-1) ^ N * ((-1) ^ C.deg τ.1 * C.d τ.1 x.1))
    rw [sum_subtype_eq (P := S) (fun κ ↦ C.d σ.1 κ * defect C (N + 1) hC T κ τ.1)
      (fun κ h ↦ (hsupp _ _ (right_ne_zero_of_mul h)).1)]
    rw [sum_subtype_eq (P := S) (fun κ ↦ defect C (N + 1) hC T σ.1 κ *
        ((-1) ^ N * ((-1) ^ C.deg τ.1 * C.d τ.1 κ)))
      (fun κ h ↦ (hsupp _ _ (left_ne_zero_of_mul h)).2), hd, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun κ _ ↦ ?_
    rw [dual_d_apply, pow_succ]
    ring

theorem bdHomB_f (hSN : (C.restrict S hS.isLocallyClosed).DimLE N) :
    (bdHomB hC hTdeg hS hsupp hSN).f = (defect C (N + 1) hC T).submatrix Subtype.val Subtype.val :=
  rfl

include hT in
theorem isSymm_bdHomB (hSN : (C.restrict S hS.isLocallyClosed).DimLE N) :
    IsSymm hSN (bdHomB hC hTdeg hS hsupp hSN) :=
  (isSymm_iff _).mpr fun σ τ ↦ defect_symm hC hTdeg hT σ.1 τ.1

include hTdeg hsupp in
/-- **The relative cap** of a based pair: the top on cochains vanishing on `Σ`,
`C^{N+1-*}(D, Σ) → C(D)`. -/
def relHomB : Hom ((C.restrict (fun σ ↦ ¬S σ) hS.isLocallyClosed_compl).dual (N + 1)
    (hC.restrict _ _)) C where
  f := T.submatrix id Subtype.val
  deg0 σ τ h := by
    have := hTdeg σ τ.1 h
    have := hC τ.1
    change (C.deg σ : ℤ) = ((N + 1 - C.deg τ.1 : ℕ) : ℤ) + 0
    omega
  comm := by
    ext σ τ
    rw [restrict_dual_d hC, mul_submatrix_apply (P := fun σ ↦ ¬S σ)]
    · have h0 : defect C (N + 1) hC T σ τ.1 = 0 := by_contra fun h' ↦ τ.2 (hsupp _ _ h').2
      rw [defect, Matrix.sub_apply, sub_eq_zero] at h0
      simp only [mul_apply, submatrix_apply, id] at h0 ⊢
      exact h0
    · intro κ hκ hSκ
      refine τ.2 (hS _ _ (fun h₀ ↦ right_ne_zero_of_mul hκ ?_) hSκ)
      rw [dual_d_apply, h₀]; ring

theorem relHomB_f :
    (relHomB hC hTdeg hS hsupp).f = T.submatrix id Subtype.val := rfl

end BasedPair

/-! ### Restrictions of controlled sequences -/

/-- Matrices whose nonzero entries join cells with equal labels have propagation `0`. -/
theorem PropTendsto.of_label_eq {X : Type} [PseudoEMetricSpace X] {C D : ℕ → BasedComplex}
    {u : ∀ i, Matrix (D i).X (C i).X ℚ} {a : ∀ i, (C i).X → X} {b : ∀ i, (D i).X → X}
    (h : ∀ i κ σ, u i κ σ ≠ 0 → b i κ = a i σ) : PropTendsto u a b :=
  tendsto_zero_of_forall_eq_zero fun i ↦ le_antisymm
    (prop_le_iff.mpr fun κ σ hκσ ↦ by rw [h i κ σ hκσ, edist_self]) bot_le

/-- The transpose of a degree-`0` matrix has degree `0`. -/
theorem HasDeg.transpose0 {C D : BasedComplex} {u : Matrix D.X C.X ℚ} (h : HasDeg C D 0 u) :
    HasDeg D C 0 uᵀ := fun σ τ hστ ↦ by
  have := h τ σ (by rwa [transpose_apply] at hστ); omega

namespace ControlledSeq

variable {X : Type} [PseudoEMetricSpace X]

/-- The restriction of a controlled sequence to locally closed sets of cells. -/
@[simps]
def restrict (A : ControlledSeq X) (P : ∀ i, (A.C i).X → Prop) [∀ i, DecidablePred (P i)]
    (hP : ∀ i, (A.C i).IsLocallyClosed (P i)) : ControlledSeq X where
  C i := (A.C i).restrict (P i) (hP i)
  label i σ := A.label i σ.1
  tendsto_d := tendsto_zero_of_le A.tendsto_d fun i ↦
    prop_submatrix_le (u := (A.C i).d) (source := A.label i) (target := A.label i)
      Subtype.val Subtype.val

variable (A : ControlledSeq X) {P : ∀ i, (A.C i).X → Prop} [∀ i, DecidablePred (P i)]

/-- The controlled inclusion of a subcomplex. -/
@[simps]
def inclSeq (hP : ∀ i, (A.C i).IsSub (P i)) :
    Hom (A.restrict P fun i ↦ (hP i).isLocallyClosed) A where
  f i := inclHom (hP i)
  tendsto := PropTendsto.of_label_eq fun i κ σ h ↦ by
    change A.label i κ = A.label i σ.1
    by_contra hne
    exact h (ite_eq_right (by rintro rfl; exact hne rfl))

/-- The controlled projection onto the quotient by a subcomplex. -/
@[simps]
def projSeq (hP : ∀ i, (A.C i).IsSub (P i)) :
    Hom A (A.restrict (fun i σ ↦ ¬P i σ) fun i ↦ (hP i).isLocallyClosed_compl) where
  f i := projHom (hP i)
  tendsto := PropTendsto.of_label_eq fun i κ σ h ↦ by
    change A.label i κ.1 = A.label i σ
    by_contra hne
    exact h (ite_eq_right (by rintro rfl; exact hne rfl))

omit [∀ i, DecidablePred (P i)] in
theorem _root_.HSFormal.Cubical.BasedComplex.mul_projHom_transpose_apply_full {C : BasedComplex}
    {Q : C.X → Prop} [DecidablePred Q] (hQ : C.IsSub Q) {Z : Type*} (M : Matrix Z C.X ℚ) (z : Z)
    (σ : {σ // ¬Q σ}) : (M * (projHom hQ).fᵀ) z σ = M z σ.1 := by
  simp [projHom, mul_apply]

theorem inclHom_transpose_mul (hP : ∀ i, (A.C i).IsSub (P i)) (i : ℕ) :
    (inclHom (hP i)).fᵀ * (inclHom (hP i)).f = 1 := by
  ext σ τ
  simp only [inclHom, mul_apply, transpose_apply, of_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, one_apply, Subtype.ext_iff]

theorem projHom_mul_transpose (hP : ∀ i, (A.C i).IsSub (P i)) (i : ℕ) :
    (projHom (hP i)).f * (projHom (hP i)).fᵀ = 1 := by
  ext σ τ
  simp [projHom, mul_apply, one_apply, Subtype.ext_iff]

section Asymptotic

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  (π : ∀ i, G i →* H) [MulAction H X] [IsIsometricSMul H X]

variable {A} in
/-- Composition of realized degree-`0` matrix sequences. -/
theorem hom_comp_deg0 {B B' : ControlledSeq X} (u : ∀ i, Matrix (B.C i).X (A.C i).X ℚ)
    (v : ∀ i, Matrix (B'.C i).X (B.C i).X ℚ) (hu hv) {r r'' : ℤ}
    (h : ∀ i, HasDeg (A.C i) (B.C i) 0 (u i)) :
    hom π u hu r r ≫ hom π v hv r r'' = hom π (fun i ↦ v i * u i) (hv.mul hu) r r'' :=
  hom_comp _ _ _ _ fun i κ σ hne hσ ↦ by have := h i κ σ hne; omega

theorem inclSeq_transpose_tendsto (hP : ∀ i, (A.C i).IsSub (P i)) :
    PropTendsto (fun i ↦ (inclHom (hP i)).fᵀ) A.label
      (A.restrict P fun i ↦ (hP i).isLocallyClosed).label :=
  PropTendsto.transpose (A.inclSeq hP).tendsto

theorem projSeq_transpose_tendsto (hP : ∀ i, (A.C i).IsSub (P i)) :
    PropTendsto (fun i ↦ (projHom (hP i)).fᵀ)
      (A.restrict (fun i σ ↦ ¬P i σ) fun i ↦ (hP i).isLocallyClosed_compl).label A.label :=
  PropTendsto.transpose (A.projSeq hP).tendsto

/-- **The realized split sequence** `0 → A_P → A → A/A_P → 0` of a subcomplex. -/
def splitSeq (hP : ∀ i, (A.C i).IsSub (P i)) :
    DegreewiseSplit ((A.inclSeq hP).toComplex π) ((A.projSeq hP).toComplex π) where
  t n := hom (A := A) (B := A.restrict P fun i ↦ (hP i).isLocallyClosed) π
    (fun i ↦ (inclHom (hP i)).fᵀ) (A.inclSeq_transpose_tendsto hP) n n
  s n := hom (A := A.restrict (fun i σ ↦ ¬P i σ) fun i ↦ (hP i).isLocallyClosed_compl) (B := A) π
    (fun i ↦ (projHom (hP i)).fᵀ) (A.projSeq_transpose_tendsto hP) n n
  it n := by
    erw [Hom.toComplex_f, hom_comp_deg0 _ _ _ _ _ fun i ↦ (inclHom (hP i)).deg0]
    exact (hom_congr (funext fun i ↦ A.inclHom_transpose_mul hP i) _ _ _ _).trans hom_one
  sq n := by
    erw [Hom.toComplex_f, hom_comp_deg0 _ _ _ _ _ fun i ↦ (projHom (hP i)).deg0.transpose0]
    exact (hom_congr (funext fun i ↦ A.projHom_mul_transpose hP i) _ _ _ _).trans hom_one
  total n := by
    erw [Hom.toComplex_f, Hom.toComplex_f,
      hom_comp_deg0 _ _ _ _ _ fun i ↦ (inclHom (hP i)).deg0.transpose0,
      hom_comp_deg0 _ _ _ _ _ fun i ↦ (projHom (hP i)).deg0, ← hom_add]
    exact (hom_congr (funext fun i ↦ inclHom_split (hP i)) _ _ _ _).trans hom_one

end Asymptotic

end ControlledSeq

/-! ### Controlled based pairs -/

/-- **A controlled based pair** `(D, Σ)` of dimension `N + 1` with a symmetric top: a controlled
sequence `D` of dimension `≤ N + 1`, subcomplexes `Σ_i = S i` of dimension `≤ N`, and controlled
matrices `T_i` of total degree `N + 1`, `(N+1)`-symmetric, whose defects `d T - T δ` are carried by
`Σ × Σ` (the relative boundary equation of the pair). -/
structure SeqPair (X : Type) [PseudoEMetricSpace X] where
  D : ControlledSeq X
  N : ℕ
  hD : D.DimLE (N + 1)
  S : ∀ i, (D.C i).X → Prop
  [decS : ∀ i, DecidablePred (S i)]
  hS : ∀ i, (D.C i).IsSub (S i)
  hSN : ∀ i σ, S i σ → (D.C i).deg σ ≤ N
  T : ∀ i, Matrix (D.C i).X (D.C i).X ℚ
  T_deg : ∀ i σ τ, T i σ τ ≠ 0 → (D.C i).deg σ + (D.C i).deg τ = N + 1
  T_symm : ∀ i σ τ, ((-1 : ℚ) ^ (N + 1 + 1)) ^ (D.C i).deg σ * T i τ σ = T i σ τ
  T_tendsto : PropTendsto T D.label D.label
  supp : ∀ i σ τ, defect (D.C i) (N + 1) (hD i) (T i) σ τ ≠ 0 → S i σ ∧ S i τ

namespace SeqPair

variable {X : Type} [PseudoEMetricSpace X] (P : SeqPair X)

attribute [instance] SeqPair.decS

open ControlledSeq

/-- The boundary sequence `Σ`. -/
abbrev Bd : ControlledSeq X := P.D.restrict P.S fun i ↦ (P.hS i).isLocallyClosed

/-- The relative sequence `D/Σ`. -/
abbrev Rel : ControlledSeq X :=
  P.D.restrict (fun i σ ↦ ¬P.S i σ) fun i ↦ (P.hS i).isLocallyClosed_compl

theorem hBd : P.Bd.DimLE P.N := fun i σ ↦ P.hSN i σ.1 σ.2

theorem hRel : P.Rel.DimLE (P.N + 1) := fun i σ ↦ P.hD i σ.1

theorem defect_tendsto :
    PropTendsto (fun i ↦ defect (P.D.C i) (P.N + 1) (P.hD i) (P.T i))
      P.D.label P.D.label :=
  PropTendsto.sub (PropTendsto.mul P.D.tendsto_d P.T_tendsto)
    (PropTendsto.mul P.T_tendsto (P.D.dual (P.N + 1) P.hD).tendsto_d)

/-- The boundary structure `φ : Σ^{N-*} → Σ` (the defect of the top on `Σ`). -/
def bdHom : ControlledSeq.Hom (P.Bd.dual P.N P.hBd) P.Bd where
  f i := bdHomB (P.hD i) (P.T_deg i) (P.hS i) (P.supp i) (P.hBd i)
  tendsto := tendsto_zero_of_le P.defect_tendsto fun i ↦
    prop_submatrix_le (u := defect (P.D.C i) (P.N + 1) (P.hD i) (P.T i))
      (source := P.D.label i) (target := P.D.label i) Subtype.val Subtype.val

theorem bdHom_f (i : ℕ) : (P.bdHom.f i).f =
    (defect (P.D.C i) (P.N + 1) (P.hD i) (P.T i)).submatrix Subtype.val Subtype.val := rfl

theorem bdHom_symm : ControlledSeq.IsSymm P.hBd P.bdHom := fun i ↦
  isSymm_bdHomB (P.hD i) (P.T_deg i) (P.T_symm i) (P.hS i) (P.supp i) (P.hBd i)

/-- The relative cap `C^{N+1-*}(D, Σ) → C(D)`. -/
def relHom : ControlledSeq.Hom (P.Rel.dual (P.N + 1) P.hRel) P.D where
  f i := relHomB (P.hD i) (P.T_deg i) (P.hS i) (P.supp i)
  tendsto := tendsto_zero_of_le P.T_tendsto fun i ↦
    prop_submatrix_le (u := P.T i) (source := P.D.label i) (target := P.D.label i)
      Subtype.val id

theorem relHom_f (i : ℕ) : (P.relHom.f i).f = (P.T i).submatrix id Subtype.val := rfl

/-- The inclusion `j : Σ → D`. -/
abbrev jHom : ControlledSeq.Hom P.Bd P.D := P.D.inclSeq P.hS

/-- The projection `q : D → D/Σ`. -/
abbrev qHom : ControlledSeq.Hom P.D P.Rel := P.D.projSeq P.hS

/-- `j φ j^*` is the defect of the top (it is carried by `Σ × Σ`). -/
theorem incl_bd_incl (i : ℕ) :
    (inclHom (P.hS i)).f * ((defect (P.D.C i) (P.N + 1) (P.hD i) (P.T i)).submatrix
      Subtype.val Subtype.val * (inclHom (P.hS i)).fᵀ) =
      defect (P.D.C i) (P.N + 1) (P.hD i) (P.T i) := by
  ext κ σ
  rw [inclHom_mul_apply]
  split_ifs with hκ
  · rw [mul_inclHom_transpose_apply]
    split_ifs with hσ
    · rfl
    · exact (by_contra fun h ↦ hσ (P.supp i _ _ h).2 :
        defect (P.D.C i) (P.N + 1) (P.hD i) (P.T i) κ σ = 0).symm
  · exact (by_contra fun h ↦ hκ (P.supp i _ _ h).1 :
      defect (P.D.C i) (P.N + 1) (P.hD i) (P.T i) κ σ = 0).symm

section Asymptotic

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  (π : ∀ i, G i →* H) [MulAction H X] [IsIsometricSMul H X]

/-- The realized top `T : D^{N-*} → D` (degree `1`). -/
abbrev topHom (r r' : ℤ) : P.D.obj π ((P.N : ℤ) - r) ⟶ P.D.obj π r' :=
  hom (A := P.D) (B := P.D) π P.T P.T_tendsto (P.N - r) r'

theorem topHom_eq_zero {r r' : ℤ} (h : r + 1 ≠ r') : P.topHom π r r' = 0 :=
  hom_eq_zero _ _ fun i κ σ hσ hκ ↦ by_contra fun hne ↦ h (by have := P.T_deg i κ σ hne; omega)

theorem toComplex_d (A : ControlledSeq X) (r r' : ℤ) :
    (A.toComplex π).d r r' = hom (A := A) (B := A) π (fun i ↦ (A.C i).d) A.tendsto_d r r' := rfl

/-- **The relative boundary** `j φ j^* = d T + T δ`, realized: a homotopy from the realized
`j φ j^*` to `0` with components the top `T`. -/
def δφ : Homotopy (dualHom (asymptoticObjInvolution π X) P.N ((P.jHom).toComplex π) ≫
    dualityMap π P.hBd P.bdHom ≫ (P.jHom).toComplex π) 0 where
  hom r r' := P.topHom π r r'
  zero r r' h := P.topHom_eq_zero π (by simpa using h)
  comm r := by
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel r (r - 1) by simp),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (r + 1) r by simp)]
    simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f, add_zero, dualHom_f,
      dualityMap_f, Hom.toComplex_f, dualComplex_d, asymptoticObjInvolution_star, transpose_hom,
      toComplex_d, Linear.units_smul_comp]
    have hN : ∀ i (σ : (P.Bd.C i).X), (P.Bd.C i).deg σ ≤ P.N := fun i σ ↦ P.hBd i σ
    erw [hom_comp (A := P.Bd) (B := P.Bd) (B' := P.D) _ _ _ _
        fun i κ σ h hσ ↦ by
          have h₁ := (P.bdHom.f i).deg0 κ σ h
          have h₂ := hN i σ
          change ((P.Bd.C i).deg κ : ℤ) = ((P.N - (P.Bd.C i).deg σ : ℕ) : ℤ) + 0 at h₁
          change ((P.Bd.C i).deg σ : ℤ) = _ at hσ
          omega,
      hom_comp (A := P.D) (B := P.Bd) (B' := P.D) _ _ _ _ fun i κ σ h hσ ↦ by
          have := (P.jHom.f i).deg0.transpose0 κ σ h
          omega,
      hom_comp (A := P.D) (B := P.D) (B' := P.D) _ _ _ _ fun i κ σ h hσ ↦ by
          rw [transpose_apply] at h
          have := (P.D.C i).d_deg _ _ h
          omega,
      hom_comp (A := P.D) (B := P.D) (B' := P.D) _ _ _ _ fun i κ σ h hσ ↦ by
          have := P.T_deg i κ σ h
          omega,
      units_smul_hom, ← hom_add]
    refine hom_eq_of_block _ _ fun i κ σ hσ hκ ↦ ?_
    erw [Matrix.mul_assoc, bdHom_f, show (P.jHom.f i).f = (inclHom (P.hS i)).f from rfl,
      incl_bd_incl, defect, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      MatRealization.negOnePow_cast_eq (N := P.N) (k := (P.D.C i).deg σ) (by omega)]
    simp only [mul_apply, transpose_apply, smul_eq_mul, Finset.mul_sum]
    have e : ∀ x, ((-1 : ℚ) ^ (P.N + 1) • ((P.D.C i).dᵀ * (P.D.C i).sgn)) x σ =
        (-1) ^ (P.N + 1) * ((-1) ^ (P.D.C i).deg σ * (P.D.C i).d σ x) :=
      fun x ↦ dual_d_apply (P.hD i) x σ
    simp only [e]
    have hb : ∑ x, P.T i κ x * ((-1) ^ (P.N + 1) * ((-1) ^ (P.D.C i).deg σ * (P.D.C i).d σ x)) =
        -∑ x, (-1) ^ P.N * (-1) ^ (P.D.C i).deg σ * (P.T i κ x * (P.D.C i).d σ x) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun x _ ↦ by ring
    rw [hb]
    ring

theorem δφ_hom (r r' : ℤ) : (P.δφ π).hom r r' = P.topHom π r r' := rfl

/-- The sign of the transposed top. -/
theorem sign_transpose_top (a N : ℕ) :
    ((((a : ℤ).negOnePow * ((a : ℤ) * ((N : ℤ) - a)).negOnePow : ℤˣ) : ℤ) : ℚ) =
      ((-1 : ℚ) ^ (N + 1 + 1)) ^ a := by
  rw [← Int.negOnePow_add, ← pow_mul, ← Int.cast_negOnePow_natCast ℚ ((N + 1 + 1) * a)]
  congr 2
  rw [Int.negOnePow_eq_iff]
  have : (a : ℤ) + a * (N - a) - (((N + 1 + 1) * a : ℕ) : ℤ) = -(a * (a + 1)) := by
    push_cast; ring
  rw [this, even_neg]
  exact Int.even_mul_succ_self a

/-- **The relative boundary is symmetric** (`T δφ = δφ`): the top is `(N+1)`-symmetric. -/
theorem δφ_symm : IsSymmHomotopy (asymptoticObjInvolution π X) P.N (P.δφ π) := by
  rw [IsSymmHomotopy, transposeHomotopy_hom]
  funext r r'
  by_cases hr : r + 1 = r'
  swap
  · simp only [transposeHomFamily, δφ_hom]
    rw [P.topHom_eq_zero π (show (P.N : ℤ) - r' + 1 ≠ P.N - r by omega), P.topHom_eq_zero π hr,
      StrictInvolution.star_zero]
    simp
  subst hr
  simp only [transposeHomFamily, δφ_hom, bidual_hom_f, asymptoticObjInvolution_star,
    transpose_hom, eqToHom_toComplex_X P.D (sub_sub_cancel (P.N : ℤ) (r + 1)),
    Linear.comp_units_smul]
  rw [hom_comp (A := P.D) (B := P.D) (B' := P.D) _ _ _ _ fun i κ σ h hσ ↦ by
      rw [transpose_apply] at h
      have := P.T_deg i σ κ h
      omega, units_smul_hom, units_smul_hom]
  refine hom_eq_of_block _ _ fun i κ σ hσ hκ ↦ ?_
  rw [Matrix.smul_apply, Matrix.smul_apply, Matrix.one_mul, transpose_apply, ← P.T_symm i κ σ, smul_eq_mul,
    smul_eq_mul, ← mul_assoc, ← Int.cast_mul, ← Units.val_mul]
  by_cases h0 : P.T i σ κ = 0
  · rw [h0, mul_zero, mul_zero]
  have hdeg := P.T_deg i σ κ h0
  obtain rfl : r = (P.D.C i).deg κ - 1 := by omega
  rw [sub_add_cancel, sign_transpose_top]

/-- The realized split sequence `0 → Σ → D → D/Σ → 0`. -/
abbrev split : DegreewiseSplit ((P.jHom).toComplex π) ((P.qHom).toComplex π) :=
  P.D.splitSeq π P.hS

theorem relHom_f_eq (i : ℕ) :
    (P.relHom.f i).f = P.T i * ((1 : Matrix (P.D.C i).X (P.D.C i).X ℚ) *
      (projHom (P.hS i)).fᵀ) :=
  Matrix.ext fun κ σ ↦ by erw [relHom_f, Matrix.one_mul, mul_projHom_transpose_apply_full]; rfl

/-- **The relative cap is `Ψ q^*`**: the relative duality map of the realized pair, precomposed
with the dual of `Cone(j) → D/Σ`, is the realized relative cap. -/
theorem dualHom_coneToCoker_comp_relDuality :
    dualHom (asymptoticObjInvolution π X) ((P.N : ℤ) + 1) (coneToCoker (P.split π)) ≫
      relDuality (P.δφ π) = dualityMap π P.hRel P.relHom := by
  ext r
  rw [HomologicalComplex.comp_f, dualHom_f, coneToCoker_f, relDuality_f,
    StrictInvolution.star_comp, Category.assoc, Preadditive.comp_add, Preadditive.comp_add,
    cone.star_sndX_inrX_assoc, Linear.comp_units_smul, Linear.comp_units_smul,
    cone.star_sndX_inlX_assoc, zero_comp, comp_zero, smul_zero, add_zero]
  simp only [relTop, δφ_hom, HomologicalComplex.XIsoOfEq, eqToIso.hom,
    eqToHom_toComplex_X P.D (show (P.N : ℤ) + 1 - r = P.N - (r - 1) by ring),
    Hom.toComplex_f, asymptoticObjInvolution_star, transpose_hom, dualityMap_f]
  rw [hom_comp (A := P.D) (B := P.D) (B' := P.D) _ _ _ _ fun i κ σ h hσ ↦ by
      obtain rfl := eq_of_one_ne_zero h; omega,
    hom_comp (A := P.Rel) (B := P.D) (B' := P.D) _ _ _ _ fun i κ σ h hσ ↦ by
      rw [(projHom (P.hS i)).deg0.transpose0 κ σ h, add_zero]; exact hσ]
  exact hom_congr (funext fun i ↦ by
    rw [Matrix.mul_assoc]; exact (P.relHom_f_eq i).symm) _ _ _ _

theorem supportedIn_D : SupportedIn (𝟙 (P.D.toComplex π)) 0 ((P.N : ℤ) + 1) := by
  have := ControlledSeq.SymDuality.supportedIn_id π P.hD
  rwa [Nat.cast_succ] at this

/-- **The realized based pair is a Poincaré pair** once its relative cap is an equivalence
(R1 for the boundary, `isKarEquiv_relDuality_of_split` for `Ψ`). -/
def toSymPair (hrel : IsKarEquiv (𝟙 _) (𝟙 _) (dualityMap π P.hRel P.relHom)) :
    SymPair (asymptoticObjInvolution π X) P.N :=
  SymPair.ofSplit (ControlledSeq.SymDuality.supportedIn_id π P.hBd) (P.supportedIn_D π)
    (dualityMap π P.hBd P.bdHom) (isStrictSymm_dualityMap P.bdHom_symm) (P.split π) (P.δφ π)
    (P.δφ_symm π) (isKarEquiv_relDuality_of_split (P.split π) (P.δφ π) (by
      rw [P.dualHom_coneToCoker_comp_relDuality π]; exact hrel))

variable {π} (hrel : IsKarEquiv (𝟙 _) (𝟙 _) (dualityMap π P.hRel P.relHom))

@[simp] theorem toSymPair_bd_C : (P.toSymPair π hrel).bd.C = P.Bd.toComplex π := rfl
@[simp] theorem toSymPair_bd_p : (P.toSymPair π hrel).bd.p = 𝟙 _ := rfl
@[simp] theorem toSymPair_bd_φ : (P.toSymPair π hrel).bd.φ = dualityMap π P.hBd P.bdHom := rfl
@[simp] theorem toSymPair_D : (P.toSymPair π hrel).D = P.D.toComplex π := rfl
@[simp] theorem toSymPair_pD : (P.toSymPair π hrel).pD = 𝟙 _ := rfl
@[simp] theorem toSymPair_j : (P.toSymPair π hrel).j = P.jHom.toComplex π := rfl
theorem toSymPair_δφ : (P.toSymPair π hrel).δφ = P.δφ π := rfl

end Asymptotic

end SeqPair

end BasedComplex

end HSFormal.Cubical
