import HSFormal.Cubical.DualBridge
import HSFormal.Cubical.GraphBridge
import HSFormal.Cubical.GridSeam
import HSFormal.LTheory.KaroubiFiltration

/-!
# Duals of controlled sequences (cubical module C2 over `𝒜_G(X)`)

The `N`-dual of a whole `ControlledSeq` (`ControlledSeq.dual` of `GridSeam`): every complex
`C i` is dualized (`BasedComplex.dual`, `δ = (-1)^N dᵀ sgn`) with the same cells and labels;
transposition does not change propagation (`prop_transpose`).  Controlled chain maps, homotopies and homotopy
equivalences dualize termwise, and Ranicki's transposition `Tφ = ε φᵀ` of a controlled
`φ : A^{N-*} → B` is controlled.

Over the prequotient `AsymptoticObject π X` with the transpose involution
(`asymptoticObjInvolution`), `dualIso` identifies `Compression.dualComplex` of `A.toComplex π`
with the complex of the dual sequence (the analogue of `MatRealization.dualIso`); it is
compatible with dual chain maps (`dualHom_toComplex`), dual homotopies
(`dualHomotopy_toHomotopy_hom`) and transposition (`transposeHom_dualityMap`).

A `ControlledSeq.SymDuality` (a controlled homotopy equivalence `A^{N-*} ≃ A` with strictly
symmetric terms, e.g. `SymDuality.ofSeq` from uniformly controlled `BasedComplex.SymDuality`s)
gives the controlled Poincaré complex of the chain model: an M1 `SymPoincare` over the
prequotient (`symPoincareObj`), in the asymptotic `InvCat` `𝒜_G(X)` (`symPoincare`), and in the
exterior quotients `ℬ_Z(X)` (`extSymPoincare`).

In `𝒜_G(X)` itself the identification is `dualIsoQuot`.  `SymDuality.ofFlip` symmetrizes a
controlled duality along a controlled flip homotopy (l. 271).

Graph types: the dual of a graph-type-`τ` family of chain maps (homotopies) is a family of type
`τ⁻¹` (`GraphHom.dual`, `GraphHtpy.dual`), compatible with `dualIso`
(`GraphHom.dualHom_toComplex`, `GraphHtpy.dualHomotopy_toHomotopy_hom`).

Compression (§9): through `dualIso`, Compression's dual near part `(π^*, σ^*)` of `nearPart` is
the inclusion/projection of the retained cells (`dualNearPart_nearPart_i/_r`, `far_dualNearPart`),
and the compressions `φ̂ = πφπ^*`, `b̂ = σ^*bσ` entering the inverse defects of Proposition 9.2 are
realized by the restricted matrices (`compress_dualityMap`, `compress_toDualMap`); `hatPhi` is
the realized based duality `π φ π^*` (`compressDuality`, `hatPhi_dualityMap`).
-/

noncomputable section

namespace HSFormal.Cubical

open Filter Matrix CategoryTheory CategoryTheory.Limits HSFormal.Compression HSFormal.LTheory
open scoped ENNReal Topology

universe u

/-! ### The transpose involution on the prequotient -/

section Inv

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  (π : ∀ i, G i →* H) (X : Type u) [MulAction H X] [PseudoEMetricSpace X]

/-- Transpose duality on the prequotient `AsymptoticObject π X`. -/
@[simps]
def asymptoticObjInvolution : StrictInvolution (AsymptoticObject π X) where
  star := AsymptoticObject.transpose
  star_comp := AsymptoticObject.transpose_comp
  star_id _ := AsymptoticObject.transpose_id
  star_add := AsymptoticObject.transpose_add
  star_star := AsymptoticObject.transpose_transpose

end Inv

section InvQuot

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  (π : ∀ i, G i →* H) (X : Type) [MulAction H X] [PseudoEMetricSpace X]

/-- The quotient functor `AsymptoticObject π X ⥤ 𝒜_G(X)` preserves duality. -/
def asymptoticQuotInv :
    InvFunctor (asymptoticObjInvolution π X) (asymptoticInvCat π X).inv where
  F := AsymptoticCategory.functor
  additive := AsymptoticCategory.functor_additive
  map_star _ := rfl

theorem asymptoticQuotInv_F : (asymptoticQuotInv π X).F = AsymptoticCategory.functor := rfl

end InvQuot

namespace BasedComplex

/-! ### Controlled transposes -/

section PropTendsto

variable {X : Type*} [PseudoEMetricSpace X] {C D : ℕ → BasedComplex} {a : ∀ i, (C i).X → X}
  {b : ∀ i, (D i).X → X}

theorem PropTendsto.transpose {u : ∀ i, Matrix (D i).X (C i).X ℚ} (hu : PropTendsto u a b) :
    PropTendsto (fun i ↦ (u i)ᵀ) b a := by
  simpa [PropTendsto, prop_transpose] using hu

theorem PropTendsto.diagonal (v : ∀ i, (C i).X → ℚ) :
    PropTendsto (fun i ↦ Matrix.diagonal (v i)) a a :=
  tendsto_zero_of_forall_eq_zero fun _ ↦ prop_diagonal _ _

theorem PropTendsto.sgn : PropTendsto (fun i ↦ (C i).sgn) a a := PropTendsto.diagonal _

theorem PropTendsto.eps (N : ℕ) : PropTendsto (fun i ↦ (C i).eps N) a a := PropTendsto.diagonal _

end PropTendsto

namespace ControlledSeq

variable {X : Type u} [PseudoEMetricSpace X] {A B B' : ControlledSeq X} {N : ℕ}

theorem Hom.ext_f {F F' : Hom A B} (h : ∀ i, F.f i = F'.f i) : F = F' := by
  cases F; cases F'; congr; exact funext h

/-- Transport a controlled homotopy along equalities of its endpoints. -/
def Htpy.congr {F G F' G' : Hom A B} (K : Htpy F G) (hF : F = F') (hG : G = G') : Htpy F' G' :=
  hF ▸ hG ▸ K

/-! ### The dual sequence -/

/-- All complexes of the sequence have dimension `≤ N`. -/
abbrev DimLE (A : ControlledSeq X) (N : ℕ) : Prop := ∀ i, (A.C i).DimLE N

/-! The `N`-dual sequence `A.dual N hN` (the dual complexes `C_i^{N-*}` with the same cells and
labels) is `ControlledSeq.dual` of `HSFormal.Cubical.GridSeam`; `hN : A.DimLE N` is its
hypothesis `∀ i, (A.C i).DimLE N`. -/

@[simp] theorem dual_C (hN : A.DimLE N) (i : ℕ) : (A.dual N hN).C i = (A.C i).dual N (hN i) := rfl

@[simp] theorem dual_label (hN : A.DimLE N) : (A.dual N hN).label = A.label := rfl

theorem dimLE_dual (hN : A.DimLE N) : (A.dual N hN).DimLE N :=
  fun i ↦ BasedComplex.dimLE_dual (hN i)

/-- The dual of a controlled chain map, by transposition. -/
@[simps]
def Hom.dual (F : Hom A B) (N : ℕ) (hA : A.DimLE N) (hB : B.DimLE N) :
    Hom (B.dual N hB) (A.dual N hA) :=
  ⟨fun i ↦ (F.f i).dual N (hA i) (hB i), PropTendsto.transpose F.tendsto⟩

theorem Hom.dual_comp (G : Hom B B') (F : Hom A B) (hA : A.DimLE N) (hB : B.DimLE N)
    (hB' : B'.DimLE N) : (G.comp F).dual N hA hB' = (F.dual N hA hB).comp (G.dual N hB hB') :=
  Hom.ext_f fun _ ↦ BasedComplex.Hom.dual_comp _ _ _ _ _

theorem Hom.dual_id (hA : A.DimLE N) : (Hom.id A).dual N hA hA = Hom.id (A.dual N hA) :=
  Hom.ext_f fun _ ↦ BasedComplex.Hom.dual_id _

/-- The dual of a controlled homotopy, `K = -(-1)^N Hᵀ sgn` termwise. -/
@[simps]
def Htpy.dual {F G : Hom A B} (K : Htpy F G) (hA : A.DimLE N) (hB : B.DimLE N) :
    Htpy (F.dual N hA hB) (G.dual N hA hB) :=
  ⟨fun i ↦ (K.h i).dual (hA i) (hB i), (K.tendsto.transpose.mul PropTendsto.sgn).smul _⟩

/-- The dual of a controlled homotopy equivalence. -/
def HtpyEquiv.dual (e : HtpyEquiv A B) (hA : A.DimLE N) (hB : B.DimLE N) :
    HtpyEquiv (B.dual N hB) (A.dual N hA) where
  hom := e.hom.dual N hA hB
  inv := e.inv.dual N hB hA
  homInv := (e.invHom.dual hB hB).congr (Hom.dual_comp _ _ _ _ _) (Hom.dual_id _)
  invHom := (e.homInv.dual hA hA).congr (Hom.dual_comp _ _ _ _ _) (Hom.dual_id _)

/-- Ranicki's transposition `Tφ = ε φᵀ : B^{N-*} → A` of a controlled `φ : A^{N-*} → B`. -/
@[simps]
def transpose (hA : A.DimLE N) (hB : B.DimLE N) (φ : Hom (A.dual N hA) B) :
    Hom (B.dual N hB) A :=
  ⟨fun i ↦ BasedComplex.transpose (hA i) (hB i) (φ.f i),
    (PropTendsto.eps N).mul (PropTendsto.transpose φ.tendsto)⟩

@[simp]
theorem transpose_transpose (hA : A.DimLE N) (hB : B.DimLE N) (φ : Hom (A.dual N hA) B) :
    transpose hB hA (transpose hA hB φ) = φ :=
  Hom.ext_f fun _ ↦ BasedComplex.transpose_transpose _ _ _

/-- Termwise strict symmetry `Tφ = φ`. -/
def IsSymm (hN : A.DimLE N) (φ : Hom (A.dual N hN) A) : Prop :=
  ∀ i, BasedComplex.IsSymm (hN i) (φ.f i)

theorem isSymm_iff_transpose_eq (hN : A.DimLE N) (φ : Hom (A.dual N hN) A) :
    IsSymm hN φ ↔ transpose hN hN φ = φ :=
  ⟨fun h ↦ Hom.ext_f h, fun h i ↦ congrArg (fun F : Hom _ _ ↦ F.f i) h⟩

/-! ### `dualComplex` of the realization is the realization of the dual -/

section Asymptotic

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  {π : ∀ i, G i →* H} [MulAction H X] [IsIsometricSMul H X]

theorem hom_eq_of_block {u v : ∀ i, Matrix (B.C i).X (A.C i).X ℚ} (hu hv) {r r' : ℤ}
    (h : ∀ i κ σ, ((A.C i).deg σ : ℤ) = r → ((B.C i).deg κ : ℤ) = r' → u i κ σ = v i κ σ) :
    hom π u hu r r' = hom π v hv r r' :=
  AsymptoticObject.hom_ext fun i ↦ by
    rw [hom_val, hom_val]
    congr 1
    ext k' k
    exact h i _ _ ((cellEquiv (A.C i) r).symm k).2 ((cellEquiv (B.C i) r').symm k').2

theorem transpose_hom (u : ∀ i, Matrix (B.C i).X (A.C i).X ℚ) (hu) (r r' : ℤ) :
    AsymptoticObject.transpose (hom π u hu r r') =
      hom π (fun i ↦ (u i)ᵀ) (PropTendsto.transpose hu) r' r :=
  AsymptoticObject.hom_ext fun i ↦ by
    rw [AsymptoticObject.transpose_val, hom_val, hom_val, sheet_transpose, inv_one]
    rfl

theorem smul_hom (c : ℚ) (u : ∀ i, Matrix (B.C i).X (A.C i).X ℚ) (hu) (r r' : ℤ) :
    c • hom π u hu r r' = hom π (fun i ↦ c • u i) (hu.smul c) r r' :=
  AsymptoticObject.hom_ext fun i ↦ by
    rw [AsymptoticObject.smul_val, hom_val, hom_val, ← sheet_smul]
    rfl

theorem units_smul_hom (c : ℤˣ) (u : ∀ i, Matrix (B.C i).X (A.C i).X ℚ) (hu) (r r' : ℤ) :
    c • hom π u hu r r' = hom π (fun i ↦ (((c : ℤ) : ℚ)) • u i) (hu.smul _) r r' := by
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℚ, smul_hom]

theorem eqToHom_toComplex_X (A : ControlledSeq X) {a b : ℤ} (h : a = b) :
    eqToHom (congrArg (A.toComplex π).X h) =
      hom (A := A) (B := A) π (fun _ ↦ 1) PropTendsto.one a b := by
  subst h
  rw [eqToHom_refl, hom_one]

theorem Hom.toComplex_congr {F F' : Hom A B} (h : ∀ i, (F.f i).f = (F'.f i).f) :
    F.toComplex π = F'.toComplex π := by
  ext r
  exact hom_congr (funext h) F.tendsto F'.tendsto r r

theorem eq_of_one_ne_zero {α : Type*} [DecidableEq α] {κ σ : α}
    (h : (1 : Matrix α α ℚ) κ σ ≠ 0) : κ = σ := by
  by_contra h'; exact h (one_apply_ne h')

/-- The cells of `A^{N-*}` in degree `r` are the `(N - r)`-cells of `A`. -/
theorem deg_dual_iff (hN : A.DimLE N) {i : ℕ} (σ : (A.C i).X) {r : ℤ} :
    ((A.C i).deg σ : ℤ) = N - r ↔ (((A.dual N hN).C i).deg σ : ℤ) = r := by
  have := hN i σ
  change _ ↔ ((N - (A.C i).deg σ : ℕ) : ℤ) = r
  omega

variable (π) in
/-- **`dualComplex` of the realization is the realization of the dual sequence**: the identity
on cells, `A.obj (N - r) ≅ (A.dual N).obj r`; the signs `δ_r = (-1)^r d^*` agree. -/
def dualIso (A : ControlledSeq X) (N : ℕ) (hN : A.DimLE N) :
    dualComplex (asymptoticObjInvolution π X) N (A.toComplex π) ≅ (A.dual N hN).toComplex π :=
  HomologicalComplex.Hom.isoOfComponents
    (fun r ↦
      { hom := hom (A := A) (B := A.dual N hN) π (fun i ↦ (1 : Matrix (A.C i).X (A.C i).X ℚ))
          PropTendsto.one (N - r) r
        inv := hom (A := A.dual N hN) (B := A) π (fun i ↦ (1 : Matrix (A.C i).X (A.C i).X ℚ))
          PropTendsto.one r (N - r)
        hom_inv_id := by
          erw [hom_comp _ _ _ _ fun i κ σ h hσ ↦ by
            obtain rfl := eq_of_one_ne_zero h; exact (deg_dual_iff hN κ).mp hσ]
          exact (hom_congr (funext fun _ ↦ Matrix.one_mul _) _ _ _ _).trans hom_one
        inv_hom_id := by
          erw [hom_comp _ _ _ _ fun i κ σ h hσ ↦ by
            obtain rfl := eq_of_one_ne_zero h; exact (deg_dual_iff hN κ).mpr hσ]
          exact (hom_congr (funext fun _ ↦ Matrix.one_mul _) _ _ _ _).trans hom_one })
    (fun r r' h ↦ by
      change r' + 1 = r at h
      change hom (A := A) (B := A.dual N hN) π (fun i ↦ (1 : Matrix (A.C i).X (A.C i).X ℚ))
          PropTendsto.one (N - r) r ≫ hom π _ (A.dual N hN).tendsto_d r r' =
        (r.negOnePow • AsymptoticObject.transpose (hom π _ A.tendsto_d (N - r') (N - r))) ≫
          hom (A := A) (B := A.dual N hN) π (fun i ↦ (1 : Matrix (A.C i).X (A.C i).X ℚ))
            PropTendsto.one (N - r') r'
      erw [transpose_hom, units_smul_hom, hom_comp _ _ _ _ fun i κ σ h hσ ↦ by
          obtain rfl := eq_of_one_ne_zero h; exact (deg_dual_iff hN κ).mp hσ,
        hom_comp _ _ _ _ fun i κ σ h hσ ↦ ?_]
      · refine hom_eq_of_block _ _ fun i κ σ hσ hκ ↦ ?_
        have hle := hN i σ
        rw [Matrix.mul_one, Matrix.one_mul]
        change ((A.C i).dual N (hN i)).d κ σ = _
        rw [dual_d_apply, Matrix.smul_apply, transpose_apply,
          MatRealization.negOnePow_cast_eq (k := (A.C i).deg σ) (by omega), smul_eq_mul,
          mul_assoc]
      · rw [Matrix.smul_apply, transpose_apply] at h
        have := (A.C i).d_deg σ κ (right_ne_zero_of_mul h)
        omega)

theorem dualIso_hom_f (A : ControlledSeq X) (N : ℕ) (hN : A.DimLE N) (r : ℤ) :
    (dualIso π A N hN).hom.f r =
      hom (A := A) (B := A.dual N hN) π (fun i ↦ (1 : Matrix (A.C i).X (A.C i).X ℚ))
        PropTendsto.one (N - r) r := rfl

theorem dualIso_inv_f (A : ControlledSeq X) (N : ℕ) (hN : A.DimLE N) (r : ℤ) :
    (dualIso π A N hN).inv.f r =
      hom (A := A.dual N hN) (B := A) π (fun i ↦ (1 : Matrix (A.C i).X (A.C i).X ℚ))
        PropTendsto.one r (N - r) := rfl

theorem Htpy.toHomotopy_hom {F G : Hom A B} (K : Htpy F G) (r r' : ℤ) :
    (K.toHomotopy π).hom r r' = hom π (fun i ↦ (K.h i).h) K.tendsto r r' := rfl

set_option maxHeartbeats 1000000 in
/-- `dualIso` is compatible with dual chain maps: `(F)^{N-*} = F^{N-*}` under the
identifications. -/
theorem dualHom_toComplex (F : Hom A B) (N : ℕ) (hA : A.DimLE N) (hB : B.DimLE N) :
    dualHom (asymptoticObjInvolution π X) N (F.toComplex π) =
      (dualIso π B N hB).hom ≫ (F.dual N hA hB).toComplex π ≫ (dualIso π A N hA).inv := by
  ext r
  simp only [HomologicalComplex.comp_f, dualHom_f, asymptoticObjInvolution_star, Hom.toComplex_f,
    dualIso_hom_f, dualIso_inv_f, transpose_hom]
  erw [hom_comp _ _ _ _ fun i κ σ h hσ ↦ by
      exact (((F.f i).dual N (hA i) (hB i)).deg0 κ σ h).trans ((add_zero _).trans hσ),
    hom_comp _ _ _ _ fun i κ σ h hσ ↦ by
      obtain rfl := eq_of_one_ne_zero h; exact (deg_dual_iff hB κ).mp hσ]
  exact hom_congr (funext fun i ↦ by simp) _ _ _ _

set_option maxHeartbeats 1000000 in
/-- `dualIso` is compatible with dual homotopies: Compression's `K_r = (-1)^{r+1} T^*` is the
realization of the based dual homotopy `-(-1)^N Tᵀ sgn`. -/
theorem dualHomotopy_toHomotopy_hom {F G : Hom A B} (K : Htpy F G) (hA : A.DimLE N)
    (hB : B.DimLE N) (r r' : ℤ) :
    (dualHomotopy (asymptoticObjInvolution π X) N (K.toHomotopy π)).hom r r' =
      (dualIso π B N hB).hom.f r ≫ ((K.dual hA hB).toHomotopy π).hom r r' ≫
        (dualIso π A N hA).inv.f r' := by
  by_cases hr : r + 1 = r'
  swap
  · have h₁ := (dualHomotopy (asymptoticObjInvolution π X) N (K.toHomotopy π)).zero r r'
      (by simpa using hr)
    have h₂ := ((K.dual hA hB).toHomotopy π).zero r r' (by simpa using hr)
    rw [h₁, h₂, zero_comp, comp_zero]
  subst hr
  simp only [dualHomotopy_hom, Htpy.toHomotopy_hom, asymptoticObjInvolution_star, transpose_hom,
    dualIso_hom_f, dualIso_inv_f]
  erw [units_smul_hom, hom_comp _ _ _ _ fun i κ σ h hσ ↦ by
      exact (((K.h i).dual (hA i) (hB i)).deg1 κ σ h).trans (congrArg (· + 1) hσ),
    hom_comp _ _ _ _ fun i κ σ h hσ ↦ by
      obtain rfl := eq_of_one_ne_zero h; exact (deg_dual_iff hB κ).mp hσ]
  refine hom_eq_of_block _ _ fun i κ σ hσ hκ ↦ ?_
  simp only [Matrix.mul_one, Matrix.one_mul, Htpy.dual_h, BasedComplex.Htpy.dual, Matrix.smul_apply,
    transpose_apply, sgn, mul_diagonal, smul_eq_mul]
  rw [Int.negOnePow_succ, Units.val_neg, Int.cast_neg,
    MatRealization.negOnePow_cast_eq (k := (B.C i).deg σ) hσ]
  ring

variable (π) in
/-- The realized duality map `φ : (A)^{N-*} → B` of a controlled `φ : A^{N-*} → B`. -/
def dualityMap (hA : A.DimLE N) (φ : Hom (A.dual N hA) B) :
    dualComplex (asymptoticObjInvolution π X) N (A.toComplex π) ⟶ B.toComplex π :=
  (dualIso π A N hA).hom ≫ φ.toComplex π

theorem dualityMap_f (hA : A.DimLE N) (φ : Hom (A.dual N hA) B) (r : ℤ) :
    (dualityMap π hA φ).f r = hom (A := A) (B := B) π (fun i ↦ (φ.f i).f) φ.tendsto (N - r) r := by
  erw [dualityMap, HomologicalComplex.comp_f, dualIso_hom_f, Hom.toComplex_f,
    hom_comp _ _ _ _ fun i κ σ h hσ ↦ by
      obtain rfl := eq_of_one_ne_zero h; exact (deg_dual_iff hA κ).mp hσ]
  exact hom_congr (funext fun _ ↦ Matrix.mul_one _) _ _ _ _

/-- **The chain-level transpose**: Ranicki's `Tφ = φ^{N-*} ε` of the realized duality map is the
realization of the based transpose `ε φᵀ`. -/
theorem transposeHom_dualityMap (hA : A.DimLE N) (hB : B.DimLE N) (φ : Hom (A.dual N hA) B) :
    transposeHom (asymptoticObjInvolution π X) N (dualityMap π hA φ) =
      dualityMap π hB (transpose hA hB φ) := by
  ext r
  erw [transposeHom_f, dualityMap_f, dualityMap_f, asymptoticObjInvolution_star, transpose_hom,
    eqToHom_toComplex_X A (sub_sub_cancel (N : ℤ) r), hom_comp _ _ _ _ fun i κ σ h hσ ↦ by
      have h₁ := (φ.f i).deg0 σ κ h
      have h₂ := hA i κ
      change (((A.C i).deg κ : ℕ) : ℤ) = N - (N - r)
      change ((B.C i).deg σ : ℤ) = ((N - (A.C i).deg κ : ℕ) : ℤ) + 0 at h₁
      omega, units_smul_hom]
  refine hom_eq_of_block _ _ fun i κ σ hσ hκ ↦ ?_
  have hle := hA i κ
  have hc : (((r * (N - r)).negOnePow : ℤˣ) : ℤ) =
      (((((A.C i).deg κ * (N - (A.C i).deg κ) : ℕ) : ℤ).negOnePow : ℤˣ) : ℤ) := by
    congr 2; push_cast [Nat.cast_sub hle]; rw [hκ]
  simp only [Matrix.smul_apply, Matrix.one_mul, transpose_apply, smul_eq_mul, hc,
    Int.cast_negOnePow_natCast, transpose_f, BasedComplex.transpose_f_apply,
    ← eps_eq_neg_one_pow (A.C i) (hA i)]

/-- Based strict symmetry gives Ranicki's strict symmetry of the realized duality map. -/
theorem isStrictSymm_dualityMap {hN : A.DimLE N} {φ : Hom (A.dual N hN) A} (h : IsSymm hN φ) :
    IsStrictSymm (asymptoticObjInvolution π X) N (dualityMap π hN φ) := by
  rw [IsStrictSymm, transposeHom_dualityMap, (isSymm_iff_transpose_eq hN φ).mp h]

end Asymptotic

section AsymptoticQuot

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  (π : ∀ i, G i →* H) {Y : Type} [MulAction H Y] [PseudoEMetricSpace Y] [IsIsometricSMul H Y]

/-- `dualIso` in the asymptotic category `𝒜_G(Y)`, for the transpose involution of
`asymptoticInvCat`. -/
def dualIsoQuot (A : ControlledSeq Y) (N : ℕ) (hN : A.DimLE N) :
    dualComplex (asymptoticInvCat π Y).inv N ((asymptoticQuotInv π Y).mapC (A.toComplex π)) ≅
      (asymptoticQuotInv π Y).mapC ((A.dual N hN).toComplex π) :=
  ((asymptoticQuotInv π Y).mapDualIso N (A.toComplex π)).symm ≪≫
    ((asymptoticQuotInv π Y).F.mapHomologicalComplex _).mapIso (dualIso π A N hN)

theorem dualIsoQuot_hom_f (A : ControlledSeq Y) (N : ℕ) (hN : A.DimLE N) (r : ℤ) :
    (dualIsoQuot π A N hN).hom.f r =
      AsymptoticCategory.functor.map ((dualIso π A N hN).hom.f r) := by
  simp [dualIsoQuot, asymptoticQuotInv_F]
  erw [Iso.trans_hom, HomologicalComplex.comp_f, Iso.symm_hom, InvFunctor.mapDualIso_inv_f,
    Category.id_comp]
  rfl

end AsymptoticQuot

/-! ### Controlled symmetric dualities and the controlled Poincaré complex -/

/-- A controlled `N`-dimensional strictly symmetric duality: a controlled homotopy equivalence
`A^{N-*} ≃ A` whose terms `φ_i` are strictly symmetric. -/
structure SymDuality (A : ControlledSeq X) (N : ℕ) (hN : A.DimLE N) extends
    ControlledSeq.HtpyEquiv (A.dual N hN) A where
  symm : IsSymm hN hom

namespace SymDuality

variable {hN : A.DimLE N}

/-- Uniformly controlled termwise symmetric dualities: the duality maps `φ_i`, their inverses
and both homotopies have propagation tending to zero. -/
def ofSeq (Φ : ∀ i, BasedComplex.SymDuality (A.C i) N (hN i))
    (hφ : PropTendsto (fun i ↦ (Φ i).hom.f) A.label A.label)
    (hψ : PropTendsto (fun i ↦ (Φ i).inv.f) A.label A.label)
    (h₁ : PropTendsto (fun i ↦ (Φ i).homInv.h) A.label A.label)
    (h₂ : PropTendsto (fun i ↦ (Φ i).invHom.h) A.label A.label) : A.SymDuality N hN where
  hom := ⟨fun i ↦ (Φ i).hom, hφ⟩
  inv := ⟨fun i ↦ (Φ i).inv, hψ⟩
  homInv := ⟨fun i ↦ (Φ i).homInv, h₁⟩
  invHom := ⟨fun i ↦ (Φ i).invHom, h₂⟩
  symm i := (Φ i).symm

/-- **Controlled symmetrization** (l. 271): a controlled duality equivalence `φ₀` with a
controlled flip homotopy `U : φ₀ ≃ Tφ₀` gives the controlled symmetric duality
`(φ₀ + Tφ₀)/2`, with the same inverse (termwise `BasedComplex.SymDuality.ofFlip`). -/
def ofFlip (e : ControlledSeq.HtpyEquiv (A.dual N hN) A)
    (U : Htpy e.hom (transpose hN hN e.hom)) : A.SymDuality N hN :=
  ofSeq (fun i ↦ BasedComplex.SymDuality.ofFlip ⟨e.hom.f i, e.inv.f i, e.homInv.h i, e.invHom.h i⟩
      (U.h i))
    ((e.hom.tendsto.add (transpose hN hN e.hom).tendsto).smul (1 / 2)) e.inv.tendsto
    ((e.inv.tendsto.mul (U.tendsto.smul (1 / 2)).neg).add e.homInv.tendsto)
    (((U.tendsto.smul (1 / 2)).neg.mul e.inv.tendsto).add e.invHom.tendsto)

theorem ofFlip_hom_f (e : ControlledSeq.HtpyEquiv (A.dual N hN) A)
    (U : Htpy e.hom (transpose hN hN e.hom)) (i : ℕ) :
    (ofFlip e U).hom.f i = sym (hN i) (e.hom.f i) := rfl

theorem ofFlip_inv (e : ControlledSeq.HtpyEquiv (A.dual N hN) A)
    (U : Htpy e.hom (transpose hN hN e.hom)) : (ofFlip e U).inv = e.inv := rfl

/-- The `i`-th term as a based symmetric duality. -/
def term (P : A.SymDuality N hN) (i : ℕ) : BasedComplex.SymDuality (A.C i) N (hN i) where
  hom := P.hom.f i
  inv := P.inv.f i
  homInv := P.homInv.h i
  invHom := P.invHom.h i
  symm := P.symm i

section Asymptotic

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  (π : ∀ i, G i →* H) [MulAction H X] [IsIsometricSMul H X]

/-- The complex of a sequence of dimension `≤ N` is concentrated in `[0, N]`. -/
theorem supportedIn_id (hN : A.DimLE N) :
    SupportedIn (𝟙 (A.toComplex π)) 0 N := fun r hr ↦ by
  rw [HomologicalComplex.id_f]
  change 𝟙 (A.obj π r) = 0
  rw [← hom_one (A := A) (π := π) (r := r)]
  refine hom_eq_zero _ _ fun i κ σ hσ _ ↦ ?_
  have := hN i σ
  omega

/-- **The controlled Poincaré complex of a chain model** over the prequotient: `(A, φ)` with
`φ = (φ_i)` realized through `dualIso`, as an M1 strictly symmetric Poincaré complex. -/
@[reducible] def symPoincareObj (P : A.SymDuality N hN) : SymPoincare (asymptoticObjInvolution π X) N where
  C := A.toComplex π
  p := 𝟙 _
  p_idem := by simp
  support := supportedIn_id π hN
  φ := dualityMap π hN P.hom
  φ_kar := by simp
  symm := isStrictSymm_dualityMap P.symm
  poincare := by
    refine ⟨P.inv.toComplex π ≫ (dualIso π A N hN).inv, by simp, ⟨?_⟩, ⟨?_⟩⟩
    · refine homotopyCongr (P.invHom.toHomotopy π) ?_ (Hom.toComplex_id A)
      rw [Hom.toComplex_comp]; simp [dualityMap]
    · refine homotopyCongr (((P.homInv.toHomotopy π).compRight (dualIso π A N hN).inv).compLeft
        (dualIso π A N hN).hom) ?_ ?_
      · rw [Hom.toComplex_comp]; simp [dualityMap]
      · simp [Hom.toComplex_id]

theorem symPoincareObj_C (P : A.SymDuality N hN) : (P.symPoincareObj π).C = A.toComplex π := rfl

theorem symPoincareObj_φ (P : A.SymDuality N hN) :
    (P.symPoincareObj π).φ = dualityMap π hN P.hom := rfl

end Asymptotic

section InvCat

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  (π : ∀ i, G i →* H) {Y : Type} [MulAction H Y] [PseudoEMetricSpace Y] [IsIsometricSMul H Y]
  {A : ControlledSeq Y} {hN : A.DimLE N}

/-- The controlled Poincaré complex of a chain model in the asymptotic `InvCat` `𝒜_G(Y)`. -/
def symPoincare (P : A.SymDuality N hN) : SymPoincare (asymptoticInvCat π Y).inv N :=
  (P.symPoincareObj π).map (asymptoticQuotInv π Y)

theorem symPoincare_C (P : A.SymDuality N hN) :
    (P.symPoincare π).C =
      (AsymptoticCategory.functor.mapHomologicalComplex _).obj (A.toComplex π) := rfl

/-- Its image in the exterior quotient `ℬ_Z(Y) = 𝒜_G(Y)/𝒜_Z(Y)`. -/
def extSymPoincare (Z : Set Y) (P : A.SymDuality N hN) :
    SymPoincare (exteriorInvCat π Z).inv N :=
  (P.symPoincare π).map (supportKaroubiFiltration π Z).proj

end InvCat

end SymDuality

/-! ### Graph types under duality -/

section Graph

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] {π : ∀ i, G i →* H}
  [MulAction H X] [IsIsometricSMul H X] {J : ℕ → Type*} {τ : ∀ i, J i → G i}

/-- **Duality inverts graph types**: the termwise duals `a_j^{N-*} = a_jᵀ` of a family of chain
maps of uniform graph type `τ` form a family of type `τ⁻¹`. -/
@[simps]
def GraphHom.dual (F : GraphHom π τ A B) (N : ℕ) (hA : A.DimLE N) (hB : B.DimLE N) :
    GraphHom π (fun i j ↦ (τ i j)⁻¹) (B.dual N hB) (A.dual N hA) :=
  ⟨fun i j ↦ (F.f i j).dual N (hA i) (hB i), by simpa using F.tendsto.transpose⟩

/-- The duals of a family of homotopies of type `τ`, of type `τ⁻¹`. -/
@[simps]
def GraphHtpy.dual {F F' : GraphHom π τ A B} (K : GraphHtpy π F F') (hA : A.DimLE N)
    (hB : B.DimLE N) : GraphHtpy π (F.dual N hA hB) (F'.dual N hA hB) :=
  ⟨fun i j ↦ (K.h i j).dual (hA i) (hB i),
    ((K.tendsto.transpose.mul_right (PropTendsto.sgn.on fun _ _ ↦ True)
      (Eventually.of_forall fun _ _ _ _ _ ↦ trivial)).smul fun _ _ ↦ -(-1 : ℚ) ^ N).congr
      (funext₂ fun _ _ ↦ (map_inv _ _).symm) rfl⟩

variable [∀ i, Fintype (G i)] [∀ i, Fintype (J i)]

set_option maxHeartbeats 1000000 in
/-- `dualIso` turns the dual `∑_j (a_j ⊗ R_{τ_j⁻¹})^* ` of a shifted sum into the shifted sum
`∑_j a_j^{N-*} ⊗ R_{τ_j}` of the duals, of types `τ⁻¹`. -/
theorem GraphHom.dualHom_toComplex (F : GraphHom π τ A B) (hA : A.DimLE N) (hB : B.DimLE N) :
    dualHom (asymptoticObjInvolution π X) N (F.toComplex π) =
      (dualIso π B N hB).hom ≫ (F.dual N hA hB).toComplex π ≫ (dualIso π A N hA).inv := by
  ext r
  simp only [HomologicalComplex.comp_f, dualHom_f, asymptoticObjInvolution_star,
    GraphHom.toComplex_f, dualIso_hom_f, dualIso_inv_f, transpose_graphHom]
  erw [graphHom_comp_hom _ _ _ fun i j κ σ h hσ ↦ by
      exact (((F.f i j).dual N (hA i) (hB i)).deg0 κ σ h).trans ((add_zero _).trans hσ),
    hom_comp_graphHom _ _ _ fun i κ σ h hσ ↦ by
      obtain rfl := eq_of_one_ne_zero h; exact (deg_dual_iff hB κ).mp hσ]
  exact graphHom_congr rfl (funext₂ fun i j ↦ by simp) _ _ _ _

set_option maxHeartbeats 1000000 in
/-- `dualIso` turns Compression's dual of a shifted homotopy family into the shifted sum of the
based dual homotopies. -/
theorem GraphHtpy.dualHomotopy_toHomotopy_hom {F F' : GraphHom π τ A B} (K : GraphHtpy π F F')
    (hA : A.DimLE N) (hB : B.DimLE N) (r r' : ℤ) :
    (dualHomotopy (asymptoticObjInvolution π X) N K.toHomotopy).hom r r' =
      (dualIso π B N hB).hom.f r ≫ (K.dual hA hB).toHomotopy.hom r r' ≫
        (dualIso π A N hA).inv.f r' := by
  by_cases hr : r + 1 = r'
  swap
  · have h₁ := (dualHomotopy (asymptoticObjInvolution π X) N K.toHomotopy).zero r r'
      (by simpa using hr)
    have h₂ := (K.dual hA hB).toHomotopy.zero r r' (by simpa using hr)
    rw [h₁, h₂, zero_comp, comp_zero]
  subst hr
  change (r + 1).negOnePow • AsymptoticObject.transpose (graphHom π τ (fun i j ↦ (K.h i j).h)
      K.tendsto (N - (r + 1)) (N - r)) =
    hom (A := B) (B := B.dual N hB) π (fun i ↦ (1 : Matrix (B.C i).X (B.C i).X ℚ))
        PropTendsto.one (N - r) r ≫
      graphHom π (fun i j ↦ (τ i j)⁻¹) (fun i j ↦ ((K.dual hA hB).h i j).h) (K.dual hA hB).tendsto
        r (r + 1) ≫
      hom (A := A.dual N hA) (B := A) π (fun i ↦ (1 : Matrix (A.C i).X (A.C i).X ℚ))
        PropTendsto.one (r + 1) (N - (r + 1))
  erw [transpose_graphHom, Units.smul_def, ← Int.cast_smul_eq_zsmul ℚ, graphHom_smul,
    graphHom_comp_hom _ _ _ fun i j κ σ h hσ ↦ by
      exact (((K.h i j).dual (hA i) (hB i)).deg1 κ σ h).trans (congrArg (· + 1) hσ),
    hom_comp_graphHom _ _ _ fun i κ σ h hσ ↦ by
      obtain rfl := eq_of_one_ne_zero h; exact (deg_dual_iff hB κ).mp hσ]
  refine graphHom_eq_of_blockMat _ _ fun i j ↦ ?_
  ext k' k
  have hσ : ((B.C i).deg ((cellEquiv (B.C i) (N - r)).symm k).1 : ℤ) = N - r :=
    ((cellEquiv (B.C i) (N - r)).symm k).2
  simp only [blockMat, submatrix_apply, Matrix.mul_one, Matrix.one_mul, GraphHtpy.dual_h,
    BasedComplex.Htpy.dual, Matrix.smul_apply, transpose_apply, sgn, mul_diagonal, smul_eq_mul]
  rw [Int.negOnePow_succ, Units.val_neg, Int.cast_neg,
    MatRealization.negOnePow_cast_eq (k := (B.C i).deg _) hσ]
  ring

end Graph

/-! ### Compression through the dual near part: `φ̂` and `b̂` -/

section Compress

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  {π : ∀ i, G i →* H} [MulAction H X] [IsIsometricSMul H X]

variable (π) in
/-- The realized map `A → B^{N-*}` of a controlled `ψ : A → B^{N-*}` (e.g. the inverse `b` of a
duality). -/
def toDualMap (hB : B.DimLE N) (ψ : Hom A (B.dual N hB)) :
    A.toComplex π ⟶ dualComplex (asymptoticObjInvolution π X) N (B.toComplex π) :=
  ψ.toComplex π ≫ (dualIso π B N hB).inv

theorem toDualMap_f (hB : B.DimLE N) (ψ : Hom A (B.dual N hB)) (r : ℤ) :
    (toDualMap π hB ψ).f r = hom (A := A) (B := B) π (fun i ↦ (ψ.f i).f) ψ.tendsto r (N - r) := by
  erw [toDualMap, HomologicalComplex.comp_f, dualIso_inv_f, Hom.toComplex_f,
    hom_comp _ _ _ _ fun i κ σ h hσ ↦ by exact ((ψ.f i).deg0 κ σ h).trans ((add_zero _).trans hσ)]
  exact hom_congr (funext fun _ ↦ Matrix.one_mul _) _ _ _ _

variable {D D' : ControlledSeq X} {far : ∀ i, (D.C i).X → Prop} {far' : ∀ i, (D'.C i).X → Prop}
  [∀ i, DecidablePred (far i)] [∀ i, DecidablePred (far' i)]
  {hfar : ∀ i, (D.C i).IsSub (far i)} {hfar' : ∀ i, (D'.C i).IsSub (far' i)}

theorem dimLE_quot (hD : D.DimLE N) : (D.quot far hfar).DimLE N := fun i σ ↦ hD i σ.1

/-- Restrictions of controlled matrices to the retained cells are controlled. -/
theorem PropTendsto.quot {u : ∀ i, Matrix (D'.C i).X (D.C i).X ℚ}
    (hu : PropTendsto u D.label D'.label) :
    PropTendsto (fun i ↦ (u i).submatrix Subtype.val Subtype.val) (D.quot far hfar).label
      (D'.quot far' hfar').label :=
  tendsto_zero_of_le hu fun _ ↦ prop_submatrix_le _ _

theorem nearProj_transpose {α : Type*} [DecidableEq α] (P : α → Prop) :
    (nearProj P)ᵀ = nearIncl P := by
  ext ρ σ; simp [nearProj, nearIncl]

theorem nearIncl_transpose {α : Type*} [DecidableEq α] (P : α → Prop) :
    (nearIncl P)ᵀ = nearProj P := by
  rw [← nearProj_transpose, Matrix.transpose_transpose]

/-- The section `π^*` of the dual near part is the inclusion of the retained cells. -/
theorem dualNearPart_nearPart_i (r : ℤ) :
    (dualNearPart (asymptoticObjInvolution π X) N (nearPart π D far hfar) r).i =
      hom (A := D.quot far hfar) (B := D) π (fun i ↦ nearIncl fun σ ↦ ¬far i σ)
        (tendsto_nearIncl D far hfar) (N - r) (N - r) := by
  erw [Compression.dualNearPart_i, nearPart_r, asymptoticObjInvolution_star, transpose_hom]
  exact hom_congr (funext fun _ ↦ nearProj_transpose _) _ _ _ _

/-- The retraction `σ^*` of the dual near part is the projection onto the retained cells. -/
theorem dualNearPart_nearPart_r (r : ℤ) :
    (dualNearPart (asymptoticObjInvolution π X) N (nearPart π D far hfar) r).r =
      hom (A := D) (B := D.quot far hfar) π (fun i ↦ nearProj fun σ ↦ ¬far i σ)
        (D.toQuot far hfar).tendsto (N - r) (N - r) := by
  erw [Compression.dualNearPart_r, nearPart_i, asymptoticObjInvolution_star, transpose_hom]
  exact hom_congr (funext fun _ ↦ nearIncl_transpose _) _ _ _ _

/-- The far projection `P^*` of the dual near part is the diagonal projection onto the far
cells, in degree `N - r`. -/
theorem far_dualNearPart (r : ℤ) :
    Compression.far (dualNearPart (asymptoticObjInvolution π X) N (nearPart π D far hfar) r) =
      hom π (fun i ↦ farProj (far i)) (tendsto_farProj D far) (N - r) (N - r) := by
  rw [dualNearPart, far_starRetract, far_nearPart, asymptoticObjInvolution_star, transpose_hom]
  refine hom_congr (funext fun i ↦ ?_) _ _ _ _
  ext a b
  simp only [transpose_apply, farProj, Matrix.diagonal, Matrix.of_apply]
  by_cases h : a = b
  · subst h; rfl
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

/-- **`φ̂ = π φ π^*` is the restricted matrix**: the compression through the dual near part of the
realized duality map of `φ : D^{N-*} → D'` is realized by `φ` on the retained cells. -/
theorem compress_dualityMap (hD : D.DimLE N) (φ : Hom (D.dual N hD) D') (r : ℤ) :
    Compression.compress (dualNearPart (asymptoticObjInvolution π X) N (nearPart π D far hfar) r)
        (nearPart π D' far' hfar' r) ((dualityMap π hD φ).f r) =
      hom (A := D.quot far hfar) (B := D'.quot far' hfar') π
        (fun i ↦ (φ.f i).f.submatrix Subtype.val Subtype.val)
        (PropTendsto.quot (D := D) (D' := D') (hfar := hfar) (hfar' := hfar') φ.tendsto)
        (N - r) r := by
  erw [Compression.compress, dualNearPart_nearPart_i, dualityMap_f, nearPart_r,
    hom_comp _ _ _ _ fun i κ σ h hσ ↦ by
      exact ((φ.f i).deg0 κ σ h).trans ((add_zero _).trans ((deg_dual_iff hD σ).mp hσ)),
    hom_comp _ _ _ _ fun i κ σ h hσ ↦ by obtain rfl := nearIncl_ne_zero h; exact hσ]
  exact hom_congr (funext fun _ ↦ nearProj_mul_mul_nearIncl _) _ _ _ _

/-- **`b̂ = σ^* b σ` is the restricted matrix**: the compression into the dual near part of the
realized `ψ : D → D'^{N-*}` is realized by `ψ` on the retained cells. -/
theorem compress_toDualMap (hD' : D'.DimLE N) (ψ : Hom D (D'.dual N hD')) (r : ℤ) :
    Compression.compress (nearPart π D far hfar r)
        (dualNearPart (asymptoticObjInvolution π X) N (nearPart π D' far' hfar') r)
        ((toDualMap π hD' ψ).f r) =
      hom (A := D.quot far hfar) (B := D'.quot far' hfar') π
        (fun i ↦ (ψ.f i).f.submatrix Subtype.val Subtype.val)
        (PropTendsto.quot (D := D) (D' := D') (hfar := hfar) (hfar' := hfar') ψ.tendsto)
        r (N - r) := by
  erw [Compression.compress, nearPart_i, toDualMap_f, dualNearPart_nearPart_r,
    hom_comp _ _ _ _ fun i κ σ h hσ ↦ by
      exact (deg_dual_iff hD' κ).mpr (((ψ.f i).deg0 κ σ h).trans ((add_zero _).trans hσ)),
    hom_comp _ _ _ _ fun i κ σ h hσ ↦ by obtain rfl := nearIncl_ne_zero h; exact hσ]
  exact hom_congr (funext fun _ ↦ nearProj_mul_mul_nearIncl _) _ _ _ _

/-- The compressed duality `π φ π^* : (D/F)^{N-*} → D'/F'` of a controlled `φ : D^{N-*} → D'`,
a controlled chain map since `π` and `π^*` are. -/
def compressDuality (hD : D.DimLE N) (φ : Hom (D.dual N hD) D') :
    Hom ((D.quot far hfar).dual N (dimLE_quot hD)) (D'.quot far' hfar') :=
  (D'.toQuot far' hfar').comp (φ.comp ((D.toQuot far hfar).dual N hD (dimLE_quot hD)))

theorem compressDuality_f (hD : D.DimLE N) (φ : Hom (D.dual N hD) D') (i : ℕ) :
    ((compressDuality (far := far) (far' := far') (hfar := hfar) (hfar' := hfar') hD φ).f i).f =
      (φ.f i).f.submatrix Subtype.val Subtype.val := by
  rw [← nearProj_mul_mul_nearIncl (P := fun σ ↦ ¬far' i σ) (Q := fun σ ↦ ¬far i σ),
    ← nearProj_transpose, Matrix.mul_assoc]
  rfl

/-- **`φ̂` of Compression is the realized compressed duality** (l. 769): `hatPhi` of the realized
`φ` is, degreewise, the realization of the based `π φ π^*`. -/
theorem hatPhi_dualityMap (hD : D.DimLE N) (φ : Hom (D.dual N hD) D) (r : ℤ) :
    (hatPhi (asymptoticObjInvolution π X) N (nearPart π D far hfar)
        (farClosed_nearPart π D far hfar) (dualityMap π hD φ)).f r =
      (dualityMap π (dimLE_quot hD) (compressDuality (far := far) (far' := far) (hfar := hfar)
        (hfar' := hfar) hD φ)).f r := by
  erw [hatPhi_f, compress_dualityMap, dualityMap_f]
  exact hom_congr (funext fun i ↦ (compressDuality_f hD φ i).symm) _ _ _ _

end Compress

end ControlledSeq

end BasedComplex

end HSFormal.Cubical
