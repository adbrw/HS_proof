import HSFormal.LTheory.Model.CutComplex
import HSFormal.LTheory.Model.CutTrunc
import HSFormal.LTheory.Model.Domination
import HSFormal.LTheory.Model.FreeLineAux

/-!
# The lower cut pair of a free Poincaré complex over `C_ℤ(A)`, with window boundary

Lower L-theory model, module 22 (`DecBij`), part 4: algebraic transversality for honest free
complexes, the half that does not need the line complex or triads.

Let `P = (C, 1, φ)` be an `(N+1)`-dimensional Poincaré complex over `C_ℤ(A)` with identity Kar
idempotent (so `C` vanishes outside `[0, N+1]`), and `D` cut data (`CZ.CutData`: propagation bound
`b`, thresholds `t_{r-1} + b ≤ t_r`).  Let `T = C|_{(-∞, t_*)}` be the lower Thom complex with
`θ = q^* φ q` (`CutData.thom`).

* **Connectivity at the ends** (`SymComplex.bdSec`, `SymComplex.bdRet`).  If
  `σ₁ θ_0 + σ₂ d = 1` on `T_0` (a splitting of `(θ_0, d) : T^{N+1} ⊕ T_1 ⟶ T_0`), then
  `ρ = -(σ₁, σ₂)` is a section of `d : ∂T_0 ⟶ ∂T_{-1}` (`bdSec_d`); transporting its dual
  along the chain isomorphism `∂φ₀ = bdSwap` gives a retraction of `d : ∂T_{N+1} ⟶ ∂T_N`
  (`d_bdRet`).  For the Thom complex, `σ₁ = ι_E ψ_0 π_E`, `σ₂ = -ι_E H_{0,1} π_E` come from the
  Poincaré inverse `ψ` of `P` and a homotopy `H : ψ φ ≃ 1` (`CutData.Sec`), using that `ψ_0` and
  `H_{0,1}` have propagation `≤ b` and `t_0 + b ≤ t_1, t_{N+1}` (`CutData.sec_eq`).
* **The truncated boundary** (`CutData.truncIdem`): cancelling these two elementary pairs
  (`KarCancel`) turns the boundary idempotent `p_∂ = 1` of `∂T` (supported in `[-1, N+1]`) into a
  Kar homotopy equivalent idempotent supported in `[0, N]` (`truncIdem_support`).
* **The lower pair** `CutData.lowerPair`: Ranicki's boundary pair `(∂T ⟶ T^{N+1-*}, (0, ∂φ))`
  transported along this truncation (`SymComplex.boundaryPairOf`), an `(N+1)`-dimensional
  Poincaré pair over `C_ℤ(A)` all of whose chain objects (interior and boundary) lie in the
  negative half-line (`lowerPair_D_negHalf`, `lowerPair_bd_negHalf`).
* **Window boundary** (`CutData.exists_lowerPair_window`): the boundary of the lower pair is
  homotopy isometric to the image of an `N`-dimensional Poincaré complex over the bounded
  category `C_ℤ^{bdd}(A)` (equivalently over `A`, `Lconc.czBddEquiv`): `∂T` is contractible modulo
  bounded objects because `θ` is Poincaré modulo bounded objects (`thom_isPoincare_mod`), so
  domination plus the Balmer–Schlichting splitting (`SymPoincare.exists_sub`) give a Kar model.
* `CZ.exists_lowerPair`: the unconditional statement for every honest free `P` (bounds and
  thresholds `t_r = r b` are chosen).

**Blueprint check.** The blueprint's "common boundary `∂P` concentrated in a bounded window
(hence a complex over `B`)" is only correct for *Kar* (projective) complexes: the boundary of a
cut of a free complex is Kar homotopy equivalent to a window complex whose projective class is
the image of the torsion of `φ` in `K₀(Kar A)` (nonzero in general at level `0`), so it cannot
in general be taken free.  This is harmless since `Lconc A N` is `L^p`.  Moreover, Ranicki's
boundary of a Thom complex in `[0, N+1]` lives in `[-1, N+1]`; the truncation above (which uses
the Poincaré inverse of `P`) is needed even to state it as a `SymPoincare`.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression
  homotopyCofiber

noncomputable section

attribute [local implicit_reducible] CZ.cut CZ.diagSplitting

/-! ### Sections at the two ends of the boundary -/

namespace SymComplex

variable {V : Type*} [Category V] [Preadditive V] [HasBinaryBiproducts V]
  {J : StrictInvolution V} {N : ℤ} (X : SymComplex J (N + 1))

/-- The section `ρ = -(σ₁, σ₂) : ∂C_{-1} = C_0 ⟶ ∂C_0 = C^{N+1} ⊕ C_1` of `d`, from a splitting
`σ₁ φ_0 + σ₂ d = 1` of `(φ_0, d)`. -/
def bdSec (σ₁ : X.C.X 0 ⟶ (dualComplex J (N + 1) X.C).X 0) (σ₂ : X.C.X 0 ⟶ X.C.X 1) :
    X.bdC.X (-1) ⟶ X.bdC.X 0 :=
  -(sndX X.φ 0 ≫ (σ₁ ≫ inlX X.φ 0 1 (by simp) + σ₂ ≫ inrX X.φ 1))

lemma bdSec_d {σ₁ : X.C.X 0 ⟶ (dualComplex J (N + 1) X.C).X 0} {σ₂ : X.C.X 0 ⟶ X.C.X 1}
    (hσ : σ₁ ≫ X.φ.f 0 + σ₂ ≫ X.C.d 1 0 = 𝟙 _)
    (hz : IsZero ((dualComplex J (N + 1) X.C).X (-1))) :
    X.bdSec σ₁ σ₂ ≫ X.bdC.d 0 (-1) = 𝟙 _ := by
  change (-(sndX X.φ 0 ≫ (σ₁ ≫ inlX X.φ 0 1 (by simp) + σ₂ ≫ inrX X.φ 1))) ≫
    (-(cone X.φ).d 1 0) = 𝟙 ((cone X.φ).X 0)
  have hl : inlX X.φ (-1) 0 (by simp) = 0 := hz.eq_of_src _ _
  rw [Preadditive.neg_comp_neg, cone.id_X X.φ 0 (-1) (by simp), hl, comp_zero]
  simp only [homotopyCofiber_d, assoc, add_comp, comp_add,
    inlX_d X.φ 1 0 (-1) (by simp) (by simp), inrX_d, hl, comp_zero, neg_zero, zero_add]
  rw [← comp_add, ← assoc σ₁, ← assoc σ₂, ← add_comp, hσ, id_comp]

/-- The retraction `τ : ∂C_N ⟶ ∂C_{N+1}` of `d`: the dual of a section `ρ` of
`d : ∂C_0 ⟶ ∂C_{-1}`, transported along the chain isomorphism `∂φ₀ : ∂C^{N-*} ≅ ∂C`. -/
def bdRet (ρ : X.bdC.X (-1) ⟶ X.bdC.X 0) : X.bdC.X N ⟶ X.bdC.X (N + 1) :=
  (inv X.bdSwap).f N ≫ ((N + 1).negOnePow • J.star
    ((X.bdC.XIsoOfEq (by omega : N - (N + 1) = -1)).hom ≫ ρ ≫
      (X.bdC.XIsoOfEq (by omega : 0 = N - N)).hom)) ≫ X.bdSwap.f (N + 1)

lemma d_bdRet {ρ : X.bdC.X (-1) ⟶ X.bdC.X 0} (hρ : ρ ≫ X.bdC.d 0 (-1) = 𝟙 _) :
    X.bdC.d (N + 1) N ≫ X.bdRet ρ = 𝟙 _ := by
  have hρ' : ((X.bdC.XIsoOfEq (by omega : N - (N + 1) = -1)).hom ≫ ρ ≫
      (X.bdC.XIsoOfEq (by omega : 0 = N - N)).hom) ≫ X.bdC.d (N - N) (N - (N + 1)) = 𝟙 _ := by
    rw [assoc, assoc, HomologicalComplex.XIsoOfEq_hom_comp_d,
      ← HomologicalComplex.d_comp_XIsoOfEq_hom X.bdC (show (-1 : ℤ) = N - (N + 1) by omega),
      reassoc_of% hρ]
    simp
  have h₁ : X.bdC.d (N + 1) N ≫ (inv X.bdSwap).f N =
      (inv X.bdSwap).f (N + 1) ≫ (dualComplex J N X.bdC).d (N + 1) N :=
    ((inv X.bdSwap).comm (N + 1) N).symm
  rw [bdRet, ← assoc, h₁, assoc, ← assoc ((dualComplex J N X.bdC).d (N + 1) N), dualComplex_d,
    Linear.units_smul_comp, Linear.comp_units_smul, smul_smul, Int.units_mul_self, one_smul,
    ← J.star_comp, hρ', J.star_id]
  erw [id_comp]
  rw [← comp_f, IsIso.inv_hom_id, id_f]

end SymComplex

/-! ### Contractibility modulo `U` passes to smaller idempotents -/

lemma KaroubiFiltration.contractibleMod_of_le {A' : InvCat} {F : KaroubiFiltration A'}
    {D : ChainComplex A' ℤ} {p q : D ⟶ D} (h : F.ContractibleMod p) (hq : q ≫ q = q)
    (hqp : q ≫ p = q) : F.ContractibleMod q := by
  obtain ⟨e, -, heU, ⟨H⟩⟩ := h
  refine ⟨q ≫ e ≫ q, by simp only [assoc, hq, reassoc_of% hq], fun r ↦ ?_,
    ⟨homotopyCongr ((H.compRight q).compLeft q) rfl (by rw [reassoc_of% hqp, hq])⟩⟩
  rw [comp_f, comp_f, ← assoc]
  exact ((heU r).comp_left _).comp_right _

/-! ### Honest free complexes and their lower Thom complexes -/

namespace CZ

variable {A : InvCat} {N : ℤ}

lemma isZero_obj_of_isZero {X : A.cz} (h : IsZero X) (v : ℤ) : IsZero (X.obj v) := by
  rw [IsZero.iff_id_eq_zero, ← id_apply_self, h.eq_of_src (𝟙 X) 0, zero_apply]

lemma isZero_cut_E_of_isZero {X : A.cz} (h : IsZero X) (p : ℤ → Prop) [DecidablePred p] :
    IsZero (cut X p).E :=
  isZero_of_forall fun v ↦ by
    change IsZero (if p v then splitE (X.obj v) else splitU (X.obj v)).E
    split_ifs
    · exact isZero_obj_of_isZero h v
    · exact isZero_zero A

/-- A Poincaré complex with identity Kar idempotent vanishes outside `[0, N+1]`. -/
lemma isZero_X_of_p_eq_id {P : SymPoincare A.cz.inv (N + 1)} (hp : P.p = 𝟙 _) {r : ℤ}
    (hr : r < 0 ∨ N + 1 < r) : IsZero (P.C.X r) := by
  rw [IsZero.iff_id_eq_zero, ← HomologicalComplex.id_f, ← hp]
  exact P.support r hr

/-- Propagation bounds for a family of morphisms vanishing outside a finite set. -/
lemma exists_bound_family {X Y : ℤ → A.cz} (f : ∀ r, X r ⟶ Y r) (S : Finset ℤ)
    (h : ∀ r ∉ S, f r = 0) : ∃ b : ℕ, ∀ r, PropLE (f r).1 b := by
  refine ⟨S.sup fun r ↦ Classical.choose (exists_propLE (f r)), fun r ↦ ?_⟩
  by_cases hr : r ∈ S
  · exact (Classical.choose_spec (exists_propLE (f r))).mono
      (Finset.le_sup (f := fun r ↦ Classical.choose (exists_propLE (f r))) hr)
  · rw [h r hr]
    exact PropLE.zero _

namespace CutData

variable {P : SymPoincare A.cz.inv (N + 1)} (D : CutData P)

lemma isZero_thomC (hp : P.p = 𝟙 _) {r : ℤ} (hr : r < 0 ∨ N + 1 < r) : IsZero (D.thomC.X r) :=
  isZero_cut_E_of_isZero (isZero_X_of_p_eq_id hp hr) _

lemma pT_eq_id (hp : P.p = 𝟙 _) : D.pT = 𝟙 _ := by
  ext r : 1
  rw [pT_f, hp, id_f, id_comp, Splitting.ιE_πE]
  rfl

lemma bdP_eq_id (hp : P.p = 𝟙 _) : D.thom.bdP = 𝟙 _ := by
  ext r : 1
  change (coneMap (dualHom A.cz.inv (N + 1) D.pT) D.pT D.thom.comm).f (r + 1) = 𝟙 _
  apply ext_from_X D.thom.φ r (r + 1) (by simp)
  · rw [inlX_coneMap_f, dualHom_f, D.pT_eq_id hp, id_f]
    erw [A.cz.inv.star_id, id_comp, comp_id]
  · rw [inrX_coneMap_f, D.pT_eq_id hp, id_f]
    erw [id_comp, comp_id]

/-- A map out of the lower part of degree `r` with propagation `≤ b` lands in the lower part of
any target cut at a threshold `≥ t_r + b`. -/
lemma ιE_comp_idem {r : ℤ} {Y : A.cz} (g : P.C.X r ⟶ Y) (hg : PropLE g.1 D.b) (s : ℤ)
    (hs : D.t r + D.b ≤ s) :
    (D.σ r).ιE ≫ g ≫ (cut Y (fun v ↦ v < s)).idem = (D.σ r).ιE ≫ g := by
  rw [← assoc]
  refine comp_cut_idem _ _ fun w v hw ↦ ?_
  rw [cut_ιE_eq_diag, diag_comp_apply]
  by_cases hv : v < D.t r
  · rw [hg w v (by rw [lt_abs]; omega), comp_zero]
  · exact (isZero_cut_E (P.C.X r) (fun x ↦ x < D.t r) hv).eq_of_src _ _

/-- **Degree-`0` Poincaré data adapted to the cut**: a Poincaré inverse `ψ` of `P` and a homotopy
`H : ψ φ ≃ p` whose relevant components have propagation `≤ b`, with `t_0 + b ≤ t_{N+1}`. -/
structure Sec where
  ψ : P.C ⟶ dualComplex A.cz.inv (N + 1) P.C
  H : Homotopy (ψ ≫ P.φ) P.p
  hψ : PropLE (ψ.f 0).1 D.b
  hH : PropLE (H.hom 0 1).1 D.b
  ht : D.t 0 + D.b ≤ D.t (N + 1 - 0)

variable {D}

namespace Sec

variable (S : D.Sec)

/-- `σ₁ = ι_E ψ_0 π_E : T_0 ⟶ T^{N+1}`. -/
def σ₁ : D.thomC.X 0 ⟶ (dualComplex A.cz.inv (N + 1) D.thomC).X 0 :=
  (D.σ 0).ιE ≫ S.ψ.f 0 ≫ (D.σ (N + 1 - 0)).πE

/-- `σ₂ = -ι_E H_{0,1} π_E : T_0 ⟶ T_1`. -/
def σ₂ : D.thomC.X 0 ⟶ D.thomC.X 1 := -((D.σ 0).ιE ≫ S.H.hom 0 1 ≫ (D.σ 1).πE)

/-- **The degree-`0` splitting** `σ₁ θ_0 + σ₂ d = 1` of the lower Thom complex. -/
lemma sec_eq (hp : P.p = 𝟙 _) : S.σ₁ ≫ D.θ.f 0 + S.σ₂ ≫ D.thomC.d 1 0 = 𝟙 _ := by
  have hc := S.H.comm 0
  rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel 0 (-1) by simp),
    prevD_eq _ (show (ComplexShape.down ℤ).Rel 1 0 by simp)] at hc
  have h0 : P.C.d 0 (-1) = 0 := (isZero_X_of_p_eq_id hp (by omega)).eq_of_tgt _ _
  have hp0 : P.p.f 0 = 𝟙 _ := by rw [hp, id_f]
  rw [h0, zero_comp, zero_add, hp0, comp_f] at hc
  have ht1 : D.t 0 + D.b ≤ D.t 1 := by simpa using D.ht 1
  have e₁ : S.σ₁ ≫ D.θ.f 0 = (D.σ 0).ιE ≫ (S.ψ.f 0 ≫ P.φ.f 0) ≫ (D.σ 0).πE := by
    simp only [σ₁, θ, comp_f, dualHom_f, SplitCx.toQuot_f, assoc]
    erw [star_cut_πE]
    change (D.σ 0).ιE ≫ S.ψ.f 0 ≫ (D.σ (N + 1 - 0)).πE ≫ (D.σ (N + 1 - 0)).ιE ≫ P.φ.f 0 ≫
      (D.σ 0).πE = _
    rw [← assoc (D.σ (N + 1 - 0)).πE, ← Splitting.idem]
    rw [← assoc (S.ψ.f 0), ← assoc (D.σ 0).ιE,
      D.ιE_comp_idem (Y := P.C.X (N + 1 - 0)) (S.ψ.f 0) S.hψ _ S.ht]
    simp only [assoc]
  have e₂ : S.σ₂ ≫ D.thomC.d 1 0 = -((D.σ 0).ιE ≫ (S.H.hom 0 1 ≫ P.C.d 1 0) ≫ (D.σ 0).πE) := by
    simp only [σ₂, SplitCx.quot_d, Preadditive.neg_comp, assoc]
    rw [← assoc (D.σ 1).πE, ← Splitting.idem, ← assoc (S.H.hom 0 1), ← assoc (D.σ 0).ιE,
      D.ιE_comp_idem (S.H.hom 0 1) S.hH _ ht1]
    simp only [assoc]
  rw [e₁, e₂, hc, add_comp, comp_add, id_comp, Splitting.ιE_πE]
  abel

end Sec

variable (S : D.Sec) (hp : P.p = 𝟙 _)

/-- The section `ρ` of `d : ∂T_0 ⟶ ∂T_{-1}`. -/
def ρ : D.thom.bdC.X (-1) ⟶ D.thom.bdC.X 0 := D.thom.bdSec S.σ₁ S.σ₂

include hp in
lemma ρ_d : ρ S ≫ D.thom.bdC.d 0 (-1) = 𝟙 _ :=
  D.thom.bdSec_d (S.sec_eq hp) (D.isZero_thomC hp (by omega))

/-! ### The truncated boundary -/

include hp in
lemma ρ_h₁ : ρ S ≫ D.thom.bdC.d 0 (-1) ≫ ρ S = ρ S := by
  rw [reassoc_of% (ρ_d S hp)]

lemma ρ_h₂ : HomologicalComplex.Hom.f (𝟙 D.thom.bdC) (-1) ≫ ρ S = ρ S := by
  rw [id_f, id_comp]

lemma ρ_h₃ : ρ S ≫ HomologicalComplex.Hom.f (𝟙 D.thom.bdC) 0 = ρ S := by rw [id_f, comp_id]

/-- The first cancellation: `∂T_{-1}` against part of `∂T_0`. -/
def p₁ : D.thom.bdC ⟶ D.thom.bdC :=
  KarCancel.cancel (𝟙 _) (show (-1 : ℤ) + 1 = 0 by norm_num) (ρ S)

include hp in
lemma p₁_idem : p₁ S ≫ p₁ S = p₁ S :=
  KarCancel.cancel_idem (ρ_h₁ S hp) (ρ_h₂ S) (ρ_h₃ S) (id_comp _)

lemma p₁_f_of_ne {r : ℤ} (h : r ≠ -1) (h' : r ≠ 0) : (p₁ S).f r = 𝟙 _ := by
  rw [p₁, KarCancel.cancel_f_of_ne h h', id_f]

/-- The retraction of `d : ∂T_{N+1} ⟶ ∂T_N`. -/
def τ : D.thom.bdC.X N ⟶ D.thom.bdC.X (N + 1) := D.thom.bdRet (ρ S)

/-- The data of the second cancellation, `ρ₂ = p₁ τ`. -/
def ρ₂ : D.thom.bdC.X N ⟶ D.thom.bdC.X (N + 1) := (p₁ S).f N ≫ τ S

variable (hN : 0 ≤ N)

include hp hN in
lemma d_ρ₂ : D.thom.bdC.d (N + 1) N ≫ ρ₂ S = 𝟙 _ := by
  rw [ρ₂, ← assoc, ← (p₁ S).comm (N + 1) N, p₁_f_of_ne S (by omega) (by omega), id_comp]
  exact D.thom.d_bdRet (ρ_d S hp)

include hp hN in
lemma ρ₂_h₁ : ρ₂ S ≫ D.thom.bdC.d (N + 1) N ≫ ρ₂ S = ρ₂ S := by
  rw [d_ρ₂ S hp hN, comp_id]

include hp in
lemma ρ₂_h₂ : (p₁ S).f N ≫ ρ₂ S = ρ₂ S := by
  rw [ρ₂, ← assoc, idem_f (p₁_idem S hp)]

include hN in
lemma ρ₂_h₃ : ρ₂ S ≫ (p₁ S).f (N + 1) = ρ₂ S := by
  rw [p₁_f_of_ne S (by omega) (by omega), comp_id]

/-- **The truncation idempotent** of `∂T`: the second cancellation, `∂T_{N+1}` against part of
`∂T_N`. -/
def truncIdem : D.thom.bdC ⟶ D.thom.bdC :=
  KarCancel.cancel (p₁ S) (show N + 1 = N + 1 from rfl) (ρ₂ S)

include hp hN in
lemma truncIdem_idem : truncIdem S ≫ truncIdem S = truncIdem S :=
  KarCancel.cancel_idem (ρ₂_h₁ S hp hN) (ρ₂_h₂ S hp) (ρ₂_h₃ S hN) (p₁_idem S hp)

include hp hN in
/-- `(∂T, 1) ≃ (∂T, truncIdem)` in `Kar`. -/
def truncEquivId : KarHtpyEquiv (𝟙 D.thom.bdC) (truncIdem S) :=
  (KarCancel.cancelEquiv (ρ_h₁ S hp) (ρ_h₂ S) (ρ_h₃ S) (id_comp _)).trans
    (KarCancel.cancelEquiv (ρ₂_h₁ S hp hN) (ρ₂_h₂ S hp) (ρ₂_h₃ S hN) (p₁_idem S hp))

include hp hN in
/-- `(∂T, p_∂) ≃ (∂T, truncIdem)` in `Kar` (`p_∂ = 1` for honest free `P`). -/
def truncEquiv : KarHtpyEquiv D.thom.bdP (truncIdem S) :=
  (D.bdP_eq_id hp).symm ▸ truncEquivId S hp hN

include hp in
lemma isZero_bdC {r : ℤ} (hr : r < -1 ∨ N + 1 < r) : IsZero (D.thom.bdC.X r) :=
  FreeLine.isZero_cone_X D.thom.φ (r + 1) (D.isZero_thomC hp (by omega))
    (D.isZero_thomC hp (by omega))

include hp hN in
/-- **The truncated boundary idempotent is concentrated in `[0, N]`.** -/
lemma truncIdem_support : SupportedIn (truncIdem S) 0 N := by
  intro r hr
  by_cases h₁ : r = -1
  · subst h₁
    rw [truncIdem, KarCancel.cancel_f_of_ne (by omega) (by omega), p₁, KarCancel.cancel_f_self,
      id_f, ρ_d S hp, sub_self]
  · by_cases h₂ : r = N + 1
    · subst h₂
      rw [truncIdem, KarCancel.cancel_f_succ, d_ρ₂ S hp hN, p₁_f_of_ne S (by omega) (by omega),
        sub_self]
    · exact (isZero_bdC (D := D) hp (by omega)).eq_of_src _ _

/-! ### The lower pair -/

/-- **The lower cut pair** of an honest free `P`: Ranicki's boundary pair
`(∂T ⟶ T^{N+1-*}, (0, ∂φ))` of the lower Thom complex, transported along the truncation of the
boundary to `[0, N]`. -/
def lowerPair : SymPair A.cz.inv N :=
  D.thom.boundaryPairOf D.pT_support (truncEquiv S hp hN) (truncIdem_idem S hp hN)
    (truncIdem_support S hp hN)

@[simp]
lemma lowerPair_D : (lowerPair S hp hN).D = dualComplex A.cz.inv (N + 1) D.thomC := rfl

@[simp]
lemma lowerPair_bd_C : (lowerPair S hp hN).bd.C = D.thom.bdC := rfl

@[simp]
lemma lowerPair_bd_p : (lowerPair S hp hN).bd.p = truncIdem S := rfl

/-- The interior of the lower pair lies in the negative half-line. -/
lemma lowerPair_D_negHalf (r : ℤ) : negHalf A ((lowerPair S hp hN).D.X r) :=
  D.thomC_negHalf (N + 1 - r)

/-- The boundary of the lower pair lies in the negative half-line. -/
lemma lowerPair_bd_negHalf (r : ℤ) : negHalf A ((lowerPair S hp hN).bd.C.X r) :=
  (negHalf A).prop_of_iso (homotopyCofiber.XIsoBiprod D.thom.φ (r + 1) r (by simp)).symm
    (IsAdditiveSub.biprod_mem (BinaryBiproduct.bicone _ _) (BinaryBiproduct.isBilimit _ _)
      (D.thomC_negHalf (N + 1 - r)) (D.thomC_negHalf (r + 1)))

/-- **The boundary of the lower pair has a window model**: it is homotopy isometric to the image
of an `N`-dimensional Poincaré complex over the bounded category `C_ℤ^{bdd}(A)`. -/
theorem exists_lowerPair_window :
    ∃ Q : SymPoincare A.czBdd.inv N,
      Nonempty ((lowerPair S hp hN).bd.HomotopyIsometry (Q.map (A.cz.subIncl (bdd A)))) := by
  have h0 : (bddFiltration A).ContractibleMod D.thom.bdP :=
    KaroubiFiltration.contractibleMod_bd D.thom.p_idem D.thom.φ_kar D.thom.comm
      D.thom_isPoincare_mod
  have h1 : (bddFiltration A).ContractibleMod (lowerPair S hp hN).bd.p :=
    KaroubiFiltration.contractibleMod_of_le h0 (truncIdem_idem S hp hN)
      (by rw [lowerPair_bd_p, D.bdP_eq_id hp]; exact comp_id _)
  exact SymPoincare.exists_sub _ h1

end CutData

/-- **Algebraic transversality, lower half** (unconditional form): every `(N+1)`-dimensional
Poincaré complex `P` over `C_ℤ(A)` with identity Kar idempotent (`N ≥ 0`) admits, for suitable
thresholds (`t_r = r b`), an `(N+1)`-dimensional Poincaré pair `X` over `C_ℤ(A)` whose interior
and boundary have all chain objects in the negative half-line, and whose boundary is homotopy
isometric to the image of an `N`-dimensional Poincaré complex over the bounded category
(the lower cut pair `CutData.lowerPair`; window model `CutData.exists_lowerPair_window`). -/
theorem exists_lowerPair (hN : 0 ≤ N) (P : SymPoincare A.cz.inv (N + 1)) (hp : P.p = 𝟙 _) :
    ∃ (X : SymPair A.cz.inv N) (Q : SymPoincare A.czBdd.inv N),
      (∀ r, negHalf A (X.D.X r)) ∧ (∀ r, negHalf A (X.bd.C.X r)) ∧
      Nonempty (X.bd.HomotopyIsometry (Q.map (A.cz.subIncl (bdd A)))) := by
  obtain ⟨ψ, -, ⟨H⟩, -⟩ := P.poincare
  obtain ⟨b₁, hb₁⟩ := exists_bound_family (X := fun r ↦ P.C.X r) (Y := fun r ↦ P.C.X (r - 1))
    (fun r ↦ P.C.d r (r - 1)) (Finset.Icc 1 (N + 1)) fun r hr ↦ by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hr
      rcases hr with hr | hr
      · exact (isZero_X_of_p_eq_id hp (by omega)).eq_of_tgt _ _
      · exact (isZero_X_of_p_eq_id hp (by omega)).eq_of_src _ _
  obtain ⟨b₂, hb₂⟩ := exists_bound_family
    (X := fun r ↦ (dualComplex A.cz.inv (N + 1) P.C).X r) (Y := fun r ↦ P.C.X r)
    (fun r ↦ P.φ.f r) (Finset.Icc 0 (N + 1)) fun r hr ↦ by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hr
      exact (isZero_X_of_p_eq_id hp (by omega)).eq_of_tgt _ _
  obtain ⟨b₃, hb₃⟩ := exists_propLE (ψ.f 0)
  obtain ⟨b₄, hb₄⟩ := exists_propLE (H.hom 0 1)
  set b := b₁ + b₂ + b₃ + b₄ with hb
  let D : CutData P :=
    { b := b
      t := fun r ↦ r * b
      hd := fun r ↦ (hb₁ r).mono (by omega)
      hφ := fun r ↦ (hb₂ r).mono (by omega)
      ht := fun r ↦ le_of_eq (by ring)
      hp := fun r ↦ Or.inl (by rw [hp, id_f]) }
  let S : D.Sec :=
    { ψ := ψ
      H := H
      hψ := hb₃.mono (show b₃ ≤ b by omega)
      hH := hb₄.mono (show b₄ ≤ b by omega)
      ht := by
        change 0 * (b : ℤ) + b ≤ (N + 1 - 0) * b
        nlinarith [(Nat.cast_nonneg b : (0 : ℤ) ≤ b)] }
  obtain ⟨Q, hQ⟩ := CutData.exists_lowerPair_window S hp hN
  exact ⟨_, Q, CutData.lowerPair_D_negHalf S hp hN, CutData.lowerPair_bd_negHalf S hp hN, hQ⟩

/-- **Algebraic transversality, lower half, at the level of classes**: the boundary of the lower
cut pair of an honest free `P` has the class of a complex over `A` placed at position `0`:
`[∂X] = [Q at 0] ∈ Lconc (C_ℤ A) N` for some `Q : SymPoincare A.inv N` (the window model summed
by `Window.sumF`). -/
theorem exists_lowerPair_cls (hN : 0 ≤ N) (P : SymPoincare A.cz.inv (N + 1)) (hp : P.p = 𝟙 _) :
    ∃ (X : SymPair A.cz.inv N) (Q : SymPoincare A.inv N),
      (∀ r, negHalf A (X.D.X r)) ∧ (∀ r, negHalf A (X.bd.C.X r)) ∧
      Lconc.cls X.bd = Lconc.cls (Q.map (atZero A)) := by
  obtain ⟨X, Q, h₁, h₂, ⟨e⟩⟩ := exists_lowerPair hN P hp
  refine ⟨X, Q.map (Window.sumF A), h₁, h₂, ?_⟩
  have key : Lconc.map (Window.sumF A ≫ atZero A) (Lconc.cls Q) =
      Lconc.cls (Q.map (A.cz.subIncl (bdd A))) := by
    rw [atZero, ← Category.assoc, Lconc.map_comp, AddMonoidHom.comp_apply,
      Lconc.map_eq_of_unitaryIso (Window.sumOfBaseIso A), Lconc.map_id, AddMonoidHom.id_apply,
      Lconc.map_cls]
  rw [Lconc.cls_eq_of_isometry e, ← key, Lconc.map_comp, AddMonoidHom.comp_apply, Lconc.map_cls,
    Lconc.map_cls]

end CZ

end

end HSFormal.LTheory
