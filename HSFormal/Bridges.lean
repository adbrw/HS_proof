import HSFormal.Assembly
import HSFormal.TailGroups
import HSFormal.Cubical.DualBridge
import HSFormal.LTheory.SignatureCobordism
import HSFormal.LTheory.PointCategory

/-!
# Bridges between committed modules

* `FixedData.toTailGroups`: the tail groups `Gᵢ = PadicTail / Kᵢ ≅ ℤ/p^{i+1}` with `πᵢ : Gᵢ ↠ C_p`
  of `TailGroups.lean`, packaged as the `TailGroups` input of `Assembly`.
* `PermRep.matRealization G S`: a based rational matrix `A` acts on `PermRep G S` as `A ⊗ 1_S`
  (a `MatRealization` of the transpose duality).  Hence the cellular `ℂP²` is a symmetric
  Poincaré complex `PermRep.cpSymPoincare` over `PermRep G S`; its ordinary signature is `|S|`
  (`cpSymPoincare_sign₄_one`).  For `G = S = Unit` (`Free(ℚ)`) this is the final signature-one
  class (`cpSymPoincare_unit_sign₄_one`), and its class in `Lconc_4` is nonzero
  (`cls_cpSymPoincare_ne_zero`): the concrete L-group `L_4` is not degenerate.
* `AsymptoticCategory.forgetControl π X : 𝒜_G(X) ⟶ 𝒜_G(pt)` (push-forward to a point) and
  `AsymptoticCategory.toPointInvCat`, as morphisms of `InvCat`, so that `Lconc.map` and `𝕃.map`
  apply; `ControlData.forgetControlT` is the instance `𝒜_G(T) ⟶ 𝒜_G(pt)`.
* `PermRep.karHomologyEquiv`: for an idempotent chain map `e`, the Kar homology `H_r(E, e)` (cycles
  modulo boundaries and `ker e`) is the homology of the subcomplex `im e`, via `[z] ↦ [e z]`;
  `SymPoincare.middleEquiv`: `H^m(C, p) ≅ H_m(im p^*)`.
-/

open CategoryTheory HSFormal.LTheory HSFormal.Compression
open scoped Matrix Kronecker

noncomputable section

/-! ### `FixedData` provides `TailGroups` -/

namespace HSFormal.FixedData

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {M : Type*} [TopologicalSpace M] [AddAction ℤ_[p] M]
  (d : FixedData p n M)

/-- The tail groups `Gᵢ = PadicTail / Kᵢ` (cyclic of order `p^{i+1}`) with the surjections
`πᵢ : Gᵢ → C_p` of `TailGroups.lean`, as the `TailGroups` of `Assembly`. -/
def toTailGroups : TailGroups p d.Cp where
  G := d.G
  π := d.π
  isCyclic _ := inferInstance
  isPGroup i := IsPGroup.of_card (n := i + 1) (d.natCard_G i)
  surjective := d.π_surjective

@[simp] lemma toTailGroups_G : d.toTailGroups.G = d.G := rfl

@[simp] lemma toTailGroups_π (i : ℕ) : d.toTailGroups.π i = d.π i := rfl

/-- The control data carry the same `C_p`. -/
lemma control_Cp : d.control.Cp = d.Cp := rfl

end HSFormal.FixedData

/-! ### Based matrices in `PermRep G S` -/

namespace HSFormal.LTheory.PermRep

open HSFormal.Cubical

section MatReal

variable (G S : Type) [Group G] [MulAction G S] [Fintype S] [DecidableEq S]

/-- The based matrix `A` acting as `A ⊗ 1_S` on `ℚ^{Fin |ι| × S}`. -/
def kronOne {ι κ : Type} [Fintype ι] [Fintype κ] (A : Matrix κ ι ℚ) :
    Matrix (Fin (Fintype.card κ) × S) (Fin (Fintype.card ι) × S) ℚ :=
  A.submatrix (Fintype.equivFin κ).symm (Fintype.equivFin ι).symm ⊗ₖ (1 : Matrix S S ℚ)

omit [Fintype S] in
lemma kronOne_mem {ι κ : Type} [Fintype ι] [Fintype κ] (A : Matrix κ ι ℚ) :
    kronOne S A ∈ homSubmodule (G := G) ⟨Fintype.card ι⟩ ⟨Fintype.card κ⟩ := fun g i s j t ↦ by
  simp [kronOne, Matrix.one_apply]

/-- Based rational matrices act on `PermRep G S` as `A ⊗ 1_S`, compatibly with transposition:
a `MatRealization` of `PermRep.inv G S` (for `S = G`, of `Free(ℚ[G])`). -/
def matRealization : MatRealization (inv G S) where
  obj ι _ := ⟨Fintype.card ι⟩
  mat A := ⟨kronOne S A, kronOne_mem G S A⟩
  mat_add A B := hom_ext (by
    change kronOne S (A + B) = kronOne S A + kronOne S B
    simp [kronOne, Matrix.submatrix_add, Matrix.add_kronecker])
  mat_mul {ι κ μ} _ _ _ A B := hom_ext (by
    change kronOne S (A * B) = kronOne S A * kronOne S B
    simp only [kronOne]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.submatrix_mul_equiv])
  mat_one {ι} _ _ := hom_ext (by
    change kronOne S (1 : Matrix ι ι ℚ) = 1
    simp only [kronOne]
    rw [Matrix.submatrix_one_equiv, Matrix.one_kronecker_one])
  star_mat A := hom_ext (by
    change (kronOne S A)ᵀ = kronOne S Aᵀ
    simp only [kronOne]
    rw [← Matrix.kroneckerMap_transpose, Matrix.transpose_one, Matrix.transpose_submatrix])

end MatReal

/-! ### The cellular `ℂP²` over `PermRep G S` -/

section CP

variable {G S : Type} [Group G] [MulAction G S] [Fintype S] [DecidableEq S]

variable (G S) in
/-- The cellular `ℂP²` (`CPcell.symPoincare`) over `PermRep G S`. -/
abbrev cpSymPoincare : SymPoincare (inv G S) 4 :=
  BasedComplex.CPcell.symPoincare (matRealization G S)

/-- The dual complex `C^{4-*}`. -/
private abbrev cpE : ChainComplex (PermRep G S) ℤ :=
  dualComplex (inv G S) 4 (cpSymPoincare G S).C

private lemma cp_d (r r' : ℤ) : (cpSymPoincare G S).C.d r r' = 0 := by
  change (matRealization G S).mat _ = 0
  simp only [MatRealization.blk, Matrix.submatrix_zero]
  exact (matRealization G S).mat_zero

private lemma cpE_d (r r' : ℤ) : (cpE (G := G) (S := S)).d r r' = 0 := by
  rw [dualComplex_d, cp_d, (inv G S).star_zero, smul_zero]

private lemma cp_mem_cycles (x : ((cpE (G := G) (S := S)).X 2).Sp) : x ∈ cycles cpE 2 := by
  rw [cycles, LinearMap.mem_ker, cpE_d, toLin_zero]

private lemma cp_karBoundaries (x : ((cpE (G := G) (S := S)).X 2).Sp)
    (hx : x ∈ karBoundaries cpE (dualHom (inv G S) 4 (cpSymPoincare G S).p) 2) : x = 0 := by
  obtain ⟨_, ⟨w, rfl⟩, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  have h2 : (dualHom (inv G S) 4 (cpSymPoincare G S).p).f 2 = 𝟙 _ := by
    rw [dualHom_f]
    exact (inv G S).star_id _
  rw [LinearMap.mem_ker, h2, toLin_id] at hz
  rw [cpE_d, hz, toLin_zero, zero_add]

/-- `ℚ^{cells} → H^2`. -/
private def cpF : ((cpE (G := G) (S := S)).X 2).Sp →ₗ[ℚ] (cpSymPoincare G S).middle 2 :=
  (Submodule.mkQ _).comp (LinearMap.id.codRestrict (cycles cpE 2) cp_mem_cycles)

private def cpG : (cpSymPoincare G S).middle 2 →ₗ[ℚ] ((cpE (G := G) (S := S)).X 2).Sp :=
  Submodule.liftQ _ (cycles cpE 2).subtype fun x hx ↦ by
    rw [Submodule.mem_comap] at hx
    rw [LinearMap.mem_ker]
    exact cp_karBoundaries _ hx

private lemma cpG_cpF (x : ((cpE (G := G) (S := S)).X 2).Sp) : cpG (cpF x) = x := rfl

private lemma cpF_surj : Function.Surjective (cpF (G := G) (S := S)) := fun u ↦ by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  exact ⟨x.1, rfl⟩

private lemma cp_comp_id : (cpSymPoincare G S).φ.f 2 ≫
    eqToHom (congrArg (cpSymPoincare G S).C.X (show (2 : ℤ) = 4 - 2 by norm_num)) =
      𝟙 ((cpE (G := G) (S := S)).X 2) := by
  have h1 := BasedComplex.CPcell.symPoincare_φ_middle (matRealization G S)
  have h2 := MatRealization.eqToHom_complex_X (matRealization G S) BasedComplex.CPcell
    (show (2 : ℤ) = 4 - 2 by norm_num)
  erw [h1, h2, ← (matRealization G S).mat_mul]
  rw [MatRealization.blk_mul _ _ (fun κ σ h hσ ↦ by
    obtain rfl : κ = σ := by by_contra h'; exact h (Matrix.one_apply_ne h')
    change _ = _ at hσ ⊢; omega), Matrix.one_mul, MatRealization.blk_one,
    (matRealization G S).mat_one]
  rfl

private lemma cp_pairing (x y : ((cpE (G := G) (S := S)).X 2).Sp) :
    pairing 2 (by norm_num) (cpSymPoincare G S).φ x y = x ⬝ᵥ y := by
  rw [pairing_apply, ← toLin_comp_eq (f_comp_eqToHom (cpSymPoincare G S).φ
    (show (2 : ℤ) = 4 - 2 by norm_num)), ← toLin_comp, cp_comp_id]
  exact congrArg _ (toLin_id y)

/-- The standard form on `ℚ^{cells}`. -/
private def cpB : LinearMap.BilinForm ℚ ((cpE (G := G) (S := S)).X 2).Sp := Matrix.toBilin' 1

private lemma cpB_apply (x y : ((cpE (G := G) (S := S)).X 2).Sp) : cpB x y = x ⬝ᵥ y := by
  simp [cpB, Matrix.toBilin'_apply']

private lemma cp_hf (x y : ((cpE (G := G) (S := S)).X 2).Sp) :
    (cpSymPoincare G S).middleForm 2 (by norm_num) (cpF x) (cpF y) = cpB x y := by
  rw [cpB_apply, ← cp_pairing]; rfl

private lemma cp_card : Fintype.card ((cpE (G := G) (S := S)).X 2).Idx = Fintype.card S := by
  have : ((cpE (G := G) (S := S)).X 2).rank = 1 := rfl
  rw [Fintype.card_prod, Fintype.card_fin, this, one_mul]

private lemma cpB_inv : IsInvariantForm ((cpE (G := G) (S := S)).X 2).act cpB where
  isSymm := ⟨fun x y ↦ by rw [cpB_apply, cpB_apply, dotProduct_comm]⟩
  nondegenerate := Matrix.Nondegenerate.toBilin' (Matrix.nondegenerate_of_det_ne_zero (by simp))
  map_map g x y := by rw [cpB_apply, cpB_apply]; exact dotProduct_act _ g x y

variable [Fintype G]

/-- The ordinary signature of the cellular `ℂP²` over `PermRep G S` is `|S|`: its middle form is
the standard form on `ℚ^{e₂ × S}`. -/
theorem cpSymPoincare_sign₄_one : (cpSymPoincare G S).sign₄ 1 = Fintype.card S := by
  have h := ratEquivariantSignature_eq_of_isometries cpB_inv
    ((cpSymPoincare G S).isInvariantForm_middleForm 2 _ even_two) cpF cpG cp_hf (fun u v ↦ by
      obtain ⟨x, rfl⟩ := cpF_surj u; obtain ⟨y, rfl⟩ := cpF_surj v
      rw [cpG_cpF, cpG_cpF, cp_hf]) (fun σ v ↦ rfl)
  rw [SymPoincare.sign₄, SymPoincare.sign, h, ratEquivariantSignature_one cpB_inv.isSymm
    cpB_inv.nondegenerate cpB_inv.map_map, cpB, BasedComplex.ratSignature_toBilin'_one, cp_card]
  simp

/-- For `S` nonempty the class of the cellular `ℂP²` in `Lconc_4(PermRep G S)` is nonzero. -/
theorem cls_cpSymPoincare_ne_zero [Nonempty S] :
    Lconc.cls (A := invCat G S) (cpSymPoincare G S) ≠ 0 := by
  intro h
  have := congrFun (congrArg sign₄Hom h) 1
  rw [signHom_cls, map_zero] at this
  have h1 : (cpSymPoincare G S).sign 2 (by norm_num) 1 = Fintype.card S :=
    cpSymPoincare_sign₄_one
  rw [h1] at this
  exact Fintype.card_ne_zero (Nat.cast_eq_zero.mp this)

/-- **The final signature-one class** (l. 1093) at the `SymPoincare` level: over
`Free(ℚ) = PermRep Unit Unit` the cellular `ℂP²` has signature `1`. -/
theorem cpSymPoincare_unit_sign₄_one : (cpSymPoincare Unit Unit).sign₄ 1 = 1 := by
  rw [cpSymPoincare_sign₄_one, Fintype.card_unit, Nat.cast_one]

/-- Non-vacuity of `Lconc_4`: the class of the cellular `ℂP²` over `Free(ℚ)` is nonzero. -/
theorem cls_cpSymPoincare_unit_ne_zero :
    Lconc.cls (A := invCat Unit Unit) (cpSymPoincare Unit Unit) ≠ 0 :=
  cls_cpSymPoincare_ne_zero

end CP

end HSFormal.LTheory.PermRep

/-! ### Forgetting control as an `InvCat` morphism -/

namespace HSFormal.AsymptoticCategory

variable {H : Type} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  (π : ∀ i, G i →* H) {X : Type} [MulAction H X] [PseudoEMetricSpace X]
  {Y : Type} [MulAction H Y] [PseudoEMetricSpace Y]

/-- Push-forward along an equivariant uniformly continuous `j : Y → X` (`pushTailInv`) as a
morphism `𝒜_G(Y) ⟶ 𝒜_G(X)` of `InvCat`. -/
def pushTailInvCat {j : Y → X} (hjeq : ∀ (h : H) (y : Y), j (h • y) = h • j y)
    (hj : UniformContinuous j) : asymptoticInvCat π Y ⟶ asymptoticInvCat π X :=
  pushTailInv hjeq hj

@[simp]
lemma pushTailInvCat_F {j : Y → X} (hjeq : ∀ (h : H) (y : Y), j (h • y) = h • j y)
    (hj : UniformContinuous j) :
    (pushTailInvCat π hjeq hj : InvFunctor _ _).F = pushTail hjeq hj := rfl

variable (X) in
/-- **Forget control** `𝒜_G(X) ⟶ 𝒜_G(pt)`: push forward along `X → pt`, keeping the groups. -/
def forgetControl : asymptoticInvCat π X ⟶ asymptoticInvCat π PUnit :=
  pushTailInvCat π (j := fun _ : X ↦ PUnit.unit) (fun _ _ ↦ rfl) uniformContinuous_const

variable (X) in
/-- `toPointInv` (forget the group and push to a point, `𝒜_G(X) → 𝒜_1(pt)`) as an `InvCat`
morphism. -/
def toPointInvCat : asymptoticInvCat π X ⟶ asymptoticInvCat (scalarHom H) PUnit :=
  toPointInv π X

/-- Forgetting control, then the group, is `toPointInv`. -/
lemma forgetControl_comp_forgetInv :
    forgetControl π X ≫ (forgetInv : asymptoticInvCat π PUnit ⟶ _) = toPointInvCat π X :=
  InvCat.hom_ext (CategoryTheory.Quotient.lift_unique' _ _ _ rfl)

/-- `Lconc_N` is functorial along forgetting control. -/
example (N : ℤ) : Lconc (asymptoticInvCat π X) N →+ Lconc (asymptoticInvCat π PUnit) N :=
  Lconc.map (forgetControl π X)

end HSFormal.AsymptoticCategory

namespace HSFormal.ControlData

variable {p : ℕ} (cd : ControlData p) (Γ : TailGroups p cd.Cp)

/-- `𝒜_G(T) ⟶ 𝒜_G(pt)` for the free `C_p`-sphere `T = S^{2m-1} ⊆ ℂ^m` of the control data. -/
abbrev forgetControlT :
    asymptoticInvCat Γ.π (Metric.sphere (0 : EuclideanSpace ℂ (Fin cd.m)) 1) ⟶
      asymptoticInvCat Γ.π PUnit :=
  AsymptoticCategory.forgetControl Γ.π _

end HSFormal.ControlData

/-! ### Kar homology is the homology of the image -/

namespace HSFormal.LTheory.PermRep

variable {G S : Type} [Group G] [MulAction G S] [Fintype S] [DecidableEq S]
  (E : ChainComplex (PermRep G S) ℤ) (e : E ⟶ E) (r : ℤ)

/-- The cycles of the subcomplex `im e`. -/
def imCycles : Submodule ℚ (E.X r).Sp :=
  LinearMap.range (toLin (e.f r)) ⊓ cycles E r

/-- The boundaries `d(e w)` of the subcomplex `im e`. -/
def imBoundaries : Submodule ℚ (E.X r).Sp :=
  LinearMap.range ((toLin (E.d (r + 1) r)).comp (toLin (e.f (r + 1))))

/-- The homology `H_r(im e)` of the subcomplex `im e`. -/
abbrev imHomology : Type :=
  imCycles E e r ⧸ (imBoundaries E e r).comap (imCycles E e r).subtype

variable {E e r}

private lemma toLin_d_e (r' : ℤ) (x : (E.X r).Sp) :
    toLin (E.d r r') (toLin (e.f r) x) = toLin (e.f r') (toLin (E.d r r') x) :=
  toLin_comp_eq (e.comm r r') x

private lemma toLin_e_e (he : e ≫ e = e) (x : (E.X r).Sp) :
    toLin (e.f r) (toLin (e.f r) x) = toLin (e.f r) x := by
  rw [← toLin_comp, ← HomologicalComplex.comp_f, he]

private lemma e_mem_imCycles {x : (E.X r).Sp} (hx : x ∈ cycles E r) :
    toLin (e.f r) x ∈ imCycles E e r := by
  refine ⟨⟨x, rfl⟩, ?_⟩
  rw [cycles, LinearMap.mem_ker] at hx
  change toLin (E.d r (r - 1)) (toLin (e.f r) x) = 0
  rw [toLin_d_e, hx, map_zero]

private lemma e_mem_imBoundaries {x : (E.X r).Sp} (hx : x ∈ karBoundaries E e r) :
    toLin (e.f r) x ∈ imBoundaries E e r := by
  obtain ⟨_, ⟨w, rfl⟩, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  rw [LinearMap.mem_ker] at hz
  rw [map_add, hz, add_zero, ← toLin_d_e]
  exact ⟨w, rfl⟩

private lemma imBoundaries_le : imBoundaries E e r ≤ karBoundaries E e r := by
  rintro _ ⟨w, rfl⟩
  exact Submodule.mem_sup_left ⟨_, rfl⟩

variable (r) in
/-- For an idempotent chain map `e`, the Kar homology `H_r(E, e)` (cycles modulo boundaries and
`ker e`) is the homology of the subcomplex `im e`, via `[z] ↦ [e z]`. -/
def karHomologyEquiv (he : e ≫ e = e) : karHomology E e r ≃ₗ[ℚ] imHomology E e r :=
  LinearEquiv.ofLinear
    (Submodule.mapQ _ _ ((toLin (e.f r)).restrict fun _ hx ↦ e_mem_imCycles hx)
      fun _ hx ↦ e_mem_imBoundaries hx)
    (Submodule.mapQ _ _ (Submodule.inclusion inf_le_right) fun _ hx ↦ imBoundaries_le hx)
    (Submodule.linearMap_qext _ (LinearMap.ext fun y ↦ congrArg Submodule.Quotient.mk
      (Subtype.ext (by
        obtain ⟨w, hw⟩ := y.2.1
        change toLin (e.f r) y.1 = y.1
        rw [← hw, toLin_e_e he]))))
    (Submodule.linearMap_qext _ (LinearMap.ext fun x ↦ (Submodule.Quotient.eq _).mpr
      (Submodule.mem_sup_right (by
        change toLin (e.f r) (toLin (e.f r) x.1 - x.1) = 0
        rw [map_sub, toLin_e_e he, sub_self]))))

@[simp]
lemma karHomologyEquiv_mk (he : e ≫ e = e) (x : cycles E r) :
    karHomologyEquiv r he (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨toLin (e.f r) x, e_mem_imCycles x.2⟩ := rfl

end HSFormal.LTheory.PermRep

namespace HSFormal.LTheory.SymPoincare

open PermRep

variable {G S : Type} [Group G] [MulAction G S] [Fintype S] [DecidableEq S] {N : ℤ}
  (P : SymPoincare (inv G S) N) (m : ℤ)

/-- The middle `H^m(C, p)` (cycles of `C^{N-*}` modulo boundaries and `ker p^*`) is the homology
`H_m(im p^*)` of the image of `p^*`, via `[z] ↦ [p^* z]`. -/
def middleEquiv : P.middle m ≃ₗ[ℚ]
    imHomology (dualComplex (inv G S) N P.C) (dualHom (inv G S) N P.p) m :=
  karHomologyEquiv m (by rw [← dualHom_comp, P.p_idem])

end HSFormal.LTheory.SymPoincare
