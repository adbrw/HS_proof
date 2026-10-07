import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
import Mathlib.Algebra.Polynomial.Module.TensorProduct
import Mathlib.RepresentationTheory.Maschke
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Category.Ring.Basic

/-!
# Theorem R, part 1: projective dimension bounds (NegKHigh module N9, `RegPd`)

`blueprint/negK-high.md` §4, steps (R1) and (R2).

We work with unbundled modules in the universe of the ring and write `PdLE R M d` for mathlib's
`HasProjectiveDimensionLE (ModuleCat.of R M) d`, and `GlobalDimLE R d` for "every module has
`pd ≤ d`".

* Short exact sequence calculus (`pdLE_ker`, `pdLE_of_ker`), invariance under linear
  equivalences and ring isomorphisms (`GlobalDimLE.of_ringEquiv`).
* **(R2) Maschke averaging** over a commutative `k` with `|G|` invertible:
  `projective_monoidAlgebra` (`k`-projective `k[G]`-modules are `k[G]`-projective, by averaging
  a `k`-linear section with mathlib's `equivariantProjection`), `pdLE_monoidAlgebra`
  (`pd_{k[G]} M ≤ pd_k M`) and `GlobalDimLE.monoidAlgebra`.
* Flat base change does not increase `pd` (`pdLE_baseChange`).
* **(R1) The polynomial step** `pdLE_polynomial`: `pd_{A[X]} N ≤ pd_A N + 1`, from the canonical
  sequence `0 → N[X] → N[X] → N → 0` (`canD`, `canE`, `canD_injective`, `range_canD`) with
  `N[X] = PolynomialModule A N ≅ A[X] ⊗[A] N`. Hence `GlobalDimLE.polynomial`.
* Localization (`GlobalDimLE.localization`, via mathlib's
  `localizedModule_hasProjectiveDimensionLE`) and Laurent extensions (`GlobalDimLE.laurent`).
* `lpComm n A`: the `n`-fold Laurent extension with the newest variable innermost (the recursion
  of `Lpow`), and the conclusion of (R1)+(R2):
  `globalDimLE_lpComm_polynomial_monoidAlgebra : GlobalDimLE (C[G]) (n + 1)` for
  `C = lpComm n (K[X])`, `K` a field with `|G| ≠ 0` in `K`.
-/

open CategoryTheory

namespace HSFormal.LTheory.Reg

universe u

section Pd

variable (R : Type u) [Ring R]

/-- `pd_R M ≤ d` for an unbundled module `M` in the universe of `R`. -/
abbrev PdLE (M : Type u) [AddCommGroup M] [Module R M] (d : ℕ) : Prop :=
  HasProjectiveDimensionLE (ModuleCat.of R M) d

/-- Global dimension `≤ d`: every module (in the universe of `R`) has `pd ≤ d`. -/
def GlobalDimLE (d : ℕ) : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module R M], PdLE R M d

variable {R}
variable {M N P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

lemma pdLE_zero_iff : PdLE R M 0 ↔ Module.Projective R M := by
  rw [IsProjective.iff_projective, projective_iff_hasProjectiveDimensionLT_one]

lemma pdLE_zero_of_projective [Module.Projective R M] : PdLE R M 0 := pdLE_zero_iff.2 ‹_›

lemma PdLE.projective (h : PdLE R M 0) : Module.Projective R M := pdLE_zero_iff.1 h

lemma PdLE.mono {d d' : ℕ} (h : PdLE R M d) (hd : d ≤ d') : PdLE R M d' :=
  hasProjectiveDimensionLT_of_ge _ (d + 1) (d' + 1) (by omega)

lemma pdLE_of_projective [Module.Projective R M] (d : ℕ) : PdLE R M d :=
  (pdLE_zero_of_projective (M := M)).mono (Nat.zero_le d)

lemma PdLE.of_equiv {d : ℕ} (e : M ≃ₗ[R] N) (h : PdLE R M d) : PdLE R N d :=
  ModuleCat.hasProjectiveDimensionLE_of_linearEquiv (M := ModuleCat.of R M) (N := ModuleCat.of R N) e d

/-- Kernel of a surjection with middle term of `pd ≤ d`: `pd ker ≤ d` when `pd M ≤ d + 1`. -/
lemma pdLE_ker {d : ℕ} (f : P →ₗ[R] M) (hf : Function.Surjective f) (hP : PdLE R P d)
    (hM : PdLE R M (d + 1)) : PdLE R (LinearMap.ker f) d :=
  (LinearMap.shortExact_shortComplexKer hf).hasProjectiveDimensionLT_X₁ (d + 1) hP hM

/-- `pd M ≤ d + 1` from a surjection `P ↠ M` with `pd P ≤ d + 1` and `pd ker ≤ d`. -/
lemma pdLE_of_ker {d : ℕ} (f : P →ₗ[R] M) (hf : Function.Surjective f)
    (hK : PdLE R (LinearMap.ker f) d) (hP : PdLE R P (d + 1)) : PdLE R M (d + 1) :=
  (LinearMap.shortExact_shortComplexKer hf).hasProjectiveDimensionLT_X₃ (d + 1) hK hP

end Pd


section Transfer

variable {R R' : Type u} [Ring R] [Ring R']

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- Global dimension is invariant under ring isomorphisms. -/
lemma GlobalDimLE.of_ringEquiv {d : ℕ} (e : R ≃+* R') (h : GlobalDimLE R d) :
    GlobalDimLE R' d := by
  intro N _ _
  let : Module R N := Module.compHom N e.toRingHom
  let e' : (ModuleCat.of R N) ≃ₛₗ[RingHomClass.toRingHom e] (ModuleCat.of R' N) :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have := h N
  exact ModuleCat.hasProjectiveDimensionLE_of_semiLinearEquiv.{u, u} e e' d

/-- Division rings have global dimension `0`. -/
lemma globalDimLE_zero_of_divisionRing (K : Type u) [DivisionRing K] : GlobalDimLE K 0 :=
  fun _ _ _ ↦ pdLE_zero_of_projective

end Transfer


section Maschke

open MonoidAlgebra

variable {k : Type u} [CommRing k] {G : Type u} [Group G] [Fintype G]

/-- **Maschke averaging** (projective form): a `k[G]`-module which is `k`-projective is
`k[G]`-projective, when `|G|` is invertible in `k`. -/
lemma projective_monoidAlgebra (hG : IsUnit (Nat.card G : k))
    (M : Type u) [AddCommGroup M] [Module k M] [Module (MonoidAlgebra k G) M]
    [IsScalarTower k (MonoidAlgebra k G) M] [Module.Projective k M] :
    Module.Projective (MonoidAlgebra k G) M := by
  let s : (M →₀ MonoidAlgebra k G) →ₗ[MonoidAlgebra k G] M := Finsupp.linearCombination _ id
  have hs : Function.Surjective s := Finsupp.linearCombination_surjective _ Function.surjective_id
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property (s.restrictScalars k) LinearMap.id hs
  refine Module.Projective.of_split (σ.equivariantProjection G) s ?_
  ext m
  have hc : ∀ g : G, s (σ.conjugate g m) = m := by
    intro g
    rw [LinearMap.conjugate_apply, LinearMap.map_smul]
    have := congrArg (fun f ↦ f (MonoidAlgebra.single g (1 : k) • m)) hσ
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
      LinearMap.id_apply] at this
    rw [this, ← mul_smul, single_mul_single, mul_one, inv_mul_cancel, ← one_def, one_smul]
  rw [LinearMap.coe_comp, Function.comp_apply, LinearMap.equivariantProjection_apply,
    LinearMap.map_smul_of_tower, map_sum]
  simp only [hc, Finset.sum_const, Finset.card_univ, LinearMap.id_apply]
  rw [← Nat.cast_smul_eq_nsmul k, smul_smul, Fintype.card_eq_nat_card,
    Ring.inverse_mul_cancel _ hG, one_smul]


/-- The kernel of a `k[G]`-linear map, seen `k`-linearly. -/
def kerRestrictScalarsEquiv {M N : Type u} [AddCommGroup M] [Module k M]
    [Module (MonoidAlgebra k G) M] [IsScalarTower k (MonoidAlgebra k G) M] [AddCommGroup N]
    [Module k N] [Module (MonoidAlgebra k G) N] [IsScalarTower k (MonoidAlgebra k G) N]
    (f : M →ₗ[MonoidAlgebra k G] N) :
    LinearMap.ker (f.restrictScalars k) ≃ₗ[k] LinearMap.ker f where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Maschke averaging** (dimension form): `pd_{k[G]} M ≤ pd_k M`. -/
lemma pdLE_monoidAlgebra (hG : IsUnit (Nat.card G : k)) (d : ℕ) :
    ∀ (M : Type u) [AddCommGroup M] [Module k M] [Module (MonoidAlgebra k G) M]
      [IsScalarTower k (MonoidAlgebra k G) M], PdLE k M d → PdLE (MonoidAlgebra k G) M d := by
  induction d with
  | zero =>
    intro M _ _ _ _ hM
    have := hM.projective
    exact pdLE_zero_iff.2 (projective_monoidAlgebra hG M)
  | succ d ih =>
    intro M _ _ _ _ hM
    let s : (M →₀ MonoidAlgebra k G) →ₗ[MonoidAlgebra k G] M := Finsupp.linearCombination _ id
    have hs : Function.Surjective s :=
      Finsupp.linearCombination_surjective _ Function.surjective_id
    have hK : PdLE k (LinearMap.ker (s.restrictScalars k)) d :=
      pdLE_ker (s.restrictScalars k) hs (pdLE_of_projective _) hM
    exact pdLE_of_ker s hs (ih _ (hK.of_equiv (kerRestrictScalarsEquiv s)))
      (pdLE_of_projective _)

/-- **Maschke averaging** (global form): `gldim k[G] ≤ gldim k`. -/
lemma GlobalDimLE.monoidAlgebra (hG : IsUnit (Nat.card G : k)) {d : ℕ} (h : GlobalDimLE k d) :
    GlobalDimLE (MonoidAlgebra k G) d := by
  intro M _ _
  let : Module k M := Module.compHom M (algebraMap k (MonoidAlgebra k G))
  have : IsScalarTower k (MonoidAlgebra k G) M :=
    ⟨fun r s m ↦ by
      change (r • s) • m = algebraMap k (MonoidAlgebra k G) r • (s • m)
      rw [Algebra.smul_def, mul_smul]⟩
  exact pdLE_monoidAlgebra hG d M (h M)

end Maschke


section BaseChange

open TensorProduct

variable {A : Type u} [CommRing A] (B : Type u) [CommRing B] [Algebra A B] [Module.Flat A B]

/-- The inductive step of `pdLE_baseChange`, for a projective cover `f : P ↠ M`. -/
lemma pdLE_baseChange_of_ker {d : ℕ} {M P : Type u} [AddCommGroup M] [Module A M] [AddCommGroup P]
    [Module A P] [Module.Projective A P] (f : P →ₗ[A] M) (hf : Function.Surjective f)
    (hK : PdLE B (B ⊗[A] LinearMap.ker f) d) : PdLE B (B ⊗[A] M) (d + 1) := by
  let g : B ⊗[A] P →ₗ[B] B ⊗[A] M := f.baseChange B
  have hg : Function.Surjective g := LinearMap.lTensor_surjective B hf
  let i : B ⊗[A] LinearMap.ker f →ₗ[B] B ⊗[A] P := (LinearMap.ker f).subtype.baseChange B
  have hi : Function.Injective i :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (LinearMap.ker f).injective_subtype
  have hex : Function.Exact i g := lTensor_exact B (LinearMap.exact_subtype_ker_map f) hf
  let e : B ⊗[A] LinearMap.ker f ≃ₗ[B] LinearMap.ker g :=
    (LinearEquiv.ofInjective i hi).trans (LinearEquiv.ofEq _ _ hex.linearMap_ker_eq.symm)
  exact pdLE_of_ker g hg (hK.of_equiv e) (pdLE_of_projective _)

/-- Flat base change does not increase projective dimension. -/
lemma pdLE_baseChange (d : ℕ) :
    ∀ (M : Type u) [AddCommGroup M] [Module A M], PdLE A M d → PdLE B (B ⊗[A] M) d := by
  induction d with
  | zero =>
    intro M _ _ hM
    have := hM.projective
    exact pdLE_zero_of_projective
  | succ d ih =>
    intro M _ _ hM
    let f : (M →₀ A) →ₗ[A] M := Finsupp.linearCombination A id
    have hf : Function.Surjective f :=
      Finsupp.linearCombination_surjective _ Function.surjective_id
    exact pdLE_baseChange_of_ker B f hf (ih _ (pdLE_ker f hf (pdLE_of_projective _) hM))

end BaseChange


section Polynomial

open Polynomial TensorProduct PolynomialModule

variable (A : Type u) [CommRing A] (N : Type u) [AddCommGroup N]

omit [CommRing A] in
lemma PolynomialModule.coeff_sub' [CommRing A] [Module A N] (x y : PolynomialModule A N) :
    (x - y).coeff = x.coeff - y.coeff := rfl

lemma X_pow_smul_single [Module A N] (k : ℕ) (n : N) :
    (X : A[X]) ^ k • single A 0 n = single A k n := by
  rw [← Polynomial.monomial_one_right_eq_X_pow, monomial_smul_single, add_zero, one_smul]

lemma X_smul_single [Module A N] (k : ℕ) (n : N) :
    (X : A[X]) • single A k n = single A (k + 1) n := by
  rw [← pow_one (X : A[X]), ← Polynomial.monomial_one_right_eq_X_pow, monomial_smul_single,
    one_smul, add_comm]

lemma coeff_X_smul_succ [Module A N] (x : PolynomialModule A N) (j : ℕ) :
    ((X : A[X]) • x).coeff (j + 1) = x.coeff j := by
  rw [← pow_one (X : A[X]), ← Polynomial.monomial_one_right_eq_X_pow, monomial_smul_apply]
  simp

variable [Module A[X] N] [Module A N] [IsScalarTower A A[X] N]

/-- The coefficientwise action of `X`, `(n_k) ↦ (X • n_k)`, on `N[X] = PolynomialModule A N`. -/
noncomputable def coeffX : PolynomialModule A N →ₗ[A[X]] PolynomialModule A N where
  toFun := PolynomialModule.map A ((LinearMap.lsmul A[X] N X).restrictScalars A)
  map_add' := map_add _
  map_smul' p q := by
    rw [PolynomialModule.map_smul, Algebra.algebraMap_self, Polynomial.map_id]
    rfl

lemma coeffX_single (k : ℕ) (n : N) :
    coeffX A N (single A k n) = single A k ((X : A[X]) • n) := by
  simp [coeffX]

lemma coeff_coeffX (x : PolynomialModule A N) (j : ℕ) :
    (coeffX A N x).coeff j = (X : A[X]) • x.coeff j :=
  rfl

/-- The first map `(n_k) ↦ (n_{k-1} - X • n_k)` of the canonical sequence
`0 → N[X] → N[X] → N → 0`. -/
noncomputable def canD : PolynomialModule A N →ₗ[A[X]] PolynomialModule A N :=
  (X : A[X]) • LinearMap.id - coeffX A N

/-- The second map `(n_k) ↦ ∑ X^k • n_k` of the canonical sequence. -/
noncomputable def canE : PolynomialModule A N →ₗ[A[X]] N :=
  (LinearMap.liftBaseChange A[X] (LinearMap.id : N →ₗ[A] N)) ∘ₗ
    (polynomialTensorProductLEquivPolynomialModule A N).symm.toLinearMap

lemma canE_single (k : ℕ) (n : N) : canE A N (single A k n) = (X : A[X]) ^ k • n := by
  have h : (polynomialTensorProductLEquivPolynomialModule A N).symm (single A k n) =
      ((X : A[X]) ^ k) ⊗ₜ[A] n := by
    rw [LinearEquiv.symm_apply_eq]
    symm
    change LinearMap.liftBaseChange A[X] (lsingle A 0 (M := N)) (((X : A[X]) ^ k) ⊗ₜ[A] n) = _
    rw [LinearMap.liftBaseChange_tmul]
    exact X_pow_smul_single A N k n
  simp [canE, h]

lemma canD_single (k : ℕ) (n : N) :
    canD A N (single A k n) = single A (k + 1) n - single A k ((X : A[X]) • n) := by
  simp only [canD, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, coeffX_single,
    X_smul_single]

lemma canD_coeff_succ (x : PolynomialModule A N) (j : ℕ) :
    (canD A N x).coeff (j + 1) = x.coeff j - (X : A[X]) • x.coeff (j + 1) := by
  simp only [canD, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
  rw [PolynomialModule.coeff_sub', Finsupp.sub_apply, coeff_X_smul_succ, coeff_coeffX]

lemma canE_canD (x : PolynomialModule A N) : canE A N (canD A N x) = 0 := by
  induction x using PolynomialModule.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | single k n =>
    rw [canD_single, map_sub, canE_single, canE_single, pow_succ, mul_smul, sub_self]

lemma sub_single_canE_mem (x : PolynomialModule A N) :
    x - single A 0 (canE A N x) ∈ LinearMap.range (canD A N) := by
  induction x using PolynomialModule.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, single_add, add_sub_add_comm]
    exact Submodule.add_mem _ hx hy
  | single k n =>
    induction k generalizing n with
    | zero => simp [canE_single]
    | succ k ih =>
      have h := Submodule.add_mem _ (LinearMap.mem_range_self (canD A N) (single A k n))
        (ih ((X : A[X]) • n))
      rw [canD_single, canE_single, ← mul_smul, ← pow_succ] at h
      rw [canE_single]
      convert h using 1
      abel

lemma canD_injective : Function.Injective (canD A N) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have hrec : ∀ j, x.coeff j = (X : A[X]) • x.coeff (j + 1) := fun j ↦ by
    have := canD_coeff_succ A N x j
    rw [hx, PolynomialModule.coeff_zero, Finsupp.zero_apply] at this
    exact sub_eq_zero.mp this.symm
  have hpow : ∀ m j, x.coeff j = (X : A[X]) ^ m • x.coeff (j + m) := by
    intro m
    induction m with
    | zero => intro j; simp
    | succ m ih =>
      intro j
      rw [ih j, hrec (j + m), ← mul_smul, ← pow_succ, add_assoc]
  rw [← coeff_eq_zero]
  ext j
  rw [hpow (x.coeff.support.sup id + 1) j, Finsupp.zero_apply]
  have : x.coeff (j + (x.coeff.support.sup id + 1)) = 0 := by
    rw [← Finsupp.notMem_support_iff]
    intro hmem
    have := Finset.le_sup (f := id) hmem
    simp only [id] at this
    omega
  rw [this, smul_zero]

lemma range_canD : LinearMap.range (canD A N) = LinearMap.ker (canE A N) := by
  refine le_antisymm ?_ fun x hx ↦ ?_
  · rintro _ ⟨x, rfl⟩
    exact canE_canD A N x
  · have := sub_single_canE_mem A N x
    rwa [LinearMap.mem_ker.mp hx, single_zero, sub_zero] at this

lemma canE_surjective : Function.Surjective (canE A N) := fun n ↦
  ⟨single A 0 n, by rw [canE_single, pow_zero, one_smul]⟩

/-- **The polynomial step**: `pd_{A[X]} N ≤ pd_A N + 1`, by the canonical sequence
`0 → N[X] → N[X] → N → 0` and flat base change `pd_{A[X]} N[X] ≤ pd_A N`. -/
lemma pdLE_polynomial {d : ℕ} (hN : PdLE A N d) : PdLE A[X] N (d + 1) := by
  have h₂ : PdLE A[X] (PolynomialModule A N) d :=
    (pdLE_baseChange A[X] d N hN).of_equiv (polynomialTensorProductLEquivPolynomialModule A N)
  let e : PolynomialModule A N ≃ₗ[A[X]] LinearMap.ker (canE A N) :=
    (LinearEquiv.ofInjective (canD A N) (canD_injective A N)).trans
      (LinearEquiv.ofEq _ _ (range_canD A N))
  exact pdLE_of_ker (canE A N) (canE_surjective A N) (h₂.of_equiv e) (h₂.mono (Nat.le_succ d))

variable {A} in
omit N in
/-- `gldim A[X] ≤ gldim A + 1`. -/
lemma GlobalDimLE.polynomial {d : ℕ} (h : GlobalDimLE A d) : GlobalDimLE A[X] (d + 1) := by
  intro N _ _
  let : Module A N := Module.compHom N (algebraMap A A[X])
  have : IsScalarTower A A[X] N :=
    ⟨fun r s m ↦ by
      change (r • s) • m = algebraMap A A[X] r • (s • m)
      rw [Algebra.smul_def, mul_smul]⟩
  exact pdLE_polynomial A N (h N)

end Polynomial


section Localization

variable {A : Type u} [CommRing A]

/-- Localization does not increase global dimension. -/
lemma GlobalDimLE.localization {d : ℕ} (h : GlobalDimLE A d) (S : Submonoid A) :
    GlobalDimLE (Localization S) d := by
  intro N _ _
  let : Module A N := Module.compHom N (algebraMap A (Localization S))
  have : IsScalarTower A (Localization S) N :=
    ⟨fun r s m ↦ by
      change (r • s) • m = algebraMap A (Localization S) r • (s • m)
      rw [Algebra.smul_def, mul_smul]⟩
  have := h N
  have h1 := ModuleCat.localizedModule_hasProjectiveDimensionLE d S (ModuleCat.of A N)
  have hl : IsLocalizedModule S (LinearMap.id : N →ₗ[A] N) :=
    isLocalizedModule_id S N (Localization S)
  have := ModuleCat.localizedModule_isLocalizedModule (ModuleCat.of A N) S
  let e : N ≃ₗ[Localization S] ((ModuleCat.of A N).localizedModule S) :=
    LinearEquiv.extendScalarsOfIsLocalization S (Localization S)
      (IsLocalizedModule.linearEquiv S LinearMap.id
        ((ModuleCat.of A N).localizedModuleMkLinearMap S))
  exact PdLE.of_equiv e.symm h1

/-- `gldim A[T;T⁻¹] ≤ gldim A + 1`. -/
lemma GlobalDimLE.laurent {d : ℕ} (h : GlobalDimLE A d) :
    GlobalDimLE (LaurentPolynomial A) (d + 1) :=
  (h.polynomial.localization (Submonoid.powers (Polynomial.X : Polynomial A))).of_ringEquiv
    (IsLocalization.algEquiv (Submonoid.powers (Polynomial.X : Polynomial A))
      (Localization.Away (Polynomial.X : Polynomial A)) (LaurentPolynomial A)).toRingEquiv

end Localization


section Iterate

/-- The `n`-fold Laurent extension of a commutative ring, with the **newest variable
innermost**: `lpComm 0 A = A`, `lpComm (n + 1) A = lpComm n (A[T;T⁻¹])` (the recursion of
`Lpow`). -/
noncomputable def lpComm : ℕ → CommRingCat.{u} → CommRingCat.{u}
  | 0, A => A
  | n + 1, A => lpComm n (CommRingCat.of (LaurentPolynomial A))

lemma lpComm_zero (A : CommRingCat.{u}) : lpComm 0 A = A := rfl

lemma lpComm_succ (n : ℕ) (A : CommRingCat.{u}) :
    lpComm (n + 1) A = lpComm n (CommRingCat.of (LaurentPolynomial A)) := rfl

/-- The constants `A →+* lpComm n A`. -/
noncomputable def lpCommC : ∀ (n : ℕ) (A : CommRingCat.{u}), A →+* lpComm n A
  | 0, _ => RingHom.id _
  | n + 1, A => (lpCommC n (CommRingCat.of (LaurentPolynomial A))).comp LaurentPolynomial.C

/-- `gldim (lpComm n A) ≤ gldim A + n`. -/
lemma GlobalDimLE.lpComm : ∀ (n : ℕ) {A : CommRingCat.{u}} {d : ℕ}, GlobalDimLE A d →
    GlobalDimLE (lpComm n A) (d + n)
  | 0, _, _, h => h
  | n + 1, _, d, h => by
    have := GlobalDimLE.lpComm n (A := CommRingCat.of (LaurentPolynomial _)) h.laurent
    rwa [Nat.add_right_comm, add_assoc] at this

/-- **(R1)** `C = lpComm n (K[X])` has global dimension `≤ n + 1`, for a field `K`. -/
lemma globalDimLE_lpComm_polynomial (K : Type u) [Field K] (n : ℕ) :
    GlobalDimLE (lpComm n (CommRingCat.of (Polynomial K))) (n + 1) := by
  have := GlobalDimLE.lpComm n (A := CommRingCat.of (Polynomial K))
    (globalDimLE_zero_of_divisionRing K).polynomial
  rwa [zero_add, add_comm] at this

/-- **(R1) + (R2)** `S = C[G]`, `C = lpComm n (K[X])`, has global dimension `≤ n + 1` when
`|G|` is invertible in the field `K`. -/
lemma globalDimLE_lpComm_polynomial_monoidAlgebra (K : Type u) [Field K] (G : Type u) [Group G]
    [Fintype G] [NeZero (Nat.card G : K)] (n : ℕ) :
    GlobalDimLE (MonoidAlgebra (lpComm n (CommRingCat.of (Polynomial K))) G) (n + 1) := by
  refine (globalDimLE_lpComm_polynomial K n).monoidAlgebra ?_
  have : IsUnit (Nat.card G : K) := (NeZero.ne _).isUnit
  simpa using (this.map (Polynomial.C : K →+* Polynomial K)).map
    (lpCommC n (CommRingCat.of (Polynomial K)))

end Iterate

end HSFormal.LTheory.Reg
