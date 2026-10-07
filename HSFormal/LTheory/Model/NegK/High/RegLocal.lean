import HSFormal.LTheory.Model.NegK.High.RegNoeth
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Theorem R, part 3: localization at a central element and Theorem R (N11, `RegLocal`)

`blueprint/negK-high.md` §4, steps (R5)–(R7), and Theorem R in module form.

**Deviation from the blueprint (and from the review's fix G3).**  We never build a module
structure over `S′ = C′[G]` on `LocalizedModule`.  Instead we axiomatize the localization of a
(noncommutative) ring at a central element, `IsCentralLoc ι w` for `ι : S →+* S′`, and the
localization of modules as a property of a `ι`-semilinear map, `IsLocMap ι w ℓ` for
`ℓ : M →ₛₗ[ι] M′` (surjective up to powers of `ι w`, kernel = `w`-torsion).  Every localized
module that occurs is concrete: `S′^k` (`isLocMap_piMap`), kernels (`IsLocMap.kerRestrict`:
localization is left exact; `surjective_of_isLocMap`: right exact), products
(`IsLocMap.prod`), and the lattice quotient `S^k/N → P` (`exists_lattice`, (R6)).  Localizations
are unique up to `S′`-linear isomorphism (`locEquiv`).  Projectivity of the localized terms is
never needed separately: it follows from the splitting `F′ ≅ K′ × M′`.

* `stable_of_isLocMap`: the induction (R4)+(R7) (resolution, localize, split from the left).
* **`theoremR_abstract`**: for `S` left noetherian of finite global dimension and `ι : S → S′`
  the localization at a central `w`, every finitely generated projective `S′`-module `P`
  satisfies `P ⊕ Q₁[w⁻¹] ≅ Q₀[w⁻¹]` with `Q₀, Q₁` finitely generated projective over `S`
  (bundled with their localizations as `LocProj ι w`).
* `lpRing n R` (iterated Laurent extension, newest variable innermost), `faceMap n R :
  lpRing n (R[X]) →+* lpRing (n + 1) R` and `isCentralLoc_faceMap`: the face map is the
  localization at the central innermost variable (`isCentralLoc_toLaurent`,
  `IsCentralLoc.laurent`: Laurent extensions preserve central localizations).

The concrete instance (noetherianity and global dimension of `lpRing n (K[G][X])` through the
ring isomorphism with `C[G]`) and the matrix form are in `RegMatrix`.
-/

open CategoryTheory

namespace HSFormal.LTheory.Reg

universe u

section CentralLoc

variable {S S' : Type u} [Ring S] [Ring S']

/-- `ι : S → S'` is the localization of the (noncommutative) ring `S` at the powers of a
central element `w`: `ι w` is a unit, every element of `S'` is `ι(w)⁻ⁿ ι(s)`, and
`ι s = 0` iff `wⁿ s = 0` for some `n`. -/
structure IsCentralLoc (ι : S →+* S') (w : S) : Prop where
  comm : ∀ s, w * s = s * w
  isUnit : IsUnit (ι w)
  surj : ∀ s' : S', ∃ (s : S) (n : ℕ), ι w ^ n * s' = ι s
  ker : ∀ s, ι s = 0 → ∃ n : ℕ, w ^ n * s = 0

variable {ι : S →+* S'} {w : S}

namespace IsCentralLoc

variable (hι : IsCentralLoc ι w)
include hι

lemma comm' (s' : S') : ι w * s' = s' * ι w := by
  obtain ⟨s, n, hs⟩ := hι.surj s'
  have h1 : ι w * ι s = ι s * ι w := by rw [← map_mul, ← map_mul, hι.comm]
  have h2 : ι w ^ n * (ι w * s') = ι w ^ n * (s' * ι w) := by
    rw [← mul_assoc, ← pow_succ, pow_succ', mul_assoc, hs, h1, ← hs, mul_assoc]
  exact (hι.isUnit.pow n).mul_left_cancel h2

lemma commute_pow (n : ℕ) (s' : S') : Commute (ι w ^ n) s' :=
  Commute.pow_left (hι.comm' s') n

/-- `ι w ^ n • (s' • x) = s' • (ι w ^ n • x)`. -/
lemma pow_smul_comm {M : Type*} [AddCommGroup M] [Module S' M] (n : ℕ) (s' : S') (x : M) :
    ι w ^ n • s' • x = s' • ι w ^ n • x := by
  rw [← mul_smul, ← mul_smul, (hι.commute_pow n s').eq]

lemma pow_smul_eq_zero {M : Type*} [AddCommGroup M] [Module S' M] {n : ℕ} {x : M}
    (h : ι w ^ n • x = 0) : x = 0 :=
  ((hι.isUnit.pow n).smul_eq_zero).mp h

end IsCentralLoc

end CentralLoc

section LocMap

variable {S S' : Type u} [Ring S] [Ring S'] {ι : S →+* S'} {w : S}
variable {M M' : Type*} [AddCommGroup M] [Module S M] [AddCommGroup M'] [Module S' M']

variable (ι w) in
/-- `ℓ : M → M'` (`ι`-semilinear, `M'` an `S'`-module) exhibits `M'` as the localization
`M[w⁻¹]`: every element of `M'` is `ι(w)⁻ⁿ ℓ(m)`, and the kernel of `ℓ` is the `w`-torsion. -/
structure IsLocMap (ℓ : M →ₛₗ[ι] M') : Prop where
  surj : ∀ m' : M', ∃ (m : M) (n : ℕ), ι w ^ n • m' = ℓ m
  ker : ∀ m : M, ℓ m = 0 → ∃ n : ℕ, w ^ n • m = 0

lemma map_pow_smul (ℓ : M →ₛₗ[ι] M') (n : ℕ) (m : M) : ℓ (w ^ n • m) = ι w ^ n • ℓ m := by
  rw [LinearMap.map_smulₛₗ, map_pow]

namespace IsLocMap

/-- Precomposition with an `S`-linear equivalence. -/
lemma comp_equiv {N : Type*} [AddCommGroup N] [Module S N] {ℓ : M →ₛₗ[ι] M'}
    (h : IsLocMap ι w ℓ) (e : N ≃ₗ[S] M) : IsLocMap ι w (ℓ.comp e.toLinearMap) := by
  refine ⟨fun m' ↦ ?_, fun n hn ↦ ?_⟩
  · obtain ⟨m, k, hm⟩ := h.surj m'
    exact ⟨e.symm m, k, by simp [hm]⟩
  · obtain ⟨k, hk⟩ := h.ker (e n) hn
    exact ⟨k, by rw [← map_smul, LinearEquiv.map_eq_zero_iff] at hk; exact hk⟩

/-- Postcomposition with an `S'`-linear equivalence. -/
lemma equiv_comp {N' : Type*} [AddCommGroup N'] [Module S' N'] {ℓ : M →ₛₗ[ι] M'}
    (h : IsLocMap ι w ℓ) (e : M' ≃ₗ[S'] N') : IsLocMap ι w (e.toLinearMap.comp ℓ) := by
  refine ⟨fun n' ↦ ?_, fun m hm ↦ h.ker m ?_⟩
  · obtain ⟨m, k, hm⟩ := h.surj (e.symm n')
    exact ⟨m, k, by rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ← hm, map_smul,
      LinearEquiv.apply_symm_apply]⟩
  · simpa using hm

end IsLocMap

/-! ### Constructions of localizations -/

variable (ι) in
/-- Coefficientwise `ι` on a finite free module, `S^α → S'^α`. -/
def piMap (α : Type*) : (α → S) →ₛₗ[ι] (α → S') where
  toFun x i := ι (x i)
  map_add' _ _ := funext fun _ ↦ map_add ι _ _
  map_smul' _ _ := funext fun _ ↦ map_mul ι _ _

@[simp] lemma piMap_apply (α : Type*) (x : α → S) (i : α) : piMap ι α x i = ι (x i) := rfl

/-- The product of two semilinear maps. -/
def prodMapₛₗ {N N' : Type*} [AddCommGroup N] [Module S N] [AddCommGroup N'] [Module S' N']
    (ℓ₁ : M →ₛₗ[ι] M') (ℓ₂ : N →ₛₗ[ι] N') : M × N →ₛₗ[ι] M' × N' where
  toFun x := (ℓ₁ x.1, ℓ₂ x.2)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

@[simp] lemma prodMapₛₗ_apply {N N' : Type*} [AddCommGroup N] [Module S N] [AddCommGroup N']
    [Module S' N'] (ℓ₁ : M →ₛₗ[ι] M') (ℓ₂ : N →ₛₗ[ι] N') (x : M × N) :
    prodMapₛₗ ℓ₁ ℓ₂ x = (ℓ₁ x.1, ℓ₂ x.2) := rfl

variable (hι : IsCentralLoc ι w)
include hι

/-- `S^α → S'^α` is a localization. -/
lemma isLocMap_piMap (α : Type*) [Fintype α] : IsLocMap ι w (piMap ι α) := by
  classical
  refine ⟨fun x' ↦ ?_, fun x hx ↦ ?_⟩
  · choose s n hs using fun i ↦ hι.surj (x' i)
    refine ⟨fun i ↦ w ^ (∑ j, n j - n i) * s i, ∑ j, n j, funext fun i ↦ ?_⟩
    have hle : n i ≤ ∑ j, n j := Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ i)
    simp only [Pi.smul_apply, smul_eq_mul, piMap_apply, map_mul, map_pow]
    rw [← hs i, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  · choose n hn using fun i ↦ hι.ker (x i) (congrFun hx i)
    refine ⟨∑ j, n j, funext fun i ↦ ?_⟩
    have hle : n i ≤ ∑ j, n j := Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ i)
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc, hn i, mul_zero]

omit hι in
/-- Products of localizations are localizations. -/
lemma IsLocMap.prod {N N' : Type*} [AddCommGroup N] [Module S N] [AddCommGroup N']
    [Module S' N'] {ℓ₁ : M →ₛₗ[ι] M'} {ℓ₂ : N →ₛₗ[ι] N'} (h₁ : IsLocMap ι w ℓ₁)
    (h₂ : IsLocMap ι w ℓ₂) : IsLocMap ι w (prodMapₛₗ ℓ₁ ℓ₂) := by
  refine ⟨fun ⟨m', n'⟩ ↦ ?_, fun ⟨m, n⟩ h ↦ ?_⟩
  · obtain ⟨m, a, hm⟩ := h₁.surj m'
    obtain ⟨n, b, hn⟩ := h₂.surj n'
    refine ⟨(w ^ b • m, w ^ a • n), a + b, ?_⟩
    simp only [prodMapₛₗ_apply, Prod.smul_mk, map_pow_smul, ← hm, ← hn, smul_smul, ← pow_add,
      add_comm b a]
  · simp only [prodMapₛₗ_apply, Prod.mk_eq_zero] at h
    obtain ⟨a, ha⟩ := h₁.ker m h.1
    obtain ⟨b, hb⟩ := h₂.ker n h.2
    refine ⟨a + b, ?_⟩
    simp only [Prod.smul_mk, Prod.mk_eq_zero]
    constructor
    · rw [add_comm, pow_add, mul_smul, ha, smul_zero]
    · rw [pow_add, mul_smul, hb, smul_zero]

omit hι in
/-- The zero module localizes to the zero module. -/
lemma isLocMap_zero : IsLocMap ι w (0 : PUnit.{u + 1} →ₛₗ[ι] PUnit.{u + 1}) :=
  ⟨fun _ ↦ ⟨0, 0, Subsingleton.elim _ _⟩, fun _ _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

section Kernel

variable {F F' : Type*} [AddCommGroup F] [Module S F] [AddCommGroup F'] [Module S' F']
  {ℓF : F →ₛₗ[ι] F'} {ℓM : M →ₛₗ[ι] M'} (f : F →ₗ[S] M) (f' : F' →ₗ[S'] M')
  (hcomm : ∀ x, f' (ℓF x) = ℓM (f x))

omit hι in
include hcomm in
lemma map_ker_mem (x : LinearMap.ker f) : ℓF x ∈ LinearMap.ker f' := by
  rw [LinearMap.mem_ker, hcomm, LinearMap.mem_ker.mp x.2, map_zero]

/-- The restriction of `ℓF` to the kernels. -/
def kerRestrict : LinearMap.ker f →ₛₗ[ι] LinearMap.ker f' :=
  LinearMap.codRestrict _ (ℓF.comp (LinearMap.ker f).subtype) (map_ker_mem f f' hcomm)

omit hι in
@[simp] lemma coe_kerRestrict (x : LinearMap.ker f) :
    (kerRestrict f f' hcomm x : F') = ℓF x := rfl

include hcomm

omit hι in
/-- Localization is left exact: the restriction to the kernels is a localization. -/
lemma IsLocMap.kerRestrict (hF : IsLocMap ι w ℓF) (hM : IsLocMap ι w ℓM) :
    IsLocMap ι w (kerRestrict f f' hcomm) := by
  refine ⟨fun k' ↦ ?_, fun k hk ↦ ?_⟩
  · obtain ⟨x, n, hx⟩ := hF.surj k'
    have h0 : ℓM (f x) = 0 := by
      rw [← hcomm, ← hx, map_smul, LinearMap.mem_ker.mp k'.2, smul_zero]
    obtain ⟨m, hm⟩ := hM.ker _ h0
    refine ⟨⟨w ^ m • x, by rw [LinearMap.mem_ker, map_smul, hm]⟩, m + n, ?_⟩
    ext
    simp only [SetLike.val_smul, coe_kerRestrict, map_pow_smul, ← hx, smul_smul, ← pow_add]
  · obtain ⟨n, hn⟩ := hF.ker k (by simpa using congrArg Subtype.val hk)
    exact ⟨n, Subtype.ext hn⟩

/-- Localization is right exact: `f` surjective implies `f'` surjective. -/
lemma surjective_of_isLocMap (hM : IsLocMap ι w ℓM)
    (hf : Function.Surjective f) : Function.Surjective f' := by
  intro m'
  obtain ⟨m, n, hm⟩ := hM.surj m'
  obtain ⟨x, rfl⟩ := hf m
  refine ⟨(((hι.isUnit.pow n).unit⁻¹ : S'ˣ) : S') • ℓF x, ?_⟩
  rw [map_smul, hcomm, ← hm, smul_smul, IsUnit.val_inv_mul, one_smul]

end Kernel

/-! ### Uniqueness of localizations -/

section Unique

variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module S' M₁] [AddCommGroup M₂] [Module S' M₂]

omit hι

variable (w) in
/-- The graph relation `x = ι(w)⁻ⁿ ℓ₁ m ↔ y = ι(w)⁻ⁿ ℓ₂ m` between two localizations. -/
def LocRel (ℓ₁ : M →ₛₗ[ι] M₁) (ℓ₂ : M →ₛₗ[ι] M₂) (x : M₁) (y : M₂) : Prop :=
  ∃ (m : M) (n : ℕ), ι w ^ n • x = ℓ₁ m ∧ ι w ^ n • y = ℓ₂ m

variable {ℓ₁ : M →ₛₗ[ι] M₁} {ℓ₂ : M →ₛₗ[ι] M₂}

lemma LocRel.symm {x : M₁} {y : M₂} (h : LocRel w ℓ₁ ℓ₂ x y) : LocRel w ℓ₂ ℓ₁ y x :=
  let ⟨m, n, hx, hy⟩ := h; ⟨m, n, hy, hx⟩

lemma locRel_apply (m : M) : LocRel w ℓ₁ ℓ₂ (ℓ₁ m) (ℓ₂ m) := ⟨m, 0, by simp, by simp⟩

lemma LocRel.add {x x' : M₁} {y y' : M₂} (h : LocRel w ℓ₁ ℓ₂ x y)
    (h' : LocRel w ℓ₁ ℓ₂ x' y') : LocRel w ℓ₁ ℓ₂ (x + x') (y + y') := by
  obtain ⟨m, a, hx, hy⟩ := h
  obtain ⟨m', b, hx', hy'⟩ := h'
  refine ⟨w ^ b • m + w ^ a • m', a + b, ?_, ?_⟩
  · rw [map_add, map_pow_smul, map_pow_smul, ← hx, ← hx', smul_smul, smul_smul, ← pow_add,
      ← pow_add, add_comm b a, smul_add]
  · rw [map_add, map_pow_smul, map_pow_smul, ← hy, ← hy', smul_smul, smul_smul, ← pow_add,
      ← pow_add, add_comm b a, smul_add]

include hι in
lemma LocRel.smul {x : M₁} {y : M₂} (h : LocRel w ℓ₁ ℓ₂ x y) (s' : S') :
    LocRel w ℓ₁ ℓ₂ (s' • x) (s' • y) := by
  obtain ⟨m, n, hx, hy⟩ := h
  obtain ⟨s, a, hs⟩ := hι.surj s'
  refine ⟨s • m, a + n, ?_, ?_⟩
  · rw [pow_add, mul_smul, hι.pow_smul_comm n s' x, hx, ← mul_smul, hs,
      LinearMap.map_smulₛₗ]
  · rw [pow_add, mul_smul, hι.pow_smul_comm n s' y, hy, ← mul_smul, hs,
      LinearMap.map_smulₛₗ]

lemma locRel_total (h₁ : IsLocMap ι w ℓ₁) (hu : IsUnit (ι w)) (x : M₁) :
    ∃ y, LocRel w ℓ₁ ℓ₂ x y := by
  obtain ⟨m, n, hm⟩ := h₁.surj x
  refine ⟨(((hu.pow n).unit⁻¹ : S'ˣ) : S') • ℓ₂ m, m, n, hm, ?_⟩
  rw [smul_smul, IsUnit.mul_val_inv, one_smul]

lemma LocRel.unique (h₁ : IsLocMap ι w ℓ₁) (hu : IsUnit (ι w)) {x : M₁} {y y' : M₂}
    (h : LocRel w ℓ₁ ℓ₂ x y) (h' : LocRel w ℓ₁ ℓ₂ x y') : y = y' := by
  obtain ⟨m, a, hx, hy⟩ := h
  obtain ⟨m', b, hx', hy'⟩ := h'
  have h0 : ℓ₁ (w ^ b • m - w ^ a • m') = 0 := by
    rw [map_sub, map_pow_smul, map_pow_smul, ← hx, ← hx', smul_smul, smul_smul, ← pow_add,
      ← pow_add, add_comm b a, sub_self]
  obtain ⟨j, hj⟩ := h₁.ker _ h0
  have h1 := congrArg ℓ₂ hj
  rw [map_zero, map_pow_smul, map_sub, map_pow_smul, map_pow_smul, ← hy, ← hy', smul_smul,
    smul_smul, ← pow_add, ← pow_add, add_comm b a, ← smul_sub] at h1
  have h2 := ((hu.pow j).smul_eq_zero).mp h1
  exact sub_eq_zero.mp (((hu.pow (a + b)).smul_eq_zero).mp h2)

include hι in
/-- **Uniqueness of localization**: two localizations of the same `S`-module are
`S'`-linearly isomorphic. -/
noncomputable def locEquiv (h₁ : IsLocMap ι w ℓ₁) (h₂ : IsLocMap ι w ℓ₂) : M₁ ≃ₗ[S'] M₂ where
  toFun x := (locRel_total (ℓ₂ := ℓ₂) h₁ hι.isUnit x).choose
  invFun y := (locRel_total (ℓ₂ := ℓ₁) h₂ hι.isUnit y).choose
  map_add' x x' := (locRel_total h₁ hι.isUnit (x + x')).choose_spec.unique h₁ hι.isUnit
    ((locRel_total h₁ hι.isUnit x).choose_spec.add (locRel_total h₁ hι.isUnit x').choose_spec)
  map_smul' s' x := (locRel_total h₁ hι.isUnit (s' • x)).choose_spec.unique h₁ hι.isUnit
    ((locRel_total h₁ hι.isUnit x).choose_spec.smul hι s')
  left_inv x := by
    have h := (locRel_total (ℓ₂ := ℓ₁) h₂ hι.isUnit
      (locRel_total (ℓ₂ := ℓ₂) h₁ hι.isUnit x).choose).choose_spec
    exact h.unique h₂ hι.isUnit (locRel_total (ℓ₂ := ℓ₂) h₁ hι.isUnit x).choose_spec.symm
  right_inv y := by
    have h := (locRel_total (ℓ₂ := ℓ₂) h₁ hι.isUnit
      (locRel_total (ℓ₂ := ℓ₁) h₂ hι.isUnit y).choose).choose_spec
    exact h.unique h₁ hι.isUnit (locRel_total (ℓ₂ := ℓ₁) h₂ hι.isUnit y).choose_spec.symm

include hι in
lemma locEquiv_apply (h₁ : IsLocMap ι w ℓ₁) (h₂ : IsLocMap ι w ℓ₂) (m : M) :
    locEquiv hι h₁ h₂ (ℓ₁ m) = ℓ₂ m :=
  (locRel_total h₁ hι.isUnit (ℓ₁ m)).choose_spec.unique h₁ hι.isUnit (locRel_apply m)

end Unique

/-! ### The lattice -/

include hι in
/-- **(R6) Lattice.** Every finitely generated `S'`-module is the localization of a finitely
generated `S`-module (a quotient of some `S^k`). -/
theorem exists_lattice (P : Type*) [AddCommGroup P] [Module S' P] [Module.Finite S' P] :
    ∃ (k : ℕ) (N : Submodule S (Fin k → S)) (ℓ : ((Fin k → S) ⧸ N) →ₛₗ[ι] P),
      IsLocMap ι w ℓ := by
  obtain ⟨k, π, hπ⟩ := Module.Finite.exists_fin' S' P
  let φ : (Fin k → S) →ₛₗ[ι] P := π.comp (piMap ι (Fin k))
  refine ⟨k, LinearMap.ker φ, (LinearMap.ker φ).liftQ φ le_rfl, fun p ↦ ?_, fun q hq ↦ ?_⟩
  · obtain ⟨x', rfl⟩ := hπ p
    obtain ⟨x, n, hx⟩ := (isLocMap_piMap hι (Fin k)).surj x'
    exact ⟨Submodule.Quotient.mk x, n, by
      rw [Submodule.liftQ_apply, ← map_smul, hx]; rfl⟩
  · refine ⟨0, ?_⟩
    induction q using Submodule.Quotient.induction_on with
    | H x =>
      rw [Submodule.liftQ_apply] at hq
      rw [pow_zero, one_smul, Submodule.Quotient.mk_eq_zero]
      exact hq

end LocMap


/-! ### Theorem R (abstract central-localization form) -/

section TheoremR

variable {S S' : Type u} [Ring S] [Ring S'] {ι : S →+* S'} {w : S}

variable (ι w) in
/-- A finitely generated projective `S`-module `Q` together with a localization `Q → Q'`
(so `Q' ≅ Q[w⁻¹]` as `S'`-modules, uniquely by `locEquiv`). -/
structure LocProj where
  /-- The finitely generated projective `S`-module. -/
  Q : Type u
  [instAddCommGroup : AddCommGroup Q]
  [instModule : Module S Q]
  [instFinite : Module.Finite S Q]
  [instProjective : Module.Projective S Q]
  /-- Its localization `Q[w⁻¹]`. -/
  Q' : Type u
  [instAddCommGroup' : AddCommGroup Q']
  [instModule' : Module S' Q']
  /-- The localization map. -/
  ℓ : Q →ₛₗ[ι] Q'
  isLocMap : IsLocMap ι w ℓ

attribute [instance] LocProj.instAddCommGroup LocProj.instModule LocProj.instFinite
  LocProj.instProjective LocProj.instAddCommGroup' LocProj.instModule'

namespace LocProj

/-- The free module `S^k` and its localization `S'^k`. -/
def free (hι : IsCentralLoc ι w) (k : ℕ) : LocProj ι w :=
  ⟨Fin k → S, Fin k → S', piMap ι (Fin k), isLocMap_piMap hι (Fin k)⟩

/-- The product of two localized projectives. -/
def prod (E₁ E₂ : LocProj ι w) : LocProj ι w :=
  ⟨E₁.Q × E₂.Q, E₁.Q' × E₂.Q', prodMapₛₗ E₁.ℓ E₂.ℓ, E₁.isLocMap.prod E₂.isLocMap⟩

/-- The zero module. -/
def zero : LocProj ι w :=
  ⟨PUnit.{u + 1}, PUnit.{u + 1}, 0, isLocMap_zero⟩

end LocProj

variable (hι : IsCentralLoc ι w)
include hι

/-- The map `S'^k → M'`, `x ↦ ∑ xᵢ • ℓ (f eᵢ)`, localizing `f : S^k → M`. -/
def locLift {M M' : Type*} [AddCommGroup M] [Module S M] [AddCommGroup M'] [Module S' M']
    (ℓ : M →ₛₗ[ι] M') {k : ℕ} (f : (Fin k → S) →ₗ[S] M) : (Fin k → S') →ₗ[S'] M' where
  toFun x := ∑ i, x i • ℓ (f (Pi.single i 1))
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum, mul_smul]

omit hι in
lemma locLift_piMap {M M' : Type*} [AddCommGroup M] [Module S M] [AddCommGroup M']
    [Module S' M'] (ℓ : M →ₛₗ[ι] M') {k : ℕ} (f : (Fin k → S) →ₗ[S] M) (x : Fin k → S) :
    locLift ℓ f (piMap ι (Fin k) x) = ℓ (f x) := by
  conv_rhs => rw [← Finset.univ_sum_single x]
  simp only [locLift, LinearMap.coe_mk, AddHom.coe_mk, piMap_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← LinearMap.map_smulₛₗ, ← map_smul]
  congr 2
  ext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

/-- **(R4)–(R7), the induction.** Let `M` be a finitely generated `S`-module of `pd ≤ d`
whose localization `M'` is `S'`-projective. Then `M' ⊕ Q₁[w⁻¹] ≅ Q₀[w⁻¹]` for some finitely
generated projective `S`-modules `Q₀, Q₁` (Euler characteristic of a resolution, split from
the left). -/
theorem stable_of_isLocMap [IsNoetherianRing S] (d : ℕ) :
    ∀ (M : Type u) [AddCommGroup M] [Module S M] [Module.Finite S M] (M' : Type u)
      [AddCommGroup M'] [Module S' M'] [Module.Projective S' M'] (ℓ : M →ₛₗ[ι] M'),
      IsLocMap ι w ℓ → PdLE S M d →
      ∃ E₀ E₁ : LocProj ι w, Nonempty ((M' × E₁.Q') ≃ₗ[S'] E₀.Q') := by
  induction d with
  | zero =>
    intro M _ _ _ M' _ _ _ ℓ hℓ hM
    have := hM.projective
    exact ⟨⟨M, M', ℓ, hℓ⟩, LocProj.zero,
      ⟨(LinearEquiv.prodUnique : (M' × PUnit.{u + 1}) ≃ₗ[S'] M')⟩⟩
  | succ d ih =>
    intro M _ _ _ M' _ _ _ ℓ hℓ hM
    obtain ⟨k, f, hf, hfin, hK⟩ := exists_resolution_step M hM
    let f' := locLift ℓ f
    have hcomm : ∀ x, f' (piMap ι (Fin k) x) = ℓ (f x) := locLift_piMap ℓ f
    have hf' : Function.Surjective f' := surjective_of_isLocMap hι f f' hcomm hℓ hf
    obtain ⟨e⟩ := exists_prodEquiv_of_surjective f' hf'
    have : Module.Projective S' (LinearMap.ker f' × M') := Module.Projective.of_equiv e.symm
    have : Module.Projective S' (LinearMap.ker f') :=
      Module.Projective.of_split (LinearMap.inl S' _ M') (LinearMap.fst S' _ M')
        (LinearMap.fst_comp_inl S' _ M')
    obtain ⟨E₀', E₁', ⟨e'⟩⟩ := ih (LinearMap.ker f) (LinearMap.ker f')
      (kerRestrict f f' hcomm) ((isLocMap_piMap hι (Fin k)).kerRestrict f f' hcomm hℓ) hK
    refine ⟨(LocProj.free hι k).prod E₁', E₀', ⟨?_⟩⟩
    show (M' × E₀'.Q') ≃ₗ[S'] ((Fin k → S') × E₁'.Q')
    exact ((LinearEquiv.refl S' M').prodCongr e'.symm).trans
      ((LinearEquiv.prodAssoc S' M' (LinearMap.ker f') E₁'.Q').symm.trans
        (((LinearEquiv.prodComm S' M' (LinearMap.ker f')).trans e).prodCongr
          (LinearEquiv.refl S' E₁'.Q')))

/-- **Theorem R (abstract form).** Let `ι : S → S'` be the localization of a left noetherian
ring `S` of finite global dimension at a central element `w`. Then for every finitely
generated projective `S'`-module `P` there are finitely generated projective `S`-modules
`Q₀, Q₁` with `P ⊕ Q₁[w⁻¹] ≅ Q₀[w⁻¹]`. -/
theorem theoremR_abstract [IsNoetherianRing S] {d : ℕ} (hgl : GlobalDimLE S d) (P : Type u)
    [AddCommGroup P] [Module S' P] [Module.Finite S' P] [Module.Projective S' P] :
    ∃ E₀ E₁ : LocProj ι w, Nonempty ((P × E₁.Q') ≃ₗ[S'] E₀.Q') := by
  obtain ⟨k, N, ℓ, hℓ⟩ := exists_lattice hι P
  exact stable_of_isLocMap hι d _ P ℓ hℓ (hgl _)

end TheoremR


/-! ### Laurent extensions and central localizations -/

section Laurent

open LaurentPolynomial

variable {S S' : Type u} [Ring S] [Ring S']

/-- `ι` applied to the coefficients of a Laurent polynomial. -/
noncomputable abbrev laurentMap (ι : S →+* S') : S[T;T⁻¹] →+* S'[T;T⁻¹] :=
  AddMonoidAlgebra.mapRingHom ℤ ι

lemma laurentMap_C_mul_T (ι : S →+* S') (a : S) (n : ℤ) :
    laurentMap ι (C a * T n) = C (ι a) * T n := by
  rw [← single_eq_C_mul_T, ← single_eq_C_mul_T, AddMonoidAlgebra.mapRingHom_single]

lemma coeff_laurentMap (ι : S →+* S') (f : S[T;T⁻¹]) (i : ℤ) :
    (laurentMap ι f).coeff i = ι (f.coeff i) :=
  AddMonoidAlgebra.coeff_mapRingHom ι f i

lemma coeff_C_mul (a : S) (f : S[T;T⁻¹]) (i : ℤ) : (C a * f).coeff i = a * f.coeff i := by
  rw [← single_eq_C]
  exact AddMonoidAlgebra.coeff_single_zero_mul f a i

lemma coeff_mul_C (a : S) (f : S[T;T⁻¹]) (i : ℤ) : (f * C a).coeff i = f.coeff i * a := by
  rw [← single_eq_C]
  exact AddMonoidAlgebra.coeff_mul_single_zero f a i

/-- **Base case.** `R[X] → R[T;T⁻¹]` is the localization at the central element `X`, for any
(noncommutative) ring `R`. -/
lemma isCentralLoc_toLaurent (R : Type u) [Ring R] :
    IsCentralLoc (Polynomial.toLaurent : Polynomial R →+* R[T;T⁻¹]) Polynomial.X := by
  refine ⟨fun p ↦ (Polynomial.commute_X p).eq, ?_, fun f ↦ ?_, fun p hp ↦ ⟨0, ?_⟩⟩
  · rw [Polynomial.toLaurent_X]
    exact isUnit_T 1
  · obtain ⟨n, f', hf'⟩ := exists_T_pow f
    refine ⟨f', n, ?_⟩
    rw [hf', Polynomial.toLaurent_X, T_pow, mul_one, T_mul]
  · rw [Polynomial.toLaurent_eq_zero.mp hp, mul_zero]

/-- **Laurent extension preserves central localizations**: if `ι : S → S'` is the localization
at the central `w`, then `S[T;T⁻¹] → S'[T;T⁻¹]` is the localization at `C w`. -/
lemma IsCentralLoc.laurent {ι : S →+* S'} {w : S} (hι : IsCentralLoc ι w) :
    IsCentralLoc (laurentMap ι) (C w) := by
  refine ⟨fun f ↦ ?_, ?_, fun f ↦ ?_, fun f hf ↦ ?_⟩
  · ext i
    rw [coeff_C_mul, coeff_mul_C, hι.comm]
  · rw [← single_eq_C, AddMonoidAlgebra.mapRingHom_single, single_eq_C]
    exact hι.isUnit.map C
  · induction f using LaurentPolynomial.induction_on' with
    | add f g hf hg =>
      obtain ⟨p, a, hp⟩ := hf
      obtain ⟨q, b, hq⟩ := hg
      refine ⟨C w ^ b * p + C w ^ a * q, a + b, ?_⟩
      rw [map_add, map_mul, map_mul, map_pow, map_pow, ← hp, ← hq, ← mul_assoc, ← mul_assoc,
        ← pow_add, ← pow_add, add_comm b a, mul_add]
    | C_mul_T n c =>
      obtain ⟨s, a, hs⟩ := hι.surj c
      refine ⟨C s * T n, a, ?_⟩
      rw [laurentMap_C_mul_T, ← hs, ← single_eq_C, AddMonoidAlgebra.mapRingHom_single,
        single_eq_C, ← map_pow, ← mul_assoc, ← map_mul]
  · have h0 : ∀ i, ι (f.coeff i) = 0 := fun i ↦ by
      rw [← coeff_laurentMap, hf]; rfl
    choose n hn using fun i ↦ hι.ker _ (h0 i)
    refine ⟨∑ i ∈ f.coeff.support, n i, ?_⟩
    ext i
    rw [← map_pow, coeff_C_mul]
    change w ^ _ * f.coeff i = 0
    by_cases hi : i ∈ f.coeff.support
    · have hle : n i ≤ ∑ j ∈ f.coeff.support, n j := Finset.single_le_sum
        (fun _ _ ↦ Nat.zero_le _) hi
      rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc, hn i, mul_zero]
    · rw [Finsupp.notMem_support_iff.mp hi, mul_zero]

end Laurent


section Iterate

/-- `lpRing n R = R[t₁^±]…[tₙ^±]`: the `n`-fold Laurent extension of a (noncommutative) ring,
with the **newest variable innermost**: `lpRing (n + 1) R = lpRing n (R[T;T⁻¹])`. This is the
recursion of `Lpow`, so `Hom` in `Lpow n` of a matrix category is matrices over `lpRing n`. -/
noncomputable def lpRing : ℕ → RingCat.{u} → RingCat.{u}
  | 0, R => R
  | n + 1, R => lpRing n (RingCat.of (LaurentPolynomial R))

lemma lpRing_zero (R : RingCat.{u}) : lpRing 0 R = R := rfl

lemma lpRing_succ (n : ℕ) (R : RingCat.{u}) :
    lpRing (n + 1) R = lpRing n (RingCat.of (LaurentPolynomial R)) := rfl

/-- Functoriality of `lpRing` (coefficientwise). -/
noncomputable def lpRingMap : ∀ (n : ℕ) {R R' : RingCat.{u}}, (R →+* R') →
    (lpRing n R →+* lpRing n R')
  | 0, _, _, f => f
  | n + 1, _, _, f => lpRingMap n (R := RingCat.of (LaurentPolynomial _))
      (R' := RingCat.of (LaurentPolynomial _)) (laurentMap f)

/-- The constants `R →+* lpRing n R`. -/
noncomputable def lpRingC : ∀ (n : ℕ) (R : RingCat.{u}), R →+* lpRing n R
  | 0, _ => RingHom.id _
  | n + 1, R => (lpRingC n (RingCat.of (LaurentPolynomial R))).comp LaurentPolynomial.C

/-- Iterated Laurent extensions preserve central localizations. -/
lemma IsCentralLoc.lpRing : ∀ (n : ℕ) {R R' : RingCat.{u}} {ι : R →+* R'} {w : R},
    IsCentralLoc ι w → IsCentralLoc (lpRingMap n ι) (lpRingC n R w)
  | 0, _, _, _, _, h => h
  | n + 1, _, _, _, _, h => IsCentralLoc.lpRing n h.laurent

/-- The **face map** `lpRing n (R[X]) → lpRing n (R[T;T⁻¹]) = lpRing (n + 1) R`, induced by
`R[X] → R[T;T⁻¹]` in the innermost variable. -/
noncomputable def faceMap (n : ℕ) (R : RingCat.{u}) :
    lpRing n (RingCat.of (Polynomial R)) →+* lpRing (n + 1) R :=
  lpRingMap n (R := RingCat.of (Polynomial R)) (R' := RingCat.of (LaurentPolynomial R))
    Polynomial.toLaurent

/-- The innermost variable `X ∈ lpRing n (R[X])`. -/
noncomputable def faceVar (n : ℕ) (R : RingCat.{u}) : lpRing n (RingCat.of (Polynomial R)) :=
  lpRingC n (RingCat.of (Polynomial R)) Polynomial.X

/-- The face map is the localization at the central element `X` (blueprint: "`C → C'` is
`IsLocalization.Away w`; Laurent preserves `Away` localizations"). -/
lemma isCentralLoc_faceMap (n : ℕ) (R : RingCat.{u}) :
    IsCentralLoc (faceMap n R) (faceVar n R) :=
  IsCentralLoc.lpRing n (isCentralLoc_toLaurent R)

end Iterate

end HSFormal.LTheory.Reg
