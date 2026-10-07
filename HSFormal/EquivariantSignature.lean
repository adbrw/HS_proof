import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.RepresentationTheory.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import HSFormal.AlgebraicReduction

/-!
# Equivariant signatures (manuscript §3, Lemma 3.1)

For a group `G` acting linearly on a finite-dimensional real vector space `V` and preserving a
symmetric bilinear form `b`, a `SignatureDecomposition` is a `G`-invariant splitting
`V = V⁺ ⊕ V⁻` with `b` positive definite on `V⁺`, negative definite on `V⁻`, and `V⁺ ⊥_b V⁻`.
Its character `χ_{V⁺} - χ_{V⁻}` (real traces, which equal the traces on `V^±_ℂ`) is the
manuscript's `Sign_G(V, b)` (3.1), packaged as `equivariantSignature`.

* `SignatureDecomposition.character_eq`: equivariant Sylvester inertia, the character does not
  depend on the decomposition.
* `SignatureDecomposition.character_one`: the value at `1` is the ordinary signature, defined
  G-free via maximal positive definite subspaces (`posIndex`).
* `exists_signatureDecomposition`: for finite `G` and nondegenerate `b`, a decomposition exists
  (average an inner product, take the spectral subspaces of the `b`-operator).
* `SignatureDecomposition.prime_dvd_signature` and
  `prime_dvd_signature_of_equivariantSignature_eq_zero`: manuscript Lemma 3.1, via
  `prime_dvd_sum_of_character_vanishes`.
* `ratEquivariantSignature`, `prime_dvd_ratSignature`: the rational forms of the manuscript,
  through `V_ℝ = ℝ ⊗[ℚ] V`.
-/

noncomputable section

open Module
open LinearMap (BilinForm)

namespace HSFormal

section Sylvester

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The bilinear form `b` is positive definite on the subspace `W`. -/
def PosDefOn (b : BilinForm ℝ V) (W : Submodule ℝ V) : Prop :=
  ∀ v ∈ W, v ≠ 0 → 0 < b v v

/-- The positive index of inertia: the largest dimension of a subspace on which `b` is
positive definite. -/
def posIndex (b : BilinForm ℝ V) : ℕ :=
  sSup {k | ∃ W : Submodule ℝ V, PosDefOn b W ∧ finrank ℝ W = k}

/-- The ordinary signature `σ(b)` of a real symmetric bilinear form. -/
def signature (b : BilinForm ℝ V) : ℤ :=
  posIndex b - posIndex (-b)

theorem disjoint_of_posDefOn {b : BilinForm ℝ V} {W N : Submodule ℝ V} (hW : PosDefOn b W)
    (hN : PosDefOn (-b) N) : Disjoint W N := by
  rw [Submodule.disjoint_def]
  intro v hvW hvN
  by_contra hv
  have h₁ := hW v hvW hv
  have h₂ := hN v hvN hv
  simp only [LinearMap.neg_apply] at h₂
  linarith

variable [FiniteDimensional ℝ V]

theorem finrank_le_of_posDefOn {b : BilinForm ℝ V} {P N W : Submodule ℝ V} (h : IsCompl P N)
    (hN : PosDefOn (-b) N) (hW : PosDefOn b W) : finrank ℝ W ≤ finrank ℝ P := by
  have hWN := Submodule.finrank_sup_add_finrank_inf_eq W N
  rw [(disjoint_of_posDefOn hW hN).eq_bot, finrank_bot] at hWN
  have := Submodule.finrank_le (W ⊔ N)
  have := Submodule.finrank_add_eq_of_isCompl h
  omega

/-- Sylvester's law of inertia: a complementary pair of a positive definite and a negative
definite subspace computes the positive index. -/
theorem posIndex_eq_finrank {b : BilinForm ℝ V} {P N : Submodule ℝ V} (h : IsCompl P N)
    (hP : PosDefOn b P) (hN : PosDefOn (-b) N) : posIndex b = finrank ℝ P := by
  apply le_antisymm
  · refine csSup_le ⟨_, P, hP, rfl⟩ ?_
    rintro _ ⟨W, hW, rfl⟩
    exact finrank_le_of_posDefOn h hN hW
  · refine le_csSup ⟨finrank ℝ V, ?_⟩ ⟨P, hP, rfl⟩
    rintro _ ⟨W, -, rfl⟩
    exact Submodule.finrank_le W

end Sylvester

section Decomposition

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℝ V]

/-- A `G`-invariant signature decomposition `V = V⁺ ⊕ V⁻` of an invariant form `b`. -/
structure SignatureDecomposition (ρ : Representation ℝ G V) (b : BilinForm ℝ V) where
  /-- The positive part `V⁺`. -/
  pos : Submodule ℝ V
  /-- The negative part `V⁻`. -/
  neg : Submodule ℝ V
  isCompl : IsCompl pos neg
  pos_le_comap : ∀ g, pos ≤ pos.comap (ρ g)
  neg_le_comap : ∀ g, neg ≤ neg.comap (ρ g)
  posDefOn : PosDefOn b pos
  negDefOn : PosDefOn (-b) neg
  orthogonal : ∀ v ∈ pos, ∀ w ∈ neg, b v w = 0

namespace SignatureDecomposition

variable {ρ : Representation ℝ G V} {b : BilinForm ℝ V} (d : SignatureDecomposition ρ b)

/-- The character of `V⁺`. -/
def posChar (g : G) : ℝ :=
  LinearMap.trace ℝ d.pos (ρ.subrepresentation d.pos d.pos_le_comap g)

/-- The character of `V⁻`. -/
def negChar (g : G) : ℝ :=
  LinearMap.trace ℝ d.neg (ρ.subrepresentation d.neg d.neg_le_comap g)

/-- The signature character `χ_{V⁺} - χ_{V⁻}`, manuscript (3.1). -/
def character (g : G) : ℂ :=
  ((d.posChar g - d.negChar g : ℝ) : ℂ)

variable [FiniteDimensional ℝ V]

theorem finrank_pos : finrank ℝ d.pos = posIndex b :=
  (posIndex_eq_finrank d.isCompl d.posDefOn d.negDefOn).symm

theorem finrank_neg : finrank ℝ d.neg = posIndex (-b) :=
  (posIndex_eq_finrank d.isCompl.symm d.negDefOn fun v hv hne => by
    simpa using d.posDefOn v hv hne).symm

/-- The value of the signature character at `1` is the ordinary signature. -/
theorem character_one : d.character 1 = signature b := by
  simp only [character, posChar, negChar, map_one, LinearMap.trace_one, finrank_pos, finrank_neg,
    signature]
  push_cast
  rfl

end SignatureDecomposition

open Submodule in
theorem projection_map_of_le_comap {P N : Submodule ℝ V} (h : IsCompl P N) (f : V →ₗ[ℝ] V)
    (hP : P ≤ P.comap f) (hN : N ≤ N.comap f) (v : V) :
    P.projection N h (f v) = f (P.projection N h v) := by
  conv_lhs => rw [← projection_add_projection_eq_self h v, map_add, map_add]
  rw [(projection_eq_self_iff h _).mpr (hP (projection_apply_mem h v)),
    (projection_apply_eq_zero_iff h).mpr (hN (projection_apply_mem h.symm v)), add_zero]

variable [FiniteDimensional ℝ V] {ρ : Representation ℝ G V}

/-- Equivariant Sylvester inertia, abstract form: if `P` meets the invariant complement `N'`
of `P'` trivially and has the same dimension, projection along `N'` is a `G`-isomorphism
`P ≃ P'`, so the characters agree. -/
theorem trace_subrepresentation_eq {P P' N' : Submodule ℝ V} (hP : ∀ g, P ≤ P.comap (ρ g))
    (hP' : ∀ g, P' ≤ P'.comap (ρ g)) (hN' : ∀ g, N' ≤ N'.comap (ρ g)) (h' : IsCompl P' N')
    (hdisj : Disjoint P N') (hdim : finrank ℝ P = finrank ℝ P') (g : G) :
    LinearMap.trace ℝ P (ρ.subrepresentation P hP g) =
      LinearMap.trace ℝ P' (ρ.subrepresentation P' hP' g) := by
  set f : P →ₗ[ℝ] P' := P'.projectionOnto N' h' ∘ₗ P.subtype
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hxN : (x : V) ∈ N' := (Submodule.projectionOnto_apply_eq_zero_iff h').mp hx
    exact Subtype.ext ((Submodule.disjoint_def.mp hdisj) _ x.2 hxN)
  set e := f.linearEquivOfInjective hf hdim
  have hcomm : ∀ x : P, e (ρ.subrepresentation P hP g x) =
      ρ.subrepresentation P' hP' g (e x) := by
    intro x
    apply Subtype.ext
    simpa [e, f] using projection_map_of_le_comap h' (ρ g) (hP' g) (hN' g) x
  rw [← LinearMap.trace_conj' _ e]
  congr 1
  refine LinearMap.ext fun x => ?_
  simp only [LinearEquiv.conj_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, hcomm, LinearEquiv.apply_symm_apply]

namespace SignatureDecomposition

variable {b : BilinForm ℝ V}

/-- Equivariant Sylvester inertia: the signature character does not depend on the choice of
invariant decomposition. -/
theorem character_eq (d d' : SignatureDecomposition ρ b) : d.character = d'.character := by
  funext g
  have hpos : d.posChar g = d'.posChar g :=
    trace_subrepresentation_eq d.pos_le_comap d'.pos_le_comap d'.neg_le_comap d'.isCompl
      (disjoint_of_posDefOn d.posDefOn d'.negDefOn) (by rw [d.finrank_pos, d'.finrank_pos]) g
  have hneg : d.negChar g = d'.negChar g :=
    trace_subrepresentation_eq d.neg_le_comap d'.neg_le_comap d'.pos_le_comap d'.isCompl.symm
      (disjoint_of_posDefOn d'.posDefOn d.negDefOn).symm
      (by rw [d.finrank_neg, d'.finrank_neg]) g
  simp only [character, hpos, hneg]

end SignatureDecomposition

end Decomposition

section Cyclic

/-- Sums of `n`-th roots of unity are integral combinations of powers of a primitive root,
with multiplicities adding up to the number of summands. -/
theorem multiset_sum_eq_sum_count_pow {n : ℕ} [NeZero n] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n)
    (s : Multiset ℂ) (hs : ∀ r ∈ s, r ^ n = 1) :
    s.sum = ∑ j : Fin n, (s.count (ζ ^ (j : ℕ)) : ℂ) * ζ ^ (j : ℕ) ∧
      ∑ j : Fin n, s.count (ζ ^ (j : ℕ)) = Multiset.card s := by
  classical
  have hinj : Set.InjOn (fun j : Fin n => ζ ^ (j : ℕ)) (Finset.univ : Finset (Fin n)) :=
    fun i _ j _ hij => Fin.ext (hζ.pow_inj i.2 j.2 hij)
  have hmem : ∀ r ∈ s, r ∈ Finset.univ.image (fun j : Fin n => ζ ^ (j : ℕ)) := by
    intro r hr
    obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one (hs r hr)
    exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [Finset.sum_multiset_count_of_subset s _ fun r hr => hmem r (Multiset.mem_toFinset.mp hr),
      Finset.sum_image hinj]
    simp [nsmul_eq_mul]
  · rw [← Multiset.sum_count_eq_card hmem, Finset.sum_image hinj]

/-- The trace of a real operator `A` with `A ^ n = 1` is `∑ j, m j * ζ ^ j` for natural
multiplicities `m` (of the eigenvalues `ζ ^ j` of `A ⊗ ℂ`) summing to the dimension. -/
theorem exists_trace_eq_sum_pow {W : Type*} [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ W] {n : ℕ} [NeZero n] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n)
    {A : W →ₗ[ℝ] W} (hA : A ^ n = 1) :
    ∃ m : Fin n → ℕ, ((LinearMap.trace ℝ W A : ℝ) : ℂ) = ∑ j, (m j : ℂ) * ζ ^ (j : ℕ) ∧
      ∑ j, m j = finrank ℝ W := by
  classical
  set B := Module.finBasis ℝ W
  set M := Complex.ofRealHom.mapMatrix (LinearMap.toMatrixAlgEquiv B A)
  have hM : M ^ n = 1 := by
    simp only [M, ← map_pow, hA, map_one]
  have hroots : ∀ r ∈ M.charpoly.roots, r ^ n = 1 := by
    intro r hr
    have hr' : r ∈ spectrum ℂ M := Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
      ((Polynomial.mem_roots M.charpoly_monic.ne_zero).mp hr)
    have hpow := spectrum.pow_mem_pow M n hr'
    rw [hM, spectrum.mem_iff, ← map_one (algebraMap ℂ _), ← map_sub] at hpow
    by_contra hne
    exact hpow ((sub_ne_zero.mpr hne).isUnit.map _)
  obtain ⟨hsum, hcard⟩ := multiset_sum_eq_sum_count_pow hζ _ hroots
  refine ⟨fun j => M.charpoly.roots.count (ζ ^ (j : ℕ)), ?_, ?_⟩
  · rw [← hsum, ← Matrix.trace_eq_sum_roots_charpoly, LinearMap.trace_eq_matrix_trace ℝ B]
    simp [M, Matrix.trace, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
  · rw [hcard, IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin]

end Cyclic

namespace SignatureDecomposition

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  {ρ : Representation ℝ G V} {b : BilinForm ℝ V}

/-- Manuscript Lemma 3.1: if `g ^ p ^ (k + 1) = 1` (for instance `g` generates `C_{p^a}`,
`a ≥ 1`) and the signature character vanishes at `g`, then `p ∣ σ(b)`. -/
theorem prime_dvd_signature (d : SignatureDecomposition ρ b) {p k : ℕ} (hp : p.Prime) {g : G}
    (hg : g ^ p ^ (k + 1) = 1) (h : d.character g = 0) : (p : ℤ) ∣ signature b := by
  haveI : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hζ := Complex.isPrimitiveRoot_exp (p ^ (k + 1)) (NeZero.ne _)
  obtain ⟨m₁, hm₁, hs₁⟩ := exists_trace_eq_sum_pow hζ
    (A := ρ.subrepresentation d.pos d.pos_le_comap g) (by rw [← map_pow, hg, map_one])
  obtain ⟨m₂, hm₂, hs₂⟩ := exists_trace_eq_sum_pow hζ
    (A := ρ.subrepresentation d.neg d.neg_le_comap g) (by rw [← map_pow, hg, map_one])
  have key := prime_dvd_sum_of_character_vanishes p k hp _ hζ (fun j => (m₁ j : ℤ) - m₂ j) ?_
  · rw [signature, ← d.finrank_pos, ← d.finrank_neg, ← hs₁, ← hs₂]
    push_cast
    simpa [Finset.sum_sub_distrib] using key
  · simp only [character, posChar, negChar, Complex.ofReal_sub, hm₁, hm₂] at h
    rw [← h, ← Finset.sum_sub_distrib]
    push_cast
    simp [sub_mul]

end SignatureDecomposition

section Existence

variable {G : Type*} [Group G]

/-- Given a `G`-invariant inner product, the positive and negative spectral subspaces of the
self-adjoint operator representing `b` form an invariant signature decomposition. -/
theorem exists_signatureDecomposition_of_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : Representation ℝ G E)
    (hρ : ∀ g v w, inner ℝ (ρ g v) (ρ g w) = inner ℝ v w) {b : BilinForm ℝ E} (hb : b.IsSymm)
    (hnd : b.Nondegenerate) (hinv : ∀ g v w, b (ρ g v) (ρ g w) = b v w) :
    Nonempty (SignatureDecomposition ρ b) := by
  classical
  have hI : BilinForm.Nondegenerate (innerₗ E) :=
    ⟨fun v hv => inner_self_eq_zero.mp (hv v), fun v hv => inner_self_eq_zero.mp (hv v)⟩
  set T := b.symmCompOfNondegenerate (innerₗ E) hI
  have hT : ∀ v w, inner ℝ (T v) w = b v w := fun v w =>
    LinearMap.congr_fun (b.comp_symmCompOfNondegenerate_apply hI v) w
  have hTs : T.IsSymmetric := fun v w => by
    rw [hT, real_inner_comm, hT, hb.eq]
  have hcomm : ∀ g v, T (ρ g v) = ρ g (T v) := by
    intro g v
    refine ext_inner_right ℝ fun w => ?_
    rw [hT, ← ρ.self_inv_apply g w, hinv, hρ, hT]
  set e := hTs.eigenvectorBasis (rfl : finrank ℝ E = finrank ℝ E)
  set μ := hTs.eigenvalues (rfl : finrank ℝ E = finrank ℝ E)
  have hTe : ∀ v i, e.repr (T v) i = μ i * e.repr v i :=
    hTs.eigenvectorBasis_apply_self_apply rfl
  have hb_eq : ∀ v w, b v w = ∑ i, μ i * (e.repr v i * e.repr w i) := by
    intro v w
    rw [← hT, ← e.sum_inner_mul_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm, ← e.repr_apply_apply, ← e.repr_apply_apply, hTe, mul_assoc]
  have hcoord : ∀ w (c : ℝ), T w = c • w → ∀ j, μ j ≠ c → e.repr w j = 0 := by
    intro w c hw j hj
    have h := hTe w j
    rw [hw, map_smul, PiLp.smul_apply, smul_eq_mul] at h
    exact (mul_eq_zero.mp (by linarith : (c - μ j) * e.repr w j = 0)).resolve_left
      (sub_ne_zero.mpr hj.symm)
  have hzero : ∀ v, (∀ i, e.repr v i = 0) → v = 0 := fun v hv => by
    rw [← e.sum_repr v]
    simp [hv]
  have hμ : ∀ i, μ i ≠ 0 := by
    intro i hi
    refine e.orthonormal.ne_zero i (hnd.1 _ fun w => ?_)
    rw [hb_eq]
    exact Finset.sum_eq_zero fun j _ => by
      by_cases hij : j = i
      · simp [hij, hi]
      · simp [e.repr_self, PiLp.single_apply, hij]
  -- the subspace where the coordinates with eigenvalue in `S` vanish
  let Q : (ℝ → Prop) → Submodule ℝ E := fun S =>
    ⨅ (i) (_ : S (μ i)), LinearMap.ker (e.toBasis.coord i)
  have hQ : ∀ S v, v ∈ Q S ↔ ∀ i, S (μ i) → e.repr v i = 0 := by
    intro S v
    simp [Q, Submodule.mem_iInf, Basis.coord_apply, OrthonormalBasis.coe_toBasis_repr_apply]
  have hQe : ∀ S i, ¬ S (μ i) → e i ∈ Q S := by
    intro S i hi
    rw [hQ]
    intro j hj
    have hji : j ≠ i := fun h => hi (h ▸ hj)
    simp [e.repr_self, PiLp.single_apply, hji]
  have hQinv : ∀ S g, Q S ≤ (Q S).comap (ρ g) := by
    intro S g v hv
    rw [Submodule.mem_comap, hQ]
    intro i hi
    have hw : T (ρ g⁻¹ (e i)) = μ i • ρ g⁻¹ (e i) := by
      rw [hcomm, hTs.apply_eigenvectorBasis]
      simp
      rfl
    rw [e.repr_apply_apply, ← hρ g⁻¹, ρ.inv_self_apply, ← e.sum_inner_mul_inner]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : μ j = μ i
    · rw [← e.repr_apply_apply, (hQ S v).mp hv j (hj ▸ hi), mul_zero]
    · rw [real_inner_comm, ← e.repr_apply_apply, hcoord _ _ hw j hj, zero_mul]
  refine ⟨{
    pos := Q (· ≤ 0)
    neg := Q (0 ≤ ·)
    isCompl := ⟨?_, ?_⟩
    pos_le_comap := hQinv (· ≤ 0)
    neg_le_comap := hQinv (0 ≤ ·)
    posDefOn := ?_
    negDefOn := ?_
    orthogonal := ?_ }⟩
  · rw [Submodule.disjoint_def]
    intro v hP hN
    exact hzero v fun i => (le_total (μ i) 0).elim ((hQ (· ≤ 0) v).mp hP i) ((hQ (0 ≤ ·) v).mp hN i)
  · refine codisjoint_iff_le_sup.mpr fun v _ => ?_
    rw [← e.sum_repr v]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    rcases (hμ i).lt_or_gt with h | h
    · exact Submodule.mem_sup_right (hQe (0 ≤ ·) i h.not_ge)
    · exact Submodule.mem_sup_left (hQe (· ≤ 0) i h.not_ge)
  · intro v hv hv0
    rw [hQ (· ≤ 0)] at hv
    obtain ⟨i, hi⟩ : ∃ i, e.repr v i ≠ 0 := by
      by_contra! h
      exact hv0 (hzero v h)
    rw [hb_eq]
    refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
    · rcases le_or_gt (μ j) 0 with h | h
      · simp [hv j h]
      · exact mul_nonneg h.le (mul_self_nonneg _)
    · have h : 0 < μ i := lt_of_not_ge fun h => hi (hv i h)
      exact mul_pos h (mul_self_pos.mpr hi)
  · intro v hv hv0
    rw [hQ (0 ≤ ·)] at hv
    obtain ⟨i, hi⟩ : ∃ i, e.repr v i ≠ 0 := by
      by_contra! h
      exact hv0 (hzero v h)
    rw [LinearMap.neg_apply, LinearMap.neg_apply, hb_eq, ← Finset.sum_neg_distrib]
    refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
    · rcases le_or_gt 0 (μ j) with h | h
      · simp [hv j h]
      · nlinarith [mul_self_nonneg (e.repr v j)]
    · have h : μ i < 0 := lt_of_not_ge fun h => hi (hv i h)
      nlinarith [mul_self_pos.mpr hi]
  · intro v hv w hw
    rw [hQ (· ≤ 0)] at hv
    rw [hQ (0 ≤ ·)] at hw
    rw [hb_eq]
    refine Finset.sum_eq_zero fun j _ => ?_
    rcases le_total (μ j) 0 with h | h
    · simp [hv j h]
    · simp [hw j h]

/-- Existence of an invariant signature decomposition for a finite group: average an inner
product over `G`, then take spectral subspaces of the `b`-operator. -/
theorem exists_signatureDecomposition [Finite G] {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (ρ : Representation ℝ G V) {b : BilinForm ℝ V} (hb : b.IsSymm)
    (hnd : b.Nondegenerate) (hinv : ∀ g v w, b (ρ g v) (ρ g w) = b v w) :
    Nonempty (SignatureDecomposition ρ b) := by
  classical
  have := Fintype.ofFinite G
  set B := Module.finBasis ℝ V
  set q : V → V → ℝ := fun v w => ∑ g : G, ∑ i, B.repr (ρ g v) i * B.repr (ρ g w) i
  have hq_inv : ∀ h v w, q (ρ h v) (ρ h w) = q v w := by
    intro h v w
    simp only [q, ← Module.End.mul_apply, ← map_mul]
    exact Fintype.sum_equiv (Equiv.mulRight h) _ _ fun g => rfl
  have hq_nonneg : ∀ v, 0 ≤ q v v := fun v =>
    Finset.sum_nonneg fun g _ => Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hq_def : ∀ v, q v v = 0 → v = 0 := by
    intro v hv
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun g _ =>
      Finset.sum_nonneg fun i _ => mul_self_nonneg _).mp hv 1 (Finset.mem_univ _)
    have h2 : ∀ i, B.repr v i = 0 := fun i => by
      have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_self_nonneg _).mp h1 i
        (Finset.mem_univ _)
      simpa using this
    exact B.repr.injective (by ext i; simp [h2])
  letI core : InnerProductSpace.Core ℝ V :=
    { inner := q
      conj_inner_symm := fun v w => by simp [q, mul_comm]
      re_inner_nonneg := fun v => by simpa using hq_nonneg v
      add_left := fun u v w => by simp [q, add_mul, Finset.sum_add_distrib]
      smul_left := fun u v r => by simp [q, Finset.mul_sum, mul_assoc]
      definite := hq_def }
  letI : NormedAddCommGroup V := @InnerProductSpace.Core.toNormedAddCommGroup ℝ V _ _ _ core
  letI : InnerProductSpace ℝ V := InnerProductSpace.ofCore core.toCore
  exact exists_signatureDecomposition_of_inner ρ hq_inv hb hnd hinv

end Existence

section Sign

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℝ V]

open Classical in
/-- The equivariant signature `Sign_G(V, b) : G → ℂ` of manuscript (3.1): the character of any
invariant signature decomposition (`0` if there is none, which cannot happen for finite `G`
and nondegenerate `b`). -/
def equivariantSignature (ρ : Representation ℝ G V) (b : BilinForm ℝ V) : G → ℂ :=
  if h : Nonempty (SignatureDecomposition ρ b) then h.some.character else 0

variable [FiniteDimensional ℝ V] {ρ : Representation ℝ G V} {b : BilinForm ℝ V}

theorem equivariantSignature_eq (d : SignatureDecomposition ρ b) :
    equivariantSignature ρ b = d.character := by
  rw [equivariantSignature, dite_eq_left ⟨d⟩]
  exact SignatureDecomposition.character_eq _ _

theorem equivariantSignature_one [Finite G] (hb : b.IsSymm) (hnd : b.Nondegenerate)
    (hinv : ∀ g v w, b (ρ g v) (ρ g w) = b v w) : equivariantSignature ρ b 1 = signature b := by
  obtain ⟨d⟩ := exists_signatureDecomposition ρ hb hnd hinv
  rw [equivariantSignature_eq d, d.character_one]

/-- Manuscript Lemma 3.1: for `G` of order `p ^ a` with `a ≥ 1` (e.g. `G = C_{p^a} = ⟨g⟩`),
`Sign_G(V, b)(g) = 0` implies `p ∣ σ(V, b)`. -/
theorem prime_dvd_signature_of_equivariantSignature_eq_zero [Fintype G] (hb : b.IsSymm)
    (hnd : b.Nondegenerate) (hinv : ∀ g v w, b (ρ g v) (ρ g w) = b v w) {p k : ℕ}
    (hp : p.Prime) (hG : Fintype.card G = p ^ (k + 1)) {g : G}
    (h : equivariantSignature ρ b g = 0) : (p : ℤ) ∣ signature b := by
  obtain ⟨d⟩ := exists_signatureDecomposition ρ hb hnd hinv
  rw [equivariantSignature_eq d] at h
  exact d.prime_dvd_signature hp (hG ▸ pow_card_eq_one) h

end Sign

section Rational

open TensorProduct

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℚ V]

/-- The real representation `V_ℝ = ℝ ⊗[ℚ] V` of a rational representation. -/
@[simps]
def realRep (ρ : Representation ℚ G V) : Representation ℝ G (ℝ ⊗[ℚ] V) where
  toFun g := (ρ g).baseChange ℝ
  map_one' := by rw [map_one, LinearMap.baseChange_one]
  map_mul' g h := by rw [map_mul, LinearMap.baseChange_mul]

theorem baseChange_invariant {ρ : Representation ℚ G V} {b : BilinForm ℚ V}
    (hinv : ∀ g v w, b (ρ g v) (ρ g w) = b v w) (g : G) (x y : ℝ ⊗[ℚ] V) :
    BilinForm.baseChange ℝ b (realRep ρ g x) (realRep ρ g y) = BilinForm.baseChange ℝ b x y := by
  induction x using TensorProduct.inductionOn with
  | tmul a v =>
    induction y using TensorProduct.inductionOn with
    | tmul a' w => simp [hinv]
    | add y y' hy hy' => simp only [map_add, hy, hy']
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']

theorem isSymm_baseChange_real {b : BilinForm ℚ V} (hb : b.IsSymm) :
    LinearMap.BilinForm.IsSymm (BilinForm.baseChange ℝ b) :=
  LinearMap.BilinForm.isSymm_iff.mpr
    (LinearMap.BilinForm.IsSymm.baseChange ℝ (LinearMap.BilinForm.isSymm_iff.mp hb))

theorem nondegenerate_baseChange_real [FiniteDimensional ℚ V] {b : BilinForm ℚ V}
    (hnd : b.Nondegenerate) : (BilinForm.baseChange ℝ b).Nondegenerate := by
  classical
  set B := Module.finBasis ℚ V
  rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero B] at hnd
  rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (B.baseChange ℝ)]
  have hM : LinearMap.BilinForm.toMatrix (B.baseChange ℝ) (BilinForm.baseChange ℝ b) =
      (algebraMap ℚ ℝ).mapMatrix (LinearMap.BilinForm.toMatrix B b) := by
    ext i j
    simp [LinearMap.BilinForm.toMatrix_apply, Algebra.smul_def]
  rw [hM, ← RingHom.map_det]
  exact (map_ne_zero _).mpr hnd

/-- `Sign_G(V, b)` of a rational invariant form, manuscript (3.1), computed on `V_ℝ`. -/
def ratEquivariantSignature (ρ : Representation ℚ G V) (b : BilinForm ℚ V) : G → ℂ :=
  equivariantSignature (realRep ρ) (BilinForm.baseChange ℝ b)

/-- The signature `σ(V, b)` of a rational symmetric form. -/
def ratSignature (b : BilinForm ℚ V) : ℤ :=
  signature (BilinForm.baseChange ℝ b)

variable [FiniteDimensional ℚ V] {ρ : Representation ℚ G V} {b : BilinForm ℚ V}

theorem ratEquivariantSignature_one [Finite G] (hb : b.IsSymm) (hnd : b.Nondegenerate)
    (hinv : ∀ g v w, b (ρ g v) (ρ g w) = b v w) :
    ratEquivariantSignature ρ b 1 = ratSignature b :=
  equivariantSignature_one (isSymm_baseChange_real hb) (nondegenerate_baseChange_real hnd)
    (baseChange_invariant hinv)

/-- Manuscript Lemma 3.1 with rational coefficients: for `|G| = p ^ a`, `a ≥ 1`
(e.g. `G = C_{p^a} = ⟨g⟩`), `Sign_G(V, b)(g) = 0` implies `p ∣ σ(V, b)`. -/
theorem prime_dvd_ratSignature [Fintype G] (hb : b.IsSymm) (hnd : b.Nondegenerate)
    (hinv : ∀ g v w, b (ρ g v) (ρ g w) = b v w) {p k : ℕ} (hp : p.Prime)
    (hG : Fintype.card G = p ^ (k + 1)) {g : G} (h : ratEquivariantSignature ρ b g = 0) :
    (p : ℤ) ∣ ratSignature b :=
  prime_dvd_signature_of_equivariantSignature_eq_zero (isSymm_baseChange_real hb)
    (nondegenerate_baseChange_real hnd) (baseChange_invariant hinv) hp hG h

end Rational

end HSFormal
