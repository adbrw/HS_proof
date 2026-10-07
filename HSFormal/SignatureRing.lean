import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.RingTheory.Flat.Basic
import HSFormal.EquivariantSignature

/-!
# Algebraic laws of the equivariant signature (manuscript §3, §6)

The basic tool is a *signature involution* `J` (`J = ±1` on `V^±`): every invariant signature
decomposition gives one, and conversely, and `Sign_G(V, b)(g) = tr (g ∘ J)`
(`IsSignatureInvolution.equivariantSignature_apply`). From this:

* `equivariantSignature_congr`, `equivariantSignature_neg`, `equivariantSignature_orthSum`:
  isometry invariance, `Sign(-b) = -Sign(b)`, additivity under `b₁ ⊥ b₂`.
* `equivariantSignature_eq_zero_of_isotropic`, `equivariantSignature_eq_zero_of_orthogonal_eq`:
  vanishing on metabolic forms; `equivariantSignature_eq_of_isotropic_orthSum_neg`: Witt
  invariance, so `Sign_G` is well defined on the equivariant Witt group.
* `equivariantSignature_tprod`: `Sign(b ⊗ c) = Sign(b) · χ_W` for positive definite `c`;
  `trace_ofMulAction_quotient`: `χ_τ = [G : K] · 1_K` for `τ = k[G/K]`, `K` normal;
  `equivariantSignature_tprod_perm`.
* `hermForm`, `trOne_hermForm`, `forgetForm_hermForm`, `hermForm_forgetForm`,
  `regMatrix_transpose`, `regMatrix_mul`, `toMatrix_eq_regMatrix`: the trace correspondence
  (3.2), with the unnormalized trace `tr₁`.
* `map_nu_pow`, `prime_dvd_signature_of_annihilation`, `prime_dvd_signature_of_nu_pow_eq_zero`:
  the character step of Theorem 6.3.
* `ratEquivariantSignature_*`, `prime_dvd_ratSignature_of_annihilation`: rational versions.
-/

noncomputable section

open Module Submodule TensorProduct
open LinearMap (BilinForm)

namespace HSFormal

section Involution

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℝ V]

/-- `J` is a signature involution of `(V, b)`: an equivariant `b`-self-adjoint involution with
`b (J ·) ·` positive definite, i.e. `J = ±1` on `V^±`. -/
structure IsSignatureInvolution (ρ : Representation ℝ G V) (b : BilinForm ℝ V)
    (J : V →ₗ[ℝ] V) : Prop where
  apply_apply : ∀ v, J (J v) = v
  comm : ∀ g v, J (ρ g v) = ρ g (J v)
  selfAdjoint : ∀ v w, b (J v) w = b v (J w)
  posDef : ∀ v, v ≠ 0 → 0 < b (J v) v

theorem trace_restrict_eq [FiniteDimensional ℝ V] {P N : Submodule ℝ V} (h : IsCompl P N)
    (f : V →ₗ[ℝ] V) (hf : P ≤ P.comap f) :
    LinearMap.trace ℝ P (f.restrict hf) = LinearMap.trace ℝ V (f ∘ₗ P.projection N h) := by
  rw [Submodule.projection, ← LinearMap.comp_assoc, LinearMap.trace_comp_comm']
  congr 1
  ext x
  simp [Submodule.projectionOnto_apply_left h ⟨f x, hf x.2⟩]

namespace SignatureDecomposition

variable {ρ : Representation ℝ G V} {b : BilinForm ℝ V} (d : SignatureDecomposition ρ b)

/-- The involution `J = π⁺ - π⁻` of a signature decomposition. -/
def involution : V →ₗ[ℝ] V :=
  d.pos.projection d.neg d.isCompl - d.neg.projection d.pos d.isCompl.symm

theorem involution_apply (v : V) :
    d.involution v =
      d.pos.projection d.neg d.isCompl v - d.neg.projection d.pos d.isCompl.symm v :=
  rfl

theorem involution_of_mem_pos {v : V} (hv : v ∈ d.pos) : d.involution v = v := by
  rw [involution_apply, (projection_eq_self_iff d.isCompl _).mpr hv,
    (projection_apply_eq_zero_iff d.isCompl.symm).mpr hv, sub_zero]

theorem involution_of_mem_neg {v : V} (hv : v ∈ d.neg) : d.involution v = -v := by
  rw [involution_apply, (projection_eq_self_iff d.isCompl.symm _).mpr hv,
    (projection_apply_eq_zero_iff d.isCompl).mpr hv, zero_sub]

theorem exists_add (v : V) : ∃ a c, a ∈ d.pos ∧ c ∈ d.neg ∧ a + c = v :=
  ⟨_, _, projection_apply_mem d.isCompl v, projection_apply_mem d.isCompl.symm v,
    projection_add_projection_eq_self d.isCompl v⟩

theorem apply_involution_add (hb : b.IsSymm) {a c a' c' : V} (ha : a ∈ d.pos) (hc : c ∈ d.neg)
    (ha' : a' ∈ d.pos) (hc' : c' ∈ d.neg) :
    b (d.involution (a + c)) (a' + c') = b a a' - b c c' := by
  have h₁ := d.orthogonal a ha c' hc'
  have h₂ : b c a' = 0 := by rw [hb.eq]; exact d.orthogonal a' ha' c hc
  rw [map_add d.involution, d.involution_of_mem_pos ha, d.involution_of_mem_neg hc]
  simp only [map_add, map_neg, LinearMap.add_apply, LinearMap.neg_apply, h₁, h₂]
  ring

theorem isSignatureInvolution (hb : b.IsSymm) : IsSignatureInvolution ρ b d.involution := by
  refine ⟨fun v => ?_, fun g v => ?_, fun v w => ?_, fun v hv => ?_⟩
  · obtain ⟨a, c, ha, hc, rfl⟩ := d.exists_add v
    rw [map_add, d.involution_of_mem_pos ha, d.involution_of_mem_neg hc, map_add, map_neg,
      d.involution_of_mem_pos ha, d.involution_of_mem_neg hc, neg_neg]
  · simp only [involution_apply, map_sub,
      projection_map_of_le_comap d.isCompl _ (d.pos_le_comap g) (d.neg_le_comap g),
      projection_map_of_le_comap d.isCompl.symm _ (d.neg_le_comap g) (d.pos_le_comap g)]
  · obtain ⟨a, c, ha, hc, rfl⟩ := d.exists_add v
    obtain ⟨a', c', ha', hc', rfl⟩ := d.exists_add w
    rw [d.apply_involution_add hb ha hc ha' hc', hb.eq (a + c),
      d.apply_involution_add hb ha' hc' ha hc,
      hb.eq a', hb.eq c']
  · obtain ⟨a, c, ha, hc, rfl⟩ := d.exists_add v
    rw [d.apply_involution_add hb ha hc ha hc]
    have hc' : ∀ h : c ≠ 0, 0 < -b c c := fun h => by simpa using d.negDefOn c hc h
    by_cases h : a = 0
    · subst h
      have := hc' fun h => hv (by simp [h])
      simp only [map_zero]
      linarith
    · have := d.posDefOn a ha h
      by_cases h' : c = 0
      · simp [h', this]
      · linarith [hc' h']

theorem character_eq_trace [FiniteDimensional ℝ V] (g : G) :
    d.character g = ((LinearMap.trace ℝ V (ρ g ∘ₗ d.involution) : ℝ) : ℂ) := by
  have h₁ := trace_restrict_eq d.isCompl (ρ g) (d.pos_le_comap g)
  have h₂ := trace_restrict_eq d.isCompl.symm (ρ g) (d.neg_le_comap g)
  rw [character, posChar, negChar]
  erw [h₁, h₂]
  rw [involution, LinearMap.comp_sub, map_sub]

end SignatureDecomposition

namespace IsSignatureInvolution

variable {ρ : Representation ℝ G V} {b : BilinForm ℝ V} {J : V →ₗ[ℝ] V}

theorem mem_ker_sub_id {v : V} : v ∈ LinearMap.ker (J - LinearMap.id) ↔ J v = v := by
  simp [sub_eq_zero]

theorem mem_ker_add_id {v : V} : v ∈ LinearMap.ker (J + LinearMap.id) ↔ J v = -v := by
  simp [add_eq_zero_iff_eq_neg]

/-- The signature decomposition `V^± = ker (J ∓ 1)` of a signature involution. -/
def decomposition (hJ : IsSignatureInvolution ρ b J) : SignatureDecomposition ρ b where
  pos := LinearMap.ker (J - LinearMap.id)
  neg := LinearMap.ker (J + LinearMap.id)
  isCompl := by
    refine ⟨Submodule.disjoint_def.mpr fun v h₁ h₂ => ?_, codisjoint_iff_le_sup.mpr fun v _ => ?_⟩
    · rw [mem_ker_sub_id] at h₁
      rw [mem_ker_add_id, h₁] at h₂
      have h : (2 : ℝ) • v = 0 := by rw [two_smul]; nth_rw 2 [h₂]; exact add_neg_cancel v
      exact (smul_eq_zero.mp h).resolve_left two_ne_zero
    · refine Submodule.mem_sup.mpr ⟨(1 / 2 : ℝ) • (v + J v), ?_, (1 / 2 : ℝ) • (v - J v), ?_, ?_⟩
      · rw [mem_ker_sub_id, map_smul, map_add, hJ.apply_apply, add_comm]
      · rw [mem_ker_add_id, map_smul, map_sub, hJ.apply_apply, ← smul_neg, neg_sub]
      · rw [← smul_add, add_add_sub_cancel, ← two_smul ℝ, smul_smul]
        norm_num
  pos_le_comap g v hv := by
    rw [Submodule.mem_comap, mem_ker_sub_id, hJ.comm, mem_ker_sub_id.mp hv]
  neg_le_comap g v hv := by
    rw [Submodule.mem_comap, mem_ker_add_id, hJ.comm, mem_ker_add_id.mp hv, map_neg]
  posDefOn v hv h := by
    simpa [mem_ker_sub_id.mp hv] using hJ.posDef v h
  negDefOn v hv h := by
    simpa [mem_ker_add_id.mp hv] using hJ.posDef v h
  orthogonal v hv w hw := by
    have := hJ.selfAdjoint v w
    rw [mem_ker_sub_id.mp hv, mem_ker_add_id.mp hw, map_neg] at this
    linarith

theorem involution_decomposition (hJ : IsSignatureInvolution ρ b J) :
    hJ.decomposition.involution = J := by
  ext v
  obtain ⟨a, c, ha, hc, rfl⟩ := hJ.decomposition.exists_add v
  rw [map_add, map_add, hJ.decomposition.involution_of_mem_pos ha,
    hJ.decomposition.involution_of_mem_neg hc, mem_ker_sub_id.mp ha, mem_ker_add_id.mp hc]

/-- The equivariant signature is the character `g ↦ tr (g ∘ J)` of any signature involution. -/
theorem equivariantSignature_apply [FiniteDimensional ℝ V] (hJ : IsSignatureInvolution ρ b J)
    (g : G) : equivariantSignature ρ b g = ((LinearMap.trace ℝ V (ρ g ∘ₗ J) : ℝ) : ℂ) := by
  rw [equivariantSignature_eq hJ.decomposition, SignatureDecomposition.character_eq_trace,
    involution_decomposition]

/-- A form admitting a signature involution is nondegenerate. -/
theorem nondegenerate (hJ : IsSignatureInvolution ρ b J) : b.Nondegenerate := by
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · by_contra h
    have := hJ.posDef v h
    rw [hJ.selfAdjoint, hv] at this
    exact lt_irrefl _ this
  · by_contra h
    have := hJ.posDef v h
    rw [hv] at this
    exact lt_irrefl _ this

end IsSignatureInvolution

end Involution

section Laws

variable {G : Type*} [Group G]

/-- A symmetric nondegenerate `G`-invariant bilinear form, the input of manuscript (3.1). -/
structure IsInvariantForm {k V : Type*} [CommRing k] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (b : BilinForm k V) : Prop where
  isSymm : b.IsSymm
  nondegenerate : b.Nondegenerate
  map_map : ∀ g v w, b (ρ g v) (ρ g w) = b v w

/-- The orthogonal sum `b₁ ⊥ b₂` on `V₁ × V₂`. -/
def orthSum {k V₁ V₂ : Type*} [CommRing k] [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂]
    [Module k V₂] (b₁ : BilinForm k V₁) (b₂ : BilinForm k V₂) : BilinForm k (V₁ × V₂) :=
  b₁.compl₁₂ (LinearMap.fst k V₁ V₂) (LinearMap.fst k V₁ V₂) +
    b₂.compl₁₂ (LinearMap.snd k V₁ V₂) (LinearMap.snd k V₁ V₂)

@[simp]
theorem orthSum_apply {k V₁ V₂ : Type*} [CommRing k] [AddCommGroup V₁] [Module k V₁]
    [AddCommGroup V₂] [Module k V₂] (b₁ : BilinForm k V₁) (b₂ : BilinForm k V₂)
    (x y : V₁ × V₂) : orthSum b₁ b₂ x y = b₁ x.1 y.1 + b₂ x.2 y.2 :=
  rfl

namespace IsInvariantForm

variable {k V₁ V₂ : Type*} [CommRing k] [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂]
  [Module k V₂] {ρ₁ : Representation k G V₁} {ρ₂ : Representation k G V₂}
  {b₁ : BilinForm k V₁} {b₂ : BilinForm k V₂}

theorem neg (h : IsInvariantForm ρ₁ b₁) : IsInvariantForm ρ₁ (-b₁) where
  isSymm := ⟨fun x y => by simp [h.isSymm.eq x y]⟩
  nondegenerate := ⟨fun x hx => h.nondegenerate.1 x fun y => by simpa using hx y,
    fun x hx => h.nondegenerate.2 x fun y => by simpa using hx y⟩
  map_map g v w := by simp [h.map_map]

theorem orthSum (h₁ : IsInvariantForm ρ₁ b₁) (h₂ : IsInvariantForm ρ₂ b₂) :
    IsInvariantForm (ρ₁.prod ρ₂) (orthSum b₁ b₂) where
  isSymm := ⟨fun x y => by simp [h₁.isSymm.eq x.1, h₂.isSymm.eq x.2]⟩
  nondegenerate := ⟨fun x hx => Prod.ext
      (h₁.nondegenerate.1 x.1 fun y => by simpa using hx (y, 0))
      (h₂.nondegenerate.1 x.2 fun y => by simpa using hx (0, y)),
    fun x hx => Prod.ext
      (h₁.nondegenerate.2 x.1 fun y => by simpa using hx (y, 0))
      (h₂.nondegenerate.2 x.2 fun y => by simpa using hx (0, y))⟩
  map_map g v w := by simp [h₁.map_map, h₂.map_map]

end IsInvariantForm

variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup V₁] [Module ℝ V₁]
  [AddCommGroup V₂] [Module ℝ V₂]
  {ρ : Representation ℝ G V} {ρ₁ : Representation ℝ G V₁} {ρ₂ : Representation ℝ G V₂}
  {b : BilinForm ℝ V} {b₁ : BilinForm ℝ V₁} {b₂ : BilinForm ℝ V₂} {J : V →ₗ[ℝ] V}

namespace IsSignatureInvolution

theorem nonneg (hJ : IsSignatureInvolution ρ b J) (v : V) : 0 ≤ b (J v) v := by
  by_cases h : v = 0
  · simp [h]
  · exact (hJ.posDef v h).le

theorem congr {J : V₁ →ₗ[ℝ] V₁} (hJ : IsSignatureInvolution ρ₁ b₁ J) (e : V₁ ≃ₗ[ℝ] V₂)
    (he : ∀ g v, e (ρ₁ g v) = ρ₂ g (e v)) (hbe : ∀ v w, b₂ (e v) (e w) = b₁ v w) :
    IsSignatureInvolution ρ₂ b₂ (e.conj J) := by
  have he' : ∀ g v, e.symm (ρ₂ g v) = ρ₁ g (e.symm v) := fun g v => by
    rw [LinearEquiv.symm_apply_eq, he, LinearEquiv.apply_symm_apply]
  refine ⟨fun v => ?_, fun g v => ?_, fun v w => ?_, fun v hv => ?_⟩
  · simp [hJ.apply_apply]
  · simp [he', hJ.comm, he]
  · rw [LinearEquiv.conj_apply_apply, LinearEquiv.conj_apply_apply, ← e.apply_symm_apply w, hbe,
      ← e.apply_symm_apply v, hbe, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply,
      hJ.selfAdjoint]
  · rw [LinearEquiv.conj_apply_apply, ← e.apply_symm_apply v, hbe, LinearEquiv.symm_apply_apply]
    exact hJ.posDef _ (by simpa using hv)

theorem neg (hJ : IsSignatureInvolution ρ b J) : IsSignatureInvolution ρ (-b) (-J) :=
  ⟨fun v => by simp [hJ.apply_apply], fun g v => by simp [hJ.comm],
    fun v w => by simp [hJ.selfAdjoint], fun v hv => by simpa using hJ.posDef v hv⟩

theorem smul (hJ : IsSignatureInvolution ρ b J) {c : ℝ} (hc : 0 < c) :
    IsSignatureInvolution ρ (c • b) J :=
  ⟨hJ.apply_apply, hJ.comm, fun v w => by simp [hJ.selfAdjoint],
    fun v hv => by simpa using mul_pos hc (hJ.posDef v hv)⟩

theorem prodMap {J₁ : V₁ →ₗ[ℝ] V₁} {J₂ : V₂ →ₗ[ℝ] V₂} (hJ₁ : IsSignatureInvolution ρ₁ b₁ J₁)
    (hJ₂ : IsSignatureInvolution ρ₂ b₂ J₂) :
    IsSignatureInvolution (ρ₁.prod ρ₂) (orthSum b₁ b₂) (J₁.prodMap J₂) := by
  refine ⟨fun v => ?_, fun g v => ?_, fun v w => ?_, fun v hv => ?_⟩
  · simp [hJ₁.apply_apply, hJ₂.apply_apply]
  · simp [hJ₁.comm, hJ₂.comm]
  · simp [hJ₁.selfAdjoint, hJ₂.selfAdjoint]
  · simp only [LinearMap.prodMap_apply, orthSum_apply]
    by_cases h : v.1 = 0
    · have h₂ : v.2 ≠ 0 := fun h₂ => hv (Prod.ext h h₂)
      linarith [hJ₁.nonneg v.1, hJ₂.posDef _ h₂]
    · linarith [hJ₁.posDef _ h, hJ₂.nonneg v.2]

end IsSignatureInvolution

theorem posDefOn_smul_iff {c : ℝ} (hc : 0 < c) {W : Submodule ℝ V} :
    PosDefOn (c • b) W ↔ PosDefOn b W := by
  simp only [PosDefOn, LinearMap.smul_apply, smul_eq_mul, mul_pos_iff_of_pos_left hc]

/-- The ordinary signature is invariant under positive rescaling (e.g. by `1 / |G|`). -/
theorem signature_smul {c : ℝ} (hc : 0 < c) (b : BilinForm ℝ V) :
    signature (c • b) = signature b := by
  have h : -(c • b) = c • -b := by ext; simp
  rw [signature, signature, h]
  simp only [posIndex, posDefOn_smul_iff hc]

variable [FiniteDimensional ℝ V] [FiniteDimensional ℝ V₁] [FiniteDimensional ℝ V₂]

theorem IsInvariantForm.exists_isSignatureInvolution [Finite G] (hb : IsInvariantForm ρ b) :
    ∃ J, IsSignatureInvolution ρ b J :=
  let ⟨d⟩ := exists_signatureDecomposition ρ hb.isSymm hb.nondegenerate hb.map_map
  ⟨d.involution, d.isSignatureInvolution hb.isSymm⟩

theorem IsSignatureInvolution.equivariantSignature_congr {J : V₁ →ₗ[ℝ] V₁}
    (hJ : IsSignatureInvolution ρ₁ b₁ J) (e : V₁ ≃ₗ[ℝ] V₂)
    (he : ∀ g v, e (ρ₁ g v) = ρ₂ g (e v)) (hbe : ∀ v w, b₂ (e v) (e w) = b₁ v w) :
    equivariantSignature ρ₂ b₂ = equivariantSignature ρ₁ b₁ := by
  funext g
  rw [(hJ.congr e he hbe).equivariantSignature_apply, hJ.equivariantSignature_apply,
    ← LinearMap.trace_conj' _ e]
  congr 3
  ext v
  simp [he]

/-- `Sign_G` is an isometry invariant. -/
theorem equivariantSignature_congr [Finite G] (hb₁ : IsInvariantForm ρ₁ b₁) (e : V₁ ≃ₗ[ℝ] V₂)
    (he : ∀ g v, e (ρ₁ g v) = ρ₂ g (e v)) (hbe : ∀ v w, b₂ (e v) (e w) = b₁ v w) :
    equivariantSignature ρ₂ b₂ = equivariantSignature ρ₁ b₁ :=
  let ⟨_, hJ⟩ := hb₁.exists_isSignatureInvolution
  hJ.equivariantSignature_congr e he hbe

theorem equivariantSignature_neg [Finite G] (hb : IsInvariantForm ρ b) :
    equivariantSignature ρ (-b) = -equivariantSignature ρ b := by
  obtain ⟨J, hJ⟩ := hb.exists_isSignatureInvolution
  funext g
  rw [hJ.neg.equivariantSignature_apply, Pi.neg_apply, hJ.equivariantSignature_apply,
    LinearMap.comp_neg, map_neg, Complex.ofReal_neg]

theorem equivariantSignature_smul [Finite G] (hb : IsInvariantForm ρ b) {c : ℝ} (hc : 0 < c) :
    equivariantSignature ρ (c • b) = equivariantSignature ρ b := by
  obtain ⟨J, hJ⟩ := hb.exists_isSignatureInvolution
  funext g
  rw [(hJ.smul hc).equivariantSignature_apply, hJ.equivariantSignature_apply]

/-- Additivity of `Sign_G` under orthogonal sums. -/
theorem equivariantSignature_orthSum [Finite G] (hb₁ : IsInvariantForm ρ₁ b₁)
    (hb₂ : IsInvariantForm ρ₂ b₂) :
    equivariantSignature (ρ₁.prod ρ₂) (orthSum b₁ b₂) =
      equivariantSignature ρ₁ b₁ + equivariantSignature ρ₂ b₂ := by
  obtain ⟨J₁, hJ₁⟩ := hb₁.exists_isSignatureInvolution
  obtain ⟨J₂, hJ₂⟩ := hb₂.exists_isSignatureInvolution
  funext g
  rw [(hJ₁.prodMap hJ₂).equivariantSignature_apply, Pi.add_apply, hJ₁.equivariantSignature_apply,
    hJ₂.equivariantSignature_apply, ← Complex.ofReal_add, ← LinearMap.trace_prodMap']
  rfl

/-- Manuscript §3: `Sign_G` vanishes on metabolic forms, i.e. those with an invariant subspace
`L` on which `b` vanishes and with `2 dim L = dim V`. -/
theorem equivariantSignature_eq_zero_of_isotropic [Finite G] (hb : IsInvariantForm ρ b)
    {L : Submodule ℝ V} (hL : ∀ g, L ≤ L.comap (ρ g)) (hiso : ∀ v ∈ L, ∀ w ∈ L, b v w = 0)
    (hdim : 2 * finrank ℝ L = finrank ℝ V) : equivariantSignature ρ b = 0 := by
  obtain ⟨d⟩ := exists_signatureDecomposition ρ hb.isSymm hb.nondegenerate hb.map_map
  have hneg : Disjoint L d.neg := Submodule.disjoint_def.mpr fun v hvL hvN => by
    by_contra h
    simpa [hiso v hvL v hvL] using d.negDefOn v hvN h
  have hpos : Disjoint L d.pos := Submodule.disjoint_def.mpr fun v hvL hvP => by
    by_contra h
    simpa [hiso v hvL v hvL] using d.posDefOn v hvP h
  have h₁ := Submodule.finrank_sup_add_finrank_inf_eq L d.neg
  have h₂ := Submodule.finrank_sup_add_finrank_inf_eq L d.pos
  rw [hneg.eq_bot, finrank_bot] at h₁
  rw [hpos.eq_bot, finrank_bot] at h₂
  have := Submodule.finrank_le (L ⊔ d.neg)
  have := Submodule.finrank_le (L ⊔ d.pos)
  have := Submodule.finrank_add_eq_of_isCompl d.isCompl
  funext g
  rw [equivariantSignature_eq d]
  have hp := trace_subrepresentation_eq hL d.pos_le_comap d.neg_le_comap d.isCompl hneg
    (by omega) g
  have hn := trace_subrepresentation_eq hL d.neg_le_comap d.pos_le_comap d.isCompl.symm hpos
    (by omega) g
  simp only [SignatureDecomposition.character, SignatureDecomposition.posChar,
    SignatureDecomposition.negChar, ← hp, ← hn, sub_self, Complex.ofReal_zero, Pi.zero_apply]

/-- `Sign_G` vanishes on forms with an invariant Lagrangian `L = L^⊥`. -/
theorem equivariantSignature_eq_zero_of_orthogonal_eq [Finite G] (hb : IsInvariantForm ρ b)
    {L : Submodule ℝ V} (hL : ∀ g, L ≤ L.comap (ρ g)) (hLL : b.orthogonal L = L) :
    equivariantSignature ρ b = 0 := by
  refine equivariantSignature_eq_zero_of_isotropic hb hL
    (fun v hv w hw => LinearMap.BilinForm.mem_orthogonal_iff.mp (by rw [hLL]; exact hw) v hv) ?_
  have h := LinearMap.BilinForm.finrank_add_finrank_orthogonal hb.isSymm.isRefl L
  have htop : L ⊓ b.orthogonal ⊤ = ⊥ := by
    refine eq_bot_iff.mpr fun v hv => (Submodule.mem_bot ℝ).mpr (hb.nondegenerate.1 v fun w => ?_)
    rw [hb.isSymm.eq]
    exact (Submodule.mem_inf.mp hv).2 w Submodule.mem_top
  rw [htop, hLL, finrank_bot] at h
  omega

/-- Witt invariance of `Sign_G`: if `b₁ ⊥ (-b₂)` is metabolic, then
`Sign_G(V₁, b₁) = Sign_G(V₂, b₂)`. With additivity this makes `Sign_G` a homomorphism on the
equivariant Witt group. -/
theorem equivariantSignature_eq_of_isotropic_orthSum_neg [Finite G]
    (hb₁ : IsInvariantForm ρ₁ b₁) (hb₂ : IsInvariantForm ρ₂ b₂) {L : Submodule ℝ (V₁ × V₂)}
    (hL : ∀ g, L ≤ L.comap (ρ₁.prod ρ₂ g))
    (hiso : ∀ v ∈ L, ∀ w ∈ L, orthSum b₁ (-b₂) v w = 0)
    (hdim : 2 * finrank ℝ L = finrank ℝ V₁ + finrank ℝ V₂) :
    equivariantSignature ρ₁ b₁ = equivariantSignature ρ₂ b₂ := by
  have h := equivariantSignature_eq_zero_of_isotropic (hb₁.orthSum hb₂.neg) hL hiso
    (by rw [Module.finrank_prod]; exact hdim)
  rw [equivariantSignature_orthSum hb₁ hb₂.neg, equivariantSignature_neg hb₂] at h
  exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h)

end Laws

section PosDef

variable {K V W : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup V]
  [Module K V] [AddCommGroup W] [Module K W]

theorem posDef_of_basis {ι : Type*} [Fintype ι] {B : BilinForm K V} (e : Basis ι K V)
    (ho : B.IsOrthoᵢ e) (hpos : ∀ i, 0 < B (e i) (e i)) (v : V) (hv : v ≠ 0) : 0 < B v v := by
  classical
  have hB : B v v = ∑ i, e.repr v i * e.repr v i * B (e i) (e i) := by
    have : B v v = B (∑ i, e.repr v i • e i) (∑ j, e.repr v j • e j) := by rw [e.sum_repr]
    rw [this]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [show B (e j) (e i) = 0 from ho hj])
      (by simp)]
    ring
  obtain ⟨i, hi⟩ : ∃ i, e.repr v i ≠ 0 := by
    by_contra! h
    exact hv (e.repr.injective (by ext i; simp [h]))
  rw [hB]
  exact Finset.sum_pos' (fun j _ => mul_nonneg (mul_self_nonneg _) (hpos j).le)
    ⟨i, Finset.mem_univ _, mul_pos (mul_self_pos.mpr hi) (hpos i)⟩

theorem exists_basis_isOrthoᵢ_pos [FiniteDimensional K V] {B : BilinForm K V} (hB : B.IsSymm)
    (hpos : ∀ v, v ≠ 0 → 0 < B v v) :
    ∃ e : Basis (Fin (finrank K V)) K V, B.IsOrthoᵢ e ∧ ∀ i, 0 < B (e i) (e i) := by
  haveI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  obtain ⟨e, he⟩ :=
    LinearMap.BilinForm.exists_orthogonal_basis (LinearMap.BilinForm.isSymm_iff.mp hB)
  exact ⟨e, he, fun i => hpos _ (e.ne_zero i)⟩

/-- The tensor product of positive definite symmetric forms is positive definite. -/
theorem posDef_tmul [FiniteDimensional K V] [FiniteDimensional K W] {B₁ : BilinForm K V}
    {B₂ : BilinForm K W} (h₁ : B₁.IsSymm) (h₂ : B₂.IsSymm) (hp₁ : ∀ v, v ≠ 0 → 0 < B₁ v v)
    (hp₂ : ∀ w, w ≠ 0 → 0 < B₂ w w) (x : V ⊗[K] W) (hx : x ≠ 0) : 0 < B₁.tmul B₂ x x := by
  obtain ⟨e, he, hpe⟩ := exists_basis_isOrthoᵢ_pos h₁ hp₁
  obtain ⟨f, hf, hpf⟩ := exists_basis_isOrthoᵢ_pos h₂ hp₂
  refine posDef_of_basis (e.tensorProduct f) ?_ (fun ij => ?_) x hx
  · rintro ⟨i, j⟩ ⟨i', j'⟩ hne
    change B₁.tmul B₂ (e.tensorProduct f (i, j)) (e.tensorProduct f (i', j')) = 0
    simp only [Basis.tensorProduct_apply, LinearMap.BilinForm.tensorDistrib_tmul, smul_eq_mul]
    by_cases hi : i = i'
    · subst hi
      rw [show B₂ (f j) (f j') = 0 from hf fun h => hne (by rw [h]), zero_mul]
    · rw [show B₁ (e i) (e i') = 0 from he hi, mul_zero]
  · simp only [Basis.tensorProduct_apply', LinearMap.BilinForm.tensorDistrib_tmul, smul_eq_mul]
    exact mul_pos (hpf _) (hpe _)

end PosDef

section Tensor

variable {G V W : Type*} [Group G] [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  {ρ : Representation ℝ G V} {σ : Representation ℝ G W} {b : BilinForm ℝ V}
  {c : BilinForm ℝ W} {J : V →ₗ[ℝ] V}

theorem tmul_compl₁₂_map (J : V →ₗ[ℝ] V) :
    (b.tmul c).compl₁₂ (TensorProduct.map J LinearMap.id) LinearMap.id =
      LinearMap.BilinForm.tmul (b.compl₁₂ J LinearMap.id) c :=
  TensorProduct.ext' fun _ _ => TensorProduct.ext' fun _ _ => by simp

theorem IsSignatureInvolution.map_id [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (hJ : IsSignatureInvolution ρ b J) (hb : b.IsSymm) (hc : c.IsSymm)
    (hcpos : ∀ w, w ≠ 0 → 0 < c w w) :
    IsSignatureInvolution (ρ.tprod σ) (b.tmul c) (TensorProduct.map J LinearMap.id) := by
  have hJJ : J ∘ₗ J = LinearMap.id := LinearMap.ext hJ.apply_apply
  have hJρ : ∀ g, J ∘ₗ ρ g = ρ g ∘ₗ J := fun g => LinearMap.ext (hJ.comm g)
  refine ⟨fun x => ?_, fun g x => ?_, fun x y => ?_, fun x hx => ?_⟩
  · rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, hJJ, LinearMap.id_comp,
      TensorProduct.map_id, LinearMap.id_apply]
  · rw [Representation.tprod_apply, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
      ← TensorProduct.map_comp, ← TensorProduct.map_comp, hJρ, LinearMap.id_comp,
      LinearMap.comp_id]
  · have key : (b.tmul c).compl₁₂ (TensorProduct.map J LinearMap.id) LinearMap.id =
        (b.tmul c).compl₁₂ LinearMap.id (TensorProduct.map J LinearMap.id) :=
      TensorProduct.ext' fun v w => TensorProduct.ext' fun v' w' => by
        simp [hJ.selfAdjoint]
    exact LinearMap.congr_fun₂ key x y
  · have h : b.tmul c (TensorProduct.map J LinearMap.id x) x =
        LinearMap.BilinForm.tmul (b.compl₁₂ J LinearMap.id) c x x :=
      LinearMap.congr_fun₂ (tmul_compl₁₂_map J) x x
    rw [h]
    refine posDef_tmul ⟨fun v w => ?_⟩ hc hJ.posDef hcpos x hx
    simp only [LinearMap.compl₁₂_apply, LinearMap.id_apply]
    rw [hJ.selfAdjoint, hb.eq]

/-- Manuscript §3: tensoring with a positive definite symmetric form `(W, c)` multiplies the
signature character by the character `χ_W` of `W`. -/
theorem equivariantSignature_tprod [Finite G] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (hb : IsInvariantForm ρ b) (hc : c.IsSymm) (hcpos : ∀ w, w ≠ 0 → 0 < c w w) (g : G) :
    equivariantSignature (ρ.tprod σ) (b.tmul c) g =
      equivariantSignature ρ b g * (LinearMap.trace ℝ W (σ g) : ℂ) := by
  obtain ⟨J, hJ⟩ := hb.exists_isSignatureInvolution
  rw [(hJ.map_id hb.isSymm hc hcpos).equivariantSignature_apply, hJ.equivariantSignature_apply,
    Representation.tprod_apply, ← TensorProduct.map_comp, LinearMap.comp_id,
    LinearMap.trace_tensorProduct', Complex.ofReal_mul]

theorem IsInvariantForm.tmul [Finite G] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (hb : IsInvariantForm ρ b) (hc : IsInvariantForm σ c) (hcpos : ∀ w, w ≠ 0 → 0 < c w w) :
    IsInvariantForm (ρ.tprod σ) (b.tmul c) where
  isSymm := LinearMap.BilinForm.isSymm_iff.mpr
    ((LinearMap.BilinForm.isSymm_iff.mp hb.isSymm).tmul
      (LinearMap.BilinForm.isSymm_iff.mp hc.isSymm))
  nondegenerate :=
    let ⟨_, hJ⟩ := hb.exists_isSignatureInvolution
    (hJ.map_id (σ := σ) hb.isSymm hc.isSymm hcpos).nondegenerate
  map_map g x y := by
    have key : (b.tmul c).compl₁₂ ((ρ.tprod σ) g) ((ρ.tprod σ) g) = b.tmul c :=
      TensorProduct.ext' fun v w => TensorProduct.ext' fun v' w' => by
        simp [hb.map_map, hc.map_map]
    exact LinearMap.congr_fun₂ key x y

end Tensor

section Permutation

open Representation

variable (k : Type*) {G : Type*} [Group G] (H : Type*) [MulAction G H] [Fintype H]

/-- The standard form `∑ₓ f x * f' x` on the permutation module `k[H]`, for which `H` is an
orthonormal basis (the form on `τ = ℚ[G/P]` in manuscript §6). -/
def permForm [CommRing k] : BilinForm k (MonoidAlgebra k H) :=
  ∑ x : H, (LinearMap.mul k k).compl₁₂ (Finsupp.lapply x ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap)
    (Finsupp.lapply x ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap)

variable {k H}

@[simp]
theorem permForm_apply [CommRing k] (f f' : MonoidAlgebra k H) :
    permForm k H f f' = ∑ x, f.coeff x * f'.coeff x := by
  simp [permForm]

theorem permForm_isSymm [CommRing k] : (permForm k H).IsSymm :=
  ⟨fun f f' => by simp [mul_comm]⟩

theorem isInvariantForm_permForm [CommRing k] :
    IsInvariantForm (ofMulAction k G H) (permForm k H) where
  isSymm := permForm_isSymm
  nondegenerate := by
    classical
    refine ⟨fun f hf => ?_, fun f hf => ?_⟩
    · ext y
      simpa [Finsupp.single_apply] using hf (MonoidAlgebra.single y 1)
    · ext y
      simpa [Finsupp.single_apply] using hf (MonoidAlgebra.single y 1)
  map_map g f f' := by
    simp only [permForm_apply, coeff_ofMulAction]
    exact Fintype.sum_equiv (MulAction.toPerm g⁻¹) _ _ fun x => rfl

theorem permForm_pos {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (f : MonoidAlgebra K H) (hf : f ≠ 0) : 0 < permForm K H f f := by
  obtain ⟨x, hx⟩ : ∃ x, f.coeff x ≠ 0 := by
    by_contra! h
    exact hf (MonoidAlgebra.ext (Finsupp.ext h))
  rw [permForm_apply]
  exact Finset.sum_pos' (fun y _ => mul_self_nonneg _) ⟨x, Finset.mem_univ _, mul_self_pos.mpr hx⟩

/-- The permutation character counts fixed points. -/
theorem trace_ofMulAction [CommRing k] [DecidableEq H] (g : G) :
    LinearMap.trace k (MonoidAlgebra k H) (ofMulAction k G H g) =
      ∑ x : H, if g • x = x then 1 else 0 := by
  rw [LinearMap.trace_eq_matrix_trace k (MonoidAlgebra.basis H k)]
  simp [Matrix.trace, LinearMap.toMatrix_apply, MonoidAlgebra.basis, Finsupp.single_apply]

theorem smul_eq_self_iff_mem {K : Subgroup G} [K.Normal] (g : G) (x : G ⧸ K) :
    g • x = x ↔ g ∈ K := by
  induction x using QuotientGroup.induction_on with
  | H a =>
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul, mul_inv_rev, mul_assoc,
      Subgroup.Normal.mem_comm_iff inferInstance, mul_inv_cancel_right, inv_mem_iff]

open Classical in
/-- The character of `τ = k[G/K]` for normal `K`: it is `[G : K]` on `K` and `0` off `K`. -/
theorem trace_ofMulAction_quotient [CommRing k] (K : Subgroup G) [K.Normal] [Fintype (G ⧸ K)]
    (g : G) : LinearMap.trace k (MonoidAlgebra k (G ⧸ K)) (ofMulAction k G (G ⧸ K) g) =
      if g ∈ K then (K.index : k) else 0 := by
  rw [trace_ofMulAction]
  simp_rw [smul_eq_self_iff_mem]
  split_ifs
  · simp [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  · simp

end Permutation

section Annihilation

open Representation

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  {ρ : Representation ℝ G V} {b : BilinForm ℝ V}

/-- Applying a homomorphism `S` with `S (T x) = χ * S x` to `ν ^ s x`, `ν = p - T`
(manuscript (6.1) with `T = τ ⊗ (-)` and `S = Sign_G`). -/
theorem map_nu_pow {A F : Type*} [AddCommGroup A] [CommRing F] (S : A →+ F)
    (T : AddMonoid.End A) (χ : F) (hT : ∀ x, S (T x) = χ * S x) (p s : ℕ) (x : A) :
    S ((((p : AddMonoid.End A) - T) ^ s) x) = ((p : F) - χ) ^ s * S x := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hs : (((p : AddMonoid.End A) - T) ^ (s + 1)) x =
        ((p : AddMonoid.End A) - T) ((((p : AddMonoid.End A) - T) ^ s) x) := by
      rw [pow_succ']
      rfl
    have hsub : ∀ y, ((p : AddMonoid.End A) - T) y = p • y - T y := fun _ => rfl
    rw [hs, hsub, map_sub, map_nsmul, hT, ih, nsmul_eq_mul, pow_succ']
    ring

/-- Theorem 6.3 at the level of characters: if `(p - χ_τ) ^ s · Sign_G(V, b) = 0` for
`τ = ℝ[G/K]`, `K` normal, `|G| = p ^ (k + 1)` and `g ∉ K` (e.g. a generator of `C_{p^a}`),
then `Sign_G(V, b)(g) = 0` and `p ∣ σ(V, b)`. -/
theorem prime_dvd_signature_of_annihilation [Fintype G] (hb : IsInvariantForm ρ b) {p k s : ℕ}
    (hp : p.Prime) (hG : Fintype.card G = p ^ (k + 1)) {K : Subgroup G} [K.Normal]
    [Fintype (G ⧸ K)] {g : G} (hg : g ∉ K)
    (h : ∀ x, ((p : ℂ) - (LinearMap.trace ℝ _ (ofMulAction ℝ G (G ⧸ K) x) : ℂ)) ^ s *
      equivariantSignature ρ b x = 0) :
    equivariantSignature ρ b g = 0 ∧ (p : ℤ) ∣ signature b := by
  have hg' := h g
  rw [trace_ofMulAction_quotient, ite_eq_right hg, Complex.ofReal_zero, sub_zero] at hg'
  have h0 := character_vanishes_of_prime_power_annihilation p s hp _ hg'
  exact ⟨h0, prime_dvd_signature_of_equivariantSignature_eq_zero hb.isSymm hb.nondegenerate
    hb.map_map hp hG h0⟩

/-- Theorem 6.3, signature step: let `S : A →+ (G → ℂ)` be a signature homomorphism on a group
`A` of forms with `S (τ ⊗ y) = χ_τ · S y`. If `ν ^ s x = 0` for `ν = p - τ ⊗ (-)` and
`S x = Sign_G(V, b)`, then `p ∣ σ(V, b)`. -/
theorem prime_dvd_signature_of_nu_pow_eq_zero [Fintype G] (hb : IsInvariantForm ρ b)
    {p k s : ℕ} (hp : p.Prime) (hG : Fintype.card G = p ^ (k + 1)) {K : Subgroup G} [K.Normal]
    [Fintype (G ⧸ K)] {g : G} (hg : g ∉ K) {A : Type*} [AddCommGroup A] (S : A →+ G → ℂ)
    (T : AddMonoid.End A)
    (hT : ∀ y, S (T y) =
      (fun x => (LinearMap.trace ℝ _ (ofMulAction ℝ G (G ⧸ K) x) : ℂ)) * S y)
    {x : A} (hx : (((p : AddMonoid.End A) - T) ^ s) x = 0)
    (hSx : S x = equivariantSignature ρ b) : (p : ℤ) ∣ signature b := by
  have h := map_nu_pow S T _ hT p s x
  rw [hx, map_zero, hSx] at h
  refine (prime_dvd_signature_of_annihilation (s := s) hb hp hG hg fun y => ?_).2
  simpa using (congr_fun h y).symm

end Annihilation

section TraceCorrespondence

open MonoidAlgebra

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
  {ρ : Representation k G V}

/-- The unnormalized trace `tr₁ : k[G] → k`, the coefficient of `1` (no factor `1 / |G|`). -/
def trOne : MonoidAlgebra k G →ₗ[k] k :=
  Finsupp.lapply 1 ∘ₗ (coeffLinearEquiv k).toLinearMap

/-- Forgetting the action, `U_*`: the `k`-valued form `tr₁ ∘ λ` underlying `λ`. -/
def forgetForm (l : V →ₗ[k] V →ₗ[k] MonoidAlgebra k G) : BilinForm k V :=
  l.compr₂ trOne

@[simp]
theorem forgetForm_apply (l : V →ₗ[k] V →ₗ[k] MonoidAlgebra k G) (v w : V) :
    forgetForm l v w = (l v w).coeff 1 :=
  rfl

theorem forgetForm_invariant {l : V →ₗ[k] V →ₗ[k] MonoidAlgebra k G}
    (hl₁ : ∀ h v w, l (ρ h v) w = MonoidAlgebra.single h 1 * l v w)
    (hl₂ : ∀ h v w, l v (ρ h w) = l v w * MonoidAlgebra.single h⁻¹ 1) (g : G) (v w : V) :
    forgetForm l (ρ g v) (ρ g w) = forgetForm l v w := by
  rw [forgetForm_apply, forgetForm_apply, hl₁, hl₂]
  simp [coeff_single_mul_apply, coeff_mul_single_apply]

variable {ι : Type*}

/-- The `k`-matrix, in the basis `(g, i) ↦ g e_i`, of a `k[G]`-matrix in a free basis `e`. -/
def regMatrix (A : Matrix ι ι (MonoidAlgebra k G)) : Matrix (G × ι) (G × ι) k :=
  fun p q => (A p.2 q.2).coeff (p.1⁻¹ * q.1)

/-- The adjoint of a `k[G]`-matrix for the involution `g ↦ g⁻¹`. -/
def groupAdjoint (A : Matrix ι ι (MonoidAlgebra k G)) : Matrix ι ι (MonoidAlgebra k G) :=
  fun i j => MonoidAlgebra.ofCoeff (Finsupp.equivMapDomain (Equiv.inv G) (A j i).coeff)

/-- In a free equivariant basis, transpose of the `k`-matrix is the group-ring adjoint. -/
theorem regMatrix_transpose (A : Matrix ι ι (MonoidAlgebra k G)) :
    (regMatrix A).transpose = regMatrix (groupAdjoint A) := by
  ext ⟨g, i⟩ ⟨h, j⟩
  simp [regMatrix, groupAdjoint, Finsupp.equivMapDomain_apply]

variable [Fintype G] (ρ) (b : BilinForm k V)

/-- The `k[G]`-valued form `λ(v, w) = ∑_g b(v, g w) g` of an invariant form, manuscript (3.2). -/
def hermForm : V →ₗ[k] V →ₗ[k] MonoidAlgebra k G :=
  ∑ g : G, (b.compl₂ (ρ g)).compr₂ (MonoidAlgebra.lsingle g)

theorem hermForm_apply (v w : V) :
    hermForm ρ b v w = ∑ g, MonoidAlgebra.single g (b v (ρ g w)) := by
  simp [hermForm]

@[simp]
theorem hermForm_apply_apply (v w : V) (x : G) : (hermForm ρ b v w).coeff x = b v (ρ x w) := by
  classical
  rw [hermForm_apply, coeff_sum, Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply]

/-- Manuscript (3.2): `tr₁ λ(v, w) = b(v, w)`. -/
theorem trOne_hermForm (v w : V) : trOne (hermForm ρ b v w) = b v w := by
  change (hermForm ρ b v w).coeff 1 = b v w
  simp

/-- Forgetting the action returns the original form, with no factor `1 / |G|`. -/
theorem forgetForm_hermForm : forgetForm (hermForm ρ b) = b := by
  ext v w
  simp

variable {ρ b}

theorem hermForm_left (hinv : ∀ g v w, b (ρ g v) (ρ g w) = b v w) (h : G) (v w : V) :
    hermForm ρ b (ρ h v) w = MonoidAlgebra.single h 1 * hermForm ρ b v w := by
  ext x
  rw [coeff_single_mul_apply, hermForm_apply_apply, hermForm_apply_apply, one_mul,
    ← hinv h⁻¹, ρ.inv_self_apply, ← Module.End.mul_apply, ← map_mul]

theorem hermForm_right (h : G) (v w : V) :
    hermForm ρ b v (ρ h w) = hermForm ρ b v w * MonoidAlgebra.single h⁻¹ 1 := by
  ext x
  rw [coeff_mul_single_apply, hermForm_apply_apply, hermForm_apply_apply, mul_one, inv_inv,
    map_mul, Module.End.mul_apply]

/-- `λ` is hermitian for the involution `g ↦ g⁻¹`. -/
theorem hermForm_swap (hb : b.IsSymm) (hinv : ∀ g v w, b (ρ g v) (ρ g w) = b v w)
    (v w : V) (x : G) : (hermForm ρ b w v).coeff x = (hermForm ρ b v w).coeff x⁻¹ := by
  rw [hermForm_apply_apply, hermForm_apply_apply, hb.eq, ← hinv x⁻¹, ρ.inv_self_apply]

theorem hermForm_eq_zero_iff (v : V) : (∀ w, hermForm ρ b v w = 0) ↔ ∀ w, b v w = 0 := by
  refine ⟨fun h w => ?_, fun h w => ?_⟩
  · simpa using congr_arg (·.coeff 1) (h w)
  · ext x
    simp [h]

/-- Conversely, `λ ↦ tr₁ ∘ λ` inverts `b ↦ λ` on sesquilinear forms. -/
theorem hermForm_forgetForm {l : V →ₗ[k] V →ₗ[k] MonoidAlgebra k G}
    (hl : ∀ h v w, l v (ρ h w) = l v w * MonoidAlgebra.single h⁻¹ 1) :
    hermForm ρ (forgetForm l) = l := by
  ext v w x
  rw [hermForm_apply_apply, forgetForm_apply, hl, coeff_mul_single_apply, inv_inv, one_mul, mul_one]

theorem regMatrix_mul [Fintype ι] (A B : Matrix ι ι (MonoidAlgebra k G)) :
    regMatrix (A * B) = regMatrix A * regMatrix B := by
  ext ⟨g, i⟩ ⟨h, j⟩
  simp only [regMatrix, Matrix.mul_apply, Fintype.sum_prod_type]
  rw [coeff_sum, Finsupp.finsetSum_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [coeff_mul_apply_left, Finsupp.sum_fintype _ _ (by simp)]
  exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun x => by simp [mul_assoc]

/-- The Gram matrix of `b` in a free equivariant basis `(g, i) ↦ g e_i` is the `k`-matrix of
the `k[G]`-Gram matrix `λ(e_i, e_j)`. -/
theorem toMatrix_eq_regMatrix [DecidableEq G] [Fintype ι] [DecidableEq ι] (hinv : ∀ g v w, b (ρ g v) (ρ g w) = b v w) (e : ι → V)
    (f : Basis (G × ι) k V) (hf : ∀ g i, f (g, i) = ρ g (e i)) :
    LinearMap.BilinForm.toMatrix f b =
      regMatrix (Matrix.of fun i j => hermForm ρ b (e i) (e j)) := by
  ext ⟨g, i⟩ ⟨h, j⟩
  rw [LinearMap.BilinForm.toMatrix_apply, hf, hf, regMatrix, Matrix.of_apply,
    hermForm_apply_apply, ← hinv g⁻¹, ρ.inv_self_apply, ← Module.End.mul_apply, ← map_mul]

end TraceCorrespondence

section RationalTrace

variable {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℚ V]
  [FiniteDimensional ℚ V] {ρ : Representation ℚ G V} {b : BilinForm ℚ V}

/-- `Sign_G(V, b)(1) = σ(U_*(V, λ))`: the value at `1` is the signature of the form underlying
`λ` after forgetting the action. -/
theorem ratEquivariantSignature_one_eq_forgetForm (hb : b.IsSymm) (hnd : b.Nondegenerate)
    (hinv : ∀ g v w, b (ρ g v) (ρ g w) = b v w) :
    ratEquivariantSignature ρ b 1 = ratSignature (forgetForm (hermForm ρ b)) := by
  rw [forgetForm_hermForm, ratEquivariantSignature_one hb hnd hinv]

omit [FiniteDimensional ℚ V] in
/-- The signature is insensitive to positive rescaling, e.g. a normalized trace `tr₁ / |G|`. -/
theorem ratSignature_smul {c : ℚ} (hc : 0 < c) (b : BilinForm ℚ V) :
    ratSignature (c • b) = ratSignature b := by
  have h : BilinForm.baseChange ℝ (c • b) = (c : ℝ) • BilinForm.baseChange ℝ b := by
    ext x y
    simp [Algebra.smul_def]
  rw [ratSignature, ratSignature, h, signature_smul (by exact_mod_cast hc)]

end RationalTrace

section RationalLaws

open Representation

variable {G : Type*} [Group G]

open Classical in
/-- `Sign(α ⊗ τ) = Sign(α) · χ_τ` for `τ = ℝ[G/K]` with its standard form, `K` normal. -/
theorem equivariantSignature_tprod_perm [Finite G] {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] {ρ : Representation ℝ G V} {b : BilinForm ℝ V}
    (hb : IsInvariantForm ρ b) (K : Subgroup G) [K.Normal] [Fintype (G ⧸ K)] (g : G) :
    equivariantSignature (ρ.tprod (ofMulAction ℝ G (G ⧸ K))) (b.tmul (permForm ℝ (G ⧸ K))) g =
      equivariantSignature ρ b g * if g ∈ K then (K.index : ℂ) else 0 := by
  rw [equivariantSignature_tprod hb permForm_isSymm permForm_pos,
    trace_ofMulAction_quotient]
  split_ifs <;> simp

theorem bilin_baseChange_ext {M : Type*} [AddCommGroup M] [Module ℚ M]
    {B B' : BilinForm ℝ (ℝ ⊗[ℚ] M)}
    (h : ∀ v w, B (1 ⊗ₜ v) (1 ⊗ₜ w) = B' (1 ⊗ₜ v) (1 ⊗ₜ w)) : B = B' := by
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul a v =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul a' w =>
      rw [← mul_one a, ← smul_eq_mul, ← smul_tmul', ← mul_one a', ← smul_eq_mul, ← smul_tmul']
      simp only [map_smul, LinearMap.smul_apply, h]

theorem linearMap_baseChange_tmul_ext {M N P : Type*} [AddCommGroup M] [Module ℚ M]
    [AddCommGroup N] [Module ℚ N] [AddCommGroup P] [Module ℝ P]
    {f f' : (ℝ ⊗[ℚ] M) ⊗[ℝ] (ℝ ⊗[ℚ] N) →ₗ[ℝ] P}
    (h : ∀ m n, f ((1 ⊗ₜ m) ⊗ₜ (1 ⊗ₜ n)) = f' ((1 ⊗ₜ m) ⊗ₜ (1 ⊗ₜ n))) : f = f' := by
  refine TensorProduct.ext' fun x y => ?_
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [add_tmul, map_add, hx, hx']
  | tmul a m =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [tmul_add, map_add, hy, hy']
    | tmul a' n =>
      have e₁ : (a ⊗ₜ[ℚ] m : ℝ ⊗[ℚ] M) = a • (1 ⊗ₜ m) := by rw [smul_tmul', smul_eq_mul, mul_one]
      have e₂ : (a' ⊗ₜ[ℚ] n : ℝ ⊗[ℚ] N) = a' • (1 ⊗ₜ n) := by
        rw [smul_tmul', smul_eq_mul, mul_one]
      rw [e₁, e₂, smul_tmul_smul, map_smul, map_smul, h]

theorem bilin_baseChange_tmul_ext {M N : Type*} [AddCommGroup M] [Module ℚ M]
    [AddCommGroup N] [Module ℚ N] {B B' : BilinForm ℝ ((ℝ ⊗[ℚ] M) ⊗[ℝ] (ℝ ⊗[ℚ] N))}
    (h : ∀ m n m' n', B ((1 ⊗ₜ m) ⊗ₜ (1 ⊗ₜ n)) ((1 ⊗ₜ m') ⊗ₜ (1 ⊗ₜ n')) =
      B' ((1 ⊗ₜ m) ⊗ₜ (1 ⊗ₜ n)) ((1 ⊗ₜ m') ⊗ₜ (1 ⊗ₜ n'))) : B = B' :=
  linearMap_baseChange_tmul_ext fun m n => linearMap_baseChange_tmul_ext fun m' n' => h m n m' n'

variable {V V₁ V₂ W : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
  [AddCommGroup V₁] [Module ℚ V₁] [FiniteDimensional ℚ V₁]
  [AddCommGroup V₂] [Module ℚ V₂] [FiniteDimensional ℚ V₂]
  [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
  {ρ : Representation ℚ G V} {ρ₁ : Representation ℚ G V₁} {ρ₂ : Representation ℚ G V₂}
  {σ : Representation ℚ G W} {b : BilinForm ℚ V} {b₁ : BilinForm ℚ V₁} {b₂ : BilinForm ℚ V₂}
  {c : BilinForm ℚ W}

theorem IsInvariantForm.baseChange (hb : IsInvariantForm ρ b) :
    IsInvariantForm (realRep ρ) (BilinForm.baseChange ℝ b) :=
  ⟨isSymm_baseChange_real hb.isSymm, nondegenerate_baseChange_real hb.nondegenerate,
    baseChange_invariant hb.map_map⟩

omit [FiniteDimensional ℚ W] in
theorem baseChange_neg (c : BilinForm ℚ W) :
    BilinForm.baseChange ℝ (-c) = -BilinForm.baseChange ℝ c :=
  bilin_baseChange_ext fun v w => by simp

/-- A positive definite rational form stays positive definite over `ℝ`. -/
theorem posDef_baseChange (hc : c.IsSymm) (hpos : ∀ w, w ≠ 0 → 0 < c w w) (x : ℝ ⊗[ℚ] W)
    (hx : x ≠ 0) : 0 < BilinForm.baseChange ℝ c x x := by
  obtain ⟨e, he, hpe⟩ := exists_basis_isOrthoᵢ_pos hc hpos
  refine posDef_of_basis (Algebra.TensorProduct.basis ℝ e) (fun i j hij => ?_) (fun i => ?_) x hx
  · change BilinForm.baseChange ℝ c (Algebra.TensorProduct.basis ℝ e i)
      (Algebra.TensorProduct.basis ℝ e j) = 0
    simp [Algebra.TensorProduct.basis_apply, show c (e i) (e j) = 0 from he hij]
  · simpa [Algebra.TensorProduct.basis_apply] using hpe i

theorem ratEquivariantSignature_neg [Finite G] (hb : IsInvariantForm ρ b) :
    ratEquivariantSignature ρ (-b) = -ratEquivariantSignature ρ b := by
  rw [ratEquivariantSignature, baseChange_neg, equivariantSignature_neg hb.baseChange]
  rfl

/-- Additivity of the rational `Sign_G` under orthogonal sums. -/
theorem ratEquivariantSignature_orthSum [Finite G] (hb₁ : IsInvariantForm ρ₁ b₁)
    (hb₂ : IsInvariantForm ρ₂ b₂) :
    ratEquivariantSignature (ρ₁.prod ρ₂) (orthSum b₁ b₂) =
      ratEquivariantSignature ρ₁ b₁ + ratEquivariantSignature ρ₂ b₂ := by
  rw [ratEquivariantSignature, ratEquivariantSignature, ratEquivariantSignature,
    ← equivariantSignature_orthSum hb₁.baseChange hb₂.baseChange]
  refine (equivariantSignature_congr (hb₁.orthSum hb₂).baseChange
    (prodRight ℚ ℝ ℝ V₁ V₂) (fun g x => ?_) fun x y => ?_).symm
  · induction x using TensorProduct.inductionOn with
    | add x x' hx hx' => simp only [map_add, hx, hx']
    | tmul a v => simp
  · have h : (orthSum (BilinForm.baseChange ℝ b₁) (BilinForm.baseChange ℝ b₂)).compl₁₂
        (prodRight ℚ ℝ ℝ V₁ V₂).toLinearMap (prodRight ℚ ℝ ℝ V₁ V₂).toLinearMap =
        BilinForm.baseChange ℝ (orthSum b₁ b₂) :=
      bilin_baseChange_ext fun v w => by simp [add_smul]
    exact LinearMap.congr_fun₂ h x y

/-- The rational `Sign_G` vanishes on metabolic forms. -/
theorem ratEquivariantSignature_eq_zero_of_isotropic [Finite G] (hb : IsInvariantForm ρ b)
    {L : Submodule ℚ V} (hL : ∀ g, L ≤ L.comap (ρ g)) (hiso : ∀ v ∈ L, ∀ w ∈ L, b v w = 0)
    (hdim : 2 * finrank ℚ L = finrank ℚ V) : ratEquivariantSignature ρ b = 0 := by
  let ι := L.subtype.baseChange ℝ
  have hι : Function.Injective ι := by
    have := Module.Flat.lTensor_preserves_injective_linearMap (M := ℝ) L.subtype
      L.injective_subtype
    rwa [← LinearMap.baseChange_eq_ltensor] at this
  have hinv : ∀ g, LinearMap.range ι ≤ (LinearMap.range ι).comap (realRep ρ g) := by
    rintro g _ ⟨x, rfl⟩
    refine ⟨((ρ g).restrict (hL g)).baseChange ℝ x, ?_⟩
    induction x using TensorProduct.inductionOn with
    | add x x' hx hx' => simp only [map_add, hx, hx']
    | tmul a v => simp [ι]
  have hzero : (BilinForm.baseChange ℝ b).compl₁₂ ι ι = 0 :=
    bilin_baseChange_ext fun v w => by simp [ι, hiso _ v.2 _ w.2]
  refine equivariantSignature_eq_zero_of_isotropic hb.baseChange hinv ?_ ?_
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact LinearMap.congr_fun₂ hzero x y
  · rw [LinearMap.finrank_range_of_inj hι, Module.finrank_baseChange, Module.finrank_baseChange,
      hdim]

/-- Witt invariance of the rational `Sign_G`. -/
theorem ratEquivariantSignature_eq_of_isotropic_orthSum_neg [Finite G]
    (hb₁ : IsInvariantForm ρ₁ b₁) (hb₂ : IsInvariantForm ρ₂ b₂) {L : Submodule ℚ (V₁ × V₂)}
    (hL : ∀ g, L ≤ L.comap (ρ₁.prod ρ₂ g))
    (hiso : ∀ v ∈ L, ∀ w ∈ L, orthSum b₁ (-b₂) v w = 0)
    (hdim : 2 * finrank ℚ L = finrank ℚ V₁ + finrank ℚ V₂) :
    ratEquivariantSignature ρ₁ b₁ = ratEquivariantSignature ρ₂ b₂ := by
  have h := ratEquivariantSignature_eq_zero_of_isotropic (hb₁.orthSum hb₂.neg) hL hiso
    (by rw [Module.finrank_prod]; exact hdim)
  rw [ratEquivariantSignature_orthSum hb₁ hb₂.neg, ratEquivariantSignature_neg hb₂] at h
  exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h)

/-- Tensoring with a positive definite rational form `(W, c)` multiplies the rational `Sign_G`
by `χ_W`. -/
theorem ratEquivariantSignature_tprod [Finite G] (hb : IsInvariantForm ρ b) (hc : c.IsSymm)
    (hcpos : ∀ w, w ≠ 0 → 0 < c w w) (g : G) :
    ratEquivariantSignature (ρ.tprod σ) (b.tmul c) g =
      ratEquivariantSignature ρ b g * (LinearMap.trace ℚ W (σ g) : ℂ) := by
  obtain ⟨J, hJ⟩ := hb.baseChange.exists_isSignatureInvolution
  have hcℝ := isSymm_baseChange_real hc
  have hJ' := hJ.map_id (σ := realRep σ) hb.baseChange.isSymm hcℝ (posDef_baseChange hc hcpos)
  set e := (TensorProduct.AlgebraTensorModule.distribBaseChange ℚ ℝ V W).symm
  have he : ∀ a a' v w, e ((a ⊗ₜ v) ⊗ₜ (a' ⊗ₜ w)) = (a' * a) ⊗ₜ (v ⊗ₜ w) := fun a a' v w => by
    simp [e, TensorProduct.AlgebraTensorModule.distribBaseChange, smul_tmul', smul_eq_mul]
  rw [ratEquivariantSignature, hJ'.equivariantSignature_congr e (fun g x => ?_) fun x y => ?_,
    equivariantSignature_tprod hb.baseChange hcℝ (posDef_baseChange hc hcpos), realRep_apply,
    LinearMap.trace_baseChange, ratEquivariantSignature]
  · rfl
  · have h : e.toLinearMap ∘ₗ ((realRep ρ).tprod (realRep σ)) g =
        realRep (ρ.tprod σ) g ∘ₗ e.toLinearMap :=
      linearMap_baseChange_tmul_ext fun v w => by simp [he]
    exact LinearMap.congr_fun h x
  · have h : (BilinForm.baseChange ℝ (b.tmul c)).compl₁₂ e.toLinearMap e.toLinearMap =
        (BilinForm.baseChange ℝ b).tmul (BilinForm.baseChange ℝ c) :=
      bilin_baseChange_tmul_ext fun v w v' w' => by simp [he, mul_comm]
    exact LinearMap.congr_fun₂ h x y

open Classical in
/-- Manuscript §3/§6: `Sign(α ⊗ τ) = Sign(α) · χ_τ` for `τ = ℚ[G/K]` with its orthonormal form
and `K` normal, where `χ_τ(g) = [G : K]` for `g ∈ K` and `0` otherwise. -/
theorem ratEquivariantSignature_tprod_perm [Finite G] (hb : IsInvariantForm ρ b) (K : Subgroup G)
    [K.Normal] [Fintype (G ⧸ K)] (g : G) :
    ratEquivariantSignature (ρ.tprod (ofMulAction ℚ G (G ⧸ K))) (b.tmul (permForm ℚ (G ⧸ K))) g =
      ratEquivariantSignature ρ b g * if g ∈ K then (K.index : ℂ) else 0 := by
  rw [ratEquivariantSignature_tprod hb permForm_isSymm permForm_pos,
    trace_ofMulAction_quotient]
  split_ifs <;> simp

/-- Theorem 6.3 at the level of rational characters: if `(p - χ_τ) ^ s · Sign_G(V, b) = 0`
for `τ = ℚ[G/K]`, `K` normal, `|G| = p ^ (k + 1)` and `g ∉ K`, then `Sign_G(V, b)(g) = 0` and
`p ∣ σ(V, b)`. -/
theorem prime_dvd_ratSignature_of_annihilation [Fintype G] (hb : IsInvariantForm ρ b)
    {p k s : ℕ} (hp : p.Prime) (hG : Fintype.card G = p ^ (k + 1)) {K : Subgroup G} [K.Normal]
    [Fintype (G ⧸ K)] {g : G} (hg : g ∉ K)
    (h : ∀ x, ((p : ℂ) - (LinearMap.trace ℚ _ (ofMulAction ℚ G (G ⧸ K) x) : ℂ)) ^ s *
      ratEquivariantSignature ρ b x = 0) :
    ratEquivariantSignature ρ b g = 0 ∧ (p : ℤ) ∣ ratSignature b := by
  have hg' := h g
  rw [trace_ofMulAction_quotient, ite_eq_right hg, Rat.cast_zero, sub_zero] at hg'
  have h0 := character_vanishes_of_prime_power_annihilation p s hp _ hg'
  exact ⟨h0, prime_dvd_ratSignature hb.isSymm hb.nondegenerate hb.map_map hp hG h0⟩

end RationalLaws

end HSFormal
