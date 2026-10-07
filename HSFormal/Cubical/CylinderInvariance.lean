import HSFormal.Cubical.SeqDual
import HSFormal.LTheory.ConcreteL
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.UniformSpace.Equicontinuity
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Homotopy invariance of controlled Poincaré complexes (cubical module C7, Lemma 11.1)

Manuscript Lemma 11.1 (l. 914): a homotopy of control labels gives equal classes in
`L(𝒜_G(X))`. A sequence of based symmetric dualities `Φ i : SymDuality (C i) N _` with labels
`ℓ i : (C i).X → X` is *controlled* (`IsControlledDuality`) when `d`, `φ`, the inverse `ψ` and
both homotopies have propagation `→ 0`; it then realizes (`SeqDual`) a strictly symmetric
Poincaré complex `toAsymptotic` in `𝒜_G(X)`.

* `IsUnifControlledDuality.cls_eq_of_steps`: labellings `ℓ i 0, …, ℓ i (k i)`, controlling
  uniformly in the step, with `sup_{j,σ} d(ℓ i (j+1) σ, ℓ i j σ) → 0`, give equal end classes.
* `IsUnifControlledDuality.cls_eq_of_homotopy` (**Lemma 11.1**): a family `ℓ i t`, `t ∈ [0,1]`,
  controlling uniformly in `t` and uniformly equicontinuous in `t`.
* `IsControlledDuality.cls_eq_of_homotopic`: cells with centres in a compact `K`, controlled
  over `K`, labelled by `f ∘ centre`; homotopic `f₀ ≃ f₁ : K → X` give equal classes
  (compactness gives both uniformities). `torusCP.cls_eq_of_homotopic` is the germ
  `Tⁿ_{m_i} ⊗ CPcell` over `(ℝ/Lℤ)ⁿ`.

Instead of the prism `C_i ⊗ I_{k_i}` of the manuscript we telescope in the L-group: on
`k i + 1` copies of `C i` (`blocks`), the copy `j` labelled by `ℓ i j`, the cuts at the first and
last copies are `P⁰`, `P¹`, and the shift of copies `j ↦ j + 1` (controlled by the step size) is an
isometry between the complementary cuts; so `[P⁰] + [R] = [R'] + [P¹]` with `[R] = [R']`. The
L-group computation happens over the prequotient `asymptoticObjInvCat` and is pushed to
`𝒜_G(X)` by `asymptoticQuotInv`.
-/

noncomputable section

namespace HSFormal.Cubical

open Filter Matrix CategoryTheory CategoryTheory.Limits HSFormal.LTheory HSFormal.Compression
open scoped ENNReal Topology Kronecker

/-- The prequotient `AsymptoticObject π X` with the transpose involution as an `InvCat`; the
quotient functor `asymptoticQuotInv` is a morphism to `asymptoticInvCat π X`. -/
abbrev asymptoticObjInvCat {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)]
    [∀ i, Fintype (G i)] (π : ∀ i, G i →* H) (X : Type) [MulAction H X] [PseudoEMetricSpace X] :
    InvCat where
  carrier := AsymptoticObject π X
  inv := asymptoticObjInvolution π X
  unitary A B := ⟨{ toBinaryBicone := AsymptoticObject.biprodBicone A B
                    isBilimit := isBinaryBilimitOfTotal _ (AsymptoticObject.biprodBicone_total A B)
                    star_inl := rfl
                    star_inr := rfl }⟩

namespace BasedComplex

namespace ControlledSeq

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  {π : ∀ i, G i →* H} {X : Type} [MulAction H X] [PseudoEMetricSpace X] [IsIsometricSMul H X]
  {A B : ControlledSeq X}

@[simp] theorem Hom.comp_f_f {B' : ControlledSeq X} (G : Hom B B') (F : Hom A B) (i : ℕ) :
    ((G.comp F).f i).f = (G.f i).f * (F.f i).f := rfl

theorem Hom.toComplex_eq_zero {F : Hom A B} (hF : ∀ i, (F.f i).f = 0) : F.toComplex π = 0 := by
  ext r
  rw [HomologicalComplex.zero_f, Hom.toComplex_f]
  exact hom_eq_zero _ F.tendsto fun i κ σ _ _ ↦ by rw [hF]; rfl

end ControlledSeq

/-- The labels `ℓ` control the complexes `C i`, the duality maps `φ_i`, their inverses `ψ_i` and
both homotopies `ψ φ ≃ 1`, `φ ψ ≃ 1`: all propagations tend to zero. -/
structure IsControlledDuality {X : Type*} [PseudoEMetricSpace X] {C : ℕ → BasedComplex}
    {N : ℕ} {hN : ∀ i, (C i).DimLE N} (Φ : ∀ i, SymDuality (C i) N (hN i))
    (ℓ : ∀ i, (C i).X → X) : Prop where
  d : PropTendsto (fun i ↦ (C i).d) ℓ ℓ
  hom : PropTendsto (fun i ↦ (Φ i).hom.f) ℓ ℓ
  inv : PropTendsto (fun i ↦ (Φ i).inv.f) ℓ ℓ
  homInv : PropTendsto (fun i ↦ (Φ i).homInv.h) ℓ ℓ
  invHom : PropTendsto (fun i ↦ (Φ i).invHom.h) ℓ ℓ

namespace IsControlledDuality

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  (π : ∀ i, G i →* H) {X : Type} [MulAction H X] [PseudoEMetricSpace X] [IsIsometricSMul H X]
  {C : ℕ → BasedComplex} {N : ℕ} {hN : ∀ i, (C i).DimLE N} {Φ : ∀ i, SymDuality (C i) N (hN i)}
  {ℓ : ∀ i, (C i).X → X} (h : IsControlledDuality Φ ℓ)

/-- The controlled sequence `(C i, ℓ i)`. -/
abbrev seq : ControlledSeq X := ⟨C, ℓ, h.d⟩

/-- The controlled symmetric duality `(Φ i)` on `(C i, ℓ i)`. -/
abbrev symDuality : h.seq.SymDuality N hN :=
  ControlledSeq.SymDuality.ofSeq Φ h.hom h.inv h.homInv h.invHom

/-- The controlled Poincaré complex `(C, ℓ, φ)` over the prequotient. -/
abbrev toSymPoincare : SymPoincare (asymptoticObjInvCat π X).inv N :=
  h.symDuality.symPoincareObj π

/-- The controlled Poincaré complex `(C, ℓ, φ)` in `𝒜_G(X)`. -/
abbrev toAsymptotic : SymPoincare (asymptoticInvCat π X).inv N := h.symDuality.symPoincare π

open ControlledSeq

theorem cls_toAsymptotic :
    Lconc.cls (h.toAsymptotic π) =
      Lconc.map (asymptoticQuotInv π X : asymptoticObjInvCat π X ⟶ asymptoticInvCat π X)
        (Lconc.cls (h.toSymPoincare π)) :=
  (Lconc.map_cls (A := asymptoticObjInvCat π X) (B := asymptoticInvCat π X) _ _).symm

/-- The class depends only on the labelling. -/
theorem cls_toAsymptotic_congr {ℓ' : ∀ i, (C i).X → X} (h' : IsControlledDuality Φ ℓ')
    (e : ℓ = ℓ') : Lconc.cls (h.toAsymptotic π) = Lconc.cls (h'.toAsymptotic π) := by
  subst e; rfl

theorem toSymPoincare_p : (h.toSymPoincare π).p = 𝟙 _ := rfl
theorem toSymPoincare_φ :
    (h.toSymPoincare π).φ = (dualIso π h.seq N hN).hom ≫ h.symDuality.hom.toComplex π := rfl

/-- A controlled chain idempotent `e` with `φ eᵀ = e φ` is a reducing idempotent. -/
theorem isReducing (e : h.seq.Hom h.seq) (he : ∀ i, (e.f i).f * (e.f i).f = (e.f i).f)
    (hadj : ∀ i, (Φ i).hom.f * (e.f i).fᵀ = (e.f i).f * (Φ i).hom.f) :
    (h.toSymPoincare π).IsReducing (e.toComplex π) where
  idem := by
    rw [← Hom.toComplex_comp]
    exact Hom.toComplex_congr fun i ↦ by simpa using he i
  comm := by simp [toSymPoincare_p]
  adj := by
    rw [toSymPoincare_φ]
    rw [dualHom_toComplex _ N hN hN]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ← Hom.toComplex_comp]
    congr 1
    exact Hom.toComplex_congr fun i ↦ by simp; exact hadj i

variable {D : ℕ → BasedComplex} {hD : ∀ i, (D i).DimLE N} {Ψ : ∀ i, SymDuality (D i) N (hD i)}
  {m : ∀ i, (D i).X → X} (h' : IsControlledDuality Ψ m)

/-- Cuts of two realizations are isometric, hence have equal classes, if controlled chain maps
`F`, `G` restrict to inverse isomorphisms between the summands `e_A`, `e_B` carrying `φ` to `ψ`. -/
theorem cls_cut_eq_cls_cut {eA : h.seq.Hom h.seq} {eB : h'.seq.Hom h'.seq}
    (heA : (h.toSymPoincare π).IsReducing (eA.toComplex π))
    (heB : (h'.toSymPoincare π).IsReducing (eB.toComplex π))
    (F : h.seq.Hom h'.seq) (G : h'.seq.Hom h.seq)
    (hF : ∀ i, (eB.f i).f * ((F.f i).f * (eA.f i).f) = (F.f i).f)
    (hG : ∀ i, (eA.f i).f * ((G.f i).f * (eB.f i).f) = (G.f i).f)
    (hGF : ∀ i, (G.f i).f * (F.f i).f = (eA.f i).f)
    (hFG : ∀ i, (F.f i).f * (G.f i).f = (eB.f i).f)
    (hconj : ∀ i, (F.f i).f * ((eA.f i).f * ((Φ i).hom.f * (F.f i).fᵀ)) =
      (eB.f i).f * (Ψ i).hom.f) :
    Lconc.cls ((h.toSymPoincare π).cut heA) = Lconc.cls ((h'.toSymPoincare π).cut heB) := by
  refine Lconc.cls_eq_of_isometry (SymPoincare.HomotopyIsometry.ofEq (F.toComplex π)
    (G.toComplex π) ?_ ?_ ?_ ?_ ?_)
  · simp only [SymPoincare.cut_p, toSymPoincare_p, Category.id_comp, ← Hom.toComplex_comp]
    exact Hom.toComplex_congr fun i ↦ by simpa [Matrix.mul_assoc] using hF i
  · simp only [SymPoincare.cut_p, toSymPoincare_p, Category.id_comp, ← Hom.toComplex_comp]
    exact Hom.toComplex_congr fun i ↦ by simpa [Matrix.mul_assoc] using hG i
  · simp only [SymPoincare.cut_p, toSymPoincare_p, Category.id_comp, ← Hom.toComplex_comp]
    exact Hom.toComplex_congr fun i ↦ by simpa [Matrix.mul_assoc] using hGF i
  · simp only [SymPoincare.cut_p, toSymPoincare_p, Category.id_comp, ← Hom.toComplex_comp]
    exact Hom.toComplex_congr fun i ↦ by simpa [Matrix.mul_assoc] using hFG i
  · simp only [SymPoincare.cut_φ, toSymPoincare_φ, ControlledSeq.dualityMap]
    rw [dualHom_toComplex _ N hN hD]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ← Hom.toComplex_comp]
    congr 1
    exact Hom.toComplex_congr fun i ↦ by simp [Matrix.mul_assoc]; exact hconj i

/-- Splitting along complementary controlled idempotents. -/
theorem cls_eq_cls_cut_add {e e' : h.seq.Hom h.seq}
    (he : (h.toSymPoincare π).IsReducing (e.toComplex π))
    (he' : (h.toSymPoincare π).IsReducing (e'.toComplex π))
    (hsum : ∀ i, (e.f i).f + (e'.f i).f = 1) (h₁ : ∀ i, (e'.f i).f * (e.f i).f = 0)
    (h₂ : ∀ i, (e.f i).f * (e'.f i).f = 0) :
    Lconc.cls (h.toSymPoincare π) =
      Lconc.cls ((h.toSymPoincare π).cut he) + Lconc.cls ((h.toSymPoincare π).cut he') := by
  have h₁₂ : e.toComplex π ≫ e'.toComplex π = 0 := by
    rw [← Hom.toComplex_comp]; exact Hom.toComplex_eq_zero h₁
  have h₂₁ : e'.toComplex π ≫ e.toComplex π = 0 := by
    rw [← Hom.toComplex_comp]; exact Hom.toComplex_eq_zero h₂
  rw [← Lconc.cls_cut_add _ he he' h₁₂ h₂₁, Lconc.cls_cut_of_eq]
  rw [toSymPoincare_p, Category.id_comp]
  ext r
  simp only [HomologicalComplex.add_f_apply, Hom.toComplex_f, HomologicalComplex.id_f]
  erw [← hom_add]
  exact (hom_congr (funext hsum) _ _ _ _).trans hom_one

end IsControlledDuality

/-! ### Disjoint copies -/

section Blocks

variable {C : BasedComplex} {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι']
  [DecidableEq ι'] {N : ℕ}

/-- `ι` disjoint copies `C ⊗ ℚ^ι` of `C`. -/
@[reducible]
def blocks (C : BasedComplex) (ι : Type) [Fintype ι] [DecidableEq ι] : BasedComplex where
  X := C.X × ι
  deg p := C.deg p.1
  d := C.d ⊗ₖ (1 : Matrix ι ι ℚ)
  d_deg := by
    rintro ⟨σ, j⟩ ⟨τ, j'⟩ h
    rw [kronecker_apply] at h
    exact C.d_deg σ τ (left_ne_zero_of_mul h)
  d_d := by rw [← mul_kronecker_mul, C.d_d, Matrix.one_mul, zero_kronecker]

theorem DimLE.blocks (hC : C.DimLE N) : (C.blocks ι).DimLE N := fun p ↦ hC p.1

theorem blocks_dual_d (hC : C.DimLE N) :
    ((C.blocks ι).dual N hC.blocks).d = (C.dual N hC).d ⊗ₖ (1 : Matrix ι ι ℚ) := by
  ext ⟨a, j⟩ ⟨b, j'⟩
  rw [dual_d_apply, kronecker_apply, dual_d_apply]
  change (-1) ^ N * ((-1) ^ C.deg b * (C.d b a * (1 : Matrix ι ι ℚ) j' j)) =
    (-1) ^ N * ((-1) ^ C.deg b * C.d b a) * (1 : Matrix ι ι ℚ) j j'
  rcases eq_or_ne j j' with rfl | h
  · simp
  · simp [one_apply_ne h, one_apply_ne h.symm]

/-- `φ ⊗ 1`, `ψ ⊗ 1` and the homotopies `⊗ 1` on `ι` copies. -/
def SymDuality.blocks {hC : C.DimLE N} (P : SymDuality C N hC) (ι : Type) [Fintype ι]
    [DecidableEq ι] : SymDuality (C.blocks ι) N hC.blocks where
  hom := ⟨P.hom.f ⊗ₖ 1, by rintro ⟨σ, j⟩ ⟨τ, j'⟩ h; exact P.hom.deg0 σ τ (left_ne_zero_of_mul h),
    by rw [blocks_dual_d hC, ← mul_kronecker_mul, ← mul_kronecker_mul, P.hom.comm]⟩
  inv := ⟨P.inv.f ⊗ₖ 1, by rintro ⟨σ, j⟩ ⟨τ, j'⟩ h; exact P.inv.deg0 σ τ (left_ne_zero_of_mul h),
    by rw [blocks_dual_d hC, ← mul_kronecker_mul, ← mul_kronecker_mul, P.inv.comm]⟩
  homInv := ⟨P.homInv.h ⊗ₖ 1,
    by rintro ⟨σ, j⟩ ⟨τ, j'⟩ h; exact P.homInv.deg1 σ τ (left_ne_zero_of_mul h), by
      change P.inv.f ⊗ₖ 1 * P.hom.f ⊗ₖ 1 - 1 =
        ((C.blocks ι).dual N hC.blocks).d * P.homInv.h ⊗ₖ (1 : Matrix ι ι ℚ) +
          P.homInv.h ⊗ₖ 1 * ((C.blocks ι).dual N hC.blocks).d
      rw [blocks_dual_d hC, ← mul_kronecker_mul, ← mul_kronecker_mul, ← mul_kronecker_mul,
        ← one_kronecker_one, Matrix.mul_one, ← sub_kronecker, ← add_kronecker]
      exact congrArg (· ⊗ₖ (1 : Matrix ι ι ℚ)) P.homInv.eq⟩
  invHom := ⟨P.invHom.h ⊗ₖ 1,
    by rintro ⟨σ, j⟩ ⟨τ, j'⟩ h; exact P.invHom.deg1 σ τ (left_ne_zero_of_mul h), by
      change P.hom.f ⊗ₖ 1 * P.inv.f ⊗ₖ 1 - 1 =
        C.d ⊗ₖ 1 * P.invHom.h ⊗ₖ (1 : Matrix ι ι ℚ) + P.invHom.h ⊗ₖ 1 * C.d ⊗ₖ 1
      rw [← mul_kronecker_mul, ← mul_kronecker_mul, ← mul_kronecker_mul,
        ← one_kronecker_one, Matrix.mul_one, ← sub_kronecker, ← add_kronecker]
      exact congrArg (· ⊗ₖ (1 : Matrix ι ι ℚ)) P.invHom.eq⟩
  symm := by
    refine (isSymm_iff _).mpr ?_
    rintro ⟨a, j⟩ ⟨b, j'⟩
    change _ * (P.hom.f b a * (1 : Matrix ι ι ℚ) j' j) = P.hom.f a b * (1 : Matrix ι ι ℚ) j j'
    rw [← mul_assoc, (isSymm_iff _).mp P.symm a b]
    rcases eq_or_ne j j' with rfl | h
    · rfl
    · simp [one_apply_ne h, one_apply_ne h.symm]

theorem SymDuality.blocks_hom_f {hC : C.DimLE N} (P : SymDuality C N hC) :
    (P.blocks ι).hom.f = P.hom.f ⊗ₖ 1 := rfl

/-- The chain map `1 ⊗ D` between copies. -/
@[simps]
def blocksMap (C : BasedComplex) (D : Matrix ι' ι ℚ) : Hom (C.blocks ι) (C.blocks ι') where
  f := (1 : Matrix C.X C.X ℚ) ⊗ₖ D
  deg0 := by
    rintro ⟨σ, j⟩ ⟨τ, j'⟩ h
    rw [kronecker_apply] at h
    obtain rfl : σ = τ := by by_contra h'; exact h (by simp [one_apply_ne h'])
    simp
  comm := by
    change C.d ⊗ₖ 1 * _ = _ * C.d ⊗ₖ 1
    rw [← mul_kronecker_mul, ← mul_kronecker_mul]
    simp

/-- The inclusion of the copy `j`. -/
@[simps]
def blocksIncl (C : BasedComplex) (j : ι) : Hom C (C.blocks ι) where
  f := Matrix.of fun p σ ↦ if p.2 = j then (1 : Matrix C.X C.X ℚ) p.1 σ else 0
  deg0 := by
    rintro ⟨σ, j'⟩ τ h
    simp only [of_apply, ne_eq, ite_eq_right_iff, Classical.not_imp] at h
    obtain rfl : σ = τ := by by_contra h'; exact h.2 (one_apply_ne h')
    simp
  comm := by
    ext ⟨κ, j'⟩ σ
    simp [mul_apply, Fintype.sum_prod_type, one_apply, apply_ite]
    split_ifs <;> simp_all

/-- The projection onto the copy `j`. -/
@[simps]
def blocksProj (C : BasedComplex) (j : ι) : Hom (C.blocks ι) C where
  f := (blocksIncl C j).fᵀ
  deg0 p σ h := ((blocksIncl C j).deg0 σ p h).symm
  comm := by
    ext σ ⟨κ, j'⟩
    simp [mul_apply, Fintype.sum_prod_type, one_apply, apply_ite]
    split_ifs <;> simp_all

end Blocks

/-! ### Propagation on copies -/

section BlockProp

variable {X : Type*} [PseudoEMetricSpace X] {A B ι ι' : Type*}

theorem prop_kronecker_one_le [DecidableEq ι] (u : Matrix B A ℚ) (a : ι → A → X) (b : ι → B → X) :
    prop (u ⊗ₖ (1 : Matrix ι ι ℚ)) (fun p ↦ a p.2 p.1) (fun q ↦ b q.2 q.1) ≤
      ⨆ j, prop u (a j) (b j) := by
  refine prop_le_iff.mpr ?_
  rintro ⟨κ, j'⟩ ⟨σ, j⟩ h
  rw [kronecker_apply] at h
  obtain rfl : j' = j := by_contra fun hne ↦ h (by simp [one_apply_ne hne])
  exact (edist_le_prop (left_ne_zero_of_mul h)).trans (le_iSup (fun j ↦ prop u (a j) (b j)) j')

theorem prop_one_kronecker_le [DecidableEq A] (D : Matrix ι' ι ℚ) (a : ι → A → X)
    (b : ι' → A → X) :
    prop ((1 : Matrix A A ℚ) ⊗ₖ D) (fun p ↦ a p.2 p.1) (fun q ↦ b q.2 q.1) ≤
      ⨆ (j') (j) (_ : D j' j ≠ 0) (σ), edist (b j' σ) (a j σ) := by
  refine prop_le_iff.mpr ?_
  rintro ⟨κ, j'⟩ ⟨σ, j⟩ h
  rw [kronecker_apply] at h
  obtain rfl : κ = σ := by_contra fun hne ↦ h (by simp [one_apply_ne hne])
  exact le_iSup_of_le j' <| le_iSup_of_le j <| le_iSup_of_le (right_ne_zero_of_mul h) <|
    le_iSup_of_le κ le_rfl

theorem prop_one_kronecker_diagonal [DecidableEq A] [DecidableEq ι] (v : ι → ℚ) (L : A × ι → X) :
    prop ((1 : Matrix A A ℚ) ⊗ₖ diagonal v) L L = 0 := by
  rw [← diagonal_one, diagonal_kronecker_diagonal, prop_diagonal]

theorem prop_blocksIncl_le {C : BasedComplex} {ι : Type} [Fintype ι] [DecidableEq ι] (j : ι)
    (a : C.X → X) (b : ι → C.X → X) :
    prop (blocksIncl C j).f a (fun q ↦ b q.2 q.1) ≤ ⨆ σ, edist (b j σ) (a σ) := by
  refine prop_le_iff.mpr ?_
  rintro ⟨κ, j'⟩ σ h
  simp only [blocksIncl_f, of_apply, ne_eq, ite_eq_right_iff, Classical.not_imp] at h
  obtain ⟨rfl, h⟩ := h
  obtain rfl : κ = σ := by_contra fun hne ↦ h (one_apply_ne hne)
  exact le_iSup (fun σ ↦ edist (b j' σ) (a σ)) κ

end BlockProp

/-! ### Indicators and the shift -/

section Scalar

variable {ι : Type*} [DecidableEq ι] {n : ℕ}

/-- The diagonal indicator of `S`. -/
def indMat (S : ι → Prop) [DecidablePred S] : Matrix ι ι ℚ := diagonal fun j ↦ if S j then 1 else 0

variable (S S' : ι → Prop) [DecidablePred S] [DecidablePred S']

theorem indMat_mul_indMat [Fintype ι] : indMat S * indMat S' = indMat fun j ↦ S j ∧ S' j := by
  rw [indMat, indMat, indMat, diagonal_mul_diagonal]
  congr 1
  ext j
  split_ifs <;> simp_all

theorem indMat_add_indMat_not : indMat S + indMat (fun j ↦ ¬S j) = 1 := by
  rw [indMat, indMat, diagonal_add, ← diagonal_one]
  congr 1
  ext j
  split_ifs <;> simp_all

theorem indMat_mul_self [Fintype ι] : indMat S * indMat S = indMat S := by
  rw [indMat, diagonal_mul_diagonal]
  congr 1
  ext j
  split_ifs <;> simp

theorem indMat_transpose : (indMat S)ᵀ = indMat S := diagonal_transpose _

/-- The shiftMat `e_b ↦ e_{b+1}` on `Fin (n + 1)`, killing the last basis vector. -/
def shiftMat (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
  of fun a b ↦ if (a : ℕ) = b + 1 then 1 else 0

theorem sum_ite_val_eq_succ (a : Fin (n + 1)) (f : Fin (n + 1) → ℚ) :
    ∑ x : Fin (n + 1), (if (a : ℕ) = (x : ℕ) + 1 then f x else 0) =
      if h : (a : ℕ) = 0 then 0 else f ⟨a - 1, by omega⟩ := by
  split_ifs with h
  · exact Finset.sum_eq_zero fun x _ ↦ ite_eq_right (by omega)
  · rw [Fintype.sum_eq_single ⟨a - 1, by omega⟩ fun x hx ↦ ite_eq_right fun h' ↦ hx (Fin.ext (by
      simp; omega)), ite_eq_left (by simp; omega)]

theorem sum_ite_succ_eq_val (b : Fin (n + 1)) (f : Fin (n + 1) → ℚ) :
    ∑ x : Fin (n + 1), (if (x : ℕ) = (b : ℕ) + 1 then f x else 0) =
      if h : (b : ℕ) = n then 0 else f ⟨b + 1, by omega⟩ := by
  split_ifs with h
  · exact Finset.sum_eq_zero fun x _ ↦ ite_eq_right (by omega)
  · rw [Fintype.sum_eq_single ⟨b + 1, by omega⟩ fun x hx ↦ ite_eq_right fun h' ↦ hx (Fin.ext (by
      simp; omega)), ite_eq_left rfl]

theorem shiftMat_ne_zero {a b : Fin (n + 1)} (h : shiftMat n a b ≠ 0) : (a : ℕ) = b + 1 := by
  by_contra h'
  simp [shiftMat, h'] at h

theorem shiftMat_mul_transpose : shiftMat n * (shiftMat n)ᵀ = indMat (fun a ↦ ¬a = 0) := by
  ext a a'
  simp only [shiftMat, indMat, mul_apply, transpose_apply, of_apply, diagonal_apply, mul_ite,
    mul_one, mul_zero, sum_ite_val_eq_succ, Fin.ext_iff, Fin.val_zero]
  split_ifs <;> first | rfl | (simp; done) | (exfalso; omega)

theorem transpose_mul_shiftMat :
    (shiftMat n)ᵀ * shiftMat n = indMat (fun a ↦ ¬a = Fin.last n) := by
  ext b b'
  simp only [shiftMat, indMat, mul_apply, transpose_apply, of_apply, diagonal_apply, ite_mul,
    one_mul, zero_mul, sum_ite_succ_eq_val, Fin.ext_iff, Fin.val_last]
  split_ifs <;> first | rfl | (simp; done) | (exfalso; omega)

theorem shiftMat_mul_indMat : shiftMat n * indMat (fun a ↦ ¬a = Fin.last n) = shiftMat n := by
  ext a b
  simp only [shiftMat, indMat, mul_diagonal, of_apply, Fin.ext_iff, Fin.val_last]
  split_ifs <;> first | rfl | (simp; done) | (exfalso; omega)

theorem indMat_mul_shiftMat : indMat (fun a ↦ ¬a = 0) * shiftMat n = shiftMat n := by
  ext a b
  simp only [shiftMat, indMat, diagonal_mul, of_apply, Fin.ext_iff, Fin.val_zero]
  split_ifs <;> first | rfl | (simp; done) | (exfalso; omega)

theorem transpose_shiftMat_mul_indMat :
    (shiftMat n)ᵀ * indMat (fun a ↦ ¬a = 0) = (shiftMat n)ᵀ := by
  rw [← indMat_transpose, ← transpose_mul, indMat_mul_shiftMat]

theorem indMat_mul_transpose_shiftMat :
    indMat (fun a ↦ ¬a = Fin.last n) * (shiftMat n)ᵀ = (shiftMat n)ᵀ := by
  rw [← indMat_transpose, ← transpose_mul, shiftMat_mul_indMat]

end Scalar

section BlockIncl

variable {C : BasedComplex} {ι : Type} [Fintype ι] [DecidableEq ι] (j : ι)

theorem blocksIncl_transpose_mul : (blocksIncl C j).fᵀ * (blocksIncl C j).f = 1 := by
  ext σ τ
  simp only [blocksIncl_f, mul_apply, transpose_apply, of_apply, Fintype.sum_prod_type, one_apply,
    mul_ite, mul_one, mul_zero]
  by_cases h : σ = τ
  · subst h; simp
  · simp [h, Ne.symm h]

theorem blocksIncl_mul_transpose :
    (blocksIncl C j).f * (blocksIncl C j).fᵀ = (1 : Matrix C.X C.X ℚ) ⊗ₖ indMat (· = j) := by
  ext ⟨κ, a⟩ ⟨σ, b⟩
  simp only [blocksIncl_f, mul_apply, transpose_apply, of_apply, kronecker_apply, indMat,
    diagonal_apply, one_apply]
  split_ifs <;> simp_all [Finset.sum_ite_eq]

theorem indMat_mul_blocksIncl :
    (1 : Matrix C.X C.X ℚ) ⊗ₖ indMat (· = j) * (blocksIncl C j).f = (blocksIncl C j).f := by
  rw [← blocksIncl_mul_transpose, Matrix.mul_assoc, blocksIncl_transpose_mul, Matrix.mul_one]

theorem blocksIncl_transpose_mul_indMat :
    (blocksIncl C j).fᵀ * (1 : Matrix C.X C.X ℚ) ⊗ₖ indMat (· = j) = (blocksIncl C j).fᵀ := by
  rw [← blocksIncl_mul_transpose, ← Matrix.mul_assoc, blocksIncl_transpose_mul, Matrix.one_mul]

theorem blocksIncl_conj (u : Matrix C.X C.X ℚ) :
    (blocksIncl C j).f * (u * (blocksIncl C j).fᵀ) =
      (1 : Matrix C.X C.X ℚ) ⊗ₖ indMat (· = j) * u ⊗ₖ (1 : Matrix ι ι ℚ) := by
  ext ⟨κ, a⟩ ⟨σ, b⟩
  simp only [blocksIncl_f, mul_apply, transpose_apply, of_apply, kronecker_apply, indMat,
    diagonal_apply, one_apply, Fintype.sum_prod_type]
  rcases eq_or_ne a j with rfl | ha
  · rcases eq_or_ne b a with rfl | hb
    · simp [Finset.sum_ite_eq]
    · simp [hb, Ne.symm hb]
  · simp [ha]

end BlockIncl

/-! ### Uniform control -/

/-- The labellings `ℓ i t` control the complexes, the dualities, their inverses and both
homotopies uniformly in `t : T i`. -/
structure IsUnifControlledDuality {X : Type*} [PseudoEMetricSpace X] {C : ℕ → BasedComplex}
    {N : ℕ} {hN : ∀ i, (C i).DimLE N} (Φ : ∀ i, SymDuality (C i) N (hN i)) {T : ℕ → Type*}
    (ℓ : ∀ i, T i → (C i).X → X) : Prop where
  d : Tendsto (fun i ↦ ⨆ t, prop (C i).d (ℓ i t) (ℓ i t)) atTop (𝓝 0)
  hom : Tendsto (fun i ↦ ⨆ t, prop (Φ i).hom.f (ℓ i t) (ℓ i t)) atTop (𝓝 0)
  inv : Tendsto (fun i ↦ ⨆ t, prop (Φ i).inv.f (ℓ i t) (ℓ i t)) atTop (𝓝 0)
  homInv : Tendsto (fun i ↦ ⨆ t, prop (Φ i).homInv.h (ℓ i t) (ℓ i t)) atTop (𝓝 0)
  invHom : Tendsto (fun i ↦ ⨆ t, prop (Φ i).invHom.h (ℓ i t) (ℓ i t)) atTop (𝓝 0)

namespace IsUnifControlledDuality

variable {X : Type*} [PseudoEMetricSpace X] {C : ℕ → BasedComplex} {N : ℕ}
  {hN : ∀ i, (C i).DimLE N} {Φ : ∀ i, SymDuality (C i) N (hN i)} {T : ℕ → Type*}
  {ℓ : ∀ i, T i → (C i).X → X}

/-- Each labelling of a uniform family is controlling. -/
theorem apply (h : IsUnifControlledDuality Φ ℓ) (t : ∀ i, T i) :
    IsControlledDuality Φ fun i ↦ ℓ i (t i) where
  d := tendsto_zero_of_le h.d fun i ↦ le_iSup (fun t ↦ prop (C i).d (ℓ i t) (ℓ i t)) (t i)
  hom := tendsto_zero_of_le h.hom fun i ↦
    le_iSup (fun t ↦ prop (Φ i).hom.f (ℓ i t) (ℓ i t)) (t i)
  inv := tendsto_zero_of_le h.inv fun i ↦
    le_iSup (fun t ↦ prop (Φ i).inv.f (ℓ i t) (ℓ i t)) (t i)
  homInv := tendsto_zero_of_le h.homInv fun i ↦
    le_iSup (fun t ↦ prop (Φ i).homInv.h (ℓ i t) (ℓ i t)) (t i)
  invHom := tendsto_zero_of_le h.invHom fun i ↦
    le_iSup (fun t ↦ prop (Φ i).invHom.h (ℓ i t) (ℓ i t)) (t i)

/-- The copies `C i ⊗ ℚ^{T i}`, the copy `t` labelled by `ℓ i t`, are controlled. -/
theorem blocks {T : ℕ → Type} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
    {ℓ : ∀ i, T i → (C i).X → X} (h : IsUnifControlledDuality Φ ℓ) :
    IsControlledDuality (fun i ↦ (Φ i).blocks (T i)) fun i p ↦ ℓ i p.2 p.1 where
  d := tendsto_zero_of_le h.d fun _ ↦ prop_kronecker_one_le _ _ _
  hom := tendsto_zero_of_le h.hom fun _ ↦ prop_kronecker_one_le _ _ _
  inv := tendsto_zero_of_le h.inv fun _ ↦ prop_kronecker_one_le _ _ _
  homInv := tendsto_zero_of_le h.homInv fun _ ↦ prop_kronecker_one_le _ _ _
  invHom := tendsto_zero_of_le h.invHom fun _ ↦ prop_kronecker_one_le _ _ _

end IsUnifControlledDuality

/-! ### Lemma 11.1 -/

section Telescope

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  (π : ∀ i, G i →* H) {X : Type} [MulAction H X] [PseudoEMetricSpace X] [IsIsometricSMul H X]
  {C : ℕ → BasedComplex} {N : ℕ} {hN : ∀ i, (C i).DimLE N} {Φ : ∀ i, SymDuality (C i) N (hN i)}

theorem IsControlledDuality.isReducing_id {ℓ : ∀ i, (C i).X → X} (h : IsControlledDuality Φ ℓ) :
    (h.toSymPoincare π).IsReducing ((ControlledSeq.Hom.id h.seq).toComplex π) :=
  h.isReducing π _ (fun _ ↦ Matrix.one_mul _) fun _ ↦ by simp [ControlledSeq.Hom.id]

theorem IsControlledDuality.cls_cut_id {ℓ : ∀ i, (C i).X → X} (h : IsControlledDuality Φ ℓ) :
    Lconc.cls ((h.toSymPoincare π).cut (h.isReducing_id π)) = Lconc.cls (h.toSymPoincare π) :=
  Lconc.cls_cut_of_eq _ _ (by rw [ControlledSeq.Hom.toComplex_id]; exact Category.comp_id _)

namespace IsUnifControlledDuality

variable {k : ℕ → ℕ} {ℓ : ∀ i, Fin (k i + 1) → (C i).X → X} (h : IsUnifControlledDuality Φ ℓ)

/-- `1 ⊗ indMat S` on the copies. -/
def indHom (S : ∀ i, Fin (k i + 1) → Prop) [∀ i, DecidablePred (S i)] :
    h.blocks.seq.Hom h.blocks.seq :=
  ⟨fun i ↦ blocksMap (C i) (indMat (S i)),
    tendsto_zero_of_forall_eq_zero fun _ ↦ prop_one_kronecker_diagonal _ _⟩

theorem isReducing_indHom (S : ∀ i, Fin (k i + 1) → Prop) [∀ i, DecidablePred (S i)] :
    (h.blocks.toSymPoincare π).IsReducing ((h.indHom S).toComplex π) := by
  refine h.blocks.isReducing π _ (fun i ↦ ?_) fun i ↦ ?_
  · change (1 : Matrix (C i).X (C i).X ℚ) ⊗ₖ indMat (S i) * (1 ⊗ₖ indMat (S i)) = 1 ⊗ₖ indMat (S i)
    rw [← mul_kronecker_mul, Matrix.one_mul, indMat_mul_self]
  · change (Φ i).hom.f ⊗ₖ (1 : Matrix (Fin (k i + 1)) _ ℚ) * (1 ⊗ₖ indMat (S i))ᵀ =
      1 ⊗ₖ indMat (S i) * (Φ i).hom.f ⊗ₖ 1
    rw [← kroneckerMap_transpose, transpose_one, indMat_transpose, ← mul_kronecker_mul,
      ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one]

/-- The shiftMat of copies `j ↦ j + 1`, controlled by the step size. -/
def shiftHom (hstep : Tendsto (fun i ↦ ⨆ (j : Fin (k i)) (σ), edist (ℓ i j.succ σ)
      (ℓ i j.castSucc σ)) atTop (𝓝 0)) :
    h.blocks.seq.Hom h.blocks.seq :=
  ⟨fun i ↦ blocksMap (C i) (shiftMat (k i)), tendsto_zero_of_le hstep fun i ↦
    (prop_one_kronecker_le _ _ _).trans <| iSup₂_le fun a b ↦ iSup₂_le fun hab σ ↦ by
      have h₁ := shiftMat_ne_zero hab
      have h₂ := a.2
      refine le_iSup₂_of_le (⟨b, by omega⟩ : Fin (k i)) σ (le_of_eq ?_)
      congr 2
      exact Fin.ext (by simp [h₁])⟩

/-- The transposed shiftMat. -/
def shiftTHom (hstep : Tendsto (fun i ↦ ⨆ (j : Fin (k i)) (σ), edist (ℓ i j.succ σ)
      (ℓ i j.castSucc σ)) atTop (𝓝 0)) :
    h.blocks.seq.Hom h.blocks.seq :=
  ⟨fun i ↦ blocksMap (C i) (shiftMat (k i))ᵀ, by
    have e : ∀ i, (blocksMap (C i) (shiftMat (k i))ᵀ).f = ((blocksMap (C i) (shiftMat (k i))).f)ᵀ :=
      fun i ↦ by rw [blocksMap_f, blocksMap_f, ← kroneckerMap_transpose, transpose_one]
    simpa only [PropTendsto, e, shiftHom] using PropTendsto.transpose (h.shiftHom hstep).tendsto⟩

/-- The inclusion of the copy `j i`. -/
def inclHom (j : ∀ i, Fin (k i + 1)) : (h.apply j).seq.Hom h.blocks.seq :=
  ⟨fun i ↦ blocksIncl (C i) (j i), tendsto_zero_of_forall_eq_zero fun _ ↦
    le_antisymm ((prop_blocksIncl_le _ _ _).trans (by simp)) bot_le⟩

/-- The projection onto the copy `j i`. -/
def projHom (j : ∀ i, Fin (k i + 1)) : h.blocks.seq.Hom (h.apply j).seq :=
  ⟨fun i ↦ blocksProj (C i) (j i), by
    simpa only [PropTendsto, blocksProj_f, prop_transpose, inclHom] using (h.inclHom j).tendsto⟩

theorem cls_apply_eq (j : ∀ i, Fin (k i + 1)) :
    Lconc.cls ((h.apply j).toSymPoincare π) =
      Lconc.cls ((h.blocks.toSymPoincare π).cut (h.isReducing_indHom π fun i a ↦ a = j i)) := by
  rw [← (h.apply j).cls_cut_id π]
  refine (h.apply j).cls_cut_eq_cls_cut π h.blocks _ _ (h.inclHom j) (h.projHom j)
    (fun i ↦ ?_) (fun i ↦ ?_) (fun i ↦ ?_) (fun i ↦ ?_) fun i ↦ ?_
  · change _ * ((blocksIncl (C i) (j i)).f * 1) = _
    rw [Matrix.mul_one]; exact indMat_mul_blocksIncl _
  · change 1 * ((blocksIncl (C i) (j i)).fᵀ * _) = _
    rw [Matrix.one_mul]; exact blocksIncl_transpose_mul_indMat _
  · exact blocksIncl_transpose_mul _
  · exact blocksIncl_mul_transpose _
  · change (blocksIncl (C i) (j i)).f * (1 * ((Φ i).hom.f * (blocksIncl (C i) (j i)).fᵀ)) = _
    rw [Matrix.one_mul]; exact blocksIncl_conj _ _

/-- **Lemma 11.1**, discrete form: labellings `ℓ i 0, …, ℓ i (k i)` controlling `(C i, φ_i)`
uniformly, with consecutive labellings uniformly close, give the same class at both ends. -/
theorem cls_eq_of_steps_obj (hstep : Tendsto (fun i ↦ ⨆ (j : Fin (k i)) (σ),
      edist (ℓ i j.succ σ) (ℓ i j.castSucc σ)) atTop (𝓝 0)) :
    Lconc.cls ((h.apply fun _ ↦ 0).toSymPoincare π) =
      Lconc.cls ((h.apply fun i ↦ Fin.last (k i)).toSymPoincare π) := by
  have hsum (S : ∀ i, Fin (k i + 1) → Prop) [∀ i, DecidablePred (S i)] (i : ℕ) :
      ((h.indHom S).f i).f + ((h.indHom fun i a ↦ ¬S i a).f i).f = 1 := by
    change (1 : Matrix (C i).X (C i).X ℚ) ⊗ₖ _ + 1 ⊗ₖ _ = 1
    rw [← kronecker_add, indMat_add_indMat_not, one_kronecker_one]
  have horth (S S' : ∀ i, Fin (k i + 1) → Prop) [∀ i, DecidablePred (S i)]
      [∀ i, DecidablePred (S' i)] (hS : ∀ i a, ¬(S i a ∧ S' i a)) (i : ℕ) :
      ((h.indHom S).f i).f * ((h.indHom S').f i).f = 0 := by
    change (1 : Matrix (C i).X (C i).X ℚ) ⊗ₖ _ * 1 ⊗ₖ _ = 0
    rw [← mul_kronecker_mul, indMat_mul_indMat, show (indMat fun a ↦ S i a ∧ S' i a) = 0 by
      simp [indMat, hS], kronecker_zero]
  have h₀ := h.blocks.cls_eq_cls_cut_add π (h.isReducing_indHom π fun _ a ↦ a = 0)
    (h.isReducing_indHom π fun _ a ↦ ¬a = 0) (hsum _) (horth _ _ fun _ _ h ↦ h.1 h.2)
    (horth _ _ fun _ _ h ↦ h.2 h.1)
  have h₁ := h.blocks.cls_eq_cls_cut_add π (h.isReducing_indHom π fun i a ↦ a = Fin.last (k i))
    (h.isReducing_indHom π fun i a ↦ ¬a = Fin.last (k i)) (hsum _)
    (horth _ _ fun _ _ h ↦ h.1 h.2) (horth _ _ fun _ _ h ↦ h.2 h.1)
  have hsh : Lconc.cls ((h.blocks.toSymPoincare π).cut
      (h.isReducing_indHom π fun i a ↦ ¬a = Fin.last (k i))) =
      Lconc.cls ((h.blocks.toSymPoincare π).cut (h.isReducing_indHom π fun _ a ↦ ¬a = 0)) := by
    refine h.blocks.cls_cut_eq_cls_cut π h.blocks _ _ (h.shiftHom hstep) (h.shiftTHom hstep)
      (fun i ↦ ?_) (fun i ↦ ?_) (fun i ↦ ?_) (fun i ↦ ?_) fun i ↦ ?_ <;>
      simp only [indHom, shiftHom, shiftTHom, blocksMap_f, SymDuality.blocks_hom_f,
        ← kroneckerMap_transpose, transpose_one, ← mul_kronecker_mul, Matrix.one_mul,
        Matrix.mul_one]
    · rw [shiftMat_mul_indMat, indMat_mul_shiftMat]
    · rw [transpose_shiftMat_mul_indMat, indMat_mul_transpose_shiftMat]
    · rw [transpose_mul_shiftMat]
    · rw [shiftMat_mul_transpose]
    · rw [← Matrix.mul_assoc, shiftMat_mul_indMat, shiftMat_mul_transpose]
  have := h₀.symm.trans h₁
  rw [← hsh] at this
  rw [h.cls_apply_eq π, h.cls_apply_eq π]
  exact add_right_cancel this

/-- **Lemma 11.1**, discrete form in `L(𝒜_G(X))`: labellings `ℓ i 0, …, ℓ i (k i)` controlling
`(C i, φ_i)` uniformly, with consecutive labellings uniformly close, give the same class at both
ends. The proof telescopes: `k i + 1` copies of `C i`, the copy `j` labelled by `ℓ i j`, split as
`P⁰ ⊕ (copies 1..k)` and as `(copies 0..k-1) ⊕ P¹`, and the shift of copies is a controlled
isometry between the two middle parts. -/
theorem cls_eq_of_steps (hstep : Tendsto (fun i ↦ ⨆ (j : Fin (k i)) (σ),
      edist (ℓ i j.succ σ) (ℓ i j.castSucc σ)) atTop (𝓝 0)) :
    Lconc.cls ((h.apply fun _ ↦ 0).toAsymptotic π) =
      Lconc.cls ((h.apply fun i ↦ Fin.last (k i)).toAsymptotic π) := by
  rw [IsControlledDuality.cls_toAsymptotic, IsControlledDuality.cls_toAsymptotic,
    h.cls_eq_of_steps_obj π hstep]

end IsUnifControlledDuality

end Telescope

/-! ### Relabelling along uniformly continuous maps -/

section Relabel

variable {X K T : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace K]

theorem PropTendsto.iSup_comp {C D : ℕ → BasedComplex} {u : ∀ i, Matrix (D i).X (C i).X ℚ}
    {a : ∀ i, (C i).X → K} {b : ∀ i, (D i).X → K} (hu : PropTendsto u a b) {g : T → K → X}
    (hg : UniformEquicontinuous g) :
    Tendsto (fun i ↦ ⨆ t, prop (u i) (fun σ ↦ g t (a i σ)) fun κ ↦ g t (b i κ)) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨δ, hδ, hg⟩ :=
    (uniformity_basis_edist.uniformEquicontinuous_iff uniformity_basis_edist).1 hg ε hε
  filter_upwards [hu.eventually (gt_mem_nhds hδ)] with i hi
  exact iSup_le fun t ↦ prop_le_iff.mpr fun κ σ h ↦
    (hg _ _ ((edist_le_prop h).trans_lt hi) t).le

variable {C : ℕ → BasedComplex} {N : ℕ} {hN : ∀ i, (C i).DimLE N}
  {Φ : ∀ i, SymDuality (C i) N (hN i)} {c : ∀ i, (C i).X → K}

/-- Control over `K` pushes forward along a uniformly equicontinuous family `g t : K → X`,
uniformly in `t`. -/
theorem IsControlledDuality.unifComp (hc : IsControlledDuality Φ c) {g : T → K → X}
    (hg : UniformEquicontinuous g) :
    IsUnifControlledDuality Φ fun i t σ ↦ g t (c i σ) :=
  ⟨hc.d.iSup_comp hg, hc.hom.iSup_comp hg, hc.inv.iSup_comp hg, hc.homInv.iSup_comp hg,
    hc.invHom.iSup_comp hg⟩

/-- Control over `K` pushes forward along a uniformly continuous `f : K → X`. -/
theorem IsControlledDuality.comp (hc : IsControlledDuality Φ c) {f : K → X}
    (hf : UniformContinuous f) : IsControlledDuality Φ fun i σ ↦ f (c i σ) :=
  ⟨.of_uniformContinuous hf hc.d, .of_uniformContinuous hf hc.hom,
    .of_uniformContinuous hf hc.inv, .of_uniformContinuous hf hc.homInv,
    .of_uniformContinuous hf hc.invHom⟩

/-- Reparametrizing a uniform family keeps it uniform. -/
theorem IsUnifControlledDuality.comp {T : ℕ → Type*} {T' : ℕ → Type*}
    {ℓ : ∀ i, T i → (C i).X → X} (h : IsUnifControlledDuality Φ ℓ) (f : ∀ i, T' i → T i) :
    IsUnifControlledDuality Φ fun i t ↦ ℓ i (f i t) where
  d := tendsto_zero_of_le h.d fun i ↦ iSup_le fun t ↦
    le_iSup (fun t ↦ prop (C i).d (ℓ i t) (ℓ i t)) (f i t)
  hom := tendsto_zero_of_le h.hom fun i ↦ iSup_le fun t ↦
    le_iSup (fun t ↦ prop (Φ i).hom.f (ℓ i t) (ℓ i t)) (f i t)
  inv := tendsto_zero_of_le h.inv fun i ↦ iSup_le fun t ↦
    le_iSup (fun t ↦ prop (Φ i).inv.f (ℓ i t) (ℓ i t)) (f i t)
  homInv := tendsto_zero_of_le h.homInv fun i ↦ iSup_le fun t ↦
    le_iSup (fun t ↦ prop (Φ i).homInv.h (ℓ i t) (ℓ i t)) (f i t)
  invHom := tendsto_zero_of_le h.invHom fun i ↦ iSup_le fun t ↦
    le_iSup (fun t ↦ prop (Φ i).invHom.h (ℓ i t) (ℓ i t)) (f i t)

end Relabel

/-! ### Lemma 11.1 for homotopies -/

/-- The grid point `j / k` of `[0, 1]`. -/
def unitTick (k j : ℕ) : unitInterval := Set.projIcc 0 1 zero_le_one (j / k)

theorem unitTick_zero (k : ℕ) : unitTick k 0 = 0 := by
  simp [unitTick, Set.projIcc_left]

theorem unitTick_self {k : ℕ} (hk : k ≠ 0) : unitTick k k = 1 := by
  rw [unitTick, div_self (Nat.cast_ne_zero.2 hk : (k : ℝ) ≠ 0), Set.projIcc_right]
  rfl

theorem edist_unitTick_succ_le (k j : ℕ) :
    edist (unitTick k (j + 1)) (unitTick k j) ≤ ENNReal.ofReal (1 / k) := by
  rw [edist_dist, Subtype.dist_eq, Real.dist_eq]
  refine ENNReal.ofReal_le_ofReal ((Set.abs_projIcc_sub_projIcc _).trans_eq ?_)
  push_cast
  rw [← sub_div, add_sub_cancel_left, abs_of_nonneg (by positivity)]

section Homotopy

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  (π : ∀ i, G i →* H) {X : Type} [MulAction H X] [PseudoEMetricSpace X] [IsIsometricSMul H X]
  {C : ℕ → BasedComplex} {N : ℕ} {hN : ∀ i, (C i).DimLE N} {Φ : ∀ i, SymDuality (C i) N (hN i)}

/-- **Lemma 11.1.** A homotopy of labellings `ℓ i t`, `t ∈ [0, 1]`, of a sequence of based
symmetric dualities `(C i, φ_i)`, which controls the complexes, the dualities, their inverses and
both homotopies uniformly in `t` and is uniformly equicontinuous in `t` (uniformly in `i` and the
cell), gives the same class `[C, ℓ 0] = [C, ℓ 1]` in `L(𝒜_G(X))`. -/
theorem IsUnifControlledDuality.cls_eq_of_homotopy {ℓ : ∀ i, unitInterval → (C i).X → X}
    (h : IsUnifControlledDuality Φ ℓ)
    (hℓ : UniformEquicontinuous fun p : (Σ i, (C i).X) ↦ fun t ↦ ℓ p.1 t p.2) :
    Lconc.cls ((h.apply fun _ ↦ 0).toAsymptotic π) =
      Lconc.cls ((h.apply fun _ ↦ 1).toAsymptotic π) := by
  have hτ := h.comp fun i (j : Fin (i + 1 + 1)) ↦ unitTick (i + 1) j
  have hstep : Tendsto (fun i ↦ ⨆ (j : Fin (i + 1)) (σ), edist (ℓ i (unitTick (i + 1) j.succ) σ)
      (ℓ i (unitTick (i + 1) j.castSucc) σ)) atTop (𝓝 0) := by
    refine ENNReal.tendsto_nhds_zero.2 fun ε hε ↦ ?_
    obtain ⟨δ, hδ, hℓδ⟩ :=
      (uniformity_basis_edist.uniformEquicontinuous_iff uniformity_basis_edist).1 hℓ ε hε
    have h₀ : Tendsto (fun i : ℕ ↦ ENNReal.ofReal (1 / ((i + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal ((tendsto_one_div_add_atTop_nhds_zero_nat).congr
        fun i ↦ by push_cast; rfl)
    filter_upwards [(tendsto_order.1 h₀).2 δ hδ] with i hi
    refine iSup₂_le fun j σ ↦ (hℓδ _ _ ?_ ⟨i, σ⟩).le
    rw [Fin.val_succ, Fin.val_castSucc]
    exact (edist_unitTick_succ_le _ _).trans_lt hi
  have := hτ.cls_eq_of_steps π hstep
  rwa [IsControlledDuality.cls_toAsymptotic_congr π (hτ.apply fun _ ↦ 0) (h.apply fun _ ↦ 0)
      (funext fun i ↦ by rw [Fin.val_zero, unitTick_zero]),
    IsControlledDuality.cls_toAsymptotic_congr π (hτ.apply fun i ↦ Fin.last (i + 1))
      (h.apply fun _ ↦ 1)
      (funext fun i ↦ by rw [Fin.val_last, unitTick_self (Nat.succ_ne_zero i)])] at this

/-- **Lemma 11.1 for the germ** ((11.3)): cells with centres `c i σ` in a compact space `K`, the
complexes and dualities controlled over `K`, labelled by `f ∘ c` for continuous `f : K → X`
(uniformly continuous by compactness). Homotopic `f₀ ≃ f₁` give the same class. -/
theorem IsControlledDuality.cls_eq_of_homotopic {K : Type*} [PseudoEMetricSpace K]
    [CompactSpace K] {c : ∀ i, (C i).X → K} (hc : IsControlledDuality Φ c) {f₀ f₁ : C(K, X)}
    (hf : f₀.Homotopic f₁) (h₀ : IsControlledDuality Φ fun i σ ↦ f₀ (c i σ))
    (h₁ : IsControlledDuality Φ fun i σ ↦ f₁ (c i σ)) :
    Lconc.cls (h₀.toAsymptotic π) = Lconc.cls (h₁.toAsymptotic π) := by
  obtain ⟨F⟩ := hf
  have hF := EMetric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous F.continuous)
  have hg : UniformEquicontinuous fun (t : unitInterval) (x : K) ↦ F (t, x) :=
    (uniformity_basis_edist.uniformEquicontinuous_iff uniformity_basis_edist).2 fun ε hε ↦
      let ⟨δ, hδ, h⟩ := hF ε hε
      ⟨δ, hδ, fun x y hxy t ↦ h (by simpa [Prod.edist_eq] using hxy)⟩
  have hU := hc.unifComp hg
  have := hU.cls_eq_of_homotopy π
    ((uniformity_basis_edist.uniformEquicontinuous_iff uniformity_basis_edist).2 fun ε hε ↦
      let ⟨δ, hδ, h⟩ := hF ε hε
      ⟨δ, hδ, fun s t hst p ↦ h (by simpa [Prod.edist_eq] using hst)⟩)
  rwa [IsControlledDuality.cls_toAsymptotic_congr π _ h₀ (funext fun i ↦ funext fun σ ↦
      F.apply_zero _),
    IsControlledDuality.cls_toAsymptotic_congr π _ h₁ (funext fun i ↦ funext fun σ ↦
      F.apply_one _)] at this

end Homotopy

/-! ### The cubical germ `Tⁿ ⊗ CPcell` -/

section Torus

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  (π : ∀ i, G i →* H) {X : Type} [MulAction H X] [PseudoEMetricSpace X] [IsIsometricSMul H X]
  (L : ℝ) [Fact (0 < L)] (n : ℕ) {m : ℕ → ℕ} [∀ i, NeZero (m i)]

/-- The centres control `W_i = Tⁿ_{m_i} ⊗ CPcell` and its duality over the torus `(ℝ/Lℤ)ⁿ`. -/
theorem torusCP.isControlledDuality (hm : Tendsto m atTop atTop) :
    IsControlledDuality (fun i ↦ torusCP.duality (m i) n)
      fun i q ↦ torus.center L (m i) n q.1 where
  d := tendsto_zero_of_le (tendsto_ofReal_mesh L hm) fun i ↦
    (torusCP.prop_d_le L (m i) n).trans (torus.le_mesh L (m i))
  hom := tendsto_zero_of_le (tendsto_ofReal_mesh L hm) fun i ↦
    (torusCP.propLE L (m i) n).hom.trans (torus.le_mesh L (m i))
  inv := tendsto_zero_of_le (tendsto_ofReal_mesh L hm) fun i ↦
    (torusCP.propLE L (m i) n).inv.trans (torus.le_mesh L (m i))
  homInv := tendsto_zero_of_le (tendsto_ofReal_mesh L hm) fun i ↦
    (torusCP.propLE L (m i) n).homInv
  invHom := tendsto_zero_of_le (tendsto_ofReal_mesh L hm) fun i ↦
    (torusCP.propLE L (m i) n).invHom

/-- **(11.3) for the cubical germ**: `W_i = Tⁿ_{m_i} ⊗ CPcell` labelled by `f ∘ centre` for a
continuous `f : (ℝ/Lℤ)ⁿ → X`; homotopic `f₀ ≃ f₁` give the same class in `L(𝒜_G(X))`. -/
theorem torusCP.cls_eq_of_homotopic (hm : Tendsto m atTop atTop)
    {f₀ f₁ : C(Fin n → AddCircle L, X)} (hf : f₀.Homotopic f₁) :
    Lconc.cls (((torusCP.isControlledDuality L n hm).comp
        (CompactSpace.uniformContinuous_of_continuous f₀.continuous)).toAsymptotic π) =
      Lconc.cls (((torusCP.isControlledDuality L n hm).comp
        (CompactSpace.uniformContinuous_of_continuous f₁.continuous)).toAsymptotic π) :=
  (torusCP.isControlledDuality L n hm).cls_eq_of_homotopic π hf _ _

end Torus

end BasedComplex

end HSFormal.Cubical
