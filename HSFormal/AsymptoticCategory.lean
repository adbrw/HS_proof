import HSFormal.ControlledMatrices
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.CategoryTheory.Quotient.Linear
import Mathlib.CategoryTheory.Quotient.Preadditive
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.CategoryTheory.Idempotents.Biproducts
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# The asymptotic category `𝒜_G(X)` of manuscript §2

Fix groups `G i` (finite), a group `H` acting on `X`, and homomorphisms `π i : G i →* H`
(the manuscript takes `G i = C_{p^{a_i}}`, `H = C_p`).  An object is a sequence of finite
free `G i`-sets `Fin (rank i) × G i` (left multiplication on the second factor) with labels
`(k, g) ↦ π i g • label i k`, equivariant through `π i`.  Every finite free `G i`-set with an
equivariant labelling is based-isomorphic to one of this form, which keeps the category small.

Morphisms are sequences of `G`-equivariant rational matrices whose propagation (2.1) tends to
zero, modulo eventual exact equality.  We build the prequotient category `AsymptoticObject π X`,
the quotient `AsymptoticCategory π X`, its `ℚ`-linear preadditive structure, zero object,
finite biproducts, transpose duality and Karoubi completion.
-/

noncomputable section

namespace HSFormal

open Filter Matrix CategoryTheory CategoryTheory.Limits
open scoped Classical ENNReal Topology

universe u

/-! ### Propagation, (2.1) and (2.2) -/

section Propagation

variable {A B C X : Type*} [PseudoEMetricSpace X]

/-- Manuscript (2.1): `prop u = sup_{u b a ≠ 0} d(target b, source a)`; empty sups are `0`. -/
def prop (u : Matrix B A ℚ) (source : A → X) (target : B → X) : ℝ≥0∞ :=
  ⨆ (b) (a) (_ : u b a ≠ 0), edist (target b) (source a)

variable {u v : Matrix B A ℚ} {source : A → X} {target : B → X}

theorem prop_le_iff {r : ℝ≥0∞} :
    prop u source target ≤ r ↔ ∀ b a, u b a ≠ 0 → edist (target b) (source a) ≤ r := by
  simp only [prop, iSup_le_iff]

theorem edist_le_prop {b : B} {a : A} (h : u b a ≠ 0) :
    edist (target b) (source a) ≤ prop u source target :=
  prop_le_iff.mp le_rfl b a h

/-- Manuscript (2.2), first inequality. -/
theorem prop_mul_le [Fintype B] (w : Matrix C B ℚ) (middle : B → X) (target' : C → X)
    (u : Matrix B A ℚ) :
    prop (w * u) source target' ≤ prop u source middle + prop w middle target' := by
  rw [prop_le_iff]
  intro c a h
  obtain ⟨b, hw, hu⟩ := matrix_mul_entry_nonzero_witness u w c a h
  calc edist (target' c) (source a)
      ≤ edist (target' c) (middle b) + edist (middle b) (source a) := edist_triangle _ _ _
    _ ≤ prop w middle target' + prop u source middle :=
        add_le_add (edist_le_prop hw) (edist_le_prop hu)
    _ = _ := add_comm _ _

/-- Manuscript (2.2), second inequality. -/
theorem prop_add_le :
    prop (u + v) source target ≤ max (prop u source target) (prop v source target) := by
  rw [prop_le_iff]
  intro b a h
  by_cases hu : u b a = 0
  · have hv : v b a ≠ 0 := by simpa [hu] using h
    exact (edist_le_prop hv).trans (le_max_right _ _)
  · exact (edist_le_prop hu).trans (le_max_left _ _)

@[simp]
theorem prop_zero : prop (0 : Matrix B A ℚ) source target = 0 :=
  le_antisymm (prop_le_iff.mpr fun _ _ h ↦ (h rfl).elim) bot_le

theorem prop_smul_le (c : ℚ) : prop (c • u) source target ≤ prop u source target :=
  prop_le_iff.mpr fun _ _ h ↦ edist_le_prop (right_ne_zero_of_mul h)

@[simp]
theorem prop_neg : prop (-u) source target = prop u source target := by
  simp only [prop, Matrix.neg_apply, ne_eq, neg_eq_zero]

/-- Duality: the transpose has the same propagation. -/
@[simp]
theorem prop_transpose : prop uᵀ target source = prop u source target := by
  simp only [prop, Matrix.transpose_apply]
  rw [iSup_comm]
  simp only [edist_comm]

theorem prop_submatrix_le {A' B' : Type*} (f : A' → A) (g : B' → B) :
    prop (u.submatrix g f) (source ∘ f) (target ∘ g) ≤ prop u source target :=
  prop_le_iff.mpr fun _ _ h ↦ edist_le_prop (u := u) h

theorem prop_diagonal [DecidableEq A] (d : A → ℚ) (label : A → X) : prop (diagonal d) label label = 0 := by
  refine le_antisymm (prop_le_iff.mpr fun b a h ↦ ?_) bot_le
  by_cases hba : b = a
  · simp [hba]
  · exact (h (diagonal_apply_ne d hba)).elim

theorem prop_one [DecidableEq A] (label : A → X) : prop (1 : Matrix A A ℚ) label label = 0 :=
  prop_diagonal _ label

/-- Bridge to the real-valued calculus of `HSFormal.ControlledMatrices`. -/
theorem prop_le_ofReal_iff {Y : Type*} [PseudoMetricSpace Y] {u : Matrix B A ℚ}
    {source : A → Y} {target : B → Y} {r : ℝ} (hr : 0 ≤ r) :
    prop u source target ≤ ENNReal.ofReal r ↔ HasPropagationLE u source target r := by
  rw [prop_le_iff]
  refine forall₂_congr fun b a ↦ imp_congr_right fun _ ↦ ?_
  rw [edist_dist, ENNReal.ofReal_le_ofReal_iff hr]

end Propagation

/-! ### Equivariant matrices between free bases `Fin n × Γ` -/

section Equivariant

variable {Γ : Type*} [Group Γ] {l m n : ℕ}

/-- `u (g • b') (g • b) = u b' b` for the free left action on `Fin n × Γ`. -/
def IsEquivariant (u : Matrix (Fin n × Γ) (Fin m × Γ) ℚ) : Prop :=
  ∀ (g : Γ) (b' : Fin n × Γ) (b : Fin m × Γ), u (b'.1, g * b'.2) (b.1, g * b.2) = u b' b

namespace IsEquivariant

variable {u v : Matrix (Fin n × Γ) (Fin m × Γ) ℚ}

theorem zero : IsEquivariant (0 : Matrix (Fin n × Γ) (Fin m × Γ) ℚ) := fun _ _ _ ↦ rfl

theorem add (hu : IsEquivariant u) (hv : IsEquivariant v) : IsEquivariant (u + v) :=
  fun g b' b ↦ by simp [hu g b' b, hv g b' b]

theorem neg (hu : IsEquivariant u) : IsEquivariant (-u) :=
  fun g b' b ↦ by simp [hu g b' b]

theorem smul (c : ℚ) (hu : IsEquivariant u) : IsEquivariant (c • u) :=
  fun g b' b ↦ by simp [hu g b' b]

theorem one : IsEquivariant (1 : Matrix (Fin n × Γ) (Fin n × Γ) ℚ) := by
  intro g b' b
  simp only [Matrix.one_apply, mul_right_inj, Prod.ext_iff]

theorem transpose (hu : IsEquivariant u) : IsEquivariant uᵀ :=
  fun g b' b ↦ hu g b b'

theorem diagonal (d : Fin n → ℚ) :
    IsEquivariant (Matrix.diagonal fun b : Fin n × Γ ↦ d b.1) := by
  intro g b' b
  by_cases h : b' = b
  · subst h; simp
  · have h' : ((b'.1, g * b'.2) : Fin n × Γ) ≠ (b.1, g * b.2) := by
      simpa [Prod.ext_iff] using fun h1 h2 ↦ h (Prod.ext h1 h2)
    rw [diagonal_apply_ne _ h, diagonal_apply_ne _ h']

theorem mul [Fintype Γ] {w : Matrix (Fin l × Γ) (Fin n × Γ) ℚ} (hw : IsEquivariant w)
    (hu : IsEquivariant u) : IsEquivariant (w * u) := by
  intro g c a
  simp only [Matrix.mul_apply]
  rw [← (Equiv.prodCongr (Equiv.refl (Fin n)) (Equiv.mulLeft g)).sum_comp]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  change w (c.1, g * c.2) (b.1, g * b.2) * u (b.1, g * b.2) (a.1, g * a.2) = _
  rw [hw g c b, hu g b a]

end IsEquivariant

end Equivariant

theorem tendsto_zero_of_le {a b : ℕ → ℝ≥0∞} (hb : Tendsto b atTop (𝓝 0)) (h : ∀ i, a i ≤ b i) :
    Tendsto a atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun _ ↦ zero_le) h

theorem tendsto_zero_of_forall_eq_zero {a : ℕ → ℝ≥0∞} (h : ∀ i, a i = 0) :
    Tendsto a atTop (𝓝 0) := by
  rw [show a = fun _ ↦ 0 from funext h]
  exact tendsto_const_nhds

theorem tendsto_zero_of_eventually_le {a b : ℕ → ℝ≥0∞} (hb : Tendsto b atTop (𝓝 0))
    (h : ∀ᶠ i in atTop, a i ≤ b i) : Tendsto a atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
    (Eventually.of_forall fun _ ↦ zero_le) h

/-! ### Objects and controlled families -/

/-- Every finite free `Γ`-set with a labelling equivariant through `ρ` is, by an equivariant
label-preserving bijection, a basis `Fin n × Γ` with labels `(k, g) ↦ ρ g • ℓ₀ k`. -/
theorem exists_equiv_fin_prod_of_free {H Γ B Z : Type*} [Group H] [Group Γ] [MulAction Γ B]
    [Finite B] [MulAction H Z] (hfree : ∀ (g : Γ) (b : B), g • b = b → g = 1) (ρ : Γ →* H)
    (ℓ : B → Z) (hℓ : ∀ (g : Γ) b, ℓ (g • b) = ρ g • ℓ b) :
    ∃ (n : ℕ) (e : Fin n × Γ ≃ B) (ℓ₀ : Fin n → Z),
      (∀ (g : Γ) (p : Fin n × Γ), e (p.1, g * p.2) = g • e p) ∧
        ∀ p, ℓ (e p) = ρ p.2 • ℓ₀ p.1 := by
  let Q := MulAction.orbitRel.Quotient Γ B
  let e₀ : Fin (Nat.card Q) ≃ Q := (Finite.equivFin Q).symm
  let f : Fin (Nat.card Q) × Γ → B := fun p ↦ p.2 • (e₀ p.1).out
  have hmk : ∀ p, (⟦f p⟧ : Q) = e₀ p.1 := fun p ↦
    (Quotient.sound (MulAction.mem_orbit _ p.2)).trans (Quotient.out_eq _)
  have hinj : Function.Injective f := by
    rintro ⟨k, g⟩ ⟨k', g'⟩ h
    have hk : k = k' := e₀.injective ((hmk (k, g)).symm.trans ((congrArg _ h).trans (hmk _)))
    subst hk
    have : (g'⁻¹ * g) • (e₀ k).out = (e₀ k).out := by
      rw [← smul_smul, show g • (e₀ k).out = g' • (e₀ k).out from h, inv_smul_smul]
    rw [inv_mul_eq_one.mp (hfree _ _ this)]
  have hsurj : Function.Surjective f := by
    intro b
    obtain ⟨g, hg⟩ := Quotient.mk_out (s := MulAction.orbitRel Γ B) b
    refine ⟨(e₀.symm ⟦b⟧, g⁻¹), ?_⟩
    simp only [f, Equiv.apply_symm_apply]
    rw [← hg, inv_smul_smul]
  refine ⟨_, Equiv.ofBijective f ⟨hinj, hsurj⟩, fun k ↦ ℓ (e₀ k).out, fun g p ↦ ?_, fun p ↦ ?_⟩
  · show f (p.1, g * p.2) = g • f p
    simp [f, smul_smul]
  · show ℓ (f p) = _
    simp [f, hℓ]

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)]

/-- An object of `𝒜_G(X)`: at index `i` the free `G i`-basis `Fin (rank i) × G i`, whose orbit
representatives `(k, 1)` carry the labels `label i k`. -/
structure AsymptoticObject (π : ∀ i, G i →* H) (X : Type u) where
  rank : ℕ → ℕ
  label : ∀ i, Fin (rank i) → X

namespace AsymptoticObject

variable {π : ∀ i, G i →* H} {X : Type u}

/-- Rational matrix families, target rows and source columns. -/
abbrev Family (M N : AsymptoticObject π X) : Type :=
  ∀ i, Matrix (Fin (N.rank i) × G i) (Fin (M.rank i) × G i) ℚ

section Label

variable [MulAction H X]

/-- The labelling of the whole free basis, equivariant through `π i`. -/
def fullLabel (M : AsymptoticObject π X) (i : ℕ) (b : Fin (M.rank i) × G i) : X :=
  π i b.2 • M.label i b.1

theorem fullLabel_smul (M : AsymptoticObject π X) (i : ℕ) (g : G i)
    (b : Fin (M.rank i) × G i) : M.fullLabel i (b.1, g * b.2) = π i g • M.fullLabel i b := by
  simp [fullLabel, smul_smul]

@[simp]
theorem fullLabel_one (M : AsymptoticObject π X) (i : ℕ) (k : Fin (M.rank i)) :
    M.fullLabel i (k, 1) = M.label i k := by
  simp [fullLabel]

/-- The manuscript's objects (sequences of finite free `G i`-sets `B i` with labels equivariant
through `π i`) are based-isomorphic to objects of `AsymptoticObject π X`. -/
theorem exists_of_free (B : ℕ → Type*) [∀ i, MulAction (G i) (B i)] [∀ i, Finite (B i)]
    (hfree : ∀ i (g : G i) (b : B i), g • b = b → g = 1) (ℓ : ∀ i, B i → X)
    (hℓ : ∀ i (g : G i) b, ℓ i (g • b) = π i g • ℓ i b) :
    ∃ (M : AsymptoticObject π X) (e : ∀ i, Fin (M.rank i) × G i ≃ B i),
      ∀ i, (∀ (g : G i) p, e i (p.1, g * p.2) = g • e i p) ∧
        ∀ p, ℓ i (e i p) = M.fullLabel i p := by
  choose n e ℓ₀ he hℓ₀ using fun i ↦ exists_equiv_fin_prod_of_free (hfree i) (π i) (ℓ i) (hℓ i)
  exact ⟨⟨n, ℓ₀⟩, e, fun i ↦ ⟨he i, hℓ₀ i⟩⟩

end Label

variable [MulAction H X] [PseudoEMetricSpace X] [∀ i, Fintype (G i)]

/-- The propagation sequence `i ↦ prop (f i)`. -/
def propSeq (M N : AsymptoticObject π X) (f : Family M N) (i : ℕ) : ℝ≥0∞ :=
  prop (f i) (M.fullLabel i) (N.fullLabel i)

/-- Morphisms of `𝒜_G(X)` before passing to eventual equality: equivariant matrix sequences
satisfying (2.1). -/
structure IsControlled (M N : AsymptoticObject π X) (f : Family M N) : Prop where
  equivariant : ∀ i, IsEquivariant (f i)
  tendsto_prop : Tendsto (propSeq M N f) atTop (𝓝 0)

section Control

variable {M N P : AsymptoticObject π X}

omit [∀ i, Fintype (G i)] in
theorem isControlled_zero : IsControlled M N 0 :=
  ⟨fun _ ↦ IsEquivariant.zero, tendsto_zero_of_forall_eq_zero fun _ ↦ by simp [propSeq]⟩

omit [∀ i, Fintype (G i)] in
theorem isControlled_add {f g : Family M N} (hf : IsControlled M N f)
    (hg : IsControlled M N g) : IsControlled M N (f + g) :=
  ⟨fun i ↦ (hf.equivariant i).add (hg.equivariant i),
    tendsto_zero_of_le (by simpa [propSeq] using hf.tendsto_prop.max hg.tendsto_prop)
      fun _ ↦ prop_add_le⟩

omit [∀ i, Fintype (G i)] in
theorem isControlled_smul (c : ℚ) {f : Family M N} (hf : IsControlled M N f) :
    IsControlled M N (c • f) :=
  ⟨fun i ↦ (hf.equivariant i).smul c, tendsto_zero_of_le hf.tendsto_prop
    fun _ ↦ prop_smul_le c⟩

omit [∀ i, Fintype (G i)] in
theorem isControlled_id (M : AsymptoticObject π X) : IsControlled M M fun _ ↦ 1 :=
  ⟨fun _ ↦ IsEquivariant.one, tendsto_zero_of_forall_eq_zero fun i ↦ prop_one (M.fullLabel i)⟩

theorem isControlled_comp {f : Family M N} {g : Family N P} (hf : IsControlled M N f)
    (hg : IsControlled N P g) : IsControlled M P fun i ↦ g i * f i :=
  ⟨fun i ↦ (hg.equivariant i).mul (hf.equivariant i),
    tendsto_zero_of_le (by simpa [propSeq] using hf.tendsto_prop.add hg.tendsto_prop)
      fun i ↦ prop_mul_le _ _ _ _⟩

end Control

/-- The controlled families form a rational subspace. -/
def homSubmodule (M N : AsymptoticObject π X) : Submodule ℚ (Family M N) where
  carrier := {f | IsControlled M N f}
  zero_mem' := isControlled_zero
  add_mem' hf hg := isControlled_add hf hg
  smul_mem' c _ hf := isControlled_smul c hf

/-- The prequotient category: honest controlled families, no identifications. -/
instance category : Category.{0} (AsymptoticObject π X) where
  Hom M N := homSubmodule M N
  id M := ⟨fun _ ↦ 1, isControlled_id M⟩
  comp f g := ⟨fun i ↦ g.1 i * f.1 i, isControlled_comp f.2 g.2⟩
  id_comp f := Subtype.ext <| funext fun i ↦ Matrix.mul_one (f.1 i)
  comp_id f := Subtype.ext <| funext fun i ↦ Matrix.one_mul (f.1 i)
  assoc f g h := Subtype.ext <| funext fun i ↦ (Matrix.mul_assoc (h.1 i) (g.1 i) (f.1 i)).symm

instance preadditive : Preadditive (AsymptoticObject π X) where
  homGroup M N := inferInstanceAs (AddCommGroup (homSubmodule M N))
  add_comp _ _ _ f f' g := Subtype.ext <| funext fun i ↦ Matrix.mul_add (g.1 i) (f.1 i) (f'.1 i)
  comp_add _ _ _ f g g' := Subtype.ext <| funext fun i ↦ Matrix.add_mul (g.1 i) (g'.1 i) (f.1 i)

instance linear : Linear ℚ (AsymptoticObject π X) where
  homModule M N := inferInstanceAs (Module ℚ (homSubmodule M N))
  smul_comp _ _ _ c f g := Subtype.ext <| funext fun i ↦ Matrix.mul_smul (g.1 i) c (f.1 i)
  comp_smul _ _ _ f c g := Subtype.ext <| funext fun i ↦ Matrix.smul_mul c (g.1 i) (f.1 i)

section Simp

variable {M N P : AsymptoticObject π X}

theorem hom_ext {f g : M ⟶ N} (h : ∀ i, f.1 i = g.1 i) : f = g :=
  Subtype.ext (funext h)

@[simp] theorem id_val (i : ℕ) : (𝟙 M : M ⟶ M).1 i = 1 := rfl
@[simp] theorem comp_val (f : M ⟶ N) (g : N ⟶ P) (i : ℕ) : (f ≫ g).1 i = g.1 i * f.1 i := rfl
@[simp] theorem zero_val (i : ℕ) : (0 : M ⟶ N).1 i = 0 := rfl
@[simp] theorem add_val (f g : M ⟶ N) (i : ℕ) : (f + g).1 i = f.1 i + g.1 i := rfl
@[simp] theorem neg_val (f : M ⟶ N) (i : ℕ) : (-f).1 i = -f.1 i := rfl
@[simp] theorem sub_val (f g : M ⟶ N) (i : ℕ) : (f - g).1 i = f.1 i - g.1 i := rfl
@[simp] theorem smul_val (c : ℚ) (f : M ⟶ N) (i : ℕ) : (c • f).1 i = c • f.1 i := rfl

theorem equivariant (f : M ⟶ N) (i : ℕ) : IsEquivariant (f.1 i) := f.2.equivariant i

theorem tendsto_propSeq (f : M ⟶ N) : Tendsto (propSeq M N f.1) atTop (𝓝 0) :=
  f.2.tendsto_prop

end Simp

/-! ### Based free summands -/

section Summands

/-- An injective, label-preserving map of orbit representatives: a based free summand. -/
structure OrbitEmbedding (M N : AsymptoticObject π X) where
  toFun : ∀ i, Fin (M.rank i) → Fin (N.rank i)
  injective : ∀ i, Function.Injective (toFun i)
  label_toFun : ∀ i k, N.label i (toFun i k) = M.label i k

/-- The based projection onto the orbits satisfying `P`; it has propagation zero. -/
def diagProj (M : AsymptoticObject π X) (P : ∀ i, Fin (M.rank i) → Prop) : M ⟶ M :=
  ⟨fun i ↦ diagonal fun b ↦ if P i b.1 then 1 else 0,
    ⟨fun i ↦ IsEquivariant.diagonal fun k ↦ if P i k then 1 else 0,
      tendsto_zero_of_forall_eq_zero fun i ↦ prop_diagonal _ (M.fullLabel i)⟩⟩

@[simp]
theorem diagProj_val (M : AsymptoticObject π X) (P : ∀ i, Fin (M.rank i) → Prop) (i : ℕ) :
    (M.diagProj P).1 i = diagonal fun b ↦ if P i b.1 then 1 else 0 := rfl

theorem diagProj_comp_diagProj (M : AsymptoticObject π X) (P Q : ∀ i, Fin (M.rank i) → Prop)
    (h : ∀ i k, P i k → Q i k) :
    M.diagProj P ≫ M.diagProj Q = M.diagProj P ∧ M.diagProj Q ≫ M.diagProj P = M.diagProj P := by
  constructor <;> refine hom_ext fun i ↦ ?_ <;>
    simp only [comp_val, diagProj_val, diagonal_mul_diagonal] <;>
    congr 1 <;> funext b <;> by_cases hP : P i b.1 <;> simp [hP, h i b.1]

theorem diagProj_true (M : AsymptoticObject π X) : M.diagProj (fun _ _ ↦ True) = 𝟙 M :=
  hom_ext fun i ↦ by simp [Matrix.diagonal_one]

theorem diagProj_add_compl (M : AsymptoticObject π X) (P : ∀ i, Fin (M.rank i) → Prop) :
    M.diagProj P + M.diagProj (fun i k ↦ ¬ P i k) = 𝟙 M := by
  refine hom_ext fun i ↦ ?_
  simp only [add_val, diagProj_val, diagonal_add, id_val]
  rw [← diagonal_one]
  congr 1; funext b; by_cases hP : P i b.1 <;> simp [hP]

namespace OrbitEmbedding

variable {M N P : AsymptoticObject π X} (e : OrbitEmbedding M N)

/-- The induced injection of free bases. -/
def basisMap (i : ℕ) (b : Fin (M.rank i) × G i) : Fin (N.rank i) × G i :=
  (e.toFun i b.1, b.2)

omit [MulAction H X] [PseudoEMetricSpace X] [∀ i, Fintype (G i)] in
theorem basisMap_injective (i : ℕ) : Function.Injective (e.basisMap i) := by
  rintro ⟨k, g⟩ ⟨k', g'⟩ h
  simp only [basisMap, Prod.mk.injEq] at h
  rw [e.injective i h.1, h.2]

omit [PseudoEMetricSpace X] [∀ i, Fintype (G i)] in
theorem fullLabel_basisMap (i : ℕ) (b : Fin (M.rank i) × G i) :
    N.fullLabel i (e.basisMap i b) = M.fullLabel i b := by
  simp [fullLabel, basisMap, e.label_toFun]

omit [MulAction H X] [PseudoEMetricSpace X] [∀ i, Fintype (G i)] in
theorem mem_range_basisMap (i : ℕ) (c : Fin (N.rank i) × G i) :
    c ∈ Set.range (e.basisMap i) ↔ c.1 ∈ Set.range (e.toFun i) := by
  constructor
  · rintro ⟨b, rfl⟩; exact ⟨b.1, rfl⟩
  · rintro ⟨k, hk⟩; exact ⟨(k, c.2), by simp [basisMap, hk]⟩

/-- The matrix of the summand inclusion. -/
def inclMatrix (i : ℕ) : Matrix (Fin (N.rank i) × G i) (Fin (M.rank i) × G i) ℚ :=
  (1 : Matrix (Fin (N.rank i) × G i) (Fin (N.rank i) × G i) ℚ).submatrix id (e.basisMap i)

omit [MulAction H X] [PseudoEMetricSpace X] [∀ i, Fintype (G i)] in
theorem inclMatrix_apply (i : ℕ) (c : Fin (N.rank i) × G i) (b : Fin (M.rank i) × G i) :
    e.inclMatrix i c b = if c = e.basisMap i b then 1 else 0 := by
  simp [inclMatrix, one_apply]

omit [MulAction H X] [PseudoEMetricSpace X] [∀ i, Fintype (G i)] in
theorem inclMatrix_equivariant (i : ℕ) : IsEquivariant (e.inclMatrix i) := by
  intro g c b
  simp only [inclMatrix_apply, basisMap, Prod.ext_iff, mul_right_inj]

omit [∀ i, Fintype (G i)] in
theorem prop_inclMatrix (i : ℕ) : prop (e.inclMatrix i) (M.fullLabel i) (N.fullLabel i) = 0 := by
  refine le_antisymm (prop_le_iff.mpr fun c b h ↦ ?_) bot_le
  have hc : c = e.basisMap i b := by
    by_contra hne
    exact h (by simp [inclMatrix_apply, hne])
  simp [hc, fullLabel_basisMap]

omit [MulAction H X] [PseudoEMetricSpace X] in
theorem mul_inclMatrix {A : Type*} (i : ℕ) (f : Matrix A (Fin (N.rank i) × G i) ℚ) :
    f * e.inclMatrix i = f.submatrix id (e.basisMap i) := by
  ext a b
  simp [mul_apply, inclMatrix_apply]

omit [MulAction H X] [PseudoEMetricSpace X] in
theorem inclMatrix_transpose_mul {A : Type*} (i : ℕ) (f : Matrix (Fin (N.rank i) × G i) A ℚ) :
    (e.inclMatrix i)ᵀ * f = f.submatrix (e.basisMap i) id := by
  ext b a
  simp [mul_apply, inclMatrix_apply]

/-- The inclusion of the based summand. -/
def incl : M ⟶ N :=
  ⟨e.inclMatrix, ⟨e.inclMatrix_equivariant,
    tendsto_zero_of_forall_eq_zero fun i ↦ e.prop_inclMatrix i⟩⟩

/-- The based projection onto the summand, the transpose of `incl`. -/
def proj : N ⟶ M :=
  ⟨fun i ↦ (e.inclMatrix i)ᵀ, ⟨fun i ↦ (e.inclMatrix_equivariant i).transpose,
    tendsto_zero_of_forall_eq_zero fun i ↦ by simp [propSeq, e.prop_inclMatrix i]⟩⟩

@[simp] theorem incl_val (i : ℕ) : e.incl.1 i = e.inclMatrix i := rfl
@[simp] theorem proj_val (i : ℕ) : e.proj.1 i = (e.inclMatrix i)ᵀ := rfl

@[simp]
theorem incl_proj : e.incl ≫ e.proj = 𝟙 M := by
  refine hom_ext fun i ↦ ?_
  simp only [comp_val, incl_val, proj_val, id_val, inclMatrix_transpose_mul]
  ext b b'
  simp [inclMatrix_apply, one_apply, (e.basisMap_injective i).eq_iff]

theorem proj_incl : e.proj ≫ e.incl = N.diagProj fun i k ↦ k ∈ Set.range (e.toFun i) := by
  refine hom_ext fun i ↦ ?_
  simp only [comp_val, incl_val, proj_val, diagProj_val]
  ext c c'
  simp only [mul_apply, transpose_apply, inclMatrix_apply, diagonal_apply,
    ← e.mem_range_basisMap]
  by_cases hc : c ∈ Set.range (e.basisMap i)
  · obtain ⟨b, rfl⟩ := hc
    rw [Finset.sum_eq_single b]
    · by_cases h : c' = e.basisMap i b
      · simp [h]
      · simp [h, Ne.symm h]
    · intro b' _ hb'
      simp [(e.basisMap_injective i).eq_iff, Ne.symm hb']
    · simp
  · rw [Finset.sum_eq_zero fun b _ ↦ by rw [ite_eq_right fun h ↦ hc ⟨b, h.symm⟩, zero_mul]]
    simp [hc]

theorem incl_comp (f : N ⟶ P) (i : ℕ) : (e.incl ≫ f).1 i = (f.1 i).submatrix id (e.basisMap i) :=
  e.mul_inclMatrix i (f.1 i)

theorem comp_proj (f : P ⟶ N) (i : ℕ) : (f ≫ e.proj).1 i = (f.1 i).submatrix (e.basisMap i) id :=
  e.inclMatrix_transpose_mul i (f.1 i)

/-- Inclusions of summands with disjoint orbit images are orthogonal. -/
theorem incl_proj_eq_zero {M' : AsymptoticObject π X} (e' : OrbitEmbedding M' N)
    (h : ∀ i k k', e.toFun i k ≠ e'.toFun i k') : e.incl ≫ e'.proj = 0 := by
  refine hom_ext fun i ↦ ?_
  ext b b'
  simp only [comp_val, incl_val, proj_val, inclMatrix_transpose_mul, submatrix_apply,
    inclMatrix_apply, zero_val, Matrix.zero_apply, id]
  rw [ite_eq_right]
  simp only [basisMap, Prod.ext_iff, not_and]
  exact fun h' ↦ absurd h'.symm (h i b'.1 b.1)

end OrbitEmbedding

/-- The based summand on the orbits satisfying `P`. -/
def restrict (M : AsymptoticObject π X) (P : ∀ i, Fin (M.rank i) → Prop) :
    AsymptoticObject π X where
  rank i := Fintype.card {k // P i k}
  label i k := M.label i ((Fintype.equivFin {k // P i k}).symm k)

/-- The orbit embedding of a restriction. -/
def restrictEmb (M : AsymptoticObject π X) (P : ∀ i, Fin (M.rank i) → Prop) :
    OrbitEmbedding (M.restrict P) M where
  toFun i k := ((Fintype.equivFin {k // P i k}).symm k).1
  injective _ := Subtype.val_injective.comp (Equiv.injective _)
  label_toFun _ _ := rfl

omit [MulAction H X] [PseudoEMetricSpace X] [∀ i, Fintype (G i)] in
theorem mem_range_restrictEmb (M : AsymptoticObject π X) (P : ∀ i, Fin (M.rank i) → Prop)
    (i : ℕ) (k : Fin (M.rank i)) : k ∈ Set.range ((M.restrictEmb P).toFun i) ↔ P i k := by
  constructor
  · rintro ⟨k', rfl⟩
    exact ((Fintype.equivFin {k // P i k}).symm k').2
  · intro hk
    exact ⟨Fintype.equivFin {k // P i k} ⟨k, hk⟩, by simp [restrictEmb]⟩

theorem restrict_proj_incl (M : AsymptoticObject π X) (P : ∀ i, Fin (M.rank i) → Prop) :
    (M.restrictEmb P).proj ≫ (M.restrictEmb P).incl = M.diagProj P := by
  rw [OrbitEmbedding.proj_incl]
  simp only [mem_range_restrictEmb]

omit [MulAction H X] [PseudoEMetricSpace X] [∀ i, Fintype (G i)] in
theorem restrictEmb_disjoint (M : AsymptoticObject π X) (P : ∀ i, Fin (M.rank i) → Prop)
    (i : ℕ) (k : Fin ((M.restrict P).rank i)) (k' : Fin ((M.restrict fun i k ↦ ¬ P i k).rank i)) :
    (M.restrictEmb P).toFun i k ≠ (M.restrictEmb fun i k ↦ ¬ P i k).toFun i k' := by
  intro h
  have h1 := (M.mem_range_restrictEmb P i _).mp ⟨k, rfl⟩
  have h2 := (M.mem_range_restrictEmb (fun i k ↦ ¬ P i k) i _).mp ⟨k', rfl⟩
  exact h2 (h ▸ h1)

/-- The splitting `M = restrict P ⊕ restrict ¬P` as a bilimit bicone in the prequotient. -/
def restrictBicone (M : AsymptoticObject π X) (P : ∀ i, Fin (M.rank i) → Prop) :
    BinaryBicone (M.restrict P) (M.restrict fun i k ↦ ¬ P i k) where
  pt := M
  fst := (M.restrictEmb P).proj
  snd := (M.restrictEmb _).proj
  inl := (M.restrictEmb P).incl
  inr := (M.restrictEmb _).incl
  inl_fst := OrbitEmbedding.incl_proj _
  inl_snd := OrbitEmbedding.incl_proj_eq_zero _ _ (M.restrictEmb_disjoint P)
  inr_fst := OrbitEmbedding.incl_proj_eq_zero _ _ fun i k k' h ↦
    M.restrictEmb_disjoint P i k' k h.symm
  inr_snd := OrbitEmbedding.incl_proj _

theorem restrictBicone_total (M : AsymptoticObject π X) (P : ∀ i, Fin (M.rank i) → Prop) :
    (M.restrictBicone P).fst ≫ (M.restrictBicone P).inl +
      (M.restrictBicone P).snd ≫ (M.restrictBicone P).inr = 𝟙 M := by
  simp only [restrictBicone, restrict_proj_incl]
  exact diagProj_add_compl M P

/-! ### Zero object and biproducts -/

/-- The object with empty bases. -/
def zeroObj : AsymptoticObject π X := ⟨fun _ ↦ 0, fun _ k ↦ k.elim0⟩

theorem isZero_zeroObj : IsZero (zeroObj : AsymptoticObject π X) :=
  (IsZero.iff_id_eq_zero _).mpr <| hom_ext fun i ↦ by ext b; exact b.1.elim0

instance hasZeroObject : HasZeroObject (AsymptoticObject π X) := ⟨⟨_, isZero_zeroObj⟩⟩

/-- Direct sum: disjoint union of the bases. -/
def biprodObj (M N : AsymptoticObject π X) : AsymptoticObject π X where
  rank i := M.rank i + N.rank i
  label i := Fin.append (M.label i) (N.label i)

def inlEmb (M N : AsymptoticObject π X) : OrbitEmbedding M (biprodObj M N) where
  toFun i := Fin.castAdd (N.rank i)
  injective _ := Fin.castAdd_injective _ _
  label_toFun _ k := Fin.append_left _ _ k

def inrEmb (M N : AsymptoticObject π X) : OrbitEmbedding N (biprodObj M N) where
  toFun i := Fin.natAdd (M.rank i)
  injective _ := Fin.natAdd_injective _ _
  label_toFun _ k := Fin.append_right _ _ k

omit [MulAction H X] [PseudoEMetricSpace X] [∀ i, Fintype (G i)] in
theorem inlEmb_ne_inrEmb (M N : AsymptoticObject π X) (i : ℕ) (k : Fin (M.rank i))
    (k' : Fin (N.rank i)) : (inlEmb M N).toFun i k ≠ (inrEmb M N).toFun i k' := by
  intro h
  have := congrArg Fin.val h
  simp only [inlEmb, inrEmb, Fin.val_castAdd, Fin.val_natAdd] at this
  omega

def biprodBicone (M N : AsymptoticObject π X) : BinaryBicone M N where
  pt := biprodObj M N
  fst := (inlEmb M N).proj
  snd := (inrEmb M N).proj
  inl := (inlEmb M N).incl
  inr := (inrEmb M N).incl
  inl_fst := OrbitEmbedding.incl_proj _
  inl_snd := OrbitEmbedding.incl_proj_eq_zero _ _ (inlEmb_ne_inrEmb M N)
  inr_fst := OrbitEmbedding.incl_proj_eq_zero _ _ fun i k k' h ↦
    inlEmb_ne_inrEmb M N i k' k h.symm
  inr_snd := OrbitEmbedding.incl_proj _

theorem biprodBicone_total (M N : AsymptoticObject π X) :
    (biprodBicone M N).fst ≫ (biprodBicone M N).inl +
      (biprodBicone M N).snd ≫ (biprodBicone M N).inr = 𝟙 (biprodObj M N) := by
  simp only [biprodBicone, OrbitEmbedding.proj_incl]
  refine hom_ext fun i ↦ ?_
  erw [add_val]
  simp only [diagProj_val, diagonal_add, id_val]
  rw [← diagonal_one]
  congr 1
  funext b
  have h1 : ∀ k, k ∈ Set.range ((inlEmb M N).toFun i) → k ∉ Set.range ((inrEmb M N).toFun i) := by
    rintro _ ⟨k, rfl⟩ ⟨k', hk'⟩
    exact inlEmb_ne_inrEmb M N i k k' hk'.symm
  have h2 : b.1 ∈ Set.range ((inlEmb M N).toFun i) ∨ b.1 ∈ Set.range ((inrEmb M N).toFun i) := by
    refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) b.1
    · exact Or.inl ⟨k, rfl⟩
    · exact Or.inr ⟨k, rfl⟩
  rcases h2 with h | h
  · simp [h, h1 _ h]
  · have : b.1 ∉ Set.range ((inlEmb M N).toFun i) := fun h' ↦ h1 _ h' h
    simp [h, this]

instance hasBinaryBiproducts : HasBinaryBiproducts (AsymptoticObject π X) :=
  ⟨fun M N ↦ HasBinaryBiproduct.mk
    ⟨biprodBicone M N, isBinaryBilimitOfTotal _ (biprodBicone_total M N)⟩⟩

instance hasFiniteBiproducts : HasFiniteBiproducts (AsymptoticObject π X) := by
  haveI : HasFiniteProducts (AsymptoticObject π X) := hasFiniteProducts_of_has_binary_and_terminal
  exact HasFiniteBiproducts.of_hasFiniteProducts

end Summands

/-! ### Duality: same labelled basis, transpose matrix -/

section Duality

variable {M N P : AsymptoticObject π X}

def transpose (f : M ⟶ N) : N ⟶ M :=
  ⟨fun i ↦ (f.1 i)ᵀ, ⟨fun i ↦ (equivariant f i).transpose,
    (tendsto_propSeq f).congr fun i ↦ (prop_transpose (u := f.1 i)).symm⟩⟩

@[simp] theorem transpose_val (f : M ⟶ N) (i : ℕ) : (transpose f).1 i = (f.1 i)ᵀ := rfl

@[simp] theorem transpose_transpose (f : M ⟶ N) : transpose (transpose f) = f :=
  hom_ext fun _ ↦ Matrix.transpose_transpose _

@[simp] theorem transpose_id : transpose (𝟙 M) = 𝟙 M := hom_ext fun _ ↦ Matrix.transpose_one

@[simp] theorem transpose_comp (f : M ⟶ N) (g : N ⟶ P) :
    transpose (f ≫ g) = transpose g ≫ transpose f :=
  hom_ext fun _ ↦ Matrix.transpose_mul _ _

@[simp] theorem transpose_add (f g : M ⟶ N) : transpose (f + g) = transpose f + transpose g :=
  hom_ext fun _ ↦ Matrix.transpose_add _ _

@[simp] theorem transpose_smul (c : ℚ) (f : M ⟶ N) : transpose (c • f) = c • transpose f :=
  hom_ext fun _ ↦ by simp

/-- Based summand inclusions and projections are exchanged by duality. -/
@[simp] theorem OrbitEmbedding.transpose_incl (e : OrbitEmbedding M N) :
    transpose e.incl = e.proj := rfl

@[simp] theorem OrbitEmbedding.transpose_proj (e : OrbitEmbedding M N) :
    transpose e.proj = e.incl :=
  hom_ext fun _ ↦ Matrix.transpose_transpose _

@[simp] theorem transpose_diagProj (Q : ∀ i, Fin (M.rank i) → Prop) :
    transpose (M.diagProj Q) = M.diagProj Q :=
  hom_ext fun _ ↦ Matrix.diagonal_transpose _

end Duality

/-! ### Eventual equality -/

/-- Manuscript §2: morphisms are taken modulo eventual exact equality. -/
def eventualEquality : HomRel (AsymptoticObject π X) :=
  fun _ _ f g ↦ ∀ᶠ i in atTop, f.1 i = g.1 i

instance eventualEquality_congruence : Congruence (eventualEquality (π := π) (X := X)) where
  equivalence := ⟨fun _ ↦ Eventually.of_forall fun _ ↦ rfl,
    fun h ↦ h.mono fun _ h ↦ h.symm, fun h h' ↦ (h.and h').mono fun _ h ↦ h.1.trans h.2⟩
  comp_left _ _ _ h := h.mono fun _ h ↦ by simp [h]
  comp_right _ h := h.mono fun _ h ↦ by simp [h]

theorem eventualEquality_add {M N : AsymptoticObject π X} (f₁ f₂ g₁ g₂ : M ⟶ N)
    (hf : eventualEquality f₁ f₂) (hg : eventualEquality g₁ g₂) :
    eventualEquality (f₁ + g₁) (f₂ + g₂) :=
  (hf.and hg).mono fun _ h ↦ by simp [h.1, h.2]

theorem eventualEquality_smul (c : ℚ) {M N : AsymptoticObject π X} (f g : M ⟶ N)
    (h : eventualEquality f g) : eventualEquality (c • f) (c • g) :=
  h.mono fun _ h ↦ by simp [h]

theorem eventualEquality_transpose {M N : AsymptoticObject π X} {f g : M ⟶ N}
    (h : eventualEquality f g) : eventualEquality (transpose f) (transpose g) :=
  h.mono fun _ h ↦ by simp [h]

end AsymptoticObject

open AsymptoticObject

variable {π : ∀ i, G i →* H} {X : Type u} [MulAction H X] [PseudoEMetricSpace X]
  [∀ i, Fintype (G i)]

variable (π X) in
/-- The asymptotic category `𝒜_G(X)` of manuscript §2. -/
abbrev AsymptoticCategory :=
  CategoryTheory.Quotient (eventualEquality (π := π) (X := X))

namespace AsymptoticCategory

instance preadditive : Preadditive (AsymptoticCategory π X) :=
  Quotient.preadditive _ fun _ _ ↦ eventualEquality_add

/-- The quotient functor from honest controlled families. -/
abbrev functor : AsymptoticObject π X ⥤ AsymptoticCategory π X :=
  Quotient.functor _

instance functor_additive : (functor (π := π) (X := X)).Additive :=
  Quotient.functor_additive _ fun _ _ ↦ eventualEquality_add

instance linear : Linear ℚ (AsymptoticCategory π X) :=
  Quotient.linear ℚ _ fun c _ _ ↦ eventualEquality_smul c

instance functor_linear : (functor (π := π) (X := X)).Linear ℚ :=
  Quotient.linear_functor ℚ _ fun c _ _ ↦ eventualEquality_smul c

/-- Equality in `𝒜_G(X)` is eventual exact equality of matrices. -/
theorem functor_map_eq_iff {M N : AsymptoticObject π X} (f g : M ⟶ N) :
    functor.map f = functor.map g ↔ ∀ᶠ i in atTop, f.1 i = g.1 i :=
  Quotient.functor_map_eq_iff _ f g

theorem functor_map_eq_zero_iff {M N : AsymptoticObject π X} (f : M ⟶ N) :
    functor.map f = 0 ↔ ∀ᶠ i in atTop, f.1 i = 0 := by
  rw [← functor.map_zero M N, functor_map_eq_iff]
  rfl

theorem exists_rep {A B : AsymptoticCategory π X} (φ : A ⟶ B) :
    ∃ f : A.as ⟶ B.as, functor.map f = φ :=
  functor.map_surjective φ

instance hasZeroObject : HasZeroObject (AsymptoticCategory π X) :=
  ⟨⟨_, functor.map_isZero isZero_zeroObj⟩⟩

/-- The direct sum of `𝒜_G(X)`: disjoint union of bases. -/
def biprodBicone (A B : AsymptoticCategory π X) : BinaryBicone A B :=
  functor.mapBinaryBicone (AsymptoticObject.biprodBicone A.as B.as)

theorem biprodBicone_total (A B : AsymptoticCategory π X) :
    (biprodBicone A B).fst ≫ (biprodBicone A B).inl +
      (biprodBicone A B).snd ≫ (biprodBicone A B).inr = 𝟙 _ := by
  have := congrArg functor.map (AsymptoticObject.biprodBicone_total A.as B.as)
  simp only [Functor.map_add, Functor.map_comp] at this
  exact this

instance hasBinaryBiproducts : HasBinaryBiproducts (AsymptoticCategory π X) :=
  ⟨fun A B ↦ HasBinaryBiproduct.mk ⟨biprodBicone A B, isBinaryBilimitOfTotal _
    (biprodBicone_total A B)⟩⟩

instance hasFiniteBiproducts : HasFiniteBiproducts (AsymptoticCategory π X) := by
  haveI : HasFiniteProducts (AsymptoticCategory π X) :=
    hasFiniteProducts_of_has_binary_and_terminal
  exact HasFiniteBiproducts.of_hasFiniteProducts

/-- Duality on `𝒜_G(X)`: transpose of any representative. -/
def transpose {A B : AsymptoticCategory π X} (φ : A ⟶ B) : B ⟶ A :=
  Quot.liftOn φ (fun f ↦ functor.map (AsymptoticObject.transpose f)) fun f g h ↦ by
    rw [HomRel.compClosure_eq_self] at h
    exact (functor_map_eq_iff _ _).mpr (eventualEquality_transpose h)

@[simp]
theorem transpose_map {M N : AsymptoticObject π X} (f : M ⟶ N) :
    transpose (functor.map f) = functor.map (AsymptoticObject.transpose f) := rfl

@[simp]
theorem transpose_transpose {A B : AsymptoticCategory π X} (φ : A ⟶ B) :
    transpose (transpose φ) = φ := by
  obtain ⟨f, rfl⟩ := exists_rep φ
  simp

@[simp]
theorem transpose_id (A : AsymptoticCategory π X) : transpose (𝟙 A) = 𝟙 A := by
  change transpose (functor.map (𝟙 A.as)) = functor.map (𝟙 A.as)
  rw [transpose_map, AsymptoticObject.transpose_id]

@[simp]
theorem transpose_comp {A B C : AsymptoticCategory π X} (φ : A ⟶ B) (ψ : B ⟶ C) :
    transpose (φ ≫ ψ) = transpose ψ ≫ transpose φ := by
  obtain ⟨f, rfl⟩ := exists_rep φ
  obtain ⟨g, rfl⟩ := exists_rep ψ
  rw [← Functor.map_comp, transpose_map, transpose_map, transpose_map,
    AsymptoticObject.transpose_comp, Functor.map_comp]

@[simp]
theorem transpose_add {A B : AsymptoticCategory π X} (φ ψ : A ⟶ B) :
    transpose (φ + ψ) = transpose φ + transpose ψ := by
  obtain ⟨f, rfl⟩ := exists_rep φ
  obtain ⟨g, rfl⟩ := exists_rep ψ
  rw [← Functor.map_add, transpose_map, transpose_map, transpose_map,
    AsymptoticObject.transpose_add, Functor.map_add]

/-- The strict duality functor, the identity on objects. -/
def duality : (AsymptoticCategory π X)ᵒᵖ ⥤ AsymptoticCategory π X where
  obj A := A.unop
  map φ := transpose φ.unop

instance duality_additive : (duality (π := π) (X := X)).Additive where
  map_add := transpose_add _ _

/-- The additive idempotent completion `Kar(𝒜_G(X))`. -/
abbrev Kar (π : ∀ i, G i →* H) (X : Type u) [MulAction H X] [PseudoEMetricSpace X] :=
  Idempotents.Karoubi (AsymptoticCategory π X)

example : HasFiniteBiproducts (Kar π X) := inferInstance
example : IsIdempotentComplete (Kar π X) := inferInstance

end AsymptoticCategory

end HSFormal
