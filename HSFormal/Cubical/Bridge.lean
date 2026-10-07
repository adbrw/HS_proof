import HSFormal.Cubical.Carrier
import HSFormal.GraphType
import Mathlib.Algebra.Homology.Homotopy

/-!
# Bridges from based complexes to `𝒜_G(X)` (module C1)

Propagation bounds for the Koszul tensor, and the passage from sequences of based complexes
with control labels to chain complexes over the prequotient asymptotic category
`AsymptoticObject π X` (the setting of `HSFormal.Compression` and the L-theory modules).
A `ControlledSeq` is a sequence `C i` of based complexes with labels `label i : (C i).X → X`
whose boundary propagation tends to zero.  Its degree-`r` object has one free `G i`-orbit per
`r`-cell, labelled through `Fintype.equivFin`; matrix sequences become free-sheet families
(`sheetFamily 1`).  Exact identities of matrices become identities of morphisms, so controlled
chain maps, homotopies and homotopy equivalences go to their mathlib counterparts.
-/

noncomputable section

namespace HSFormal.Cubical

open Filter Matrix CategoryTheory
open scoped ENNReal Topology Kronecker

namespace BasedComplex

/-! ### Propagation of Koszul tensors -/

section Propagation

variable {E F : Type*} [PseudoEMetricSpace E] [PseudoEMetricSpace F]

theorem prop_kronecker_le {l m n p : Type*} (A : Matrix l m ℚ) (B : Matrix n p ℚ) (a : m → E)
    (a' : l → E) (b : p → F) (b' : n → F) :
    prop (A ⊗ₖ B) (fun q ↦ (a q.1, b q.2)) (fun q ↦ (a' q.1, b' q.2)) ≤
      max (prop A a a') (prop B b b') := by
  refine prop_le_iff.mpr fun x y h ↦ ?_
  rw [kronecker_apply] at h
  rw [Prod.edist_eq]
  exact max_le_max (edist_le_prop (left_ne_zero_of_mul h)) (edist_le_prop (right_ne_zero_of_mul h))

/-- Entries carried by `car` propagate at most `r` if every carrier is `r`-close to its cell. -/
theorem prop_le_of_carrier {A B : Type*} {u : Matrix B A ℚ} {a : A → E} {b : B → E}
    {car : A → B → Prop} {r : ℝ≥0∞} (hu : ∀ ρ σ, u ρ σ ≠ 0 → car σ ρ)
    (hr : ∀ σ ρ, car σ ρ → edist (b ρ) (a σ) ≤ r) : prop u a b ≤ r :=
  prop_le_iff.mpr fun ρ σ h ↦ hr σ ρ (hu ρ σ h)

theorem prop_tensor_d_le {C D : BasedComplex} (a : C.X → E) (b : D.X → F) :
    prop (C.tensor D).d (fun q ↦ (a q.1, b q.2)) (fun q ↦ (a q.1, b q.2)) ≤
      max (prop C.d a a) (prop D.d b b) := by
  refine (prop_add_le).trans (max_le ?_ ?_)
  · refine (prop_kronecker_le _ _ _ _ _ _).trans ?_
    rw [prop_one]; simp
  · refine (prop_kronecker_le _ _ _ _ _ _).trans ?_
    rw [sgn, prop_diagonal]; simp

/-- Tensor products of maps: propagation is the larger of the two factors'. -/
theorem prop_hom_tensor_le {C C' D D' : BasedComplex} (u : Matrix C'.X C.X ℚ)
    (v : Matrix D'.X D.X ℚ) (a : C.X → E) (a' : C'.X → E) (b : D.X → F) (b' : D'.X → F) :
    prop (u ⊗ₖ v) (fun q ↦ (a q.1, b q.2)) (fun q ↦ (a' q.1, b' q.2)) ≤
      max (prop u a a') (prop v b b') :=
  prop_kronecker_le u v a a' b b'

end Propagation

/-! ### Sequences of based complexes in `𝒜_G(X)` -/

universe u

/-- The cells of degree `r`. -/
abbrev Cells (C : BasedComplex) (r : ℤ) : Type := {σ : C.X // (C.deg σ : ℤ) = r}

/-- The enumeration of the `r`-cells. -/
def cellEquiv (C : BasedComplex) (r : ℤ) : Cells C r ≃ Fin (Fintype.card (Cells C r)) :=
  Fintype.equivFin _

theorem sum_cells (C : BasedComplex) (r : ℤ) (f : C.X → ℚ)
    (hf : ∀ κ, f κ ≠ 0 → (C.deg κ : ℤ) = r) : ∑ k, f ((cellEquiv C r).symm k).1 = ∑ κ, f κ := by
  rw [Equiv.sum_comp (cellEquiv C r).symm (fun κ ↦ f κ.1),
    ← Fintype.sum_subtype_add_sum_subtype (fun κ ↦ (C.deg κ : ℤ) = r) f]
  have h₀ : ∑ κ : {κ // ¬(C.deg κ : ℤ) = r}, f κ = 0 :=
    Finset.sum_eq_zero fun κ _ ↦ by_contra fun h ↦ κ.2 (hf _ h)
  rw [h₀, add_zero]

/-- Matrix sequences whose propagation tends to zero. -/
def PropTendsto {X : Type u} [PseudoEMetricSpace X] {C D : ℕ → BasedComplex}
    (u : ∀ i, Matrix (D i).X (C i).X ℚ) (a : ∀ i, (C i).X → X) (b : ∀ i, (D i).X → X) :
    Prop :=
  Tendsto (fun i ↦ prop (u i) (a i) (b i)) atTop (𝓝 0)

namespace PropTendsto

variable {X : Type u} [PseudoEMetricSpace X] {C D D' : ℕ → BasedComplex}
  {a : ∀ i, (C i).X → X} {b : ∀ i, (D i).X → X} {b' : ∀ i, (D' i).X → X}
  {u v : ∀ i, Matrix (D i).X (C i).X ℚ}

theorem add (hu : PropTendsto u a b) (hv : PropTendsto v a b) :
    PropTendsto (fun i ↦ u i + v i) a b :=
  tendsto_zero_of_le (by simpa using hu.max hv) fun _ ↦ prop_add_le

theorem smul (c : ℚ) (hu : PropTendsto u a b) : PropTendsto (fun i ↦ c • u i) a b :=
  tendsto_zero_of_le hu fun _ ↦ prop_smul_le c

theorem neg (hu : PropTendsto u a b) : PropTendsto (fun i ↦ -u i) a b := by
  simpa [PropTendsto] using hu

theorem sub (hu : PropTendsto u a b) (hv : PropTendsto v a b) :
    PropTendsto (fun i ↦ u i - v i) a b := by
  simpa [sub_eq_add_neg] using hu.add hv.neg

theorem mul {w : ∀ i, Matrix (D' i).X (D i).X ℚ} (hw : PropTendsto w b b')
    (hu : PropTendsto u a b) : PropTendsto (fun i ↦ w i * u i) a b' :=
  tendsto_zero_of_le (by simpa using Filter.Tendsto.add hu hw) fun _ ↦ prop_mul_le _ _ _ _

theorem one : PropTendsto (fun i ↦ (1 : Matrix (C i).X (C i).X ℚ)) a a :=
  tendsto_zero_of_forall_eq_zero fun _ ↦ prop_one _

theorem zero : PropTendsto (fun i ↦ (0 : Matrix (D i).X (C i).X ℚ)) a b :=
  tendsto_zero_of_forall_eq_zero fun _ ↦ prop_zero

end PropTendsto

/-- A sequence of based complexes with control labels and shrinking boundary propagation. -/
structure ControlledSeq (X : Type u) [PseudoEMetricSpace X] where
  C : ℕ → BasedComplex
  label : ∀ i, (C i).X → X
  tendsto_d : PropTendsto (fun i ↦ (C i).d) label label

namespace ControlledSeq

variable {X : Type u} [PseudoEMetricSpace X] (A B B' : ControlledSeq X)

/-- Controlled chain maps. -/
structure Hom where
  f : ∀ i, BasedComplex.Hom (A.C i) (B.C i)
  tendsto : PropTendsto (fun i ↦ (f i).f) A.label B.label

/-- Controlled exact homotopies. -/
structure Htpy {A B : ControlledSeq X} (F G : Hom A B) where
  h : ∀ i, BasedComplex.Htpy (F.f i) (G.f i)
  tendsto : PropTendsto (fun i ↦ (h i).h) A.label B.label

variable {A B B'}

/-- The identity. -/
def Hom.id (A : ControlledSeq X) : Hom A A := ⟨fun _ ↦ BasedComplex.Hom.id _, PropTendsto.one⟩

/-- Composition. -/
def Hom.comp (G : Hom B B') (F : Hom A B) : Hom A B' :=
  ⟨fun i ↦ (G.f i).comp (F.f i), G.tendsto.mul F.tendsto⟩

/-- Controlled homotopy equivalences. -/
structure HtpyEquiv (A B : ControlledSeq X) where
  hom : Hom A B
  inv : Hom B A
  homInv : Htpy (inv.comp hom) (Hom.id A)
  invHom : Htpy (hom.comp inv) (Hom.id B)

section Asymptotic

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] (π : ∀ i, G i →* H)
  [MulAction H X] [IsIsometricSMul H X] [∀ i, Fintype (G i)]

/-- The degree-`r` object: one free orbit per `r`-cell, labelled by the cell's label. -/
@[reducible]
def obj (A : ControlledSeq X) (r : ℤ) : AsymptoticObject π X where
  rank i := Fintype.card (Cells (A.C i) r)
  label i k := A.label i ((cellEquiv (A.C i) r).symm k).1

/-- The block of a matrix sequence from degree `r` to degree `r'`, on one sheet. -/
def block (u : ∀ i, Matrix (B.C i).X (A.C i).X ℚ) (r r' : ℤ) :
    AsymptoticObject.ScalarFamily (A.obj π r) (B.obj π r') :=
  fun i ↦ (u i).submatrix (fun k ↦ ((cellEquiv (B.C i) r').symm k).1)
    (fun k ↦ ((cellEquiv (A.C i) r).symm k).1)

/-- A controlled matrix sequence as a morphism of `𝒜_G(X)` (free sheets, graph type `1`). -/
def hom (u : ∀ i, Matrix (B.C i).X (A.C i).X ℚ) (hu : PropTendsto u A.label B.label)
    (r r' : ℤ) : A.obj π r ⟶ B.obj π r' :=
  ⟨AsymptoticObject.sheetFamily 1 (block π u r r'),
    AsymptoticObject.isControlled_sheetFamily_iff.mpr <| tendsto_zero_of_le hu fun i ↦ by
      simp only [Pi.one_apply, map_one, graphProp_one]; exact prop_submatrix_le _ _⟩

variable {π}

theorem hom_val (u : ∀ i, Matrix (B.C i).X (A.C i).X ℚ) (hu) (r r' : ℤ) (i : ℕ) :
    (hom π u hu r r').1 i = sheet 1 (block π u r r' i) := rfl

theorem hom_congr {u v : ∀ i, Matrix (B.C i).X (A.C i).X ℚ} (huv : u = v) (hu hv) (r r' : ℤ) :
    hom π u hu r r' = hom π v hv r r' := by subst huv; rfl

theorem hom_add (u v : ∀ i, Matrix (B.C i).X (A.C i).X ℚ) (hu hv) (r r' : ℤ) :
    hom π (fun i ↦ u i + v i) (hu.add hv) r r' = hom π u hu r r' + hom π v hv r r' :=
  AsymptoticObject.hom_ext fun i ↦ by
    simp only [hom_val, AsymptoticObject.add_val, ← sheet_add]; rfl

theorem hom_eq_zero (u : ∀ i, Matrix (B.C i).X (A.C i).X ℚ) (hu) {r r' : ℤ}
    (h : ∀ i κ σ, (A.C i).deg σ = r → (B.C i).deg κ = r' → u i κ σ = 0) :
    hom π u hu r r' = 0 :=
  AsymptoticObject.hom_ext fun i ↦ by
    rw [hom_val, AsymptoticObject.zero_val, ← sheet_zero (1 : G i)]
    congr 1
    ext k' k
    exact h i _ _ ((cellEquiv (A.C i) r).symm k).2 ((cellEquiv (B.C i) r').symm k').2

theorem hom_comp (u : ∀ i, Matrix (B.C i).X (A.C i).X ℚ) (v : ∀ i, Matrix (B'.C i).X (B.C i).X ℚ)
    (hu hv) {r r' r'' : ℤ}
    (h : ∀ i κ σ, u i κ σ ≠ 0 → (A.C i).deg σ = r → (B.C i).deg κ = r') :
    hom π u hu r r' ≫ hom π v hv r' r'' = hom π (fun i ↦ v i * u i) (hv.mul hu) r r'' :=
  AsymptoticObject.hom_ext fun i ↦ by
    simp only [AsymptoticObject.comp_val, hom_val, sheet_mul, mul_one]
    congr 1
    ext k'' k
    simp only [block, submatrix_apply, mul_apply]
    exact sum_cells _ _ (fun κ ↦ v i _ κ * u i κ _) fun κ hκ ↦
      h i κ _ (right_ne_zero_of_mul hκ) ((cellEquiv (A.C i) r).symm k).2

theorem hom_one {r : ℤ} : hom π (fun i ↦ (1 : Matrix (A.C i).X (A.C i).X ℚ)) PropTendsto.one r r =
    𝟙 (A.obj π r) :=
  AsymptoticObject.hom_ext fun i ↦ by
    ext ⟨k', g'⟩ ⟨k, g⟩
    simp only [hom_val, sheet_apply, block, submatrix_apply, AsymptoticObject.id_val, mul_one,
      one_apply, Subtype.val_inj, Equiv.apply_eq_iff_eq, Prod.mk.injEq]
    split_ifs <;> simp_all

variable (π) in
/-- The chain complex over `𝒜_G(X)` of a controlled sequence. -/
@[reducible]
def toComplex (A : ControlledSeq X) : ChainComplex (AsymptoticObject π X) ℤ where
  X r := A.obj π r
  d r r' := hom π (fun i ↦ (A.C i).d) A.tendsto_d r r'
  shape r r' h := hom_eq_zero _ _ fun i κ σ hσ hκ ↦ by_contra fun hne ↦ h (by
    have := (A.C i).d_deg κ σ hne; change r' + 1 = r; omega)
  d_comp_d' r r' r'' (h : r' + 1 = r) _ := by
    rw [hom_comp _ _ _ _ fun i κ σ hne hσ ↦ by have := (A.C i).d_deg κ σ hne; omega]
    exact hom_eq_zero _ _ fun i κ σ _ _ ↦ by rw [(A.C i).d_d]; rfl

variable (π) in
/-- A controlled chain map as a chain map over `𝒜_G(X)`. -/
def Hom.toComplex (F : Hom A B) : A.toComplex π ⟶ B.toComplex π where
  f r := hom π (fun i ↦ (F.f i).f) F.tendsto r r
  comm' r r' (h : r' + 1 = r) := by
    change hom π _ F.tendsto r r ≫ hom π (fun i ↦ (B.C i).d) B.tendsto_d r r' =
      hom π (fun i ↦ (A.C i).d) A.tendsto_d r r' ≫ hom π _ F.tendsto r' r'
    rw [hom_comp _ _ _ _ fun i κ σ hne hσ ↦ by have := (F.f i).deg0 κ σ hne; omega,
      hom_comp _ _ _ _ fun i κ σ hne hσ ↦ by have := (A.C i).d_deg κ σ hne; omega]
    exact hom_congr (funext fun i ↦ (F.f i).comm) _ _ _ _

theorem Hom.toComplex_f (F : Hom A B) (r : ℤ) :
    (F.toComplex π).f r = hom π (fun i ↦ (F.f i).f) F.tendsto r r := rfl

theorem Hom.toComplex_id (A : ControlledSeq X) : (Hom.id A).toComplex π = 𝟙 (A.toComplex π) := by
  ext r; exact hom_one

theorem Hom.toComplex_comp (G : Hom B B') (F : Hom A B) :
    (G.comp F).toComplex π = F.toComplex π ≫ G.toComplex π := by
  ext r
  exact (hom_comp _ _ F.tendsto G.tendsto fun i κ σ hne hσ ↦ by
    have := (F.f i).deg0 κ σ hne; omega).symm

variable (π) in
/-- A controlled exact homotopy as a mathlib `Homotopy` over `𝒜_G(X)`. -/
def Htpy.toHomotopy {F G : Hom A B} (H : Htpy F G) : Homotopy (F.toComplex π) (G.toComplex π) where
  hom r r' := hom π (fun i ↦ (H.h i).h) H.tendsto r r'
  zero r r' h := hom_eq_zero _ _ fun i κ σ hσ hκ ↦ by_contra fun hne ↦ h (by
    have := (H.h i).deg1 κ σ hne; change r + 1 = r'; omega)
  comm r := by
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel r (r - 1) by simp),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (r + 1) r by simp)]
    change hom π _ F.tendsto r r =
      hom π (fun i ↦ (A.C i).d) A.tendsto_d r (r - 1) ≫ hom π _ H.tendsto (r - 1) r +
        hom π _ H.tendsto r (r + 1) ≫ hom π (fun i ↦ (B.C i).d) B.tendsto_d (r + 1) r +
          hom π _ G.tendsto r r
    rw [hom_comp _ _ _ _ fun i κ σ hne hσ ↦ by have := (A.C i).d_deg κ σ hne; omega,
      hom_comp _ _ _ _ fun i κ σ hne hσ ↦ by have := (H.h i).deg1 κ σ hne; omega,
      ← hom_add, ← hom_add]
    refine hom_congr (funext fun i ↦ ?_) _ _ _ _
    have := (H.h i).eq
    rw [sub_eq_iff_eq_add] at this
    rw [this]; abel

variable (π) in
/-- A controlled homotopy equivalence as a mathlib `HomotopyEquiv` over `𝒜_G(X)`. -/
def HtpyEquiv.toHomotopyEquiv (e : HtpyEquiv A B) :
    HomotopyEquiv (A.toComplex π) (B.toComplex π) where
  hom := e.hom.toComplex π
  inv := e.inv.toComplex π
  homotopyHomInvId := (Homotopy.ofEq (Hom.toComplex_comp _ _).symm).trans
    ((e.homInv.toHomotopy π).trans (Homotopy.ofEq (Hom.toComplex_id A)))
  homotopyInvHomId := (Homotopy.ofEq (Hom.toComplex_comp _ _).symm).trans
    ((e.invHom.toHomotopy π).trans (Homotopy.ofEq (Hom.toComplex_id B)))

end Asymptotic

end ControlledSeq

end BasedComplex

end HSFormal.Cubical
