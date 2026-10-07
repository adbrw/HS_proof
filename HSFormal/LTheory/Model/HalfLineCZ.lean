import HSFormal.LTheory.Model.HalfLinePair
import HSFormal.LTheory.Model.CutWindow

/-!
# The two half-lines of `C_ℤ(A)` (half-line splitting, part 4)

Write `Δ = (CZ.lineData A).Δ` (the constant functor) and `s` for the shift.  The constant object
`ΔX` restricted to the positions `p` is the `E`-part of the self-dual diagonal cut
`CZ.cut (ΔX) p`; `CZ.halfF A p : A ⟶ A.cz` is the resulting duality-preserving functor.
Natural transformations between them are compressions `ι_E M π_E` of natural constant matrices
`M` (`CZ.cutNat`: the identity or the shift).

* `CZ.negLine A`: the half-line data of `(-∞, 0]`: edges `[v, v+1]` at `v ≤ -1`, vertices at
  `v ≤ 0`, `u` the shift (unitary: `(-∞, -1] ≅ (-∞, 0]`), `w` the inclusion, `β` the vertex `0`.
* `CZ.posLine A`: the half-line data of `[0, ∞)`: edges `[v, v+1]` and vertices at `v ≥ 0`,
  `u = 1`, `w` the shift (an isometry missing the vertex `0`), `β` the vertex `0`.

All identities reduce (`cut_ext`) to identities of diagonal and shift matrices on constant
objects, checked entrywise.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression

noncomputable section

attribute [local implicit_reducible] CZ.lineData

namespace CZ

variable (A : InvCat)

/-- The constant functor `Δ = (lineData A).Δ`. -/
abbrev Δc : A ⟶ A.cz := (lineData A).Δ

/-! ### Matrices on constant objects -/

section Mat

variable {A}

/-- The shift `s` of the constant object. -/
abbrev sh (X : A) : (Δc A).F.obj X ⟶ (Δc A).F.obj X := (lineData A).s.iso.hom.app X

/-- The inverse shift `s⁻¹`. -/
abbrev shi (X : A) : (Δc A).F.obj X ⟶ (Δc A).F.obj X := (lineData A).s.iso.inv.app X

/-- The cut idempotent `χ_p` of a constant object. -/
abbrev χ (X : A) (p : ℤ → Prop) [DecidablePred p] : (Δc A).F.obj X ⟶ (Δc A).F.obj X :=
  (cut ((Δc A).F.obj X) p).idem

lemma χ_eq (X : A) (p : ℤ → Prop) [DecidablePred p] :
    χ X p = diag (X := constObj A X) (Y := constObj A X) fun v ↦ if p v then 𝟙 X else 0 :=
  cut_idem _ p

lemma diag_shift_diag_apply (X : A) (d e : ℤ → (X ⟶ X)) (k w v : ℤ) :
    (diag (X := constObj A X) (Y := constObj A X) d ≫ constShift k X ≫
      diag (X := constObj A X) (Y := constObj A X) e).1 w v =
        if w = v + k then d v ≫ e w else 0 := by
  rw [diag_comp_apply, comp_diag_apply, shift_apply]
  split_ifs <;> simp

lemma diag_shift_apply (X : A) (d : ℤ → (X ⟶ X)) (k w v : ℤ) :
    (diag (X := constObj A X) (Y := constObj A X) d ≫ constShift k X).1 w v =
        if w = v + k then d v else 0 := by
  rw [diag_comp_apply, shift_apply]
  split_ifs <;> simp

/-- `χ_p s_k χ_q = χ_p s_k` if the shift by `k` maps `p` into `q`. -/
lemma idem_constShift_idem (X : A) (p q : ℤ → Prop) [DecidablePred p] [DecidablePred q]
    (k : ℤ) (h : ∀ v, p v → q (v + k)) :
    χ X p ≫ constShift k X ≫ χ X q = χ X p ≫ constShift k X := by
  ext w v
  rw [χ_eq, χ_eq, diag_shift_diag_apply, diag_shift_apply]
  split_ifs with h₁ h₂ h₃ <;> first | rfl | (subst h₁; exact absurd (h v h₂) h₃) | simp

/-- `χ_p s_k χ_q = 0` if the shift by `k` maps `p` off `q`. -/
lemma idem_constShift_idem_eq_zero (X : A) (p q : ℤ → Prop) [DecidablePred p] [DecidablePred q]
    (k : ℤ) (h : ∀ v, p v → ¬ q (v + k)) :
    χ X p ≫ constShift k X ≫ χ X q = 0 := by
  ext w v
  rw [χ_eq, χ_eq, diag_shift_diag_apply]
  split_ifs with h₁ h₂ h₃ <;> first | rfl | (subst h₁; exact absurd h₃ (h v h₂)) | simp

@[reassoc]
lemma idem_sh_idem (X : A) (p q : ℤ → Prop) [DecidablePred p] [DecidablePred q]
    (h : ∀ v, p v → q (v + 1)) : χ X p ≫ sh X ≫ χ X q = χ X p ≫ sh X :=
  idem_constShift_idem X p q 1 h

@[reassoc]
lemma idem_shi_idem (X : A) (p q : ℤ → Prop) [DecidablePred p] [DecidablePred q]
    (h : ∀ v, p v → q (v + -1)) : χ X p ≫ shi X ≫ χ X q = χ X p ≫ shi X :=
  idem_constShift_idem X p q (-1) h

@[reassoc]
lemma idem_sh_idem_eq_zero (X : A) (p q : ℤ → Prop) [DecidablePred p] [DecidablePred q]
    (h : ∀ v, p v → ¬ q (v + 1)) : χ X p ≫ sh X ≫ χ X q = 0 :=
  idem_constShift_idem_eq_zero X p q 1 h

lemma idem_shi_idem_eq_zero (X : A) (p q : ℤ → Prop) [DecidablePred p] [DecidablePred q]
    (h : ∀ v, p v → ¬ q (v + -1)) : χ X p ≫ shi X ≫ χ X q = 0 :=
  idem_constShift_idem_eq_zero X p q (-1) h

lemma shift_diag_apply (X : A) (e : ℤ → (X ⟶ X)) (k w v : ℤ) :
    (constShift k X ≫ diag (X := constObj A X) (Y := constObj A X) e).1 w v =
        if w = v + k then e w else 0 := by
  rw [comp_diag_apply, shift_apply]
  split_ifs <;> simp

/-- The shift moves cut idempotents. -/
lemma constShift_idem (X : A) (q : ℤ → Prop) [DecidablePred q] (k : ℤ) :
    (constShift k X : (Δc A).F.obj X ⟶ (Δc A).F.obj X) ≫ χ X q =
      χ X (fun v ↦ q (v + k)) ≫ constShift k X := by
  ext w v
  rw [χ_eq, χ_eq, diag_shift_apply, shift_diag_apply]
  split_ifs with h₁ h₂ h₃ h₃ <;>
    first
    | rfl
    | (subst h₁; exact absurd h₃ h₂)
    | (subst h₁; exact absurd h₂ h₃)

@[reassoc]
lemma shi_idem (X : A) (q : ℤ → Prop) [DecidablePred q] :
    shi X ≫ χ X q = χ X (fun v ↦ q (v + -1)) ≫ shi X :=
  constShift_idem X q (-1)

lemma idem_eq_zero (X : A) (p : ℤ → Prop) [DecidablePred p] (h : ∀ v, ¬ p v) : χ X p = 0 := by
  rw [χ_eq]
  exact (diag_ext fun v ↦ by simp [h v]).trans diag_zero

/-- Products of cut idempotents. -/
@[reassoc]
lemma idem_idem (X : A) (p q : ℤ → Prop) [DecidablePred p] [DecidablePred q]
    (r : ℤ → Prop) [DecidablePred r] (h : ∀ v, (p v ∧ q v) ↔ r v) :
    χ X p ≫ χ X q = χ X r := by
  rw [χ_eq, χ_eq, χ_eq, diag_comp_diag]
  refine diag_ext fun v ↦ ?_
  by_cases hp : p v <;> by_cases hq : q v <;> simp [hp, hq, ← h v]

/-- Sums of cut idempotents. -/
lemma idem_add_idem (X : A) (p q : ℤ → Prop) [DecidablePred p] [DecidablePred q]
    (r : ℤ → Prop) [DecidablePred r] (h : ∀ v, (p v ∨ q v) ↔ r v) (h' : ∀ v, ¬ (p v ∧ q v)) :
    χ X p + χ X q = χ X r := by
  rw [χ_eq, χ_eq, χ_eq, ← diag_add]
  refine diag_ext fun v ↦ ?_
  by_cases hp : p v <;> by_cases hq : q v
  · exact absurd ⟨hp, hq⟩ (h' v)
  all_goals simp [hp, hq, ← h v]

lemma idem_eq_id (X : A) (p : ℤ → Prop) [DecidablePred p] (h : ∀ v, p v) : χ X p = 𝟙 _ := by
  rw [χ_eq]
  exact (diag_ext fun v ↦ by simp [h v]).trans (diag_id _)

/-- Constant maps commute with cut idempotents. -/
@[reassoc]
lemma idem_Δmap {X Y : A} (f : X ⟶ Y) (p : ℤ → Prop) [DecidablePred p] :
    χ X p ≫ (Δc A).F.map f = (Δc A).F.map f ≫ χ Y p := by
  rw [χ_eq, χ_eq]
  change diag _ ≫ diag _ = diag _ ≫ diag _
  rw [diag_comp_diag, diag_comp_diag]
  exact diag_ext fun v ↦ by
    split_ifs
    · erw [comp_id, id_comp]
    · rw [comp_zero, zero_comp]

@[reassoc]
lemma ιE_idem {X : A.cz} (p : ℤ → Prop) [DecidablePred p] :
    (cut X p).ιE ≫ (cut X p).idem = (cut X p).ιE := by
  rw [Splitting.idem, ← assoc, (cut X p).ιE_πE, id_comp]

@[reassoc]
lemma idem_πE {X : A.cz} (p : ℤ → Prop) [DecidablePred p] :
    (cut X p).idem ≫ (cut X p).πE = (cut X p).πE := by
  rw [Splitting.idem, assoc, (cut X p).ιE_πE, comp_id]

@[reassoc]
lemma πE_ιE {X : A.cz} (p : ℤ → Prop) [DecidablePred p] :
    (cut X p).πE ≫ (cut X p).ιE = (cut X p).idem := by rw [Splitting.idem]

@[reassoc]
lemma idem_idem_self {X : A.cz} (p : ℤ → Prop) [DecidablePred p] :
    (cut X p).idem ≫ (cut X p).idem = (cut X p).idem := by
  rw [Splitting.idem, assoc, reassoc_of% (cut X p).ιE_πE]

/-- Maps between cut objects are determined by their extensions `π_E F ι_E`. -/
lemma cut_ext {X Y : A.cz} (p q : ℤ → Prop) [DecidablePred p] [DecidablePred q]
    {F G : (cut X p).E ⟶ (cut Y q).E}
    (h : (cut X p).πE ≫ F ≫ (cut Y q).ιE = (cut X p).πE ≫ G ≫ (cut Y q).ιE) : F = G := by
  have e (K : (cut X p).E ⟶ (cut Y q).E) :
      K = (cut X p).ιE ≫ ((cut X p).πE ≫ K ≫ (cut Y q).ιE) ≫ (cut Y q).πE := by
    have h₁ := (cut X p).ιE_πE
    have h₂ := (cut Y q).ιE_πE
    simp only [assoc, reassoc_of% h₁, h₂, comp_id]
  rw [e F, e G, h]

end Mat

/-! ### Half-constant functors -/

section HalfF

variable (p : ℤ → Prop) [DecidablePred p]

/-- The constant object `X` restricted to the positions `p`. -/
abbrev halfObj (X : A) : A.cz := (cut ((Δc A).F.obj X) p).E

/-- `f` restricted to the positions `p`. -/
def halfMap {X Y : A} (f : X ⟶ Y) : halfObj A p X ⟶ halfObj A p Y :=
  (cut ((Δc A).F.obj X) p).ιE ≫ (Δc A).F.map f ≫ (cut ((Δc A).F.obj Y) p).πE

lemma halfMap_id (X : A) : halfMap A p (𝟙 X) = 𝟙 _ := by
  rw [halfMap, CategoryTheory.Functor.map_id, id_comp, (cut _ p).ιE_πE]

lemma halfMap_comp {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    halfMap A p (f ≫ g) = halfMap A p f ≫ halfMap A p g := by
  simp only [halfMap, CategoryTheory.Functor.map_comp, assoc]
  rw [πE_ιE_assoc, idem_Δmap_assoc, idem_πE]

lemma halfMap_add {X Y : A} (f g : X ⟶ Y) : halfMap A p (f + g) = halfMap A p f
    + halfMap A p g := by
  simp [halfMap, CategoryTheory.Functor.map_add, add_comp, comp_add]

lemma halfMap_star {X Y : A} (f : X ⟶ Y) :
    halfMap A p (A.inv.star f) = A.cz.inv.star (halfMap A p f) := by
  rw [halfMap, halfMap, A.cz.inv.star_comp, A.cz.inv.star_comp, star_cut_ιE, star_cut_πE,
    (Δc A).map_star, assoc]

/-- **The half-constant functor** `X ↦ (X)_{v ∈ p}`. -/
@[implicit_reducible]
def halfF : A ⟶ A.cz where
  F :=
    { obj := halfObj A p
      map := halfMap A p
      map_id := halfMap_id A p
      map_comp := halfMap_comp A p }
  additive := ⟨fun {_ _ f g} ↦ halfMap_add A p f g⟩
  map_star := halfMap_star A p

@[simp] lemma halfF_obj (X : A) : (halfF A p).F.obj X = halfObj A p X := rfl

lemma halfF_map {X Y : A} (f : X ⟶ Y) : (halfF A p).F.map f = halfMap A p f := rfl

/-- The inclusion `κ : (X)_{v ∈ p} ⟶ ΔX`, natural. -/
def κ : (halfF A p).F ⟶ (Δc A).F where
  app X := (cut ((Δc A).F.obj X) p).ιE
  naturality {X Y} f := by
    change halfMap A p f ≫ _ = _
    rw [halfMap, assoc, assoc, πE_ιE, ← idem_Δmap, ιE_idem_assoc]

@[simp] lemma κ_app (X : A) : (κ A p).app X = (cut ((Δc A).F.obj X) p).ιE := rfl

variable (q : ℤ → Prop) [DecidablePred q]

/-- The compression `ι_E M π_E : (X)_p ⟶ (X)_q` of a natural constant matrix `M`. -/
def cutNat (M : ∀ X : A, (Δc A).F.obj X ⟶ (Δc A).F.obj X)
    (hM : ∀ {X Y : A} (f : X ⟶ Y), (Δc A).F.map f ≫ M Y = M X ≫ (Δc A).F.map f) :
    (halfF A p).F ⟶ (halfF A q).F where
  app X := (cut ((Δc A).F.obj X) p).ιE ≫ M X ≫ (cut ((Δc A).F.obj X) q).πE
  naturality {X Y} f := by
    change halfMap A p f ≫ _ = _ ≫ halfMap A q f
    simp only [halfMap, assoc]
    rw [πE_ιE_assoc, πE_ιE_assoc, ← idem_Δmap_assoc f p, ιE_idem_assoc, idem_Δmap_assoc f q,
      idem_πE, reassoc_of% (hM f)]

lemma cutNat_app (M : ∀ X : A, (Δc A).F.obj X ⟶ (Δc A).F.obj X)
    (hM : ∀ {X Y : A} (f : X ⟶ Y), (Δc A).F.map f ≫ M Y = M X ≫ (Δc A).F.map f) (X : A) :
    (cutNat A p q M hM).app X =
      (cut ((Δc A).F.obj X) p).ιE ≫ M X ≫ (cut ((Δc A).F.obj X) q).πE := rfl

end HalfF

/-! ### Entrywise computation of sandwiches -/

section Entries

variable {A}

lemma cs_comp_apply (k : ℤ) (X : A) {Y : A.cz} (g : (Δc A).F.obj X ⟶ Y) (w v : ℤ) :
    ((constShift k X : (Δc A).F.obj X ⟶ (Δc A).F.obj X) ≫ g).1 w v = g.1 w (v + k) := by
  rw [comp_apply, finsum_eq_single _ (v + k) fun u hu ↦ by simp [hu]]
  simp

lemma χ_comp_apply (X : A) (p : ℤ → Prop) [DecidablePred p] {Y : A.cz}
    (g : (Δc A).F.obj X ⟶ Y) (w v : ℤ) :
    (χ X p ≫ g).1 w v = if p v then g.1 w v else 0 := by
  rw [χ_eq, diag_comp_apply]
  split_ifs <;> simp

lemma χ_apply (X : A) (p : ℤ → Prop) [DecidablePred p] (w v : ℤ) :
    (χ X p).1 w v = if p v ∧ w = v then 𝟙 X else 0 := by
  rw [χ_eq]
  by_cases h : v = w
  · subst h; rw [diag_apply_self]; simp
  · rw [diag_apply_ne _ h]; simp [Ne.symm h]

lemma add_Δ_apply {X Y : A.cz} (f g : X ⟶ Y) (w v : ℤ) : (f + g).1 w v = f.1 w v + g.1 w v := rfl

/-- Composites of compressions are compressions of sandwiches. -/
lemma comp_sandwich {X : A} (p q r : ℤ → Prop) [DecidablePred p] [DecidablePred q]
    [DecidablePred r] (M₁ M₂ : (Δc A).F.obj X ⟶ (Δc A).F.obj X) :
    ((cut ((Δc A).F.obj X) p).ιE ≫ M₁ ≫ (cut ((Δc A).F.obj X) q).πE) ≫
        ((cut ((Δc A).F.obj X) q).ιE ≫ M₂ ≫ (cut ((Δc A).F.obj X) r).πE) =
      (cut ((Δc A).F.obj X) p).ιE ≫ (χ X p ≫ M₁ ≫ χ X q ≫ M₂ ≫ χ X r) ≫
        (cut ((Δc A).F.obj X) r).πE := by
  simp only [assoc]
  rw [πE_ιE_assoc, idem_πE, ιE_idem_assoc]

lemma id_sandwich {X : A} (p : ℤ → Prop) [DecidablePred p] :
    𝟙 ((cut ((Δc A).F.obj X) p).E) =
      (cut ((Δc A).F.obj X) p).ιE ≫ χ X p ≫ (cut ((Δc A).F.obj X) p).πE := by
  rw [ιE_idem_assoc, (cut _ p).ιE_πE]

lemma zero_sandwich {X : A} (p q : ℤ → Prop) [DecidablePred p] [DecidablePred q] :
    (0 : (cut ((Δc A).F.obj X) p).E ⟶ (cut ((Δc A).F.obj X) q).E) =
      (cut ((Δc A).F.obj X) p).ιE ≫ 0 ≫ (cut ((Δc A).F.obj X) q).πE := by
  simp

/-- Normal form of entries of sandwich matrices. -/
macro "entry_simp" : tactic => `(tactic| (
  ext w v
  simp only [assoc, χ_comp_apply, cs_comp_apply, χ_apply, add_Δ_apply, zero_apply,
    lineData_s_hom, lineData_s_inv, sh, shi, comp_add, add_comp, comp_zero, zero_comp, id_comp,
    comp_id]
  split_ifs <;> first | rfl | (exfalso; omega) | simp | skip))

end Entries

/-! ### The negative half-line -/

section Neg

/-- `(X)_{v ≤ c}`. -/
abbrev leF (c : ℤ) : A ⟶ A.cz := halfF A (fun v ↦ v ≤ c)

/-- The boundary vertex `X ⟶ (X)_{v ∈ p}` at `0`, natural on `atZero`. -/
def βNat (p : ℤ → Prop) [DecidablePred p] : (atZero A).F ⟶ (halfF A p).F where
  app X := ((cut ((Δc A).F.obj X) (fun v ↦ v = 0)).ιE ≫ 𝟙 _ ≫ (cut ((Δc A).F.obj X) p).πE :
    (cut ((Δc A).F.obj X) (fun v ↦ v = 0)).E ⟶ _)
  naturality {X Y} f :=
    (cutNat A (fun v ↦ v = 0) p (fun X ↦ 𝟙 _) (fun f ↦ by simp)).naturality f

lemma βNat_app (p : ℤ → Prop) [DecidablePred p] (X : A) :
    (βNat A p).app X =
      (cut ((Δc A).F.obj X) (fun v ↦ v = 0)).ιE ≫ 𝟙 _ ≫ (cut ((Δc A).F.obj X) p).πE :=
  rfl

lemma sandwich_congr {X : A} (p q : ℤ → Prop) [DecidablePred p] [DecidablePred q]
    {M M' : (Δc A).F.obj X ⟶ (Δc A).F.obj X} (h : M = M') :
    (cut ((Δc A).F.obj X) p).ιE ≫ M ≫ (cut ((Δc A).F.obj X) q).πE =
      (cut ((Δc A).F.obj X) p).ιE ≫ M' ≫ (cut ((Δc A).F.obj X) q).πE := by rw [h]

/-! #### Stars in the involution of `C_ℤ(A)` -/

variable {A}

lemma star_ιE' (X : A.cz) (p : ℤ → Prop) [DecidablePred p] :
    (involution : StrictInvolution (Obj A)).star (cut X p).ιE = (cut X p).πE := star_cut_ιE X p

lemma star_πE' (X : A.cz) (p : ℤ → Prop) [DecidablePred p] :
    (involution : StrictInvolution (Obj A)).star (cut X p).πE = (cut X p).ιE := star_cut_πE X p

lemma star_sh (X : A) : (involution : StrictInvolution (Obj A)).star (sh X) = shi X :=
  (lineData A).star_s_hom X

lemma comp_star_sandwich {X : A} (p q r : ℤ → Prop) [DecidablePred p] [DecidablePred q]
    [DecidablePred r] (M₁ M₂ : (Δc A).F.obj X ⟶ (Δc A).F.obj X) :
    ((cut ((Δc A).F.obj X) p).ιE ≫ M₁ ≫ (cut ((Δc A).F.obj X) q).πE) ≫
        (involution : StrictInvolution (Obj A)).star
          ((cut ((Δc A).F.obj X) r).ιE ≫ M₂ ≫ (cut ((Δc A).F.obj X) q).πE) =
      (cut ((Δc A).F.obj X) p).ιE ≫ (χ X p ≫ M₁ ≫ χ X q ≫
        (involution : StrictInvolution (Obj A)).star M₂ ≫ χ X r) ≫ (cut ((Δc A).F.obj X) r).πE := by
  rw [StrictInvolution.star_comp, StrictInvolution.star_comp, star_ιE', star_πE']
  simp only [assoc]
  rw [πE_ιE_assoc, idem_πE, ιE_idem_assoc]

lemma star_comp_sandwich {X : A} (p q r : ℤ → Prop) [DecidablePred p] [DecidablePred q]
    [DecidablePred r] (M₁ M₂ : (Δc A).F.obj X ⟶ (Δc A).F.obj X) :
    (involution : StrictInvolution (Obj A)).star
          ((cut ((Δc A).F.obj X) q).ιE ≫ M₁ ≫ (cut ((Δc A).F.obj X) p).πE) ≫
        ((cut ((Δc A).F.obj X) q).ιE ≫ M₂ ≫ (cut ((Δc A).F.obj X) r).πE) =
      (cut ((Δc A).F.obj X) p).ιE ≫ (χ X p ≫ (involution : StrictInvolution (Obj A)).star M₁ ≫
        χ X q ≫ M₂ ≫ χ X r) ≫ (cut ((Δc A).F.obj X) r).πE := by
  rw [StrictInvolution.star_comp, StrictInvolution.star_comp, star_ιE', star_πE']
  simp only [assoc]
  rw [πE_ιE_assoc, idem_πE, ιE_idem_assoc]

lemma star_id' (X : A.cz) : (involution : StrictInvolution (Obj A)).star (𝟙 X) = 𝟙 X :=
  StrictInvolution.star_id _ X

variable (A)

/-! #### The relations of the negative half-line -/

section NegRel

variable {A} (X : A)


lemma neg_u_star : ((cut ((Δc A).F.obj X) (fun v ↦ v ≤ -1)).ιE ≫ sh X ≫
    (cut ((Δc A).F.obj X) (fun v ↦ v ≤ 0)).πE) ≫
        (involution : StrictInvolution (Obj A)).star ((cut ((Δc A).F.obj X) (fun v ↦ v ≤ -1)).ιE ≫
            sh X ≫ (cut ((Δc A).F.obj X) (fun v ↦ v ≤ 0)).πE) = 𝟙 _ := by
  rw [comp_star_sandwich]
  refine (sandwich_congr _ _ _ ?_).trans (id_sandwich _).symm
  rw [star_sh, idem_sh_idem_assoc X _ _ (fun v hv ↦ by omega),
    LineData.s_hom_inv_assoc, idem_idem_self]

lemma neg_star_u : (involution : StrictInvolution (Obj A)).star ((cut ((Δc A).F.obj X)
    (fun v ↦ v ≤ -1)).ιE ≫ sh X ≫ (cut ((Δc A).F.obj X) (fun v ↦ v ≤ 0)).πE) ≫
        ((cut ((Δc A).F.obj X) (fun v ↦ v ≤ -1)).ιE ≫ sh X ≫
            (cut ((Δc A).F.obj X) (fun v ↦ v ≤ 0)).πE) = 𝟙 _ := by
  rw [star_comp_sandwich]
  refine (sandwich_congr _ _ _ ?_).trans (id_sandwich _).symm
  rw [star_sh, idem_shi_idem_assoc X _ _ (fun v hv ↦ by omega),
    LineData.s_inv_hom_assoc, idem_idem_self]

lemma neg_w_star : ((cut ((Δc A).F.obj X) (fun v ↦ v ≤ -1)).ιE ≫ 𝟙 _ ≫
    (cut ((Δc A).F.obj X) (fun v ↦ v ≤ 0)).πE) ≫
        (involution : StrictInvolution (Obj A)).star ((cut ((Δc A).F.obj X) (fun v ↦ v ≤ -1)).ιE ≫
            𝟙 _ ≫ (cut ((Δc A).F.obj X) (fun v ↦ v ≤ 0)).πE) = 𝟙 _ := by
  rw [comp_star_sandwich]
  refine (sandwich_congr _ _ _ ?_).trans (id_sandwich _).symm
  rw [star_id', id_comp, id_comp, idem_idem_assoc X _ _ (fun v ↦ v ≤ -1)
    (fun v ↦ by (try dsimp only); omega), idem_idem_self]

lemma neg_β_star : ((cut ((Δc A).F.obj X) (fun v ↦ v = 0)).ιE ≫ 𝟙 _ ≫
    (cut ((Δc A).F.obj X) (fun v ↦ v ≤ 0)).πE) ≫
        (involution : StrictInvolution (Obj A)).star ((cut ((Δc A).F.obj X) (fun v ↦ v = 0)).ιE ≫
            𝟙 _ ≫ (cut ((Δc A).F.obj X) (fun v ↦ v ≤ 0)).πE) = 𝟙 _ := by
  rw [comp_star_sandwich]
  refine (sandwich_congr _ _ _ ?_).trans (id_sandwich _).symm
  rw [star_id', id_comp, id_comp, idem_idem_assoc X _ _ (fun v ↦ v = 0)
    (fun v ↦ by (try dsimp only); omega), idem_idem_self]

lemma neg_w_star_β : ((cut ((Δc A).F.obj X) (fun v ↦ v ≤ -1)).ιE ≫ 𝟙 _ ≫
    (cut ((Δc A).F.obj X) (fun v ↦ v ≤ 0)).πE) ≫
        (involution : StrictInvolution (Obj A)).star ((cut ((Δc A).F.obj X) (fun v ↦ v = 0)).ιE ≫
            𝟙 _ ≫ (cut ((Δc A).F.obj X) (fun v ↦ v ≤ 0)).πE) = 0 := by
  rw [comp_star_sandwich]
  refine (sandwich_congr _ _ _ ?_).trans (zero_sandwich _ _).symm
  rw [star_id', id_comp, id_comp, idem_idem_assoc X _ _ (fun v ↦ v ≤ -1)
    (fun v ↦ by (try dsimp only); omega), idem_idem X _ _ (fun v ↦ v ≤ -1 ∧ v = 0)
    (fun v ↦ Iff.rfl), idem_eq_zero X _ (fun v h ↦ by omega)]

lemma neg_total : (involution : StrictInvolution (Obj A)).star ((cut ((Δc A).F.obj X)
    (fun v ↦ v ≤ -1)).ιE ≫ 𝟙 _ ≫ (cut ((Δc A).F.obj X) (fun v ↦ v ≤ 0)).πE) ≫
        ((cut ((Δc A).F.obj X) (fun v ↦ v ≤ -1)).ιE ≫ 𝟙 _ ≫
            (cut ((Δc A).F.obj X) (fun v ↦ v ≤ 0)).πE) +
    (involution : StrictInvolution (Obj A)).star ((cut ((Δc A).F.obj X) (fun v ↦ v = 0)).ιE ≫ 𝟙 _ ≫
        (cut ((Δc A).F.obj X) (fun v ↦ v ≤ 0)).πE) ≫ ((cut ((Δc A).F.obj X) (fun v ↦ v = 0)).ιE ≫
            𝟙 _ ≫ (cut ((Δc A).F.obj X) (fun v ↦ v ≤ 0)).πE) = 𝟙 _ := by
  rw [star_comp_sandwich, star_comp_sandwich, ← comp_add, ← add_comp]
  refine (sandwich_congr _ _ _ ?_).trans (id_sandwich _).symm
  rw [star_id']
  simp only [id_comp]
  rw [idem_idem_assoc X _ _ (fun v ↦ v ≤ -1) (fun v ↦ by (try dsimp only); omega),
    idem_idem X _ _ (fun v ↦ v ≤ -1) (fun v ↦ by (try dsimp only); omega),
    idem_idem_assoc X _ _ (fun v ↦ v = 0) (fun v ↦ by (try dsimp only); omega),
    idem_idem X _ _ (fun v ↦ v = 0) (fun v ↦ by (try dsimp only); omega),
    idem_add_idem X _ _ (fun v ↦ v ≤ 0) (fun v ↦ by (try dsimp only); omega)
      (fun v ↦ by omega)]

end NegRel

/-- **The half-line data of `(-∞, 0]`.** -/
abbrev negLine : HalfLineData A A.cz where
  E := leF A (-1)
  V := leF A 0
  O := atZero A
  u := cutNat A (fun v ↦ v ≤ -1) (fun v ↦ v ≤ 0) (fun X ↦ sh X)
    (fun f ↦ (lineData A).s_hom_nat f)
  w := cutNat A (fun v ↦ v ≤ -1) (fun v ↦ v ≤ 0) (fun X ↦ 𝟙 _) (fun f ↦ by simp)
  β := βNat A (fun v ↦ v ≤ 0)
  u_star X := neg_u_star X
  star_u X := neg_star_u X
  w_star X := neg_w_star X
  β_star X := neg_β_star X
  w_star_β X := neg_w_star_β X
  total X := neg_total X

end Neg

/-! ### The positive half-line -/

section Pos

/-- `(X)_{v ≥ 0}`. -/
abbrev geF : A ⟶ A.cz := halfF A (fun v ↦ 0 ≤ v)

section PosRel

variable {A} (X : A)


lemma pos_w_star : ((cut ((Δc A).F.obj X) (fun v ↦ 0 ≤ v)).ιE ≫ sh X ≫
    (cut ((Δc A).F.obj X) (fun v ↦ 0 ≤ v)).πE) ≫
        (involution : StrictInvolution (Obj A)).star ((cut ((Δc A).F.obj X) (fun v ↦ 0 ≤ v)).ιE ≫
            sh X ≫ (cut ((Δc A).F.obj X) (fun v ↦ 0 ≤ v)).πE) = 𝟙 _ := by
  rw [comp_star_sandwich]
  refine (sandwich_congr _ _ _ ?_).trans (id_sandwich _).symm
  rw [star_sh, idem_sh_idem_assoc X _ _ (fun v hv ↦ by omega),
    LineData.s_hom_inv_assoc, idem_idem_self]

lemma pos_β_star : ((cut ((Δc A).F.obj X) (fun v ↦ v = 0)).ιE ≫ 𝟙 _ ≫
    (cut ((Δc A).F.obj X) (fun v ↦ 0 ≤ v)).πE) ≫
        (involution : StrictInvolution (Obj A)).star ((cut ((Δc A).F.obj X) (fun v ↦ v = 0)).ιE ≫
            𝟙 _ ≫ (cut ((Δc A).F.obj X) (fun v ↦ 0 ≤ v)).πE) = 𝟙 _ := by
  rw [comp_star_sandwich]
  refine (sandwich_congr _ _ _ ?_).trans (id_sandwich _).symm
  rw [star_id', id_comp, id_comp, idem_idem_assoc X _ _ (fun v ↦ v = 0)
    (fun v ↦ by (try dsimp only); omega), idem_idem_self]

lemma pos_w_star_β : ((cut ((Δc A).F.obj X) (fun v ↦ 0 ≤ v)).ιE ≫ sh X ≫
    (cut ((Δc A).F.obj X) (fun v ↦ 0 ≤ v)).πE) ≫
        (involution : StrictInvolution (Obj A)).star ((cut ((Δc A).F.obj X) (fun v ↦ v = 0)).ιE ≫
            𝟙 _ ≫ (cut ((Δc A).F.obj X) (fun v ↦ 0 ≤ v)).πE) = 0 := by
  rw [comp_star_sandwich]
  refine (sandwich_congr _ _ _ ?_).trans (zero_sandwich _ _).symm
  rw [star_id', id_comp, idem_sh_idem_assoc X _ _ (fun v hv ↦ by omega),
    idem_sh_idem_eq_zero X _ _ (fun v hv ↦ by omega)]

lemma pos_total : (involution : StrictInvolution (Obj A)).star ((cut ((Δc A).F.obj X)
    (fun v ↦ 0 ≤ v)).ιE ≫ sh X ≫ (cut ((Δc A).F.obj X) (fun v ↦ 0 ≤ v)).πE) ≫
        ((cut ((Δc A).F.obj X) (fun v ↦ 0 ≤ v)).ιE ≫ sh X ≫
            (cut ((Δc A).F.obj X) (fun v ↦ 0 ≤ v)).πE) +
    (involution : StrictInvolution (Obj A)).star ((cut ((Δc A).F.obj X) (fun v ↦ v = 0)).ιE ≫ 𝟙 _ ≫
        (cut ((Δc A).F.obj X) (fun v ↦ 0 ≤ v)).πE) ≫ ((cut ((Δc A).F.obj X) (fun v ↦ v = 0)).ιE ≫
            𝟙 _ ≫ (cut ((Δc A).F.obj X) (fun v ↦ 0 ≤ v)).πE) = 𝟙 _ := by
  rw [star_comp_sandwich, star_comp_sandwich, ← comp_add, ← add_comp]
  refine (sandwich_congr _ _ _ ?_).trans (id_sandwich _).symm
  rw [star_id', star_sh, id_comp, id_comp, shi_idem_assoc, LineData.s_inv_hom_assoc,
    idem_idem_assoc X _ _ (fun v ↦ 0 ≤ v + -1) (fun v ↦ by (try dsimp only); omega),
    idem_idem X _ _ (fun v ↦ 0 ≤ v + -1) (fun v ↦ by (try dsimp only); omega),
    idem_idem_assoc X _ _ (fun v ↦ v = 0) (fun v ↦ by (try dsimp only); omega),
    idem_idem X _ _ (fun v ↦ v = 0) (fun v ↦ by (try dsimp only); omega),
    idem_add_idem X _ _ (fun v ↦ 0 ≤ v) (fun v ↦ by (try dsimp only); omega)
      (fun v ↦ by omega)]

end PosRel

/-- **The half-line data of `[0, ∞)`.** -/
abbrev posLine : HalfLineData A A.cz where
  E := geF A
  V := geF A
  O := atZero A
  u := 𝟙 _
  w := cutNat A (fun v ↦ 0 ≤ v) (fun v ↦ 0 ≤ v) (fun X ↦ sh X) (fun f ↦ (lineData A).s_hom_nat f)
  β := βNat A (fun v ↦ 0 ≤ v)
  u_star X := by simp
  star_u X := by simp
  w_star X := pos_w_star X
  β_star X := pos_β_star X
  w_star_β X := pos_w_star_β X
  total X := pos_total X

end Pos

end CZ

end

end HSFormal.LTheory
