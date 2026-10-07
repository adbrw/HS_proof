import HSFormal.LTheory.Model.Transport

/-!
# Free-ification of Kar complexes: chain-level tools (lower L-theory model, module 15)

Support for `Model/FreeLine.lean` (plan (L1-i)), independent of the line complex.

* **The e-trick.**  For a complex `K`, a chain idempotent `q` and a chain map `a` commuting with
  `q`, put `b = q a + q - 1` (for `a = s - 1` this is `q s - 1`).  Then the Kar complex
  `(Cone(a), q ⊕ q)` is Kar homotopy equivalent to the honest complex `(Cone(b), 1)`
  (`eTrick`): with respect to `K = (K, q) ⊕ (K, 1 - q)`, `b = q a q ⊕ (-(1 - q))`, so
  `Cone(b) = (Cone(a), q ⊕ q) ⊕ Cone(-(1 - q))` and the second summand is contractible.  Both
  maps are `q ⊕ q`; `(q ⊕ q)(q ⊕ q) = q ⊕ q` strictly, and on `Cone(b)` the homotopy
  `q ⊕ q ≃ 1` is `(x, y) ↦ ((1 - q) y, 0)` (`eHomotopy`, via `coneHomotopy`).
* **Zero-truncation.**  A chain idempotent `p` supported in `[lo, hi]` lives on a complex `C`
  whose objects outside `[lo, hi]` need not vanish.  `cutCx C lo hi` replaces them by zero
  objects (keeping `C.X r` for `r ∈ [lo, hi]`), `cutP` is `p` on it, and
  `(C, p) ≅ (cutCx C lo hi, cutP)` strictly in `Kar` (`cutEquiv`).  This is needed to make the
  free model *bounded*: its identity must be supported in the dimension range.
* `isZero_cone_X`: a cone is zero in degree `i` if both summands are.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression
  homotopyCofiber

noncomputable section

namespace FreeLine

variable {V : Type*} [Category V] [Preadditive V]

/-! ### The e-trick -/

section ETrick

variable [HasBinaryBiproducts V] {K : ChainComplex V ℤ} (a q : K ⟶ K)

/-- The e-trick differential `b = q a + q - 1` (`= q s - 1` for `a = s - 1`). -/
def eDiff : K ⟶ K := q ≫ a + q - 𝟙 K

omit [HasBinaryBiproducts V] in
lemma eDiff_f (i : ℤ) : (eDiff a q).f i = q.f i ≫ a.f i + q.f i - 𝟙 _ := rfl

variable {a q}

omit [HasBinaryBiproducts V] in
lemma eDiff_sq_to (hq : q ≫ q = q) (hc : q ≫ a = a ≫ q) : q ≫ eDiff a q = a ≫ q := by
  rw [eDiff, comp_sub, comp_add, ← assoc, hq, comp_id, add_sub_cancel_right, hc]

omit [HasBinaryBiproducts V] in
lemma eDiff_sq_from (hq : q ≫ q = q) (hc : q ≫ a = a ≫ q) : q ≫ a = eDiff a q ≫ q := by
  rw [eDiff, sub_comp, add_comp, id_comp, hq, add_sub_cancel_right, assoc, ← hc, ← assoc, hq]

variable (hq : q ≫ q = q) (hc : q ≫ a = a ≫ q)

/-- `q ⊕ q : Cone(a) ⟶ Cone(b)`. -/
def eTo : cone a ⟶ cone (eDiff a q) := coneMap q q (eDiff_sq_to hq hc)

/-- `q ⊕ q : Cone(b) ⟶ Cone(a)`. -/
def eFrom : cone (eDiff a q) ⟶ cone a := coneMap q q (eDiff_sq_from hq hc)

lemma eTo_eq : eTo hq hc = coneMap q q (eDiff_sq_to hq hc) := rfl

lemma eFrom_eq : eFrom hq hc = coneMap q q (eDiff_sq_from hq hc) := rfl

/-- The homotopy `q ⊕ q ≃ 1` on `Cone(b)`, `(x, y) ↦ ((1 - q) y, 0)`. -/
def eHomotopy : Homotopy (coneMap q q (j := eDiff a q) (j' := eDiff a q)
    (by rw [eDiff_sq_to hq hc, ← hc, eDiff_sq_from hq hc])) (𝟙 _) :=
  homotopyCongr (coneHomotopy (𝟙 K - q) (m := q) (n := q) (m' := 𝟙 K) (n' := 𝟙 K) _ (by simp)
      (by
        rw [comp_sub, comp_id, ← eDiff_sq_from hq hc]
        simp only [eDiff]; abel)
      (by
        rw [sub_comp, id_comp, eDiff_sq_to hq hc, ← hc]
        simp only [eDiff]; abel)) rfl (coneMap_id _)

/-- **The e-trick**: `(Cone(a), q ⊕ q) ≃ (Cone(q a + q - 1), 1)` in `Kar`. -/
@[simps]
def eTrick : KarHtpyEquiv (coneMap q q hc : cone a ⟶ cone a) (𝟙 (cone (eDiff a q))) where
  f := eTo hq hc
  g := eFrom hq hc
  pf := by rw [eTo, coneMap_comp]; congr 1
  fp := comp_id _
  pg := id_comp _
  gp := by rw [eFrom, coneMap_comp]; congr 1
  fg := Homotopy.ofEq (by rw [eTo, eFrom, coneMap_comp]; congr 1)
  gf := homotopyCongr (eHomotopy hq hc)
    (by rw [eTo, eFrom, coneMap_comp]; congr 1 <;> exact hq.symm) rfl

end ETrick

/-! ### Cones of zero objects -/

lemma isZero_cone_X [HasBinaryBiproducts V] {B D : ChainComplex V ℤ} (j : B ⟶ D) (i : ℤ)
    (hB : IsZero (B.X (i - 1))) (hD : IsZero (D.X i)) : IsZero ((cone j).X i) := by
  rw [IsZero.iff_id_eq_zero, cone.id_X j i (i - 1) (by simp),
    hB.eq_of_src (inlX j (i - 1) i _) 0, hD.eq_of_src (inrX j i) 0]
  simp

/-! ### Zero-truncation -/

section Cut

open ZeroObject

variable [HasZeroObject V] (C : ChainComplex V ℤ) (lo hi : ℤ)

/-- The objects of `C` in `[lo, hi]`, zero outside. -/
def cutX (r : ℤ) : V := if lo ≤ r ∧ r ≤ hi then C.X r else 0

variable {C lo hi}

lemma cutX_of_mem {r : ℤ} (h : lo ≤ r ∧ r ≤ hi) : cutX C lo hi r = C.X r := if_pos h

lemma isZero_cutX {r : ℤ} (h : ¬ (lo ≤ r ∧ r ≤ hi)) : IsZero (cutX C lo hi r) := by
  rw [cutX, if_neg h]; exact isZero_zero V

variable (C lo hi)

/-- The inclusion `C_r ⟶ (cut C)_r` (the identity in `[lo, hi]`). -/
def cutIn (r : ℤ) : C.X r ⟶ cutX C lo hi r :=
  if h : lo ≤ r ∧ r ≤ hi then eqToHom (cutX_of_mem h).symm else 0

/-- The projection `(cut C)_r ⟶ C_r` (the identity in `[lo, hi]`). -/
def cutOut (r : ℤ) : cutX C lo hi r ⟶ C.X r :=
  if h : lo ≤ r ∧ r ≤ hi then eqToHom (cutX_of_mem h) else 0

variable {C lo hi}

@[reassoc (attr := simp)]
lemma cutOut_cutIn (r : ℤ) : cutOut C lo hi r ≫ cutIn C lo hi r = 𝟙 _ := by
  by_cases h : lo ≤ r ∧ r ≤ hi
  · simp [cutOut, cutIn, h]
  · exact (isZero_cutX h).eq_of_src _ _

@[reassoc]
lemma cutIn_cutOut_of_mem {r : ℤ} (h : lo ≤ r ∧ r ≤ hi) :
    cutIn C lo hi r ≫ cutOut C lo hi r = 𝟙 _ := by
  simp [cutOut, cutIn, h]

lemma cutIn_of_not_mem {r : ℤ} (h : ¬ (lo ≤ r ∧ r ≤ hi)) : cutIn C lo hi r = 0 := by
  simp [cutIn, h]

lemma cutOut_of_not_mem {r : ℤ} (h : ¬ (lo ≤ r ∧ r ≤ hi)) : cutOut C lo hi r = 0 := by
  simp [cutOut, h]

variable (C lo hi)

/-- **The zero-truncation** of `C` to `[lo, hi]`: objects `C_r` in `[lo, hi]`, zero objects
outside, and the differential of `C` inside. -/
@[simps, implicit_reducible]
def cutCx : ChainComplex V ℤ where
  X := cutX C lo hi
  d i j := cutOut C lo hi i ≫ C.d i j ≫ cutIn C lo hi j
  shape i j h := by rw [C.shape i j h, zero_comp, comp_zero]
  d_comp_d' i j k _ _ := by
    simp only [assoc]
    by_cases h : lo ≤ j ∧ j ≤ hi
    · rw [cutIn_cutOut_of_mem_assoc h, C.d_comp_d_assoc, zero_comp, comp_zero]
    · rw [cutIn_of_not_mem h, zero_comp, comp_zero, comp_zero]

lemma isZero_cutCx_X {r : ℤ} (h : ¬ (lo ≤ r ∧ r ≤ hi)) : IsZero ((cutCx C lo hi).X r) :=
  isZero_cutX h

variable {C lo hi} {p : C ⟶ C} (hs : SupportedIn p lo hi)
include hs

@[reassoc]
lemma p_cutIn_cutOut (r : ℤ) : p.f r ≫ cutIn C lo hi r ≫ cutOut C lo hi r = p.f r := by
  by_cases h : lo ≤ r ∧ r ≤ hi
  · rw [cutIn_cutOut_of_mem h, comp_id]
  · rw [hs r (by omega), zero_comp]

@[reassoc]
lemma cutIn_cutOut_p (r : ℤ) : cutIn C lo hi r ≫ cutOut C lo hi r ≫ p.f r = p.f r := by
  by_cases h : lo ≤ r ∧ r ≤ hi
  · rw [cutIn_cutOut_of_mem_assoc h]
  · rw [hs r (by omega), comp_zero, comp_zero]

/-- `p : C ⟶ cut C`. -/
@[simps]
def cutTo : C ⟶ cutCx C lo hi where
  f r := p.f r ≫ cutIn C lo hi r
  comm' i j _ := by
    simp only [cutCx_d, assoc, p_cutIn_cutOut_assoc hs]
    rw [← p.comm_assoc]

/-- `p : cut C ⟶ C`. -/
@[simps]
def cutFrom : cutCx C lo hi ⟶ C where
  f r := cutOut C lo hi r ≫ p.f r
  comm' i j _ := by
    simp only [cutCx_d, assoc, cutIn_cutOut_p hs]
    rw [p.comm]

/-- `p` on the zero-truncation. -/
@[simps]
def cutP : cutCx C lo hi ⟶ cutCx C lo hi where
  f r := cutOut C lo hi r ≫ p.f r ≫ cutIn C lo hi r
  comm' i j _ := by
    simp only [cutCx_d, assoc, p_cutIn_cutOut_assoc hs, cutIn_cutOut_p_assoc hs]
    rw [p.comm_assoc]

variable (hp : p ≫ p = p)
include hp

omit hs [HasZeroObject V] in
@[reassoc]
lemma p_f_idem (r : ℤ) : p.f r ≫ p.f r = p.f r := by rw [← comp_f, hp]

@[reassoc (attr := simp)]
lemma cutTo_cutFrom : cutTo hs ≫ cutFrom hs = p := by
  ext r; simp [p_cutIn_cutOut_assoc hs, p_f_idem hp]

@[reassoc (attr := simp)]
lemma cutFrom_cutTo : cutFrom hs ≫ cutTo hs = cutP hs := by
  ext r; simp [p_f_idem_assoc hp]

@[reassoc]
lemma cutTo_cutP : cutTo hs ≫ cutP hs = cutTo hs := by
  ext r; simp [p_cutIn_cutOut_assoc hs, p_f_idem_assoc hp]

@[reassoc]
lemma cutP_cutFrom : cutP hs ≫ cutFrom hs = cutFrom hs := by
  ext r; simp [p_cutIn_cutOut_assoc hs, p_f_idem hp]

@[reassoc]
lemma p_cutTo : p ≫ cutTo hs = cutTo hs := by
  ext r; simp [p_f_idem_assoc hp]

@[reassoc]
lemma cutFrom_p : cutFrom hs ≫ p = cutFrom hs := by
  ext r; simp [p_f_idem hp]

lemma cutP_idem : cutP hs ≫ cutP hs = cutP hs := by
  ext r; simp [cutIn_cutOut_p_assoc hs, p_f_idem_assoc hp]

omit hp in
lemma supportedIn_cutP : SupportedIn (cutP hs) lo hi := fun r hr ↦ by
  simp [hs r hr]

/-- **`(C, p) ≅ (cut C, p)`** strictly in `Kar`. -/
@[simps]
def cutEquiv : KarHtpyEquiv p (cutP hs) where
  f := cutTo hs
  g := cutFrom hs
  pf := p_cutTo hs hp
  fp := cutTo_cutP hs hp
  pg := cutP_cutFrom hs hp
  gp := cutFrom_p hs hp
  fg := Homotopy.ofEq (cutTo_cutFrom hs hp)
  gf := Homotopy.ofEq (cutFrom_cutTo hs hp)

end Cut

end FreeLine

end

end HSFormal.LTheory
