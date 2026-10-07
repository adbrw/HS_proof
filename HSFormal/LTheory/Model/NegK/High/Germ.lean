import HSFormal.LTheory.Model.NegK.High.LaurentCZ
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NoncommRing

/-!
# The germ lemma (NegKHigh, module N4)

`blueprint/negK-high.md` §3.2 (Lemma G), §7 row N4; review `negK-high-review.md` GAP G1.

**Lemma G** (`germ_left`, `germ_right`).  Let `T` be an object of `L^l(C_ℤ Y)` and `P₁, P₂`
idempotents on `T` with `P₁ - P₂` left-supported (resp. right-supported).  Then
`(T, P₁) ∼ (T, P₂)` (`StablyIso` in `Karoubi (L^l(C_ℤ Y))`).

*Proof* (blueprint §3.2, with the review's fix G1).
1. `u = P₁P₂`, `v = P₂P₁` (operator order).  The Whitehead matrix `w` on `T ⊕ T` and its explicit
   inverse are written in the ring `Matrix (Fin 2) (Fin 2) (End T)` (`whitehead`,
   `whiteheadInv`) and transported to `End (T ⊕ T)` by the ring hom `matHom` of a bicone.
2. `w·diag(P₂, 1 - P₁) - diag(1, 0)·w = Δ` with `Δ = [[0, P₁DP₁], [-P₂DP₂, 0]]`, `D = P₁ - P₂`
   (`whitehead_mul_diag_sub`).  Hence `E := w diag(P₂, 1 - P₁) w⁻¹` satisfies `E - E₀ = Δ w⁻¹`
   with `E₀ = diag(1, 0)`: its entries are left-supported, so `E - E₀` is supported in some
   `(-∞, c]²` on `T ⊕ T` (pointwise bicone, `chi_biconeOf`).
3. **G1.**  `E` and `E₀` commute with the cut `σ` of `T ⊕ T` at `c` and have the same `U`-part;
   their `E`-parts live on a negative half-line and are absorbed (Lemma H).  So
   `(T ⊕ T, E) ∼ (T ⊕ T, E₀)` by `stablyIso_of_eq_U`, which rests on `karIso_sum_of_comm` (the
   Kar decomposition `(Q, q) ≅ (σ.E, q_E) ⊕ (σ.U, q_U)` extracted from the proof of
   `karAbsorbs_of_splitting`, reproved here).
4. `(T, P₂) ⊕ (T, 1 - P₁) ≅ (T ⊕ T, E) ∼ (T ⊕ T, E₀) ≅ (T, 1) ⊕ (T, 0) ∼ 0`, and cancellation of
   the complement (`StablyIso.of_biprod_complement`) gives `(T, P₂) ∼ (T, P₁)`.

The core (`germ_core`) is stated for an arbitrary support predicate `p`; `germ_left`/`germ_right`
instantiate it with half-lines.  **Lemma G′** (`germ_left'`, `germ_right'`): for idempotents on
different objects `Z, Z'`, retracts of a common object `T`, whose transports to `T` differ by a
left- (right-) supported map; the construction of `T` is left to the application (N8).
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive Idempotents

noncomputable section

universe v u

/-! ### Kar decomposition along a splitting (review fix G1) -/

section Splitting

variable {V : Type u} [Category.{v} V] [Preadditive V]

/-- The parts `q_E = ιE q πE`, `q_U = ιU q πU` of an endomorphism along a splitting. -/
abbrev _root_.HSFormal.Splitting.partE {Q : V} (σ : Splitting Q) (q : Q ⟶ Q) : σ.E ⟶ σ.E := σ.ιE ≫ q ≫ σ.πE

/-- The `U`-part of an endomorphism along a splitting. -/
abbrev _root_.HSFormal.Splitting.partU {Q : V} (σ : Splitting Q) (q : Q ⟶ Q) : σ.U ⟶ σ.U := σ.ιU ≫ q ≫ σ.πU

/-- **`karIso_sum_of_comm`** (extracted from `karAbsorbs_of_splitting`): an idempotent `q`
commuting with a splitting `Q = E ⊕ U` is the sum of its parts along the splitting bicone, so
`(Q, q) ≅ (E, q_E) ⊕ (U, q_U)` as raw Kar objects. -/
def karIso_sum_of_comm {Q : V} (σ : Splitting Q) {q : Q ⟶ Q} (hq : q ≫ q = q)
    (hc : q ≫ σ.idem = σ.idem ≫ q) :
    Wall.KarIso q (σ.bicone.fst ≫ σ.partE q ≫ σ.bicone.inl +
      σ.bicone.snd ≫ σ.partU q ≫ σ.bicone.inr) :=
  (Wall.KarIso.refl hq).congr rfl (by
    show q = σ.πE ≫ (σ.ιE ≫ q ≫ σ.πE) ≫ σ.ιE + σ.πU ≫ (σ.ιU ≫ q ≫ σ.πU) ≫ σ.ιU
    simp only [assoc]
    exact SplitKar.eq_add_of_comm σ hc)

variable [HasFiniteBiproducts V]

/-- `karIso_sum_of_comm` in `Karoubi V`: `(Q, q) ≅ (E, q_E) ⊞ (U, q_U)`. -/
def karoubiIsoSumOfComm {Q : V} (σ : Splitting Q) {q : Q ⟶ Q} (hq : q ≫ q = q)
    (hc : q ≫ σ.idem = σ.idem ≫ q) :
    (⟨Q, q, hq⟩ : Karoubi V) ≅ (⟨σ.E, σ.partE q, SplitKar.idem_E σ hq hc⟩ : Karoubi V) ⊞
      ⟨σ.U, σ.partU q, SplitKar.idem_U σ hq hc⟩ :=
  karoubiIsoOfKarIso hq _ (karIso_sum_of_comm σ hq hc) ≪≫
    karoubiBiconeIso σ.bicone (SplitKar.idem_E σ hq hc) (SplitKar.idem_U σ hq hc)

open ZeroObject in
/-- **`stablyIso_of_eq_U`** (review fix G1): two idempotents commuting with a splitting, with the
same `U`-part and stably zero `E`-parts, are stably isomorphic. -/
theorem stablyIso_of_eq_U {Q : V} (σ : Splitting Q) {q q' : Q ⟶ Q} (hq : q ≫ q = q)
    (hq' : q' ≫ q' = q') (hc : q ≫ σ.idem = σ.idem ≫ q) (hc' : q' ≫ σ.idem = σ.idem ≫ q')
    (hU : σ.partU q = σ.partU q')
    (hE : StablyIso (⟨σ.E, σ.partE q, SplitKar.idem_E σ hq hc⟩ : Karoubi V) 0)
    (hE' : StablyIso (⟨σ.E, σ.partE q', SplitKar.idem_E σ hq' hc'⟩ : Karoubi V) 0) :
    StablyIso (⟨Q, q, hq⟩ : Karoubi V) ⟨Q, q', hq'⟩ := by
  have h₁ := (StablyIso.of_iso (karoubiIsoSumOfComm σ hq hc)).trans
    ((hE.biprod_right _).trans (StablyIso.zero_biprod _))
  have h₂ := (StablyIso.of_iso (karoubiIsoSumOfComm σ hq' hc')).trans
    ((hE'.biprod_right _).trans (StablyIso.zero_biprod _))
  have hUU : (⟨σ.U, σ.partU q, SplitKar.idem_U σ hq hc⟩ : Karoubi V) =
      ⟨σ.U, σ.partU q', SplitKar.idem_U σ hq' hc'⟩ := by
    simp only [hU]
  rw [hUU] at h₁
  exact h₁.trans h₂.symm

/-- The image of a splitting under an additive functor. -/
@[simps]
def _root_.HSFormal.Splitting.map {W : Type*} [Category W] [Preadditive W] (F : V ⥤ W) [F.Additive] {Q : V}
    (σ : Splitting Q) : Splitting (F.obj Q) where
  E := F.obj σ.E
  U := F.obj σ.U
  ιE := F.map σ.ιE
  πE := F.map σ.πE
  ιU := F.map σ.ιU
  πU := F.map σ.πU
  ιE_πE := by rw [← F.map_comp, σ.ιE_πE, F.map_id]
  ιU_πU := by rw [← F.map_comp, σ.ιU_πU, F.map_id]
  ιE_πU := by rw [← F.map_comp, σ.ιE_πU, F.map_zero]
  ιU_πE := by rw [← F.map_comp, σ.ιU_πE, F.map_zero]
  total := by rw [← F.map_comp, ← F.map_comp, ← F.map_add, σ.total, F.map_id]

omit [HasFiniteBiproducts V] in
lemma _root_.HSFormal.Splitting.map_idem {W : Type*} [Category W] [Preadditive W] (F : V ⥤ W) [F.Additive]
    {Q : V} (σ : Splitting Q) : (σ.map F).idem = F.map σ.idem := by
  rw [Splitting.idem, Splitting.idem, F.map_comp]; rfl

end Splitting

/-! ### `2 × 2` matrices over a bicone -/

section Matrix

variable {V : Type u} [Category.{v} V] [Preadditive V] {T : V} (b : BinaryBicone T T)

/-- The projections of a bicone on `T ⊕ T`, indexed by `Fin 2`. -/
def bproj : Fin 2 → (b.pt ⟶ T) := ![b.fst, b.snd]

/-- The inclusions of a bicone on `T ⊕ T`, indexed by `Fin 2`. -/
def binc : Fin 2 → (T ⟶ b.pt) := ![b.inl, b.inr]

lemma binc_bproj (i j : Fin 2) :
    binc b i ≫ bproj b j = if i = j then 𝟙 T else 0 := by
  fin_cases i <;> fin_cases j <;> simp [binc, bproj]

/-- The endomorphism of `b.pt = T ⊕ T` with matrix `m` (operator convention: `m i j` maps the
`j`-th summand to the `i`-th; products in `End` are `x * y = y ≫ x`). -/
def mat (m : Matrix (Fin 2) (Fin 2) (End T)) : End b.pt :=
  ∑ i, ∑ j, bproj b j ≫ m i j ≫ binc b i

omit [Preadditive V] in
lemma end_mul_eq {X : V} (x y : End X) : x * y = y ≫ x := rfl

lemma end_add_comp {X Z : V} (x y : End X) (g : X ⟶ Z) : (x + y) ≫ g = x ≫ g + y ≫ g :=
  Preadditive.add_comp _ _ _ _ _ _

lemma comp_end_add {X Z : V} (g : Z ⟶ X) (x y : End X) : g ≫ (x + y) = g ≫ x + g ≫ y :=
  Preadditive.comp_add _ _ _ _ _ _

lemma end_neg_comp {X Z : V} (x : End X) (g : X ⟶ Z) : (-x) ≫ g = -(x ≫ g) :=
  Preadditive.neg_comp _ _

lemma comp_end_neg {X Z : V} (g : Z ⟶ X) (x : End X) : g ≫ (-x) = -(g ≫ x) :=
  Preadditive.comp_neg _ _

lemma end_sub_comp {X Z : V} (x y : End X) (g : X ⟶ Z) : (x - y) ≫ g = x ≫ g - y ≫ g :=
  Preadditive.sub_comp _ _ _

lemma comp_end_sub {X Z : V} (g : Z ⟶ X) (x y : End X) : g ≫ (x - y) = g ≫ x - g ≫ y :=
  Preadditive.comp_sub _ _ _

lemma end_zero_comp {X Z : V} (g : X ⟶ Z) : (0 : End X) ≫ g = 0 := zero_comp

lemma comp_end_zero {X Z : V} (g : Z ⟶ X) : g ≫ (0 : End X) = 0 := comp_zero

lemma mat_add (m n : Matrix (Fin 2) (Fin 2) (End T)) : mat b (m + n) = mat b m + mat b n := by
  simp only [mat, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by
    rw [end_add_comp, comp_add]

lemma mat_zero : mat b 0 = 0 := by
  simp only [mat, Matrix.zero_apply]
  exact Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun j _ ↦ by
    rw [end_zero_comp, comp_zero]

lemma mat_mul (m n : Matrix (Fin 2) (Fin 2) (End T)) : mat b (m * n) = mat b m * mat b n := by
  rw [end_mul_eq]
  simp only [mat, Fin.sum_univ_two, Matrix.mul_apply, end_mul_eq, end_add_comp, comp_end_add,
    comp_add, assoc, bproj, binc, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, BinaryBicone.inl_fst_assoc, BinaryBicone.inl_snd_assoc,
    BinaryBicone.inr_fst_assoc, BinaryBicone.inr_snd_assoc, zero_comp, comp_zero, add_zero,
    zero_add]
  abel

lemma mat_one (hb : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.pt) : mat b 1 = 1 := by
  rw [Matrix.one_fin_two]
  simp only [mat, Fin.sum_univ_two, bproj, binc, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    end_zero_comp, comp_zero, add_zero, zero_add, End.one_def, id_comp]
  exact hb

/-- `mat` as a ring hom `M₂(End T) →+* End (T ⊕ T)`. -/
def matHom (hb : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.pt) :
    Matrix (Fin 2) (Fin 2) (End T) →+* End b.pt where
  toFun := mat b
  map_one' := mat_one b hb
  map_mul' := mat_mul b
  map_zero' := mat_zero b
  map_add' := mat_add b

lemma mat_fin_two (a₁₁ a₁₂ a₂₁ a₂₂ : End T) :
    mat b !![a₁₁, a₁₂; a₂₁, a₂₂] = b.fst ≫ a₁₁ ≫ b.inl + b.snd ≫ a₁₂ ≫ b.inl +
      (b.fst ≫ a₂₁ ≫ b.inr + b.snd ≫ a₂₂ ≫ b.inr) := by
  simp only [mat, Fin.sum_univ_two, bproj, binc, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]

lemma mat_diag (p q : End T) :
    mat b !![p, 0; 0, q] = b.fst ≫ p ≫ b.inl + b.snd ≫ q ≫ b.inr := by
  rw [mat_fin_two, end_zero_comp, end_zero_comp, comp_zero, comp_zero, add_zero, zero_add]

end Matrix

/-! ### The Whitehead matrix -/

section Whitehead

variable {R : Type*} [Ring R]

/-- The Whitehead matrix `E₁₂(u) E₂₁(-v) E₁₂(u) R = [[2u - uvu, uv - 1], [1 - vu, v]]`. -/
def whitehead (u v : R) : Matrix (Fin 2) (Fin 2) R := !![2 * u - u * v * u, u * v - 1; 1 - v * u, v]

/-- Its inverse `[[v, 1 - vu], [uv - 1, 2u - uvu]]`. -/
def whiteheadInv (u v : R) : Matrix (Fin 2) (Fin 2) R :=
  !![v, 1 - v * u; u * v - 1, 2 * u - u * v * u]

lemma whitehead_mul_inv (u v : R) : whitehead u v * whiteheadInv u v = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [whitehead, whiteheadInv, Matrix.mul_apply, Fin.sum_univ_two] <;> noncomm_ring

lemma whitehead_inv_mul (u v : R) : whiteheadInv u v * whitehead u v = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [whitehead, whiteheadInv, Matrix.mul_apply, Fin.sum_univ_two] <;> noncomm_ring

omit [Ring R] in
lemma fin_two_congr {S : Type*} {a b c d a' b' c' d' : S} (h₁ : a = a') (h₂ : b = b')
    (h₃ : c = c') (h₄ : d = d') : !![a, b; c, d] = !![a', b'; c', d'] := by
  rw [h₁, h₂, h₃, h₄]

lemma fin_two_sub (a b c d a' b' c' d' : R) :
    !![a, b; c, d] - !![a', b'; c', d'] = !![a - a', b - b'; c - c', d - d'] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

variable {p₁ p₂ : R} (hp₁ : p₁ * p₁ = p₁) (hp₂ : p₂ * p₂ = p₂)

include hp₁ hp₂ in
/-- **The Whitehead identity** (`blueprint/negK-high.md` §3.2, step 2): with `u = p₁p₂`,
`v = p₂p₁`, `w·diag(p₂, 1 - p₁) - diag(1, 0)·w = [[0, p₁dp₁], [-p₂dp₂, 0]]`, `d = p₁ - p₂`. -/
lemma whitehead_mul_diag_sub :
    whitehead (p₁ * p₂) (p₂ * p₁) * !![p₂, 0; 0, 1 - p₁] -
      !![1, 0; 0, 0] * whitehead (p₁ * p₂) (p₂ * p₁) =
      !![0, p₁ * (p₁ - p₂) * p₁; -(p₂ * (p₁ - p₂) * p₂), 0] := by
  have h₁ : ∀ x, p₁ * (p₁ * x) = p₁ * x := fun x ↦ by rw [← mul_assoc, hp₁]
  have h₂ : ∀ x, p₂ * (p₂ * x) = p₂ * x := fun x ↦ by rw [← mul_assoc, hp₂]
  rw [whitehead, Matrix.mul_fin_two, Matrix.mul_fin_two, fin_two_sub]
  refine fin_two_congr ?_ ?_ ?_ ?_ <;>
    simp only [mul_sub, sub_mul, mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add,
      mul_assoc, two_mul, add_mul, mul_add, hp₁, hp₂, h₁, h₂, neg_sub, sub_self, sub_zero]
  all_goals abel

end Whitehead

/-! ### The germ lemma in `L^l(C_ℤ Y)` -/

lemma karoubi_congr {V : Type u} [Category.{v} V] {X : V} {p p' : X ⟶ X} (h : p = p')
    (hp : p ≫ p = p) (hp' : p' ≫ p' = p') : (⟨X, p, hp⟩ : Karoubi V) = ⟨X, p', hp'⟩ := by
  subst h; rfl

namespace CZ.Lpow

variable {Y : InvCat} {l : ℕ}

/-- The pointwise bicone `T ⊕ T` in `C_ℤ Y` (all structure maps diagonal). -/
abbrev baseBicone (T : Y.cz) : BinaryBicone T T :=
  CZ.biconeOf fun v ↦ BinaryBiproduct.bicone (T.obj v) (T.obj v)

lemma baseBicone_total (T : Y.cz) :
    (baseBicone T).fst ≫ (baseBicone T).inl + (baseBicone T).snd ≫ (baseBicone T).inr = 𝟙 _ :=
  IsBilimit.binary_total (CZ.biconeOfIsBilimit fun _ ↦ BinaryBiproduct.isBilimit _ _)

/-- Cuts of the pointwise sum are the sums of the cuts. -/
lemma cut_baseBicone (T : Y.cz) (p : ℤ → Prop) [DecidablePred p] :
    (CZ.cut (baseBicone T).pt p).idem = (baseBicone T).fst ≫ (CZ.cut T p).idem ≫
      (baseBicone T).inl + (baseBicone T).snd ≫ (CZ.cut T p).idem ≫ (baseBicone T).inr := by
  rw [CZ.cut_idem, CZ.cut_idem, CZ.biconeOf_fst, CZ.biconeOf_inl, CZ.biconeOf_snd,
    CZ.biconeOf_inr]
  erw [CZ.diag_comp_diag, CZ.diag_comp_diag, CZ.diag_comp_diag, CZ.diag_comp_diag,
    ← CZ.diag_add]
  refine CZ.diag_ext fun v ↦ ?_
  by_cases hv : p v
  · rw [ite_eq_left hv, ite_eq_left hv]
    change 𝟙 (T.obj v ⊞ T.obj v) = biprod.fst ≫ 𝟙 _ ≫ biprod.inl + biprod.snd ≫ 𝟙 _ ≫ biprod.inr
    rw [id_comp, id_comp]
    exact biprod.total.symm
  · rw [ite_eq_right hv, ite_eq_right hv]
    change (0 : T.obj v ⊞ T.obj v ⟶ _) = biprod.fst ≫ 0 ≫ biprod.inl + biprod.snd ≫ 0 ≫ biprod.inr
    rw [zero_comp, comp_zero, zero_comp, comp_zero]
    exact (add_zero _).symm

/-- The bicone `T ⊕ T` in `L^l(C_ℤ Y)`: the degree-`0` image of the pointwise one. -/
abbrev lBicone (T : Lpow l (Y.cz : AddCat)) : BinaryBicone T T where
  pt := (baseBicone T).pt
  fst := (Lpow.incl (Y.cz : AddCat) l).map (baseBicone T).fst
  snd := (Lpow.incl (Y.cz : AddCat) l).map (baseBicone T).snd
  inl := (Lpow.incl (Y.cz : AddCat) l).map (baseBicone T).inl
  inr := (Lpow.incl (Y.cz : AddCat) l).map (baseBicone T).inr
  inl_fst := by rw [← Functor.map_comp, BinaryBicone.inl_fst]; exact CategoryTheory.Functor.map_id _ _
  inl_snd := by rw [← Functor.map_comp, BinaryBicone.inl_snd]; exact CategoryTheory.Functor.map_zero _ _ _
  inr_fst := by rw [← Functor.map_comp, BinaryBicone.inr_fst]; exact CategoryTheory.Functor.map_zero _ _ _
  inr_snd := by rw [← Functor.map_comp, BinaryBicone.inr_snd]; exact CategoryTheory.Functor.map_id _ _

lemma lBicone_total (T : Lpow l (Y.cz : AddCat)) :
    (lBicone T).fst ≫ (lBicone T).inl + (lBicone T).snd ≫ (lBicone T).inr = 𝟙 _ := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_add, baseBicone_total]
  exact CategoryTheory.Functor.map_id _ _

lemma chi_lBicone (T : Lpow l (Y.cz : AddCat)) (p : ℤ → Prop) [DecidablePred p] :
    chi (lBicone T).pt p = mat (lBicone T) !![chi T p, 0; 0, chi T p] := by
  rw [mat_diag, chi, chi, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
    ← Functor.map_comp, ← Functor.map_add, ← cut_baseBicone]

/-- A matrix with entries supported in `p × p` gives a map supported in `p × p`. -/
lemma suppIn_mat {T : Lpow l (Y.cz : AddCat)} {p : ℤ → Prop} [DecidablePred p]
    {m : Matrix (Fin 2) (Fin 2) (End T)} (hm : ∀ i j, SuppIn p (m i j)) :
    SuppIn p (mat (lBicone T) m) := by
  let χ : End T := chi T p
  have hχ : ∀ i j, χ * m i j * χ = m i j := fun i j ↦ hm i j
  have hm' : !![χ, 0; 0, χ] * m * !![χ, 0; 0, χ] = m := by
    rw [Matrix.eta_fin_two m, Matrix.mul_fin_two, Matrix.mul_fin_two]
    refine fin_two_congr ?_ ?_ ?_ ?_ <;> simpa using hχ _ _
  change chi _ p ≫ mat (lBicone T) m ≫ chi _ p = _
  rw [chi_lBicone]
  have h := congrArg (mat (lBicone T)) hm'
  rw [mat_mul, mat_mul] at h
  exact h

variable {T : Lpow l (Y.cz : AddCat)} {P₁ P₂ : End T} (h₁ : P₁ ≫ P₁ = P₁) (h₂ : P₂ ≫ P₂ = P₂)

/-- The matrix `Δ = [[0, P₁dP₁], [-P₂dP₂, 0]]`, `d = P₁ - P₂`. -/
def deltaMat (P₁ P₂ : End T) : Matrix (Fin 2) (Fin 2) (End T) :=
  !![0, P₁ * (P₁ - P₂) * P₁; -(P₂ * (P₁ - P₂) * P₂), 0]

open ZeroObject in
include h₁ h₂ in
/-- **Germ lemma, core**: if all entries of `Δ w⁻¹` are supported in `p × p` and every Kar object
on the cut `(T ⊕ T)|_p` is stably zero, then `(T, P₁) ∼ (T, P₂)`. -/
theorem germ_core (p : ℤ → Prop) [DecidablePred p]
    (hsupp : ∀ i j, SuppIn p ((deltaMat P₁ P₂ * whiteheadInv (P₁ * P₂) (P₂ * P₁)) i j))
    (habs : ∀ (e : (Lpow l (Y.cz : AddCat)).Mor (CZ.cut (baseBicone T).pt p).E
      (CZ.cut (baseBicone T).pt p).E) (he : e ≫ e = e),
      StablyIso (⟨_, e, he⟩ : Karoubi (Lpow l (Y.cz : AddCat)).carrier) 0) :
    StablyIso (⟨T, P₁, h₁⟩ : Karoubi (Lpow l (Y.cz : AddCat)).carrier) ⟨T, P₂, h₂⟩ := by
  -- the ring-level data
  have hp₁ : P₁ * P₁ = P₁ := h₁
  have hp₂ : P₂ * P₂ = P₂ := h₂
  set W := whitehead (P₁ * P₂) (P₂ * P₁) with hW
  set Wi := whiteheadInv (P₁ * P₂) (P₂ * P₁) with hWi
  set D₂ : Matrix (Fin 2) (Fin 2) (End T) := !![P₂, 0; 0, 1 - P₁] with hD₂
  set E₀ : Matrix (Fin 2) (Fin 2) (End T) := !![1, 0; 0, 0] with hE₀
  have hWWi : W * Wi = 1 := whitehead_mul_inv _ _
  have hWiW : Wi * W = 1 := whitehead_inv_mul _ _
  have hD₂D₂ : D₂ * D₂ = D₂ := by
    rw [hD₂, Matrix.mul_fin_two]
    refine fin_two_congr ?_ ?_ ?_ ?_ <;> simp [hp₂, mul_sub, sub_mul, hp₁]
  have hE₀E₀ : E₀ * E₀ = E₀ := by
    rw [hE₀, Matrix.mul_fin_two]
    refine fin_two_congr ?_ ?_ ?_ ?_ <;> simp
  have hEE : (W * D₂ * Wi) * (W * D₂ * Wi) = W * D₂ * Wi := by
    calc (W * D₂ * Wi) * (W * D₂ * Wi) = W * D₂ * (Wi * W) * D₂ * Wi := by noncomm_ring
      _ = W * D₂ * Wi := by rw [hWiW, mul_one, mul_assoc W D₂ D₂, hD₂D₂]
  have hsub : W * D₂ * Wi - E₀ = deltaMat P₁ P₂ * Wi := by
    have := whitehead_mul_diag_sub hp₁ hp₂
    rw [← hW, ← hD₂, ← hE₀] at this
    rw [deltaMat, ← this, sub_mul, mul_assoc E₀, hWWi, mul_one]
  -- transport to `End (T ⊕ T)`
  set b := lBicone T with hb
  let φ := matHom b (lBicone_total T)
  have hφ : ∀ m, φ m = mat b m := fun _ ↦ rfl
  set e := φ (W * D₂ * Wi) with he_def
  set e₀ := φ E₀ with he₀_def
  set g := φ (deltaMat P₁ P₂ * Wi) with hg_def
  have he : e ≫ e = e := by
    change e * e = e; rw [he_def, ← map_mul, hEE]
  have he₀ : e₀ ≫ e₀ = e₀ := by
    change e₀ * e₀ = e₀; rw [he₀_def, ← map_mul, hE₀E₀]
  have heg : e = e₀ + g := by
    rw [he_def, he₀_def, hg_def, ← map_add, ← hsub, add_sub_cancel]
  have hg : SuppIn p g := suppIn_mat hsupp
  -- the cut of `T ⊕ T`
  let σ := (CZ.cut (baseBicone T).pt p).map (Lpow.incl (Y.cz : AddCat) l)
  have hσ : σ.idem = chi b.pt p := by
    rw [Splitting.map_idem]; rfl
  have hχE₀ : e₀ ≫ chi b.pt p = chi b.pt p ≫ e₀ := by
    rw [chi_lBicone, he₀_def, hφ, ← end_mul_eq, ← end_mul_eq, ← mat_mul, ← mat_mul, hE₀,
      Matrix.mul_fin_two, Matrix.mul_fin_two]
    congr 1
    refine fin_two_congr ?_ ?_ ?_ ?_ <;> simp
  have hcomm : e ≫ σ.idem = σ.idem ≫ e := by
    rw [hσ, heg, add_comp, comp_add, hχE₀, hg.comp_chi, hg.chi_comp]
  have hcomm₀ : e₀ ≫ σ.idem = σ.idem ≫ e₀ := by rw [hσ, hχE₀]
  have hU : σ.partU e = σ.partU e₀ := by
    have h0 : σ.ιU ≫ g = 0 := by
      rw [← hg.chi_comp, ← hσ, Splitting.idem]
      simp only [← assoc, σ.ιU_πE, zero_comp]
    simp only [Splitting.partU]
    rw [heg, add_comp, comp_add, reassoc_of% h0, zero_comp, add_zero]
  have hEU := stablyIso_of_eq_U σ he he₀ hcomm hcomm₀ hU (habs _ _) (habs _ _)
  -- `(T ⊕ T, e) ≅ (T, P₂) ⊞ (T, 1 - P₁)`
  have hq : ((1 : End T) - P₁) ≫ ((1 : End T) - P₁) = (1 : End T) - P₁ := by
    change (1 - P₁) * (1 - P₁) = 1 - P₁
    rw [mul_sub, sub_mul, sub_mul, hp₁, one_mul, mul_one, one_mul, sub_self, sub_zero]
  have hD₂mat : φ D₂ = b.fst ≫ P₂ ≫ b.inl + b.snd ≫ (1 - P₁) ≫ b.inr := mat_diag b P₂ (1 - P₁)
  have hD₂idem : φ D₂ ≫ φ D₂ = φ D₂ := by
    change φ D₂ * φ D₂ = φ D₂; rw [← map_mul, hD₂D₂]
  have hiso₁ : StablyIso (⟨b.pt, e, he⟩ : Karoubi (Lpow l (Y.cz : AddCat)).carrier)
      ⟨b.pt, φ D₂, hD₂idem⟩ := by
    refine StablyIso.of_karIso he hD₂idem (CZ.karIsoOfFactor he hD₂idem (φ (D₂ * Wi))
      (φ (W * D₂)) ?_ ?_)
    · change φ (W * D₂) * φ (D₂ * Wi) = e
      rw [← map_mul, he_def]; congr 1
      calc W * D₂ * (D₂ * Wi) = W * (D₂ * D₂) * Wi := by noncomm_ring
        _ = W * D₂ * Wi := by rw [hD₂D₂]
    · change φ (D₂ * Wi) * φ (W * D₂) = φ D₂
      rw [← map_mul]; congr 1
      calc D₂ * Wi * (W * D₂) = D₂ * (Wi * W) * D₂ := by noncomm_ring
        _ = D₂ := by rw [hWiW, mul_one, hD₂D₂]
  have hiso₂ : StablyIso (⟨b.pt, φ D₂, hD₂idem⟩ : Karoubi (Lpow l (Y.cz : AddCat)).carrier)
      ((⟨T, P₂, h₂⟩ : Karoubi _) ⊞ (⟨T, P₁, h₁⟩ : Karoubi _).complement) := by
    rw [karoubi_congr hD₂mat hD₂idem (bicone_idem b h₂ hq)]
    exact StablyIso.of_iso (karoubiBiconeIso b h₂ hq)
  -- `(T ⊕ T, e₀) ∼ 0`
  have h1 : (1 : End T) ≫ (1 : End T) = (1 : End T) := by
    change (1 : End T) * 1 = 1; rw [mul_one]
  have h0 : (0 : End T) ≫ (0 : End T) = (0 : End T) := by
    change (0 : End T) * 0 = 0; rw [mul_zero]
  have hE₀mat : e₀ = b.fst ≫ (1 : End T) ≫ b.inl + b.snd ≫ (0 : End T) ≫ b.inr :=
    mat_diag b 1 0
  have hzero : StablyIso (⟨b.pt, e₀, he₀⟩ : Karoubi (Lpow l (Y.cz : AddCat)).carrier) 0 := by
    rw [karoubi_congr hE₀mat he₀ (bicone_idem b h1 h0)]
    refine (StablyIso.of_iso (karoubiBiconeIso b h1 h0)).trans ?_
    have hfree : StablyIso (⟨T, (1 : End T), h1⟩ : Karoubi (Lpow l (Y.cz : AddCat)).carrier) 0 :=
      toKaroubi_stablyIso_zero T
    have hz : StablyIso (⟨T, (0 : End T), h0⟩ : Karoubi (Lpow l (Y.cz : AddCat)).carrier) 0 :=
      StablyIso.of_isZero (by
        rw [IsZero.iff_id_eq_zero]; ext; exact rfl) (isZero_zero _)
    exact (hfree.biprod hz).trans (StablyIso.zero_biprod 0)
  -- conclude by cancelling the complement
  have key : StablyIso ((⟨T, P₂, h₂⟩ : Karoubi _) ⊞ (⟨T, P₁, h₁⟩ : Karoubi _).complement) 0 :=
    (hiso₂.symm.trans hiso₁.symm).trans (hEU.trans hzero)
  exact (StablyIso.of_biprod_complement key).symm

omit h₁ h₂ in
lemma LeftSupp.mul_right {x : End T} (hx : LeftSupp x) (y : End T) : LeftSupp (x * y) :=
  hx.comp_left y

omit h₁ h₂ in
lemma LeftSupp.mul_left (y : End T) {x : End T} (hx : LeftSupp x) : LeftSupp (y * x) :=
  hx.comp_right y

omit h₁ h₂ in
lemma RightSupp.mul_right {x : End T} (hx : RightSupp x) (y : End T) : RightSupp (x * y) :=
  hx.comp_left y

omit h₁ h₂ in
lemma RightSupp.mul_left (y : End T) {x : End T} (hx : RightSupp x) : RightSupp (y * x) :=
  hx.comp_right y

omit h₁ h₂ in
lemma leftSupp_deltaMat_mul (hD : LeftSupp (P₁ - P₂)) (M : Matrix (Fin 2) (Fin 2) (End T))
    (i j : Fin 2) : LeftSupp ((deltaMat P₁ P₂ * M) i j) := by
  have hΔ : ∀ i k, LeftSupp (deltaMat P₁ P₂ i k) := by
    intro i k
    fin_cases i <;> fin_cases k
    · exact LeftSupp.zero
    · exact (LeftSupp.mul_left P₁ hD).mul_right P₁
    · exact ((LeftSupp.mul_left P₂ hD).mul_right P₂).neg
    · exact LeftSupp.zero
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact ((hΔ i 0).mul_right _).add ((hΔ i 1).mul_right _)

omit h₁ h₂ in
lemma rightSupp_deltaMat_mul (hD : RightSupp (P₁ - P₂)) (M : Matrix (Fin 2) (Fin 2) (End T))
    (i j : Fin 2) : RightSupp ((deltaMat P₁ P₂ * M) i j) := by
  have hΔ : ∀ i k, RightSupp (deltaMat P₁ P₂ i k) := by
    intro i k
    fin_cases i <;> fin_cases k
    · exact RightSupp.zero
    · exact (RightSupp.mul_left P₁ hD).mul_right P₁
    · exact ((RightSupp.mul_left P₂ hD).mul_right P₂).neg
    · exact RightSupp.zero
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact ((hΔ i 0).mul_right _).add ((hΔ i 1).mul_right _)

end CZ.Lpow

namespace CZ.Lpow

variable {Y : InvCat} {l : ℕ}

/-- **Lemma G (germ lemma, left)** (`blueprint/negK-high.md` §3.2): idempotents `P₁, P₂` on `T`
in `L^l(C_ℤ Y)` whose difference is left-supported define stably isomorphic Kar objects. -/
theorem germ_left {T : Lpow l (Y.cz : AddCat)} {P₁ P₂ : (Lpow l (Y.cz : AddCat)).Mor T T}
    (h₁ : P₁ ≫ P₁ = P₁) (h₂ : P₂ ≫ P₂ = P₂) (hD : LeftSupp (P₁ - P₂)) :
    StablyIso (⟨T, P₁, h₁⟩ : Karoubi (Lpow l (Y.cz : AddCat)).carrier) ⟨T, P₂, h₂⟩ := by
  let Q₁ : End T := P₁
  let Q₂ : End T := P₂
  have hent := leftSupp_deltaMat_mul (P₁ := Q₁) (P₂ := Q₂) hD (whiteheadInv (Q₁ * Q₂) (Q₂ * Q₁))
  obtain ⟨c, hc⟩ : ∃ c : ℤ, ∀ i j, SuppIn (· ≤ c)
      ((deltaMat Q₁ Q₂ * whiteheadInv (Q₁ * Q₂) (Q₂ * Q₁)) i j) := by
    obtain ⟨c₀₀, h₀₀⟩ := hent 0 0
    obtain ⟨c₀₁, h₀₁⟩ := hent 0 1
    obtain ⟨c₁₀, h₁₀⟩ := hent 1 0
    obtain ⟨c₁₁, h₁₁⟩ := hent 1 1
    refine ⟨max (max c₀₀ c₀₁) (max c₁₀ c₁₁), fun i j ↦ ?_⟩
    fin_cases i <;> fin_cases j
    · exact h₀₀.mono fun v hv ↦ hv.trans ((le_max_left _ _).trans (le_max_left _ _))
    · exact h₀₁.mono fun v hv ↦ hv.trans ((le_max_right _ _).trans (le_max_left _ _))
    · exact h₁₀.mono fun v hv ↦ hv.trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact h₁₁.mono fun v hv ↦ hv.trans ((le_max_right _ _).trans (le_max_right _ _))
  refine germ_core (P₁ := Q₁) (P₂ := Q₂) h₁ h₂ (· ≤ c) hc fun e he ↦ ?_
  obtain ⟨F, hF⟩ := karAbsorbs_lpow_of_negHalf l (M := (CZ.cut (baseBicone T).pt (· ≤ c)).E)
    ⟨c, fun v hv ↦ CZ.isZero_cut_E _ _ (by omega)⟩ he
  exact StablyIso.of_karAbsorbs (P := ⟨_, e, he⟩) hF

/-- **Lemma G (germ lemma, right)**: idempotents `P₁, P₂` on `T` in `L^l(C_ℤ Y)` whose difference
is right-supported define stably isomorphic Kar objects. -/
theorem germ_right {T : Lpow l (Y.cz : AddCat)} {P₁ P₂ : (Lpow l (Y.cz : AddCat)).Mor T T}
    (h₁ : P₁ ≫ P₁ = P₁) (h₂ : P₂ ≫ P₂ = P₂) (hD : RightSupp (P₁ - P₂)) :
    StablyIso (⟨T, P₁, h₁⟩ : Karoubi (Lpow l (Y.cz : AddCat)).carrier) ⟨T, P₂, h₂⟩ := by
  let Q₁ : End T := P₁
  let Q₂ : End T := P₂
  have hent := rightSupp_deltaMat_mul (P₁ := Q₁) (P₂ := Q₂) hD (whiteheadInv (Q₁ * Q₂) (Q₂ * Q₁))
  obtain ⟨c, hc⟩ : ∃ c : ℤ, ∀ i j, SuppIn (c ≤ ·)
      ((deltaMat Q₁ Q₂ * whiteheadInv (Q₁ * Q₂) (Q₂ * Q₁)) i j) := by
    obtain ⟨c₀₀, h₀₀⟩ := hent 0 0
    obtain ⟨c₀₁, h₀₁⟩ := hent 0 1
    obtain ⟨c₁₀, h₁₀⟩ := hent 1 0
    obtain ⟨c₁₁, h₁₁⟩ := hent 1 1
    refine ⟨min (min c₀₀ c₀₁) (min c₁₀ c₁₁), fun i j ↦ ?_⟩
    fin_cases i <;> fin_cases j
    · exact h₀₀.mono fun v hv ↦ ((min_le_left _ _).trans (min_le_left _ _)).trans hv
    · exact h₀₁.mono fun v hv ↦ ((min_le_left _ _).trans (min_le_right _ _)).trans hv
    · exact h₁₀.mono fun v hv ↦ ((min_le_right _ _).trans (min_le_left _ _)).trans hv
    · exact h₁₁.mono fun v hv ↦ ((min_le_right _ _).trans (min_le_right _ _)).trans hv
  refine germ_core (P₁ := Q₁) (P₂ := Q₂) h₁ h₂ (c ≤ ·) hc fun e he ↦ ?_
  obtain ⟨F, hF⟩ := karAbsorbs_lpow_of_posHalf l (M := (CZ.cut (baseBicone T).pt (c ≤ ·)).E)
    ⟨c, fun v hv ↦ CZ.isZero_cut_E _ _ (by omega)⟩ he
  exact StablyIso.of_karAbsorbs (P := ⟨_, e, he⟩) hF

/-! ### Lemma G′: different objects -/

/-- A Kar object transported along a retraction `i ≫ r = 𝟙`: `(T, r P i) ≅ (Z, P)`. -/
lemma stablyIso_retract {Z T : Lpow l (Y.cz : AddCat)} (i : (Lpow l (Y.cz : AddCat)).Mor Z T)
    (r : (Lpow l (Y.cz : AddCat)).Mor T Z) (hir : i ≫ r = 𝟙 Z)
    {P : (Lpow l (Y.cz : AddCat)).Mor Z Z} (hP : P ≫ P = P) (hQ : (r ≫ P ≫ i) ≫ (r ≫ P ≫ i) =
      r ≫ P ≫ i) :
    StablyIso (⟨T, r ≫ P ≫ i, hQ⟩ : Karoubi (Lpow l (Y.cz : AddCat)).carrier) ⟨Z, P, hP⟩ :=
  StablyIso.of_karIso hQ hP (CZ.karIsoOfFactor hQ hP (r ≫ P) (P ≫ i)
    (by simp only [assoc]; rw [reassoc_of% hP])
    (by simp only [assoc]; rw [reassoc_of% hir, hP]))

lemma retract_idem {Z T : Lpow l (Y.cz : AddCat)} (i : (Lpow l (Y.cz : AddCat)).Mor Z T)
    (r : (Lpow l (Y.cz : AddCat)).Mor T Z) (hir : i ≫ r = 𝟙 Z)
    {P : (Lpow l (Y.cz : AddCat)).Mor Z Z} (hP : P ≫ P = P) :
    (r ≫ P ≫ i) ≫ (r ≫ P ≫ i) = r ≫ P ≫ i := by
  simp only [assoc]; rw [reassoc_of% hir, reassoc_of% hP]

/-- **Lemma G′ (left)** (`blueprint/negK-high.md` §3.2): let `Z, Z'` be retracts of a common
object `T` (`i ≫ r = 𝟙`, `i' ≫ r' = 𝟙`), and `P, P'` idempotents on `Z, Z'` whose transports
`r P i`, `r' P' i'` to `T` differ by a left-supported map.  Then `(Z, P) ∼ (Z', P')`. -/
theorem germ_left' {Z Z' T : Lpow l (Y.cz : AddCat)} (i : (Lpow l (Y.cz : AddCat)).Mor Z T)
    (r : (Lpow l (Y.cz : AddCat)).Mor T Z) (hir : i ≫ r = 𝟙 Z)
    (i' : (Lpow l (Y.cz : AddCat)).Mor Z' T) (r' : (Lpow l (Y.cz : AddCat)).Mor T Z')
    (hir' : i' ≫ r' = 𝟙 Z') {P : (Lpow l (Y.cz : AddCat)).Mor Z Z}
    {P' : (Lpow l (Y.cz : AddCat)).Mor Z' Z'} (hP : P ≫ P = P) (hP' : P' ≫ P' = P')
    (hD : LeftSupp (r ≫ P ≫ i - r' ≫ P' ≫ i')) :
    StablyIso (⟨Z, P, hP⟩ : Karoubi (Lpow l (Y.cz : AddCat)).carrier) ⟨Z', P', hP'⟩ :=
  ((stablyIso_retract i r hir hP (retract_idem i r hir hP)).symm.trans
    (germ_left (retract_idem i r hir hP) (retract_idem i' r' hir' hP') hD)).trans
    (stablyIso_retract i' r' hir' hP' (retract_idem i' r' hir' hP'))

/-- **Lemma G′ (right)**: as `germ_left'`, with a right-supported difference. -/
theorem germ_right' {Z Z' T : Lpow l (Y.cz : AddCat)} (i : (Lpow l (Y.cz : AddCat)).Mor Z T)
    (r : (Lpow l (Y.cz : AddCat)).Mor T Z) (hir : i ≫ r = 𝟙 Z)
    (i' : (Lpow l (Y.cz : AddCat)).Mor Z' T) (r' : (Lpow l (Y.cz : AddCat)).Mor T Z')
    (hir' : i' ≫ r' = 𝟙 Z') {P : (Lpow l (Y.cz : AddCat)).Mor Z Z}
    {P' : (Lpow l (Y.cz : AddCat)).Mor Z' Z'} (hP : P ≫ P = P) (hP' : P' ≫ P' = P')
    (hD : RightSupp (r ≫ P ≫ i - r' ≫ P' ≫ i')) :
    StablyIso (⟨Z, P, hP⟩ : Karoubi (Lpow l (Y.cz : AddCat)).carrier) ⟨Z', P', hP'⟩ :=
  ((stablyIso_retract i r hir hP (retract_idem i r hir hP)).symm.trans
    (germ_right (retract_idem i r hir hP) (retract_idem i' r' hir' hP') hD)).trans
    (stablyIso_retract i' r' hir' hP' (retract_idem i' r' hir' hP'))

end CZ.Lpow

end

end HSFormal.LTheory
