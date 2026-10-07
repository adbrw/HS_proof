import HSFormal.LTheory.Model.NegK.High.Laurent
import HSFormal.LTheory.Model.NegK.High.RegMatrix
import HSFormal.LTheory.Model.NegK.High.StablyIso
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Theorem R, Karoubi form: fibrewise matrices (NegKHigh module N13, helper `RegKarFib`)

`blueprint/negK-high.md` §4 "Kar form (dictionary)".

A **fibrewise matrix representation** `FibMat D rank R` of a bundled additive category `D` sends
each morphism `f : X ⟶ Y` to matrices `mat f i : Matrix (Fin (rank X i)) (Fin (rank Y i)) (R i)`,
additively, with `f ≫ g ↦ mat f i * mat g i` (the `vecMul` convention of `FreeQGMat`), jointly
faithfully and fully, objects having finite support.

* `FibMat.laurent`: `Laurent D` has fibre matrices over `R i [T;T⁻¹]`
  (`coeff_lmat`: coefficients of the matrix entries are the matrices of the coefficients).
* `FibMat.lpow l`: `Lpow l D` has fibre matrices over `lpRing l (R i)` (same recursion, newest
  variable innermost), with the coefficient formula `lpCoeff_lpow_mat` (`lpCoeff` the coefficients
  of `lpRing`, `lpRing_ext`, `lpCoeff_lpRingMap`).
* `FibMat.pos`: `LaurentPos D` has fibre matrices over `R i [X]`, and **the faces functor**
  `ι⁺ = Lpow.map l (LaurentPos.incl D)` acts on fibre matrices by `lpRingMap l toLaurent`
  (`lpow_mat_incl`), i.e. by `faceMap` of `RegLocal`.
* `MatKarIso.split`: a Karoubi isomorphism `e ⊕ f ≅ g` of matrices in components.
* **`FibMat.exists_karoubi_iso`** (assembly): if the matrix form of Theorem R holds at every
  fibre (`hR`) and objects of smaller support can be formed (`hmk`), then every Kar object `E` of
  `L^{l+1} D` satisfies `E ⊞ ι⁺Q₁ ≅ ι⁺Q₀` in `Karoubi`, for Kar objects `Q₀, Q₁` of `L^l(L⁺ D)`.
  Fibres where `E` vanishes get `Q₀ = Q₁ = 0`, so `Q_j` have finite support inside that of `E`.
-/

namespace HSFormal.LTheory.Reg

open CategoryTheory Limits Preadditive

noncomputable section

universe w v u

/-- **Fibrewise matrix representation** of a bundled additive category `D`: every morphism
`f : X ⟶ Y` is a family of matrices `mat f i : Matrix (Fin (rank X i)) (Fin (rank Y i)) (R i)`,
additively, with composition `f ≫ g ↦ mat f i * mat g i` (the `vecMul` convention of
`FreeQGMat`), jointly faithfully and fully, and objects have finite support. -/
structure FibMat (D : AddCat.{v, u}) (rank : D.carrier → ℕ → ℕ) (R : ℕ → RingCat.{w}) where
  /-- The fibre matrices. -/
  mat : ∀ {X Y : D.carrier}, D.Mor X Y → ∀ i, Matrix (Fin (rank X i)) (Fin (rank Y i)) (R i)
  mat_add : ∀ {X Y : D.carrier} (f g : D.Mor X Y) (i : ℕ), mat (f + g) i = mat f i + mat g i
  mat_comp : ∀ {X Y Z : D.carrier} (f : D.Mor X Y) (g : D.Mor Y Z) (i : ℕ),
    mat (f ≫ g) i = mat f i * mat g i
  mat_id : ∀ (X : D.carrier) (i : ℕ), mat (D.idMor X) i = 1
  ext : ∀ {X Y : D.carrier} {f g : D.Mor X Y}, (∀ i, mat f i = mat g i) → f = g
  full : ∀ {X Y : D.carrier} (A : ∀ i, Matrix (Fin (rank X i)) (Fin (rank Y i)) (R i)),
    ∃ f : D.Mor X Y, ∀ i, mat f i = A i
  finite : ∀ X : D.carrier, {i | rank X i ≠ 0}.Finite

namespace FibMat

variable {D : AddCat.{v, u}} {rank : D.carrier → ℕ → ℕ} {R : ℕ → RingCat.{w}}
  (M : FibMat D rank R)

lemma mat_zero {X Y : D.carrier} (i : ℕ) : M.mat (0 : D.Mor X Y) i = 0 := by
  have h := M.mat_add (0 : D.Mor X Y) 0 i
  rw [add_zero] at h
  exact (left_eq_add.mp h)

/-- `mat` at fibre `i` as an additive map. -/
def matHom {X Y : D.carrier} (i : ℕ) :
    D.Mor X Y →+ Matrix (Fin (rank X i)) (Fin (rank Y i)) (R i) where
  toFun f := M.mat f i
  map_zero' := M.mat_zero i
  map_add' f g := M.mat_add f g i

lemma mat_sum {X Y : D.carrier} {ι : Type*} (s : Finset ι) (f : ι → D.Mor X Y) (i : ℕ) :
    M.mat (∑ j ∈ s, f j) i = ∑ j ∈ s, M.mat (f j) i :=
  map_sum (M.matHom (X := X) (Y := Y) i) f s

lemma mat_neg {X Y : D.carrier} (f : D.Mor X Y) (i : ℕ) : M.mat (-f) i = -M.mat f i :=
  map_neg (M.matHom (X := X) (Y := Y) i) f

lemma mat_sub {X Y : D.carrier} (f g : D.Mor X Y) (i : ℕ) :
    M.mat (f - g) i = M.mat f i - M.mat g i :=
  map_sub (M.matHom (X := X) (Y := Y) i) f g

lemma eq_zero_of_mat {X Y : D.carrier} {f : D.Mor X Y} (h : ∀ i, M.mat f i = 0) : f = 0 :=
  M.ext fun i ↦ by rw [h, M.mat_zero]

end FibMat

/-! ### The Laurent extension -/

namespace FibMat

open LaurentPolynomial

variable {D : AddCat.{v, u}} {rank : D.carrier → ℕ → ℕ} {R : ℕ → RingCat.{w}}
  (M : FibMat D rank R)

/-- The Laurent ring of the fibre ring. -/
abbrev lRing (R : ℕ → RingCat.{w}) (i : ℕ) : RingCat.{w} := RingCat.of (LaurentPolynomial (R i))

/-- The matrix of a Laurent morphism: `∑ₙ (mat (coeff n f)) Tⁿ`. -/
def lmat {X Y : D.carrier} (f : (Laurent D).Mor X Y) (i : ℕ) :
    Matrix (Fin (rank X i)) (Fin (rank Y i)) (lRing R i) :=
  (Laurent.toFinsupp f).sum fun n a ↦ (M.mat a i).map (fun r ↦ (AddMonoidAlgebra.single n r :
    LaurentPolynomial (R i)))

lemma lmat_add {X Y : D.carrier} (f g : (Laurent D).Mor X Y) (i : ℕ) :
    M.lmat (f + g) i = M.lmat f i + M.lmat g i := by
  unfold lmat
  rw [map_add]
  refine Finsupp.sum_add_index' (fun n ↦ ?_) (fun n a b ↦ ?_)
  · ext; simp [M.mat_zero]
  · ext
    simp only [M.mat_add, Matrix.map_apply, Matrix.add_apply, AddMonoidAlgebra.single_add]

lemma lmat_single {X Y : D.carrier} (n : ℤ) (a : D.Mor X Y) (i : ℕ) :
    M.lmat (Laurent.single n a) i =
      (M.mat a i).map (fun r ↦ (AddMonoidAlgebra.single n r : LaurentPolynomial (R i))) := by
  unfold lmat Laurent.single
  rw [AddEquiv.apply_symm_apply, Finsupp.sum_single_index]
  ext; simp [M.mat_zero]

lemma lmat_zero {X Y : D.carrier} (i : ℕ) : M.lmat (0 : (Laurent D).Mor X Y) i = 0 := by
  unfold lmat
  simp

lemma coeff_lmat {X Y : D.carrier} (f : (Laurent D).Mor X Y) (i : ℕ) (a : Fin (rank X i))
    (b : Fin (rank Y i)) (n : ℤ) :
    (M.lmat f i a b).coeff n = M.mat (Laurent.coeff n f) i a b := by
  induction f using Laurent.induction_linear with
  | zero => simp [lmat_zero, M.mat_zero]
  | add f g hf hg =>
    rw [lmat_add, Matrix.add_apply, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hf, hg,
      Laurent.coeff_add, M.mat_add, Matrix.add_apply]
  | single m c =>
    rw [lmat_single, Matrix.map_apply, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
      Laurent.coeff_single]
    split_ifs <;> simp [M.mat_zero]


lemma map_single_mul_map_single {S : Type w} [Ring S] {α β γ : Type*} [Fintype β]
    (A : Matrix α β S) (B : Matrix β γ S) (m n : ℤ) :
    A.map (fun r ↦ (AddMonoidAlgebra.single m r : LaurentPolynomial S)) *
      B.map (fun r ↦ (AddMonoidAlgebra.single n r : LaurentPolynomial S)) =
      (A * B).map (fun r ↦ (AddMonoidAlgebra.single (m + n) r : LaurentPolynomial S)) := by
  refine Matrix.ext fun x y ↦ ?_
  simp only [Matrix.mul_apply, Matrix.map_apply, AddMonoidAlgebra.single_mul_single]
  exact (map_sum (AddMonoidAlgebra.singleAddHom (R := S) (m + n)) _ _).symm

lemma lmat_comp {X Y Z : D.carrier} (f : (Laurent D).Mor X Y) (g : (Laurent D).Mor Y Z)
    (i : ℕ) : M.lmat (f ≫ g) i = M.lmat f i * M.lmat g i := by
  induction f using Laurent.induction_linear with
  | zero => rw [zero_comp, lmat_zero, lmat_zero, Matrix.zero_mul]
  | add f f' hf hf' => rw [add_comp, lmat_add, lmat_add, hf, hf', Matrix.add_mul]
  | single m a =>
    induction g using Laurent.induction_linear with
    | zero => rw [comp_zero, lmat_zero, lmat_zero, Matrix.mul_zero]
    | add g g' hg hg' => rw [comp_add, lmat_add, lmat_add, hg, hg', Matrix.mul_add]
    | single n b =>
      rw [Laurent.single_comp_single, lmat_single, lmat_single, lmat_single, M.mat_comp,
        map_single_mul_map_single]

lemma lmat_id (X : D.carrier) (i : ℕ) : M.lmat ((Laurent D).idMor X) i = 1 := by
  change M.lmat (Laurent.single 0 (D.idMor X)) i = 1
  rw [lmat_single, M.mat_id]
  exact Matrix.map_one _ (by simp) rfl

lemma lmat_ext {X Y : D.carrier} {f g : (Laurent D).Mor X Y} (h : ∀ i, M.lmat f i = M.lmat g i) :
    f = g :=
  Laurent.ext fun n ↦ M.ext fun i ↦ by
    ext a b
    rw [← coeff_lmat, ← coeff_lmat, h]

lemma lmat_full {X Y : D.carrier} (A : ∀ i, Matrix (Fin (rank X i)) (Fin (rank Y i)) (lRing R i)) :
    ∃ f : (Laurent D).Mor X Y, ∀ i, M.lmat f i = A i := by
  classical
  choose a ha using fun n : ℤ ↦ M.full (X := X) (Y := Y) fun i ↦ (A i).map fun p ↦ p.coeff n
  let I := (M.finite X).toFinset
  let N : Finset ℤ := I.biUnion fun i ↦ Finset.univ.biUnion fun x ↦ Finset.univ.biUnion
    fun y ↦ (A i x y).coeff.support
  refine ⟨∑ n ∈ N, Laurent.single n (a n), fun i ↦ ?_⟩
  ext x y m
  rw [coeff_lmat, Laurent.coeff_sum]
  simp only [Laurent.coeff_single]
  rw [Finset.sum_ite_eq']
  split_ifs with hm
  · rw [ha, Matrix.map_apply]
  · rw [M.mat_zero, Matrix.zero_apply]
    have hi : i ∈ I := by
      rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      intro h0
      exact absurd x.2 (by omega)
    symm
    by_contra hne
    exact hm (Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ _,
      Finset.mem_biUnion.mpr ⟨y, Finset.mem_univ _, Finsupp.mem_support_iff.mpr hne⟩⟩⟩)

/-- **The Laurent extension** of a fibrewise matrix representation: matrices over `R i [T;T⁻¹]`. -/
def laurent : FibMat (Laurent D) rank (lRing R) where
  mat f i := M.lmat f i
  mat_add f g i := M.lmat_add f g i
  mat_comp f g i := M.lmat_comp f g i
  mat_id X i := M.lmat_id X i
  ext h := M.lmat_ext h
  full A := M.lmat_full A
  finite := M.finite

lemma laurent_mat {X Y : D.carrier} (f : (Laurent D).Mor X Y) (i : ℕ) :
    M.laurent.mat f i = M.lmat f i := rfl


/-! ### Iterated Laurent extensions -/

/-- **The `l`-fold Laurent extension** of a fibrewise matrix representation: `Lpow l D` has
fibre matrices over `lpRing l (R i)` (both recursions put the newest variable innermost). -/
def lpow : ∀ (l : ℕ) {D : AddCat.{v, u}} {rank : D.carrier → ℕ → ℕ} {R : ℕ → RingCat.{w}},
    FibMat D rank R → FibMat (Lpow l D) rank (fun i ↦ lpRing l (R i))
  | 0, _, _, _, M => M
  | l + 1, _, _, _, M => lpow l M.laurent

end FibMat

/-- The coefficient `lpRing 1 R → R` of `Tⁿ`. -/
def laurentCoeffHom {S : Type w} [Ring S] (n : ℤ) : LaurentPolynomial S →+ S where
  toFun p := p.coeff n
  map_zero' := rfl
  map_add' _ _ := rfl

/-- **Coefficients in `lpRing l R`**, `γ : Fin l → ℤ` (`γ 0` the innermost variable): the
recursion of `Lpow.coeff`. -/
def lpCoeff : ∀ (l : ℕ) {R : RingCat.{w}}, (Fin l → ℤ) → (lpRing l R →+ R)
  | 0, _, _ => AddMonoidHom.id _
  | l + 1, R, γ => (laurentCoeffHom (S := R) (γ 0)).comp
      (lpCoeff l (R := RingCat.of (LaurentPolynomial R)) (Fin.tail γ))

/-- Elements of `lpRing l R` are determined by their coefficients. -/
lemma lpRing_ext : ∀ (l : ℕ) {R : RingCat.{w}} {x y : lpRing l R},
    (∀ γ, lpCoeff l γ x = lpCoeff l γ y) → x = y
  | 0, _, _, _, h => h Fin.elim0
  | l + 1, R, x, y, h => lpRing_ext l (R := RingCat.of (LaurentPolynomial R)) fun α ↦
      LaurentPolynomial.ext fun n ↦ by
        have := h (Fin.cons n α)
        exact this

/-- Coefficients commute with coefficientwise ring homomorphisms. -/
lemma lpCoeff_lpRingMap : ∀ (l : ℕ) {R R' : RingCat.{w}} (φ : R →+* R') (γ : Fin l → ℤ)
    (x : lpRing l R), lpCoeff l γ (lpRingMap l φ x) = φ (lpCoeff l γ x)
  | 0, _, _, _, _, _ => rfl
  | l + 1, R, R', φ, γ, x => by
    have h := lpCoeff_lpRingMap l (R := RingCat.of (LaurentPolynomial R))
      (R' := RingCat.of (LaurentPolynomial R')) (laurentMap φ) (Fin.tail γ) x
    change (lpCoeff l (R := RingCat.of (LaurentPolynomial R')) (Fin.tail γ)
      (lpRingMap l (R := RingCat.of (LaurentPolynomial R))
        (R' := RingCat.of (LaurentPolynomial R')) (laurentMap φ) x) : LaurentPolynomial R').coeff
        (γ 0) = φ ((lpCoeff l (R := RingCat.of (LaurentPolynomial R)) (Fin.tail γ) x :
          LaurentPolynomial R).coeff (γ 0))
    rw [h]
    exact coeff_laurentMap φ _ _

namespace FibMat

/-- **Coefficient formula**: the `γ`-coefficient of the fibre matrix of a morphism of `Lpow l D`
is the fibre matrix of its `γ`-coefficient (`Lpow.coeff`). -/
lemma lpCoeff_lpow_mat : ∀ (l : ℕ) {D : AddCat.{v, u}} {rank : D.carrier → ℕ → ℕ}
    {R : ℕ → RingCat.{w}} (M : FibMat D rank R) {X Y : D.carrier} (f : (Lpow l D).Mor X Y)
    (i : ℕ) (a : Fin (rank X i)) (b : Fin (rank Y i)) (γ : Fin l → ℤ),
    lpCoeff l γ ((M.lpow l).mat f i a b) = M.mat (Lpow.coeff γ f) i a b
  | 0, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | l + 1, D, _, R, M, _, _, f, i, a, b, γ => by
    change ((lpCoeff l (Fin.tail γ)) ((M.laurent.lpow l).mat f i a b)).coeff (γ 0) = _
    rw [lpCoeff_lpow_mat l M.laurent f i a b (Fin.tail γ), laurent_mat, coeff_lmat,
      Lpow.coeff_succ_eq]


end FibMat

/-! ### The polynomial part `L⁺ D` -/

section Pos

open LaurentPolynomial

variable {S : Type w} [Ring S]

lemma coeff_C_mul_T' (a : S) (m n : ℤ) :
    (C a * T m : LaurentPolynomial S).coeff n = if m = n then a else 0 := by
  rw [← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

lemma coeff_toLaurent_trunc (p : LaurentPolynomial S) (n : ℤ) :
    (Polynomial.toLaurent (trunc p)).coeff n = if 0 ≤ n then p.coeff n else 0 := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq,
      AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    split_ifs <;> simp
  | C_mul_T m a =>
    rw [trunc_C_mul_T, coeff_C_mul_T']
    by_cases hm : 0 ≤ m
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
      rw [ite_eq_left (show 0 ≤ (k : ℤ) from hm), Int.toNat_natCast, Polynomial.toLaurent_C_mul_T,
        coeff_C_mul_T']
      by_cases hn : 0 ≤ n
      · rw [ite_eq_left hn]
      · rw [ite_eq_right hn, ite_eq_right (by omega)]
    · rw [ite_eq_right hm, map_zero]
      by_cases hn : 0 ≤ n
      · rw [ite_eq_left hn, ite_eq_right (by omega)]
        rfl
      · rw [ite_eq_right hn]
        rfl

lemma toLaurent_trunc_of_nonneg {p : LaurentPolynomial S} (hp : ∀ n < 0, p.coeff n = 0) :
    Polynomial.toLaurent (trunc p) = p :=
  LaurentPolynomial.ext fun n ↦ by
    rw [coeff_toLaurent_trunc]
    split_ifs with h
    · rfl
    · exact (hp n (by omega)).symm

lemma coeff_toLaurent_neg (q : Polynomial S) {n : ℤ} (hn : n < 0) :
    (Polynomial.toLaurent q).coeff n = 0 := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, add_zero]
  | monomial k r =>
    rw [Polynomial.toLaurent_C_mul_T, coeff_C_mul_T', ite_eq_right (by omega)]

end Pos

namespace FibMat

open LaurentPolynomial

variable {D : AddCat.{v, u}} {rank : D.carrier → ℕ → ℕ} {R : ℕ → RingCat.{w}}
  (M : FibMat D rank R)

/-- The polynomial ring of the fibre ring. -/
abbrev pRing (R : ℕ → RingCat.{w}) (i : ℕ) : RingCat.{w} := RingCat.of (Polynomial (R i))

/-- The matrix of a morphism of `L⁺ D`: the truncation of its Laurent matrix. -/
def pmat {X Y : D.carrier} (f : (LaurentPos D).Mor X Y) (i : ℕ) :
    Matrix (Fin (rank X i)) (Fin (rank Y i)) (pRing R i) :=
  (M.lmat (LaurentPos.toLaurent f) i).map trunc

lemma pmat_map_toLaurent {X Y : D.carrier} (f : (LaurentPos D).Mor X Y) (i : ℕ) :
    (M.pmat f i).map Polynomial.toLaurent = M.lmat (LaurentPos.toLaurent f) i := by
  ext a b : 1
  rw [pmat, Matrix.map_apply, Matrix.map_apply]
  refine toLaurent_trunc_of_nonneg fun n hn ↦ ?_
  rw [coeff_lmat, LaurentPos.toLaurent_mem f n hn, M.mat_zero, Matrix.zero_apply]

lemma pmat_injective {X Y : D.carrier} (i : ℕ) :
    Function.Injective fun A : Matrix (Fin (rank X i)) (Fin (rank Y i)) (pRing R i) ↦
      A.map (Polynomial.toLaurent : Polynomial (R i) →+* LaurentPolynomial (R i)) :=
  Matrix.map_injective Polynomial.toLaurent_injective

/-- **The polynomial part**: fibre matrices over `R i [X]`. -/
def pos : FibMat (LaurentPos D) rank (pRing R) where
  mat f i := M.pmat f i
  mat_add f g i := by
    simp only [pmat, map_add, M.lmat_add]
    exact Matrix.map_add _ (map_add _) _ _
  mat_comp f g i := pmat_injective i <| by
    change (M.pmat (f ≫ g) i).map Polynomial.toLaurent =
      (M.pmat f i * M.pmat g i).map Polynomial.toLaurent
    rw [Matrix.map_mul, pmat_map_toLaurent, pmat_map_toLaurent, pmat_map_toLaurent,
      LaurentPos.toLaurent_comp, M.lmat_comp]
  mat_id X i := pmat_injective i <| by
    change (M.pmat ((LaurentPos D).idMor X) i).map Polynomial.toLaurent =
      (1 : Matrix (Fin (rank X i)) (Fin (rank X i)) (pRing R i)).map Polynomial.toLaurent
    rw [pmat_map_toLaurent, LaurentPos.toLaurent_id, M.lmat_id]
    exact (Matrix.map_one _ (map_zero _) (map_one _)).symm
  ext {X Y f g} h := LaurentPos.toLaurent_injective <| M.lmat_ext fun i ↦ by
    rw [← pmat_map_toLaurent, ← pmat_map_toLaurent, h i]
  full {X Y} A := by
    obtain ⟨F, hF⟩ := M.lmat_full (X := X) (Y := Y) fun i ↦ (A i).map Polynomial.toLaurent
    have hneg : ∀ n < 0, Laurent.coeff n F = 0 := fun n hn ↦ M.eq_zero_of_mat fun i ↦ by
      ext a b
      rw [← coeff_lmat, hF, Matrix.map_apply, coeff_toLaurent_neg _ hn, Matrix.zero_apply]
    refine ⟨LaurentPos.ofLaurent F hneg, fun i ↦ pmat_injective i ?_⟩
    change (M.pmat (LaurentPos.ofLaurent F hneg) i).map Polynomial.toLaurent = _
    rw [pmat_map_toLaurent, LaurentPos.toLaurent_ofLaurent, hF]
  finite := M.finite

lemma pos_mat {X Y : D.carrier} (f : (LaurentPos D).Mor X Y) (i : ℕ) :
    M.pos.mat f i = M.pmat f i := rfl

/-- **The faces map**: the fibre matrices of `ι⁺ = L^l(L⁺ D ⥤ L D)` are obtained by the ring
homomorphism `lpRingMap l toLaurent : lpRing l (R i [X]) → lpRing l (R i [T;T⁻¹])`. -/
lemma lpow_mat_incl (l : ℕ) {X Y : D.carrier} (f : (Lpow l (LaurentPos D)).Mor X Y) (i : ℕ) :
    (M.laurent.lpow l).mat ((Lpow.map l (LaurentPos.incl D)).map f) i =
      ((M.pos.lpow l).mat f i).map
        (lpRingMap l (R := pRing R i) (R' := lRing R i) Polynomial.toLaurent) := by
  ext a b : 1
  refine lpRing_ext l fun γ ↦ ?_
  rw [Matrix.map_apply, lpCoeff_lpRingMap, lpCoeff_lpow_mat, lpCoeff_lpow_mat, Lpow.coeff_map,
    laurent_mat, pos_mat, LaurentPos.incl_map]
  exact (congrArg (fun A ↦ A a b) (M.pmat_map_toLaurent _ i)).symm

end FibMat


/-! ### Splitting a Karoubi isomorphism out of a block sum -/

section Split

open Matrix

variable {S : Type w} [Ring S] {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- A Karoubi isomorphism `(e ⊕ f) ≅ g` in components. -/
lemma MatKarIso.split {e : Matrix α α S} {f : Matrix β β S} {g : Matrix γ γ S}
    (h : MatKarIso (Matrix.fromBlocks e 0 0 f) g) :
    ∃ (U₁ : Matrix α γ S) (U₂ : Matrix β γ S) (V₁ : Matrix γ α S) (V₂ : Matrix γ β S),
      e * U₁ * g = U₁ ∧ f * U₂ * g = U₂ ∧ g * V₁ * e = V₁ ∧ g * V₂ * f = V₂ ∧
      U₁ * V₁ = e ∧ U₁ * V₂ = 0 ∧ U₂ * V₁ = 0 ∧ U₂ * V₂ = f ∧ V₁ * U₁ + V₂ * U₂ = g := by
  obtain ⟨U, V, h1, h2, h3, h4⟩ := h
  have hU := Matrix.fromRows_toRows U
  have hV := Matrix.fromCols_toCols V
  rw [← hU] at h1 h3 h4
  rw [← hV] at h2 h3 h4
  refine ⟨U.toRows₁, U.toRows₂, V.toCols₁, V.toCols₂, ?_⟩
  rw [Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul, Matrix.fromRows_ext_iff] at h1
  rw [Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_ext_iff] at h2
  rw [Matrix.fromRows_mul_fromCols, Matrix.fromBlocks_inj] at h3
  rw [Matrix.fromCols_mul_fromRows] at h4
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add] at h1 h2
  exact ⟨h1.1, h1.2, h2.1, h2.2, h3.1, h3.2.1, h3.2.2.1, h3.2.2.2, h4⟩


end Split

/-! ### Assembly: Theorem R fibrewise ⇒ Theorem R in Karoubi form -/

namespace FibMat

open Matrix Idempotents

variable {D : AddCat.{v, u}} {rank : D.carrier → ℕ → ℕ} {R : ℕ → RingCat.{w}}
  (M : FibMat D rank R)

/-- The face map at fibre `i`: `lpRing l (R i [X]) → lpRing l (R i [T;T⁻¹]) = lpRing (l+1) (R i)`. -/
abbrev fibFace (l : ℕ) (R : ℕ → RingCat.{w}) (i : ℕ) :
    lpRing l (pRing R i) →+* lpRing (l + 1) (R i) :=
  lpRingMap l (R := pRing R i) (R' := lRing R i) Polynomial.toLaurent

include M in
/-- **Assembly.** If the matrix form of Theorem R holds at every fibre and objects with smaller
support can be formed, then every Kar object `E` of `L^{l+1} D` satisfies
`E ⊞ ι⁺Q₁ ≅ ι⁺Q₀` for Kar objects `Q₀, Q₁` of `L^l(L⁺ D)` (an isomorphism in `Karoubi`). -/
theorem exists_karoubi_iso (l : ℕ)
    (hR : ∀ (i : ℕ) {n : ℕ} (e : Matrix (Fin n) (Fin n) (lpRing (l + 1) (R i))), e * e = e →
      ∃ (r₀ r₁ : ℕ) (e₀ : Matrix (Fin r₀) (Fin r₀) (lpRing l (pRing R i)))
        (e₁ : Matrix (Fin r₁) (Fin r₁) (lpRing l (pRing R i))),
        e₀ * e₀ = e₀ ∧ e₁ * e₁ = e₁ ∧
          MatKarIso (fromBlocks e 0 0 (e₁.map (fibFace l R i))) (e₀.map (fibFace l R i)))
    (hmk : ∀ (X : D.carrier) (r : ℕ → ℕ), (∀ i, rank X i = 0 → r i = 0) →
      ∃ Q : D.carrier, rank Q = r)
    (E : Karoubi (Lpow (l + 1) D).carrier) :
    ∃ Q₀ Q₁ : Karoubi (Lpow l (LaurentPos D)).carrier,
      Nonempty (E ⊞ (karoubiMap (Lpow.map l (LaurentPos.incl D))).obj Q₁ ≅
        (karoubiMap (Lpow.map l (LaurentPos.incl D))).obj Q₀) := by
  classical
  obtain ⟨X, e, he⟩ := E
  let MF := M.laurent.lpow l
  let MP := M.pos.lpow l
  let F := Lpow.map l (LaurentPos.incl D)
  have hei : ∀ i, MF.mat e i * MF.mat e i = MF.mat e i := fun i ↦ by
    rw [← MF.mat_comp, he]
  have key : ∀ i, ∃ (r₀ r₁ : ℕ) (e₀ : Matrix (Fin r₀) (Fin r₀) (lpRing l (pRing R i)))
      (e₁ : Matrix (Fin r₁) (Fin r₁) (lpRing l (pRing R i))),
      e₀ * e₀ = e₀ ∧ e₁ * e₁ = e₁ ∧
        MatKarIso (fromBlocks (MF.mat e i) 0 0 (e₁.map (fibFace l R i))) (e₀.map (fibFace l R i))
        ∧ (rank X i = 0 → r₀ = 0 ∧ r₁ = 0) := by
    intro i
    by_cases h0 : rank X i = 0
    · refine ⟨0, 0, 0, 0, by simp, by simp, ?_, fun _ ↦ ⟨rfl, rfl⟩⟩
      have : IsEmpty (Fin (rank X i) ⊕ Fin 0) :=
        ⟨fun a ↦ by rcases a with a | a; exact absurd a.2 (by omega); exact a.elim0⟩
      exact ⟨0, 0, Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _,
        Subsingleton.elim _ _⟩
    · obtain ⟨r₀, r₁, e₀, e₁, h₀, h₁, hiso⟩ := hR i (MF.mat e i) (hei i)
      exact ⟨r₀, r₁, e₀, e₁, h₀, h₁, hiso, fun h ↦ absurd h h0⟩
  choose r₀ r₁ e₀ e₁ he₀ he₁ hiso hz using key
  obtain ⟨Q₀, hQ₀⟩ := hmk X r₀ fun i h ↦ (hz i h).1
  obtain ⟨Q₁, hQ₁⟩ := hmk X r₁ fun i h ↦ (hz i h).2
  subst hQ₀ hQ₁
  obtain ⟨q₀, hq₀⟩ := MP.full (X := Q₀) (Y := Q₀) e₀
  obtain ⟨q₁, hq₁⟩ := MP.full (X := Q₁) (Y := Q₁) e₁
  have hq₀i : q₀ ≫ q₀ = q₀ := MP.ext fun i ↦ by rw [MP.mat_comp, hq₀, he₀]
  have hq₁i : q₁ ≫ q₁ = q₁ := MP.ext fun i ↦ by rw [MP.mat_comp, hq₁, he₁]
  have hp₀ : ∀ i, MF.mat (F.map q₀) i = (e₀ i).map (fibFace l R i) := fun i ↦ by
    rw [M.lpow_mat_incl l q₀ i]
    exact congrArg (fun A ↦ A.map (fibFace l R i)) (hq₀ i)
  have hp₁ : ∀ i, MF.mat (F.map q₁) i = (e₁ i).map (fibFace l R i) := fun i ↦ by
    rw [M.lpow_mat_incl l q₁ i]
    exact congrArg (fun A ↦ A.map (fibFace l R i)) (hq₁ i)
  choose U₁ U₂ V₁ V₂ h1 h2 h3 h4 h5 h6 h7 h8 h9 using fun i ↦ (hiso i).split
  obtain ⟨u₁, hu₁⟩ := MF.full (X := X) (Y := Q₀) U₁
  obtain ⟨u₂, hu₂⟩ := MF.full (X := Q₁) (Y := Q₀) U₂
  obtain ⟨v₁, hv₁⟩ := MF.full (X := Q₀) (Y := X) V₁
  obtain ⟨v₂, hv₂⟩ := MF.full (X := Q₀) (Y := Q₁) V₂
  have c1 : e ≫ u₁ ≫ F.map q₀ = u₁ := MF.ext fun i ↦ by
    rw [MF.mat_comp, MF.mat_comp, hu₁, hp₀]
    exact (Matrix.mul_assoc _ _ _).symm.trans (h1 i)
  have c2 : F.map q₁ ≫ u₂ ≫ F.map q₀ = u₂ := MF.ext fun i ↦ by
    rw [MF.mat_comp, MF.mat_comp, hu₂, hp₀, hp₁]
    exact (Matrix.mul_assoc _ _ _).symm.trans (h2 i)
  have c3 : F.map q₀ ≫ v₁ ≫ e = v₁ := MF.ext fun i ↦ by
    rw [MF.mat_comp, MF.mat_comp, hv₁, hp₀]
    exact (Matrix.mul_assoc _ _ _).symm.trans (h3 i)
  have c4 : F.map q₀ ≫ v₂ ≫ F.map q₁ = v₂ := MF.ext fun i ↦ by
    rw [MF.mat_comp, MF.mat_comp, hv₂, hp₀, hp₁]
    exact (Matrix.mul_assoc _ _ _).symm.trans (h4 i)
  have c5 : u₁ ≫ v₁ = e := MF.ext fun i ↦ by rw [MF.mat_comp, hu₁, hv₁, h5]
  have c6 : u₁ ≫ v₂ = 0 := MF.ext fun i ↦ by rw [MF.mat_comp, hu₁, hv₂, h6, MF.mat_zero]
  have c7 : u₂ ≫ v₁ = 0 := MF.ext fun i ↦ by rw [MF.mat_comp, hu₂, hv₁, h7, MF.mat_zero]
  have c8 : u₂ ≫ v₂ = F.map q₁ := MF.ext fun i ↦ by
    rw [MF.mat_comp, hu₂, hv₂, h8]
    exact (hp₁ i).symm
  have c9 : v₁ ≫ u₁ + v₂ ≫ u₂ = F.map q₀ := MF.ext fun i ↦ by
    rw [MF.mat_add, MF.mat_comp, MF.mat_comp, hu₁, hu₂, hv₁, hv₂, h9]
    exact (hp₀ i).symm
  let E' : Karoubi (Lpow (l + 1) D).carrier := ⟨X, e, he⟩
  let P₀ := (karoubiMap F).obj ⟨Q₀, q₀, hq₀i⟩
  let P₁ := (karoubiMap F).obj ⟨Q₁, q₁, hq₁i⟩
  let a₁ : E' ⟶ P₀ := ⟨u₁, c1⟩
  let a₂ : P₁ ⟶ P₀ := ⟨u₂, c2⟩
  let b₁ : P₀ ⟶ E' := ⟨v₁, c3⟩
  let b₂ : P₀ ⟶ P₁ := ⟨v₂, c4⟩
  have k11 : a₁ ≫ b₁ = 𝟙 E' := Karoubi.hom_ext _ _ c5
  have k12 : a₁ ≫ b₂ = 0 := Karoubi.hom_ext _ _ c6
  have k21 : a₂ ≫ b₁ = 0 := Karoubi.hom_ext _ _ c7
  have k22 : a₂ ≫ b₂ = 𝟙 P₁ := Karoubi.hom_ext _ _ c8
  have k0 : b₁ ≫ a₁ + b₂ ≫ a₂ = 𝟙 P₀ := Karoubi.hom_ext _ _ c9
  refine ⟨⟨Q₀, q₀, hq₀i⟩, ⟨Q₁, q₁, hq₁i⟩, ⟨
    { hom := biprod.desc a₁ a₂
      inv := biprod.lift b₁ b₂
      hom_inv_id := ?_
      inv_hom_id := by rw [biprod.lift_desc, k0] }⟩⟩
  apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
    simp only [Category.assoc, biprod.lift_fst, biprod.lift_snd, biprod.inl_desc_assoc,
      biprod.inr_desc_assoc, Category.comp_id, biprod.inl_fst, biprod.inl_snd, biprod.inr_fst,
      biprod.inr_snd, k11, k12, k21, k22] <;> rfl

end FibMat

end

end HSFormal.LTheory.Reg
