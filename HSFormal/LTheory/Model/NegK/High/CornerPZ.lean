import HSFormal.LTheory.Model.NegK.High.BassStatement
import HSFormal.LTheory.Model.CutWindow

/-!
# Theorem B, part 1: the window corner (NegKHigh)

`blueprint/negK-high.md` §3.1 (Theorem B), the one-dimensional `P_Z` variant of
`blueprint/negK-high-review.md` (replacing N6 `Corner` / N7 `Regroup`).

For a bounded object `Z` of `C_ℤ Y` (`Y.czBdd`) with window sum `ΣZ = ⊕_u Z_u`
(`CZ.Window.pt`), let `C = (ΣZ)_{r ∈ ℤ}` be the constant object (`CZ.periodObj`).

* `CZ.Corner.U Z j : C ⟶ Z` reads the copy of `ΣZ` at `r = j` and unfolds it along `Z`
  (entries `[v = j] π_w`); `CZ.Corner.Us Z j : Z ⟶ C` is its dual (entries `[w = j] ι_v`).
  `Us j ≫ U k = [j = k]`, and the cuts of `C` act on them by `[j ∈ cut]`.
* **Periodic maps.**  For `M : C ⟶ C` with entries `M_{w v} = Σ(g_{w - v})` for a finitely
  supported family `g : ℤ → (Z ⟶ Z)` (e.g. `M = Π(Σ ĝ)` for a Laurent morphism `ĝ` of
  `L(C_ℤ^{bdd} Y)`): `M ≫ U j = ∑ₙ U (j - n) ≫ gₙ`, `Us j ≫ M = ∑ₙ gₙ ≫ Us (j + n)`, and, for
  `g` supported in `{-1, 0, 1}`, the corners of `M` across the cut at `1/2` are
  `U 1 ≫ g₋₁ ≫ Us 0` and `U 0 ≫ g₁ ≫ Us 1`.
* **Lift to `L^l`** (`perSum_comp_U`, `Us_comp_perSum`, `chi_comp_perSum_comp_chi_pos_neg/neg_pos`):
  the same relations for `Π(Σ P) = perSum P` (`P` in `L^{l+1}(C_ℤ^{bdd} Y)`), in terms of the
  `w`-coefficients `Fₙ` of `P` (`coeff (n :: α) P = coeff α Fₙ`).
* **Symbols** `symb f₀ f₁ f₋₁ = f₀ + f₁ w + f₋₁ w⁻¹` in `L^{l+1}(C_ℤ Y)` (`ext` = old variables),
  their coefficients and products; the window `[-a, a]` (`win`, `winObj`), the restriction
  `winRes` and its lift `bddRes` to `L^{l+1}(C_ℤ^{bdd} Y)`.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive Idempotents

noncomputable section

universe v u

namespace Lpow

variable {D : AddCat.{v, u}}

/-- The coefficients of `ext f ≫ wᵐ` in `L^{l+1} D`. -/
lemma coeff_extend_comp_w {l : ℕ} {X Z : Lpow l D} (n m : ℤ) (α : Fin l → ℤ)
    (f : (Lpow l D).Mor X Z) :
    coeff (Fin.cons n α : Fin (l + 1) → ℤ) ((extend D l).map f ≫ w l m Z) =
      if m = n then coeff α f else 0 := by
  rw [coeff_cons, w, coeff_comp_incl (D := Laurent D), coeff_map,
    ← Laurent.single_eq_incl_comp_T, Laurent.coeff_single]

end Lpow

namespace CZ.Corner

open CZ.Window

variable {Y : InvCat} (Z : Y.czBdd)

/-- The propagation bound of the column maps `U j`. -/
def ubound (j : ℤ) : ℕ := (hi Z - j).toNat + (j - lo Z).toNat

lemma abs_le_ubound {j w : ℤ} (hw : lo Z ≤ w ∧ w ≤ hi Z) : |w - j| ≤ (ubound Z j : ℤ) := by
  rw [abs_le]; unfold ubound; constructor <;> omega

/-- The matrix of `U j`: `[v = j] π_w`. -/
def Umat (j : ℤ) : Mat (periodObj Y (pt Z)) Z.obj := fun w v ↦ if v = j then π Z w else 0

lemma propLE_Umat (j : ℤ) : PropLE (Umat Z j) (ubound Z j) := fun w v h ↦ by
  unfold Umat
  split_ifs with hv
  · subst hv
    by_cases hw : lo Z ≤ w ∧ w ≤ hi Z
    · exact absurd h (not_lt.mpr (abs_le_ubound Z hw))
    · exact (isZero_of_not_mem Z hw).eq_of_tgt _ _
  · rfl

/-- `U j : C ⟶ Z`: the copy of `ΣZ` at `r = j`, unfolded along `Z`. -/
def U (j : ℤ) : periodObj Y (pt Z) ⟶ Z.obj := homMk (Umat Z j) _ (propLE_Umat Z j)

lemma U_apply (j w v : ℤ) : (U Z j).1 w v = if v = j then π Z w else 0 := rfl

/-- The matrix of `Us j`: `[w = j] ι_v`. -/
def Usmat (j : ℤ) : Mat Z.obj (periodObj Y (pt Z)) := fun w v ↦ if w = j then ι Z v else 0

lemma propLE_Usmat (j : ℤ) : PropLE (Usmat Z j) (ubound Z j) := fun w v h ↦ by
  unfold Usmat
  split_ifs with hw
  · subst hw
    by_cases hv : lo Z ≤ v ∧ v ≤ hi Z
    · exact absurd h (not_lt.mpr (by rw [abs_sub_comm]; exact abs_le_ubound Z hv))
    · exact (isZero_of_not_mem Z hv).eq_of_src _ _
  · rfl

/-- `Us j : Z ⟶ C`: `Z` folded into the copy of `ΣZ` at `r = j`. -/
def Us (j : ℤ) : Z.obj ⟶ periodObj Y (pt Z) := homMk (Usmat Z j) _ (propLE_Usmat Z j)

lemma Us_apply (j w v : ℤ) : (Us Z j).1 w v = if w = j then ι Z v else 0 := rfl

/-! ### Entries of composites -/

lemma comp_U_apply {T : Y.cz} (f : T ⟶ periodObj Y (pt Z)) (j w v : ℤ) :
    (f ≫ U Z j).1 w v = f.1 j v ≫ π Z w := by
  rw [CZ.comp_apply, finsum_eq_single _ j fun x hx ↦ by rw [U_apply, ite_eq_right hx, comp_zero],
    U_apply, ite_eq_left rfl]

lemma Us_comp_apply {T : Y.cz} (f : periodObj Y (pt Z) ⟶ T) (j w v : ℤ) :
    (Us Z j ≫ f).1 w v = ι Z v ≫ f.1 w j := by
  rw [CZ.comp_apply, finsum_eq_single _ j fun x hx ↦ by rw [Us_apply, ite_eq_right hx, zero_comp],
    Us_apply, ite_eq_left rfl]

lemma U_comp_apply {T : Y.cz} (φ : Z.obj ⟶ T) (j w v : ℤ) :
    (U Z j ≫ φ).1 w v = if v = j then ∑ x ∈ supp Z, π Z x ≫ φ.1 w x else 0 := by
  rw [CZ.comp_apply]
  split_ifs with hv
  · rw [finsum_eq_sum_of_support_subset _ (s := supp Z) fun x hx ↦ Finset.mem_coe.2
      (by_contra fun hx' ↦ (Function.mem_support.1 hx) (by
        rw [U_apply, ite_eq_left hv, (isZero_of_not_mem_supp Z hx').eq_of_tgt (π Z x) 0,
          zero_comp]))]
    exact Finset.sum_congr rfl fun x _ ↦ by rw [U_apply, ite_eq_left hv]
  · exact finsum_eq_zero_of_forall_eq_zero fun x ↦ by rw [U_apply, ite_eq_right hv, zero_comp]

lemma comp_Us_apply {T : Y.cz} (φ : T ⟶ Z.obj) (j w v : ℤ) :
    (φ ≫ Us Z j).1 w v = if w = j then ∑ y ∈ supp Z, φ.1 y v ≫ ι Z y else 0 := by
  rw [CZ.comp_apply]
  split_ifs with hw
  · rw [finsum_eq_sum_of_support_subset _ (s := supp Z) fun y hy ↦ Finset.mem_coe.2
      (by_contra fun hy' ↦ (Function.mem_support.1 hy) (by
        rw [Us_apply, ite_eq_left hw, (isZero_of_not_mem_supp Z hy').eq_of_src (ι Z y) 0,
          comp_zero]))]
    exact Finset.sum_congr rfl fun y _ ↦ by rw [Us_apply, ite_eq_left hw]
  · exact finsum_eq_zero_of_forall_eq_zero fun y ↦ by rw [Us_apply, ite_eq_right hw, comp_zero]

lemma U_comp_comp_Us_apply {g : Z ⟶ Z} {φ : Z.obj ⟶ Z.obj} (hgφ : g.hom = φ) (j k w v : ℤ) :
    (U Z j ≫ φ ≫ Us Z k).1 w v = if v = j ∧ w = k then sumHom g else 0 := by
  rw [U_comp_apply]
  by_cases hv : v = j
  · rw [ite_eq_left hv]
    by_cases hw : w = k
    · rw [ite_eq_left (show v = j ∧ w = k from ⟨hv, hw⟩), sumHom, hgφ]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [comp_Us_apply, ite_eq_left hw, comp_sum]
    · rw [ite_eq_right (show ¬(v = j ∧ w = k) from fun h ↦ hw h.2)]
      exact Finset.sum_eq_zero fun x _ ↦ by rw [comp_Us_apply, ite_eq_right hw, comp_zero]
  · rw [ite_eq_right hv, ite_eq_right (show ¬(v = j ∧ w = k) from fun h ↦ hv h.1)]

/-! ### Relations -/

lemma Us_comp_U (j k : ℤ) : Us Z j ≫ U Z k = if j = k then 𝟙 Z.obj else 0 := by
  refine CZ.hom_ext fun w v ↦ ?_
  rw [Us_comp_apply, U_apply]
  by_cases hjk : j = k
  · rw [ite_eq_left hjk, ite_eq_left hjk]
    by_cases hvw : v = w
    · subst hvw; rw [ι_π_self, id_apply_self]
    · rw [ι_π_ne Z hvw, id_apply_ne _ hvw]
  · rw [ite_eq_right hjk, ite_eq_right hjk, comp_zero]; rfl

lemma Us_comp_U_self (j : ℤ) : Us Z j ≫ U Z j = 𝟙 Z.obj := by
  rw [Us_comp_U, ite_eq_left rfl]

lemma cut_comp_U (P : ℤ → Prop) [DecidablePred P] (k : ℤ) :
    (cut (periodObj Y (pt Z)) P).idem ≫ U Z k = if P k then U Z k else 0 := by
  refine CZ.hom_ext fun w v ↦ ?_
  rw [cut_idem, diag_comp_apply, U_apply]
  by_cases hv : v = k
  · subst hv
    by_cases hP : P v
    · rw [ite_eq_left hP, ite_eq_left hP, ite_eq_left rfl, id_comp, U_apply, ite_eq_left rfl]
    · rw [ite_eq_right hP, ite_eq_right hP, zero_comp]; rfl
  · rw [ite_eq_right hv, comp_zero]
    split_ifs
    · rw [U_apply, ite_eq_right hv]
    · rfl

lemma Us_comp_cut (P : ℤ → Prop) [DecidablePred P] (k : ℤ) :
    Us Z k ≫ (cut (periodObj Y (pt Z)) P).idem = if P k then Us Z k else 0 := by
  refine CZ.hom_ext fun w v ↦ ?_
  rw [cut_idem, comp_diag_apply, Us_apply]
  by_cases hw : w = k
  · subst hw
    by_cases hP : P w
    · rw [ite_eq_left hP, ite_eq_left hP, ite_eq_left rfl, comp_id, Us_apply, ite_eq_left rfl]
    · rw [ite_eq_right hP, ite_eq_right hP, comp_zero]; rfl
  · rw [ite_eq_right hw, zero_comp]
    split_ifs
    · rw [Us_apply, ite_eq_right hw]
    · rfl

/-! ### Periodic maps -/

lemma sumHom_zero' : sumHom (0 : Z ⟶ Z) = 0 := (sumF Y).F.map_zero Z Z

section Periodic

variable {Z} {M : periodObj Y (pt Z) ⟶ periodObj Y (pt Z)} {g : ℤ → (Z ⟶ Z)}
  {φ : ℤ → (Z.obj ⟶ Z.obj)} (hM : ∀ w v, M.1 w v = sumHom (g (w - v)))
  (hgφ : ∀ n, (g n).hom = φ n)
include hM hgφ

/-- `M ≫ U j = ∑ₙ U (j - n) ≫ φₙ`. -/
lemma comp_U_eq (S : Finset ℤ) (hS : ∀ n ∉ S, g n = 0) (j : ℤ) :
    M ≫ U Z j = ∑ n ∈ S, U Z (j - n) ≫ φ n := by
  refine CZ.hom_ext fun w v ↦ ?_
  rw [comp_U_apply, hM, CZ.sum_apply]
  refine Eq.trans ?_ (Finset.sum_congr rfl fun n _ ↦ (U_comp_apply Z (φ n) (j - n) w v).symm)
  by_cases hn : j - v ∈ S
  · rw [Finset.sum_eq_single (j - v) (fun n _ hne ↦ ite_eq_right (by omega))
      (fun h ↦ absurd hn h), ite_eq_left (show v = j - (j - v) by ring), sumHom_π, hgφ]
  · rw [hS _ hn, sumHom_zero', zero_comp]
    refine (Finset.sum_eq_zero fun n hnS ↦ ite_eq_right fun h ↦ hn ?_).symm
    rwa [h, sub_sub_cancel]

/-- `Us j ≫ M = ∑ₙ φₙ ≫ Us (j + n)`. -/
lemma Us_comp_eq (S : Finset ℤ) (hS : ∀ n ∉ S, g n = 0) (j : ℤ) :
    Us Z j ≫ M = ∑ n ∈ S, φ n ≫ Us Z (j + n) := by
  refine CZ.hom_ext fun w v ↦ ?_
  rw [Us_comp_apply, hM, CZ.sum_apply]
  refine Eq.trans ?_ (Finset.sum_congr rfl fun n _ ↦ (comp_Us_apply Z (φ n) (j + n) w v).symm)
  by_cases hn : w - j ∈ S
  · rw [Finset.sum_eq_single (w - j) (fun n _ hne ↦ ite_eq_right (by omega))
      (fun h ↦ absurd hn h), ite_eq_left (show w = j + (w - j) by ring), ι_sumHom, hgφ]
  · rw [hS _ hn, sumHom_zero', comp_zero]
    refine (Finset.sum_eq_zero fun n hnS ↦ ite_eq_right fun h ↦ hn ?_).symm
    rwa [h, add_sub_cancel_left]

variable (hg : ∀ n, n < -1 ∨ 1 < n → g n = 0)
include hg

/-- The corner of `M` from `r ≥ 1` to `r ≤ 0`: `U 1 ≫ φ₋₁ ≫ Us 0`. -/
lemma cut_comp_comp_cut_pos_neg :
    (cut (periodObj Y (pt Z)) (1 ≤ ·)).idem ≫ M ≫ (cut (periodObj Y (pt Z)) (· ≤ 0)).idem =
      U Z 1 ≫ φ (-1) ≫ Us Z 0 := by
  refine CZ.hom_ext fun w v ↦ ?_
  rw [U_comp_comp_Us_apply Z (hgφ (-1)), cut_idem, cut_idem, diag_comp_apply, comp_diag_apply,
    hM]
  by_cases h : v = 1 ∧ w = 0
  · rw [ite_eq_left h, h.1, h.2, ite_eq_left (show (1 : ℤ) ≤ 1 by omega),
      ite_eq_left (show (0 : ℤ) ≤ 0 by omega), id_comp, comp_id]
    rfl
  · rw [ite_eq_right h]
    by_cases hv : 1 ≤ v
    · by_cases hw : w ≤ 0
      · rw [ite_eq_left hv, ite_eq_left hw, id_comp, comp_id, hg (w - v) (by omega),
          sumHom_zero']
      · rw [ite_eq_right hw, comp_zero, comp_zero]
    · rw [ite_eq_right hv, zero_comp]

/-- The corner of `M` from `r ≤ 0` to `r ≥ 1`: `U 0 ≫ φ₁ ≫ Us 1`. -/
lemma cut_comp_comp_cut_neg_pos :
    (cut (periodObj Y (pt Z)) (· ≤ 0)).idem ≫ M ≫ (cut (periodObj Y (pt Z)) (1 ≤ ·)).idem =
      U Z 0 ≫ φ 1 ≫ Us Z 1 := by
  refine CZ.hom_ext fun w v ↦ ?_
  rw [U_comp_comp_Us_apply Z (hgφ 1), cut_idem, cut_idem, diag_comp_apply, comp_diag_apply, hM]
  by_cases h : v = 0 ∧ w = 1
  · rw [ite_eq_left h, h.1, h.2, ite_eq_left (show (1 : ℤ) ≤ 1 by omega),
      ite_eq_left (show (0 : ℤ) ≤ 0 by omega), id_comp, comp_id]
    rfl
  · rw [ite_eq_right h]
    by_cases hv : v ≤ 0
    · by_cases hw : 1 ≤ w
      · rw [ite_eq_left hv, ite_eq_left hw, id_comp, comp_id, hg (w - v) (by omega),
          sumHom_zero']
      · rw [ite_eq_right hw, comp_zero, comp_zero]
    · rw [ite_eq_right hv, zero_comp]

end Periodic

/-! ### The lift to `L^l` -/

/-- The inclusion `C_ℤ^{bdd} Y ⥤ C_ℤ Y`, on `AddCat` carriers. -/
abbrev bddIncl (Y : InvCat) : (Y.czBdd : AddCat).carrier ⥤ (Y.cz : AddCat).carrier :=
  (Y.cz.subIncl (CZ.bdd Y)).F

/-- The window sum `Σ : C_ℤ^{bdd} Y ⥤ Y`, on `AddCat` carriers. -/
abbrev sumFun (Y : InvCat) : (Y.czBdd : AddCat).carrier ⥤ (Y : AddCat).carrier :=
  (sumF Y).F

variable {l : ℕ}

/-- `Π(Σ P)` in `L^l(C_ℤ Y)`, for `P` in `L^{l+1}(C_ℤ^{bdd} Y)`. -/
abbrev perSum {Z : Y.czBdd} (P : (Lpow (l + 1) (Y.czBdd : AddCat)).Mor Z Z) :
    (Lpow l (Y.cz : AddCat)).Mor (periodObj Y (pt Z)) (periodObj Y (pt Z)) :=
  (Lpow.map l (CZ.periodize Y)).map ((Lpow.map (l + 1) (sumFun Y)).map P)

lemma perSum_coeff_apply {Z : Y.czBdd} (P : (Lpow (l + 1) (Y.czBdd : AddCat)).Mor Z Z)
    (α : Fin l → ℤ) (w v : ℤ) :
    (Lpow.coeff α (perSum P)).1 w v = sumHom (Lpow.coeff (Fin.cons (w - v) α) P) := by
  rw [Lpow.coeff_cons, Lpow.coeff_map (CZ.periodize Y), periodize_map_apply]
  change Laurent.coeff (w - v)
    (Lpow.coeff α ((Lpow.map l (Laurent.map (sumFun Y))).map P)) = _
  rw [Lpow.coeff_map]
  exact Laurent.coeff_map (sumFun Y) (w - v) _

lemma coeff_hom {k : ℕ} {Z Z' : Y.czBdd} (P : (Lpow k (Y.czBdd : AddCat)).Mor Z Z')
    (γ : Fin k → ℤ) :
    (Lpow.coeff γ P).hom = Lpow.coeff γ ((Lpow.map k (bddIncl Y)).map P) := by
  rw [Lpow.coeff_map]; rfl

section Lift

variable {Z : Y.czBdd} {P : (Lpow (l + 1) (Y.czBdd : AddCat)).Mor Z Z}
  {F : ℤ → (Lpow l (Y.cz : AddCat)).Mor Z.obj Z.obj}
  (hF : ∀ n α, Lpow.coeff (Fin.cons n α : Fin (l + 1) → ℤ)
    ((Lpow.map (l + 1) (bddIncl Y)).map P) = Lpow.coeff α (F n))
include hF

lemma coeff_hom_eq (n : ℤ) (α : Fin l → ℤ) :
    (Lpow.coeff (Fin.cons n α : Fin (l + 1) → ℤ) P).hom = Lpow.coeff α (F n) := by
  rw [coeff_hom, hF]

lemma coeff_eq_zero {n : ℤ} (hn : F n = 0) (α : Fin l → ℤ) :
    Lpow.coeff (Fin.cons n α : Fin (l + 1) → ℤ) P = 0 :=
  ObjectProperty.hom_ext _ (by rw [coeff_hom_eq hF, hn, Lpow.coeff_zero]; rfl)

/-- `Π(Σ P) ≫ U j = ∑ₙ U (j - n) ≫ Fₙ`, for `P` with `w`-coefficients `Fₙ`. -/
@[reassoc]
lemma perSum_comp_U (S : Finset ℤ) (hS : ∀ n ∉ S, F n = 0) (j : ℤ) :
    perSum P ≫ (Lpow.incl (Y.cz : AddCat) l).map (U Z j) =
      ∑ n ∈ S, (Lpow.incl (Y.cz : AddCat) l).map (U Z (j - n)) ≫ F n :=
  Lpow.ext fun α ↦ by
    rw [Lpow.coeff_comp_incl, Lpow.coeff_sum]
    refine (comp_U_eq (M := Lpow.coeff α (perSum P))
      (g := fun n ↦ Lpow.coeff (Fin.cons n α : Fin (l + 1) → ℤ) P)
      (φ := fun n ↦ Lpow.coeff α (F n)) (perSum_coeff_apply P α) (fun n ↦ coeff_hom_eq hF n α)
      S (fun n hn ↦ coeff_eq_zero hF (hS n hn) α) j).trans ?_
    exact Finset.sum_congr rfl fun n _ ↦
      (Lpow.coeff_incl_comp (D := (Y.cz : AddCat)) α (U Z (j - n)) (F n)).symm

/-- `Us j ≫ Π(Σ P) = ∑ₙ Fₙ ≫ Us (j + n)`. -/
lemma Us_comp_perSum (S : Finset ℤ) (hS : ∀ n ∉ S, F n = 0) (j : ℤ) :
    (Lpow.incl (Y.cz : AddCat) l).map (Us Z j) ≫ perSum P =
      ∑ n ∈ S, F n ≫ (Lpow.incl (Y.cz : AddCat) l).map (Us Z (j + n)) :=
  Lpow.ext fun α ↦ by
    rw [Lpow.coeff_incl_comp, Lpow.coeff_sum]
    refine (Us_comp_eq (M := Lpow.coeff α (perSum P))
      (g := fun n ↦ Lpow.coeff (Fin.cons n α : Fin (l + 1) → ℤ) P)
      (φ := fun n ↦ Lpow.coeff α (F n)) (perSum_coeff_apply P α) (fun n ↦ coeff_hom_eq hF n α)
      S (fun n hn ↦ coeff_eq_zero hF (hS n hn) α) j).trans ?_
    exact Finset.sum_congr rfl fun n _ ↦
      (Lpow.coeff_comp_incl (D := (Y.cz : AddCat)) α (F n) (Us Z (j + n))).symm

variable (hF3 : ∀ n, n < -1 ∨ 1 < n → F n = 0)
include hF3

/-- The corner of `Π(Σ P)` from `r ≥ 1` to `r ≤ 0`. -/
lemma chi_comp_perSum_comp_chi_pos_neg :
    Lpow.chi (periodObj Y (pt Z)) (1 ≤ ·) ≫ perSum P ≫ Lpow.chi (periodObj Y (pt Z)) (· ≤ 0) =
      (Lpow.incl (Y.cz : AddCat) l).map (U Z 1) ≫ F (-1) ≫
        (Lpow.incl (Y.cz : AddCat) l).map (Us Z 0) :=
  Lpow.ext fun α ↦ by
    rw [Lpow.chi, Lpow.chi, Lpow.coeff_incl_comp, Lpow.coeff_comp_incl, Lpow.coeff_incl_comp,
      Lpow.coeff_comp_incl]
    exact cut_comp_comp_cut_pos_neg (M := Lpow.coeff α (perSum P))
      (g := fun n ↦ Lpow.coeff (Fin.cons n α : Fin (l + 1) → ℤ) P)
      (φ := fun n ↦ Lpow.coeff α (F n)) (perSum_coeff_apply P α) (fun n ↦ coeff_hom_eq hF n α)
      (fun n hn ↦ coeff_eq_zero hF (hF3 n hn) α)

/-- The corner of `Π(Σ P)` from `r ≤ 0` to `r ≥ 1`. -/
lemma chi_comp_perSum_comp_chi_neg_pos :
    Lpow.chi (periodObj Y (pt Z)) (· ≤ 0) ≫ perSum P ≫ Lpow.chi (periodObj Y (pt Z)) (1 ≤ ·) =
      (Lpow.incl (Y.cz : AddCat) l).map (U Z 0) ≫ F 1 ≫
        (Lpow.incl (Y.cz : AddCat) l).map (Us Z 1) :=
  Lpow.ext fun α ↦ by
    rw [Lpow.chi, Lpow.chi, Lpow.coeff_incl_comp, Lpow.coeff_comp_incl, Lpow.coeff_incl_comp,
      Lpow.coeff_comp_incl]
    exact cut_comp_comp_cut_neg_pos (M := Lpow.coeff α (perSum P))
      (g := fun n ↦ Lpow.coeff (Fin.cons n α : Fin (l + 1) → ℤ) P)
      (φ := fun n ↦ Lpow.coeff α (F n)) (perSum_coeff_apply P α) (fun n ↦ coeff_hom_eq hF n α)
      (fun n hn ↦ coeff_eq_zero hF (hF3 n hn) α)

end Lift

/-! ### The symbol `f₀ + f₁ w + f₋₁ w⁻¹` -/

section Symbol

variable {X : Lpow l (Y.cz : AddCat)}

/-- The old variables `L^l(C_ℤ Y) ⥤ L^{l+1}(C_ℤ Y)` on endomorphisms of `X` (`Lpow.extend`, with
the objects written as `X`). -/
def ext (f : (Lpow l (Y.cz : AddCat)).Mor X X) : (Lpow (l + 1) (Y.cz : AddCat)).Mor X X :=
  (Lpow.extend _ l).map f

lemma ext_comp (f g : (Lpow l (Y.cz : AddCat)).Mor X X) : ext (f ≫ g) = ext f ≫ ext g :=
  (Lpow.extend _ l).map_comp f g

lemma ext_add (f g : (Lpow l (Y.cz : AddCat)).Mor X X) : ext (f + g) = ext f + ext g :=
  (Lpow.extend _ l).map_add

lemma ext_zero : ext (0 : (Lpow l (Y.cz : AddCat)).Mor X X) = 0 :=
  (Lpow.extend _ l).map_zero _ _

lemma ext_chi (P : ℤ → Prop) [DecidablePred P] :
    ext (Lpow.chi X P) = Lpow.chi (l := l + 1) X P :=
  Lpow.extend_chi X P

lemma w_comp_ext (n : ℤ) (f : (Lpow l (Y.cz : AddCat)).Mor X X) :
    Lpow.w l n X ≫ ext f = ext f ≫ Lpow.w l n X :=
  Lpow.w_comm_extend l n f

lemma w_comp_ext_assoc (n : ℤ) (f : (Lpow l (Y.cz : AddCat)).Mor X X)
    (k : (Lpow (l + 1) (Y.cz : AddCat)).Mor X X) :
    Lpow.w l n X ≫ ext f ≫ k = ext f ≫ Lpow.w l n X ≫ k := by
  rw [← assoc, w_comp_ext, assoc]

/-- The symbol `f₀ + f₁ w + f₋₁ w⁻¹` in `L^{l+1}(C_ℤ Y)`, for `fᵢ` in `L^l(C_ℤ Y)`. -/
def symb (f₀ f₁ f₂ : (Lpow l (Y.cz : AddCat)).Mor X X) : (Lpow (l + 1) (Y.cz : AddCat)).Mor X X :=
  ext f₀ + ext f₁ ≫ Lpow.w l 1 X + ext f₂ ≫ Lpow.w l (-1) X

/-- The `wⁿ`-coefficient of `symb f₀ f₁ f₂`. -/
def symbCoeff (f₀ f₁ f₂ : (Lpow l (Y.cz : AddCat)).Mor X X) (n : ℤ) :
    (Lpow l (Y.cz : AddCat)).Mor X X :=
  if n = 0 then f₀ else if n = 1 then f₁ else if n = -1 then f₂ else 0

lemma coeff_symb (f₀ f₁ f₂ : (Lpow l (Y.cz : AddCat)).Mor X X) (n : ℤ) (α : Fin l → ℤ) :
    Lpow.coeff (Fin.cons n α : Fin (l + 1) → ℤ) (symb f₀ f₁ f₂) =
      Lpow.coeff α (symbCoeff f₀ f₁ f₂ n) := by
  rw [symb, Lpow.coeff_add, Lpow.coeff_add, ext, ext, ext, Lpow.coeff_extend,
    Lpow.coeff_extend_comp_w, Lpow.coeff_extend_comp_w, symbCoeff]
  by_cases h0 : n = 0
  · subst h0; simp
  · by_cases h1 : n = 1
    · subst h1; simp
    · by_cases h2 : n = -1
      · subst h2; simp
      · simp [h0, h1, h2, Ne.symm h0, Ne.symm h1, Ne.symm h2]

@[simp] lemma symbCoeff_zero (f₀ f₁ f₂ : (Lpow l (Y.cz : AddCat)).Mor X X) :
    symbCoeff f₀ f₁ f₂ 0 = f₀ := by simp [symbCoeff]

@[simp] lemma symbCoeff_one (f₀ f₁ f₂ : (Lpow l (Y.cz : AddCat)).Mor X X) :
    symbCoeff f₀ f₁ f₂ 1 = f₁ := by simp [symbCoeff]

@[simp] lemma symbCoeff_neg_one (f₀ f₁ f₂ : (Lpow l (Y.cz : AddCat)).Mor X X) :
    symbCoeff f₀ f₁ f₂ (-1) = f₂ := by simp [symbCoeff]

lemma symbCoeff_eq_zero (f₀ f₁ f₂ : (Lpow l (Y.cz : AddCat)).Mor X X) {n : ℤ}
    (hn : n < -1 ∨ 1 < n) : symbCoeff f₀ f₁ f₂ n = 0 := by
  rw [symbCoeff, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

/-- Products of symbols. -/
lemma symb_comp_symb (f₀ f₁ f₂ g₀ g₁ g₂ : (Lpow l (Y.cz : AddCat)).Mor X X) :
    symb f₀ f₁ f₂ ≫ symb g₀ g₁ g₂ =
      symb (f₀ ≫ g₀ + f₁ ≫ g₂ + f₂ ≫ g₁) (f₀ ≫ g₁ + f₁ ≫ g₀) (f₀ ≫ g₂ + f₂ ≫ g₀) +
        ext (f₁ ≫ g₁) ≫ Lpow.w l 2 X + ext (f₂ ≫ g₂) ≫ Lpow.w l (-2) X := by
  simp only [symb, add_comp, comp_add, assoc, ext_add, ext_comp, w_comp_ext_assoc, w_comp_ext,
    Lpow.w_comp_w]
  rw [show (1 : ℤ) + 1 = 2 by norm_num, show (1 : ℤ) + -1 = 0 by norm_num,
    show (-1 : ℤ) + 1 = 0 by norm_num, show (-1 : ℤ) + -1 = -2 by norm_num, Lpow.w_zero,
    comp_id, comp_id]
  abel

/-- A symbol followed by an old-variable map. -/
lemma symb_comp_ext (f₀ f₁ f₂ g : (Lpow l (Y.cz : AddCat)).Mor X X) :
    symb f₀ f₁ f₂ ≫ ext g = symb (f₀ ≫ g) (f₁ ≫ g) (f₂ ≫ g) := by
  simp only [symb, add_comp, assoc, ext_comp, w_comp_ext]

/-- An old-variable map followed by a symbol. -/
lemma ext_comp_symb (f₀ f₁ f₂ g : (Lpow l (Y.cz : AddCat)).Mor X X) :
    ext g ≫ symb f₀ f₁ f₂ = symb (g ≫ f₀) (g ≫ f₁) (g ≫ f₂) := by
  simp only [symb, comp_add, ext_comp, assoc]

end Symbol

/-! ### The window `[-a, a]` and the restriction to it -/

/-- The window `[-a, a]`. -/
def win (a : ℕ) (v : ℤ) : Prop := -(a : ℤ) ≤ v ∧ v ≤ a

instance (a : ℕ) : DecidablePred (win a) := fun v ↦
  inferInstanceAs (Decidable (-(a : ℤ) ≤ v ∧ v ≤ a))

/-- `X|_{[-a, a]}`, a bounded object. -/
abbrev winObj (X : Y.cz) (a : ℕ) : Y.czBdd :=
  ⟨(cut X (win a)).E, bdd_iff.2 ⟨-a, a, fun v hv ↦ isZero_cut_E X _ (by unfold win; omega)⟩⟩

section Window

variable {k : ℕ} {X : Lpow k (Y.cz : AddCat)} (a : ℕ)

/-- The restriction `ι_E s π_E` of `s` to the window. -/
abbrev winRes (s : (Lpow k (Y.cz : AddCat)).Mor X X) :
    (Lpow k (Y.cz : AddCat)).Mor (cut X (win a)).E (cut X (win a)).E :=
  (Lpow.incl (Y.cz : AddCat) k).map (cut X (win a)).ιE ≫ s ≫
    (Lpow.incl (Y.cz : AddCat) k).map (cut X (win a)).πE

variable (k) in
/-- `L^k` of the inclusion `C_ℤ^{bdd} Y ⊂ C_ℤ Y` is fully faithful. -/
def bddFF : (Lpow.map k (bddIncl Y)).FullyFaithful :=
  Lpow.fullyFaithfulMap k (F := bddIncl Y) (ObjectProperty.fullyFaithfulι (CZ.bdd Y))

/-- The window restriction, as a morphism of `L^k(C_ℤ^{bdd} Y)`. -/
def bddRes (s : (Lpow k (Y.cz : AddCat)).Mor X X) :
    (Lpow k (Y.czBdd : AddCat)).Mor (winObj X a) (winObj X a) :=
  (bddFF (Y := Y) k).preimage (winRes a s)

lemma map_bddRes (s : (Lpow k (Y.cz : AddCat)).Mor X X) :
    (Lpow.map k (bddIncl Y)).map (bddRes a s) = winRes a s :=
  (bddFF k).map_preimage _

lemma bddRes_idem {s : (Lpow k (Y.cz : AddCat)).Mor X X}
    (hs : winRes a s ≫ winRes a s = winRes a s) : bddRes a s ≫ bddRes a s = bddRes a s :=
  (bddFF k).map_injective (by rw [Functor.map_comp, map_bddRes]; exact hs)

end Window

lemma coeff_bddRes_symb {X : Lpow l (Y.cz : AddCat)} (a : ℕ)
    (f₀ f₁ f₂ : (Lpow l (Y.cz : AddCat)).Mor X X) (n : ℤ) (α : Fin l → ℤ) :
    Lpow.coeff (Fin.cons n α : Fin (l + 1) → ℤ)
      ((Lpow.map (l + 1) (bddIncl Y)).map (bddRes a (symb f₀ f₁ f₂))) =
      Lpow.coeff α (winRes a (symbCoeff f₀ f₁ f₂ n)) := by
  rw [map_bddRes]
  change Lpow.coeff (l := l + 1) (D := (Y.cz : AddCat)) (X := (cut X (win a)).E)
    (Y := (cut X (win a)).E) _ (winRes a (symb f₀ f₁ f₂)) = _
  rw [Lpow.coeff_incl_comp, Lpow.coeff_comp_incl, coeff_symb, Lpow.coeff_incl_comp,
    Lpow.coeff_comp_incl]

end CZ.Corner

end

end HSFormal.LTheory
