import HSFormal.LTheory.Model.NegK.High.Germ

/-!
# Periodization and Lemma F (NegKHigh, module N5)

`blueprint/negK-high.md` §2 "Periodization", §3.5 (Lemma F), §7 row N5.

* `CZ.periodize Y : L Y ⥤ C_ℤ Y` (`Π_Y`): `M ↦` the constant object `(M)_r`, and
  `(Π f)_{r', r} = coeff_{r' - r} f` (`periodize_map_apply`, `rfl`).  It is additive and faithful,
  and `Π f` has propagation `≤ degBound f` (`propLE_periodize`).  Its `Lpow` lift
  `Lpow.map l (CZ.periodize Y) : L^{l+1} Y ⥤ L^l(C_ℤ Y)` needs no new definition
  (`L^{l+1} Y = L^l (L Y)` is `rfl`).
* **Lemma F** (`CZ.Lpow.stablyIso_zero_periodize_pos`, `karAbsorbs_periodize_pos`): for every Kar
  object `(M, e)` of `L^l(L⁺ Y)`, the periodized face `Π(ι⁺ e)` is stably zero, indeed absorbed
  by a free object of `L^l(C_ℤ Y)`.

*Proof of Lemma F* (a variant of the blueprint's triangular conjugation).  `P = Π(ι⁺ e)` has no
entries from `r ≥ 0` to `r' < 0` (`chi_comp_periodize_comp_chi`).  So `P = P' + c` with
`P' = χ P χ + χ' P χ'` (`χ` the cut at `r ≥ 0`, `χ' = 1 - χ`) idempotent and `c = χ' P χ`
supported near `0`, in particular left-supported.  The germ lemma gives `(M, P) ∼ (M, P')`, and
`P'` is diagonal for the cut, with halves on the two half-lines, absorbed by Lemma H
(`karAbsorbs_of_splitting`).  No explicit conjugation is needed.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive Idempotents

noncomputable section

/-! ### The periodization functor `Π_Y : L Y ⥤ C_ℤ Y` -/

namespace CZ

variable (Y : InvCat)

/-- The constant object `(M)_{r ∈ ℤ}` of `C_ℤ Y`. -/
@[instance_reducible]
def periodObj (M : Y) : Y.cz := ⟨fun _ ↦ M⟩

variable {Y}

/-- A bound for the absolute degrees of the monomials of a Laurent morphism. -/
def degBound {M N : Laurent (Y : AddCat)} (f : (Laurent (Y : AddCat)).Mor M N) : ℕ :=
  (Laurent.support f).sup Int.natAbs

lemma coeff_eq_zero_of_degBound_lt {M N : Laurent (Y : AddCat)}
    {f : (Laurent (Y : AddCat)).Mor M N} {n : ℤ} (h : (degBound f : ℤ) < |n|) :
    Laurent.coeff n f = 0 := by
  by_contra hne
  have h₁ := Finset.le_sup (f := Int.natAbs) (Laurent.mem_support_iff.mpr hne)
  have h₂ : ((n.natAbs : ℕ) : ℤ) = |n| := Int.natCast_natAbs n
  have h₃ : ((n.natAbs : ℕ) : ℤ) ≤ (degBound f : ℤ) := by exact_mod_cast h₁
  omega

lemma support_subset_Icc {M N : Laurent (Y : AddCat)} (f : (Laurent (Y : AddCat)).Mor M N) :
    Laurent.support f ⊆ Finset.Icc (-(degBound f : ℤ)) (degBound f) := fun n hn ↦ by
  have h₁ := Finset.le_sup (f := Int.natAbs) hn
  have h₂ : ((n.natAbs : ℕ) : ℤ) = |n| := Int.natCast_natAbs n
  have h₃ : ((n.natAbs : ℕ) : ℤ) ≤ (degBound f : ℤ) := by exact_mod_cast h₁
  rw [Finset.mem_Icc]
  constructor <;> [have := neg_abs_le n; have := le_abs_self n] <;> omega

/-- The matrix `(Π f)_{r', r} = coeff_{r' - r} f`. -/
def periodizeMat {M N : Laurent (Y : AddCat)} (f : (Laurent (Y : AddCat)).Mor M N) :
    Mat (periodObj Y M) (periodObj Y N) :=
  fun r' r ↦ Laurent.coeff (r' - r) f

lemma propLE_periodizeMat {M N : Laurent (Y : AddCat)} (f : (Laurent (Y : AddCat)).Mor M N) :
    PropLE (periodizeMat f) (degBound f) := fun _ _ h ↦ coeff_eq_zero_of_degBound_lt h

/-- `Π f` as a morphism of `C_ℤ Y`. -/
def periodizeHom {M N : Laurent (Y : AddCat)} (f : (Laurent (Y : AddCat)).Mor M N) :
    periodObj Y M ⟶ periodObj Y N :=
  ⟨periodizeMat f, degBound f, propLE_periodizeMat f⟩

variable (Y) in
/-- **The periodization `Π_Y : L Y ⥤ C_ℤ Y`**: `M ↦ (M)_r`, `(Π f)_{r', r} = coeff_{r' - r} f`. -/
@[instance_reducible]
def periodize : (Laurent (Y : AddCat)).carrier ⥤ (Y.cz : AddCat).carrier where
  obj M := periodObj Y M
  map f := periodizeHom f
  map_id M := hom_ext fun w v ↦ by
    change Laurent.coeff (w - v) (𝟙 M) = _
    rw [Laurent.coeff_id]
    by_cases h : v = w
    · subst h; rw [ite_eq_left (by ring), id_apply_self]; rfl
    · rw [ite_eq_right (by omega), id_apply_ne _ h]
  map_comp {L M N} f g := hom_ext fun u v ↦ by
    change Laurent.coeff (u - v) (f ≫ g) = (periodizeHom f ≫ periodizeHom g).1 u v
    rw [Laurent.coeff_comp f g _ _ (support_subset_Icc f),
      comp_apply_left (periodizeHom f) (propLE_periodizeMat f)]
    refine Finset.sum_nbij' (fun i ↦ i + v) (fun w ↦ w - v) (fun i hi ↦ ?_) (fun w hw ↦ ?_)
      (fun i _ ↦ by ring) (fun w _ ↦ by ring) (fun i _ ↦ ?_)
    · simp only [Finset.mem_Icc, window] at hi ⊢; omega
    · simp only [Finset.mem_Icc, window] at hw ⊢; omega
    · change Laurent.coeff i f ≫ Laurent.coeff (u - v - i) g =
        Laurent.coeff (i + v - v) f ≫ Laurent.coeff (u - (i + v)) g
      rw [show i + v - v = i by ring, show u - (i + v) = u - v - i by ring]

@[simp] lemma periodize_obj (M : Laurent (Y : AddCat)) : (periodize Y).obj M = periodObj Y M := rfl

lemma periodize_map_apply {M N : Laurent (Y : AddCat)} (f : (Laurent (Y : AddCat)).Mor M N)
    (r' r : ℤ) : ((periodize Y).map f).1 r' r = Laurent.coeff (r' - r) f := rfl

lemma propLE_periodize {M N : Laurent (Y : AddCat)} (f : (Laurent (Y : AddCat)).Mor M N) :
    PropLE ((periodize Y).map f).1 (degBound f) :=
  propLE_periodizeMat f

instance : (periodize Y).Additive where
  map_add {_ _ f g} := hom_ext fun _ _ ↦ Laurent.coeff_add _ f g

instance : (periodize Y).Faithful where
  map_injective {M N f g} h := Laurent.ext fun n ↦ by
    have := congrArg (fun φ : periodObj Y M ⟶ periodObj Y N ↦ φ.1 n 0) h
    simpa [periodize_map_apply] using this

/-- **No entries from `r ≥ 0` to `r' < 0`** for `Π g`, `g` without negative coefficients. -/
lemma cut_comp_periodize_comp_cut {M N : Laurent (Y : AddCat)}
    (g : (Laurent (Y : AddCat)).Mor M N) (hg : ∀ n < 0, Laurent.coeff n g = 0) :
    (cut (periodObj Y M) (0 ≤ ·)).idem ≫ (periodize Y).map g ≫
      (cut (periodObj Y N) (· < 0)).idem = 0 := by
  rw [← assoc]
  refine hom_ext fun w v ↦ ?_
  rw [cut_idem, cut_idem, comp_diag_apply, diag_comp_apply, zero_apply]
  by_cases hv : 0 ≤ v
  · by_cases hw : w < 0
    · rw [periodize_map_apply, hg _ (by omega), comp_zero, zero_comp]
    · rw [ite_eq_right hw, comp_zero]
  · rw [ite_eq_right hv, zero_comp, zero_comp]

lemma cut_add_cut (X : Y.cz) :
    (cut X (0 ≤ ·)).idem + (cut X (· < 0)).idem = 𝟙 X := by
  rw [cut_idem, cut_idem, ← diag_add, ← diag_id]
  exact diag_ext fun v ↦ by by_cases h : 0 ≤ v <;> simp [h, not_lt.mpr, lt_of_not_ge]

lemma cut_comp_cut (X : Y.cz) :
    (cut X (0 ≤ ·)).idem ≫ (cut X (· < 0)).idem = 0 := by
  rw [cut_idem, cut_idem, diag_comp_diag, ← diag_zero]
  exact diag_ext fun v ↦ by by_cases h : 0 ≤ v <;> simp [h, not_lt.mpr, lt_of_not_ge]

end CZ

/-! ### Lemma F -/

namespace CZ.Lpow

variable {Y : InvCat} {l : ℕ}

/-- `Π(ι⁺ e)` in `L^l(C_ℤ Y)`, for `e` in `L^l(L⁺ Y)`. -/
abbrev periodizePos {M N : Lpow l (LaurentPos (Y : AddCat))}
    (e : (Lpow l (LaurentPos (Y : AddCat))).Mor M N) : (Lpow l (Y.cz : AddCat)).Mor
      ((CZ.periodize Y).obj M) ((CZ.periodize Y).obj N) :=
  (Lpow.map l (CZ.periodize Y)).map ((Lpow.map l (LaurentPos.incl (Y : AddCat))).map e)

lemma chi_comp_periodizePos_comp_chi {M N : Lpow l (LaurentPos (Y : AddCat))}
    (e : (Lpow l (LaurentPos (Y : AddCat))).Mor M N) :
    chi ((CZ.periodize Y).obj M) (0 ≤ ·) ≫ periodizePos e ≫
      chi ((CZ.periodize Y).obj N) (· < 0) = 0 :=
  Lpow.ext fun γ ↦ by
    unfold periodizePos
    rw [chi, chi, Lpow.coeff_incl_comp, Lpow.coeff_comp_incl, Lpow.coeff_map (CZ.periodize Y),
      Lpow.coeff_map (LaurentPos.incl (Y : AddCat)), Lpow.coeff_zero]
    exact CZ.cut_comp_periodize_comp_cut _ fun n hn ↦ LaurentPos.coeff_incl_map_neg _ hn

open ZeroObject in
/-- **Lemma F** (`blueprint/negK-high.md` §3.5): for every Kar object `(M, e)` of `L^l(L⁺ Y)`, the
periodized face `Π(ι⁺ e)` is stably zero in `Karoubi (L^l(C_ℤ Y))`. -/
theorem stablyIso_zero_periodize_pos {M : Lpow l (LaurentPos (Y : AddCat))}
    {e : (Lpow l (LaurentPos (Y : AddCat))).Mor M M} (he : e ≫ e = e) :
    StablyIso (⟨_, periodizePos e, by rw [← Functor.map_comp, ← Functor.map_comp, he]⟩ :
      Karoubi (Lpow l (Y.cz : AddCat)).carrier) 0 := by
  set X : Lpow l (Y.cz : AddCat) := (CZ.periodize Y).obj M with hX
  set P : End X := periodizePos e with hP_def
  have hP : P ≫ P = P := by rw [hP_def, ← Functor.map_comp, ← Functor.map_comp, he]
  let ι := Lpow.incl (Y.cz : AddCat) l
  -- the cut idempotents, in `End X`
  set x : End X := chi X (0 ≤ ·) with hx_def
  set y : End X := chi X (· < 0) with hy_def
  have hy : y = 1 - x := by
    rw [eq_sub_iff_add_eq, add_comm, hx_def, hy_def, chi, chi, ← Functor.map_add, CZ.cut_add_cut]
    exact ι.map_id _
  have hxx : x * x = x := chi_idem _ X
  have htri : (1 - x) * P * x = 0 := by
    rw [← hy]
    exact chi_comp_periodizePos_comp_chi e
  have hPP : P * P = P := hP
  -- `P' = xPx + (1-x)P(1-x)`
  set P' : End X := x * P * x + (1 - x) * P * (1 - x) with hP'_def
  have hA : x * P * x * (x * P * x) = x * P * x := by
    calc x * P * x * (x * P * x) = x * P * (x * x) * P * x := by noncomm_ring
      _ = x * P * x * P * x := by rw [hxx]
      _ = x * (P * P) * x - x * P * ((1 - x) * P * x) := by noncomm_ring
      _ = x * P * x := by rw [htri, hPP, mul_zero, sub_zero]
  have hDd : (1 - x) * P * (1 - x) * ((1 - x) * P * (1 - x)) = (1 - x) * P * (1 - x) := by
    calc (1 - x) * P * (1 - x) * ((1 - x) * P * (1 - x))
        = (1 - x) * (P * P) * (1 - x) - (1 - x) * P * ((x - x * x) * P) * (1 - x) -
            ((1 - x) * P * x) * P * (1 - x) := by noncomm_ring
      _ = (1 - x) * P * (1 - x) := by
          simp only [htri, hPP, hxx, sub_self, zero_mul, mul_zero, sub_zero]
  have hAD : x * P * x * ((1 - x) * P * (1 - x)) = 0 := by
    calc x * P * x * ((1 - x) * P * (1 - x)) = x * P * (x - x * x) * P * (1 - x) := by
          noncomm_ring
      _ = 0 := by rw [hxx, sub_self, mul_zero, zero_mul, zero_mul]
  have hDA : (1 - x) * P * (1 - x) * (x * P * x) = 0 := by
    calc (1 - x) * P * (1 - x) * (x * P * x) = (1 - x) * P * (x - x * x) * P * x := by
          noncomm_ring
      _ = 0 := by rw [hxx, sub_self, mul_zero, zero_mul, zero_mul]
  have hP'P' : P' * P' = P' := by
    rw [hP'_def, mul_add, add_mul, add_mul, hA, hDd, hAD, hDA, add_zero, zero_add]
  have hP'i : P' ≫ P' = P' := hP'P'
  -- `P - P' = x P (1 - x)` is left-supported
  have hdiff : P - P' = x * P * (1 - x) := by
    have h : P = (x + (1 - x)) * P * (x + (1 - x)) := by noncomm_ring
    conv_lhs => rw [h]
    rw [hP'_def]
    calc (x + (1 - x)) * P * (x + (1 - x)) - (x * P * x + (1 - x) * P * (1 - x))
        = x * P * (1 - x) + (1 - x) * P * x := by noncomm_ring
      _ = x * P * (1 - x) := by rw [htri, add_zero]
  have hleft : LeftSupp (P - P') := by
    rw [hdiff]
    have h1 : LeftSupp ((1 : End X) - x) := by
      rw [← hy]
      exact ⟨-1, (by rw [SuppIn, chi_idem, chi_idem] :
        SuppIn (· < 0) (chi X (· < 0))).mono fun v hv ↦ by omega⟩
    exact h1.comp_right (P ≫ x)
  have hstep := germ_left hP hP'i hleft
  -- `(X, P')` is absorbed: it is diagonal for the cut at `0`
  let σ := (CZ.cut X (0 ≤ ·)).map ι
  have hσ : σ.idem = x := by rw [Splitting.map_idem]; rfl
  have hxP' : x * P' = x * P * x := by
    rw [hP'_def]
    calc x * (x * P * x + (1 - x) * P * (1 - x))
        = (x * x) * P * x + (x - x * x) * P * (1 - x) := by noncomm_ring
      _ = x * P * x := by rw [hxx, sub_self, zero_mul, zero_mul, add_zero]
  have hP'x : P' * x = x * P * x := by
    rw [hP'_def]
    calc (x * P * x + (1 - x) * P * (1 - x)) * x
        = x * P * (x * x) + (1 - x) * P * (x - x * x) := by noncomm_ring
      _ = x * P * x := by rw [hxx, sub_self, mul_zero, add_zero]
  have hc : P' ≫ σ.idem = σ.idem ≫ P' := by
    rw [hσ]
    change x * P' = P' * x
    rw [hxP', hP'x]
  obtain ⟨F₁, hF₁⟩ := karAbsorbs_lpow_of_posHalf l (M := (CZ.cut X (0 ≤ ·)).E)
    ⟨0, fun v hv ↦ CZ.isZero_cut_E _ _ (by omega)⟩ (SplitKar.idem_E σ hP'i hc)
  obtain ⟨F₂, hF₂⟩ := karAbsorbs_lpow_of_negHalf l (M := (CZ.cut X (0 ≤ ·)).U)
    ⟨-1, fun v hv ↦ CZ.isZero_cut_U _ _ (by omega)⟩ (SplitKar.idem_U σ hP'i hc)
  exact hstep.trans (StablyIso.of_karAbsorbs (P := ⟨X, P', hP'i⟩)
    (karAbsorbs_of_splitting σ hc hF₁ hF₂))

/-- **Lemma F, absorbing form**: `Π(ι⁺ e)` is absorbed by a free object of `L^l(C_ℤ Y)`. -/
theorem karAbsorbs_periodize_pos {M : Lpow l (LaurentPos (Y : AddCat))}
    {e : (Lpow l (LaurentPos (Y : AddCat))).Mor M M} (he : e ≫ e = e) :
    ∃ F : Lpow l (Y.cz : AddCat), KarAbsorbs (periodizePos e) F := by
  have hP : periodizePos e ≫ periodizePos e = periodizePos e := by
    rw [← Functor.map_comp, ← Functor.map_comp, he]
  obtain ⟨F, F', h⟩ := (stablyIso_zero_iff _).mp (stablyIso_zero_periodize_pos he)
  obtain ⟨G, hG⟩ := karAbsorbs_lpow_id F
  obtain ⟨G', hG'⟩ := karAbsorbs_lpow_id F'
  exact ⟨_, karAbsorbs_of_karStablyFree hP h hG hG'⟩

end CZ.Lpow

end

end HSFormal.LTheory
