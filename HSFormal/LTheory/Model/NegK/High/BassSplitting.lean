import HSFormal.LTheory.Model.NegK.High.CornerPZ

/-!
# Theorem B, part 2: the controlled Bass splitting (NegKHigh, N8)

`blueprint/negK-high.md` §3.1, via the one-dimensional `P_Z` variant of
`blueprint/negK-high-review.md` (replacing N6 `Corner` / N7 `Regroup`).

Let `(X, p)` be a Kar object of `L^l(C_ℤ Y)`, `b` a propagation bound of `p`, `h = χ_{r ≥ 0}`,
`q = 1 - p`, and (operator notation, `x * y = y ≫ x`)

  `P₀ = php + qhq`, `P₁ = phq`, `P₋₁ = qhp`  (so `h = P₀ + P₁ + P₋₁`).

`φ = hp - ph` is supported in `[-b, b]`, so `P₋₁ = φp` and `P₁ = -pφ` are supported in the
window `W = [-2b, 2b]`.  The **symbol** `P(w) = P₀ + P₁ w + P₋₁ w⁻¹` (`= h + (w - 1) phq +
(w⁻¹ - 1) qhp`) is an idempotent of `L^{l+1}(C_ℤ Y)` commuting with `χ_W`; its restriction to
`X_W`, collapsed along `W` (`CZ.Window.sumF`), is the Kar object `E = (ΣX_W, ē)` of `L^{l+1} Y`.

Write `C = (ΣX_W)_{r ∈ ℤ}` for the object of `Π(E)` and `Π = Π(ē)`.  With `u_k = U_k ι_E : C → X`
(the copy `r = k`, unfolded) and `us_k = π_E Us_k`, `ζ₊ = χ^C_{r ≥ 1}`, `ζ₋ = χ^C_{r ≤ 0}`,
`χ' = χ_{r > 2b}` and `K = p + qhq`, the idempotent `Q` of `T = X ⊕ C` is

  `Q = [[K - χ', u₁ ≫ P₋₁], [P₁ ≫ us₁, ζ₊ Π ζ₊]]`.

`Q - (p ⊕ 0)` is right-supported and `Q - (0 ⊕ Π)` is left-supported, so the germ lemma
(`germ_right'`, `germ_left'`) gives `(X, p) ∼ (T, Q) ∼ (C, Π) = Π(E)`.

**Theorem B** (`theoremB : TheoremBStatement`).
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive Idempotents

noncomputable section

namespace BassPZ

/-! ### Ring identities -/

section Ring

variable {R : Type*} [Ring R] {p h : R} (hp : p * p = p) (hh : h * h = h)
include hp hh

lemma ring_KK : (p + (1 - p) * h * (1 - p)) * (p + (1 - p) * h * (1 - p)) +
    (1 - p) * h * p * (p * h * (1 - p)) = p + (1 - p) * h * (1 - p) := by
  have hp' : ∀ x, p * (p * x) = p * x := fun x ↦ by rw [← mul_assoc, hp]
  have hh' : ∀ x, h * (h * x) = h * x := fun x ↦ by rw [← mul_assoc, hh]
  noncomm_ring [hp, hp', hh, hh']

lemma ring_KPm : (p + (1 - p) * h * (1 - p)) * ((1 - p) * h * p) +
    (1 - p) * h * p * (p * h * p + (1 - p) * h * (1 - p)) = (1 - p) * h * p := by
  have hp' : ∀ x, p * (p * x) = p * x := fun x ↦ by rw [← mul_assoc, hp]
  have hh' : ∀ x, h * (h * x) = h * x := fun x ↦ by rw [← mul_assoc, hh]
  noncomm_ring [hp, hp', hh, hh']

lemma ring_P1K : p * h * (1 - p) * (p + (1 - p) * h * (1 - p)) +
    (p * h * p + (1 - p) * h * (1 - p)) * (p * h * (1 - p)) = p * h * (1 - p) := by
  have hp' : ∀ x, p * (p * x) = p * x := fun x ↦ by rw [← mul_assoc, hp]
  have hh' : ∀ x, h * (h * x) = h * x := fun x ↦ by rw [← mul_assoc, hh]
  noncomm_ring [hp, hp', hh, hh']

lemma ring_P0P0 : (p * h * p + (1 - p) * h * (1 - p)) * (p * h * p + (1 - p) * h * (1 - p)) +
    (1 - p) * h * p * (p * h * (1 - p)) + p * h * (1 - p) * ((1 - p) * h * p) =
      p * h * p + (1 - p) * h * (1 - p) := by
  have hp' : ∀ x, p * (p * x) = p * x := fun x ↦ by rw [← mul_assoc, hp]
  have hh' : ∀ x, h * (h * x) = h * x := fun x ↦ by rw [← mul_assoc, hh]
  noncomm_ring [hp, hp', hh, hh']

lemma ring_P0P1 : p * h * (1 - p) * (p * h * p + (1 - p) * h * (1 - p)) +
    (p * h * p + (1 - p) * h * (1 - p)) * (p * h * (1 - p)) = p * h * (1 - p) := by
  have hp' : ∀ x, p * (p * x) = p * x := fun x ↦ by rw [← mul_assoc, hp]
  have hh' : ∀ x, h * (h * x) = h * x := fun x ↦ by rw [← mul_assoc, hh]
  noncomm_ring [hp, hp', hh, hh']

lemma ring_P0Pm : (1 - p) * h * p * (p * h * p + (1 - p) * h * (1 - p)) +
    (p * h * p + (1 - p) * h * (1 - p)) * ((1 - p) * h * p) = (1 - p) * h * p := by
  have hp' : ∀ x, p * (p * x) = p * x := fun x ↦ by rw [← mul_assoc, hp]
  have hh' : ∀ x, h * (h * x) = h * x := fun x ↦ by rw [← mul_assoc, hh]
  noncomm_ring [hp, hp', hh, hh']

lemma ring_PmPm : (1 - p) * h * p * ((1 - p) * h * p) = 0 := by
  have hp' : ∀ x, p * (p * x) = p * x := fun x ↦ by rw [← mul_assoc, hp]
  have hh' : ∀ x, h * (h * x) = h * x := fun x ↦ by rw [← mul_assoc, hh]
  noncomm_ring [hp, hp', hh, hh']

lemma ring_P1P1 : p * h * (1 - p) * (p * h * (1 - p)) = 0 := by
  have hp' : ∀ x, p * (p * x) = p * x := fun x ↦ by rw [← mul_assoc, hp]
  have hh' : ∀ x, h * (h * x) = h * x := fun x ↦ by rw [← mul_assoc, hh]
  noncomm_ring [hp, hp', hh, hh']

omit hh in
lemma ring_Pm_eq : (1 - p) * h * p = (h * p - p * h) * p := by
  have hp' : ∀ x, p * (p * x) = p * x := fun x ↦ by rw [← mul_assoc, hp]
  noncomm_ring [hp, hp']

omit hh in
lemma ring_P1_eq : p * h * (1 - p) = -(p * (h * p - p * h)) := by
  have hp' : ∀ x, p * (p * x) = p * x := fun x ↦ by rw [← mul_assoc, hp]
  noncomm_ring [hp, hp']

omit hp hh in
lemma ring_P0_eq : p * h * p + (1 - p) * h * (1 - p) =
    h - p * h * (1 - p) - (1 - p) * h * p := by
  noncomm_ring

omit hh in
/-- `K χ' = χ'` from `h' χ' = 0`, `h' p χ' = 0` (`h' = 1 - h`). -/
lemma ring_K_tail {t h' : R} (hh' : h + h' = 1) (h1 : h' * t = 0) (h2 : h' * (p * t) = 0) :
    (p + (1 - p) * h * (1 - p)) * t = t := by
  have hp' : ∀ x, p * (p * x) = p * x := fun x ↦ by rw [← mul_assoc, hp]
  have e : h = 1 - h' := eq_sub_of_add_eq hh'
  subst e
  have e2 : (p + (1 - p) * (1 - h') * (1 - p)) * t =
      t - (1 - p) * (h' * t) + (1 - p) * (h' * (p * t)) := by
    noncomm_ring [hp, hp']
  rw [e2, h1, h2, mul_zero, sub_zero, add_zero]

omit hh in
/-- `χ' K = χ'` from `χ' h' = 0`, `χ' p h' = 0`. -/
lemma ring_tail_K {t h' : R} (hh' : h + h' = 1) (h1 : t * h' = 0) (h2 : t * (p * h') = 0) :
    t * (p + (1 - p) * h * (1 - p)) = t := by
  have hp' : ∀ x, p * (p * x) = p * x := fun x ↦ by rw [← mul_assoc, hp]
  have e : h = 1 - h' := eq_sub_of_add_eq hh'
  subst e
  have e2 : t * (p + (1 - p) * (1 - h') * (1 - p)) =
      t - (t * h') * (1 - p) + (t * (p * h')) * (1 - p) := by
    noncomm_ring [hp, hp']
  rw [e2, h1, h2, zero_mul, sub_zero, add_zero]

end Ring

/-! ### Cut idempotents in `L^l(C_ℤ Y)` -/

section Chi

variable {Y : InvCat} {l : ℕ} (X : Lpow l (Y.cz : AddCat))

open CZ.Lpow

lemma chi_comp_chi (P P' : ℤ → Prop) [DecidablePred P] [DecidablePred P'] :
    chi X P ≫ chi X P' = chi X (fun v ↦ P v ∧ P' v) := by
  rw [chi, chi, chi, ← Functor.map_comp, CZ.cut_idem, CZ.cut_idem, CZ.cut_idem,
    CZ.diag_comp_diag]
  congr 1
  exact CZ.diag_ext fun v ↦ by by_cases h : P v <;> by_cases h' : P' v <;> simp [h, h']

lemma chi_comm (P P' : ℤ → Prop) [DecidablePred P] [DecidablePred P'] :
    chi X P ≫ chi X P' = chi X P' ≫ chi X P := by
  rw [chi_comp_chi, chi_comp_chi]
  congr 1
  funext v
  exact propext and_comm

lemma chi_comp_chi_eq_zero {P P' : ℤ → Prop} [DecidablePred P] [DecidablePred P']
    (h : ∀ v, P v → P' v → False) : chi X P ≫ chi X P' = 0 := by
  rw [chi, chi, ← Functor.map_comp, CZ.cut_idem, CZ.cut_idem, CZ.diag_comp_diag,
    ← Functor.map_zero (Lpow.incl (Y.cz : AddCat) l) X X]
  congr 1
  rw [← CZ.diag_zero]
  exact CZ.diag_ext fun v ↦ by
    by_cases hP : P v
    · by_cases hP' : P' v
      · exact absurd (h v hP hP') id
      · simp [hP, hP']
    · simp [hP]

lemma chi_add_chi {P P' : ℤ → Prop} [DecidablePred P] [DecidablePred P']
    (h : ∀ v, P' v ↔ ¬ P v) : chi X P + chi X P' = 𝟙 X := by
  rw [chi, chi, ← Functor.map_add, CZ.cut_idem, CZ.cut_idem, ← CZ.diag_add]
  refine Eq.trans (congrArg _ (CZ.diag_ext (d' := fun v ↦ 𝟙 _) fun v ↦ ?_))
    ((Lpow.incl (Y.cz : AddCat) l).map_id X)
  by_cases hP : P v <;> simp [hP, h v]

lemma suppIn_chi (P : ℤ → Prop) [DecidablePred P] : SuppIn P (chi X P) := by
  rw [SuppIn, chi_idem, chi_idem]

variable {X}

/-- Supports from vanishing entries. -/
lemma suppIn_of_coeff {Z : Lpow l (Y.cz : AddCat)} {f : (Lpow l (Y.cz : AddCat)).Mor X Z}
    {P : ℤ → Prop} [DecidablePred P]
    (hf : ∀ γ w v, ¬(P w ∧ P v) → (Lpow.coeff γ f).1 w v = 0) : SuppIn P f :=
  Lpow.ext fun γ ↦ by
    rw [chi, chi, Lpow.coeff_incl_comp, Lpow.coeff_comp_incl]
    refine CZ.hom_ext fun w v ↦ ?_
    rw [CZ.cut_idem, CZ.cut_idem, CZ.diag_comp_apply, CZ.comp_diag_apply]
    by_cases hv : P v
    · by_cases hw : P w
      · rw [ite_eq_left hv, ite_eq_left hw, id_comp, comp_id]
      · rw [ite_eq_right hw, comp_zero, comp_zero, hf γ w v (fun h ↦ hw h.1)]
    · rw [ite_eq_right hv, zero_comp, hf γ w v (fun h ↦ hv h.2)]

/-- **The commutator `[h, p]` is supported in `[-b, b]`.** -/
lemma suppIn_comm {p : (Lpow l (Y.cz : AddCat)).Mor X X} {b : ℕ} (hb : PropLE' p b) :
    SuppIn (CZ.Corner.win b) (p ≫ chi X (0 ≤ ·) - chi X (0 ≤ ·) ≫ p) :=
  suppIn_of_coeff fun γ w v hwv ↦ by
    unfold CZ.Corner.win at hwv
    rw [Lpow.coeff_sub, CZ.sub_apply, chi, Lpow.coeff_comp_incl, Lpow.coeff_incl_comp,
      CZ.cut_idem, CZ.comp_diag_apply, CZ.diag_comp_apply]
    have hz : ((0 : ℤ) ≤ w ↔ (0 : ℤ) ≤ v) ∨ (Lpow.coeff γ p).1 w v = 0 := by
      by_cases hw : (0 : ℤ) ≤ w <;> by_cases hv : (0 : ℤ) ≤ v
      · exact Or.inl (iff_of_true hw hv)
      · exact Or.inr (hb γ w v (by rw [lt_abs]; omega))
      · exact Or.inr (hb γ w v (by rw [lt_abs]; omega))
      · exact Or.inl (iff_of_false hw hv)
    rcases hz with hz | hz
    · by_cases hw : (0 : ℤ) ≤ w
      · rw [ite_eq_left hw, ite_eq_left (hz.mp hw), comp_id, id_comp, sub_self]
      · rw [ite_eq_right hw, ite_eq_right (fun h ↦ hw (hz.mpr h)), comp_zero, zero_comp,
          sub_self]
    · rw [hz, zero_comp, comp_zero, sub_self]

end Chi

/-! ### The data of the splitting -/

section Data

variable {Y : InvCat} {l : ℕ} (X : Lpow l (Y.cz : AddCat))

open CZ.Lpow CZ.Corner CZ.Window

/-- `h = χ_{r ≥ 0}`. -/
abbrev hE : End X := chi X (0 ≤ ·)

/-- `1 - h = χ_{r < 0}`. -/
abbrev hE' : End X := chi X (· < 0)

/-- `χ' = χ_{r ≥ 2b + 1}`. -/
abbrev tl (b : ℕ) : End X := chi X ((((2 * b : ℕ) : ℤ) + 1) ≤ ·)

/-- `1 - χ' = χ_{r ≤ 2b}`. -/
abbrev hd (b : ℕ) : End X := chi X (· ≤ ((2 * b : ℕ) : ℤ))

/-- `χ_W`, `W = [-2b, 2b]`. -/
abbrev χW (b : ℕ) : End X := chi X (win (2 * b))

/-- `X_W` as a bounded object. -/
abbrev ZW (b : ℕ) : Y.czBdd := winObj X (2 * b)

/-- `C = (ΣX_W)_{r ∈ ℤ}`. -/
abbrev CC (b : ℕ) : Lpow l (Y.cz : AddCat) := CZ.periodObj Y (pt (ZW X b))

/-- `u_k : C → X`, the copy `r = k` of `ΣX_W`, unfolded into `X_W ⊂ X`. -/
def uu (b : ℕ) (k : ℤ) : (Lpow l (Y.cz : AddCat)).Mor (CC X b) X :=
  (Lpow.incl (Y.cz : AddCat) l).map (U (ZW X b) k) ≫
    (Lpow.incl (Y.cz : AddCat) l).map (CZ.cut X (win (2 * b))).ιE

/-- `us_k : X → C`, `X_W` folded into the copy `r = k`. -/
def us (b : ℕ) (k : ℤ) : (Lpow l (Y.cz : AddCat)).Mor X (CC X b) :=
  (Lpow.incl (Y.cz : AddCat) l).map (CZ.cut X (win (2 * b))).πE ≫
    (Lpow.incl (Y.cz : AddCat) l).map (Us (ZW X b) k)

/-- `ζ₊ = χ^C_{r ≥ 1}`. -/
abbrev zp (b : ℕ) : End (CC X b) := chi (CC X b) (1 ≤ ·)

/-- `ζ₋ = χ^C_{r ≤ 0}`. -/
abbrev zm (b : ℕ) : End (CC X b) := chi (CC X b) (· ≤ 0)

variable {X}

/-- `P₀ = php + qhq`. -/
def P0 (p : End X) : End X := p * hE X * p + (1 - p) * hE X * (1 - p)

/-- `P₁ = phq`. -/
def P1 (p : End X) : End X := p * hE X * (1 - p)

/-- `P₋₁ = qhp`. -/
def Pm (p : End X) : End X := (1 - p) * hE X * p

/-- `K = p + qhq`. -/
def KK (p : End X) : End X := p + (1 - p) * hE X * (1 - p)

/-- The corner `A = K - χ'`. -/
def AA (p : End X) (b : ℕ) : End X := KK p - tl X b

/-- The symbol `P(w) = P₀ + P₁ w + P₋₁ w⁻¹` in `L^{l+1}(C_ℤ Y)`. -/
def sy (p : End X) : (Lpow (l + 1) (Y.cz : AddCat)).Mor X X := symb (P0 p) (P1 p) (Pm p)

/-- `P(w)` restricted to the window, in `L^{l+1}(C_ℤ^{bdd} Y)`. -/
def Pt (p : End X) (b : ℕ) : (Lpow (l + 1) (Y.czBdd : AddCat)).Mor (ZW X b) (ZW X b) :=
  bddRes (2 * b) (sy p)

/-- `Π = Π(Σ P_W(w))` on `C`. -/
def Pi (p : End X) (b : ℕ) : End (CC X b) := perSum (Pt p b)

/-- The corner `S = ζ₊ Π ζ₊`. -/
def SS (p : End X) (b : ℕ) : End (CC X b) := zp X b ≫ Pi p b ≫ zp X b

/-- The corner `B = u₁ P₋₁ : C → X`. -/
def BB (p : End X) (b : ℕ) : (Lpow l (Y.cz : AddCat)).Mor (CC X b) X := uu X b 1 ≫ Pm p

/-- The corner `Γ = P₁ us₁ : X → C`. -/
def GG (p : End X) (b : ℕ) : (Lpow l (Y.cz : AddCat)).Mor X (CC X b) := P1 p ≫ us X b 1

end Data

/-! ### Algebra and supports on `X` -/

section FactsX

variable {Y : InvCat} {l : ℕ} {X : Lpow l (Y.cz : AddCat)} {p : End X} {b : ℕ}

open CZ.Lpow CZ.Corner

lemma hE_idem : hE X * hE X = hE X := chi_idem _ X

lemma hE_add : hE X + hE' X = 1 := chi_add_chi X fun _ ↦ not_le.symm

lemma hd_add : hd X b + tl X b = 1 := chi_add_chi X fun v ↦ by
  constructor <;> intro h <;> omega

variable (hp : p ≫ p = p)
include hp

lemma P0_P0 : P0 p ≫ P0 p + P1 p ≫ Pm p + Pm p ≫ P1 p = P0 p := ring_P0P0 hp hE_idem
lemma P0_P1 : P0 p ≫ P1 p + P1 p ≫ P0 p = P1 p := ring_P0P1 hp hE_idem
lemma P0_Pm : P0 p ≫ Pm p + Pm p ≫ P0 p = Pm p := ring_P0Pm hp hE_idem

@[reassoc]
lemma P1_P1 : P1 p ≫ P1 p = 0 := ring_P1P1 hp hE_idem

@[reassoc]
lemma Pm_Pm : Pm p ≫ Pm p = 0 := ring_PmPm hp hE_idem

variable (hb : PropLE' p b)
include hb

/-- `P₋₁ = φ p` is supported in `W = [-2b, 2b]`. -/
lemma suppIn_Pm : SuppIn (win (2 * b)) (Pm p) := by
  have e : Pm p = p ≫ (p ≫ hE X - hE X ≫ p) := ring_Pm_eq (h := hE X) hp
  rw [e]
  exact (suppIn_comm hb).comp_left hb (fun v hv ↦ by unfold win at *; omega)
    (fun v w hv hw ↦ by unfold win at *; rw [abs_le] at hw; omega)

/-- `P₁ = -p φ` is supported in `W = [-2b, 2b]`. -/
lemma suppIn_P1 : SuppIn (win (2 * b)) (P1 p) := by
  have e : P1 p = -((p ≫ hE X - hE X ≫ p) ≫ p) := ring_P1_eq (h := hE X) hp
  rw [e]
  exact ((suppIn_comm hb).comp_right hb (fun v hv ↦ by unfold win at *; omega)
    (fun v w hv hw ↦ by unfold win at *; rw [abs_le] at hw; omega)).neg

@[reassoc]
lemma Pm_χW : Pm p ≫ χW X b = Pm p := (suppIn_Pm hp hb).comp_chi

@[reassoc]
lemma χW_Pm : χW X b ≫ Pm p = Pm p := (suppIn_Pm hp hb).chi_comp

@[reassoc]
lemma P1_χW : P1 p ≫ χW X b = P1 p := (suppIn_P1 hp hb).comp_chi

@[reassoc]
lemma χW_P1 : χW X b ≫ P1 p = P1 p := (suppIn_P1 hp hb).chi_comp

omit hp hb in
lemma χW_tl : χW X b ≫ tl X b = 0 :=
  chi_comp_chi_eq_zero X fun v h1 h2 ↦ by unfold win at h1; omega

omit hp hb in
lemma tl_χW : tl X b ≫ χW X b = 0 :=
  chi_comp_chi_eq_zero X fun v h1 h2 ↦ by unfold win at h2; omega

lemma Pm_tl : Pm p ≫ tl X b = 0 := by
  rw [← Pm_χW hp hb, assoc, χW_tl, comp_zero]

lemma tl_P1 : tl X b ≫ P1 p = 0 := by
  rw [← χW_P1 hp hb, ← assoc, tl_χW, zero_comp]

omit hp in
lemma tl_p_hE' : tl X b ≫ p ≫ hE' X = 0 := by
  have h1 : tl X b ≫ p ≫ chi X ((b : ℤ) < ·) = tl X b ≫ p :=
    chi_comp_eq hb fun v w hv hw ↦ by rw [abs_le] at hw; omega
  calc tl X b ≫ p ≫ hE' X = (tl X b ≫ p ≫ chi X ((b : ℤ) < ·)) ≫ hE' X := by
        rw [h1, assoc]
    _ = tl X b ≫ p ≫ (chi X ((b : ℤ) < ·) ≫ hE' X) := by simp only [assoc]
    _ = 0 := by
        rw [chi_comp_chi_eq_zero X (P := ((b : ℤ) < ·)) (P' := (· < 0)) fun v h1 h2 ↦ by omega,
          comp_zero, comp_zero]

omit hp in
lemma hE'_p_tl : hE' X ≫ p ≫ tl X b = 0 := by
  have h1 : chi X ((b : ℤ) < ·) ≫ p ≫ tl X b = p ≫ tl X b :=
    comp_chi_eq hb fun v w hv hw ↦ by rw [abs_le] at hw; omega
  calc hE' X ≫ p ≫ tl X b = hE' X ≫ chi X ((b : ℤ) < ·) ≫ p ≫ tl X b := by rw [h1]
    _ = (hE' X ≫ chi X ((b : ℤ) < ·)) ≫ p ≫ tl X b := by rw [assoc]
    _ = 0 := by
        rw [chi_comp_chi_eq_zero X (P := (· < 0)) (P' := ((b : ℤ) < ·)) fun v h1 h2 ↦ by omega,
          zero_comp]

/-- `K χ' = χ'` (operator order; `χ' ≫ K = χ'`). -/
lemma tl_KK : tl X b ≫ KK p = tl X b :=
  ring_K_tail (h := hE X) hp hE_add
    (chi_comp_chi_eq_zero X fun v h1 h2 ↦ by omega)
    ((assoc (tl X b) p (hE' X)).trans (tl_p_hE' hb))

/-- `χ' K = χ'` (operator order; `K ≫ χ' = χ'`). -/
lemma KK_tl : KK p ≫ tl X b = tl X b :=
  ring_tail_K (h := hE X) hp hE_add
    (chi_comp_chi_eq_zero X fun v h1 h2 ↦ by omega)
    ((assoc (hE' X) p (tl X b)).trans (hE'_p_tl hb))

omit hp hb in
lemma tl_tl : tl X b ≫ tl X b = tl X b := chi_idem _ X

/-- `A = K χ_{≤ 2b}`. -/
lemma AA_eq : AA p b = KK p ≫ hd X b := by
  have e : hd X b = 1 - tl X b := eq_sub_of_add_eq hd_add
  have htK : tl X b * KK p = tl X b := KK_tl hp hb
  change KK p - tl X b = hd X b * KK p
  rw [e, sub_mul, one_mul, htK]

/-- Block identity `(1)`: `A ≫ A + P₁ ≫ P₋₁ = A`. -/
lemma AA_AA : AA p b ≫ AA p b + P1 p ≫ Pm p = AA p b := by
  have hKK : KK p * KK p = KK p - Pm p * P1 p := eq_sub_of_add_eq (ring_KK hp hE_idem)
  have hKt : KK p * tl X b = tl X b := tl_KK hp hb
  have htK : tl X b * KK p = tl X b := KK_tl hp hb
  have htt : tl X b * tl X b = tl X b := tl_tl
  change AA p b * AA p b + Pm p * P1 p = AA p b
  rw [AA]
  noncomm_ring [hKK, hKt, htK, htt]

/-- Block identity `(2)`: `P₋₁ ≫ A + P₀ ≫ P₋₁ = P₋₁`. -/
lemma Pm_AA : Pm p ≫ AA p b + P0 p ≫ Pm p = Pm p := by
  have hKPm : KK p * Pm p = Pm p - Pm p * P0 p := eq_sub_of_add_eq (ring_KPm hp hE_idem)
  have htPm : tl X b * Pm p = 0 := Pm_tl hp hb
  change AA p b * Pm p + Pm p * P0 p = Pm p
  rw [AA]
  noncomm_ring [hKPm, htPm]

/-- Block identity `(3)`: `A ≫ P₁ + P₁ ≫ P₀ = P₁`. -/
lemma AA_P1 : AA p b ≫ P1 p + P1 p ≫ P0 p = P1 p := by
  have hP1K : P1 p * KK p = P1 p - P0 p * P1 p := eq_sub_of_add_eq (ring_P1K hp hE_idem)
  have hP1t : P1 p * tl X b = 0 := tl_P1 hp hb
  change P1 p * AA p b + P0 p * P1 p = P1 p
  rw [AA]
  noncomm_ring [hP1K, hP1t]

/-- `P₀` commutes with `χ_W`. -/
lemma P0_χW : P0 p ≫ χW X b = χW X b ≫ P0 p := by
  have e : P0 p = hE X - P1 p - Pm p := ring_P0_eq
  rw [e, sub_comp, sub_comp, comp_sub, comp_sub, P1_χW hp hb, Pm_χW hp hb, χW_P1 hp hb,
    χW_Pm hp hb, chi_comm]

end FactsX

/-! ### The maps `u_k`, `us_k` and the periodic idempotent `Π` -/

section FactsC

variable {Y : InvCat} {l : ℕ} {X : Lpow l (Y.cz : AddCat)} {p : End X} {b : ℕ}

open CZ.Lpow CZ.Corner CZ.Window

@[reassoc]
lemma πE_ιE : (Lpow.incl (Y.cz : AddCat) l).map (CZ.cut X (win (2 * b))).πE ≫
    (Lpow.incl (Y.cz : AddCat) l).map (CZ.cut X (win (2 * b))).ιE = χW X b := by
  rw [← Functor.map_comp]; rfl

lemma ιE_χW : (Lpow.incl (Y.cz : AddCat) l).map (CZ.cut X (win (2 * b))).ιE ≫ χW X b =
    (Lpow.incl (Y.cz : AddCat) l).map (CZ.cut X (win (2 * b))).ιE := by
  rw [χW, chi, ← Functor.map_comp, Splitting.idem, ← assoc, Splitting.ιE_πE, id_comp]

lemma χW_πE : χW X b ≫ (Lpow.incl (Y.cz : AddCat) l).map (CZ.cut X (win (2 * b))).πE =
    (Lpow.incl (Y.cz : AddCat) l).map (CZ.cut X (win (2 * b))).πE := by
  rw [χW, chi, ← Functor.map_comp, Splitting.idem, assoc, Splitting.ιE_πE, comp_id]

@[reassoc]
lemma uu_χW (k : ℤ) : uu X b k ≫ χW X b = uu X b k := by
  rw [uu, assoc, ιE_χW]

@[reassoc]
lemma χW_us (k : ℤ) : χW X b ≫ us X b k = us X b k := by
  rw [us, ← assoc, χW_πE]

@[reassoc]
lemma us_uu_self (k : ℤ) : us X b k ≫ uu X b k = χW X b := by
  have e : (Lpow.incl (Y.cz : AddCat) l).map (Us (ZW X b) k) ≫
      (Lpow.incl (Y.cz : AddCat) l).map (U (ZW X b) k) = 𝟙 _ := by
    rw [← Functor.map_comp, Us_comp_U_self, CategoryTheory.Functor.map_id]
  rw [us, uu, assoc, reassoc_of% e, πE_ιE]

@[reassoc]
lemma us_uu_ne {j k : ℤ} (h : j ≠ k) : us X b j ≫ uu X b k = 0 := by
  have e : (Lpow.incl (Y.cz : AddCat) l).map (Us (ZW X b) j) ≫
      (Lpow.incl (Y.cz : AddCat) l).map (U (ZW X b) k) = 0 := by
    rw [← Functor.map_comp, Us_comp_U, ite_eq_right h, Functor.map_zero]
  rw [us, uu, assoc, reassoc_of% e, zero_comp, comp_zero]

@[reassoc]
lemma chi_uu {P : ℤ → Prop} [DecidablePred P] {k : ℤ} (h : P k) :
    chi (CC X b) P ≫ uu X b k = uu X b k := by
  have e : chi (CC X b) P ≫ (Lpow.incl (Y.cz : AddCat) l).map (U (ZW X b) k) =
      (Lpow.incl (Y.cz : AddCat) l).map (U (ZW X b) k) := by
    rw [chi, ← Functor.map_comp, cut_comp_U, ite_eq_left h]
  rw [uu, reassoc_of% e]

@[reassoc]
lemma chi_uu_zero {P : ℤ → Prop} [DecidablePred P] {k : ℤ} (h : ¬P k) :
    chi (CC X b) P ≫ uu X b k = 0 := by
  have e : chi (CC X b) P ≫ (Lpow.incl (Y.cz : AddCat) l).map (U (ZW X b) k) = 0 := by
    rw [chi, ← Functor.map_comp, cut_comp_U, ite_eq_right h, Functor.map_zero]
  rw [uu, reassoc_of% e, zero_comp]

@[reassoc]
lemma us_chi {P : ℤ → Prop} [DecidablePred P] {k : ℤ} (h : P k) :
    us X b k ≫ chi (CC X b) P = us X b k := by
  have e : (Lpow.incl (Y.cz : AddCat) l).map (Us (ZW X b) k) ≫ chi (CC X b) P =
      (Lpow.incl (Y.cz : AddCat) l).map (Us (ZW X b) k) := by
    rw [chi, ← Functor.map_comp, Us_comp_cut, ite_eq_left h]
  rw [us, assoc, e]

@[reassoc]
lemma us_chi_zero {P : ℤ → Prop} [DecidablePred P] {k : ℤ} (h : ¬P k) :
    us X b k ≫ chi (CC X b) P = 0 := by
  have e : (Lpow.incl (Y.cz : AddCat) l).map (Us (ZW X b) k) ≫ chi (CC X b) P = 0 := by
    rw [chi, ← Functor.map_comp, Us_comp_cut, ite_eq_right h, Functor.map_zero]
  rw [us, assoc, e, comp_zero]

/-- The `w`-coefficients of `P_W(w)`. -/
abbrev FF (p : End X) (b : ℕ) (n : ℤ) :
    (Lpow l (Y.cz : AddCat)).Mor (ZW X b).obj (ZW X b).obj :=
  winRes (2 * b) (symbCoeff (P0 p) (P1 p) (Pm p) n)

lemma FF_eq_zero {n : ℤ} (hn : n < -1 ∨ 1 < n) : FF p b n = 0 := by
  simp only [FF, winRes, symbCoeff_eq_zero _ _ _ hn, zero_comp, comp_zero]

lemma FF_eq_zero' (n : ℤ) (hn : n ∉ ({-1, 0, 1} : Finset ℤ)) : FF p b n = 0 :=
  FF_eq_zero (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn; omega)

lemma coeff_Pt (n : ℤ) (α : Fin l → ℤ) :
    Lpow.coeff (Fin.cons n α : Fin (l + 1) → ℤ) ((Lpow.map (l + 1) (bddIncl Y)).map (Pt p b)) =
      Lpow.coeff α (FF p b n) :=
  coeff_bddRes_symb (2 * b) (P0 p) (P1 p) (Pm p) n α

/-- `Π u₁ = u₂ P₋₁ χ_W + u₁ P₀ χ_W + u₀ P₁ χ_W` (Lean order). -/
@[reassoc]
lemma Pi_uu1 : Pi p b ≫ uu X b 1 =
    uu X b 2 ≫ Pm p ≫ χW X b + uu X b 1 ≫ P0 p ≫ χW X b + uu X b 0 ≫ P1 p ≫ χW X b := by
  have h := perSum_comp_U_assoc (P := Pt p b) (F := FF p b) coeff_Pt {-1, 0, 1} FF_eq_zero' 1
    ((Lpow.incl (Y.cz : AddCat) l).map (CZ.cut X (win (2 * b))).ιE)
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    show (1 : ℤ) - -1 = 2 by norm_num, sub_zero, sub_self] at h
  simp only [FF, symbCoeff_neg_one, symbCoeff_zero, symbCoeff_one, add_comp, assoc,
    πE_ιE] at h
  rw [Pi, uu, h]
  simp only [uu, assoc]
  abel

/-- `us₁ Π = χ_W P₋₁ us₀ + χ_W P₀ us₁ + χ_W P₁ us₂` (Lean order). -/
@[reassoc]
lemma us1_Pi : us X b 1 ≫ Pi p b =
    χW X b ≫ Pm p ≫ us X b 0 + χW X b ≫ P0 p ≫ us X b 1 + χW X b ≫ P1 p ≫ us X b 2 := by
  have h := Us_comp_perSum (P := Pt p b) (F := FF p b) coeff_Pt {-1, 0, 1} FF_eq_zero' 1
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    show (1 : ℤ) + -1 = 0 by norm_num, add_zero, show (1 : ℤ) + 1 = 2 by norm_num] at h
  simp only [FF, symbCoeff_neg_one, symbCoeff_zero, symbCoeff_one, assoc] at h
  rw [Pi, us, assoc, h]
  simp only [us, comp_add, πE_ιE_assoc]
  abel

/-- The corner `ζ₊ Π ζ₋ = u₁ P₋₁ us₀`. -/
@[reassoc]
lemma zp_Pi_zm : zp X b ≫ Pi p b ≫ zm X b = uu X b 1 ≫ Pm p ≫ us X b 0 := by
  have h := chi_comp_perSum_comp_chi_pos_neg (P := Pt p b) (F := FF p b) coeff_Pt
    fun n hn ↦ FF_eq_zero hn
  simp only [FF, symbCoeff_neg_one, assoc] at h
  rw [Pi, h]
  simp only [uu, us, assoc]

/-- The corner `ζ₋ Π ζ₊ = u₀ P₁ us₁`. -/
@[reassoc]
lemma zm_Pi_zp : zm X b ≫ Pi p b ≫ zp X b = uu X b 0 ≫ P1 p ≫ us X b 1 := by
  have h := chi_comp_perSum_comp_chi_neg_pos (P := Pt p b) (F := FF p b) coeff_Pt
    fun n hn ↦ FF_eq_zero hn
  simp only [FF, symbCoeff_one, assoc] at h
  rw [Pi, h]
  simp only [uu, us, assoc]

end FactsC

/-! ### Idempotence of the symbol and of `Π` -/

section Idem

variable {Y : InvCat} {l : ℕ} {X : Lpow l (Y.cz : AddCat)} {p : End X} {b : ℕ}
  (hp : p ≫ p = p)
include hp

open CZ.Lpow CZ.Corner

lemma sy_idem : sy p ≫ sy p = sy p := by
  rw [sy, symb_comp_symb, P0_P0 hp, P0_P1 hp, P0_Pm hp, P1_P1 hp, Pm_Pm hp, ext_zero, zero_comp,
    zero_comp, add_zero, add_zero]

variable (hb : PropLE' p b)
include hb

lemma sy_χW : sy p ≫ ext (χW X b) = ext (χW X b) ≫ sy p := by
  rw [sy, symb_comp_ext, ext_comp_symb, P0_χW hp hb, P1_χW hp hb, χW_P1 hp hb, Pm_χW hp hb,
    χW_Pm hp hb]

lemma winRes_sy_idem :
    winRes (2 * b) (sy p) ≫ winRes (2 * b) (sy p) = winRes (2 * b) (sy p) := by
  have e : (Lpow.incl (Y.cz : AddCat) (l + 1)).map (CZ.cut X (win (2 * b))).πE ≫
      (Lpow.incl (Y.cz : AddCat) (l + 1)).map (CZ.cut X (win (2 * b))).ιE = ext (χW X b) := by
    rw [← Functor.map_comp, ext_chi]; rfl
  have e2 : (Lpow.incl (Y.cz : AddCat) (l + 1)).map (CZ.cut X (win (2 * b))).ιE ≫
      ext (χW X b) = (Lpow.incl (Y.cz : AddCat) (l + 1)).map (CZ.cut X (win (2 * b))).ιE := by
    rw [← e, ← assoc, ← Functor.map_comp, Splitting.ιE_πE, CategoryTheory.Functor.map_id,
      id_comp]
  simp only [winRes, assoc]
  rw [reassoc_of% e, reassoc_of% (sy_χW hp hb), reassoc_of% e2, reassoc_of% (sy_idem hp)]

lemma Pt_idem : Pt p b ≫ Pt p b = Pt p b := bddRes_idem (2 * b) (winRes_sy_idem hp hb)

lemma Pi_idem : Pi p b ≫ Pi p b = Pi p b := by
  simp only [Pi, perSum, ← Functor.map_comp, Pt_idem hp hb]

end Idem

/-! ### The idempotent `Q` on `X ⊕ C` -/

section Blocks

variable {V : Type*} [Category V] [Preadditive V] [HasBinaryBiproducts V] {X C : V}

/-- Products of `2 × 2` block matrices on `X ⊞ C`. -/
lemma blocks_comp (A A' : X ⟶ X) (B B' : C ⟶ X) (G G' : X ⟶ C) (S S' : C ⟶ C) :
    (biprod.fst ≫ A ≫ biprod.inl + biprod.snd ≫ B ≫ biprod.inl + biprod.fst ≫ G ≫ biprod.inr +
      biprod.snd ≫ S ≫ biprod.inr) ≫
    (biprod.fst ≫ A' ≫ biprod.inl + biprod.snd ≫ B' ≫ biprod.inl + biprod.fst ≫ G' ≫ biprod.inr +
      biprod.snd ≫ S' ≫ biprod.inr) =
    biprod.fst ≫ (A ≫ A' + G ≫ B') ≫ biprod.inl + biprod.snd ≫ (B ≫ A' + S ≫ B') ≫ biprod.inl +
      biprod.fst ≫ (A ≫ G' + G ≫ S') ≫ biprod.inr +
      biprod.snd ≫ (B ≫ G' + S ≫ S') ≫ biprod.inr := by
  simp only [add_comp, comp_add, assoc, biprod.inl_fst_assoc, biprod.inl_snd_assoc,
    biprod.inr_fst_assoc, biprod.inr_snd_assoc, zero_comp, comp_zero, add_zero, zero_add]
  abel

end Blocks

section Q

variable {Y : InvCat} {l : ℕ} {X : Lpow l (Y.cz : AddCat)} {p : End X} {b : ℕ}

open CZ.Lpow CZ.Corner

variable (p b) in
/-- **The idempotent `Q = [[K - χ', u₁ P₋₁], [P₁ us₁, ζ₊ Π ζ₊]]` on `T = X ⊕ C`.** -/
def QQ : End (X ⊞ CC X b) :=
  biprod.fst ≫ AA p b ≫ biprod.inl + biprod.snd ≫ BB p b ≫ biprod.inl +
    biprod.fst ≫ GG p b ≫ biprod.inr + biprod.snd ≫ SS p b ≫ biprod.inr

variable (hp : p ≫ p = p) (hb : PropLE' p b)
include hp hb

lemma block1 : AA p b ≫ AA p b + GG p b ≫ BB p b = AA p b := by
  rw [GG, BB, assoc, us_uu_self_assoc, χW_Pm hp hb, AA_AA hp hb]

lemma block2 : BB p b ≫ AA p b + SS p b ≫ BB p b = BB p b := by
  have e : SS p b ≫ BB p b = uu X b 1 ≫ P0 p ≫ Pm p := by
    rw [SS, BB, assoc, assoc, chi_uu_assoc (P := ((1 : ℤ) ≤ ·)) (k := 1) le_rfl, Pi_uu1_assoc]
    simp only [add_comp, comp_add, assoc,
      chi_uu_assoc (P := ((1 : ℤ) ≤ ·)) (k := 1) le_rfl,
      chi_uu_zero_assoc (P := ((1 : ℤ) ≤ ·)) (k := 0) (by norm_num), χW_Pm hp hb,
      Pm_Pm hp, comp_zero, zero_comp, zero_add, add_zero]
  rw [e, BB, assoc, ← comp_add, Pm_AA hp hb]

lemma block3 : AA p b ≫ GG p b + GG p b ≫ SS p b = GG p b := by
  have e : GG p b ≫ SS p b = P1 p ≫ P0 p ≫ us X b 1 := by
    rw [GG, SS, assoc, us_chi_assoc (P := ((1 : ℤ) ≤ ·)) (k := 1) le_rfl, us1_Pi_assoc]
    simp only [add_comp, comp_add, assoc,
      us_chi (P := ((1 : ℤ) ≤ ·)) (k := 2) (by norm_num),
      us_chi (P := ((1 : ℤ) ≤ ·)) (k := 1) le_rfl,
      us_chi_zero (P := ((1 : ℤ) ≤ ·)) (k := 0) (by norm_num), P1_χW_assoc hp hb,
      P1_P1_assoc hp, comp_zero, zero_comp, add_zero, zero_add]
  rw [e, GG, ← assoc, ← assoc, ← add_comp, AA_P1 hp hb]

lemma block4 : BB p b ≫ GG p b + SS p b ≫ SS p b = SS p b := by
  have hzz : zp X b ≫ zp X b = zp X b := chi_idem _ _
  have hmm : zm X b ≫ zm X b = zm X b := chi_idem _ _
  have hsum : chi (CC X b) ((1 : ℤ) ≤ ·) + chi (CC X b) (· ≤ (0 : ℤ)) = 𝟙 _ :=
    chi_add_chi (CC X b) fun v ↦ by constructor <;> intro h <;> omega
  have hBG : BB p b ≫ GG p b = (zp X b ≫ Pi p b ≫ zm X b) ≫ (zm X b ≫ Pi p b ≫ zp X b) := by
    rw [zp_Pi_zm, zm_Pi_zp, BB, GG]
    simp only [assoc, us_uu_self_assoc, χW_P1_assoc hp hb]
  have key : SS p b ≫ SS p b + (zp X b ≫ Pi p b ≫ zm X b) ≫ (zm X b ≫ Pi p b ≫ zp X b) =
      zp X b ≫ Pi p b ≫ zp X b := by
    calc SS p b ≫ SS p b + (zp X b ≫ Pi p b ≫ zm X b) ≫ (zm X b ≫ Pi p b ≫ zp X b)
        = zp X b ≫ Pi p b ≫ zp X b ≫ Pi p b ≫ zp X b +
            zp X b ≫ Pi p b ≫ zm X b ≫ Pi p b ≫ zp X b := by
          simp only [SS, assoc, reassoc_of% hzz, reassoc_of% hmm]
      _ = zp X b ≫ Pi p b ≫ (chi (CC X b) ((1 : ℤ) ≤ ·) + chi (CC X b) (· ≤ (0 : ℤ))) ≫
            Pi p b ≫ zp X b := by
          simp only [add_comp, comp_add]
      _ = zp X b ≫ Pi p b ≫ zp X b := by
          rw [hsum, id_comp, reassoc_of% (Pi_idem hp hb)]
  rw [hBG, add_comm, key]
  rfl

lemma QQ_idem : QQ p b ≫ QQ p b = QQ p b := by
  rw [QQ, blocks_comp, block1 hp hb, block2 hp hb, block3 hp hb, block4 hp hb]

end Q

/-! ### Supports and the germ lemma -/

section Supports

variable {Y : InvCat} {l : ℕ} {X : Lpow l (Y.cz : AddCat)} {p : End X} {b : ℕ}

open CZ.Lpow CZ.Corner

lemma rightSupp_hE : RightSupp (hE X) := ⟨0, suppIn_chi X _⟩

lemma rightSupp_tl : RightSupp (tl X b) := ⟨_, suppIn_chi X _⟩

lemma leftSupp_hd : LeftSupp (hd X b) := ⟨_, suppIn_chi X _⟩

lemma rightSupp_zp : RightSupp (zp X b) := ⟨1, suppIn_chi _ _⟩

lemma leftSupp_zm : LeftSupp (zm X b) := ⟨0, suppIn_chi _ _⟩

lemma rightSupp_Pm : RightSupp (Pm p) := by
  change RightSupp (p ≫ hE X ≫ (1 - p))
  exact (rightSupp_hE.comp_right _).comp_left _

lemma rightSupp_P1 : RightSupp (P1 p) := by
  change RightSupp ((1 - p) ≫ hE X ≫ p)
  exact (rightSupp_hE.comp_right _).comp_left _

variable (hp : p ≫ p = p) (hb : PropLE' p b)
include hp hb

lemma leftSupp_Pm : LeftSupp (Pm p) :=
  ⟨_, (suppIn_Pm hp hb).mono fun _ hv ↦ hv.2⟩

lemma leftSupp_P1 : LeftSupp (P1 p) :=
  ⟨_, (suppIn_P1 hp hb).mono fun _ hv ↦ hv.2⟩

lemma leftSupp_AA : LeftSupp (AA p b) := by
  rw [AA_eq hp hb]
  exact leftSupp_hd.comp_left _

omit hp hb in
lemma rightSupp_p_sub_AA : RightSupp (p - AA p b) := by
  have e : p - AA p b = tl X b - (1 - p) * hE X * (1 - p) := by
    rw [AA, KK]; abel
  rw [e]
  exact rightSupp_tl.sub ((rightSupp_hE.comp_right _).comp_left _)

omit hp hb in
lemma rightSupp_BB : RightSupp (BB p b) := by
  rw [BB]; exact rightSupp_Pm.comp_left _

omit hp hb in
lemma rightSupp_GG : RightSupp (GG p b) := by
  rw [GG]; exact rightSupp_P1.comp_right _

omit hp hb in
lemma rightSupp_SS : RightSupp (SS p b) := by
  change RightSupp (zp X b ≫ Pi p b ≫ zp X b)
  exact (rightSupp_zp.comp_left _).comp_left _

lemma leftSupp_BB : LeftSupp (BB p b) := by
  rw [BB]; exact (leftSupp_Pm hp hb).comp_left _

lemma leftSupp_GG : LeftSupp (GG p b) := by
  rw [GG]; exact (leftSupp_P1 hp hb).comp_right _

omit hp hb in
/-- `Q - (p ⊕ 0)` is right-supported. -/
lemma rightSupp_diff₁ :
    RightSupp (biprod.fst ≫ p ≫ biprod.inl - 𝟙 _ ≫ QQ p b ≫ 𝟙 (X ⊞ CC X b)) := by
  rw [id_comp, comp_id, QQ]
  have h1 : RightSupp (biprod.fst (X := X) (Y := CC X b) ≫ p ≫ biprod.inl (X := X) (Y := CC X b) -
      biprod.fst ≫ AA p b ≫ biprod.inl) := by
    rw [← comp_sub, ← sub_comp]
    exact ((rightSupp_p_sub_AA (p := p) (b := b)).comp_right _).comp_left _
  have e : biprod.fst ≫ p ≫ biprod.inl - (biprod.fst ≫ AA p b ≫ biprod.inl +
      biprod.snd ≫ BB p b ≫ biprod.inl + biprod.fst ≫ GG p b ≫ biprod.inr +
      biprod.snd ≫ SS p b ≫ biprod.inr) =
      (biprod.fst ≫ p ≫ biprod.inl - biprod.fst ≫ AA p b ≫ biprod.inl) -
        biprod.snd ≫ BB p b ≫ biprod.inl - biprod.fst ≫ GG p b ≫ biprod.inr -
        biprod.snd ≫ SS p b ≫ biprod.inr := by abel
  rw [e]
  exact ((h1.sub (((rightSupp_BB (p := p) (b := b)).comp_right _).comp_left _)).sub
    (((rightSupp_GG (p := p) (b := b)).comp_right _).comp_left _)).sub
    ((rightSupp_SS.comp_right _).comp_left _)

/-- `Q - (0 ⊕ Π)` is left-supported. -/
lemma leftSupp_diff₂ :
    LeftSupp (𝟙 (X ⊞ CC X b) ≫ QQ p b ≫ 𝟙 _ - biprod.snd ≫ Pi p b ≫ biprod.inr) := by
  rw [id_comp, comp_id, QQ]
  have hsum : chi (CC X b) ((1 : ℤ) ≤ ·) + chi (CC X b) (· ≤ (0 : ℤ)) = 𝟙 _ :=
    chi_add_chi (CC X b) fun v ↦ by constructor <;> intro h <;> omega
  have e1 : Pi p b = (chi (CC X b) ((1 : ℤ) ≤ ·) + chi (CC X b) (· ≤ (0 : ℤ))) ≫ Pi p b ≫
      (chi (CC X b) ((1 : ℤ) ≤ ·) + chi (CC X b) (· ≤ (0 : ℤ))) := by
    rw [hsum, id_comp, comp_id]
  have h4 : LeftSupp (biprod.snd (X := X) (Y := CC X b) ≫ SS p b ≫ biprod.inr -
      biprod.snd ≫ Pi p b ≫ biprod.inr (X := X) (Y := CC X b)) := by
    have e : biprod.snd (X := X) (Y := CC X b) ≫ SS p b ≫ biprod.inr -
        biprod.snd ≫ Pi p b ≫ biprod.inr (X := X) (Y := CC X b) =
        -(biprod.snd ≫ chi (CC X b) ((1 : ℤ) ≤ ·) ≫ Pi p b ≫ chi (CC X b) (· ≤ (0 : ℤ)) ≫
          biprod.inr) -
        (biprod.snd ≫ chi (CC X b) (· ≤ (0 : ℤ)) ≫ Pi p b ≫ chi (CC X b) ((1 : ℤ) ≤ ·) ≫
          biprod.inr +
         biprod.snd ≫ chi (CC X b) (· ≤ (0 : ℤ)) ≫ Pi p b ≫ chi (CC X b) (· ≤ (0 : ℤ)) ≫
          biprod.inr) := by
      conv_lhs => rw [e1]
      simp only [SS, zp, add_comp, comp_add, assoc]
      abel
    rw [e]
    exact ((((leftSupp_zm.comp_right _).comp_left _).comp_left _).comp_left _).neg.sub
      (((leftSupp_zm.comp_right _).comp_left _).add ((leftSupp_zm.comp_right _).comp_left _))
  have e : biprod.fst ≫ AA p b ≫ biprod.inl + biprod.snd ≫ BB p b ≫ biprod.inl +
      biprod.fst ≫ GG p b ≫ biprod.inr + biprod.snd ≫ SS p b ≫ biprod.inr -
      biprod.snd ≫ Pi p b ≫ biprod.inr =
      biprod.fst ≫ AA p b ≫ biprod.inl + biprod.snd ≫ BB p b ≫ biprod.inl +
        biprod.fst ≫ GG p b ≫ biprod.inr +
        (biprod.snd ≫ SS p b ≫ biprod.inr - biprod.snd ≫ Pi p b ≫ biprod.inr) := by abel
  rw [e]
  exact (((((leftSupp_AA hp hb).comp_right _).comp_left _).add
    (((leftSupp_BB hp hb).comp_right _).comp_left _)).add
    (((leftSupp_GG hp hb).comp_right _).comp_left _)).add h4

/-- **`(X, p) ∼ (C, Π)`**: the controlled Bass splitting, before identifying `Π = Π(E)`. -/
theorem stablyIso_Pi :
    StablyIso (⟨X, p, hp⟩ : Karoubi (Lpow l (Y.cz : AddCat)).carrier)
      ⟨CC X b, Pi p b, Pi_idem hp hb⟩ :=
  (germ_right' (Z := X) (Z' := X ⊞ CC X b) (T := X ⊞ CC X b) biprod.inl biprod.fst
    biprod.inl_fst (𝟙 _) (𝟙 _) (id_comp _) hp (QQ_idem hp hb) rightSupp_diff₁).trans
  (germ_left' (Z := X ⊞ CC X b) (Z' := CC X b) (T := X ⊞ CC X b) (𝟙 _) (𝟙 _) (id_comp _)
    biprod.inr biprod.snd biprod.inr_snd (QQ_idem hp hb) (Pi_idem hp hb) (leftSupp_diff₂ hp hb))

end Supports

end BassPZ

open BassPZ CZ.Corner in
/-- **Theorem B (controlled Bass splitting)**, `blueprint/negK-high.md` §3.1: every Kar object
`(X, p)` of `L^l(C_ℤ Y)` is stably isomorphic to `Π(E)` for the Kar object
`E = (ΣX_W, Σ(χ_W (h + (w - 1) phq + (w⁻¹ - 1) qhp) χ_W))` of `L^{l+1} Y`. -/
theorem theoremB : TheoremBStatement := by
  intro Y l X p hp
  obtain ⟨b, hb⟩ := CZ.Lpow.exists_propLE' p
  refine ⟨⟨CZ.Window.pt (ZW X b), (Lpow.map (l + 1) (sumFun Y)).map (Pt p b), ?_⟩, ?_⟩
  · rw [← Functor.map_comp, Pt_idem hp hb]
  · exact stablyIso_Pi hp hb

end

end HSFormal.LTheory
