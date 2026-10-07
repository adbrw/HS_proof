import HSFormal.Cubical.Contraction

/-!
# Acyclic carriers: chain maps and homotopies by residual filling (module C1)

Given contractible carriers `car σ` in a target complex `D`, one for each source cell `σ` and
nested along faces, `fillMat` builds a matrix column by column in order of degree: on
`fixed` cells it is prescribed, otherwise column `σ` is `s_σ (R σ + c · u(∂σ))`, the filling of
the residual in the carrier of `σ` (manuscript (8.5), §2.4 of the design).  Every entry is
supported in the carriers.  Two instances:

* `carrierHom`: a chain map extending a prescribed one on a face-closed set containing all
  vertices (`a_h` with `a_1 = 1`);
* `carrierHtpy`: an exact homotopy `F - G = d h + h d` between carried chain maps agreeing on
  vertex augmentations (`B_{g,h}`, `U_g`); it vanishes wherever `F = G` on a face-closed set.

Residuals in the top degree of a box vanish automatically (`SubContraction.s_eq_zero`).
`Geometry` records cell centres and closed carriers in a space `E`.
-/

namespace HSFormal.Cubical

open Matrix

namespace BasedComplex

variable {C D Y : BasedComplex}

section Fill

variable {car : C.X → D.X → Prop} (S : ∀ σ, SubContraction D (car σ))
  (fixed : C.X → Prop) [DecidablePred fixed] (pre R : Matrix D.X C.X ℚ) (c : ℚ)

/-- One column of the acyclic-carrier recursion. -/
def fillCol (σ : C.X) : D.X → ℚ :=
  if fixed σ then fun ρ ↦ pre ρ σ else
    (S σ).s *ᵥ fun κ ↦ R κ σ + c * ∑ τ, if h : C.d τ σ = 0 then 0 else fillCol τ κ * C.d τ σ
termination_by C.deg σ
decreasing_by have := C.d_deg τ σ h; omega

/-- The matrix produced by the acyclic-carrier recursion. -/
def fillMat : Matrix D.X C.X ℚ := Matrix.of fun ρ σ ↦ fillCol S fixed pre R c σ ρ

/-- The residual of column `σ`: `R σ + c · u(∂σ)`. -/
def fillRes (σ : C.X) : D.X → ℚ := fun κ ↦ (R + c • (fillMat S fixed pre R c * C.d)) κ σ

theorem fillMat_apply (ρ : D.X) (σ : C.X) :
    fillMat S fixed pre R c ρ σ =
      if fixed σ then pre ρ σ else ((S σ).s *ᵥ fillRes S fixed pre R c σ) ρ := by
  simp only [fillMat, of_apply]
  rw [fillCol]
  split_ifs with hf
  · rfl
  · congr 2
    ext κ
    simp only [fillRes, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, mul_apply, fillMat, of_apply]
    congr 2
    refine Finset.sum_congr rfl fun τ _ ↦ ?_
    split_ifs with h <;> simp [h]

variable {S fixed pre R c}

theorem fillMat_supp (hpre : ∀ ρ σ, fixed σ → pre ρ σ ≠ 0 → car σ ρ) {ρ : D.X} {σ : C.X}
    (h : fillMat S fixed pre R c ρ σ ≠ 0) : car σ ρ := by
  rw [fillMat_apply] at h
  split_ifs at h with hf
  · exact hpre ρ σ hf h
  · exact (S σ).mulVec_supp h

theorem fillMat_hasDeg {k : ℤ} (hpre : ∀ ρ σ, fixed σ → pre ρ σ ≠ 0 → (D.deg ρ : ℤ) = C.deg σ + k)
    (hR : ∀ ρ σ, ¬fixed σ → R ρ σ ≠ 0 → (D.deg ρ : ℤ) = C.deg σ + k - 1) :
    HasDeg C D k (fillMat S fixed pre R c) := by
  suffices ∀ n σ, C.deg σ = n → ∀ ρ, fillMat S fixed pre R c ρ σ ≠ 0 →
      (D.deg ρ : ℤ) = C.deg σ + k from fun ρ σ ↦ this _ σ rfl ρ
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rintro σ rfl ρ h
    rw [fillMat_apply] at h
    split_ifs at h with hf
    · exact hpre ρ σ hf h
    obtain ⟨κ, h₁, h₂⟩ := exists_mulVec_ne_zero h
    have e₁ := (S σ).deg1 ρ κ h₁
    have e₂ : (D.deg κ : ℤ) = C.deg σ + k - 1 := by
      simp only [fillRes, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h₂
      by_cases hR0 : R κ σ = 0
      · rw [hR0, zero_add] at h₂
        obtain ⟨τ, h₃, h₄⟩ := exists_mul_apply_ne_zero (right_ne_zero_of_mul h₂)
        have := C.d_deg τ σ h₄
        rw [ih (C.deg τ) (by omega) τ rfl κ h₃, this]; push_cast; ring
      · exact hR κ σ hf hR0
    rw [e₁, e₂]; ring

/-- **Acyclic-carrier construction.** The recursion solves `d u = R + c · u d`, provided the
prescribed columns do, everything is carried by the nested carriers, `d R + c · R d = 0`, and
the residuals of the filled columns have augmentation zero. -/
theorem d_mul_fillMat (hnest : ∀ τ σ, C.d τ σ ≠ 0 → ∀ ρ, car τ ρ → car σ ρ)
    (hfix : ∀ τ σ, C.d τ σ ≠ 0 → fixed σ → fixed τ)
    (hpre_supp : ∀ ρ σ, fixed σ → pre ρ σ ≠ 0 → car σ ρ)
    (hpre : ∀ ρ σ, fixed σ → (D.d * pre) ρ σ = R ρ σ + c * (pre * C.d) ρ σ)
    (hR_supp : ∀ ρ σ, ¬fixed σ → R ρ σ ≠ 0 → car σ ρ) (hR : D.d * R + c • (R * C.d) = 0)
    (haug : ∀ σ, ¬fixed σ → ∑ ρ, D.aug ρ * fillRes S fixed pre R c σ ρ = 0) :
    D.d * fillMat S fixed pre R c = R + c • (fillMat S fixed pre R c * C.d) := by
  set u := fillMat S fixed pre R c with hu
  suffices ∀ n σ, C.deg σ = n → ∀ ρ, (D.d * u) ρ σ = (R + c • (u * C.d)) ρ σ by
    ext ρ σ; exact this _ σ rfl ρ
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rintro σ rfl ρ
    have face : ∀ τ, C.d τ σ ≠ 0 → ∀ ρ, (D.d * u) ρ τ = (R + c • (u * C.d)) ρ τ :=
      fun τ h ↦ ih _ (by have := C.d_deg τ σ h; omega) τ rfl
    by_cases hf : fixed σ
    · have hcol : ∀ κ, u κ σ = pre κ σ := fun κ ↦ by rw [hu, fillMat_apply, ite_eq_left hf]
      have hud : ∀ κ, (u * C.d) κ σ = (pre * C.d) κ σ := fun κ ↦ by
        simp only [mul_apply]
        refine Finset.sum_congr rfl fun τ _ ↦ ?_
        by_cases h : C.d τ σ = 0
        · simp [h]
        · rw [hu, fillMat_apply, ite_eq_left (hfix τ σ h hf)]
      rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hud, ← hpre ρ σ hf]
      simp only [mul_apply, hcol]
    · have hcol : (fun κ ↦ u κ σ) = (S σ).s *ᵥ fillRes S fixed pre R c σ := by
        ext κ; rw [hu, fillMat_apply, ite_eq_right hf]
      have hsupp : ∀ κ, fillRes S fixed pre R c σ κ ≠ 0 → car σ κ := fun κ h ↦ by
        simp only [fillRes, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h
        by_cases hR0 : R κ σ = 0
        · rw [hR0, zero_add] at h
          obtain ⟨τ, h₃, h₄⟩ := exists_mul_apply_ne_zero (right_ne_zero_of_mul h)
          exact hnest τ σ h₄ κ (fillMat_supp hpre_supp h₃)
        · exact hR_supp κ σ hf hR0
      have hcyc : D.d *ᵥ fillRes S fixed pre R c σ = 0 := by
        ext ρ'
        have h₁ : ((D.d * u) * C.d) ρ' σ = ((R + c • (u * C.d)) * C.d) ρ' σ := by
          simp only [mul_apply (M := D.d * u), mul_apply (M := R + c • (u * C.d))]
          refine Finset.sum_congr rfl fun τ _ ↦ ?_
          by_cases h : C.d τ σ = 0
          · simp [h]
          · rw [face τ h ρ']
        have h₂ : (R + c • (u * C.d)) * C.d = R * C.d := by
          rw [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc, C.d_d, Matrix.mul_zero,
            smul_zero, add_zero]
        have h₃ := congr_fun (congr_fun hR ρ') σ
        change (D.d * (R + c • (u * C.d))) ρ' σ = 0
        rw [Matrix.mul_add, Matrix.mul_smul, ← Matrix.mul_assoc, Matrix.add_apply, Matrix.smul_apply, h₁, h₂]
        simpa using h₃
      change (D.d *ᵥ fun κ ↦ u κ σ) ρ = _
      rw [hcol, (S σ).fill hsupp hcyc (haug σ hf)]
      rfl

/-- Columns vanish on a face-closed set of unprescribed cells where `R` vanishes. -/
theorem fillMat_eq_zero {Z : C.X → Prop} (hZ : ∀ τ σ, C.d τ σ ≠ 0 → Z σ → Z τ)
    (hZf : ∀ σ, Z σ → ¬fixed σ) (hZR : ∀ ρ σ, Z σ → R ρ σ = 0) :
    ∀ σ, Z σ → ∀ ρ, fillMat S fixed pre R c ρ σ = 0 := by
  suffices ∀ n σ, C.deg σ = n → Z σ → ∀ ρ, fillMat S fixed pre R c ρ σ = 0 from
    fun σ ↦ this _ σ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rintro σ rfl hσ ρ
    have hres : fillRes S fixed pre R c σ = 0 := by
      ext κ
      simp only [fillRes, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hZR κ σ hσ, zero_add, mul_apply,
        Pi.zero_apply]
      refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun τ _ ↦ ?_)
      by_cases h : C.d τ σ = 0
      · simp [h]
      · rw [ih _ (by have := C.d_deg τ σ h; omega) τ rfl (hZ τ σ h hσ), zero_mul]
    rw [fillMat_apply, ite_eq_right (hZf σ hσ), hres, mulVec_zero, Pi.zero_apply]

end Fill

section Builders

variable {car : C.X → D.X → Prop} (S : ∀ σ, SubContraction D (car σ))

/-- **Carrier homotopy** (manuscript (8.5), (8.6)): chain maps carried by nested contractible
carriers, with equal vertex augmentations, are homotopic by a carried homotopy. -/
def carrierHtpy (F G : Hom C D) (hnest : ∀ τ σ, C.d τ σ ≠ 0 → ∀ ρ, car τ ρ → car σ ρ)
    (hF : ∀ ρ σ, F.f ρ σ ≠ 0 → car σ ρ) (hG : ∀ ρ σ, G.f ρ σ ≠ 0 → car σ ρ)
    (haug : ∀ σ, C.deg σ = 0 → ∑ ρ, D.aug ρ * F.f ρ σ = ∑ ρ, D.aug ρ * G.f ρ σ) :
    Htpy F G :=
  have hdeg : HasDeg C D 1 (fillMat S (fun _ ↦ False) 0 (F.f - G.f) (-1)) :=
    fillMat_hasDeg (fun _ _ h ↦ h.elim) fun ρ σ _ h ↦ by
      simpa using (F.deg0.sub G.deg0) ρ σ h
  { h := fillMat S (fun _ ↦ False) 0 (F.f - G.f) (-1)
    deg1 := hdeg
    eq := by
      have := d_mul_fillMat (S := S) (fixed := fun _ ↦ False) (pre := 0) (R := F.f - G.f)
        (c := -1) hnest (fun _ _ _ h ↦ h) (fun _ _ h ↦ h.elim) (fun _ _ h ↦ h.elim)
        (fun ρ σ _ h ↦ by
          rw [Matrix.sub_apply] at h
          by_cases hF0 : F.f ρ σ = 0
          · exact hG ρ σ (by simpa [hF0] using h)
          · exact hF ρ σ hF0)
        (by rw [Matrix.sub_mul, Matrix.mul_sub, F.comm, G.comm]; simp)
        (fun σ _ ↦ by
          rcases Nat.eq_zero_or_pos (C.deg σ) with h0 | hpos
          · have : ∀ κ, (fillMat S (fun _ ↦ False) 0 (F.f - G.f) (-1) * C.d) κ σ = 0 :=
              fun κ ↦ Finset.sum_eq_zero fun τ _ ↦ by
                by_cases h : C.d τ σ = 0
                · simp [h]
                · have := C.d_deg τ σ h; omega
            simp only [fillRes, Matrix.add_apply, Matrix.smul_apply, this, smul_zero, add_zero, Matrix.sub_apply,
              mul_sub, Finset.sum_sub_distrib, haug σ h0, sub_self]
          · refine sum_aug_mul_eq_zero fun ρ h ↦ ?_
            simp only [fillRes, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h
            by_cases hR0 : (F.f - G.f) ρ σ = 0
            · rw [hR0, zero_add] at h
              obtain ⟨τ, h₃, h₄⟩ := exists_mul_apply_ne_zero (right_ne_zero_of_mul h)
              have := hdeg ρ τ h₃
              omega
            · have := (F.deg0.sub G.deg0) ρ σ hR0
              omega)
      rw [this]; simp only [neg_smul, one_smul]; abel }

theorem carrierHtpy_h (F G : Hom C D) (hnest) (hF) (hG) (haug) :
    (carrierHtpy S F G hnest hF hG haug).h = fillMat S (fun _ ↦ False) 0 (F.f - G.f) (-1) :=
  rfl

theorem carrierHtpy_supp (F G : Hom C D) (hnest) (hF) (hG) (haug) {ρ : D.X} {σ : C.X}
    (h : (carrierHtpy S F G hnest hF hG haug).h ρ σ ≠ 0) : car σ ρ :=
  fillMat_supp (fun _ _ h ↦ h.elim) h

/-- The carrier homotopy vanishes on a face-closed set where `F = G`. -/
theorem carrierHtpy_eq_zero (F G : Hom C D) (hnest) (hF) (hG) (haug) {Z : C.X → Prop}
    (hZ : ∀ τ σ, C.d τ σ ≠ 0 → Z σ → Z τ) (hFG : ∀ ρ σ, Z σ → F.f ρ σ = G.f ρ σ) {σ : C.X}
    (hσ : Z σ) (ρ : D.X) : (carrierHtpy S F G hnest hF hG haug).h ρ σ = 0 :=
  fillMat_eq_zero hZ (fun _ _ h ↦ h) (fun ρ σ h ↦ by simp [hFG ρ σ h]) σ hσ ρ

/-- **Carrier chain map** (`a_h`, design §2.4): extend a chain map prescribed on a face-closed
set `fixed` containing every vertex by filling the other cells in their carriers. -/
def carrierHom (fixed : C.X → Prop) [DecidablePred fixed] (pre : Matrix D.X C.X ℚ)
    (hnest : ∀ τ σ, C.d τ σ ≠ 0 → ∀ ρ, car τ ρ → car σ ρ)
    (hfix : ∀ τ σ, C.d τ σ ≠ 0 → fixed σ → fixed τ) (hvert : ∀ σ, C.deg σ = 0 → fixed σ)
    (hpre_deg : ∀ ρ σ, fixed σ → pre ρ σ ≠ 0 → D.deg ρ = C.deg σ)
    (hpre_supp : ∀ ρ σ, fixed σ → pre ρ σ ≠ 0 → car σ ρ)
    (hpre_comm : ∀ ρ σ, fixed σ → (D.d * pre) ρ σ = (pre * C.d) ρ σ)
    (hpre_aug : ∀ σ, C.deg σ = 0 → ∑ ρ, D.aug ρ * pre ρ σ = 1) (hC : C.IsAugmented) :
    Hom C D :=
  have hdeg : HasDeg C D 0 (fillMat S fixed pre 0 1) :=
    fillMat_hasDeg (fun ρ σ hf h ↦ by simp [hpre_deg ρ σ hf h]) fun _ _ _ h ↦ (h rfl).elim
  { f := fillMat S fixed pre 0 1
    deg0 := hdeg
    comm := by
      have := d_mul_fillMat (S := S) (R := 0) (c := 1) hnest hfix hpre_supp
        (fun ρ σ hf ↦ by simp [hpre_comm ρ σ hf]) (fun _ _ _ h ↦ (h rfl).elim) (by simp)
        (fun σ hf ↦ by
          have hres : fillRes S fixed pre 0 1 σ =
              fun ρ ↦ (fillMat S fixed pre 0 1 * C.d) ρ σ := by
            ext ρ; simp [fillRes]
          rw [hres]
          by_cases h1 : C.deg σ = 1
          · simp only [mul_apply, Finset.mul_sum]
            rw [Finset.sum_comm, ← hC σ]
            refine Finset.sum_congr rfl fun τ _ ↦ ?_
            by_cases h : C.d τ σ = 0
            · simp [h]
            have hτ : C.deg τ = 0 := by have := C.d_deg τ σ h; omega
            have e : ∑ ρ, D.aug ρ * fillMat S fixed pre 0 1 ρ τ = 1 := by
              simp only [fillMat_apply, ite_eq_left (hvert τ hτ)]; exact hpre_aug τ hτ
            calc ∑ ρ, D.aug ρ * (fillMat S fixed pre 0 1 ρ τ * C.d τ σ)
                = (∑ ρ, D.aug ρ * fillMat S fixed pre 0 1 ρ τ) * C.d τ σ := by
                  rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
              _ = C.aug τ * C.d τ σ := by rw [e]; simp [aug, hτ]
          · have hpos : C.deg σ ≠ 0 := fun h ↦ hf (hvert σ h)
            refine sum_aug_mul_eq_zero fun ρ h ↦ ?_
            obtain ⟨τ, h₃, h₄⟩ := exists_mul_apply_ne_zero h
            have := hdeg ρ τ h₃
            have := C.d_deg τ σ h₄
            omega)
      simpa using this }

theorem carrierHom_f (fixed : C.X → Prop) [DecidablePred fixed] (pre) (hnest) (hfix) (hvert)
    (hpre_deg) (hpre_supp) (hpre_comm) (hpre_aug) (hC) :
    (carrierHom S fixed pre hnest hfix hvert hpre_deg hpre_supp hpre_comm hpre_aug hC).f =
      fillMat S fixed pre 0 1 := rfl

theorem carrierHom_f_of_fixed (fixed : C.X → Prop) [DecidablePred fixed] (pre) (hnest) (hfix)
    (hvert) (hpre_deg) (hpre_supp) (hpre_comm) (hpre_aug) (hC) {σ : C.X} (hσ : fixed σ)
    (ρ : D.X) :
    (carrierHom S fixed pre hnest hfix hvert hpre_deg hpre_supp hpre_comm hpre_aug hC).f ρ σ =
      pre ρ σ := by
  rw [carrierHom_f, fillMat_apply, ite_eq_left hσ]

theorem carrierHom_supp (fixed : C.X → Prop) [DecidablePred fixed] (pre) (hnest) (hfix) (hvert)
    (hpre_deg) (hpre_supp) (hpre_comm) (hpre_aug) (hC) {ρ : D.X} {σ : C.X}
    (h : (carrierHom S fixed pre hnest hfix hvert hpre_deg hpre_supp hpre_comm hpre_aug hC).f
      ρ σ ≠ 0) : car σ ρ :=
  fillMat_supp hpre_supp h

end Builders

/-! ### Centres and carriers -/

/-- Cell centres and closed carriers in `E`, nested along faces.  For the torus take `E` a
product of circles (or carriers that are unions of lifts), so that nesting holds at the seam;
propagation is measured through labels `λ ∘ center`. -/
structure Geometry (C : BasedComplex) (E : Type*) where
  center : C.X → E
  carrier : C.X → Set E
  center_mem : ∀ σ, center σ ∈ carrier σ
  face_sub : ∀ σ τ, C.d σ τ ≠ 0 → carrier σ ⊆ carrier τ

namespace Geometry

variable {E F : Type*}

/-- Product geometry of a tensor product. -/
def tensor (g : Geometry C E) (g' : Geometry D F) : Geometry (C.tensor D) (E × F) where
  center p := (g.center p.1, g'.center p.2)
  carrier p := g.carrier p.1 ×ˢ g'.carrier p.2
  center_mem p := ⟨g.center_mem p.1, g'.center_mem p.2⟩
  face_sub := by
    rintro ⟨σ, σ'⟩ ⟨τ, τ'⟩ h
    rcases tensor_d_ne_zero h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · simp only [h₂]; exact Set.prod_mono (g.face_sub _ _ h₁) le_rfl
    · simp only [h₁]; exact Set.prod_mono le_rfl (g'.face_sub _ _ h₂)

/-- Product geometry of an iterated tensor product, in `Fin n → E`. -/
def pi : (n : ℕ) → {C : Fin n → BasedComplex} → (∀ i, Geometry (C i) E) →
    Geometry (prodComplex n C) (Fin n → E)
  | 0, _, _ => ⟨fun _ ↦ Fin.elim0, fun _ ↦ Set.univ, fun _ ↦ trivial, fun _ _ _ ↦ le_rfl⟩
  | n + 1, _, g =>
    let g' := pi n fun i ↦ g i.succ
    { center := fun p ↦ Fin.cons ((g 0).center p.1) (g'.center p.2)
      carrier := fun p ↦ {x | x 0 ∈ (g 0).carrier p.1 ∧ Fin.tail x ∈ g'.carrier p.2}
      center_mem := fun p ↦ ⟨by simpa using (g 0).center_mem p.1,
        by simpa [Fin.tail] using g'.center_mem p.2⟩
      face_sub := by
        rintro ⟨σ, σ'⟩ ⟨τ, τ'⟩ h x ⟨hx₁, hx₂⟩
        rcases tensor_d_ne_zero h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · exact ⟨(g 0).face_sub _ _ h₁ hx₁, h₂ ▸ hx₂⟩
        · exact ⟨h₁ ▸ hx₁, g'.face_sub _ _ h₂ hx₂⟩ }

/-- Restriction along a cellular embedding. -/
def comap (g : Geometry C E) (e : CellEmbedding Y C) : Geometry Y E where
  center := g.center ∘ e.toFun
  carrier := g.carrier ∘ e.toFun
  center_mem _ := g.center_mem _
  face_sub σ τ h := g.face_sub _ _ (by rwa [e.d_eq])

/-- The union of the carriers of a set of cells, e.g. of a box. -/
def hull (g : Geometry C E) (P : C.X → Prop) : Set E := ⋃ (σ) (_ : P σ), g.carrier σ

theorem carrier_subset_hull (g : Geometry C E) {P : C.X → Prop} {σ : C.X} (h : P σ) :
    g.carrier σ ⊆ g.hull P :=
  Set.subset_biUnion_of_mem (u := g.carrier) h

theorem hull_mono (g : Geometry C E) {P Q : C.X → Prop} (h : ∀ σ, P σ → Q σ) :
    g.hull P ⊆ g.hull Q :=
  Set.biUnion_subset_biUnion_left h

end Geometry

end BasedComplex

end HSFormal.Cubical
