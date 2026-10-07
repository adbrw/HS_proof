import HSFormal.BalmerSchlichting.SplitCone

/-!
# Killing one component of the homotopy of a homotopy idempotent

Let `e` be a chain map with `h : e ≫ e ≃ e` whose components `h_i` vanish for `i > l + 1`, and
assume `h_{l+1} ≫ e - e ≫ h_{l+1}` factors as `d ≫ Y`. On `X ⊞ splitCone X` the "dilation"
`ε = [[e, C], [B, D]]` (with `C = -h_{l+1}`, `B = 1`, `D = 1 - e` on the summand
`cone(1_{X_{l+2}})`) is a homotopy idempotent whose homotopy vanishes in degrees `≥ l + 1`, and
`ε` corresponds to `e` under `X ⊞ splitCone X ≃ X`.
-/

namespace HSFormal.HomotopyIdempotent

open CategoryTheory Category Limits Preadditive

universe v u

variable {P : Type u} [Category.{v} P] [Preadditive P] [HasBinaryBiproducts P]
  {X : ChainComplex P ℤ} {e : X ⟶ X} (h : Homotopy (e ≫ e) e) (l : ℤ)

/-- The component `X ⟶ splitCone X` of the dilation. -/
noncomputable def dilC : X ⟶ splitCone X where
  f j := biprod.lift (-(X.d j (l + 1) ≫ h.hom (l + 1) j))
    (if j = l + 1 then -h.hom j (j + 1) else 0)
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    rw [splitCone_d]
    apply biprod.hom_ext
    · simp
    · by_cases hj : j = l + 1
      · subst hj
        simp
      · rw [X.shape (j + 1) (l + 1) (fun h ↦ hj (by simp at h; omega))]
        simp [hj]

/-- The component `splitCone X ⟶ X` of the dilation. -/
noncomputable def dilB : splitCone X ⟶ X where
  f j := biprod.desc (if j = l + 1 + 1 then 𝟙 _ else 0) (if j = l + 1 then X.d (j + 1) j else 0)
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    rw [splitCone_d]
    apply biprod.hom_ext'
    · by_cases hj : j = l + 1
      · subst hj
        simp
      · simp [hj, show j + 1 ≠ l + 1 + 1 by omega]
    · split_ifs <;> simp

variable (e) in
/-- The component `splitCone X ⟶ splitCone X` of the dilation. -/
noncomputable def dilD : splitCone X ⟶ splitCone X where
  f j := biprod.map (if j = l + 1 + 1 then 𝟙 _ - e.f j else 0)
    (if j = l + 1 then 𝟙 _ - e.f (j + 1) else 0)
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    rw [splitCone_d]
    apply biprod.hom_ext'
    · apply biprod.hom_ext
      · simp
      · by_cases hj : j = l + 1
        · subst hj
          simp
        · simp [hj, show j + 1 ≠ l + 1 + 1 by omega]
    · simp

variable {h l}

section

variable (hh : ∀ i j, l + 1 < i → h.hom i j = 0)
include hh

omit [HasBinaryBiproducts P] in
lemma dil_key : X.d (l + 1 + 1) (l + 1) ≫ (-h.hom (l + 1) (l + 1 + 1)) +
    (𝟙 _ - e.f (l + 1 + 1)) ≫ (𝟙 _ - e.f (l + 1 + 1)) = 𝟙 _ - e.f (l + 1 + 1) := by
  have := comm_succ h (l + 1)
  rw [hh (l + 1 + 1) _ (by omega), zero_comp, add_zero, HomologicalComplex.comp_f] at this
  simp only [comp_sub, sub_comp, id_comp, comp_id, comp_neg, this]
  abel

lemma dilB_comp_dilC_add : dilB l ≫ dilC h l + dilD e l ≫ dilD e l = dilD e l := by
  ext n : 1
  simp only [HomologicalComplex.add_f_apply, HomologicalComplex.comp_f, dilB, dilC, dilD]
  apply biprod.hom_ext' <;> apply biprod.hom_ext
  · by_cases hn : n = l + 1 + 1
    · subst hn
      simpa using dil_key hh
    · simp [hn]
  · by_cases hn : n = l + 1 + 1
    · subst hn
      simp
    · simp [hn]
  · by_cases hn : n = l + 1
    · subst hn
      simp
    · simp [hn]
  · by_cases hn : n = l + 1
    · subst hn
      simpa using dil_key hh
    · simp [hn]

end

lemma dilB_comp_add : dilB l ≫ e + dilD e l ≫ dilB l = dilB l := by
  ext n : 1
  simp only [HomologicalComplex.add_f_apply, HomologicalComplex.comp_f, dilB, dilD]
  apply biprod.hom_ext'
  · by_cases hn : n = l + 1 + 1
    · subst hn
      simp
    · simp [hn]
  · by_cases hn : n = l + 1
    · subst hn
      simp [e.comm]
    · simp [hn]

/-- The homotopy `h` with its component in degree `l + 1` removed. -/
def dilH₁ : ∀ i j, X.X i ⟶ X.X j := fun i j ↦ if i = l + 1 then 0 else h.hom i j

lemma comp_add_dilC_comp : e ≫ e + dilC h l ≫ dilB l =
    e + Homotopy.nullHomotopicMap (dilH₁ (h := h) (l := l)) := by
  ext n : 1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [HomologicalComplex.add_f_apply, HomologicalComplex.comp_f, dilB, dilC,
    nullHomotopicMap_f_succ, dilH₁, biprod.lift_desc]
  rw [← HomologicalComplex.comp_f, comm_succ h m]
  by_cases hm : m = l
  · subst hm
    simp
    abel
  · by_cases hm' : m = l + 1
    · subst hm'
      simp
      abel
    · rw [X.shape (m + 1) (l + 1) (by simp; omega)]
      simp [hm, hm']
      abel

section

variable (Y : ∀ i j, X.X i ⟶ X.X (j + 1)) (hY : ∀ i j, (i ≠ l ∨ j ≠ l + 1) → Y i j = 0)
  (hKI : h.hom (l + 1) (l + 1 + 1) ≫ e.f (l + 1 + 1) - e.f (l + 1) ≫ h.hom (l + 1) (l + 1 + 1) =
    X.d (l + 1) l ≫ Y l (l + 1))

/-- The null homotopy correcting the off-diagonal block `X ⟶ splitCone X` of `ε ≫ ε - ε`. -/
noncomputable def dilH₂ : ∀ i j, X.X i ⟶ (splitCone X).X j := fun i j ↦ Y i j ≫ biprod.inr

include hY hKI in
lemma comp_dilC_add : e ≫ dilC h l + dilC h l ≫ dilD e l =
    dilC h l + Homotopy.nullHomotopicMap (dilH₂ Y) := by
  ext n : 1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [HomologicalComplex.add_f_apply, HomologicalComplex.comp_f, dilC, dilD,
    nullHomotopicMap_f_succ, dilH₂, splitCone_d]
  apply biprod.hom_ext
  · by_cases hm : m = l + 1
    · subst hm
      have key := congrArg (X.d (l + 1 + 1) (l + 1) ≫ ·) hKI
      simp only [comp_sub, HomologicalComplex.d_comp_d_assoc, zero_comp, sub_eq_zero] at key
      simp [key]
    · rw [X.shape (m + 1) (l + 1) (by simp; omega)]
      simp
  · by_cases hm : m = l
    · subst hm
      simp
      rw [← hKI]
      abel
    · rw [hY m (m + 1) (Or.inl hm)]
      simp [hm]

variable (h l) in
/-- The dilation of `e`, an endomorphism of `X ⊞ splitCone X`. -/
noncomputable def dilε : X ⊞ splitCone X ⟶ X ⊞ splitCone X :=
  biprod.desc (biprod.lift e (dilC h l)) (biprod.lift (dilB l) (dilD e l))

variable (hh : ∀ i j, l + 1 < i → h.hom i j = 0)

include hh hY hKI in
lemma dilε_comp_dilε : dilε h l ≫ dilε h l = dilε h l + biprod.fst ≫
    (Homotopy.nullHomotopicMap (dilH₁ (h := h) (l := l)) ≫ biprod.inl +
      Homotopy.nullHomotopicMap (dilH₂ Y) ≫ biprod.inr) := by
  apply biprod.hom_ext' <;> apply biprod.hom_ext
  · simpa [dilε] using comp_add_dilC_comp
  · simpa [dilε] using comp_dilC_add Y hY hKI
  · simpa [dilε] using dilB_comp_add
  · simpa [dilε] using dilB_comp_dilC_add hh

/-- The homotopy `ε ≫ ε ≃ ε` of the dilation. -/
noncomputable def dilHomotopy : Homotopy (dilε h l ≫ dilε h l) (dilε h l) :=
  (Homotopy.ofEq (dilε_comp_dilε Y hY hKI hh)).trans
    (((Homotopy.refl _).add
      ((((Homotopy.nullHomotopy (dilH₁ (h := h) (l := l)) (fun i j hij ↦ by
          simp [dilH₁, h.zero i j hij])).compRight biprod.inl).add
        ((Homotopy.nullHomotopy (dilH₂ Y) (fun i j hij ↦ by
          rw [dilH₂, hY i j (by simp at hij; omega), zero_comp])).compRight
            biprod.inr)).compLeft biprod.fst)).trans (Homotopy.ofEq (by simp)))

lemma dilHomotopy_hom_eq_zero (i j : ℤ) (h₁ : dilH₁ (h := h) (l := l) i j = 0) (h₂ : Y i j = 0) :
    (dilHomotopy Y hY hKI hh).hom i j = 0 := by
  simp [dilHomotopy, h₁, dilH₂, h₂]

end

variable (X) in
/-- `X ⊞ splitCone X` is homotopy equivalent to `X`. -/
noncomputable def splitConeEquiv : HomotopyEquiv (X ⊞ splitCone X) X where
  hom := biprod.fst
  inv := biprod.inl
  homotopyHomInvId := (Homotopy.ofEq (by simp)).trans
    (((Homotopy.refl (biprod.fst ≫ biprod.inl)).add
      (((splitCone.contraction X).compRight biprod.inr).compLeft biprod.snd).symm).trans
        (Homotopy.ofEq (by simp [biprod.total])))
  homotopyInvHomId := Homotopy.ofEq (by simp)

variable (h l) in
/-- The dilation corresponds to `e` under `X ⊞ splitCone X ≃ X`. -/
noncomputable def dilεFstHomotopy : Homotopy (dilε h l ≫ biprod.fst) (biprod.fst ≫ e) :=
  (Homotopy.ofEq (by simp [dilε, biprod.desc_eq])).trans
    (((Homotopy.refl (biprod.fst ≫ e)).add
      (((splitCone.contraction X).compRight (dilB l)).compLeft biprod.snd)).trans
        (Homotopy.ofEq (by simp)))

end HSFormal.HomotopyIdempotent
