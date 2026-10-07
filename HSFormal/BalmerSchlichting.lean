import HSFormal.BoundedKaroubi
import HSFormal.BalmerSchlichting.Dilation
import HSFormal.BalmerSchlichting.Improve

/-!
# `K^b(P)` is idempotent complete ([BS01, Thm 2.8], split exact case)

Let `e` be an idempotent of `K^b(P)`, represented by a chain map with `h : e ≫ e ≃ e` whose
components `h_i : X_i ⟶ X_{i+1}` vanish outside `[a, a + m)`. We kill the top component of `h`:
first replace `(e, h)` by `(2e² - e, e²h + 2ehe + he² - h)` (`Improve.lean`), so that the commutator
of `e` and `h` in the top degree factors through the differential, then dilate `e` to an
endomorphism `ε` of `X ⊞ splitCone X` (`Dilation.lean`). Then `ε` corresponds to `e` under the
homotopy equivalence `X ⊞ splitCone X ≃ X`, and its homotopy vanishes outside `[a, a + m - 1)`.
After `m` steps the idempotent is strict, and it splits degreewise
(`BoundedHomotopyCategory.strictIdempotent_splits`).
-/

namespace HSFormal

open CategoryTheory Category Limits Idempotents

universe v u

namespace HomotopyIdempotent

variable {P : Type u} [Category.{v} P] [Preadditive P] [HasBinaryBiproducts P]

/-- `e` is conjugate in `K(P)` to a strict idempotent of a complex which is bounded if the source
of `e` is. -/
def Strictifiable {X : ChainComplex P ℤ} (e : X ⟶ X) : Prop :=
  ∃ (X' : ChainComplex P ℤ) (ε : X' ⟶ X'), ε ≫ ε = ε ∧
    (IsBoundedComplex X → IsBoundedComplex X') ∧
    ∃ φ : (HomotopyCategory.quotient P _).obj X' ≅ (HomotopyCategory.quotient P _).obj X,
      (HomotopyCategory.quotient P _).map ε ≫ φ.hom = φ.hom ≫ (HomotopyCategory.quotient P _).map e

lemma isBoundedComplex_biprod_splitCone {X : ChainComplex P ℤ} (hX : IsBoundedComplex X) :
    IsBoundedComplex (X ⊞ splitCone X) := by
  obtain ⟨n, hn⟩ := hX
  refine ⟨n + 1, fun i hi ↦ ?_⟩
  rw [lt_abs] at hi
  refine IsZero.of_iso ?_ (HomologicalComplex.biprodXIso _ _ i)
  rw [biprod_isZero_iff]
  exact ⟨hn i (by rw [lt_abs]; omega), (biprod_isZero_iff _ _).2
    ⟨hn i (by rw [lt_abs]; omega), hn (i + 1) (by rw [lt_abs]; omega)⟩⟩

theorem strictifiable_of_support (m : ℕ) : ∀ (X : ChainComplex P ℤ) (e : X ⟶ X)
    (h : Homotopy (e ≫ e) e) (a : ℤ), (∀ i j, (i < a ∨ a + m ≤ i) → h.hom i j = 0) →
      Strictifiable e := by
  induction m with
  | zero =>
    intro X e h a ha
    refine ⟨X, e, ?_, id, Iso.refl _, by simp⟩
    ext n
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, comm_succ h k,
      ha _ _ (by omega), ha _ _ (by omega)]
    simp
  | succ m ih =>
    intro X e h a ha
    set l := a + m - 1 with hl
    have hh : h.hom (l + 1 + 1) (l + 1 + 1 + 1) = 0 := ha _ _ (by omega)
    have hh' : ∀ i j, l + 1 < i → (improveHomotopy h).hom i j = 0 :=
      fun i j hi ↦ improveHomotopy_hom_eq_zero h i j (ha i j (by omega))
    let H := dilHomotopy (improveY h l) (improveY_eq_zero h l) (improve_comm h l hh) hh'
    have hH : ∀ i j, (i < a ∨ a + m ≤ i) → H.hom i j = 0 := by
      intro i j hij
      apply dilHomotopy_hom_eq_zero
      · simp only [dilH₁]
        split_ifs with hi
        · rfl
        · exact improveHomotopy_hom_eq_zero h i j (ha i j (by omega))
      · rcases hij with hi | hi
        · exact improveY_eq_zero_of_hom h l i j (ha _ _ (Or.inl hi))
        · exact improveY_eq_zero h l i j (Or.inl (by omega))
    obtain ⟨X', ε, hε, hb, φ, hφ⟩ := ih _ _ H a hH
    refine ⟨X', ε, hε, fun hX ↦ hb (isBoundedComplex_biprod_splitCone hX),
      φ ≪≫ HomotopyCategory.isoOfHomotopyEquiv (splitConeEquiv X), ?_⟩
    simp only [Iso.trans_hom, HomotopyCategory.isoOfHomotopyEquiv_hom, splitConeEquiv]
    rw [reassoc_of% hφ, ← Functor.map_comp,
      HomotopyCategory.eq_of_homotopy _ _ (dilεFstHomotopy (improveHomotopy h) l),
      Functor.map_comp, quotient_map_improve h, assoc]

end HomotopyIdempotent

open HomotopyIdempotent in
/-- [BS01, Theorem 2.8] for the split exact structure: the bounded homotopy category of an
idempotent complete additive category is idempotent complete. -/
theorem balmerSchlichting : BalmerSchlichting.{v, u} := by
  intro P _ _ _ _
  have : HasBinaryBiproducts P := hasBinaryBiproducts_of_finite_biproducts P
  refine ⟨fun X p hp ↦ ?_⟩
  obtain ⟨n, hn⟩ := X.property
  let e : X.obj.as ⟶ X.obj.as := Quot.out p.hom
  have he : (HomotopyCategory.quotient P _).map e = p.hom := HomotopyCategory.quotient_map_out _
  let h := HomotopyCategory.homotopyOfEq (e ≫ e) e (by
    rw [Functor.map_comp, he]
    exact congrArg InducedCategory.Hom.hom hp)
  have supp : ∀ i j, (i < -(n : ℤ) ∨ -(n : ℤ) + ((2 * n : ℕ) : ℤ) ≤ i) → h.hom i j = 0 := by
    intro i j hij
    rcases hij with hi | hi
    · exact (hn i (by rw [lt_abs]; omega)).eq_of_src _ _
    · by_cases hj : j = i + 1
      · subst hj
        exact (hn (i + 1) (by rw [lt_abs]; omega)).eq_of_tgt _ _
      · exact h.zero i j (by simp; omega)
  obtain ⟨X', ε, hε, hb, φ, hφ⟩ := strictifiable_of_support (2 * n) _ e h (-n) supp
  have hbX : boundedProperty P ((HomotopyCategory.quotient P _).obj X') := hb ⟨n, hn⟩
  obtain ⟨Y, i, q, hiq, hqi⟩ := BoundedHomotopyCategory.strictIdempotent_splits
    ⟨(HomotopyCategory.quotient P _).obj X', hbX⟩ ε hε
  let ψ : (⟨(HomotopyCategory.quotient P _).obj X', hbX⟩ : BoundedHomotopyCategory P) ≅ X :=
    ObjectProperty.isoMk _ φ
  refine ⟨Y, i ≫ ψ.hom, ψ.inv ≫ q, by simp [hiq], ?_⟩
  rw [assoc, reassoc_of% hqi]
  ext
  change φ.inv ≫ (HomotopyCategory.quotient P _).map ε ≫ φ.hom = p.hom
  rw [hφ, Iso.inv_hom_id_assoc, he]

end HSFormal
