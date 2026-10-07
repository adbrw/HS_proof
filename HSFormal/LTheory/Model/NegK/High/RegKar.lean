import HSFormal.LTheory.Model.NegK.High.RegKarFib
import HSFormal.LTheory.Model.NegK.High.RegKarStatement
import HSFormal.LTheory.Model.NegK.FreeQGMat

/-!
# Theorem R, Karoubi form (NegKHigh module N13, `RegKar`)

`blueprint/negK-high.md` §4 "Kar form (dictionary)", §5 (base `m = 1`, step 2).

**`regKarStatement : RegKarStatement`**: for every `G`, every `T ⊆ ℕ` (possibly infinite) and
every `l`, every Kar object `E` of `L^{l+1}(finSuppFreeQG G T)` satisfies `E ⊞ ι⁺Q₁ ∼ ι⁺Q₀` for
Kar objects `Q₀, Q₁` of `L^l(L⁺(finSuppFreeQG G T))`; in fact `E ⊞ ι⁺Q₁ ≅ ι⁺Q₀` (`regKar_iso`).

*Proof.*  `qgFibMat T`: morphisms of `finSuppFreeQG G T` are, fibrewise, matrices over `ℚ[Gᵢ]`
acting by `x ↦ x ᵥ* A` (`FreeQGMat.lin`, `repMat`, `ofLin`); this is a fibrewise matrix
representation (`FibMat`, `RegKarFib`), so `L^{l+1}` has fibre matrices over
`lpRing (l + 1) (ℚ[Gᵢ]) = FullRing ℚ Gᵢ l`, the faces `L^l(L⁺ ·)` over
`lpRing l (ℚ[Gᵢ][X]) = FaceRing ℚ Gᵢ l`, and `ι⁺` acts by `faceMap`.  At each fibre where `E` is
nonzero apply `theoremR_matrix` (`RegMatrix`); objects `Q₀, Q₁` with the resulting ranks have
finite support inside that of `E`, hence lie in `finSuppFreeQG G T`
(`qg_exists_obj`), and `FibMat.exists_karoubi_iso` assembles the fibrewise Karoubi isomorphisms.
-/

namespace HSFormal.LTheory.Reg

open CategoryTheory Limits Matrix Idempotents

noncomputable section

variable {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)] (T : Set ℕ)

variable (G) in
/-- The fibre rings `ℚ[Gᵢ]`. -/
abbrev qgRing (i : ℕ) : RingCat.{0} := RingCat.of (MonoidAlgebra ℚ (G i))

/-- The fibre ranks of an object of `finSuppFreeQG G T`. -/
abbrev qgRank : (finSuppFreeQG G T : AddCat).carrier → ℕ → ℕ := fun X i ↦ X.obj.rank i

lemma repMat_comp {Γ : Type} [Group Γ] {m n k : ℕ}
    (L : (Fin m → MonoidAlgebra ℚ Γ) →ₗ[MonoidAlgebra ℚ Γ] (Fin n → MonoidAlgebra ℚ Γ))
    (L' : (Fin n → MonoidAlgebra ℚ Γ) →ₗ[MonoidAlgebra ℚ Γ] (Fin k → MonoidAlgebra ℚ Γ)) :
    FreeQGMat.repMat (L'.comp L) = FreeQGMat.repMat L * FreeQGMat.repMat L' :=
  eq_of_vecMul_eq fun x ↦ by
    rw [← FreeQGMat.linearMap_eq_vecMul, ← vecMul_vecMul, ← FreeQGMat.linearMap_eq_vecMul,
      ← FreeQGMat.linearMap_eq_vecMul]
    rfl

lemma repMat_id {Γ : Type} [Group Γ] {m : ℕ} :
    FreeQGMat.repMat (LinearMap.id : (Fin m → MonoidAlgebra ℚ Γ) →ₗ[MonoidAlgebra ℚ Γ] _) = 1 :=
  eq_of_vecMul_eq fun x ↦ by rw [← FreeQGMat.linearMap_eq_vecMul, vecMul_one]; rfl

lemma repMat_vecMulLin {Γ : Type} [Group Γ] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (MonoidAlgebra ℚ Γ)) : FreeQGMat.repMat (vecMulLin A) = A :=
  eq_of_vecMul_eq fun x ↦ by rw [← FreeQGMat.linearMap_eq_vecMul, vecMulLin_apply]

/-- **The fibrewise matrices of `finSuppFreeQG G T`**: `f ↦ (repMat (lin f i))ᵢ`, matrices over
`ℚ[Gᵢ]` acting by `x ↦ x ᵥ* A` (`FreeQGMat`). -/
def qgFibMat : FibMat (finSuppFreeQG G T : AddCat) (qgRank T) (qgRing G) where
  mat f i := FreeQGMat.repMat (FreeQGMat.lin f i)
  mat_add f g i := by
    rw [FreeQGMat.lin_add]
    rfl
  mat_comp f g i := by
    rw [FreeQGMat.lin_comp]
    exact repMat_comp _ _
  mat_id X i := by
    rw [AddCat.idMor, FreeQGMat.lin_id]
    exact repMat_id
  ext {X Y f g} h := FreeQGMat.lin_ext fun i ↦ LinearMap.ext fun x ↦ by
    rw [FreeQGMat.linearMap_eq_vecMul, FreeQGMat.linearMap_eq_vecMul (FreeQGMat.lin g i)]
    exact congrArg (x ᵥ* ·) (h i)
  full {X Y} A := ⟨FreeQGMat.ofLin fun i ↦ vecMulLin (A i), fun i ↦ by
    rw [FreeQGMat.lin_ofLin]
    exact repMat_vecMulLin (A i)⟩
  finite X := X.property.1

/-- Objects of `finSuppFreeQG G T` with ranks dominated by those of a given object. -/
lemma qg_exists_obj (X : (finSuppFreeQG G T : AddCat).carrier) (r : ℕ → ℕ)
    (hr : ∀ i, qgRank T X i = 0 → r i = 0) :
    ∃ Q : (finSuppFreeQG G T : AddCat).carrier, qgRank T Q = r :=
  ⟨⟨⟨r, fun _ _ ↦ PUnit.unit⟩, X.property.1.subset fun i hi h0 ↦ hi (hr i h0),
    fun i hi ↦ hr i (X.property.2 i hi)⟩, rfl⟩


/-- **Theorem R, Karoubi form, isomorphism version**: for every Kar object `E` of
`L^{l+1}(finSuppFreeQG G T)` there are Kar objects `Q₀, Q₁` of `L^l(L⁺(finSuppFreeQG G T))` with
`E ⊞ ι⁺Q₁ ≅ ι⁺Q₀` in `Karoubi`. -/
theorem regKar_iso (l : ℕ) (E : Karoubi (Lpow (l + 1) (finSuppFreeQG G T : AddCat)).carrier) :
    ∃ Q₀ Q₁ : Karoubi (Lpow l (LaurentPos (finSuppFreeQG G T : AddCat))).carrier,
      Nonempty (E ⊞ (karoubiMap (Lpow.map l (LaurentPos.incl (finSuppFreeQG G T : AddCat)))).obj Q₁ ≅
        (karoubiMap (Lpow.map l (LaurentPos.incl (finSuppFreeQG G T : AddCat)))).obj Q₀) :=
  (qgFibMat T).exists_karoubi_iso l (fun i _ e he ↦ theoremR_matrix ℚ (G i) l e he)
    (qg_exists_obj T) E

end

/-- **Theorem R, Karoubi form** (`RegKarStatement`, the base case input of the induction). -/
theorem regKarStatement : RegKarStatement := fun _ _ _ T l E ↦
  let ⟨Q₀, Q₁, ⟨φ⟩⟩ := regKar_iso T l E
  ⟨Q₀, Q₁, StablyIso.of_iso φ⟩

end HSFormal.LTheory.Reg
