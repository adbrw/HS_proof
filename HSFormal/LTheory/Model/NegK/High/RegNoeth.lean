import HSFormal.LTheory.Model.NegK.High.RegPd
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Localization.Submodule

/-!
# Theorem R, part 2: noetherianity and finite resolutions (NegKHigh module N10, `RegNoeth`)

`blueprint/negK-high.md` §4, steps (R3) and (R4), and the splitting used by (R7).

* **(R3)** `isNoetherianRing_monoidAlgebra`: `k[G]` is (left) noetherian for `k` noetherian and
  `G` finite (`k[G]` is a finite `k`-module, so left ideals are finitely generated already over
  `k`); `isNoetherianRing_laurent`, `isNoetherianRing_lpComm`.
* **(R4)** `exists_resolution_step`: over a left noetherian ring, a finitely generated module of
  `pd ≤ d + 1` is a quotient of some `S^k` by a finitely generated kernel of `pd ≤ d`.  Iterating
  this gives a finite resolution by finitely generated free modules ending in a projective; the
  iteration itself is done (with localization) in `RegLocal`.
* `exists_prodEquiv_of_surjective`: a surjection onto a projective splits, `F ≃ ker f × M`
  (the splitting step of the Euler characteristic argument (R7)).
-/

open CategoryTheory

namespace HSFormal.LTheory.Reg

universe u

section Noetherian

/-- **(R3)** The group ring of a finite group over a noetherian commutative ring is (left)
noetherian. -/
lemma isNoetherianRing_monoidAlgebra (k : Type u) [CommRing k] [IsNoetherianRing k] (G : Type u)
    [Group G] [Finite G] : IsNoetherianRing (MonoidAlgebra k G) := by
  have : IsNoetherian k (MonoidAlgebra k G) := isNoetherian_of_isNoetherianRing_of_finite k _
  exact isNoetherian_of_tower k this

/-- Laurent extensions of noetherian commutative rings are noetherian. -/
instance isNoetherianRing_laurent (A : Type u) [CommRing A] [IsNoetherianRing A] :
    IsNoetherianRing (LaurentPolynomial A) :=
  IsLocalization.isNoetherianRing (Submonoid.powers (Polynomial.X : Polynomial A)) _
    inferInstance

/-- Iterated Laurent extensions of noetherian commutative rings are noetherian. -/
lemma isNoetherianRing_lpComm : ∀ (n : ℕ) (A : CommRingCat.{u}) [IsNoetherianRing A],
    IsNoetherianRing (lpComm n A)
  | 0, _, _ => ‹_›
  | n + 1, A, _ => isNoetherianRing_lpComm n (CommRingCat.of (LaurentPolynomial A))

/-- **(R3)** for `S = C[G]`, `C = lpComm n (K[X])`. -/
lemma isNoetherianRing_lpComm_polynomial_monoidAlgebra (K : Type u) [Field K] (G : Type u)
    [Group G] [Finite G] (n : ℕ) :
    IsNoetherianRing (MonoidAlgebra (lpComm n (CommRingCat.of (Polynomial K))) G) := by
  have := isNoetherianRing_lpComm n (CommRingCat.of (Polynomial K))
  exact isNoetherianRing_monoidAlgebra _ G

end Noetherian

section Resolution

variable {S : Type u} [Ring S]

/-- **(R4), one step.** Over a left noetherian ring, a finitely generated module of `pd ≤ d + 1`
is a quotient of a finite free module by a finitely generated submodule of `pd ≤ d`. -/
lemma exists_resolution_step [IsNoetherianRing S] (M : Type u) [AddCommGroup M] [Module S M]
    [Module.Finite S M] {d : ℕ} (hM : PdLE S M (d + 1)) :
    ∃ (k : ℕ) (f : (Fin k → S) →ₗ[S] M), Function.Surjective f ∧
      Module.Finite S (LinearMap.ker f) ∧ PdLE S (LinearMap.ker f) d := by
  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' S M
  exact ⟨k, f, hf, inferInstance, pdLE_ker f hf (pdLE_of_projective _) hM⟩

variable {F M : Type*} [AddCommGroup F] [Module S F] [AddCommGroup M] [Module S M]

/-- A surjection onto a projective module splits: `F ≃ ker f × M`. -/
lemma exists_prodEquiv_of_surjective [Module.Projective S M] (f : F →ₗ[S] M)
    (hf : Function.Surjective f) : Nonempty ((LinearMap.ker f × M) ≃ₗ[S] F) := by
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hσ' : ∀ m, f (σ m) = m := fun m ↦ congrArg (fun g : M →ₗ[S] M ↦ g m) hσ
  refine ⟨LinearEquiv.ofBijective ((LinearMap.ker f).subtype.coprod σ) ⟨?_, ?_⟩⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, m⟩ h
    simp only [LinearMap.coprod_apply, Submodule.coe_subtype] at h
    have hm : m = 0 := by
      have := congrArg f h
      rwa [map_add, LinearMap.mem_ker.mp x.2, hσ', zero_add, map_zero] at this
    subst hm
    rw [map_zero, add_zero] at h
    ext <;> simp [h]
  · intro y
    refine ⟨(⟨y - σ (f y), ?_⟩, f y), ?_⟩
    · rw [LinearMap.mem_ker, map_sub, hσ', sub_self]
    · simp

end Resolution

end HSFormal.LTheory.Reg
