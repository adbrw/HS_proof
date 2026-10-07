import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Integer arithmetic in the proposed Hilbert–Smith proof

This module isolates the arithmetic used in manuscript Lemma 3.1, Theorem 6.3,
and the final tail contradiction in Section 12.  It does not construct the
controlled L-theory class required to apply that arithmetic to a group action.
-/

noncomputable section

namespace HSFormal

open Filter Polynomial

/-- Manuscript Lemma 3.1 in polynomial form. A polynomial with integer
coefficients that vanishes at a primitive root of prime-power order has
`p`-divisible value at one. The exponent `k + 1` includes exactly the nontrivial
prime-power cyclic groups used by the manuscript's index-`p` subgroups. -/
theorem prime_dvd_eval_one_of_primitive_root
    (p k : ℕ) (hp : p.Prime) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (F : ℤ[X])
    (hzero : aeval ζ F = 0) : (p : ℤ) ∣ F.eval 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpos : 0 < p ^ (k + 1) := pow_pos hp.pos _
  have hdiv : cyclotomic (p ^ (k + 1)) ℤ ∣ F := by
    rw [cyclotomic_eq_minpoly hζ hpos]
    exact minpoly.isIntegrallyClosed_dvd (hζ.isIntegral hpos) hzero
  obtain ⟨Q, hQ⟩ := hdiv
  rw [hQ, eval_mul, eval_one_cyclotomic_prime_pow]
  exact dvd_mul_right _ _

/-- The integer multiplicities of a virtual cyclic character, packaged as a
polynomial. Negative coefficients are allowed, as for signature characters. -/
def cyclicSignaturePolynomial {n : ℕ} (multiplicity : Fin n → ℤ) : ℤ[X] :=
  ∑ j, C (multiplicity j) * X ^ (j : ℕ)

/-- The dimension of a virtual character is the sum of its integer
multiplicities. -/
theorem cyclicSignaturePolynomial_eval_one {n : ℕ}
    (multiplicity : Fin n → ℤ) :
    (cyclicSignaturePolynomial multiplicity).eval 1 = ∑ j, multiplicity j := by
  simp [cyclicSignaturePolynomial, eval_finsetSum]

/-- Evaluating the multiplicity polynomial at the generator's root of unity
computes the corresponding virtual cyclic character value. -/
theorem cyclicSignaturePolynomial_aeval {n : ℕ}
    (multiplicity : Fin n → ℤ) (ζ : ℂ) :
    aeval ζ (cyclicSignaturePolynomial multiplicity) =
      ∑ j, (multiplicity j : ℂ) * ζ ^ (j : ℕ) := by
  simp [cyclicSignaturePolynomial]

/-- Manuscript Lemma 3.1 for the integral multiplicities of a virtual cyclic
signature character. -/
theorem prime_dvd_sum_of_character_vanishes
    (p k : ℕ) (hp : p.Prime) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
    (multiplicity : Fin (p ^ (k + 1)) → ℤ)
    (hzero : (∑ j, (multiplicity j : ℂ) * ζ ^ (j : ℕ)) = 0) :
    (p : ℤ) ∣ ∑ j, multiplicity j := by
  have hpoly : aeval ζ (cyclicSignaturePolynomial multiplicity) = 0 := by
    simpa only [cyclicSignaturePolynomial_aeval] using hzero
  simpa only [cyclicSignaturePolynomial_eval_one] using
    prime_dvd_eval_one_of_primitive_root p k hp ζ hζ _ hpoly

/-- The scalar factor left by the proposed nilpotence argument cannot annihilate
a nonzero complex character value. -/
theorem character_vanishes_of_prime_power_annihilation
    (p s : ℕ) (hp : p.Prime) (z : ℂ)
    (h : (p : ℂ) ^ s * z = 0) : z = 0 := by
  apply (mul_eq_zero.mp h).resolve_left
  exact pow_ne_zero s (Nat.cast_ne_zero.mpr hp.ne_zero)

/-- The arithmetic implication of the character relation appearing in
manuscript Theorem 6.3. -/
theorem prime_dvd_sum_of_character_annihilation
    (p k s : ℕ) (hp : p.Prime) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
    (multiplicity : Fin (p ^ (k + 1)) → ℤ)
    (hzero : (p : ℂ) ^ s *
      (∑ j, (multiplicity j : ℂ) * ζ ^ (j : ℕ)) = 0) :
    (p : ℤ) ∣ ∑ j, multiplicity j := by
  exact prime_dvd_sum_of_character_vanishes p k hp ζ hζ multiplicity
    (character_vanishes_of_prime_power_annihilation p s hp _ hzero)

/-- A signature-one polynomial cannot satisfy the primitive-root vanishing
condition needed by manuscript Lemma 3.1. -/
theorem primitive_root_vanishing_excludes_signature_one
    (p k : ℕ) (hp : p.Prime) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (F : ℤ[X])
    (hzero : aeval ζ F = 0) (hone : F.eval 1 = 1) : False := by
  have h : (p : ℤ) ∣ 1 := by
    simpa only [hone] using prime_dvd_eval_one_of_primitive_root p k hp ζ hζ F hzero
  have hnat : p ∣ 1 := Int.natCast_dvd_natCast.mp h
  exact hp.ne_one (Nat.dvd_one.mp hnat)

/-- The final arithmetic contradiction of Section 12, stated for actual integer
sequences: an eventually `p`-divisible sequence cannot be eventually one. -/
theorem tail_divisibility_excludes_eventual_one
    (p : ℕ) (hp : p.Prime) (signature : ℕ → ℤ)
    (hdiv : ∀ᶠ i in atTop, (p : ℤ) ∣ signature i)
    (hone : ∀ᶠ i in atTop, signature i = 1) : False := by
  obtain ⟨i, hi⟩ := (hdiv.and hone).exists
  have h : (p : ℤ) ∣ 1 := by simpa only [hi.2] using hi.1
  have hnat : p ∣ 1 := Int.natCast_dvd_natCast.mp h
  exact hp.ne_one (Nat.dvd_one.mp hnat)

/-- The combined arithmetic steps of manuscript Theorem 6.3 and Section 12,
with all integer character data and both eventual hypotheses explicit. -/
theorem tail_character_annihilation_excludes_eventual_signature_one
    (p s : ℕ) (hp : p.Prime) (exponent : ℕ → ℕ) (ζ : ℕ → ℂ)
    (multiplicity : ∀ i, Fin (p ^ (exponent i + 1)) → ℤ)
    (hζ : ∀ i, IsPrimitiveRoot (ζ i) (p ^ (exponent i + 1)))
    (hzero : ∀ᶠ i in atTop, (p : ℂ) ^ s *
      (∑ j, (multiplicity i j : ℂ) * ζ i ^ (j : ℕ)) = 0)
    (hone : ∀ᶠ i in atTop, (∑ j, multiplicity i j) = 1) : False := by
  apply tail_divisibility_excludes_eventual_one p hp (fun i ↦ ∑ j, multiplicity i j) _ hone
  filter_upwards [hzero] with i hi
  exact prime_dvd_sum_of_character_annihilation p (exponent i) s hp
    (ζ i) (hζ i) (multiplicity i) hi

end HSFormal
