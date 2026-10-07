import HSFormal.Assembly
import HSFormal.LTheory.Localization

/-!
# Iterated cuts with sign relations (cubical module C8, part 3: the L-level skeleton)

The abstract shape of Lemma 11.2 over arbitrary `InvCat`s: an iterated boundary
`iterDown C d f n : L(C n)_{n+d} → L(C 0)_d` (as in `Δ_1`, (11.1)) applied to classes `x k` that
are related by single cuts up to signs, `f k (x (k+1)) = u k • x k` (Lemma 4.1 with
`bsign`, and the A/B-side sign of `PinchPair.cutBdHtpy`), lands on `± x 0`
(`iterDown_eq_of_steps`); hence a homomorphism `σ` to the tail group which is a sign tail on
`x 0` (`CPcell`, `σ = 1`) is a sign tail on the iterated boundary of `x n`
(`isSignTail_iterDown_of_steps`), which is the content of `PinchSignature` (`IsSignTail`
absorbs the product of the signs, `Assembly.IsSignTail`).
-/

noncomputable section

namespace HSFormal

open Filter

/-- Sign tails are stable under multiplication by `±1`. -/
theorem IsSignTail.units_smul {s : Tail} (hs : IsSignTail s) (u : ℤˣ) : IsSignTail (u • s) := by
  induction s using Germ.inductionOn with
  | h s =>
  rw [Units.smul_def, ← Germ.coe_smul, isSignTail_coe]
  filter_upwards [isSignTail_coe.mp hs] with i hi
  simpa [smul_eq_mul] using (Units.isUnit u).mul hi

theorem isSignTail_units_smul_iff {s : Tail} (u : ℤˣ) : IsSignTail (u • s) ↔ IsSignTail s :=
  ⟨fun h ↦ by simpa [smul_smul] using h.units_smul u⁻¹, fun h ↦ h.units_smul u⟩

namespace LTheory.LowerLTheory

variable (𝕃 : LowerLTheory)

/-- **Iterated cuts of classes related by single cuts up to sign**: if each cut sends `x (k+1)`
to `u k • x k`, the iterated boundary sends `x n` to `(∏_{k<n} u k) • x 0`. -/
theorem iterDown_eq_of_steps (C : ℕ → InvCat) (d : ℤ)
    (f : ∀ k : ℕ, 𝕃.L (C (k + 1)) ((k : ℤ) + d + 1) →+ 𝕃.L (C k) ((k : ℤ) + d))
    (x : ∀ k : ℕ, 𝕃.L (C k) ((k : ℤ) + d)) (u : ℕ → ℤˣ)
    (hx : ∀ k, f k (𝕃.castDeg _ (natDeg_succ k d) (x (k + 1))) = u k • x k) (n : ℕ) :
    𝕃.iterDown C d f n (x n) =
      (∏ k ∈ Finset.range n, u k) • 𝕃.castDeg (C 0) (by simp) (x 0) := by
  induction n with
  | zero => simp [iterDown]
  | succ n ih =>
    simp only [iterDown, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
    rw [hx, Units.smul_def, map_zsmul, ih, ← Units.smul_def, smul_smul, Finset.prod_range_succ,
      mul_comm]

/-- **The pinch signature from cut steps**: a sign tail on `x 0` is a sign tail on the iterated
boundary of `x n`. -/
theorem isSignTail_iterDown_of_steps (C : ℕ → InvCat) (d : ℤ)
    (f : ∀ k : ℕ, 𝕃.L (C (k + 1)) ((k : ℤ) + d + 1) →+ 𝕃.L (C k) ((k : ℤ) + d))
    (x : ∀ k : ℕ, 𝕃.L (C k) ((k : ℤ) + d)) (u : ℕ → ℤˣ)
    (hx : ∀ k, f k (𝕃.castDeg _ (natDeg_succ k d) (x (k + 1))) = u k • x k)
    (σ : 𝕃.L (C 0) d →+ Tail) (hσ : IsSignTail (σ (𝕃.castDeg (C 0) (by simp) (x 0)))) (n : ℕ) :
    IsSignTail (σ (𝕃.iterDown C d f n (x n))) := by
  rw [𝕃.iterDown_eq_of_steps C d f x u hx n, Units.smul_def, map_zsmul, ← Units.smul_def]
  exact hσ.units_smul _

end LTheory.LowerLTheory

end HSFormal
