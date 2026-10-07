import Mathlib.Algebra.Exact.Basic
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Mayer–Vietoris nilpotence (manuscript §4 and Lemma 6.2)

The algebraic core of Lemma 6.2, over abstract groups, to be instantiated with lower L-groups.

* `IsLES i j δ`: a `ℤ`-graded long exact sequence `A n → B n → C n → A (n - 1)`, the connecting
  map written `C (n + 1) → A n` as in the localization interface (L-theory design, W8).
* Barratt–Whitehead (`IsLES.mayerVietoris`): a ladder of two long exact sequences whose third
  vertical maps are isomorphisms gives the Mayer–Vietoris sequence
  `A n → B n × A' n → B' n → A (n - 1)` with boundary `mvBdry = δ ∘ h⁻¹ ∘ j'`.  For the
  localization sequences of `𝒜_Y ⊂ 𝒜_A` and `𝒜_B ⊂ 𝒜(X)` and the excision equivalence
  `h : L(𝒜_A/𝒜_Y) ≃ L(𝒜(X)/𝒜_B)` (2.4) this is Mayer–Vietoris with the boundary (4.1); with
  `𝒜_A/𝒜_Z ⊃ 𝒜_Y`, `𝒜/𝒜_Z ⊃ 𝒜_B` and (4.3) it is (4.2).  Every map is natural for compatible
  endomorphisms (`mvIn_comm`, `mvOut_comm`, `mvBdry_comm`).  The five lemma needed alongside is
  mathlib's `AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective`.
* `pow_succ_eq_zero_of_exact`: the inductive step of Lemma 6.2 for one Mayer–Vietoris square.
* `MVSystem`, `MVSystem.NatEnd`: Mayer–Vietoris sequences for all pairs of a lattice of supports,
  and endomorphisms commuting with all Mayer–Vietoris maps.
* `MVSystem.NatEnd.pow_card_eq_zero`: Lemma 6.2 with the paper's exponent: if `ν` vanishes on
  every support below one of `s` pieces, then `ν ^ s = 0` on their union.  Degree `n + 1` only
  needs local vanishing in degrees `n + 1` and `n`; the boundary's degree shift does not raise
  the exponent.  `pow_eq_zero_of_isLUB` and `natSub_pow_eq_zero` (for `ν = p - τ ⊗ (-)`, (6.1))
  are the statements used in Theorem 6.3.
-/

namespace HSFormal.MVNilpotence

universe u v

section LES

variable {A B C : ℤ → Type*} [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)]
  [∀ n, AddCommGroup (C n)]

/-- A long exact sequence `⋯ → A n → B n → C n → A (n - 1) → ⋯` of abelian groups, exact at every
spot; the connecting map is `δ n : C (n + 1) → A n`. -/
structure IsLES (i : ∀ n, A n →+ B n) (j : ∀ n, B n →+ C n) (δ : ∀ n, C (n + 1) →+ A n) :
    Prop where
  exact_ij : ∀ n, Function.Exact (i n) (j n)
  exact_jδ : ∀ n, Function.Exact (j (n + 1)) (δ n)
  exact_δi : ∀ n, Function.Exact (δ n) (i n)

end LES

section BarrattWhitehead

variable {A B C A' B' C' : ℤ → Type*} [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)]
  [∀ n, AddCommGroup (C n)] [∀ n, AddCommGroup (A' n)] [∀ n, AddCommGroup (B' n)]
  [∀ n, AddCommGroup (C' n)]
  (i : ∀ n, A n →+ B n) (j : ∀ n, B n →+ C n) (δ : ∀ n, C (n + 1) →+ A n)
  (i' : ∀ n, A' n →+ B' n) (j' : ∀ n, B' n →+ C' n) (δ' : ∀ n, C' (n + 1) →+ A' n)
  (f : ∀ n, A n →+ A' n) (g : ∀ n, B n →+ B' n) (h : ∀ n, C n ≃+ C' n)

/-- The first Mayer–Vietoris map `a ↦ (i a, f a)`. -/
def mvIn (n : ℤ) : A n →+ B n × A' n := (i n).prod (f n)

/-- The second Mayer–Vietoris map `(b, a') ↦ g b - i' a'`. -/
def mvOut (n : ℤ) : B n × A' n →+ B' n := (g n).coprod (-i' n)

/-- The Mayer–Vietoris boundary `δ ∘ h⁻¹ ∘ j'` (manuscript (4.1), (4.2)). -/
def mvBdry (n : ℤ) : B' (n + 1) →+ A n :=
  (δ n).comp ((h (n + 1)).symm.toAddMonoidHom.comp (j' (n + 1)))

@[simp] theorem mvIn_apply (n : ℤ) (a : A n) : mvIn i f n a = (i n a, f n a) := rfl

@[simp] theorem mvOut_apply (n : ℤ) (x : B n × A' n) : mvOut i' g n x = g n x.1 - i' n x.2 := by
  simp [mvOut, sub_eq_add_neg]

@[simp] theorem mvBdry_apply (n : ℤ) (x : B' (n + 1)) :
    mvBdry δ j' h n x = δ n ((h (n + 1)).symm (j' (n + 1) x)) := rfl

variable {i j δ i' j' δ' f g h}

theorem exact_mvIn_mvOut (n : ℤ) (hij : Function.Exact (i n) (j n))
    (hδi : Function.Exact (δ n) (i n)) (hδi' : Function.Exact (δ' n) (i' n))
    (hij' : Function.Exact (i' n) (j' n)) (sq₁ : (g n).comp (i n) = (i' n).comp (f n))
    (sq₂ : (j' n).comp (g n) = (h n).toAddMonoidHom.comp (j n))
    (sq₃ : (f n).comp (δ n) = (δ' n).comp (h (n + 1)).toAddMonoidHom) :
    Function.Exact (mvIn i f n) (mvOut i' g n) := by
  have e₁ := DFunLike.congr_fun sq₁
  have e₂ := DFunLike.congr_fun sq₂
  have e₃ := DFunLike.congr_fun sq₃
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom] at e₁ e₂ e₃
  rintro ⟨b, a'⟩
  simp only [mvOut_apply, sub_eq_zero, Set.mem_range, mvIn_apply, Prod.mk.injEq]
  constructor
  · intro hb
    obtain ⟨a₀, rfl⟩ := (hij b).1 <| (h n).injective <| by
      rw [← e₂, hb, hij'.apply_apply_eq_zero, map_zero]
    obtain ⟨c', hc'⟩ := (hδi' (a' - f n a₀)).1 <| by rw [map_sub, ← hb, e₁, sub_self]
    obtain ⟨c, rfl⟩ := (h (n + 1)).surjective c'
    refine ⟨a₀ + δ n c, ?_, ?_⟩
    · rw [map_add, hδi.apply_apply_eq_zero, add_zero]
    · rw [map_add, e₃, hc', add_sub_cancel]
  · rintro ⟨a, rfl, rfl⟩
    exact e₁ a

theorem exact_mvOut_mvBdry (n : ℤ) (hjδ : Function.Exact (j (n + 1)) (δ n))
    (hij' : Function.Exact (i' (n + 1)) (j' (n + 1)))
    (sq₂ : (j' (n + 1)).comp (g (n + 1)) = (h (n + 1)).toAddMonoidHom.comp (j (n + 1))) :
    Function.Exact (mvOut i' g (n + 1)) (mvBdry δ j' h n) := by
  have e₂ := DFunLike.congr_fun sq₂
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom] at e₂
  intro x
  simp only [mvBdry_apply, Set.mem_range, Prod.exists, mvOut_apply]
  constructor
  · intro hx
    obtain ⟨b, hb⟩ := (hjδ _).1 hx
    obtain ⟨a', ha'⟩ := (hij' (x - g (n + 1) b)).1 <| by
      rw [map_sub, e₂, hb, AddEquiv.apply_symm_apply, sub_self]
    exact ⟨b, -a', by rw [map_neg, sub_neg_eq_add, ha', add_sub_cancel]⟩
  · rintro ⟨b, a', rfl⟩
    rw [map_sub, hij'.apply_apply_eq_zero, sub_zero, e₂, AddEquiv.symm_apply_apply,
      hjδ.apply_apply_eq_zero]

theorem exact_mvBdry_mvIn (n : ℤ) (hδi : Function.Exact (δ n) (i n))
    (hjδ' : Function.Exact (j' (n + 1)) (δ' n))
    (sq₃ : (f n).comp (δ n) = (δ' n).comp (h (n + 1)).toAddMonoidHom) :
    Function.Exact (mvBdry δ j' h n) (mvIn i f n) := by
  have e₃ := DFunLike.congr_fun sq₃
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom] at e₃
  intro a
  simp only [mvIn_apply, Prod.mk_eq_zero, Set.mem_range, mvBdry_apply]
  constructor
  · rintro ⟨hi, hf⟩
    obtain ⟨c, rfl⟩ := (hδi a).1 hi
    obtain ⟨x, hx⟩ := (hjδ' (h (n + 1) c)).1 (by rw [← e₃, hf])
    exact ⟨x, by rw [hx, AddEquiv.symm_apply_apply]⟩
  · rintro ⟨x, rfl⟩
    refine ⟨hδi.apply_apply_eq_zero _, ?_⟩
    rw [e₃, AddEquiv.apply_symm_apply, hjδ'.apply_apply_eq_zero]

/-- **Barratt–Whitehead.** A map of long exact sequences whose third components `h` are
isomorphisms yields the Mayer–Vietoris long exact sequence
`A n → B n × A' n → B' n → A (n - 1)`. -/
theorem IsLES.mayerVietoris (top : IsLES i j δ) (bot : IsLES i' j' δ')
    (sq₁ : ∀ n, (g n).comp (i n) = (i' n).comp (f n))
    (sq₂ : ∀ n, (j' n).comp (g n) = (h n).toAddMonoidHom.comp (j n))
    (sq₃ : ∀ n, (f n).comp (δ n) = (δ' n).comp (h (n + 1)).toAddMonoidHom) :
    IsLES (mvIn i f) (mvOut i' g) (mvBdry δ j' h) where
  exact_ij n := exact_mvIn_mvOut n (top.exact_ij n) (top.exact_δi n) (bot.exact_δi n)
    (bot.exact_ij n) (sq₁ n) (sq₂ n) (sq₃ n)
  exact_jδ n := exact_mvOut_mvBdry n (top.exact_jδ n) (bot.exact_ij (n + 1)) (sq₂ (n + 1))
  exact_δi n := exact_mvBdry_mvIn n (top.exact_δi n) (bot.exact_jδ n) (sq₃ n)

theorem mvIn_comm {n : ℤ} {νA : A n → A n} {νB : B n → B n} {νA' : A' n → A' n}
    (hi : ∀ a, i n (νA a) = νB (i n a)) (hf : ∀ a, f n (νA a) = νA' (f n a)) (a : A n) :
    mvIn i f n (νA a) = Prod.map νB νA' (mvIn i f n a) := by
  simp [hi, hf]

theorem mvOut_comm {n : ℤ} {νB : AddMonoid.End (B n)} {νA' : AddMonoid.End (A' n)}
    {νB' : AddMonoid.End (B' n)} (hg : ∀ b, g n (νB b) = νB' (g n b))
    (hi' : ∀ a, i' n (νA' a) = νB' (i' n a)) (x : B n × A' n) :
    mvOut i' g n (Prod.map νB νA' x) = νB' (mvOut i' g n x) := by
  simp [hg, hi']

theorem mvBdry_comm {n : ℤ} {νA : A n → A n} {νC : C (n + 1) → C (n + 1)}
    {νC' : C' (n + 1) → C' (n + 1)} {νB' : B' (n + 1) → B' (n + 1)}
    (hδ : ∀ c, δ n (νC c) = νA (δ n c)) (hh : ∀ c, h (n + 1) (νC c) = νC' (h (n + 1) c))
    (hj' : ∀ b, j' (n + 1) (νB' b) = νC' (j' (n + 1) b)) (x : B' (n + 1)) :
    mvBdry δ j' h n (νB' x) = νA (mvBdry δ j' h n x) := by
  have hs : ∀ c', (h (n + 1)).symm (νC' c') = νC ((h (n + 1)).symm c') := fun c' => by
    rw [AddEquiv.symm_apply_eq, hh, AddEquiv.apply_symm_apply]
  simp [hj', hs, hδ]

end BarrattWhitehead

section Step

variable {LA LB LX LY : Type*} [AddCommGroup LA] [AddCommGroup LB] [AddCommGroup LX]
  [AddCommGroup LY]

/-- The inductive step of Lemma 6.2 for one Mayer–Vietoris square: if `ψ : L(A) × L(B) → L(X)`
and `∂ : L(X) → L(Y)` are exact and commute with `ν`, `ν = 0` on `L(Y)` and `ν ^ k = 0` on
`L(A)` and on `L(B)`, then `ν ^ (k + 1) = 0` on `L(X)`.  Only exactness at `L(X)` is used. -/
theorem pow_succ_eq_zero_of_exact {ψ : LA × LB →+ LX} {bd : LX →+ LY}
    (hex : Function.Exact ψ bd) {νA : AddMonoid.End LA} {νB : AddMonoid.End LB}
    {νX : AddMonoid.End LX} {νY : AddMonoid.End LY}
    (hψ : ∀ a b, ψ (νA a, νB b) = νX (ψ (a, b))) (hbd : ∀ x, bd (νX x) = νY (bd x))
    (hY : νY = 0) {k : ℕ} (hA : νA ^ k = 0) (hB : νB ^ k = 0) : νX ^ (k + 1) = 0 := by
  have hψk : ∀ m a b, ψ ((νA ^ m) a, (νB ^ m) b) = (νX ^ m) (ψ (a, b)) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro a b
      simp only [AddMonoid.End.coe_pow, Function.iterate_succ_apply'] at ih ⊢
      rw [hψ, ih]
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨⟨a, b⟩, hab⟩ := (hex (νX x)).1 (by rw [hbd, hY]; rfl)
  have hk := hψk k a b
  rw [hA, hB, hab] at hk
  calc (νX ^ (k + 1)) x = (νX ^ k) (νX x) := by rw [pow_succ]; rfl
    _ = 0 := by rw [← hk]; exact ψ.map_zero

end Step

/-- Mayer–Vietoris sequences over a lattice `α` of supports: groups `L S n`, maps `incl` induced
by inclusions of supports, and for every pair `A, B` the long exact sequence
`L (A ⊓ B) n → L A n × L B n → L (A ⊔ B) n → L (A ⊓ B) (n - 1)` with the conventions of
`IsLES.mayerVietoris`.

This is exactly what lower L-theory provides for `α` the closed invariant subsets of a compact
free `C_p`-space `T` and `L S n = L_n(𝒜_S(T))`: the localization sequences [CP95, 4.2] of the
Karoubi filtrations `𝒜_{A ∩ B} ⊂ 𝒜_A` and `𝒜_B ⊂ 𝒜_{A ∪ B}` (Lemma 2.1), the excision
equivalence (2.4) (Lemma 2.2, inside `A ∪ B` via Lemma 2.4), and Barratt–Whitehead.  No
functoriality of `incl`, vanishing of `L ⊥`, or compatibility between different pairs is
assumed. -/
structure MVSystem (α : Type u) [Lattice α] where
  /-- The groups `L_n(𝒜_S)`. -/
  L : α → ℤ → Type v
  [grp : ∀ S n, AddCommGroup (L S n)]
  /-- The map induced by the inclusion of support categories. -/
  incl : ∀ {S T : α}, S ≤ T → ∀ n, L S n →+ L T n
  /-- The Mayer–Vietoris boundary (4.1). -/
  bdry : ∀ A B n, L (A ⊔ B) (n + 1) →+ L (A ⊓ B) n
  isLES : ∀ A B, IsLES (mvIn (fun n => incl (inf_le_left : A ⊓ B ≤ A) n)
    (fun n => incl (inf_le_right : A ⊓ B ≤ B) n))
    (mvOut (fun n => incl (le_sup_right : B ≤ A ⊔ B) n) (fun n => incl (le_sup_left : A ≤ A ⊔ B) n))
    (bdry A B)

namespace MVSystem

attribute [instance] MVSystem.grp

variable {α : Type u} [Lattice α] {M : MVSystem.{u, v} α}

/-- Endomorphisms of all `L S n` commuting with the inclusions and the Mayer–Vietoris boundaries,
e.g. those induced by a duality-preserving functor such as `τ ⊗ (-)` which preserves every
support subcategory (manuscript l.239, R4.4). -/
structure NatEnd (M : MVSystem.{u, v} α) where
  app : ∀ S n, AddMonoid.End (M.L S n)
  incl_comm : ∀ {S T : α} (h : S ≤ T) n x, M.incl h n (app S n x) = app T n (M.incl h n x)
  bdry_comm : ∀ A B n x, M.bdry A B n (app (A ⊔ B) (n + 1) x) = app (A ⊓ B) n (M.bdry A B n x)

namespace NatEnd

/-- `ν = p - τ` (manuscript (6.1)). -/
def natSub (p : ℕ) (τ : M.NatEnd) : M.NatEnd where
  app S n := (p : AddMonoid.End (M.L S n)) - τ.app S n
  incl_comm h n x := by
    change M.incl h n (p • x - τ.app _ n x) = p • M.incl h n x - τ.app _ n (M.incl h n x)
    rw [map_sub, map_nsmul, τ.incl_comm]
  bdry_comm A B n x := by
    change M.bdry A B n (p • x - τ.app _ _ x) = p • M.bdry A B n x - τ.app _ n (M.bdry A B n x)
    rw [map_sub, map_nsmul, τ.bdry_comm]

@[simp] theorem natSub_app (p : ℕ) (τ : M.NatEnd) (S : α) (n : ℤ) :
    (natSub p τ).app S n = (p : AddMonoid.End (M.L S n)) - τ.app S n := rfl

variable (ν : M.NatEnd)

/-- One Mayer–Vietoris step: from `ν ^ k = 0` on `L A (n + 1)` and `L B (n + 1)` and `ν = 0` on
`L (A ⊓ B) n`, deduce `ν ^ (k + 1) = 0` on `L (A ⊔ B) (n + 1)`. -/
theorem pow_succ_eq_zero (A B : α) (n : ℤ) {k : ℕ} (hA : ν.app A (n + 1) ^ k = 0)
    (hB : ν.app B (n + 1) ^ k = 0) (hY : ν.app (A ⊓ B) n = 0) :
    ν.app (A ⊔ B) (n + 1) ^ (k + 1) = 0 :=
  pow_succ_eq_zero_of_exact ((M.isLES A B).exact_jδ n)
    (fun a b => by simp [ν.incl_comm]) (ν.bdry_comm A B n) hY hA hB

/-- **Lemma 6.2** (`ν ^ s = 0` on a union of `s` pieces), degreewise: if `ν = 0` on each piece
`T a` in degree `n + 1` and on every support below a piece in degree `n`, then
`ν ^ |I| = 0` on `L (⋃_{a ∈ I} T a) (n + 1)`.  As in the paper, the induction splits the union
as `A ∪ B` with `A` the union of the earlier pieces and `B` the new one. -/
theorem pow_card_eq_zero {ι : Type*} (T : ι → α) {I : Finset ι} (hI : I.Nonempty) (n : ℤ)
    (htop : ∀ a ∈ I, ν.app (T a) (n + 1) = 0) (hsub : ∀ a ∈ I, ∀ S ≤ T a, ν.app S n = 0) :
    ν.app (I.sup' hI T) (n + 1) ^ I.card = 0 := by
  induction hI using Finset.Nonempty.cons_induction with
  | singleton a =>
    rw [Finset.sup'_singleton, Finset.card_singleton, pow_one]
    exact htop a (Finset.mem_singleton_self a)
  | cons a I ha hI ih =>
    rw [Finset.sup'_cons hI, sup_comm, Finset.card_cons]
    refine ν.pow_succ_eq_zero _ _ n
      (ih (fun b hb => htop b (Finset.mem_cons_of_mem hb))
        (fun b hb => hsub b (Finset.mem_cons_of_mem hb)))
      ?_ (hsub a (Finset.mem_cons_self a I) _ inf_le_right)
    rw [htop a (Finset.mem_cons_self a I), zero_pow (Finset.card_ne_zero.2 hI)]

/-- Lemma 6.2 in all degrees, for local vanishing in all degrees (Lemma 6.1). -/
theorem pow_card_eq_zero' {ι : Type*} (T : ι → α) {I : Finset ι} (hI : I.Nonempty)
    (hloc : ∀ a ∈ I, ∀ S ≤ T a, ∀ n, ν.app S n = 0) (n : ℤ) :
    ν.app (I.sup' hI T) n ^ I.card = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (sub_add_cancel n 1).symm⟩
  exact ν.pow_card_eq_zero T hI m (fun a ha => hloc a ha _ le_rfl _)
    fun a ha S hS => hloc a ha S hS m

/-- Lemma 6.2 for a cover `X = T₁ ∪ ⋯ ∪ Tₛ`: `ν ^ s = 0` on `L X n` for every `n`. -/
theorem pow_eq_zero_of_isLUB {s : ℕ} (hs : 0 < s) (T : Fin s → α) {X : α}
    (hX : IsLUB (Set.range T) X) (hloc : ∀ a, ∀ S ≤ T a, ∀ n, ν.app S n = 0) (n : ℤ) :
    ν.app X n ^ s = 0 := by
  have hne : (Finset.univ : Finset (Fin s)).Nonempty := ⟨⟨0, hs⟩, Finset.mem_univ _⟩
  obtain rfl : Finset.univ.sup' hne T = X :=
    le_antisymm (Finset.sup'_le _ _ fun a _ => hX.1 ⟨a, rfl⟩)
      (hX.2 (by rintro _ ⟨a, rfl⟩; exact Finset.le_sup' T (Finset.mem_univ a)))
  simpa using ν.pow_card_eq_zero' T hne (fun a _ => hloc a) n

/-- Lemma 6.2 for `ν = p - τ ⊗ (-)` (6.1): if `τ` acts as `p` on every support below a piece
of the cover (Lemma 6.1), then `(p - τ) ^ s = 0` on `L X n`. -/
theorem natSub_pow_eq_zero (τ : M.NatEnd) (p : ℕ) {s : ℕ} (hs : 0 < s) (T : Fin s → α) {X : α}
    (hX : IsLUB (Set.range T) X) (hloc : ∀ a, ∀ S ≤ T a, ∀ n, τ.app S n = p) (n : ℤ) :
    ((p : AddMonoid.End (M.L X n)) - τ.app X n) ^ s = 0 :=
  (natSub p τ).pow_eq_zero_of_isLUB hs T hX (fun a S hS n => by simp [hloc a S hS n]) n

end NatEnd

end MVSystem

end HSFormal.MVNilpotence
