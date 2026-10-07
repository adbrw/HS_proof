import HSFormal.LTheory.Model.LineNatural
import HSFormal.LTheory.Model.Swindle
import Mathlib.Algebra.Colimit.Module

/-!
# The colimit model `Lmodel` (lower L-theory model, module 6)

`blueprint/lower-L-construction.md` §3.1, §3.2 "H4/H3", §4 row 6.

**Definition.**  `Lmodel A n = colim_k Lconc (C_ℤ^{∘k} A) (n + k)`, the mathlib
`AddCommGroup.DirectLimit` over `ℕ` of the levels `Lconc (A.czIter k) (deg n k)` along the
composites `SeqColim.stepLE` (via `Nat.leRecOn`) of the transitions
`step A n k = Lconc.tensorLine (A.czIter k) (deg n k)`, `[P] ↦ [P ⊗ ℝ]`.

**Degrees.**  The level degree is `Lmodel.deg n k`, defined by recursion so that
`deg n 0 = n` and `deg n (k + 1) = deg n k + 1` hold by `rfl`; with `A.czIter (k + 1) =
(A.czIter k).cz` (also `rfl`) the transition is literally `Lconc.tensorLine` and `cls` is
literally the level-`0` inclusion, with no cast.  `deg_eq : deg n k = n + k`.  For levels
written with any other degree expression `N = n + k`, `Lconc.castDeg` and `Lmodel.ofDeg` give the
same classes (`ofDeg_tensorLine`, `exists_ofDeg`, `map_ofDeg`).

**Main results.**
* The H3/H4 fields of `LowerLTheory`, in the exact form of `Interface.lean`: `Lmodel.map`,
  `map_id`, `map_comp`, `map_unitaryIso` (levelwise `Lconc.map_eq_of_unitaryIso` with
  `CZ.mapIterUnitaryIso`), `map_finSum` (levelwise `Lconc.map_finSum` with
  `CZ.mapIterIsFinSum`), `Lmodel.cls`, `cls_map`.  Levelwise maps commute with the transitions
  by `Lconc.tensorLine_map`.
* Elements: `exists_of` (every element is `of k x`), `of_tensorLine` (`[P ⊗ ℝ] = [P]`),
  `of_transit`, `of_eq_zero_iff`, `of_eq_of_iff` (equality iff agreement at a common later
  level), `hom_ext`, and the universal property `lift`/`lift_of` from families compatible with
  `tensorLine`.
* `of_injective`, `of_surjective`, `cls_bijective`: bijective transitions give bijective `cls`
  (for `dec_bij`, module 22).
* `eq_zero_of_swindle` (H4 + `InvCat.Swindle.eq_zero_of_map`), hence `Lmodel (C_{ℤ≷} B) n = 0`
  (`czPos_eq_zero`, `czNeg_eq_zero`).
-/

namespace HSFormal.LTheory

open CategoryTheory

noncomputable section

/-! ### Sequential direct limits of abelian groups -/

namespace SeqColim

variable {G : ℕ → Type*} [∀ k, AddCommGroup (G k)] (s : ∀ k, G k →+ G (k + 1))

/-- The composite `G i → G j` (`i ≤ j`) of the steps `s i, …, s (j - 1)`. -/
def stepLE (i j : ℕ) (h : i ≤ j) : G i →+ G j :=
  @Nat.leRecOn (fun j ↦ G i →+ G j) i j h (fun {k} g ↦ (s k).comp g) (AddMonoidHom.id (G i))

@[simp]
lemma stepLE_self (i : ℕ) (h : i ≤ i) : stepLE s i i h = AddMonoidHom.id (G i) :=
  Nat.leRecOn_self _

lemma stepLE_succ {i j : ℕ} (h : i ≤ j) (h' : i ≤ j + 1) :
    stepLE s i (j + 1) h' = (s j).comp (stepLE s i j h) :=
  Nat.leRecOn_succ h _

@[simp]
lemma stepLE_succ_self (i : ℕ) (h : i ≤ i + 1) : stepLE s i (i + 1) h = s i := by
  rw [stepLE_succ s le_rfl, stepLE_self]; rfl

lemma stepLE_comp {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    (stepLE s j k hjk).comp (stepLE s i j hij) = stepLE s i k (hij.trans hjk) := by
  induction k, hjk using Nat.le_induction with
  | base => rw [stepLE_self]; rfl
  | succ k hjk ih =>
    rw [stepLE_succ s hjk, AddMonoidHom.comp_assoc, ih, ← stepLE_succ]

instance directedSystem : DirectedSystem G fun i j h ↦ stepLE s i j h where
  map_self i x := by rw [stepLE_self]; rfl
  map_map _ _ _ hij hjk x := DFunLike.congr_fun (stepLE_comp s hij hjk) x

/-- Levelwise maps commuting with the steps commute with their composites. -/
lemma comp_stepLE {G' : ℕ → Type*} [∀ k, AddCommGroup (G' k)]
    {s' : ∀ k, G' k →+ G' (k + 1)} (g : ∀ k, G k →+ G' k)
    (hg : ∀ k x, g (k + 1) (s k x) = s' k (g k x)) {i j : ℕ}
    (h : i ≤ j) : (g j).comp (stepLE s i j h) = (stepLE s' i j h).comp (g i) := by
  induction j, h using Nat.le_induction with
  | base => rw [stepLE_self, stepLE_self]; rfl
  | succ j hij ih =>
    rw [stepLE_succ s hij, stepLE_succ s' hij, AddMonoidHom.comp_assoc, ← ih,
      ← AddMonoidHom.comp_assoc, ← AddMonoidHom.comp_assoc]
    congr 1
    ext x
    exact hg j x

/-- A family of maps compatible with the steps is compatible with their composites. -/
lemma apply_stepLE {P : Type*} [AddCommMonoid P] (g : ∀ k, G k →+ P)
    (hg : ∀ k x, g (k + 1) (s k x) = g k x) {i j : ℕ} (h : i ≤ j) (x : G i) :
    g j (stepLE s i j h x) = g i x := by
  induction j, h using Nat.le_induction with
  | base => rw [stepLE_self]; rfl
  | succ j hij ih => rw [stepLE_succ s hij, AddMonoidHom.comp_apply, hg, ih]

lemma stepLE_injective {i : ℕ} (hs : ∀ k, i ≤ k → Function.Injective (s k)) {j : ℕ}
    (h : i ≤ j) : Function.Injective (stepLE s i j h) := by
  induction j, h using Nat.le_induction with
  | base => rw [stepLE_self]; exact Function.injective_id
  | succ j hij ih => rw [stepLE_succ s hij, AddMonoidHom.coe_comp]; exact (hs j hij).comp ih

lemma stepLE_surjective {i : ℕ} (hs : ∀ k, i ≤ k → Function.Surjective (s k)) {j : ℕ}
    (h : i ≤ j) : Function.Surjective (stepLE s i j h) := by
  induction j, h using Nat.le_induction with
  | base => rw [stepLE_self]; exact Function.surjective_id
  | succ j hij ih => rw [stepLE_succ s hij, AddMonoidHom.coe_comp]; exact (hs j hij).comp ih

end SeqColim

/-! ### Degree casts of `Lconc` -/

namespace Lconc

variable {A B : InvCat} {N M K : ℤ}

/-- `Lconc A N ≃+ Lconc A M` along an equality of degrees `N = M`. -/
def castDeg (h : N = M) : Lconc A N ≃+ Lconc A M :=
  h ▸ AddEquiv.refl _

@[simp]
lemma castDeg_rfl : castDeg (A := A) (rfl : N = N) = AddEquiv.refl _ := rfl

/-- A cast along `N = N` (any proof) is the identity, by `rfl`. -/
lemma castDeg_self (h : N = N) (x : Lconc A N) : castDeg h x = x := rfl

@[simp]
lemma castDeg_castDeg (h : N = M) (h' : M = K) (x : Lconc A N) :
    castDeg h' (castDeg h x) = castDeg (h.trans h') x := by
  subst h h'; rfl

@[simp]
lemma castDeg_symm (h : N = M) : (castDeg h).symm = castDeg (A := A) h.symm := by
  subst h; rfl

lemma castDeg_cls (h : N = M) (P : SymPoincare A.inv N) : castDeg h (cls P) = cls (h ▸ P) := by
  subst h; rfl

lemma map_castDeg (Φ : A ⟶ B) (h : N = M) (x : Lconc A N) :
    map Φ (castDeg h x) = castDeg h (map Φ x) := by
  subst h; rfl

lemma tensorLine_castDeg (h : N = M) (x : Lconc A N) :
    tensorLine A M (castDeg h x) = castDeg (congrArg (· + 1) h) (tensorLine A N x) := by
  subst h; rfl

end Lconc

/-! ### The model -/

namespace Lmodel

/-- The degree `n + k` of the `k`-th level, by recursion on `k`, so that `deg n 0 = n` and
`deg n (k + 1) = deg n k + 1` hold by `rfl` (`deg_eq`: `deg n k = n + k`). -/
@[implicit_reducible]
def deg (n : ℤ) : ℕ → ℤ
  | 0 => n
  | k + 1 => deg n k + 1

@[simp] lemma deg_zero (n : ℤ) : deg n 0 = n := rfl

@[simp] lemma deg_succ (n : ℤ) (k : ℕ) : deg n (k + 1) = deg n k + 1 := rfl

lemma deg_eq (n : ℤ) (k : ℕ) : deg n k = n + k := by
  induction k with
  | zero => simp
  | succ k ih => rw [deg_succ, ih]; push_cast; ring

lemma deg_add (n m : ℤ) (k : ℕ) : deg (n + m) k = deg n k + m := by
  rw [deg_eq, deg_eq]; ring

lemma deg_nonneg {n : ℤ} (hn : 0 ≤ n) (k : ℕ) : 0 ≤ deg n k := by
  rw [deg_eq]; omega

variable (A : InvCat) (n : ℤ)

/-- The transition `[P] ↦ [P ⊗ ℝ]` from level `k` to level `k + 1`. -/
def step (k : ℕ) : Lconc (A.czIter k) (deg n k) →+ Lconc (A.czIter (k + 1)) (deg n (k + 1)) :=
  Lconc.tensorLine (A.czIter k) (deg n k)

end Lmodel

/-- **The colimit model** `L A n = colim_k Lconc (C_ℤ^{∘k} A) (n + k)` along `− ⊗ ℝ`
(blueprint §3.1). -/
def Lmodel (A : InvCat) (n : ℤ) : Type :=
  AddCommGroup.DirectLimit (fun k ↦ Lconc (A.czIter k) (Lmodel.deg n k))
    (SeqColim.stepLE (Lmodel.step A n))

namespace Lmodel

instance (A : InvCat) (n : ℤ) : AddCommGroup (Lmodel A n) :=
  AddCommGroup.DirectLimit.addCommGroup _ _

variable (A : InvCat) (n : ℤ)

/-- The inclusion of the `k`-th level. -/
def of (k : ℕ) : Lconc (A.czIter k) (deg n k) →+ Lmodel A n :=
  AddCommGroup.DirectLimit.of (fun k ↦ Lconc (A.czIter k) (deg n k))
    (SeqColim.stepLE (step A n)) k

/-- The composite transition from level `i` to level `j ≥ i`. -/
def transit {i j : ℕ} (h : i ≤ j) :
    Lconc (A.czIter i) (deg n i) →+ Lconc (A.czIter j) (deg n j) :=
  SeqColim.stepLE (step A n) i j h

/-- **H3** The decoration map `cls : Lconc A N → Lmodel A N`, the inclusion of level `0`. -/
def cls (N : ℤ) : Lconc A N →+ Lmodel A N := of A N 0

variable {A n}

/-! #### Transitions -/

@[simp]
lemma transit_self (k : ℕ) (h : k ≤ k) : transit A n h = AddMonoidHom.id _ :=
  SeqColim.stepLE_self (step A n) k h

@[simp]
lemma transit_succ_self (k : ℕ) (h : k ≤ k + 1) :
    transit A n h = Lconc.tensorLine (A.czIter k) (deg n k) :=
  SeqColim.stepLE_succ_self (step A n) k h

lemma transit_succ {i j : ℕ} (h : i ≤ j) (h' : i ≤ j + 1) (x : Lconc (A.czIter i) (deg n i)) :
    transit A n h' x = Lconc.tensorLine (A.czIter j) (deg n j) (transit A n h x) :=
  DFunLike.congr_fun (SeqColim.stepLE_succ (step A n) h h') x

lemma transit_transit {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (x : Lconc (A.czIter i) (deg n i)) :
    transit A n hjk (transit A n hij x) = transit A n (hij.trans hjk) x :=
  DFunLike.congr_fun (SeqColim.stepLE_comp (step A n) hij hjk) x

/-! #### Elements -/

@[simp]
lemma of_transit {i j : ℕ} (h : i ≤ j) (x : Lconc (A.czIter i) (deg n i)) :
    of A n j (transit A n h x) = of A n i x :=
  AddCommGroup.DirectLimit.of_f (G := fun k ↦ Lconc (A.czIter k) (deg n k)) h x

/-- **Compatibility with the transitions**: `[P ⊗ ℝ] = [P]` in the colimit. -/
@[simp]
lemma of_tensorLine (k : ℕ) (x : Lconc (A.czIter k) (deg n k)) :
    of A n (k + 1) (Lconc.tensorLine (A.czIter k) (deg n k) x) = of A n k x := by
  have h := of_transit (A := A) (n := n) (Nat.le_succ k) x
  rw [transit_succ_self] at h
  exact h

/-- Every element of the colimit comes from some level. -/
theorem exists_of (z : Lmodel A n) : ∃ k x, of A n k x = z :=
  AddCommGroup.DirectLimit.induction_on (G := fun k ↦ Lconc (A.czIter k) (deg n k))
    (C := fun z ↦ ∃ k x, of A n k x = z) z fun k x ↦ ⟨k, x, rfl⟩

/-- Two elements of the colimit given at the same level `k` lie in a common level `≥ k`. -/
theorem exists_of₂ (z w : Lmodel A n) : ∃ k x y, of A n k x = z ∧ of A n k y = w := by
  obtain ⟨i, x, rfl⟩ := exists_of z
  obtain ⟨j, y, rfl⟩ := exists_of w
  exact ⟨max i j, transit A n (le_max_left i j) x, transit A n (le_max_right i j) y,
    of_transit _ _, of_transit _ _⟩

/-- An element of a level vanishes in the colimit iff it vanishes at some later level. -/
theorem of_eq_zero_iff {k : ℕ} (x : Lconc (A.czIter k) (deg n k)) :
    of A n k x = 0 ↔ ∃ l, ∃ h : k ≤ l, transit A n h x = 0 := by
  refine ⟨fun hx ↦ AddCommGroup.DirectLimit.of.zero_exact
    (G := fun k ↦ Lconc (A.czIter k) (deg n k)) (f := SeqColim.stepLE (step A n)) k x hx, ?_⟩
  rintro ⟨l, h, hx⟩
  rw [← of_transit h, hx, map_zero]

/-- Two elements of levels `i`, `j` agree in the colimit iff they agree at a common later
level. -/
theorem of_eq_of_iff {i j : ℕ} (x : Lconc (A.czIter i) (deg n i))
    (y : Lconc (A.czIter j) (deg n j)) :
    of A n i x = of A n j y ↔
      ∃ l, ∃ (hi : i ≤ l) (hj : j ≤ l), transit A n hi x = transit A n hj y := by
  constructor
  · intro hxy
    have h0 : of A n (max i j) (transit A n (le_max_left i j) x -
        transit A n (le_max_right i j) y) = 0 := by
      rw [map_sub, of_transit, of_transit, hxy, sub_self]
    obtain ⟨l, hl, h⟩ := (of_eq_zero_iff _).mp h0
    refine ⟨l, (le_max_left i j).trans hl, (le_max_right i j).trans hl, ?_⟩
    rwa [map_sub, transit_transit, transit_transit, sub_eq_zero] at h
  · rintro ⟨l, hi, hj, h⟩
    rw [← of_transit hi, h, of_transit]

/-- Equality at a common level `k`. -/
theorem of_eq_of_iff_same {k : ℕ} (x y : Lconc (A.czIter k) (deg n k)) :
    of A n k x = of A n k y ↔ ∃ l, ∃ h : k ≤ l, transit A n h x = transit A n h y := by
  rw [of_eq_of_iff]
  exact ⟨fun ⟨l, hi, _, h⟩ ↦ ⟨l, hi, h⟩, fun ⟨l, h, h'⟩ ↦ ⟨l, h, h, h'⟩⟩

/-- Homomorphisms out of the colimit agree if they agree on every level. -/
theorem hom_ext {P : Type*} [AddCommMonoid P] {g₁ g₂ : Lmodel A n →+ P}
    (h : ∀ k x, g₁ (of A n k x) = g₂ (of A n k x)) : g₁ = g₂ :=
  AddCommGroup.DirectLimit.hom_ext (G := fun k ↦ Lconc (A.czIter k) (deg n k))
    (f := SeqColim.stepLE (step A n)) P fun k ↦ AddMonoidHom.ext (h k)

/-! #### The universal property -/

variable (A n) in
/-- **Universal property**: a family of homomorphisms out of the levels which is compatible
with `− ⊗ ℝ` descends to the colimit. -/
def lift {P : Type*} [AddCommMonoid P] (g : ∀ k, Lconc (A.czIter k) (deg n k) →+ P)
    (hg : ∀ k x, g (k + 1) (Lconc.tensorLine (A.czIter k) (deg n k) x) = g k x) :
    Lmodel A n →+ P :=
  AddCommGroup.DirectLimit.lift (fun k ↦ Lconc (A.czIter k) (deg n k))
    (SeqColim.stepLE (step A n)) P g fun _ _ h x ↦ SeqColim.apply_stepLE _ g hg h x

@[simp]
lemma lift_of {P : Type*} [AddCommMonoid P] (g : ∀ k, Lconc (A.czIter k) (deg n k) →+ P)
    (hg : ∀ k x, g (k + 1) (Lconc.tensorLine (A.czIter k) (deg n k) x) = g k x) (k : ℕ)
    (x : Lconc (A.czIter k) (deg n k)) : lift A n g hg (of A n k x) = g k x :=
  AddCommGroup.DirectLimit.lift_of (G := fun k ↦ Lconc (A.czIter k) (deg n k)) P g _ k x

@[simp]
lemma lift_cls {P : Type*} [AddCommMonoid P] (g : ∀ k, Lconc (A.czIter k) (deg n k) →+ P)
    (hg : ∀ k x, g (k + 1) (Lconc.tensorLine (A.czIter k) (deg n k) x) = g k x)
    (x : Lconc A n) : lift A n g hg (cls A n x) = g 0 x :=
  lift_of g hg 0 x

/-! #### Functoriality (H4) -/

/-- `Lconc.map (mapIter k Φ)` commutes with the transitions (`Lconc.tensorLine_map`). -/
lemma map_mapIter_tensorLine {B : InvCat} (Φ : A ⟶ B) (k : ℕ)
    (x : Lconc (A.czIter k) (deg n k)) :
    Lconc.map (CZ.mapIter (k + 1) Φ) (Lconc.tensorLine (A.czIter k) (deg n k) x) =
      Lconc.tensorLine (B.czIter k) (deg n k) (Lconc.map (CZ.mapIter k Φ) x) :=
  (Lconc.tensorLine_map (CZ.mapIter k Φ) x).symm

/-- `Lconc.map (mapIter j Φ)` commutes with the composite transitions. -/
lemma map_mapIter_transit {B : InvCat} (Φ : A ⟶ B) {i j : ℕ} (h : i ≤ j)
    (x : Lconc (A.czIter i) (deg n i)) :
    Lconc.map (CZ.mapIter j Φ) (transit A n h x) =
      transit B n h (Lconc.map (CZ.mapIter i Φ) x) :=
  DFunLike.congr_fun (SeqColim.comp_stepLE (step A n) (s' := step B n)
    (fun k ↦ Lconc.map (CZ.mapIter k Φ)) (map_mapIter_tensorLine Φ) h) x

lemma map_compat {B : InvCat} (Φ : A ⟶ B) (i j : ℕ) (h : i ≤ j) :
    (Lconc.map (CZ.mapIter j Φ)).comp (SeqColim.stepLE (step A n) i j h) =
      (SeqColim.stepLE (step B n) i j h).comp (Lconc.map (CZ.mapIter i Φ)) :=
  SeqColim.comp_stepLE (step A n) (s' := step B n) (fun k ↦ Lconc.map (CZ.mapIter k Φ))
    (map_mapIter_tensorLine Φ) h

/-- **H4** Functoriality: levelwise `Lconc.map (C_ℤ^{∘k} Φ)`. -/
def map {A B : InvCat} (Φ : A ⟶ B) (n : ℤ) : Lmodel A n →+ Lmodel B n :=
  AddCommGroup.DirectLimit.map (G := fun k ↦ Lconc (A.czIter k) (deg n k))
    (G' := fun k ↦ Lconc (B.czIter k) (deg n k)) (f := SeqColim.stepLE (step A n))
    (f' := SeqColim.stepLE (step B n)) (fun k ↦ Lconc.map (CZ.mapIter k Φ)) (map_compat Φ)

@[simp]
lemma map_of {B : InvCat} (Φ : A ⟶ B) (k : ℕ) (x : Lconc (A.czIter k) (deg n k)) :
    map Φ n (of A n k x) = of B n k (Lconc.map (CZ.mapIter k Φ) x) :=
  AddCommGroup.DirectLimit.map_apply_of (G := fun k ↦ Lconc (A.czIter k) (deg n k))
    (G' := fun k ↦ Lconc (B.czIter k) (deg n k)) (fun k ↦ Lconc.map (CZ.mapIter k Φ))
    (map_compat Φ) x

variable (A n) in
/-- **H4** `map (𝟙 A) = id`. -/
theorem map_id : map (𝟙 A) n = AddMonoidHom.id (Lmodel A n) :=
  hom_ext fun k x ↦ by rw [map_of, CZ.mapIter_id, Lconc.map_id]; rfl

/-- **H4** `map (Φ ≫ Ψ) = map Ψ ∘ map Φ`. -/
theorem map_comp {B C : InvCat} (Φ : A ⟶ B) (Ψ : B ⟶ C) (n : ℤ) :
    map (Φ ≫ Ψ) n = (map Ψ n).comp (map Φ n) :=
  hom_ext fun k x ↦ by
    rw [AddMonoidHom.comp_apply, map_of, map_of, map_of, CZ.mapIter_comp, Lconc.map_comp]; rfl

/-- **H4** Unitarily isomorphic functors induce the same map (levelwise
`Lconc.map_eq_of_unitaryIso`). -/
theorem map_unitaryIso {B : InvCat} {Φ Ψ : A ⟶ B} (e : InvCat.UnitaryIso Φ Ψ) (n : ℤ) :
    map Φ n = map Ψ n :=
  hom_ext fun k x ↦ by
    rw [map_of, map_of, Lconc.map_eq_of_unitaryIso (CZ.mapIterUnitaryIso k e)]

/-- **H4** Additivity along finite unitary sums (levelwise `Lconc.map_finSum`). -/
theorem map_finSum {B : InvCat} {ι : Type*} [Fintype ι] {Φ : ι → (A ⟶ B)} {S : A ⟶ B}
    (h : InvCat.IsFinSum Φ S) (n : ℤ) : map S n = ∑ i, map (Φ i) n :=
  hom_ext fun k x ↦ by
    rw [map_of, Lconc.map_finSum (CZ.mapIterIsFinSum k h), AddMonoidHom.finset_sum_apply,
      AddMonoidHom.finset_sum_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ (map_of (Φ i) k x).symm

/-- **H3** Naturality of `cls`. -/
theorem cls_map {B : InvCat} (Φ : A ⟶ B) (N : ℤ) (x : Lconc A N) :
    cls B N (Lconc.map Φ x) = map Φ N (cls A N x) :=
  (map_of Φ 0 x).symm

lemma cls_eq_of (x : Lconc A n) : cls A n x = of A n 0 x := rfl

/-! #### Levels in the form `Lconc (C_ℤ^{∘k} A) N` with `N = n + k` -/

variable (A n) in
/-- The class in `Lmodel A n` of an element of `Lconc (C_ℤ^{∘k} A) N` for any degree
`N = n + k` (a cast of `of A n k`). -/
def ofDeg (k : ℕ) {N : ℤ} (h : N = n + k) : Lconc (A.czIter k) N →+ Lmodel A n :=
  (of A n k).comp (Lconc.castDeg (h.trans (deg_eq n k).symm)).toAddMonoidHom

lemma ofDeg_apply (k : ℕ) {N : ℤ} (h : N = n + k) (x : Lconc (A.czIter k) N) :
    ofDeg A n k h x = of A n k (Lconc.castDeg (h.trans (deg_eq n k).symm) x) := rfl

lemma of_eq_ofDeg (k : ℕ) (x : Lconc (A.czIter k) (deg n k)) :
    of A n k x = ofDeg A n k (deg_eq n k) x := rfl

lemma of_eq_ofDeg_castDeg (k : ℕ) (x : Lconc (A.czIter k) (deg n k)) :
    of A n k x = ofDeg A n k rfl (Lconc.castDeg (deg_eq n k) x) := by
  rw [ofDeg_apply, Lconc.castDeg_castDeg]; rfl

lemma ofDeg_zero {N : ℤ} (h : N = n + ((0 : ℕ) : ℤ)) (x : Lconc A N) :
    ofDeg A n 0 h x = cls A n (Lconc.castDeg (by simpa using h) x) := rfl

/-- Compatibility with the transitions, in any degree form. -/
lemma ofDeg_tensorLine (k : ℕ) {N : ℤ} (h : N = n + k) (h' : N + 1 = n + ((k + 1 : ℕ) : ℤ))
    (x : Lconc (A.czIter k) N) :
    ofDeg A n (k + 1) h' (Lconc.tensorLine (A.czIter k) N x) = ofDeg A n k h x := by
  obtain rfl : N = deg n k := h.trans (deg_eq n k).symm
  exact of_tensorLine k x

/-- Every element of `Lmodel A n` is `ofDeg k x` for some `x : Lconc (C_ℤ^{∘k} A) (n + k)`. -/
theorem exists_ofDeg (z : Lmodel A n) :
    ∃ (k : ℕ) (x : Lconc (A.czIter k) (n + k)), ofDeg A n k rfl x = z := by
  obtain ⟨k, x, rfl⟩ := exists_of z
  exact ⟨k, Lconc.castDeg (deg_eq n k) x, (of_eq_ofDeg_castDeg k x).symm⟩

@[simp]
lemma ofDeg_castDeg (k : ℕ) {N M : ℤ} (h : M = n + k) (h' : N = M) (x : Lconc (A.czIter k) N) :
    ofDeg A n k h (Lconc.castDeg h' x) = ofDeg A n k (h'.trans h) x := by
  rw [ofDeg_apply, ofDeg_apply, Lconc.castDeg_castDeg]

lemma map_ofDeg {B : InvCat} (Φ : A ⟶ B) (k : ℕ) {N : ℤ} (h : N = n + k)
    (x : Lconc (A.czIter k) N) :
    map Φ n (ofDeg A n k h x) = ofDeg B n k h (Lconc.map (CZ.mapIter k Φ) x) := by
  rw [ofDeg_apply, ofDeg_apply, map_of, Lconc.map_castDeg]

/-! #### Bijectivity criteria (for `dec_bij`, module 22) -/

/-- If the transitions out of the levels `≥ i` are injective, then so is `of A n i`. -/
theorem of_injective (i : ℕ)
    (h : ∀ k, i ≤ k → Function.Injective (Lconc.tensorLine (A.czIter k) (deg n k))) :
    Function.Injective (of A n i) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨l, hl, hx⟩ := (of_eq_zero_iff x).mp hx
  exact SeqColim.stepLE_injective (step A n) h hl (hx.trans (map_zero _).symm)

/-- If the transitions out of the levels `≥ i` are surjective, then so is `of A n i`. -/
theorem of_surjective (i : ℕ)
    (h : ∀ k, i ≤ k → Function.Surjective (Lconc.tensorLine (A.czIter k) (deg n k))) :
    Function.Surjective (of A n i) := by
  intro z
  obtain ⟨k, y, rfl⟩ := exists_of z
  rcases le_total k i with hki | hik
  · exact ⟨transit A n hki y, of_transit hki y⟩
  · obtain ⟨x, rfl⟩ := SeqColim.stepLE_surjective (step A n) h hik y
    exact ⟨x, (of_transit hik x).symm⟩

/-- If all transitions are bijective, then `cls : Lconc A n → Lmodel A n` is bijective. -/
theorem cls_bijective
    (h : ∀ k, Function.Bijective (Lconc.tensorLine (A.czIter k) (deg n k))) :
    Function.Bijective (cls A n) :=
  ⟨of_injective 0 fun k _ ↦ (h k).1, of_surjective 0 fun k _ ↦ (h k).2⟩

/-- `cls : Lconc A n → Lmodel A n` is bijective for `n ≥ 0` if every transition
`Lconc (C_ℤ^{∘k} A) N → Lconc (C_ℤ^{∘k+1} A) (N + 1)` with `N ≥ 0` is bijective. -/
theorem cls_bijective_of_nonneg (hn : 0 ≤ n)
    (h : ∀ (k : ℕ) (N : ℤ), 0 ≤ N → Function.Bijective (Lconc.tensorLine (A.czIter k) N)) :
    Function.Bijective (cls A n) :=
  cls_bijective fun k ↦ h k _ (deg_nonneg hn k)

/-! #### Swindles -/

/-- **`Lmodel A n = 0`** if `A` carries an Eilenberg swindle (from H4 alone, via
`InvCat.Swindle.eq_zero_of_map`). -/
theorem eq_zero_of_swindle (s : A.Swindle) (x : Lmodel A n) : x = 0 :=
  s.eq_zero_of_map (fun Φ ↦ map Φ n) (map_id A n) (fun Φ Ψ ↦ map_comp Φ Ψ n)
    (fun e ↦ map_unitaryIso e n) (fun h ↦ map_finSum h n) x

/-- `Lmodel (C_{ℤ≥} B) n = 0`. -/
theorem czPos_eq_zero (B : InvCat) (x : Lmodel B.czPos n) : x = 0 :=
  eq_zero_of_swindle (CZ.posSwindle B) x

/-- `Lmodel (C_{ℤ≤} B) n = 0`. -/
theorem czNeg_eq_zero (B : InvCat) (x : Lmodel B.czNeg n) : x = 0 :=
  eq_zero_of_swindle (CZ.negSwindle B) x

instance (B : InvCat) (n : ℤ) : Subsingleton (Lmodel B.czPos n) :=
  ⟨fun x y ↦ by rw [czPos_eq_zero B x, czPos_eq_zero B y]⟩

instance (B : InvCat) (n : ℤ) : Subsingleton (Lmodel B.czNeg n) :=
  ⟨fun x y ↦ by rw [czNeg_eq_zero B x, czNeg_eq_zero B y]⟩

end Lmodel

end

end HSFormal.LTheory
