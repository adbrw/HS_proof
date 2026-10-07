import HSFormal.LTheory.Model.NegK.KarDiagStatement
import HSFormal.LTheory.Model.NegK.FreeQGMat
import HSFormal.LTheory.Model.NegK.TwoFlag
import HSFormal.LTheory.Model.Swindle

/-!
# Theorem A: bounded idempotents of `C_ℤ(finSuppFreeQG G T)` are diagonal (NegK level 1, module 5)

`blueprint/negK-proof.md` §2.4 and §5 row 5.  Proves `karDiag : KarDiagStatement`.

**Construction.**  Fix `X ∈ C_ℤ(B)`, `B = finSuppFreeQG G T`, and an idempotent `p` of
propagation `≤ b`.
* For every fibre `i : ℕ`, the fibre matrix `pf i w' w = lin (p w' w) i` (`FreeQGMat`) is a bounded
  idempotent matrix of `ℚ[Gᵢ]`-linear maps (`isBounded_pf`, `isIdem_pf`), and `𝕍ᵢ = Π_w Fibᵢ X_w`
  is semisimple (Maschke).  `TwoFlag.exists_blocks` gives the blocks `A i v u w`, `B i w v u`;
  `exists_blocks` collects them over **all** `i` (`Blocks`), so `T` may be infinite.
* `Q_v = ⊞_{u ∈ [v - 2b, v]} X_u` is the chosen unitary partial sum `CZ.Tower.obj X.obj (v-2b)
  (2b+1)`, with inclusions `ι v u` and projections `πT v u = ι^*`.  `toT`/`ofT`/`tmap` assemble
  block families into maps into, out of, and between the `Q_v`; only the Tower relations
  `ι_u ι_u^* = 1`, `ι_u ι_{u'}^* = 0` are used.
* The block morphisms `Am v u w = ofLin (A · v u w)`, `Bm w v u = ofLin (B · w v u)` (all `i` at
  once), `α₀ = (toT v (Am v · w))_{v,w}` (propagation `b`), `β₀ = (ofT v (Bm w v ·))_{w,v}`
  (propagation `2b`), `d v = tmap v v (Bm · v ·)`.
* `α₀ ≫ β₀ = p`, `β₀ ≫ α₀ = diag d`, `d v ≫ d v = d v` are checked fibrewise through the jointly
  faithful `lin` (`lin_ext`) from the identities (I1)–(I3) of `TwoFlag`.
* Finally `α = α₀ ≫ diag d`, `β = diag d ≫ β₀` satisfy the Kar conditions as well
  (`kar_of_split`), with the same propagation bounds.
-/

namespace HSFormal.LTheory.KarDiag

open CategoryTheory Category Limits Preadditive Finset FreeQGMat

noncomputable section

/-! ### Kar isomorphisms from a splitting -/

/-- From `α₀ β₀ = p`, `β₀ α₀ = q` (idempotents), the maps `α₀ q`, `q β₀` form a Kar isomorphism
`(X, p) ≅ (Q, q)`. -/
lemma kar_of_split {V : Type*} [Category V] {X Q : V} {p : X ⟶ X} {q : Q ⟶ Q}
    (hp : p ≫ p = p) (hq : q ≫ q = q) {α₀ : X ⟶ Q} {β₀ : Q ⟶ X} (h₁ : α₀ ≫ β₀ = p)
    (h₂ : β₀ ≫ α₀ = q) :
    (α₀ ≫ q) ≫ (q ≫ β₀) = p ∧ (q ≫ β₀) ≫ (α₀ ≫ q) = q ∧ p ≫ (α₀ ≫ q) = α₀ ≫ q ∧
      (α₀ ≫ q) ≫ q = α₀ ≫ q ∧ q ≫ (q ≫ β₀) = q ≫ β₀ ∧ (q ≫ β₀) ≫ p = q ≫ β₀ := by
  subst h₁ h₂
  have hp' : ∀ {Z : V} (h : X ⟶ Z), α₀ ≫ β₀ ≫ α₀ ≫ β₀ ≫ h = α₀ ≫ β₀ ≫ h := fun h ↦ by
    simpa only [assoc] using hp =≫ h
  have hq' : ∀ {Z : V} (h : Q ⟶ Z), β₀ ≫ α₀ ≫ β₀ ≫ α₀ ≫ h = β₀ ≫ α₀ ≫ h := fun h ↦ by
    simpa only [assoc] using hq =≫ h
  have hp'' : α₀ ≫ β₀ ≫ α₀ ≫ β₀ = α₀ ≫ β₀ := by simpa only [assoc] using hp
  have hq'' : β₀ ≫ α₀ ≫ β₀ ≫ α₀ = β₀ ≫ α₀ := by simpa only [assoc] using hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [assoc, hp'', hq'']

/-! ### The fibre data -/

variable {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)] {T : Set ℕ}

section Fibre

variable (X : (finSuppFreeQG G T).cz) (p : X ⟶ X) (b : ℕ)

/-- The fibre matrix of `p` at `i`. -/
def pf (i : ℕ) (w' w : ℤ) : Fib (X.obj w) i →ₗ[MonoidAlgebra ℚ (G i)] Fib (X.obj w') i :=
  lin (p.1 w' w) i

variable {X p b}

lemma isBounded_pf (hb : CZ.PropLE p.1 b) (i : ℕ) : LineModule.IsBounded (pf X p i) b :=
  fun w' w h ↦ by rw [pf, hb w' w h, lin_zero]

lemma isIdem_pf (hp : p ≫ p = p) (hb : CZ.PropLE p.1 b) (i : ℕ) :
    LineModule.IsIdem (pf X p i) b := fun w'' w ↦ by
  have := congrArg (fun f : X ⟶ X ↦ lin (f.1 w'' w) i) hp
  simp only [CZ.comp_apply_left p hb p, lin_sum, lin_comp] at this
  exact this

variable (X p b)

/-- The two-flag blocks of all fibres (`TwoFlag.exists_blocks`). -/
structure Blocks where
  /-- Blocks of `α`. -/
  A : ∀ i, ℤ → ∀ u w : ℤ, Fib (X.obj w) i →ₗ[MonoidAlgebra ℚ (G i)] Fib (X.obj u) i
  /-- Blocks of `β` and of the diagonal idempotent. -/
  B : ∀ i (w : ℤ), ℤ → ∀ u : ℤ, Fib (X.obj u) i →ₗ[MonoidAlgebra ℚ (G i)] Fib (X.obj w) i
  A_zero : ∀ i (v u w : ℤ), (b : ℤ) < |v - w| → A i v u w = 0
  B_zero : ∀ i (w v u : ℤ), w < v - 2 * b ∨ v < w → B i w v u = 0
  I1 : ∀ i (w' w : ℤ) (s : Finset ℤ), LineModule.win w b ⊆ s →
    ∑ v ∈ s, ∑ u ∈ Icc (v - 2 * b) v, (B i w' v u).comp (A i v u w) = pf X p i w' w
  I2 : ∀ i (v' v u' u : ℤ) (s : Finset ℤ), Icc (v - 2 * b) v ⊆ s →
    ∑ w ∈ s, (A i v' u' w).comp (B i w v u) = if v' = v then B i u' v u else 0
  I3 : ∀ i (v u'' u : ℤ), ∑ u' ∈ Icc (v - 2 * b) v, (B i u'' v u').comp (B i u' v u) = B i u'' v u

variable {X p b}

lemma exists_blocks (hp : p ≫ p = p) (hb : CZ.PropLE p.1 b) : Nonempty (Blocks X p b) := by
  choose A B hA hB h1 h2 h3 using fun i ↦
    TwoFlag.exists_blocks (V := fun w ↦ Fib (X.obj w) i) (isBounded_pf hb i) (isIdem_pf hp hb i)
  exact ⟨⟨A, B, hA, hB, h1, h2, h3⟩⟩

end Fibre

/-! ### Maps into, out of and between the window sums `Q_v` -/

section Tower

variable (X : (finSuppFreeQG G T).cz) (b : ℕ)

/-- `Q_v = ⊞_{u ∈ [v - 2b, v]} X_u` (chosen unitary partial sums). -/
def Q : (finSuppFreeQG G T).cz := ⟨fun v ↦ CZ.Tower.obj X.obj (v - 2 * b) (2 * b + 1)⟩

/-- The window `[v - 2b, v]`. -/
def I (v : ℤ) : Finset ℤ := Icc (v - 2 * b) v

/-- The inclusion `X_u → Q_v`. -/
def ι (v u : ℤ) : X.obj u ⟶ (Q X b).obj v := CZ.Tower.inc X.obj (v - 2 * b) (2 * b + 1) u

/-- The projection `Q_v → X_u`. -/
def πT (v u : ℤ) : (Q X b).obj v ⟶ X.obj u := (finSuppFreeQG G T).inv.star (ι X b v u)

variable {X b}

@[reassoc]
lemma ι_πT_self {v u : ℤ} (hu : u ∈ I b v) : ι X b v u ≫ πT X b v u = 𝟙 _ := by
  rw [I, mem_Icc] at hu
  exact CZ.Tower.inc_star_self _ _ _ hu.1 (by push_cast; omega)

@[reassoc]
lemma ι_πT_ne (v : ℤ) {u u' : ℤ} (h : u ≠ u') : ι X b v u ≫ πT X b v u' = 0 :=
  CZ.Tower.inc_star_ne _ _ _ h

/-- A map into `Q_v` from blocks `Y → X_u`. -/
def toT (v : ℤ) {Y : finSuppFreeQG G T} (F : ∀ u, Y ⟶ X.obj u) : Y ⟶ (Q X b).obj v :=
  ∑ u ∈ I b v, F u ≫ ι X b v u

/-- A map out of `Q_v` from blocks `X_u → Z`. -/
def ofT (v : ℤ) {Z : finSuppFreeQG G T} (F : ∀ u, X.obj u ⟶ Z) : (Q X b).obj v ⟶ Z :=
  ∑ u ∈ I b v, πT X b v u ≫ F u

/-- A map `Q_v → Q_{v'}` from blocks `M u' u : X_u → X_{u'}`. -/
def tmap (v v' : ℤ) (M : ∀ u' u, X.obj u ⟶ X.obj u') : (Q X b).obj v ⟶ (Q X b).obj v' :=
  ofT v fun u ↦ toT v' fun u' ↦ M u' u

lemma toT_ofT (v : ℤ) {Y Z : finSuppFreeQG G T} (F : ∀ u, Y ⟶ X.obj u) (F' : ∀ u, X.obj u ⟶ Z) :
    toT (b := b) v F ≫ ofT v F' = ∑ u ∈ I b v, F u ≫ F' u := by
  simp only [toT, ofT, Preadditive.sum_comp, Preadditive.comp_sum, assoc]
  refine sum_congr rfl fun u hu ↦ ?_
  rw [sum_eq_single u (fun u' _ h ↦ by rw [ι_πT_ne_assoc v h, zero_comp, comp_zero])
    (fun h ↦ absurd hu h), ι_πT_self_assoc hu]

lemma comp_toT (v : ℤ) {Y Y' : finSuppFreeQG G T} (h : Y' ⟶ Y) (F : ∀ u, Y ⟶ X.obj u) :
    h ≫ toT (b := b) v F = toT v fun u ↦ h ≫ F u := by
  simp only [toT, Preadditive.comp_sum, assoc]

lemma ofT_comp (v : ℤ) {Z Z' : finSuppFreeQG G T} (F : ∀ u, X.obj u ⟶ Z) (h : Z ⟶ Z') :
    ofT (b := b) v F ≫ h = ofT v fun u ↦ F u ≫ h := by
  simp only [ofT, Preadditive.sum_comp, assoc]

lemma toT_sum (v : ℤ) {ι' : Type*} (s : Finset ι') {Y : finSuppFreeQG G T}
    (F : ι' → ∀ u, Y ⟶ X.obj u) :
    ∑ j ∈ s, toT (b := b) v (F j) = toT v fun u ↦ ∑ j ∈ s, F j u := by
  simp only [toT, Preadditive.sum_comp]
  exact sum_comm

lemma ofT_sum (v : ℤ) {ι' : Type*} (s : Finset ι') {Z : finSuppFreeQG G T}
    (F : ι' → ∀ u, X.obj u ⟶ Z) :
    ∑ j ∈ s, ofT (b := b) v (F j) = ofT v fun u ↦ ∑ j ∈ s, F j u := by
  simp only [ofT, Preadditive.comp_sum]
  exact sum_comm

lemma ofT_toT (v v' : ℤ) {Y : finSuppFreeQG G T} (F : ∀ u, X.obj u ⟶ Y)
    (F' : ∀ u', Y ⟶ X.obj u') :
    ofT (b := b) v F ≫ toT v' F' = tmap v v' fun u' u ↦ F u ≫ F' u' := by
  rw [ofT_comp, tmap]
  simp only [comp_toT]

lemma tmap_comp (v v' v'' : ℤ) (M : ∀ u' u, X.obj u ⟶ X.obj u')
    (N : ∀ u'' u', X.obj u' ⟶ X.obj u'') :
    tmap (b := b) v v' M ≫ tmap v' v'' N =
      tmap v v'' fun u'' u ↦ ∑ u' ∈ I b v', M u' u ≫ N u'' u' := by
  rw [tmap, ofT_comp, tmap]
  simp only [toT_ofT, comp_toT, toT_sum]
  rfl

lemma tmap_sum (v v' : ℤ) {ι' : Type*} (s : Finset ι') (M : ι' → ∀ u' u, X.obj u ⟶ X.obj u') :
    ∑ j ∈ s, tmap (b := b) v v' (M j) = tmap v v' fun u' u ↦ ∑ j ∈ s, M j u' u := by
  simp only [tmap, ofT_sum, toT_sum]

lemma tmap_congr {v v' : ℤ} {M M' : ∀ u' u, X.obj u ⟶ X.obj u'} (h : ∀ u' u, M u' u = M' u' u) :
    tmap (b := b) v v' M = tmap v v' M' := by
  rw [show M = M' from funext fun u' ↦ funext fun u ↦ h u' u]

lemma tmap_zero (v v' : ℤ) : tmap (X := X) (b := b) v v' (fun _ _ ↦ 0) = 0 := by
  simp [tmap, toT, ofT]

end Tower

/-! ### The morphisms `α₀`, `β₀`, `d` -/

section Morphisms

variable {X : (finSuppFreeQG G T).cz} {p : X ⟶ X} {b : ℕ} (D : Blocks X p b)

/-- The block morphisms of `α`. -/
def Am (v u w : ℤ) : X.obj w ⟶ X.obj u := ofLin fun i ↦ D.A i v u w

/-- The block morphisms of `β` and `d`. -/
def Bm (w v u : ℤ) : X.obj u ⟶ X.obj w := ofLin fun i ↦ D.B i w v u

lemma Am_eq_zero {v u w : ℤ} (h : (b : ℤ) < |v - w|) : Am D v u w = 0 :=
  lin_eq_zero fun i ↦ by rw [Am, lin_ofLin, D.A_zero i v u w h]

lemma Bm_eq_zero {w v u : ℤ} (h : w < v - 2 * b ∨ v < w) : Bm D w v u = 0 :=
  lin_eq_zero fun i ↦ by rw [Bm, lin_ofLin, D.B_zero i w v u h]

lemma propLE_α : CZ.PropLE (X := X) (Y := Q X b) (fun v w ↦ toT v fun u ↦ Am D v u w) b :=
  fun v w h ↦ by simp [toT, Am_eq_zero D h]

lemma propLE_β : CZ.PropLE (X := Q X b) (Y := X) (fun w v ↦ ofT v fun u ↦ Bm D w v u) (2 * b) :=
  fun w v h ↦ by
    have : w < v - 2 * b ∨ v < w := by rw [lt_abs] at h; push_cast at h; omega
    simp [ofT, Bm_eq_zero D this]

/-- `α₀ : X ⟶ Q`, `α₀ v w = ∑_u Am v u w ≫ ι_u`. -/
def α₀ : X ⟶ Q X b := CZ.homMk _ b (propLE_α D)

/-- `β₀ : Q ⟶ X`, `β₀ w v = ∑_u πT_u ≫ Bm w v u`. -/
def β₀ : Q X b ⟶ X := CZ.homMk _ (2 * b) (propLE_β D)

/-- The diagonal idempotent `d v = ∑_{u, u'} πT_u ≫ Bm u' v u ≫ ι_{u'}`. -/
def d (v : ℤ) : (Q X b).obj v ⟶ (Q X b).obj v := tmap v v fun u' u ↦ Bm D u' v u

lemma lin_sum_comp {Y Z W : finSuppFreeQG G T} {ι' : Type*} (s : Finset ι') (f : ι' → (Y ⟶ Z))
    (g : ι' → (Z ⟶ W)) (i : ℕ) :
    lin (∑ j ∈ s, f j ≫ g j) i = ∑ j ∈ s, (lin (g j) i).comp (lin (f j) i) := by
  simp only [lin_sum, lin_comp]

/-- `α₀ ≫ β₀ = p` (identity (I1)). -/
lemma α₀_β₀ : α₀ D ≫ β₀ D = p := by
  ext w' w
  rw [CZ.comp_apply_left _ (propLE_α D)]
  simp only [α₀, β₀, CZ.homMk_apply, toT_ofT]
  refine lin_ext fun i ↦ ?_
  simp only [lin_sum, lin_comp, Am, Bm, lin_ofLin]
  exact D.I1 i w' w _ subset_rfl

/-- `d v ≫ d v = d v` (identity (I3)). -/
lemma d_idem (v : ℤ) : d D v ≫ d D v = d D v := by
  rw [d, tmap_comp]
  refine tmap_congr fun u'' u ↦ lin_ext fun i ↦ ?_
  simp only [lin_sum, lin_comp, Bm, lin_ofLin]
  exact D.I3 i v u'' u

/-- `β₀ ≫ α₀ = diag d` (identity (I2)). -/
lemma β₀_α₀ : β₀ D ≫ α₀ D = CZ.diag (d D) := by
  ext v' v
  rw [CZ.comp_apply_left _ (propLE_β D)]
  simp only [α₀, β₀, CZ.homMk_apply, ofT_toT, tmap_sum]
  have key : ∀ u' u, ∑ w ∈ CZ.window v (2 * b), Bm D w v u ≫ Am D v' u' w =
      if v' = v then Bm D u' v u else 0 := fun u' u ↦ by
    refine lin_ext fun i ↦ ?_
    simp only [lin_sum, lin_comp, Am, Bm, lin_ofLin]
    rw [D.I2 i v' v u' u _ fun x hx ↦ by
      rw [mem_Icc] at hx; rw [CZ.window, mem_Icc]; push_cast; omega]
    split_ifs
    · rw [lin_ofLin]
    · rw [lin_zero]
  rw [tmap_congr key]
  by_cases h : v' = v
  · subst h
    simp only [if_true, CZ.diag_apply_self]
    rfl
  · simp only [h, if_false, tmap_zero]
    exact (CZ.diag_apply_ne _ (Ne.symm h)).symm

end Morphisms

/-- **Theorem A** (`blueprint/negK-proof.md` §2.4). -/
theorem karDiag : KarDiagStatement := by
  intro G _ _ T X p hp b hb
  obtain ⟨D⟩ := exists_blocks hp hb
  have hq : CZ.diag (d D) ≫ CZ.diag (d D) = CZ.diag (d D) := by
    rw [CZ.diag_comp_diag]; exact CZ.diag_ext (d_idem D)
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := kar_of_split hp hq (α₀_β₀ D) (β₀_α₀ D)
  refine ⟨Q X b, d D, α₀ D ≫ CZ.diag (d D), CZ.diag (d D) ≫ β₀ D, d_idem D, h₁, h₂, h₃, h₄, h₅,
    h₆, fun v w h ↦ ?_, fun w v h ↦ ?_⟩
  · rw [CZ.comp_diag_apply]
    change (toT v fun u ↦ Am D v u w) ≫ d D v = 0
    rw [show (toT v fun u ↦ Am D v u w) = 0 from propLE_α D v w h, zero_comp]
  · rw [CZ.diag_comp_apply]
    change d D v ≫ (ofT v fun u ↦ Bm D w v u) = 0
    rw [show (ofT v fun u ↦ Bm D w v u) = 0 from propLE_β D w v h, comp_zero]

end

end HSFormal.LTheory.KarDiag
