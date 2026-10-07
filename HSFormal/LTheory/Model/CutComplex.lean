import HSFormal.LTheory.Model.CutWindow
import HSFormal.LTheory.Model.BoundaryConstruction
import HSFormal.LTheory.Model.Transport
import HSFormal.LTheory.Model.Cascade

/-!
# Threshold cuts of free Poincaré complexes over `C_ℤ(A)` and their Thom complexes

Lower L-theory model, module 22 (`DecBij`), part 2: algebraic transversality, the half that does
not need the line complex.

* `SplitCx.quot`: for degreewise splittings `C_r = E_r ⊕ U_r` whose `U`-parts form a subcomplex
  (`SplitCx.IsSubU`: the `U → E` components of `d` vanish), the quotient complex
  `(E_r, π_E d ι_E)` with the chain map `toQuot = π_E : C ⟶ E`.
* **Threshold cuts.**  For a complex `C` over `C_ℤ(A)` whose differentials have propagation
  `≤ b` and thresholds `t` with `t (r - 1) + b ≤ t r` (the blueprint's `t_{r-1} ≤ t_r - b`), the
  upper parts `C_r|_{[t_r, ∞)}` (the `U`-parts of the self-dual cuts `CZ.cut (C.X r) (· < t r)`)
  form a subcomplex (`CZ.isSubU_lowCut`); the quotient is the **lower part**
  `C|_{(-∞, t_r)}`, all of whose chain objects lie in `negHalf` (`CutData.thomC_negHalf`).
* **The lower Thom complex** `CutData.thom` of a free Poincaré complex `P` (idempotent `0` or `1`
  in each degree) with cut data `D` (bound `b` for `d` and `φ`, thresholds `t`): the quotient
  complex `T = C|_{(-∞, t_*)}` with the pushforward structure `θ = q_% φ = q^* φ q`
  (`q = π_E : C ⟶ T`), a strictly symmetric (not Poincaré) complex over `C_ℤ(A)` supported in
  `[0, n]`.  Geometrically `T = C(M⁻, ∂M⁻)` for the lower half `M⁻` of the cut.
* **Poincaré modulo bounded objects** (`CutData.thom_isPoincare_mod`): the image of `(T, θ)` in
  `C_ℤ(A)/C_ℤ^{bdd}(A)` (`CZ.bddFiltration`) is Poincaré.  Proof: modulo bounded objects the
  cut idempotent `e_r = diag(χ_{v < t_r})` commutes with `d` and is `φ`-self-adjoint (the
  defects have bounded row support: `d` and `φ` have propagation `≤ b` and only finitely many
  thresholds are involved), so it is a reducing idempotent of `P` in the quotient
  (`SymPoincare.cut`, Poincaré), and `π_E`, `ι_E p` form a strict Kar isomorphism between that
  cut and the image of `(T, θ)` which carries the cut structure to `θ`
  (`SymPoincare.transport`).

By `KaroubiFiltration.contractibleMod_bd`, the boundary `∂T = Σ⁻¹Cone(θ)` of the Thom complex is
therefore contractible modulo bounded objects, which is the input for its window (Kar) model
(`Model/CutBoundary.lean`).
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression

noncomputable section

attribute [local implicit_reducible] CZ.cut CZ.diagSplitting

/-! ### Quotient complexes along degreewise splittings -/

namespace SplitCx

variable {V : Type*} [Category V] [Preadditive V] (C : ChainComplex V ℤ)
  (σ : ∀ r, Splitting (C.X r))

/-- The `U`-parts form a subcomplex: all `U → E` components of `d` vanish. -/
def IsSubU : Prop := ∀ r r', (σ r).ιU ≫ C.d r r' ≫ (σ r').πE = 0

variable {C σ}

lemma πE_ιE (r : ℤ) : (σ r).πE ≫ (σ r).ιE = 𝟙 _ - (σ r).πU ≫ (σ r).ιU := by
  rw [← (σ r).total]; abel

/-- **The quotient complex** `(E_r, π_E d ι_E)` by the subcomplex of `U`-parts. -/
@[simps, implicit_reducible]
def quot (h : IsSubU C σ) : ChainComplex V ℤ where
  X r := (σ r).E
  d r r' := (σ r).ιE ≫ C.d r r' ≫ (σ r').πE
  shape r r' hr := by rw [C.shape r r' hr]; simp
  d_comp_d' r r' r'' _ _ := by
    simp only [assoc]
    rw [← assoc (σ r').πE, πE_ιE, sub_comp, id_comp, comp_sub, comp_sub, C.d_comp_d_assoc,
      assoc, h r' r'']
    simp

/-- The quotient map `π_E : C ⟶ E`. -/
@[simps]
def toQuot (h : IsSubU C σ) : C ⟶ quot h where
  f r := (σ r).πE
  comm' r r' _ := by
    change (σ r).πE ≫ (σ r).ιE ≫ C.d r r' ≫ (σ r').πE = C.d r r' ≫ (σ r').πE
    rw [← assoc, πE_ιE, sub_comp, id_comp, assoc, h r r', comp_zero, sub_zero]

/-- **The subcomplex of `U`-parts** `(U_r, π_U d ι_U)`. -/
@[simps, implicit_reducible]
def sub (h : IsSubU C σ) : ChainComplex V ℤ where
  X r := (σ r).U
  d r r' := (σ r).ιU ≫ C.d r r' ≫ (σ r').πU
  shape r r' hr := by rw [C.shape r r' hr]; simp
  d_comp_d' r r' r'' _ _ := by
    have e : (σ r').πU ≫ (σ r').ιU = 𝟙 _ - (σ r').πE ≫ (σ r').ιE := by
      rw [← (σ r').total]; abel
    simp only [assoc]
    rw [← assoc (σ r').πU, e, sub_comp, id_comp, comp_sub, comp_sub, C.d_comp_d_assoc]
    simp only [assoc, reassoc_of% (h r r'), zero_comp, comp_zero, sub_zero]

/-- The inclusion `ι_U : U ⟶ C`. -/
@[simps]
def fromSub (h : IsSubU C σ) : sub h ⟶ C where
  f r := (σ r).ιU
  comm' r r' _ := by
    change (σ r).ιU ≫ C.d r r' = ((σ r).ιU ≫ C.d r r' ≫ (σ r').πU) ≫ (σ r').ιU
    have e : (σ r').πU ≫ (σ r').ιU = 𝟙 _ - (σ r').πE ≫ (σ r').ιE := by
      rw [← (σ r').total]; abel
    rw [assoc, assoc, e, comp_sub, comp_sub, comp_id]
    simp only [reassoc_of% (h r r'), zero_comp, sub_zero]

/-- The crossing components `ι_E d π_U : E_r ⟶ U_{r'}` (the extension class of
`0 ⟶ U ⟶ C ⟶ E ⟶ 0`). -/
def cross (r r' : ℤ) : (σ r).E ⟶ (σ r').U := (σ r).ιE ≫ C.d r r' ≫ (σ r').πU

end SplitCx

/-! ### Threshold cuts in `C_ℤ(A)` -/

namespace CZ

variable {A : InvCat}

lemma isZero_cut_U (X : A.cz) (p : ℤ → Prop) [DecidablePred p] {v : ℤ} (h : p v) :
    IsZero ((cut X p).U.obj v) := by
  change IsZero (if p v then splitE (X.obj v) else splitU (X.obj v)).U
  rw [if_pos h]
  exact isZero_zero A

/-- The cut of degree `r` at the threshold `t r`: `E = C_r|_{(-∞, t_r)}`, `U = C_r|_{[t_r, ∞)}`. -/
abbrev lowCut (C : ChainComplex A.cz ℤ) (t : ℤ → ℤ) (r : ℤ) : Splitting (C.X r) :=
  cut (C.X r) (fun v ↦ v < t r)

/-- **Upper parts form a subcomplex** when `d` has propagation `≤ b` and `t (r - 1) + b ≤ t r`:
a position `v ≥ t_r` is moved by `d` to positions `≥ v - b ≥ t_{r-1}`. -/
lemma isSubU_lowCut (C : ChainComplex A.cz ℤ) (b : ℕ) (hd : ∀ r, PropLE (C.d r (r - 1)).1 b)
    (t : ℤ → ℤ) (ht : ∀ r, t (r - 1) + b ≤ t r) : SplitCx.IsSubU C (lowCut C t) := by
  intro r r'
  by_cases hr : r' = r - 1
  · subst hr
    ext w v
    rw [zero_apply]
    by_cases hv : v < t r
    · exact (isZero_cut_U (C.X r) (fun x ↦ x < t r) hv).eq_of_src _ _
    · by_cases hw : w < t (r - 1)
      · rw [cut_ιU_eq_diag, diag_comp_apply, cut_πE_eq_diag, comp_diag_apply,
          hd r w v (by rw [lt_abs]; have := ht r; omega), zero_comp, comp_zero]
      · exact (isZero_cut_E (C.X (r - 1)) (fun x ↦ x < t (r - 1)) hw).eq_of_tgt _ _
  · rw [C.shape r r' (by simp only [ComplexShape.down_Rel]; omega), zero_comp, comp_zero]

/-- A morphism of `C_ℤ(A)` agrees modulo bounded objects with another one if their entries agree
outside finitely many rows. -/
lemma proj_map_eq_of_rows {X Y : A.cz} (f g : X ⟶ Y) (lo hi : ℤ)
    (h : ∀ w v, w < lo ∨ hi < w → f.1 w v = g.1 w v) :
    (bddFiltration A).proj.F.map f = (bddFiltration A).proj.F.map g :=
  ((bddFiltration A).proj_map_eq_iff f g).2 (factorsThrough_bdd_of_rows (f - g) lo hi
    fun w v hw ↦ by rw [sub_apply, h w v hw, sub_self])

variable (A) in
/-- The projection `C_ℤ(A) ⟶ C_ℤ(A)/C_ℤ^{bdd}(A)` (germs at `±∞`). -/
abbrev projB : A.cz ⟶ (bddFiltration A).quot := (bddFiltration A).proj

/-! ### Cut data and the lower Thom complex -/

variable {n : ℤ}

/-- **Cut data** for a free Poincaré complex `P` over `C_ℤ(A)`: a bound `b` for the propagation
of `d` and `φ` (in all degrees), thresholds `t` with `t (r - 1) + b ≤ t r`, and freeness: the
Kar idempotent is `1` or `0` in each degree. -/
structure CutData (P : SymPoincare A.cz.inv n) where
  /-- A common propagation bound for `d` and `φ`. -/
  b : ℕ
  /-- The degree-dependent thresholds. -/
  t : ℤ → ℤ
  hd : ∀ r, PropLE (P.C.d r (r - 1)).1 b
  hφ : ∀ r, PropLE (P.φ.f r).1 b
  ht : ∀ r, t (r - 1) + b ≤ t r
  hp : ∀ r, P.p.f r = 𝟙 _ ∨ P.p.f r = 0

namespace CutData

variable {P : SymPoincare A.cz.inv n} (D : CutData P)

/-- The cut of degree `r`. -/
abbrev σ (r : ℤ) : Splitting (P.C.X r) := lowCut P.C D.t r

lemma isSubU : SplitCx.IsSubU P.C D.σ := isSubU_lowCut P.C D.b D.hd D.t D.ht

/-- The lower part `T = C|_{(-∞, t_*)}` (a quotient complex of `C`). -/
abbrev thomC : ChainComplex A.cz ℤ := SplitCx.quot D.isSubU

/-- The quotient map `q = π_E : C ⟶ T`. -/
abbrev q : P.C ⟶ D.thomC := SplitCx.toQuot D.isSubU

/-- The cut idempotent `e_r = diag(χ_{v < t_r})` of `C_r`. -/
abbrev e (r : ℤ) : P.C.X r ⟶ P.C.X r := (D.σ r).idem

lemma e_eq (r : ℤ) : D.e r = diag fun v ↦ if v < D.t r then 𝟙 ((P.C.X r).obj v) else 0 :=
  cut_idem _ _

include D in
lemma p_comm (r : ℤ) (x : P.C.X r ⟶ P.C.X r) : P.p.f r ≫ x = x ≫ P.p.f r := by
  rcases D.hp r with h | h <;> rw [h] <;> simp

include D in
lemma star_p (r : ℤ) : A.cz.inv.star (P.p.f r) = P.p.f r := by
  rcases D.hp r with h | h <;> rw [h]
  · exact A.cz.inv.star_id _
  · exact A.cz.inv.star_zero

@[reassoc]
lemma ιE_p_πE_ιE (r : ℤ) :
    (D.σ r).ιE ≫ P.p.f r ≫ (D.σ r).πE ≫ (D.σ r).ιE = (D.σ r).ιE ≫ P.p.f r := by
  rw [← Splitting.idem, D.p_comm, Casc.ιE_idem_assoc]

@[reassoc]
lemma πE_ιE_p_πE (r : ℤ) :
    (D.σ r).πE ≫ (D.σ r).ιE ≫ P.p.f r ≫ (D.σ r).πE = P.p.f r ≫ (D.σ r).πE := by
  rw [← assoc, ← Splitting.idem, ← reassoc_of% D.p_comm, Casc.idem_πE]

/-- The Kar idempotent of `T` induced by `p`. -/
def pT : D.thomC ⟶ D.thomC where
  f r := (D.σ r).ιE ≫ P.p.f r ≫ (D.σ r).πE
  comm' r r' _ := by
    change ((D.σ r).ιE ≫ P.p.f r ≫ (D.σ r).πE) ≫ ((D.σ r).ιE ≫ P.C.d r r' ≫ (D.σ r').πE) =
      ((D.σ r).ιE ≫ P.C.d r r' ≫ (D.σ r').πE) ≫ ((D.σ r').ιE ≫ P.p.f r' ≫ (D.σ r').πE)
    simp only [assoc]
    rw [D.ιE_p_πE_ιE_assoc, D.πE_ιE_p_πE, P.p.comm_assoc]

@[simp]
lemma pT_f (r : ℤ) : D.pT.f r = (D.σ r).ιE ≫ P.p.f r ≫ (D.σ r).πE := rfl

lemma pT_idem : D.pT ≫ D.pT = D.pT := by
  ext r : 1
  simp only [comp_f, pT_f, assoc]
  rw [D.ιE_p_πE_ιE_assoc, ← assoc (P.p.f r), idem_f P.p_idem]

lemma pT_support : SupportedIn D.pT 0 n := fun r hr ↦ by
  rw [pT_f, P.support r hr, zero_comp, comp_zero]

@[reassoc]
lemma q_pT : D.q ≫ D.pT = P.p ≫ D.q := by
  ext r : 1
  simp only [comp_f, pT_f, SplitCx.toQuot_f]
  exact D.πE_ιE_p_πE r

/-- The pushforward structure `θ = q^* φ q` on `T`. -/
abbrev θ : dualComplex A.cz.inv n D.thomC ⟶ D.thomC := dualHom A.cz.inv n D.q ≫ P.φ ≫ D.q

lemma θ_kar : dualHom A.cz.inv n D.pT ≫ D.θ ≫ D.pT = D.θ := by
  rw [θ, assoc, assoc, D.q_pT, ← assoc (dualHom _ _ D.pT), ← dualHom_comp, D.q_pT, dualHom_comp,
    assoc, ← assoc P.φ, ← assoc (dualHom _ _ P.p), P.φ_kar]

/-- **The lower Thom complex** `(T, p_T, q^* φ q)`: the lower part of the cut with the
pushforward structure, a strictly symmetric `n`-dimensional complex over `C_ℤ(A)` (not Poincaré;
Poincaré modulo bounded objects by `thom_isPoincare_mod`). -/
@[implicit_reducible]
def thom : SymComplex A.cz.inv n where
  C := D.thomC
  p := D.pT
  p_idem := D.pT_idem
  φ := D.θ
  φ_kar := D.θ_kar
  symm := P.symm.conj D.q

@[simp] lemma thom_C : D.thom.C = D.thomC := rfl

@[simp] lemma thom_p : D.thom.p = D.pT := rfl

@[simp] lemma thom_φ : D.thom.φ = D.θ := rfl

/-- All chain objects of the lower Thom complex lie in the negative half-line. -/
lemma thomC_negHalf (r : ℤ) : negHalf A (D.thomC.X r) :=
  ⟨D.t r - 1, fun v hv ↦ isZero_cut_E (P.C.X r) (fun x ↦ x < D.t r) (by omega)⟩

/-! ### The Thom complex is Poincaré modulo bounded objects -/

/-- Modulo bounded objects, the cut idempotent commutes with `d`. -/
lemma proj_e_d (r r' : ℤ) :
    (projB A).F.map (D.e r ≫ P.C.d r r') = (projB A).F.map (P.C.d r r' ≫ D.e r') := by
  by_cases hr : r' = r - 1
  · subst hr
    refine proj_map_eq_of_rows _ _ (D.t (r - 1)) (D.t r + D.b) fun w v hw ↦ ?_
    rw [D.e_eq, D.e_eq, diag_comp_apply, comp_diag_apply]
    have ht := D.ht r
    rcases hw with hw | hw
    · rw [if_pos hw, comp_id]
      split_ifs with hv
      · rw [id_comp]
      · rw [zero_comp, D.hd r w v (by rw [lt_abs]; omega)]
    · rw [if_neg (show ¬ w < D.t (r - 1) by omega), comp_zero]
      split_ifs with hv
      · rw [id_comp, D.hd r w v (by rw [lt_abs]; omega)]
      · rw [zero_comp]
  · rw [P.C.shape r r' (by simp only [ComplexShape.down_Rel]; omega), comp_zero, zero_comp]

/-- The cut idempotent, as a chain endomorphism of `C` modulo bounded objects. -/
def eBar : (projB A).mapC P.C ⟶ (projB A).mapC P.C where
  f r := (projB A).F.map (D.e r)
  comm' r r' _ := by
    simp only [Functor.mapHomologicalComplex_obj_d, ← Functor.map_comp]
    exact D.proj_e_d r r'

@[simp] lemma eBar_f (r : ℤ) : D.eBar.f r = (projB A).F.map (D.e r) := rfl

/-- Modulo bounded objects, the cut idempotent is `φ`-self-adjoint. -/
lemma proj_e_φ (r : ℤ) :
    (projB A).F.map (D.e (n - r) ≫ P.φ.f r) = (projB A).F.map (P.φ.f r ≫ D.e r) := by
  refine proj_map_eq_of_rows _ _ (min (D.t r) (D.t (n - r) - D.b))
    (max (D.t r) (D.t (n - r) + D.b)) fun w v hw ↦ ?_
  rw [D.e_eq, D.e_eq, diag_comp_apply, comp_diag_apply]
  rcases hw with hw | hw
  · rw [if_pos (show w < D.t r by omega), comp_id]
    split_ifs with hv
    · rw [id_comp]
    · rw [zero_comp, D.hφ r w v (by rw [lt_abs]; omega)]
  · rw [if_neg (show ¬ w < D.t r by omega), comp_zero]
    split_ifs with hv
    · rw [id_comp, D.hφ r w v (by rw [lt_abs]; omega)]
    · rw [zero_comp]

/-- **The cut idempotent is reducing for `P` modulo bounded objects.** -/
lemma isReducing : (P.map (projB A)).IsReducing D.eBar where
  idem := by
    ext r : 1
    simp only [comp_f, eBar_f, ← Functor.map_comp, Casc.idem_idem]
  comm := by
    ext r : 1
    simp only [comp_f, eBar_f, SymPoincare.map_p, Functor.mapHomologicalComplex_map_f,
      ← Functor.map_comp, D.p_comm]
  adj := by
    ext r : 1
    simp only [comp_f, dualHom_f, eBar_f, SymPoincare.map_φ, InvFunctor.mapDual_f]
    rw [← (projB A).map_star, star_cut_idem, ← Functor.map_comp, ← Functor.map_comp]
    exact D.proj_e_φ r

/-- `ι_E ≫ p : T ⟶ C`, a chain map modulo bounded objects. -/
lemma proj_ιE_p_d (r r' : ℤ) :
    (projB A).F.map (((D.σ r).ιE ≫ P.p.f r) ≫ P.C.d r r') =
      (projB A).F.map (D.thomC.d r r' ≫ (D.σ r').ιE ≫ P.p.f r') := by
  by_cases hr : r' = r - 1
  · subst hr
    have e₁ : ((D.σ r).ιE ≫ P.p.f r) ≫ P.C.d r (r - 1) =
        (D.σ r).ιE ≫ P.C.d r (r - 1) ≫ P.p.f (r - 1) := by
      rw [assoc, P.p.comm]
    have e₂ : D.thomC.d r (r - 1) ≫ (D.σ (r - 1)).ιE ≫ P.p.f (r - 1) =
        ((D.σ r).ιE ≫ P.C.d r (r - 1) ≫ P.p.f (r - 1)) ≫ D.e (r - 1) := by
      rw [SplitCx.quot_d]
      simp only [assoc]
      rw [← assoc (D.σ (r - 1)).πE, ← Splitting.idem, ← D.p_comm (r - 1) (D.σ (r - 1)).idem]
    rw [e₁, e₂]
    refine proj_map_eq_of_rows _ _ (D.t (r - 1)) (D.t r + D.b) fun w v hw ↦ ?_
    rw [D.e_eq, comp_diag_apply]
    have ht := D.ht r
    rcases hw with hw | hw
    · rw [if_pos hw, comp_id]
    · rw [if_neg (show ¬ w < D.t (r - 1) by omega), comp_zero]
      by_cases hv : v < D.t r
      · rw [cut_ιE_eq_diag, diag_comp_apply]
        rcases D.hp (r - 1) with h | h <;> rw [h]
        · rw [comp_id, D.hd r w v (by rw [lt_abs]; omega), comp_zero]
        · rw [comp_zero, zero_apply, comp_zero]
      · exact (isZero_cut_E (P.C.X r) (fun x ↦ x < D.t r) hv).eq_of_src _ _
  · rw [P.C.shape r r' (by simp only [ComplexShape.down_Rel]; omega), comp_zero,
      D.thomC.shape r r' (by simp only [ComplexShape.down_Rel]; omega), zero_comp]

/-- The inclusion `T ⟶ C` modulo bounded objects. -/
def incl : (projB A).mapC D.thomC ⟶ (projB A).mapC P.C where
  f r := (projB A).F.map ((D.σ r).ιE ≫ P.p.f r)
  comm' r r' _ := by
    simp only [Functor.mapHomologicalComplex_obj_d, ← Functor.map_comp]
    exact D.proj_ιE_p_d r r'

@[simp] lemma incl_f (r : ℤ) : D.incl.f r = (projB A).F.map ((D.σ r).ιE ≫ P.p.f r) := rfl

/-- **The strict Kar isomorphism** between the cut of `P` along `ē` and the image of the Thom
complex, modulo bounded objects: `q p : (C, p ē) ⟶ (T, p_T)` and `ι_E p` back. -/
def thomEquiv : KarHtpyEquiv ((P.map (projB A)).cut D.isReducing).p ((projB A).mapH D.pT) where
  f := (projB A).mapH (P.p ≫ D.q)
  g := D.incl
  pf := by
    ext r : 1
    simp only [SymPoincare.cut_p, SymPoincare.map_p, comp_f, eBar_f,
      Functor.mapHomologicalComplex_map_f, SplitCx.toQuot_f, ← Functor.map_comp, assoc]
    rw [← assoc (D.e r) (P.p.f r), ← D.p_comm r (D.e r), assoc (P.p.f r) (D.e r),
      Casc.idem_πE, ← assoc (P.p.f r) (P.p.f r), idem_f P.p_idem]
  fp := by
    ext r : 1
    simp only [comp_f, Functor.mapHomologicalComplex_map_f, SplitCx.toQuot_f, pT_f,
      ← Functor.map_comp, assoc, D.πE_ιE_p_πE]
    rw [← assoc (P.p.f r), idem_f P.p_idem]
  pg := by
    ext r : 1
    simp only [comp_f, Functor.mapHomologicalComplex_map_f, incl_f, pT_f, ← Functor.map_comp,
      assoc, D.ιE_p_πE_ιE_assoc]
    rw [idem_f P.p_idem]
  gp := by
    ext r : 1
    simp only [SymPoincare.cut_p, SymPoincare.map_p, comp_f, eBar_f,
      Functor.mapHomologicalComplex_map_f, incl_f, ← Functor.map_comp, assoc]
    rw [← assoc (P.p.f r) (P.p.f r), idem_f P.p_idem, D.p_comm r (D.e r), ← assoc,
      Casc.ιE_idem]
  fg := Homotopy.ofEq (by
    ext r : 1
    simp only [SymPoincare.cut_p, SymPoincare.map_p, comp_f, eBar_f,
      Functor.mapHomologicalComplex_map_f, incl_f, SplitCx.toQuot_f, ← Functor.map_comp, assoc]
    rw [← assoc (D.σ r).πE, ← Splitting.idem, ← D.p_comm, idem_f_assoc P.p_idem])
  gf := Homotopy.ofEq (by
    ext r : 1
    simp only [comp_f, Functor.mapHomologicalComplex_map_f, incl_f, SplitCx.toQuot_f, pT_f,
      ← Functor.map_comp, assoc]
    rw [idem_f_assoc P.p_idem])

lemma thomEquiv_conj :
    dualHom (bddFiltration A).quot.inv n D.thomEquiv.f ≫ ((P.map (projB A)).cut D.isReducing).φ ≫
      D.thomEquiv.f = (projB A).mapDual D.θ := by
  ext r : 1
  have hk : P.p.f (n - r) ≫ P.φ.f r ≫ P.p.f r = P.φ.f r := by
    have := congrArg (fun g ↦ g.f r) P.φ_kar
    simp only [comp_f, dualHom_f] at this
    rwa [D.star_p] at this
  simp only [thomEquiv, θ, SymPoincare.cut_φ, SymPoincare.map_φ, comp_f, dualHom_f, eBar_f,
    InvFunctor.mapDual_f, Functor.mapHomologicalComplex_map_f, SplitCx.toQuot_f]
  rw [← (projB A).map_star, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  change A.cz.inv.star (P.p.f (n - r) ≫ (D.σ (n - r)).πE) ≫ (P.φ.f r ≫ D.e r) ≫ P.p.f r ≫
    (D.σ r).πE = A.cz.inv.star (D.σ (n - r)).πE ≫ P.φ.f r ≫ (D.σ r).πE
  rw [A.cz.inv.star_comp, star_cut_πE, D.star_p]
  simp only [assoc]
  rw [← assoc (D.e r) (P.p.f r), ← D.p_comm r (D.e r), assoc (P.p.f r) (D.e r), Casc.idem_πE,
    reassoc_of% hk]

/-- **The lower Thom complex is Poincaré modulo bounded objects**: its image in
`C_ℤ(A)/C_ℤ^{bdd}(A)` is (by `thomEquiv`, `thomEquiv_conj`) the transport of the cut
`P.cut ē` of `P` along the reducing idempotent `ē`, which is Poincaré. -/
theorem thom_isPoincare_mod :
    IsPoincare (bddFiltration A).quot.inv n ((projB A).mapH D.pT) ((projB A).mapDual D.θ) := by
  have hp' : (projB A).mapH D.pT ≫ (projB A).mapH D.pT = (projB A).mapH D.pT := by
    rw [← Functor.map_comp, D.pT_idem]
  have hs : SupportedIn ((projB A).mapH D.pT) 0 n := fun r hr ↦ by
    rw [Functor.mapHomologicalComplex_map_f, D.pT_support r hr, Functor.map_zero]
  have h := (((P.map (projB A)).cut D.isReducing).transport hp' hs D.thomEquiv).poincare
  simp only [SymPoincare.transport_p, SymPoincare.transport_φ, D.thomEquiv_conj] at h
  exact h

end CutData

end CZ

end

end HSFormal.LTheory
