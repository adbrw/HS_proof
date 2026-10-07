import HSFormal.LTheory.Model.LiftingPair
import HSFormal.LTheory.Model.LineNatural
import HSFormal.LTheory.Model.FreeLine

/-!
# Lifting pairs and the line transitions (lower L-theory model, module 16, end)

`blueprint/lower-L-construction.md` §3.2 ("Lifting pairs", "(L1)") and §6: the lifting pairs of
`LiftingPair.lean` connected to the transitions `⊗ ℝ` of the colimit model, for a Karoubi
filtration `F : U ⊂ A` and its iterates `F.czIter j : C_ℤ^{∘j} U ⊂ C_ℤ^{∘j} A`.

## Main results

* (1) **Existence after one transition** (`nonempty_liftingPair_sym`): for every closed
  `D : SymPoincare F.quot.inv (N + 1)` (any Kar complex) with `0 ≤ N + 1`, the transition image
  `D ⊗ ℝ = (CZ.lineData F.quot).sym D`, transported along
  `F.czQuotIso : (C_ℤ F).quot ≅ C_ℤ(A/U)`, has a lifting pair over `F.cz`.  Proof: the free
  model `freeSym D` (identity idempotent, support `[0, N + 2]`) is transported along
  `czQuotIso.inv` and `nonempty_liftingPair_of_isometric_free` is applied at `N + 1`.  The
  negative `-(D ⊗ ℝ)` then has the lifting pair `P.neg`.  At every level:
  `nonempty_liftingPairAt_succ j D` (lifting pairs at level `j` are `F.LiftingPairAt j D`,
  over `F.czIter j`, of `D.map (F.czIterQuotIso j).inv`).
* (2) **Compatibility with the transitions** (H2 at higher levels): for `P : F.LiftingPair D'`,
  `P.line` has `X = (CZ.lineData A).pair P.X` and is a lifting pair over `F.cz` of
  `-(D' ⊗ ℝ)` (quotient sign `t_N = -1`, `CZ.pair_toQuot`), and
  `line_bdCls : czSubIso_*(P.line.bdCls) = tensorLine P.bdCls` (boundary sign `s_N = +1`).
  `P.lineNeg = -(P.line)` is a lifting pair of `D' ⊗ ℝ` itself with
  `lineNeg_bdCls : czSubIso_*(P.lineNeg.bdCls) = -tensorLine P.bdCls`.  Level-`j` versions:
  `LiftingPairAt.line`, `line_bdClsAt`, `lineNeg`, `lineNeg_bdClsAt`, where
  `bdClsAt = (czIterSubIso j)_* bdCls ∈ Lconc (C_ℤ^{∘j} U) N`.
* (3) **Naturality**: `LiftingPairAt.map Φ` (for `Φ : FiltrationHom F F'`) with
  `map_bdClsAt : (P.map Φ).bdClsAt = (mapIter j Φ.sub)_* P.bdClsAt`, and the line construction
  commutes with it on boundary classes (`line_map_bdClsAt`, `lineNeg_map_bdClsAt`).
* Helpers: `LineData.symIsometry` (`P ≃ Q ⇒ P ⊗ ℝ ≃ Q ⊗ ℝ`),
  `SymPoincare.HomotopyIsometry.unmapSubIncl` (isometries are reflected by full subcategory
  inclusions), `SymPoincare.map_hom_inv`/`map_inv_hom` (strict isos).

## Sign bookkeeping for module 18 (`Bdry`) and the colimit transitions

The transitions of `Lmodel B m = colim_k Lconc (B.czIter k) (m + k)` are the **unsigned**
`Lconc.tensorLine`, on the `A/U` side and on the `U` side alike (both are `Lmodel` of some
`InvCat`, so a twist on the quotient side only is not available, and a uniform constant twist
`-tensorLine` cancels).  The two line signs are `s_N = +1` (`line_bdCls`) and `t_N = -1`
(`LiftingPair.line`), so a lifting pair `P` of `D` at level `j` gives the lifting pair
`P.lineNeg` of the transition image `D ⊗ ℝ` at level `j + 1` with boundary class
`-(P.bdClsAt ⊗ ℝ)` (`lineNeg_bdClsAt`).  Hence `σ_{j+1} = s t σ_j = -σ_j`, i.e. with `σ_0 = 1`
the boundary must be normalized by `σ_j = (-1)^j` (`sgnBdClsAt = (j : ℤ).negOnePow • bdClsAt`):

  `∂ (ι_k [D]) := ι_{k+1} (σ_{k+1} • [Y])`, `Y` the boundary of any lifting pair at level `k + 1`
  of `D ⊗ ℝ` (exists by `nonempty_liftingPairAt_succ` when `0 ≤ N + 1`, `N + 1 = dim D`),

and the normalized class commutes with the transitions on the nose (`lineNeg_sgnBdClsAt`:
`P.lineNeg.sgnBdClsAt = tensorLine P.sgnBdClsAt`); independence of the choices is module 17
(L2).  For a pair `X` with boundary in `U`, `X.liftingPairAt F hU` is a level-`0` lifting pair
of `X.toQuot` with `sgnBdClsAt = [X.bdLift]` and its `lineNeg` a level-`1` lifting pair of
`X.toQuot ⊗ ℝ` with `sgnBdClsAt = [X.bdLift] ⊗ ℝ` (`liftingPairAt_lineNeg_sgnBdClsAt`), so
`∂ ι_0 [X.toQuot] = ι_1 ([X.bdLift] ⊗ ℝ) = ι_0 [X.bdLift]`: **`bsign N = 1` for all `N`**.
(Equivalently the sign could be moved into degree-dependent transitions
`(-1)^M • tensorLine` on `Lconc _ M`, which would make `σ_j = 1`; not recommended.)
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex

noncomputable section

attribute [local implicit_reducible] InvCat.czIter

/-! ### Strict isomorphisms, full subcategories and the line -/

namespace SymPoincare

variable {A B : InvCat} {N : ℤ}

/-- Transport along a strict isomorphism and back is the identity. -/
@[simp]
lemma map_hom_inv (e : A ≅ B) (P : SymPoincare A.inv N) : (P.map e.hom).map e.inv = P := by
  change P.map (e.hom ≫ e.inv) = P
  rw [e.hom_inv_id]
  rfl

/-- Transport along a strict isomorphism and back is the identity. -/
@[simp]
lemma map_inv_hom (e : A ≅ B) (P : SymPoincare B.inv N) : (P.map e.inv).map e.hom = P := by
  change P.map (e.inv ≫ e.hom) = P
  rw [e.inv_hom_id]
  rfl

namespace HomotopyIsometry

/-- An isometry `e(P) ≃ Q` along a strict isomorphism `e` gives `P ≃ e⁻¹(Q)`. -/
def ofMapHom (e : A ≅ B) {P : SymPoincare A.inv N} {Q : SymPoincare B.inv N}
    (h : HomotopyIsometry (P.map e.hom) Q) : HomotopyIsometry P (Q.map e.inv) :=
  (HomotopyIsometry.ofEq' (map_hom_inv e P).symm).trans (h.map e.inv)

/-- **Isometries are reflected by the inclusion of a full subcategory.** -/
def unmapSubIncl {U : ObjectProperty A} [IsAdditiveSub U]
    {P Q : SymPoincare (A.sub U).inv N}
    (e : HomotopyIsometry (P.map (A.subIncl U)) (Q.map (A.subIncl U))) :
    HomotopyIsometry P Q where
  f := liftHom e.f
  g := liftHom e.g
  f_kar := HomologicalComplex.hom_ext _ _ fun r ↦ ObjectProperty.hom_ext _
    (congrArg (fun φ ↦ φ.f r) e.f_kar)
  g_kar := HomologicalComplex.hom_ext _ _ fun r ↦ ObjectProperty.hom_ext _
    (congrArg (fun φ ↦ φ.f r) e.g_kar)
  fg := liftHomotopy (homotopyCongr e.fg (by ext r; rfl) rfl)
  gf := liftHomotopy (homotopyCongr e.gf (by ext r; rfl) rfl)
  conj := liftHomotopy (homotopyCongr e.conj (by ext r; rfl) (by ext r; rfl))

end HomotopyIsometry

end SymPoincare

namespace LineData

variable {A B : InvCat} (L : LineData A B) {N : ℤ}

/-- **`P ⊗ ℝ` is functorial in homotopy isometries**: `P ≃ Q` gives `P ⊗ ℝ ≃ Q ⊗ ℝ`. -/
def symIsometry {P Q : SymPoincare A.inv N} (e : P.HomotopyIsometry Q) :
    (L.sym P).HomotopyIsometry (L.sym Q) where
  f := L.map e.f
  g := L.map e.g
  f_kar := by rw [sym_p, sym_p, ← map_comp, ← map_comp, e.f_kar]
  g_kar := by rw [sym_p, sym_p, ← map_comp, ← map_comp, e.g_kar]
  fg := homotopyCongr (L.htpy e.fg) (L.map_comp _ _) rfl
  gf := homotopyCongr (L.htpy e.gf) (L.map_comp _ _) rfl
  conj := homotopyCongr ((L.htpy e.conj).compLeft (L.θs N Q.C))
    (by simp only [sym_φ, assoc]; rw [θ_natural_assoc, map_comp, map_comp]) rfl

end LineData

/-! ### (1) Existence of lifting pairs after one transition -/

namespace KaroubiFiltration

variable {A : InvCat} (F : KaroubiFiltration A) {N : ℤ}

/-- The free model of `D ⊗ ℝ`, transported to `C_ℤ(A)/C_ℤ(U)`, is free on `[0, N + 2]`. -/
lemma freeSym_map_p_f (D : SymPoincare F.quot.inv (N + 1)) (r : ℤ) :
    ((((CZ.lineData F.quot).freeSym D).map F.czQuotIso.inv).p.f r) = 𝟙 _ := by
  simp

theorem nonempty_liftingPair_sym (D : SymPoincare F.quot.inv (N + 1)) (hN : 0 ≤ N + 1) :
    Nonempty (F.cz.LiftingPair (((CZ.lineData F.quot).sym D).map F.czQuotIso.inv)) :=
  nonempty_liftingPair_of_isometric_free hN (fun r _ _ ↦ F.freeSym_map_p_f D r)
    (((CZ.lineData F.quot).freeSym D).map F.czQuotIso.inv).support
    ⟨((CZ.lineData F.quot).freeSymIsometry D).symm.map F.czQuotIso.inv⟩

end KaroubiFiltration

/-! ### (2) Compatibility with the transitions -/

namespace KaroubiFiltration.LiftingPair

variable {A : InvCat} {F : KaroubiFiltration A} {N : ℤ} {D' : SymPoincare F.quot.inv (N + 1)}
  (P : F.LiftingPair D')

/-- **H2 at the next level**: `X ⊗ ℝ` is a lifting pair over `C_ℤ F` of `-(D' ⊗ ℝ)`. -/
def line : F.cz.LiftingPair ((((CZ.lineData F.quot).sym D').neg).map F.czQuotIso.inv) where
  X := (CZ.lineData A).pair P.X
  mem := CZ.pair_bd_mem F P.X P.mem
  iso := SymPoincare.HomotopyIsometry.ofMapHom F.czQuotIso
    ((CZ.pair_toQuot F P.X P.mem).some.trans ((CZ.lineData F.quot).symIsometry P.iso).neg)

@[simp] lemma line_X : P.line.X = (CZ.lineData A).pair P.X := rfl

/-- The boundary of `P.line` is `P.bd ⊗ ℝ`, up to `czSubIso`. -/
def lineBdIsometry :
    P.line.bd.HomotopyIsometry (((CZ.lineData F.sub).sym P.bd).map F.czSubIso.inv) :=
  SymPoincare.HomotopyIsometry.unmapSubIncl ((CZ.lineHom F.incl).symMapIsometry P.bd)

lemma line_bdCls :
    Lconc.map F.czSubIso.hom P.line.bdCls = Lconc.tensorLine F.sub N P.bdCls := by
  rw [Lconc.map_cls, Lconc.tensorLine_cls,
    Lconc.cls_eq_of_isometry (P.lineBdIsometry.map F.czSubIso.hom), SymPoincare.map_inv_hom]

/-- `-(X ⊗ ℝ)` is a lifting pair of `D' ⊗ ℝ` itself (the transition image of `D'`). -/
def lineNeg : F.cz.LiftingPair (((CZ.lineData F.quot).sym D').map F.czQuotIso.inv) :=
  P.line.neg.ofIsometry (.ofEq' (by rw [SymPoincare.map_neg, SymPoincare.neg_neg]))

@[simp] lemma lineNeg_X : P.lineNeg.X = ((CZ.lineData A).pair P.X).neg := rfl

lemma lineNeg_bdCls :
    Lconc.map F.czSubIso.hom P.lineNeg.bdCls = -Lconc.tensorLine F.sub N P.bdCls := by
  change Lconc.map F.czSubIso.hom P.line.neg.bdCls = _
  rw [neg_bdCls, map_neg, line_bdCls]

end KaroubiFiltration.LiftingPair

/-! ### Iterates: lifting pairs at level `j` -/

namespace KaroubiFiltration

variable {A : InvCat} (F : KaroubiFiltration A) {N : ℤ}

/-- **A lifting pair at level `j`** of a closed `(N+1)`-complex `D` of `C_ℤ^{∘j}(A/U)`: a
lifting pair over `C_ℤ^{∘j} F` of the transport of `D` along
`F.czIterQuotIso j : (C_ℤ^{∘j} F).quot ≅ C_ℤ^{∘j}(A/U)`. -/
abbrev LiftingPairAt (j : ℕ) (D : SymPoincare (F.quot.czIter j).inv (N + 1)) :=
  (F.czIter j).LiftingPair (D.map (F.czIterQuotIso j).inv)

/-- **(L1) after one transition, at every level**: for a closed `(N+1)`-complex `D` of
`C_ℤ^{∘j}(A/U)` (any Kar complex) with `N + 1 ≥ 0`, its transition image `D ⊗ ℝ` has a lifting
pair at level `j + 1`. -/
theorem nonempty_liftingPairAt_succ (j : ℕ) (D : SymPoincare (F.quot.czIter j).inv (N + 1))
    (hN : 0 ≤ N + 1) :
    Nonempty (F.LiftingPairAt (j + 1) ((CZ.lineData (F.quot.czIter j)).sym D)) := by
  obtain ⟨P⟩ := (F.czIter j).nonempty_liftingPair_sym (D.map (F.czIterQuotIso j).inv) hN
  exact ⟨P.ofIsometry (((CZ.lineHom (F.czIterQuotIso j).inv).symMapIsometry D).map
    (F.czIter j).czQuotIso.inv)⟩

namespace LiftingPairAt

variable {F} {j : ℕ} {D : SymPoincare (F.quot.czIter j).inv (N + 1)} (P : F.LiftingPairAt j D)

/-- The boundary class at level `j`, in `Lconc (C_ℤ^{∘j} U) N`. -/
abbrev bdClsAt : Lconc (F.sub.czIter j) N := Lconc.map (F.czIterSubIso j).hom P.bdCls

/-- The sign-normalized boundary class `σ_j [Y] = (-1)^j [Y]` at level `j`. -/
abbrev sgnBdClsAt : Lconc (F.sub.czIter j) N := (j : ℤ).negOnePow • P.bdClsAt

/-- **Compatibility with the transitions at level `j`**: `X ⊗ ℝ` is a lifting pair at level
`j + 1` of `-(D ⊗ ℝ)`. -/
def line : F.LiftingPairAt (j + 1) ((CZ.lineData (F.quot.czIter j)).sym D).neg :=
  (LiftingPair.line P).ofIsometry
    ((((CZ.lineHom (F.czIterQuotIso j).inv).symMapIsometry D).neg.trans
      (.ofEq' (SymPoincare.map_neg _ _).symm)).map (F.czIter j).czQuotIso.inv)

/-- The boundary of `P.line` is `P.bd ⊗ ℝ` (`s_N = +1`). -/
lemma line_bdClsAt : P.line.bdClsAt = Lconc.tensorLine (F.sub.czIter j) N P.bdClsAt := by
  change Lconc.map ((F.czIter j).czSubIso.hom ≫ CZ.map (F.czIterSubIso j).hom)
    (LiftingPair.line P).bdCls = _
  rw [Lconc.map_comp, AddMonoidHom.comp_apply, LiftingPair.line_bdCls, ← Lconc.tensorLine_map]

/-- `-(X ⊗ ℝ)` is a lifting pair at level `j + 1` of the transition image `D ⊗ ℝ`. -/
def lineNeg : F.LiftingPairAt (j + 1) ((CZ.lineData (F.quot.czIter j)).sym D) :=
  (LiftingPair.neg P.line).ofIsometry (.ofEq' (by rw [SymPoincare.map_neg, SymPoincare.neg_neg]))

/-- The boundary class of `P.lineNeg` is `-(P.bdCls ⊗ ℝ)` (`s_N t_N = -1`). -/
lemma lineNeg_bdClsAt :
    P.lineNeg.bdClsAt = -Lconc.tensorLine (F.sub.czIter j) N P.bdClsAt := by
  change Lconc.map (F.czIterSubIso (j + 1)).hom (LiftingPair.neg P.line).bdCls = _
  rw [LiftingPair.neg_bdCls, map_neg, ← P.line_bdClsAt]

/-- **The normalized boundary class commutes with the transitions**: `σ_{j+1} [∂(-(X ⊗ ℝ))] =
(σ_j [∂X]) ⊗ ℝ` for `σ_j = (-1)^j`. -/
lemma lineNeg_sgnBdClsAt :
    P.lineNeg.sgnBdClsAt = Lconc.tensorLine (F.sub.czIter j) N P.sgnBdClsAt := by
  rw [sgnBdClsAt, sgnBdClsAt, lineNeg_bdClsAt, Nat.cast_succ, Int.negOnePow_succ, Units.neg_smul,
    smul_neg, neg_neg, Units.smul_def, Units.smul_def, map_zsmul]

lemma line_sgnBdClsAt :
    P.line.sgnBdClsAt = -Lconc.tensorLine (F.sub.czIter j) N P.sgnBdClsAt := by
  rw [sgnBdClsAt, sgnBdClsAt, line_bdClsAt, Nat.cast_succ, Int.negOnePow_succ, Units.neg_smul,
    Units.smul_def, Units.smul_def, map_zsmul]

end LiftingPairAt

end KaroubiFiltration

/-! ### Level `0`: H2 -/

namespace SymPair

variable {A : InvCat} (F : KaroubiFiltration A) {N : ℤ}

/-- **H2 at level `0`**: a pair with boundary in `U` is a lifting pair at level `0` of its image
(`SymPair.liftingPair`). -/
def liftingPairAt (X : SymPair A.inv N) (hU : ∀ r, F.U (X.bd.C.X r)) :
    F.LiftingPairAt 0 (X.toQuot F hU) :=
  X.liftingPair F hU

lemma liftingPairAt_bdClsAt (X : SymPair A.inv N) (hU : ∀ r, F.U (X.bd.C.X r)) :
    (X.liftingPairAt F hU).bdClsAt = Lconc.cls (X.bdLift F hU) := by
  change Lconc.map (𝟙 _) _ = _
  rw [Lconc.map_id]
  rfl

lemma liftingPairAt_sgnBdClsAt (X : SymPair A.inv N) (hU : ∀ r, F.U (X.bd.C.X r)) :
    (X.liftingPairAt F hU).sgnBdClsAt = Lconc.cls (X.bdLift F hU) := by
  rw [KaroubiFiltration.LiftingPairAt.sgnBdClsAt, liftingPairAt_bdClsAt, Nat.cast_zero,
    Int.negOnePow_zero, one_smul]

/-- **H2 through one transition** (`bsign = 1`): `-(X ⊗ ℝ)` is a lifting pair at level `1` of
the transition image `X.toQuot ⊗ ℝ`, and its normalized boundary class `σ_1 [∂] = -[∂]` is
`[X.bdLift] ⊗ ℝ`, the transition image of `[X.bdLift]`. -/
lemma liftingPairAt_lineNeg_sgnBdClsAt (X : SymPair A.inv N) (hU : ∀ r, F.U (X.bd.C.X r)) :
    (X.liftingPairAt F hU).lineNeg.sgnBdClsAt =
      Lconc.tensorLine F.sub N (Lconc.cls (X.bdLift F hU)) := by
  rw [KaroubiFiltration.LiftingPairAt.lineNeg_sgnBdClsAt, liftingPairAt_sgnBdClsAt]
  rfl

end SymPair

/-! ### (3) Naturality -/

namespace KaroubiFiltration

variable {A B : InvCat} {F : KaroubiFiltration A} {F' : KaroubiFiltration B} {N : ℤ}
  (Φ : FiltrationHom F F')

lemma czIterQuotIso_inv_comp_quot (j : ℕ) :
    (F.czIterQuotIso j).inv ≫ (Φ.czIter j).quot =
      CZ.mapIter j Φ.quot ≫ (F'.czIterQuotIso j).inv := by
  rw [Iso.inv_comp_eq, ← assoc, Iso.eq_comp_inv, Φ.czIter_quot_comp_czIterQuotIso]

namespace LiftingPairAt

variable {j : ℕ} {D : SymPoincare (F.quot.czIter j).inv (N + 1)} (P : F.LiftingPairAt j D)

/-- **Naturality of lifting pairs at level `j`** under maps of filtrations. -/
def map : F'.LiftingPairAt j (D.map (CZ.mapIter j Φ.quot)) :=
  (LiftingPair.map P (Φ.czIter j)).ofIsometry (.ofEq' (by
    change D.map ((F.czIterQuotIso j).inv ≫ (Φ.czIter j).quot) =
      D.map (CZ.mapIter j Φ.quot ≫ (F'.czIterQuotIso j).inv)
    rw [czIterQuotIso_inv_comp_quot]))

lemma map_bdClsAt : (P.map Φ).bdClsAt = Lconc.map (CZ.mapIter j Φ.sub) P.bdClsAt := by
  change Lconc.map (F'.czIterSubIso j).hom (LiftingPair.map P (Φ.czIter j)).bdCls = _
  rw [LiftingPair.map_bdCls, ← AddMonoidHom.comp_apply, ← Lconc.map_comp,
    Φ.czIter_sub_comp_czIterSubIso, Lconc.map_comp, AddMonoidHom.comp_apply]

lemma map_sgnBdClsAt : (P.map Φ).sgnBdClsAt = Lconc.map (CZ.mapIter j Φ.sub) P.sgnBdClsAt := by
  rw [sgnBdClsAt, sgnBdClsAt, map_bdClsAt, Units.smul_def, Units.smul_def, map_zsmul]

/-- **Naturality of the line construction** on boundary classes. -/
lemma line_map_bdClsAt : (P.map Φ).line.bdClsAt = (P.line.map Φ).bdClsAt := by
  rw [line_bdClsAt, map_bdClsAt, map_bdClsAt, line_bdClsAt, Lconc.tensorLine_map]
  rfl

lemma lineNeg_map_bdClsAt : (P.map Φ).lineNeg.bdClsAt = (P.lineNeg.map Φ).bdClsAt := by
  rw [lineNeg_bdClsAt, map_bdClsAt, map_bdClsAt, lineNeg_bdClsAt, Lconc.tensorLine_map, map_neg]
  rfl

end LiftingPairAt

end KaroubiFiltration

end

end HSFormal.LTheory
