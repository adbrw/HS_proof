import HSFormal.LTheory.Model.LineComplex
import HSFormal.LTheory.Model.FreeLineAux

/-!
# Free-ification of `P ⊗ ℝ` (lower L-theory model, module 15)

`blueprint/lower-L-construction.md` §3.2 (L1-i) and §4 row 15.  For line data `L = (Δ, s)`
(`LineComplex.lean`; for `C_ℤ(A)`, `Δ` is the constant functor and `s` the shift) and a Kar
complex `(C, p)` over `A`, the Kar complex `(C, p) ⊗ ℝ = (Cone(s - 1 : ΔC ⟶ ΔC), Δp ⊕ Δp)`
over `B` is Kar homotopy equivalent to an honest (*free*: identity idempotent) bounded complex
over `B`.

**The free model.**  Let `C' = cutCx C lo hi` be the zero-truncation of `C` to the support
`[lo, hi]` of `p` (zero objects outside; `(C, p) ≅ (C', p)` strictly in `Kar`), and put
`free(C, p) = Cone(Δp ∘ s - 1 : ΔC' ⟶ ΔC')` (`freeCx`), with differential
`(x, y) ↦ (-dx, (ps - 1)x + dy)`, i.e. `d_C ⊗ 1 + (p·shift - 1)` (`eg_f`).  Then
`(C, p) ⊗ ℝ ≃ (free(C, p), 1)` (`freeEquiv`): the e-trick `FreeLine.eTrick` splits
`Δp s - 1 = Δp (s - 1) Δp ⊕ (-(1 - Δp))`, and the cone of the second summand is contractible.
`free(C, p)` vanishes outside `[lo, hi + 1]` (`isZero_freeCx_X`), so its identity is a Kar
idempotent supported there (`supportedIn_freeCx`); its chain objects are `ΔC'_{r-1} ⊞ ΔC'_r`
(`freeCxXIso`), i.e. images of objects of `A` (for `C_ℤ`: honest objects of `C_ℤ A`).

**Deviation from the blueprint formula.**  The blueprint's `(C ⊗ ℝ, d_C ⊗ 1 + (p·shift - 1))`
is right as a complex, but it is unbounded whenever the objects of `C` outside the support of
`p` are nonzero (it is only contractible there), so its identity is not an idempotent supported
in `[0, N + 1]` and it carries no `SymPoincare`.  The correct free model applies the formula to
the zero-truncation `C'` of `C`.

**Structures.**  `freeSym P = (L.sym P).transport (freeEquiv)`: the free model with the
transported strictly symmetric structure `f^* φ_{P⊗ℝ} f`.  Its idempotent is `1` (`freeSym_p`;
the hypothesis of `KaroubiFiltration.exists_quotPoincare`), it is homotopy isometric to `P ⊗ ℝ`
(`freeSymIsometry`) and `cls (freeSym P) = cls (P ⊗ ℝ)` (`Lconc.cls_freeSym`).

**Functoriality and pairs.**  A Kar map `j : (C, p) ⟶ (D, q)` induces an honest chain map
`freeMap j` of free models with `g_C ≫ (j ⊗ ℝ) ≫ f_D = freeMap j` (`freeEquiv_g_map_f`) and
`f_C ≫ freeMap j = (j ⊗ ℝ) ≫ f_D` (`freeEquiv_f_freeMap`).  For a pair `Y` over `B`,
`SymPair.toFree` / `toFreeD` transport `Y` along Kar equivalences of its boundary and interior
(resp. interior only) with free complexes; for `Y = X ⊗ ℝ` and `fb = L.freeEquiv ..` the
boundary is `L.freeSym X.bd` by definition.  `SymPair.freeLine` / `freeLineD` do the same given
Kar equivalences with line complexes `(C_b, p_b) ⊗ ℝ`, `(C_D, p_D) ⊗ ℝ`.  `toFreeD` keeps the
boundary, the input shape of `KaroubiFiltration.exists_quotPair`.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression
  homotopyCofiber FreeLine

noncomputable section

namespace LineData

variable {A B : InvCat} (L : LineData A B)

/-! ### The e-trick for line complexes -/

section Chain

variable {C C' : ChainComplex A ℤ}

/-- Kar homotopy equivalences act on line complexes. -/
@[simps]
def mapKarEquiv {p : C ⟶ C} {p' : C' ⟶ C'} (e : KarHtpyEquiv p p') :
    KarHtpyEquiv (L.map p) (L.map p') where
  f := L.map e.f
  g := L.map e.g
  pf := by rw [← map_comp, e.pf]
  fp := by rw [← map_comp, e.fp]
  pg := by rw [← map_comp, e.pg]
  gp := by rw [← map_comp, e.gp]
  fg := homotopyCongr (L.htpy e.fg) (L.map_comp _ _) rfl
  gf := homotopyCongr (L.htpy e.gf) (L.map_comp _ _) rfl

lemma mapH_idem {p : C ⟶ C} (hp : p ≫ p = p) : L.Δ.mapH p ≫ L.Δ.mapH p = L.Δ.mapH p := by
  rw [← Functor.map_comp, hp]

/-- The e-trick differential `Δp ∘ s - 1` on `ΔC` (`eg_f`). -/
abbrev eg (C : ChainComplex A ℤ) (p : C ⟶ C) : L.Δ.mapC C ⟶ L.Δ.mapC C :=
  eDiff (L.g C) (L.Δ.mapH p)

lemma eg_f (p : C ⟶ C) (i : ℤ) :
    (L.eg C p).f i = L.Δ.F.map (p.f i) ≫ L.s.iso.hom.app (C.X i) - 𝟙 _ := by
  rw [eDiff_f, g_f]
  simp only [InvFunctor.mapH, Functor.mapHomologicalComplex_map_f, comp_sub]
  erw [comp_id]
  rw [sub_add_cancel]
  rfl

/-- **The e-trick** for line complexes: `(C, p) ⊗ ℝ ≃ (Cone(Δp ∘ s - 1), 1)`. -/
def eTrick {p : C ⟶ C} (hp : p ≫ p = p) : KarHtpyEquiv (L.map p) (𝟙 (cone (L.eg C p))) :=
  FreeLine.eTrick (L.mapH_idem hp) (L.mapH_comp_g p)

lemma eTrick_f {p : C ⟶ C} (hp : p ≫ p = p) :
    (L.eTrick hp).f = eTo (L.mapH_idem hp) (L.mapH_comp_g p) := rfl

lemma eTrick_g {p : C ⟶ C} (hp : p ≫ p = p) :
    (L.eTrick hp).g = eFrom (L.mapH_idem hp) (L.mapH_comp_g p) := rfl

end Chain

/-! ### The free model -/

section Free

variable {C : ChainComplex A ℤ} {lo hi : ℤ}

variable (C) in
/-- **The free model** of `(C, p) ⊗ ℝ`: `Cone(Δp ∘ s - 1)` on the zero-truncation of `C` to
the support `[lo, hi]` of `p`. -/
@[implicit_reducible]
def freeCx (p : C ⟶ C) (hs : SupportedIn p lo hi) : ChainComplex B ℤ :=
  cone (L.eg (cutCx C lo hi) (cutP hs))

/-- **Free-ification**: `(C, p) ⊗ ℝ ≃ (freeCx C p, 1)` in `Kar B`. -/
def freeEquiv {p : C ⟶ C} (hp : p ≫ p = p) (hs : SupportedIn p lo hi) :
    KarHtpyEquiv (L.map p) (𝟙 (L.freeCx C p hs)) :=
  (L.mapKarEquiv (cutEquiv hs hp)).trans (L.eTrick (cutP_idem hs hp))

lemma freeEquiv_f {p : C ⟶ C} (hp : p ≫ p = p) (hs : SupportedIn p lo hi) :
    (L.freeEquiv hp hs).f = L.map (cutTo hs) ≫
      coneMap (L.Δ.mapH (cutP hs)) (L.Δ.mapH (cutP hs))
        (eDiff_sq_to (L.mapH_idem (cutP_idem hs hp)) (L.mapH_comp_g _)) := rfl

lemma freeEquiv_g {p : C ⟶ C} (hp : p ≫ p = p) (hs : SupportedIn p lo hi) :
    (L.freeEquiv hp hs).g =
      coneMap (L.Δ.mapH (cutP hs)) (L.Δ.mapH (cutP hs))
        (eDiff_sq_from (L.mapH_idem (cutP_idem hs hp)) (L.mapH_comp_g _)) ≫
      L.map (cutFrom hs) := rfl

/-- The chain objects of the free model are images of objects of `A` (of the zero-truncation). -/
def freeCxXIso (p : C ⟶ C) (hs : SupportedIn p lo hi) (r : ℤ) :
    (L.freeCx C p hs).X r ≅ L.Δ.F.obj (cutX C lo hi (r - 1)) ⊞ L.Δ.F.obj (cutX C lo hi r) :=
  XIsoBiprod (L.eg (cutCx C lo hi) (cutP hs)) r (r - 1) (by simp)

lemma isZero_freeCx_X (p : C ⟶ C) (hs : SupportedIn p lo hi) {r : ℤ}
    (hr : r < lo ∨ hi + 1 < r) : IsZero ((L.freeCx C p hs).X r) :=
  isZero_cone_X _ r (L.Δ.F.map_isZero (isZero_cutCx_X C lo hi (by omega)))
    (L.Δ.F.map_isZero (isZero_cutCx_X C lo hi (by omega)))

/-- The identity of the free model is a Kar idempotent supported in `[lo, hi + 1]`. -/
lemma supportedIn_freeCx (p : C ⟶ C) (hs : SupportedIn p lo hi) :
    SupportedIn (𝟙 (L.freeCx C p hs)) lo (hi + 1) := fun r hr ↦ by
  rw [id_f]; exact (L.isZero_freeCx_X p hs hr).eq_of_src _ _

end Free

/-! ### Functoriality of the free model -/

section FreeMap

variable {C D : ChainComplex A ℤ} {pC : C ⟶ C} {pD : D ⟶ D} {loC hiC loD hiD : ℤ}
  (hpC : pC ≫ pC = pC) (hpD : pD ≫ pD = pD) (hsC : SupportedIn pC loC hiC)
  (hsD : SupportedIn pD loD hiD) (j : C ⟶ D)

/-- The chain map `cut C ⟶ cut D` of a map `j`, compressed by `p_C`, `p_D`. -/
def cutMap : cutCx C loC hiC ⟶ cutCx D loD hiD := cutFrom hsC ≫ j ≫ cutTo hsD

include hpC hpD in
lemma cutMap_sq : L.Δ.mapH (cutMap hsC hsD j) ≫ L.eg _ (cutP hsD) =
    L.eg _ (cutP hsC) ≫ L.Δ.mapH (cutMap hsC hsD j) := by
  have h₁ : L.Δ.mapH (cutMap hsC hsD j) ≫ L.Δ.mapH (cutP hsD) =
      L.Δ.mapH (cutMap hsC hsD j) := by
    rw [← Functor.map_comp]; simp only [cutMap, assoc, cutTo_cutP hsD hpD]
  have h₂ : L.Δ.mapH (cutP hsC) ≫ L.Δ.mapH (cutMap hsC hsD j) =
      L.Δ.mapH (cutMap hsC hsD j) := by
    rw [← Functor.map_comp]; simp only [cutMap, cutP_cutFrom_assoc hsC hpC]
  simp only [eDiff, comp_sub, sub_comp, comp_add, add_comp, comp_id, id_comp, reassoc_of% h₁,
    h₁, assoc]
  rw [← L.mapH_comp_g, reassoc_of% h₂, h₂]

/-- **The free model of a Kar map** `j : (C, p_C) ⟶ (D, p_D)`: an honest chain map. -/
def freeMap : L.freeCx C pC hsC ⟶ L.freeCx D pD hsD :=
  coneMap (L.Δ.mapH (cutMap hsC hsD j)) (L.Δ.mapH (cutMap hsC hsD j))
    (L.cutMap_sq hpC hpD hsC hsD j)

/-- The free model of `j` is `g_C ≫ (j ⊗ ℝ) ≫ f_D` (for any chain map `j`: the outer maps
compress it by `p_C`, `p_D`). -/
lemma freeEquiv_g_map_f :
    (L.freeEquiv hpC hsC).g ≫ L.map j ≫ (L.freeEquiv hpD hsD).f =
      L.freeMap hpC hpD hsC hsD j := by
  rw [freeEquiv_g, freeEquiv_f, LineData.map, LineData.map, LineData.map, freeMap]
  simp only [assoc, coneMap_comp]
  congr 1 <;> simp only [cutMap, ← Functor.map_comp, cutTo_cutP hsD hpD,
    cutP_cutFrom_assoc hsC hpC]

variable {j} in
/-- For a Kar map `j`, the free model of `j` commutes strictly with the equivalences:
`f_C ≫ free(j) = (j ⊗ ℝ) ≫ f_D`. -/
lemma freeEquiv_f_freeMap (hj : pC ≫ j ≫ pD = j) :
    (L.freeEquiv hpC hsC).f ≫ L.freeMap hpC hpD hsC hsD j =
      L.map j ≫ (L.freeEquiv hpD hsD).f := by
  have hjC : pC ≫ j = j := by rw [← hj, reassoc_of% hpC]
  rw [freeEquiv_f, freeEquiv_f, LineData.map, LineData.map, LineData.map, freeMap]
  simp only [assoc, coneMap_comp]
  congr 1 <;> simp only [← Functor.map_comp, cutMap, cutP_cutFrom_assoc hsC hpC,
    cutTo_cutFrom_assoc hsC hpC, cutTo_cutP hsD hpD, reassoc_of% hjC]

end FreeMap

/-! ### The free model with its symmetric Poincaré structure -/

section Sym

variable {N : ℤ} (P : SymPoincare A.inv N)

/-- **`P ⊗ ℝ` as a free complex**: the free model `freeCx P.C P.p` (identity idempotent) with
the transported strictly symmetric structure `f^* φ_{P⊗ℝ} f`. -/
def freeSym : SymPoincare B.inv (N + 1) :=
  (L.sym P).transport (id_comp _) (L.supportedIn_freeCx P.p P.support)
    (L.freeEquiv P.p_idem P.support)

@[simp]
lemma freeSym_C : (L.freeSym P).C = L.freeCx P.C P.p P.support := rfl

@[simp]
lemma freeSym_p : (L.freeSym P).p = 𝟙 _ := rfl

/-- The free model is free: its idempotent is `1` in every degree (in particular on
`[0, N + 1]`, the hypothesis of `KaroubiFiltration.exists_quotPoincare`). -/
lemma freeSym_p_f (r : ℤ) : (L.freeSym P).p.f r = 𝟙 _ := rfl

lemma freeSym_φ : (L.freeSym P).φ = dualHom B.inv (N + 1) (L.freeEquiv P.p_idem P.support).f ≫
    (L.sym P).φ ≫ (L.freeEquiv P.p_idem P.support).f := rfl

lemma isZero_freeSym_X {r : ℤ} (hr : r < 0 ∨ N + 1 < r) : IsZero ((L.freeSym P).C.X r) :=
  L.isZero_freeCx_X P.p P.support hr

/-- `P ⊗ ℝ` is homotopy isometric to its free model. -/
def freeSymIsometry : (L.sym P).HomotopyIsometry (L.freeSym P) :=
  (L.sym P).transportIsometry _ _ _

lemma isometric_freeSym : (L.sym P).Isometric (L.freeSym P) :=
  ⟨L.freeSymIsometry P⟩

end Sym

end LineData

/-- **`cls (P ⊗ ℝ) = cls (free model)`**. -/
theorem Lconc.cls_freeSym {A B : InvCat} (L : LineData A B) {N : ℤ} (P : SymPoincare A.inv N) :
    Lconc.cls (L.freeSym P) = Lconc.cls (L.sym P) :=
  Lconc.cls_transport _ _ _ _

/-- Null-cobordisms of `P ⊗ ℝ` transport to its free model. -/
lemma NullCobordant.freeSym {A B : InvCat} (L : LineData A B) {N : ℤ} {P : SymPoincare A.inv N}
    (h : NullCobordant (L.sym P)) : NullCobordant (L.freeSym P) :=
  h.transport _ _ _

/-! ### The relative version: pairs -/

namespace SymPair

section ToFree

variable {B : InvCat} {M : ℤ} (Y : SymPair B.inv M) {Fb FD : ChainComplex B ℤ}
  (hsb : SupportedIn (𝟙 Fb) 0 M) (hsD : SupportedIn (𝟙 FD) 0 (M + 1))

/-- **A pair made free**: transport of `Y` along Kar equivalences of its boundary and interior
with free complexes `(F_b, 1)`, `(F_D, 1)`.  For `Y = X ⊗ ℝ` (boundary `L.sym X.bd`, interior
idempotent `L.map X.pD`) take `fb = L.freeEquiv X.bd.p_idem X.bd.support`; the boundary is then
`L.freeSym X.bd` by definition (`toFree_bd`). -/
abbrev toFree (fb : KarHtpyEquiv Y.bd.p (𝟙 Fb)) (fD : KarHtpyEquiv Y.pD (𝟙 FD)) :
    SymPair B.inv M :=
  Y.transport fb fD (id_comp _) hsb (id_comp _) hsD

lemma toFree_bd (fb : KarHtpyEquiv Y.bd.p (𝟙 Fb)) (fD : KarHtpyEquiv Y.pD (𝟙 FD)) :
    (Y.toFree hsb hsD fb fD).bd = Y.bd.transport (id_comp _) hsb fb := rfl

lemma toFree_j (fb : KarHtpyEquiv Y.bd.p (𝟙 Fb)) (fD : KarHtpyEquiv Y.pD (𝟙 FD)) :
    (Y.toFree hsb hsD fb fD).j = (fb.g ≫ Y.j) ≫ fD.f := rfl

/-- **The interior made free**, boundary kept (the input shape of
`KaroubiFiltration.exists_quotPair`). -/
abbrev toFreeD (fD : KarHtpyEquiv Y.pD (𝟙 FD)) : SymPair B.inv M :=
  Y.transportD fD (id_comp _) hsD

lemma toFreeD_bd (fD : KarHtpyEquiv Y.pD (𝟙 FD)) : (Y.toFreeD hsD fD).bd = Y.bd := rfl

lemma toFreeD_j (fD : KarHtpyEquiv Y.pD (𝟙 FD)) : (Y.toFreeD hsD fD).j = Y.j ≫ fD.f := rfl

end ToFree

variable {A B : InvCat} (L : LineData A B) {N : ℤ} (Y : SymPair B.inv (N + 1))
  {Cb CD : ChainComplex A ℤ} {pb : Cb ⟶ Cb} {pD : CD ⟶ CD}
  (hpb : pb ≫ pb = pb) (hpD : pD ≫ pD = pD) (hsb : SupportedIn pb 0 N)
  (hsD : SupportedIn pD 0 (N + 1))

section Interior

variable (eD : KarHtpyEquiv Y.pD (L.map pD))

/-- **Free-ification of the interior**, boundary kept: for a pair `Y` over `B` and a Kar
equivalence `e_D` of its interior with a line complex `(C_D, p_D) ⊗ ℝ`, the transported pair
with interior the free model `(freeCx C_D p_D, 1)` and map `j ≫ f`. -/
def freeLineD : SymPair B.inv (N + 1) :=
  Y.toFreeD (L.supportedIn_freeCx pD hsD) (eD.trans (L.freeEquiv hpD hsD))

@[simp]
lemma freeLineD_bd : (Y.freeLineD L hpD hsD eD).bd = Y.bd := rfl

@[simp]
lemma freeLineD_D : (Y.freeLineD L hpD hsD eD).D = L.freeCx CD pD hsD := rfl

@[simp]
lemma freeLineD_pD : (Y.freeLineD L hpD hsD eD).pD = 𝟙 _ := rfl

lemma freeLineD_j : (Y.freeLineD L hpD hsD eD).j = Y.j ≫ (eD.trans (L.freeEquiv hpD hsD)).f :=
  rfl

end Interior

variable (eb : KarHtpyEquiv Y.bd.p (L.map pb)) (eD : KarHtpyEquiv Y.pD (L.map pD))

/-- **Free-ification of a pair**: for a pair `Y` over `B` and Kar equivalences of its boundary
and interior with line complexes `(C_b, p_b) ⊗ ℝ`, `(C_D, p_D) ⊗ ℝ`, the transported pair whose
boundary and interior are the free models (identity idempotents).  (For `Y = X ⊗ ℝ`, `toFree`
with `L.freeEquiv` directly gives boundary exactly `L.freeSym X.bd`.) -/
def freeLine : SymPair B.inv (N + 1) :=
  Y.toFree (L.supportedIn_freeCx pb hsb) (L.supportedIn_freeCx pD hsD)
    (eb.trans (L.freeEquiv hpb hsb)) (eD.trans (L.freeEquiv hpD hsD))

lemma freeLine_bd : (Y.freeLine L hpb hpD hsb hsD eb eD).bd =
    Y.bd.transport (id_comp _) (L.supportedIn_freeCx pb hsb) (eb.trans (L.freeEquiv hpb hsb)) :=
  rfl

@[simp]
lemma freeLine_bd_C : (Y.freeLine L hpb hpD hsb hsD eb eD).bd.C = L.freeCx Cb pb hsb := rfl

@[simp]
lemma freeLine_bd_p : (Y.freeLine L hpb hpD hsb hsD eb eD).bd.p = 𝟙 _ := rfl

@[simp]
lemma freeLine_D : (Y.freeLine L hpb hpD hsb hsD eb eD).D = L.freeCx CD pD hsD := rfl

@[simp]
lemma freeLine_pD : (Y.freeLine L hpb hpD hsb hsD eb eD).pD = 𝟙 _ := rfl

lemma freeLine_j : (Y.freeLine L hpb hpD hsb hsD eb eD).j =
    ((eb.trans (L.freeEquiv hpb hsb)).g ≫ Y.j) ≫ (eD.trans (L.freeEquiv hpD hsD)).f := rfl

/-- The boundary of the free pair has the class of the boundary of `Y`. -/
lemma cls_freeLine_bd : Lconc.cls (Y.freeLine L hpb hpD hsb hsD eb eD).bd = Lconc.cls Y.bd :=
  Lconc.cls_transport _ _ _ _

end SymPair

end

end HSFormal.LTheory
