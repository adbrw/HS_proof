import HSFormal.LTheory.Model.Transport
import HSFormal.LTheory.Model.BoundaryConstruction

/-!
# Degree truncation of Kar complexes and the boundary pair of non-connected complexes

Lower L-theory model, module 22 (`DecBij`), part 3 (independent of `LineComplex`/`Triads`).

`SymComplex.boundaryPair` needs the `(N+1)`-dimensional complex `(C, p)` to be concentrated in
`[1, N+1]`: in general `∂C = Σ⁻¹Cone(φ)` lives in `[-1, N+1]` (`∂C_{-1} = C_0`,
`∂C_{N+1} = C^0`).  The Thom complexes of algebraic transversality (`Model/CutComplex.lean`)
live in `[0, N+1]`, and they are *not* Kar homotopy equivalent to complexes in `[1, N+1]` (for
the cellular line, `d : C_1 → C_0` of the lower half has no bounded section).  What holds is
that `(φ_0, d) : C^{N+1} ⊕ C_1 ⟶ C_0` is split surjective, which makes the two end degrees of
`∂C` cancel.  This file provides the general machinery.

* `KarCancel`: for a chain idempotent `p` of `D` and `ρ : D_a ⟶ D_{a+1}` with `ρ d ρ = ρ`
  (Kar for `p`), the null-homotopic idempotent `N = dρ + ρd` (`nmap`) lies below `p`, and
  `p' = p - N` (`cancel`) is a chain idempotent Kar homotopy equivalent to `p`
  (`cancelEquiv`), equal to `p` outside degrees `a, a+1`, with `p'_a = p_a - ρ d` and
  `p'_{a+1} = p_{a+1} - d ρ`.  With `ρ d = p_a` (a Kar section of `d`) this kills degree `a`;
  with `d ρ = p_{a+1}` (a Kar retraction) it kills degree `a + 1`.
* `RawPair`: the data of a `SymPair` whose boundary `(C, p, φ)` is a Poincaré complex **without**
  the support condition.  `RawPair.transportBd` transports it along a Kar equivalence of the
  boundary with a complex supported in `[0, N]`, producing an honest `SymPair` (the proof of
  `SymPair.transportBd` never uses the support of the old boundary).
* `SymComplex.rawBoundaryPair`: Ranicki's boundary pair `(∂C ⟶ C^{N+1-*}, (0, ∂φ))` of a complex
  concentrated in `[0, N+1]` as a `RawPair`; `SymComplex.boundaryPairOf` its transport along a
  truncation `(∂C, p_∂) ≃ (∂C', p')` with `p'` in `[0, N]`.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression

noncomputable section

/-! ### Cancellation of an elementary pair of degrees -/

namespace KarCancel

variable {V : Type*} [Category V] [Preadditive V] {D : ChainComplex V ℤ}

/-- The homotopy data concentrated in `ρ : D_a ⟶ D_b`, `b = a + 1`. -/
def hom (a b : ℤ) (hab : a + 1 = b) (ρ : D.X a ⟶ D.X b) (i j : ℤ)
    (hij : (ComplexShape.down ℤ).Rel j i) : D.X i ⟶ D.X j :=
  if h : i = a then (D.XIsoOfEq h).hom ≫ ρ ≫
    (D.XIsoOfEq (by simp only [ComplexShape.down_Rel] at hij; omega : b = j)).hom else 0

variable {a b : ℤ} {hab : a + 1 = b} {ρ : D.X a ⟶ D.X b}

lemma hom_self (h : (ComplexShape.down ℤ).Rel b a) : hom a b hab ρ a b h = ρ := by
  simp [hom]

lemma hom_ne {i j : ℤ} (h : (ComplexShape.down ℤ).Rel j i) (hi : i ≠ a) :
    hom a b hab ρ i j h = 0 := by
  simp [hom, hi]

variable (hab ρ) in
/-- The null-homotopic map `N = d ρ + ρ d`. -/
def nmap : D ⟶ D := Homotopy.nullHomotopicMap' (hom a b hab ρ)

lemma nmap_f_self : (nmap hab ρ).f a = ρ ≫ D.d b a := by
  rw [nmap, Homotopy.nullHomotopicMap'_f (k₂ := b) (k₁ := a) (k₀ := a - 1)
    (by simp only [ComplexShape.down_Rel]; omega) (by simp), hom_ne _ (by omega), hom_self,
    comp_zero, zero_add]

lemma nmap_f_succ : (nmap hab ρ).f b = D.d b a ≫ ρ := by
  rw [nmap, Homotopy.nullHomotopicMap'_f (k₂ := b + 1) (k₁ := b) (k₀ := a) (by simp)
    (by simp only [ComplexShape.down_Rel]; omega), hom_ne _ (by omega : b ≠ a), hom_self,
    zero_comp, add_zero]

lemma nmap_f_of_ne {r : ℤ} (h₁ : r ≠ a) (h₂ : r ≠ b) : (nmap hab ρ).f r = 0 := by
  rw [nmap, Homotopy.nullHomotopicMap'_f (k₂ := r + 1) (k₁ := r) (k₀ := r - 1) (by simp)
    (by simp), hom_ne _ (by omega : r - 1 ≠ a), hom_ne _ h₁, comp_zero, zero_comp, add_zero]

variable (a b) in
/-- Case analysis on the degree. -/
lemma f_cases {E : ChainComplex V ℤ} {f g : D ⟶ E} (ha : f.f a = g.f a)
    (hb : f.f b = g.f b) (ho : ∀ r, r ≠ a → r ≠ b → f.f r = g.f r) : f = g := by
  ext r
  by_cases h₁ : r = a
  · subst h₁; exact ha
  · by_cases h₂ : r = b
    · subst h₂; exact hb
    · exact ho r h₁ h₂

variable {p : D ⟶ D} (h₁ : ρ ≫ D.d b a ≫ ρ = ρ) (h₂ : p.f a ≫ ρ = ρ) (h₃ : ρ ≫ p.f b = ρ)

include h₂ in
lemma p_nmap : p ≫ nmap hab ρ = nmap hab ρ := by
  refine f_cases a b ?_ ?_ fun r h h' ↦ by rw [comp_f, nmap_f_of_ne h h', comp_zero]
  · rw [comp_f, nmap_f_self, reassoc_of% h₂]
  · rw [comp_f, nmap_f_succ, ← assoc, p.comm, assoc, h₂]

include h₃ in
lemma nmap_p : nmap hab ρ ≫ p = nmap hab ρ := by
  refine f_cases a b ?_ ?_ fun r h h' ↦ by rw [comp_f, nmap_f_of_ne h h', zero_comp]
  · rw [comp_f, nmap_f_self, assoc, ← p.comm, reassoc_of% h₃]
  · rw [comp_f, nmap_f_succ, assoc, h₃]

include h₁ in
lemma nmap_idem : nmap hab ρ ≫ nmap hab ρ = nmap hab ρ := by
  refine f_cases a b ?_ ?_ fun r h h' ↦ by rw [comp_f, nmap_f_of_ne h h', zero_comp]
  · rw [comp_f, nmap_f_self, assoc, reassoc_of% h₁]
  · rw [comp_f, nmap_f_succ]
    simp only [assoc]
    rw [h₁]

omit h₁ h₂ h₃ in
/-- The cancelled idempotent `p' = p - (dρ + ρd)`. -/
def cancel (p : D ⟶ D) (hab : a + 1 = b) (ρ : D.X a ⟶ D.X b) : D ⟶ D := p - nmap hab ρ

lemma cancel_f_of_ne {r : ℤ} (h : r ≠ a) (h' : r ≠ b) : (cancel p hab ρ).f r = p.f r := by
  rw [cancel, sub_f_apply, nmap_f_of_ne h h', sub_zero]

lemma cancel_f_self : (cancel p hab ρ).f a = p.f a - ρ ≫ D.d b a := by
  rw [cancel, sub_f_apply, nmap_f_self]

lemma cancel_f_succ : (cancel p hab ρ).f b = p.f b - D.d b a ≫ ρ := by
  rw [cancel, sub_f_apply, nmap_f_succ]

include h₁ h₂ h₃ in
lemma cancel_idem (hp : p ≫ p = p) : cancel p hab ρ ≫ cancel p hab ρ = cancel p hab ρ := by
  rw [cancel, sub_comp, comp_sub, comp_sub, hp, p_nmap h₂, nmap_p h₃, nmap_idem h₁]
  abel

include h₂ in
lemma p_cancel (hp : p ≫ p = p) : p ≫ cancel p hab ρ = cancel p hab ρ := by
  rw [cancel, comp_sub, hp, p_nmap h₂]

include h₃ in
lemma cancel_p (hp : p ≫ p = p) : cancel p hab ρ ≫ p = cancel p hab ρ := by
  rw [cancel, sub_comp, hp, nmap_p h₃]

/-- `p' ≃ p`: `p - p' = dρ + ρd` is null-homotopic. -/
def cancelHomotopy : Homotopy (cancel p hab ρ) p :=
  (Homotopy.equivSubZero.symm (homotopyCongr (Homotopy.nullHomotopy' (hom a b hab ρ))
    (by rw [cancel, sub_sub_cancel]; rfl) rfl)).symm

include h₁ h₂ h₃ in
/-- **Cancellation**: `(D, p) ≃ (D, p - (dρ + ρd))` in `Kar`. -/
def cancelEquiv (hp : p ≫ p = p) : KarHtpyEquiv p (cancel p hab ρ) where
  f := cancel p hab ρ
  g := cancel p hab ρ
  pf := p_cancel h₂ hp
  fp := cancel_idem h₁ h₂ h₃ hp
  pg := cancel_idem h₁ h₂ h₃ hp
  gp := cancel_p h₃ hp
  fg := homotopyCongr cancelHomotopy (cancel_idem h₁ h₂ h₃ hp).symm rfl
  gf := Homotopy.ofEq (cancel_idem h₁ h₂ h₃ hp)

end KarCancel

/-! ### Pairs with an unsupported boundary -/

variable {V : Type*} [Category V] [Preadditive V] [HasBinaryBiproducts V]

/-- The data of an `(N+1)`-dimensional Poincaré pair `(j : C ⟶ D, (δφ, φ))` whose boundary
`(C, p, φ)` is a strictly symmetric Poincaré complex **not** assumed concentrated in `[0, N]`
(all other fields as in `SymPair`). -/
structure RawPair (J : StrictInvolution V) (N : ℤ) where
  C : ChainComplex V ℤ
  p : C ⟶ C
  p_idem : p ≫ p = p
  φ : dualComplex J N C ⟶ C
  φ_kar : dualHom J N p ≫ φ ≫ p = φ
  φ_symm : IsStrictSymm J N φ
  φ_poincare : IsPoincare J N p φ
  D : ChainComplex V ℤ
  pD : D ⟶ D
  pD_idem : pD ≫ pD = pD
  support : SupportedIn pD 0 (N + 1)
  j : C ⟶ D
  j_kar : p ≫ j ≫ pD = j
  δφ : Homotopy (dualHom J N j ≫ φ ≫ j) 0
  δφ_kar : ∀ r r', (dualHom J N pD).f r ≫ δφ.hom r r' ≫ pD.f r' = δφ.hom r r'
  symm : IsSymmHomotopy J N δφ
  poincare : IsKarEquiv (dualHom J (N + 1) (coneMap p pD (comm_of_kar p_idem pD_idem j_kar)))
    pD (relDuality δφ)

namespace RawPair

variable {J : StrictInvolution V} {N : ℤ} (X : RawPair J N) {C' : ChainComplex V ℤ}
  {p' : C' ⟶ C'} (e : KarHtpyEquiv X.p p')

attribute [reassoc (attr := simp)] p_idem pD_idem

@[reassoc (attr := simp)]
lemma j_comp_pD : X.j ≫ X.pD = X.j := kar_right X.pD_idem X.j_kar

@[reassoc (attr := simp)]
lemma p_comp_j : X.p ≫ X.j = X.j := kar_left X.p_idem X.j_kar

/-- The transported boundary `(C', p', f φ f^*)`, a Poincaré complex in `[0, N]`. -/
@[simps, implicit_reducible]
def bdTransport (hp' : p' ≫ p' = p') (hs : SupportedIn p' 0 N) : SymPoincare J N where
  C := C'
  p := p'
  p_idem := hp'
  support := hs
  φ := dualHom J N e.f ≫ X.φ ≫ e.f
  φ_kar := by simp only [assoc, e.fp]; rw [← assoc, ← dualHom_comp, e.fp]
  symm := X.φ_symm.conj e.f
  poincare := (e.dual J N).isKarEquiv.comp (IsKarEquiv.comp X.φ_poincare e.isKarEquiv
    (dualHom_idem X.p_idem) X.p_idem hp') (dualHom_idem hp') (dualHom_idem X.p_idem) hp'

variable [Linear ℚ V]

/-- The Kar homotopy `(gf) φ (gf)^* ≃ φ` on the boundary, before symmetrization. -/
def bdW₀ : Homotopy (dualHom J N (e.f ≫ e.g) ≫ X.φ ≫ e.f ≫ e.g) X.φ :=
  karHomotopy (p := dualHom J N X.p) (q := X.p)
    (homotopyCongr (conjHomotopy e.fg (Homotopy.refl X.φ)) rfl X.φ_kar)
    (by simp only [assoc, e.gp]; rw [← assoc (dualHom J N X.p), ← dualHom_comp, assoc, e.gp])
    X.φ_kar

omit [Linear ℚ V] in
lemma bdW₀_kar (r r' : ℤ) : (dualHom J N X.p).f r ≫ (X.bdW₀ e).hom r r' ≫ X.p.f r' =
    (X.bdW₀ e).hom r r' := by
  have h₁ (i : ℤ) : X.p.f i ≫ X.p.f i = X.p.f i := idem_f X.p_idem i
  have h₂ : J.star (X.p.f (N - r)) ≫ J.star (X.p.f (N - r)) = J.star (X.p.f (N - r)) := by
    rw [← J.star_comp, h₁]
  simp [bdW₀, h₁, reassoc_of% h₂]

/-- The symmetrized Kar homotopy `W : (gf) φ (gf)^* ≃ φ` on the boundary. -/
def bdW : Homotopy (dualHom J N (e.f ≫ e.g) ≫ X.φ ≫ e.f ≫ e.g) X.φ :=
  symmHomotopy (X.φ_symm.conj _) X.φ_symm (X.bdW₀ e)

lemma bdW_kar (r r' : ℤ) : (dualHom J N X.p).f r ≫ (X.bdW e).hom r r' ≫ X.p.f r' =
    (X.bdW e).hom r r' :=
  kar_symmHomotopy_hom X.p_idem _ _ _ (X.bdW₀_kar e) r r'

/-- The relative structure `j W j^* + δφ` on `j` for the boundary structure `(gf) φ (gf)^*`. -/
def transportBdδφ₀ :
    Homotopy (dualHom J N X.j ≫ (dualHom J N (e.f ≫ e.g) ≫ X.φ ≫ e.f ≫ e.g) ≫ X.j) 0 :=
  (((X.bdW e).compRight X.j).compLeft (dualHom J N X.j)).trans X.δφ

/-- The relative structure of the transported pair, on `j' = g j`. -/
def transportBdδφ : Homotopy (dualHom J N (e.g ≫ X.j) ≫ (dualHom J N e.f ≫ X.φ ≫ e.f) ≫
    e.g ≫ X.j) 0 :=
  homotopyCongr (X.transportBdδφ₀ e) (by simp) rfl

lemma transportBdδφ_hom : (X.transportBdδφ e).hom =
    (fun r r' ↦ (dualHom J N X.j).f r ≫ (X.bdW e).hom r r' ≫ X.j.f r') + X.δφ.hom := rfl

lemma transportBdδφ_kar (r r' : ℤ) : (dualHom J N X.pD).f r ≫ (X.transportBdδφ e).hom r r' ≫
    X.pD.f r' = (X.transportBdδφ e).hom r r' := by
  have h₁ : (dualHom J N X.pD).f r ≫ (dualHom J N X.j).f r = (dualHom J N X.j).f r := by
    rw [← comp_f, ← dualHom_comp, X.j_comp_pD]
  have h₂ : X.j.f r' ≫ X.pD.f r' = X.j.f r' := by rw [← comp_f, X.j_comp_pD]
  simp only [transportBdδφ_hom, Pi.add_apply, comp_add, add_comp, assoc, h₂, reassoc_of% h₁,
    X.δφ_kar]

lemma isSymmHomotopy_transportBdδφ : IsSymmHomotopy J N (X.transportBdδφ e) := by
  rw [IsSymmHomotopy, transposeHomotopy_hom, transportBdδφ_hom, transposeHomFamily_add,
    transposeHomFamily_conj', transposeHomFamily_eq (show IsSymmHomotopy J N (X.bdW e) from
      isSymmHomotopy_symmHomotopy _ _ _), transposeHomFamily_eq X.symm]

variable [HasFiniteBiproducts V]

lemma isKarEquiv_transportBd (hp' : p' ≫ p' = p') (hj : p' ≫ (e.g ≫ X.j) ≫ X.pD = e.g ≫ X.j) :
    IsKarEquiv (dualHom J (N + 1) (coneMap p' X.pD (comm_of_kar hp' X.pD_idem hj))) X.pD
      (relDuality (X.transportBdδφ e)) := by
  have hc : e.g ≫ X.j = (e.g ≫ X.j) ≫ X.pD := by simp
  have hC := isKarEquiv_coneMap hp' X.pD_idem X.p_idem X.pD_idem hj X.j_kar e.g_kar
    (by simp) hc e.symm.isKarEquiv (KarHtpyEquiv.refl X.pD_idem).isKarEquiv
  have hl (r r' : ℤ) : (dualHom J N X.pD).f r ≫ (X.transportBdδφ e).hom r r' =
      (X.transportBdδφ e).hom r r' := by
    conv_lhs => rw [← X.transportBdδφ_kar e]
    rw [← assoc, ← comp_f, ← dualHom_comp, X.pD_idem, X.transportBdδφ_kar]
  have hr (r r' : ℤ) : (X.transportBdδφ e).hom r r' ≫ X.pD.f r' = (X.transportBdδφ e).hom r r' := by
    conv_lhs => rw [← X.transportBdδφ_kar e]
    rw [assoc, assoc, ← comp_f, X.pD_idem, X.transportBdδφ_kar]
  have hid : dualHom J (N + 1) (coneMap _ _ hc) ≫ relDuality (X.transportBdδφ e) =
      relDuality (X.transportBdδφ₀ e) := by
    ext r
    simp [star_coneMap_f hc _ _ (down_rel_sub N r), star_comp_relTop _ hl]
    rfl
  have hΨ := X.poincare.of_homotopy (homotopyCongr (transportRelDualityHomotopy (X.bdW e)
    (X.transportBdδφ₀ e) X.δφ fun _ _ ↦ rfl).symm rfl hid.symm)
  refine IsKarEquiv.of_comp_left hC.dualHom (dualHom_kar ?_) hΨ ?_
    (dualHom_idem (coneMap_idem _ X.p_idem X.pD_idem))
    (dualHom_idem (coneMap_idem _ hp' X.pD_idem)) X.pD_idem
  · rw [coneMap_comp, coneMap_comp]; congr 1 <;> simp
  · have hφ' : dualHom J N p' ≫ (dualHom J N e.f ≫ X.φ ≫ e.f) =
        dualHom J N e.f ≫ X.φ ≫ e.f := by rw [← assoc, ← dualHom_comp, e.fp]
    rw [← assoc, dualHom_coneMap_comp_relDuality _ _ hφ' hl, relDuality_comp_pD (by simp) _ hr]

/-- **Transport of a raw pair along a boundary truncation** `e : (C, p) ≃ (C', p')`, `p'` in
`[0, N]`: the honest Poincaré pair `(g j : C' ⟶ D, (j W j^* + δφ, f φ f^*))` with boundary
`bdTransport e` and the same target (proof of `SymPair.transportBd`). -/
@[simps, implicit_reducible]
def transportBd (hp' : p' ≫ p' = p') (hs : SupportedIn p' 0 N) : SymPair J N where
  bd := X.bdTransport e hp' hs
  D := X.D
  pD := X.pD
  pD_idem := X.pD_idem
  support := X.support
  j := e.g ≫ X.j
  j_kar := by simp
  δφ := X.transportBdδφ e
  δφ_kar := X.transportBdδφ_kar e
  symm := X.isSymmHomotopy_transportBdδφ e
  poincare := X.isKarEquiv_transportBd e hp' (by simp)

end RawPair

/-! ### The raw boundary pair of a complex concentrated in `[0, N+1]` -/

namespace SymComplex

variable {J : StrictInvolution V} {N : ℤ} (X : SymComplex J (N + 1))

/-- **Ranicki's boundary pair as a raw pair** `(j : ∂C ⟶ C^{N+1-*}, (0, ∂φ))`, for `(C, p)`
concentrated in `[0, N+1]`; the boundary `∂C` lives in `[-1, N+1]`. -/
@[simps, implicit_reducible]
def rawBoundaryPair (h : SupportedIn X.p 0 (N + 1)) : RawPair J N where
  C := X.bdC
  p := X.bdP
  p_idem := X.bdP_idem
  φ := X.bdφ
  φ_kar := X.bdφ_kar
  φ_symm := X.bdφ_symm
  φ_poincare := X.bdφ_poincare
  D := dualComplex J (N + 1) X.C
  pD := dualHom J (N + 1) X.p
  pD_idem := X.dualHom_p_idem
  support := (h.dualHom (J := J) (N := N + 1)).mono (by omega) (by omega)
  j := X.bdJ
  j_kar := X.bdJ_kar
  δφ := X.bdRel
  δφ_kar r r' := by simp [bdRel, Homotopy.ofEq]
  symm := by
    rw [IsSymmHomotopy, transposeHomotopy_hom]
    funext r r'
    simp [bdRel, Homotopy.ofEq, transposeHomFamily]
  poincare := X.isKarEquiv_relDuality

variable [Linear ℚ V] [HasFiniteBiproducts V]

/-- **The boundary pair of a complex in `[0, N+1]`** along a truncation
`e : (∂C, p_∂) ≃ (C', p')` with `p'` in `[0, N]`: an honest `(N+1)`-dimensional Poincaré pair with
target `C^{N+1-*}` and boundary `(C', p', f ∂φ f^*)`. -/
abbrev boundaryPairOf (h : SupportedIn X.p 0 (N + 1)) {C' : ChainComplex V ℤ} {p' : C' ⟶ C'}
    (e : KarHtpyEquiv X.bdP p') (hp' : p' ≫ p' = p') (hs : SupportedIn p' 0 N) : SymPair J N :=
  (X.rawBoundaryPair h).transportBd e hp' hs

end SymComplex

end

end HSFormal.LTheory
