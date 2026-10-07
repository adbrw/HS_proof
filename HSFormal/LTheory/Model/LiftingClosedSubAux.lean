import HSFormal.LTheory.Model.Exact
import HSFormal.LTheory.Model.BoundaryConstructionRel
import HSFormal.LTheory.Model.CutTrunc

/-!
# Raw closed complexes and the trace cobordism in general degrees (for `LiftingClosedSub`)

Infrastructure for `Model/LiftingClosedSub.lean`.

* `RawSym`: a strictly symmetric Poincaré complex **without** the support condition (the new face
  `Z_D` of the relative boundary construction lives in `[-1, N + 2]`); `ofSymPoincare`, `neg`,
  `sum` (copies of the `SymPoincare` constructions, which never use the support), and
  `RawSym.transport`, the honest `SymPoincare` obtained by transporting along a Kar equivalence
  with an idempotent supported in `[0, N]`.
* `RelRawPair.rawClosed`: a raw pair on a boundary with zero chain objects is a raw closed
  complex (as `SymPair.closedOfIsZero`).
* `KarHtpyEquiv.sum`: direct sums of Kar homotopy equivalences.
* `zcone K = Cone(K ⟶ 0)`, `zconeIso : K ≅ Σ⁻¹ zcone K` and
  `zconeDualIso : (zcone K)^{M+1-*} ≅ K^{M-*}` (with the signs `(-1)^r`).
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression
  homotopyCofiber

noncomputable section

variable {V : Type*} [Category V] [Preadditive V] {J : StrictInvolution V} {N : ℤ}

/-! ### Raw strictly symmetric Poincaré complexes -/

variable (J N) in
/-- An `N`-dimensional strictly symmetric Poincaré complex in `Kar V` **without** the support
condition. -/
structure RawSym where
  C : ChainComplex V ℤ
  p : C ⟶ C
  p_idem : p ≫ p = p
  φ : dualComplex J N C ⟶ C
  φ_kar : dualHom J N p ≫ φ ≫ p = φ
  symm : IsStrictSymm J N φ
  poincare : IsPoincare J N p φ

namespace RawSym

attribute [reassoc (attr := simp)] p_idem

variable (P Q : RawSym J N)

/-- A Poincaré complex as a raw one. -/
@[simps, implicit_reducible]
def ofSymPoincare (P : SymPoincare J N) : RawSym J N :=
  ⟨P.C, P.p, P.p_idem, P.φ, P.φ_kar, P.symm, P.poincare⟩

/-- `-(C, φ) = (C, -φ)`. -/
@[simps, implicit_reducible]
def neg : RawSym J N where
  C := P.C
  p := P.p
  p_idem := P.p_idem
  φ := -P.φ
  φ_kar := by simp [P.φ_kar]
  symm := P.symm.neg
  poincare := P.poincare.neg

@[reassoc (attr := simp)]
lemma φ_comp_p : P.φ ≫ P.p = P.φ := by
  rw [← P.φ_kar]; simp

@[reassoc (attr := simp)]
lemma dualHom_p_comp_φ : dualHom J N P.p ≫ P.φ = P.φ := by
  conv_lhs => rw [← P.φ_kar]
  rw [← assoc, ← dualHom_comp, P.p_idem, P.φ_kar]

/-- The direct sum along degreewise bicones (as `SymPoincare.sum`). -/
@[simps, implicit_reducible]
def sum (b : ∀ r, BinaryBicone (P.C.X r) (Q.C.X r)) : RawSym J N where
  C := sumComplex b
  p := sumFst b ≫ P.p ≫ sumInl b + sumSnd b ≫ Q.p ≫ sumInr b
  p_idem := by simp
  φ := dualHom J N (sumInl b) ≫ P.φ ≫ sumInl b + dualHom J N (sumInr b) ≫ Q.φ ≫ sumInr b
  φ_kar := by simp
  symm := (P.symm.conj _).add (Q.symm.conj _)
  poincare := by
    obtain ⟨ψ, hψ, ⟨H₁⟩, ⟨H₂⟩⟩ := P.poincare
    obtain ⟨ψ', hψ', ⟨H₁'⟩, ⟨H₂'⟩⟩ := Q.poincare
    refine ⟨sumFst b ≫ ψ ≫ dualHom J N (sumFst b) + sumSnd b ≫ ψ' ≫ dualHom J N (sumSnd b),
      by simp [reassoc_of% hψ, reassoc_of% hψ'], ⟨homotopyCongr
        (((H₁.compLeft (sumFst b)).compRight (sumInl b)).add
          ((H₁'.compLeft (sumSnd b)).compRight (sumInr b))) (by simp) (by simp)⟩,
      ⟨homotopyCongr
        (((H₂.compLeft (dualHom J N (sumInl b))).compRight (dualHom J N (sumFst b))).add
          ((H₂'.compLeft (dualHom J N (sumInr b))).compRight (dualHom J N (sumSnd b))))
        (by simp) (by simp)⟩⟩

/-- **Transport to an honest Poincaré complex** along `e : (C, p) ≃ (C', p')`, `p'` in `[0, N]`:
`(C', p', f φ f^*)` (as `RawPair.bdTransport`). -/
@[simps, implicit_reducible]
def transport {C' : ChainComplex V ℤ} {p' : C' ⟶ C'} (e : KarHtpyEquiv P.p p')
    (hp' : p' ≫ p' = p') (hs : SupportedIn p' 0 N) : SymPoincare J N where
  C := C'
  p := p'
  p_idem := hp'
  support := hs
  φ := dualHom J N e.f ≫ P.φ ≫ e.f
  φ_kar := by simp only [assoc, e.fp]; rw [← assoc, ← dualHom_comp, e.fp]
  symm := P.symm.conj e.f
  poincare := (e.dual J N).isKarEquiv.comp (IsKarEquiv.comp P.poincare e.isKarEquiv
    (dualHom_idem P.p_idem) P.p_idem hp') (dualHom_idem hp') (dualHom_idem P.p_idem) hp'

end RawSym

/-! ### Sums of Kar homotopy equivalences -/

namespace KarHtpyEquiv

variable {C C' D D' : ChainComplex V ℤ} {p : C ⟶ C} {p' : C' ⟶ C'} {q : D ⟶ D}
  {q' : D' ⟶ D'} (e : KarHtpyEquiv p p') (e' : KarHtpyEquiv q q')
  (b : ∀ r, BinaryBicone (C.X r) (D.X r)) (b' : ∀ r, BinaryBicone (C'.X r) (D'.X r))

/-- The direct sum `e ⊕ e'` of Kar homotopy equivalences. -/
@[simps]
def sum : KarHtpyEquiv (sumFst b ≫ p ≫ sumInl b + sumSnd b ≫ q ≫ sumInr b)
    (sumFst b' ≫ p' ≫ sumInl b' + sumSnd b' ≫ q' ≫ sumInr b') where
  f := sumFst b ≫ e.f ≫ sumInl b' + sumSnd b ≫ e'.f ≫ sumInr b'
  g := sumFst b' ≫ e.g ≫ sumInl b + sumSnd b' ≫ e'.g ≫ sumInr b
  pf := by simp [add_comp, comp_add]
  fp := by simp [add_comp, comp_add]
  pg := by simp [add_comp, comp_add]
  gp := by simp [add_comp, comp_add]
  fg := homotopyCongr (((e.fg.compLeft (sumFst b)).compRight (sumInl b)).add
      ((e'.fg.compLeft (sumSnd b)).compRight (sumInr b))) (by simp [add_comp, comp_add])
      (by simp)
  gf := homotopyCongr (((e.gf.compLeft (sumFst b')).compRight (sumInl b')).add
      ((e'.gf.compLeft (sumSnd b')).compRight (sumInr b'))) (by simp [add_comp, comp_add])
      (by simp)

end KarHtpyEquiv

/-! ### A raw pair on a vanishing boundary is a raw closed complex -/

namespace RelRawPair

variable [HasBinaryBiproducts V] {P : SymPoincare J N} (X : RelRawPair P)
  (hZ : ∀ r, IsZero (P.C.X r))
include hZ

lemma j_f_eq_zero (r : ℤ) : X.j.f r = 0 := (hZ r).eq_of_src _ _

/-- With vanishing boundary, the relative top `δφ` is a chain map `D^{N+1-*} ⟶ D`. -/
@[simps, implicit_reducible]
def topHom : dualComplex J (N + 1) X.D ⟶ X.D where
  f r := relTop X.δφ r
  comm' r r' h := by simp [relTop_comm X.δφ r r' h, X.j_f_eq_zero hZ]

/-- With vanishing boundary, the projection `Cone(j) ⟶ D` is a chain map. -/
@[simps]
def coneSnd : cone X.j ⟶ X.D where
  f i := sndX X.j i
  comm' i i' h := by simp [d_sndX X.j i i' h, X.j_f_eq_zero hZ]

/-- With vanishing boundary, `inr : D ⟶ Cone(j)` is an isomorphism. -/
@[simps]
def coneIso : cone X.j ≅ X.D where
  hom := X.coneSnd hZ
  inv := inr X.j
  hom_inv_id := by
    ext i
    have h : fstX X.j i (i - 1) (by simp) = 0 := (hZ _).eq_of_tgt _ _
    rw [comp_f, id_f, cone.id_X X.j i (i - 1) (by simp), h]
    simp
  inv_hom_id := by ext; simp

lemma relDuality_eq_of_isZero : relDuality X.δφ = dualHom J (N + 1) (inr X.j) ≫ X.topHom hZ := by
  ext r
  simp [X.j_f_eq_zero hZ]

lemma inr_comp_coneIdem_comp_coneSnd :
    inr X.j ≫ coneMap P.p X.pD (comm_of_kar P.p_idem X.pD_idem X.j_kar) ≫ X.coneSnd hZ =
      X.pD := by
  ext; simp

omit hZ in
lemma dualHom_pD_comp_δφ_hom (r r' : ℤ) :
    (dualHom J N X.pD).f r ≫ X.δφ.hom r r' = X.δφ.hom r r' := by
  conv_lhs => rw [← X.δφ_kar]
  rw [← assoc, ← comp_f, ← dualHom_comp, X.pD_idem, X.δφ_kar]

omit hZ in
lemma δφ_hom_comp_pD (r r' : ℤ) : X.δφ.hom r r' ≫ X.pD.f r' = X.δφ.hom r r' := by
  conv_lhs => rw [← X.δφ_kar]
  rw [assoc, assoc, ← comp_f, X.pD_idem, X.δφ_kar]

/-- **A raw pair on a vanishing boundary is a raw closed complex** `(D, p_D, δφ)` of dimension
`N + 1` (as `SymPair.closedOfIsZero`). -/
@[simps, implicit_reducible]
def rawClosed : RawSym J (N + 1) where
  C := X.D
  p := X.pD
  p_idem := X.pD_idem
  φ := X.topHom hZ
  φ_kar := by
    ext r
    simp only [comp_f, dualHom_f, topHom_f]
    rw [← assoc, star_comp_relTop X.δφ X.dualHom_pD_comp_δφ_hom, relTop, assoc,
      X.δφ_hom_comp_pD]
  symm := by
    ext r
    rw [transposeHom_f]
    exact relTop_transpose X.δφ X.symm r
  poincare := by
    have h := X.poincare.conjIso (dualIso J (N + 1) (X.coneIso hZ)).symm
    simp only [Iso.symm_inv, Iso.symm_hom, dualIso_hom, dualIso_inv, coneIso_hom, coneIso_inv,
      ← dualHom_comp, assoc, X.inr_comp_coneIdem_comp_coneSnd hZ] at h
    rw [isPoincare_iff]
    convert h using 1
    rw [relDuality_eq_of_isZero X hZ, ← assoc, ← dualHom_comp, ← X.coneIso_inv hZ,
      ← X.coneIso_hom hZ, Iso.inv_hom_id, dualHom_id, id_comp]

end RelRawPair

/-! ### The cone of a map to zero -/

section ZeroCone

variable [HasBinaryBiproducts V] [HasFiniteBiproducts V] (K : ChainComplex V ℤ)

/-- `ΣK = Cone(K ⟶ 0)`. -/
abbrev zcone : ChainComplex V ℤ := cone (0 : K ⟶ (HomologicalComplex.zero : ChainComplex V ℤ))

@[reassoc (attr := simp)]
lemma zcone_fstX_inlX (n k : ℤ) (h : (ComplexShape.down ℤ).Rel n k) :
    fstX (0 : K ⟶ HomologicalComplex.zero) n k h ≫ inlX (0 : K ⟶ HomologicalComplex.zero) k n h =
      𝟙 _ := by
  have h0 : sndX (0 : K ⟶ HomologicalComplex.zero) n = 0 := (isZero_zero V).eq_of_tgt _ _
  apply ext_to_X _ n k h
  · simp
  · simp [h0]

/-- `K ≅ Σ⁻¹ Cone(K ⟶ 0)`, `x ↦ (x, 0)`. -/
@[simps]
def zconeIso : K ≅ desusp (zcone K) where
  hom :=
    { f := fun r ↦ inlX (0 : K ⟶ HomologicalComplex.zero) r (r + 1) (down_rel_succ r)
      comm' := fun r r' h ↦ by
        obtain rfl : r = r' + 1 := by simp at h; omega
        simp [inlX_d _ (r' + 1 + 1) (r' + 1) r' (down_rel_succ _) (down_rel_succ _)] }
  inv := coneFst (0 : K ⟶ HomologicalComplex.zero)
  hom_inv_id := by ext; simp [coneFst]
  inv_hom_id := by ext n; simp [coneFst]

variable (J : StrictInvolution V) (M : ℤ)

/-- The components of `(Cone(K ⟶ 0))^{M+1-*} ≅ K^{M-*}`. -/
@[simps]
def zconeDualIsoX (r : ℤ) : (dualComplex J (M + 1) (zcone K)).X r ≅ (dualComplex J M K).X r where
  hom := r.negOnePow • J.star (inlX (0 : K ⟶ HomologicalComplex.zero) (M - r) (M + 1 - r)
    (down_rel_sub M r))
  inv := r.negOnePow • J.star (fstX (0 : K ⟶ HomologicalComplex.zero) (M + 1 - r) (M - r)
    (down_rel_sub M r))
  hom_inv_id := by
    simp only [dualComplex_X, Linear.units_smul_comp, Linear.comp_units_smul, smul_smul,
      Int.units_mul_self, one_smul, ← J.star_comp, zcone_fstX_inlX]
    exact J.star_id _
  inv_hom_id := by
    simp only [dualComplex_X, Linear.units_smul_comp, Linear.comp_units_smul, smul_smul,
      Int.units_mul_self, one_smul, cone.star_fstX_inlX]

/-- `(Cone(K ⟶ 0))^{M+1-*} ≅ K^{M-*}` (with the signs `(-1)^r`). -/
def zconeDualIso : dualComplex J (M + 1) (zcone K) ≅ dualComplex J M K :=
  Hom.isoOfComponents (zconeDualIsoX K J M) fun r r' h ↦ by
    obtain rfl : r = r' + 1 := by simp at h; omega
    apply cone.ext_star (J := J) (0 : K ⟶ HomologicalComplex.zero) (M + 1 - (r' + 1))
      (M - (r' + 1)) (down_rel_sub M (r' + 1))
    · simp only [zconeDualIsoX_hom, dualComplex_d, Linear.units_smul_comp, Linear.comp_units_smul,
        cone.star_fstX_inlX_assoc, smul_smul, cone.star_fstX_d_assoc _ (M + 1 - r')
          (M + 1 - (r' + 1)) (M - (r' + 1)) (by simp; omega) (down_rel_sub M (r' + 1)), neg_comp,
        assoc, cone.star_fstX_inlX' _ (by simp; omega : (ComplexShape.down ℤ).Rel
          (M + 1 - r') (M + 1 - (r' + 1))) (down_rel_sub M r'), smul_neg, star_d_XIsoOfEq]
      rw [Int.negOnePow_succ]
      simp
    · exact (isZero_zero V).eq_of_src _ _

@[simp]
lemma zconeDualIso_hom_f (r : ℤ) : (zconeDualIso K J M).hom.f r = (zconeDualIsoX K J M r).hom :=
  rfl

@[simp]
lemma zconeDualIso_inv_f (r : ℤ) : (zconeDualIso K J M).inv.f r = (zconeDualIsoX K J M r).inv :=
  rfl

end ZeroCone

end

end HSFormal.LTheory
