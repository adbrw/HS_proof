import HSFormal.LTheory.Model.LiftComplex
import HSFormal.LTheory.Model.Domination
import HSFormal.LTheory.Union

/-!
# Lifting pairs: technical lemmas (lower L-theory model, module 16)

Auxiliary results for `Model/LiftingPair.lean`, for a Karoubi filtration `F : U ⊂ A`.

* `exists_quotPoincare_of_supportedIn`: `exists_quotPoincare` (LiftComplex) for free complexes
  concentrated in `[lo, M]` (`0 ≤ lo`), with the lift's idempotent the degree truncation.
* `SymPair.transportBdRelHomotopy`: for `SymPair.transportBd` along `e`, `c^* Ψ' ≃ Ψ` with
  `c = g ⊕ p_D : Cone(g j) ⟶ Cone(j)` (`transportRelDualityHomotopy`).
* `InvFunctor.mapDual_*`, `mapDualHomotopy`; `SymPair.mapDual_Ψ_eq`: in `A/U` the relative duality
  map of a pair with boundary in `U` is `[inr]^* ∘ (toQuot).φ`.
* `SymComplex.bdTransport` (with `bdTBd`, `bdTδφ`, `bdTRelHomotopy`): **Ranicki's boundary pair
  `(∂C ⟶ C^{N+1-*}, (0, ∂φ))` transported along any Kar equivalence `e : (∂C, p_∂) ≃ (C', p')`**
  with `(C', p')` in `[0, N]`, as a `SymPair`; unlike `boundaryPair` it only needs `C` in
  `[0, N+1]` (`∂C` itself lives in `[-1, N+1]`).  The proofs follow `SymPair.transportBd`
  (Transport) with the boundary pair's data.
* `SymComplex.exists_trunc` (`exists_truncLo`, `exists_truncHi`): if the bottom differential of
  `∂C` splits (`p₀ (a φ₀ + b d) p₀ = p₀`), then `(∂C, p_∂)` is Kar-equivalent to `(∂C, q)` with
  `q` concentrated in `[0, N]`: an explicit homotopy `s₀ : Cone(φ)_0 ⟶ Cone(φ)_1` cuts the bottom
  (`truncLo`), and Poincaré duality of `∂φ` with `KarHtpyEquiv.trunc` cuts the top.
* `QuotPoincare.flat`, `exists_flat`: **compression of degree `0` of a lift** by `1 - ε`
  (`ε ∈ I_U` idempotent): `C♭ = (C, p d q)`, `φ♭ = τ φ τ^*` for the chain map `τ = q`; its image is
  strictly isometric to that of `L` (`flatIso`), and for `ε` killing the lifted Poincaré defect
  `u = ψ̃ φ₀ - h̃ d - 1` the bottom of `∂C♭` splits.
* `ContractibleMod.of_karHtpyEquiv`, `SymComplex.exists_sub_of_trunc`: the truncated boundary has a
  Kar(U) model (domination + BS01, `SymPoincare.exists_sub`).
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression
  homotopyCofiber LiftComplex

noncomputable section

attribute [local implicit_reducible] SymPair.map

namespace KaroubiFiltration

variable {A : InvCat} {F : KaroubiFiltration A}

/-! ### Lifts concentrated in `[lo, M]` -/

/-- **Honest strict lift of a free Poincaré complex concentrated in `[lo, M]`** (the variant of
`exists_quotPoincare` with a lower bound `lo ≥ 0`): if `P.p = 1` on `[lo, M]` and `0` outside,
`P` is strictly isometric to the image of a `QuotPoincare` whose idempotent is the degree
truncation onto `[lo, M]`. -/
theorem exists_quotPoincare_of_supportedIn {M : ℤ} (lo : ℤ) (hlo : 0 ≤ lo)
    (P : SymPoincare F.quot.inv M) (hp : ∀ r, lo ≤ r → r ≤ M → P.p.f r = 𝟙 _)
    (hs : SupportedIn P.p lo M) :
    ∃ L : F.QuotPoincare M, SupportedIn L.p lo M ∧ (∀ r, lo ≤ r → r ≤ M → L.p.f r = 𝟙 _) ∧
      Nonempty (SymPoincare.HomotopyIsometry L.toQuot P) := by
  have hp0 : ∀ r, ¬ (lo ≤ r ∧ r ≤ M) → P.p.f r = 0 := fun r h ↦ hs r (by omega)
  obtain ⟨C'', φ'', e, hsym, hconj, hd, hφ0⟩ := F.exists_strictLift (karTrunc P.p P.p_idem)
    (dualHom F.quot.inv M (karTruncTo P.p P.p_idem) ≫ P.φ ≫ karTruncTo P.p P.p_idem)
    (P.symm.conj (karTruncTo P.p P.p_idem)) M
    (fun i k h ↦ by rw [karTrunc_d, hp0 i (by omega), zero_comp])
  have hd' : ∀ i k, ¬ (lo ≤ i ∧ i ≤ M ∧ lo ≤ k ∧ k ≤ M) → C''.d i k = 0 := fun i k h ↦ hd i k (by
    rw [karTrunc_d]
    by_cases hi : lo ≤ i ∧ i ≤ M
    · rw [P.p.comm, hp0 k (by omega), comp_zero]
    · rw [hp0 i hi, zero_comp])
  set τ := degTrunc C'' lo M hd'
  have hkar : dualHom A.inv M τ ≫ φ'' ≫ τ = φ'' := by
    ext r
    simp only [comp_f, dualHom_f]
    by_cases h : (lo ≤ r ∧ r ≤ M) ∧ (lo ≤ M - r ∧ M - r ≤ M)
    · rw [degTrunc_f_of_mem hd' h.1, degTrunc_f_of_mem hd' h.2]
      erw [A.inv.star_id]
      rw [id_comp, comp_id]
    · rw [hφ0 r, zero_comp, comp_zero]
      simp only [comp_f, dualHom_f, karTruncTo_f]
      rcases not_and_or.mp h with h | h
      · rw [hp0 r h, comp_zero, comp_zero]
      · rw [hp0 (M - r) h, StrictInvolution.star_zero, zero_comp]
  have hτ : ∀ r, F.proj.F.map (τ.f r) = if lo ≤ r ∧ r ≤ M then 𝟙 _ else 0 := fun r ↦ by
    by_cases h : lo ≤ r ∧ r ≤ M
    · rw [degTrunc_f_of_mem hd' h, if_pos h, CategoryTheory.Functor.map_id]
    · rw [degTrunc_f_of_not_mem hd' h, if_neg h, Functor.map_zero]
  have hfg : (e.hom ≫ karTruncFrom P.p P.p_idem) ≫ karTruncTo P.p P.p_idem ≫ e.inv =
      F.projF.mapH τ := by
    ext r
    simp only [comp_f, karTruncFrom_f, karTruncTo_f, InvFunctor.mapH,
      Functor.mapHomologicalComplex_map_f, hτ]
    split_ifs with h
    · rw [hp r h.1 h.2]; erw [comp_id, id_comp]; exact iso_hom_inv_f e r
    · rw [hp0 r h]; simp
  have hgf : (karTruncTo P.p P.p_idem ≫ e.inv) ≫ e.hom ≫ karTruncFrom P.p P.p_idem = P.p := by
    ext r; simp
  have hpf : F.projF.mapH τ ≫ e.hom ≫ karTruncFrom P.p P.p_idem =
      e.hom ≫ karTruncFrom P.p P.p_idem := by
    ext r
    simp only [comp_f, karTruncFrom_f, InvFunctor.mapH, Functor.mapHomologicalComplex_map_f, hτ]
    split_ifs with h
    · erw [id_comp]
    · rw [hp0 r h]; simp
  have hgp : P.p ≫ karTruncTo P.p P.p_idem ≫ e.inv = karTruncTo P.p P.p_idem ≫ e.inv := by
    ext r; simp [reassoc_of% f_idem P.p P.p_idem]
  have hconj' : dualHom F.quot.inv M (e.hom ≫ karTruncFrom P.p P.p_idem) ≫
      F.projF.mapDual φ'' ≫ e.hom ≫ karTruncFrom P.p P.p_idem = P.φ := by
    rw [dualHom_comp]
    simp only [assoc]
    rw [reassoc_of% hconj, karTruncTo_comp_from, ← assoc (dualHom _ M (karTruncFrom P.p P.p_idem)),
      ← dualHom_comp, karTruncTo_comp_from, P.φ_kar]
  let L : F.QuotPoincare M :=
    { C := C''
      p := τ
      p_idem := degTrunc_idem hd'
      support := (supportedIn_degTrunc hd').mono hlo le_rfl
      φ := φ''
      φ_kar := hkar
      symm := hsym
      poincare := isPoincare_of_strict P (F.projF.mapDual_kar hkar) _ _ hfg hgf hpf hconj' }
  exact ⟨L, supportedIn_degTrunc hd', fun r h h' ↦ degTrunc_f_of_mem hd' ⟨h, h'⟩,
    ⟨strictIsometry (Q := L.toQuot) _ _ hfg hgf hpf hgp hconj'⟩⟩

end KaroubiFiltration

/-! ### Relative duality of a transported pair -/

namespace SymPair

section TransportBdRel

variable {V : Type*} [Category V] [Preadditive V] [Linear ℚ V] [HasFiniteBiproducts V]
  [HasBinaryBiproducts V] {J : StrictInvolution V} {N : ℤ} (X : SymPair J N)
  {C' : ChainComplex V ℤ} {p' : C' ⟶ C'} (e : KarHtpyEquiv X.bd.p p')

/-- The cone map `g ⊕ p_D : Cone(g j) ⟶ Cone(j)` of a boundary transport. -/
abbrev transportBdCone : cone (e.g ≫ X.j) ⟶ cone X.j :=
  coneMap e.g X.pD (by simp : e.g ≫ X.j = (e.g ≫ X.j) ≫ X.pD)

/-- **`c^* Ψ' ≃ Ψ`** for the transport `X'` of `X` along a boundary equivalence `e`
(`c = g ⊕ p_D`): the relative duality maps agree up to the homotopy of
`transportRelDualityHomotopy`. -/
def transportBdRelHomotopy (hp' : p' ≫ p' = p') (hs : SupportedIn p' 0 N) :
    Homotopy (dualHom J (N + 1) (X.transportBdCone e) ≫ (X.transportBd e hp' hs).Ψ) X.Ψ := by
  have hl (r r' : ℤ) : (dualHom J N X.pD).f r ≫ (X.transportBdδφ e).hom r r' =
      (X.transportBdδφ e).hom r r' := by
    conv_lhs => rw [← X.transportBdδφ_kar e]
    rw [← assoc, ← comp_f, ← dualHom_comp, X.pD_idem, X.transportBdδφ_kar]
  have hid : dualHom J (N + 1) (X.transportBdCone e) ≫ relDuality (X.transportBdδφ e) =
      relDuality (X.transportBdδφ₀ e) := by
    ext r
    simp [star_coneMap_f (by simp : e.g ≫ X.j = (e.g ≫ X.j) ≫ X.pD) _ _ (down_rel_sub N r),
      star_comp_relTop _ hl]
    rfl
  exact (Homotopy.ofEq hid).trans
    (transportRelDualityHomotopy (X.bdW e) (X.transportBdδφ₀ e) X.δφ fun _ _ ↦ rfl)

end TransportBdRel

@[reassoc (attr := simp)]
lemma inr_comp_transportBdCone {V : Type*} [Category V] [Preadditive V] [HasBinaryBiproducts V]
    {J : StrictInvolution V} {N : ℤ} (X : SymPair J N) {C' : ChainComplex V ℤ} {p' : C' ⟶ C'}
    (e : KarHtpyEquiv X.bd.p p') : inr (e.g ≫ X.j) ≫ X.transportBdCone e = X.pD ≫ inr X.j := by
  ext i; simp

end SymPair

/-! ### Duality-preserving functors and `mapDual` -/

namespace InvFunctor

variable {V W : Type*} [Category V] [Preadditive V] [Category W] [Preadditive W]
  {J : StrictInvolution V} {J' : StrictInvolution W} (Φ : InvFunctor J J') {N : ℤ}

lemma mapDual_dualHom_comp {C C' D : ChainComplex V ℤ} (g : C ⟶ C')
    (ψ : dualComplex J N C ⟶ D) :
    Φ.mapDual (dualHom J N g ≫ ψ) = dualHom J' N (Φ.mapH g) ≫ Φ.mapDual ψ := by
  ext r; simp [Φ.map_star]

lemma mapDual_comp {C D D' : ChainComplex V ℤ} (ψ : dualComplex J N C ⟶ D) (g : D ⟶ D') :
    Φ.mapDual (ψ ≫ g) = Φ.mapDual ψ ≫ Φ.mapH g := by
  ext r; simp

lemma mapDual_units_smul {C D : ChainComplex V ℤ} (u : ℤˣ) (ψ : dualComplex J N C ⟶ D) :
    Φ.mapDual (u • ψ) = u • Φ.mapDual ψ := by
  ext r; simp

lemma mapDual_neg {C D : ChainComplex V ℤ} (ψ : dualComplex J N C ⟶ D) :
    Φ.mapDual (-ψ) = -Φ.mapDual ψ := by
  ext r; simp

/-- `Φ.mapDual` respects homotopies. -/
def mapDualHomotopy {C D : ChainComplex V ℤ} {ψ ψ' : dualComplex J N C ⟶ D}
    (H : Homotopy ψ ψ') : Homotopy (Φ.mapDual ψ) (Φ.mapDual ψ') :=
  homotopyCongr ((Φ.F.mapHomotopy H).compLeft (Φ.mapDualIso N C).inv) (Φ.mapDual_eq ψ).symm
    (Φ.mapDual_eq ψ').symm

end InvFunctor

namespace SymPair

variable {A : InvCat} (F : KaroubiFiltration A) {N : ℤ}

/-- In `A/U` the relative duality map of a pair with boundary in `U` factors through the top
structure of `toQuot`: `[Ψ] = [inr]^* ∘ (toQuot).φ`. -/
lemma mapDual_Ψ_eq (X : SymPair A.inv N) (hU : ∀ r, F.U (X.bd.C.X r)) :
    F.projF.mapDual X.Ψ =
      dualHom F.quot.inv (N + 1) (F.projF.mapH (inr X.j)) ≫ (X.toQuot F hU).φ := by
  have hZ : ∀ r, IsZero ((X.map F.projF).bd.C.X r) := fun r ↦ F.isZero_proj_obj (hU r)
  rw [← F.projF.dualHom_coneComparison_comp_relDuality X.δφ]
  have h2 := (X.map F.projF).relDuality_eq_of_isZero hZ
  rw [show relDuality (F.projF.mapRel X.δφ) = relDuality (X.map F.projF).δφ from rfl, h2,
    ← assoc, ← dualHom_comp]
  congr 2
  ext i; simp
  exact F.projF.inrX_coneComparison_f X.j i

end SymPair

/-- A Kar equivalence `f` carrying `φ_P` to `φ_Q` up to homotopy is a homotopy isometry. -/
lemma SymPoincare.HomotopyIsometry.nonempty_of_conj {V : Type*} [Category V] [Preadditive V]
    {J : StrictInvolution V} {M : ℤ} {P Q : SymPoincare J M} (f : P.C ⟶ Q.C)
    (hf : P.p ≫ f ≫ Q.p = f) (he : IsKarEquiv P.p Q.p f)
    (H : Homotopy (dualHom J M f ≫ P.φ ≫ f) Q.φ) :
    Nonempty (SymPoincare.HomotopyIsometry P Q) := by
  obtain ⟨g, hg, ⟨H₁⟩, ⟨H₂⟩⟩ := he
  exact ⟨⟨f, g, hf, hg, H₂, H₁, H⟩⟩

namespace SymComplex

variable {V : Type*} [Category V] [Preadditive V] [HasBinaryBiproducts V]
  {J : StrictInvolution V} {N : ℤ} (X : SymComplex J (N + 1))

/-- `π ∘ inr = -φ` on `Cone(j)`, `j : ∂C ⟶ C^{N+1-*}`. -/
@[reassoc (attr := simp)]
lemma inr_comp_coneπ : inr X.bdJ ≫ X.coneπ = -X.φ := by
  ext s; simp

end SymComplex

/-- A homotopy isometry from an equality. -/
def SymPoincare.HomotopyIsometry.ofEq' {V : Type*} [Category V] [Preadditive V]
    {J : StrictInvolution V} {M : ℤ} {P Q : SymPoincare J M} (h : P = Q) :
    SymPoincare.HomotopyIsometry P Q :=
  h ▸ .refl P


/-! ### Transport of Ranicki's boundary pair without support hypotheses -/

namespace SymComplex

@[reassoc (attr := simp)]
lemma bdJ_comp_dualHom_p {V : Type*} [Category V] [Preadditive V] [HasBinaryBiproducts V]
    {J : StrictInvolution V} {N : ℤ} (X : SymComplex J (N + 1)) :
    X.bdJ ≫ dualHom J (N + 1) X.p = X.bdJ := by
  conv_lhs => rw [← X.bdJ_kar]
  rw [assoc, assoc, X.dualHom_p_idem, X.bdJ_kar]

section BdTransport

variable {V : Type*} [Category V] [Preadditive V] [Linear ℚ V] [HasFiniteBiproducts V]
  [HasBinaryBiproducts V] {J : StrictInvolution V} {N : ℤ} (X : SymComplex J (N + 1))
  {C' : ChainComplex V ℤ} {p' : C' ⟶ C'} (e : KarHtpyEquiv X.bdP p')

/-- The Kar homotopy `(gf) ∂φ (gf)^* ≃ ∂φ` on `∂C`, before symmetrization. -/
def bdTW₀ : Homotopy (dualHom J N (e.f ≫ e.g) ≫ X.bdφ ≫ e.f ≫ e.g) X.bdφ :=
  karHomotopy (p := dualHom J N X.bdP) (q := X.bdP)
    (homotopyCongr (conjHomotopy e.fg (Homotopy.refl X.bdφ)) rfl X.bdφ_kar)
    (by simp only [assoc, e.gp]; rw [← assoc (dualHom J N X.bdP), ← dualHom_comp, assoc, e.gp])
    X.bdφ_kar

omit [Linear ℚ V] [HasFiniteBiproducts V] in
lemma bdTW₀_kar (r r' : ℤ) : (dualHom J N X.bdP).f r ≫ (X.bdTW₀ e).hom r r' ≫ X.bdP.f r' =
    (X.bdTW₀ e).hom r r' := by
  have h₁ : X.bdP.f r' ≫ X.bdP.f r' = X.bdP.f r' := idem_f X.bdP_idem r'
  have h₂ : (dualHom J N X.bdP).f r ≫ (dualHom J N X.bdP).f r = (dualHom J N X.bdP).f r :=
    idem_f (dualHom_idem X.bdP_idem) r
  have e₀ : (X.bdTW₀ e).hom r r' = (dualHom J N X.bdP).f r ≫
      (conjHomotopy e.fg (Homotopy.refl X.bdφ)).hom r r' ≫ X.bdP.f r' := rfl
  rw [e₀, assoc, assoc, h₁, ← assoc, h₂]

/-- The symmetrized Kar homotopy `W : (gf) ∂φ (gf)^* ≃ ∂φ`. -/
def bdTW : Homotopy (dualHom J N (e.f ≫ e.g) ≫ X.bdφ ≫ e.f ≫ e.g) X.bdφ :=
  symmHomotopy (X.bdφ_symm.conj _) X.bdφ_symm (X.bdTW₀ e)

omit [HasFiniteBiproducts V] in
lemma bdTW_kar (r r' : ℤ) : (dualHom J N X.bdP).f r ≫ (X.bdTW e).hom r r' ≫ X.bdP.f r' =
    (X.bdTW e).hom r r' :=
  kar_symmHomotopy_hom X.bdP_idem _ _ _ (X.bdTW₀_kar e) r r'

/-- The relative structure `j W j^* + 0` on `j : ∂C ⟶ C^{N+1-*}` for `(gf) ∂φ (gf)^*`. -/
def bdTδφ₀ :
    Homotopy (dualHom J N X.bdJ ≫ (dualHom J N (e.f ≫ e.g) ≫ X.bdφ ≫ e.f ≫ e.g) ≫ X.bdJ) 0 :=
  (((X.bdTW e).compRight X.bdJ).compLeft (dualHom J N X.bdJ)).trans X.bdRel

/-- The relative structure of the transported pair, on `j' = g j`. -/
def bdTδφ : Homotopy (dualHom J N (e.g ≫ X.bdJ) ≫ (dualHom J N e.f ≫ X.bdφ ≫ e.f) ≫
    e.g ≫ X.bdJ) 0 :=
  homotopyCongr (X.bdTδφ₀ e) (by simp) rfl

omit [HasFiniteBiproducts V] in
lemma bdTδφ_hom : (X.bdTδφ e).hom =
    (fun r r' ↦ (dualHom J N X.bdJ).f r ≫ (X.bdTW e).hom r r' ≫ X.bdJ.f r') + X.bdRel.hom :=
  rfl

omit [HasFiniteBiproducts V] in
lemma bdTδφ_kar (r r' : ℤ) : (dualHom J N (dualHom J (N + 1) X.p)).f r ≫ (X.bdTδφ e).hom r r' ≫
    (dualHom J (N + 1) X.p).f r' = (X.bdTδφ e).hom r r' := by
  have hj : X.bdJ ≫ dualHom J (N + 1) X.p = X.bdJ := X.bdJ_comp_dualHom_p
  have h₁ : (dualHom J N (dualHom J (N + 1) X.p)).f r ≫ (dualHom J N X.bdJ).f r =
      (dualHom J N X.bdJ).f r := by
    rw [← comp_f, ← dualHom_comp, hj]
  have h₂ : X.bdJ.f r' ≫ (dualHom J (N + 1) X.p).f r' = X.bdJ.f r' := by rw [← comp_f, hj]
  simp only [bdTδφ_hom, Pi.add_apply, comp_add, add_comp, assoc, h₂, reassoc_of% h₁]
  simp [bdRel, Homotopy.ofEq]

omit [HasFiniteBiproducts V] in
lemma isSymmHomotopy_bdTδφ : IsSymmHomotopy J N (X.bdTδφ e) := by
  have hR : transposeHomFamily J N X.bdRel.hom = X.bdRel.hom := by
    funext r r'; simp [bdRel, Homotopy.ofEq, transposeHomFamily]
  rw [IsSymmHomotopy, transposeHomotopy_hom, bdTδφ_hom, transposeHomFamily_add,
    transposeHomFamily_conj', transposeHomFamily_eq (show IsSymmHomotopy J N (X.bdTW e) from
      isSymmHomotopy_symmHomotopy _ _ _), hR]

/-- The cone map `g ⊕ p^* : Cone(g j) ⟶ Cone(j)`. -/
abbrev bdTCone : cone (e.g ≫ X.bdJ) ⟶ cone X.bdJ :=
  coneMap e.g (dualHom J (N + 1) X.p)
    (by rw [assoc, ← X.bdP_comp_bdJ, e.gp_assoc] : e.g ≫ X.bdJ = (e.g ≫ X.bdJ) ≫ _)

omit [Linear ℚ V] [HasFiniteBiproducts V] in
@[reassoc (attr := simp)]
lemma inr_comp_bdTCone : inr (e.g ≫ X.bdJ) ≫ X.bdTCone e = dualHom J (N + 1) X.p ≫ inr X.bdJ := by
  ext i; simp

omit [HasFiniteBiproducts V] in
lemma relDuality_bdTδφ_eq :
    dualHom J (N + 1) (X.bdTCone e) ≫ relDuality (X.bdTδφ e) = relDuality (X.bdTδφ₀ e) := by
  have hl (r r' : ℤ) : (dualHom J N (dualHom J (N + 1) X.p)).f r ≫ (X.bdTδφ e).hom r r' =
      (X.bdTδφ e).hom r r' := by
    conv_lhs => rw [← X.bdTδφ_kar e]
    rw [← assoc, ← comp_f, ← dualHom_comp, X.dualHom_p_idem, X.bdTδφ_kar]
  have hT (r : ℤ) : X.p.f (N + 1 - (N + 1 - r)) ≫ relTop (X.bdTδφ e) r = relTop (X.bdTδφ e) r := by
    simpa using star_comp_relTop (X.bdTδφ e) hl r
  ext r
  simp [star_coneMap_f (by rw [assoc, ← X.bdP_comp_bdJ, e.gp_assoc] :
      e.g ≫ X.bdJ = (e.g ≫ X.bdJ) ≫ dualHom J (N + 1) X.p) _ _ (down_rel_sub N r), hT]
  rfl

/-- **`c^* Ψ' ≃ Ψ`** for the transported boundary pair. -/
def bdTRelHomotopy :
    Homotopy (dualHom J (N + 1) (X.bdTCone e) ≫ relDuality (X.bdTδφ e)) (relDuality X.bdRel) :=
  (Homotopy.ofEq (X.relDuality_bdTδφ_eq e)).trans
    (transportRelDualityHomotopy (X.bdTW e) (X.bdTδφ₀ e) X.bdRel fun _ _ ↦ rfl)

lemma isKarEquiv_bdT (hp' : p' ≫ p' = p') :
    IsKarEquiv (dualHom J (N + 1) (coneMap p' (dualHom J (N + 1) X.p)
      (comm_of_kar hp' X.dualHom_p_idem (by simp :
        p' ≫ (e.g ≫ X.bdJ) ≫ dualHom J (N + 1) X.p = e.g ≫ X.bdJ))))
      (dualHom J (N + 1) X.p) (relDuality (X.bdTδφ e)) := by
  have hj : p' ≫ (e.g ≫ X.bdJ) ≫ dualHom J (N + 1) X.p = e.g ≫ X.bdJ := by simp
  have hc : e.g ≫ X.bdJ = (e.g ≫ X.bdJ) ≫ dualHom J (N + 1) X.p := by simp
  have hC := isKarEquiv_coneMap hp' X.dualHom_p_idem X.bdP_idem X.dualHom_p_idem hj X.bdJ_kar
    e.g_kar (by simp) hc e.symm.isKarEquiv (KarHtpyEquiv.refl X.dualHom_p_idem).isKarEquiv
  have hl (r r' : ℤ) : (dualHom J N (dualHom J (N + 1) X.p)).f r ≫ (X.bdTδφ e).hom r r' =
      (X.bdTδφ e).hom r r' := by
    conv_lhs => rw [← X.bdTδφ_kar e]
    rw [← assoc, ← comp_f, ← dualHom_comp, X.dualHom_p_idem, X.bdTδφ_kar]
  have hr (r r' : ℤ) : (X.bdTδφ e).hom r r' ≫ (dualHom J (N + 1) X.p).f r' =
      (X.bdTδφ e).hom r r' := by
    conv_lhs => rw [← X.bdTδφ_kar e]
    rw [assoc, assoc, ← comp_f, X.dualHom_p_idem, X.bdTδφ_kar]
  have hΨ := X.isKarEquiv_relDuality.of_homotopy (homotopyCongr (transportRelDualityHomotopy
    (X.bdTW e) (X.bdTδφ₀ e) X.bdRel fun _ _ ↦ rfl).symm rfl (X.relDuality_bdTδφ_eq e).symm)
  refine IsKarEquiv.of_comp_left hC.dualHom (dualHom_kar ?_) hΨ ?_
    (dualHom_idem (coneMap_idem _ X.bdP_idem X.dualHom_p_idem))
    (dualHom_idem (coneMap_idem _ hp' X.dualHom_p_idem)) X.dualHom_p_idem
  · rw [coneMap_comp, coneMap_comp]; congr 1 <;> simp
  · have hφ' : dualHom J N p' ≫ (dualHom J N e.f ≫ X.bdφ ≫ e.f) =
        dualHom J N e.f ≫ X.bdφ ≫ e.f := by rw [← assoc, ← dualHom_comp, e.fp]
    rw [← assoc, dualHom_coneMap_comp_relDuality _ _ hφ' hl, relDuality_comp_pD (by simp) _ hr]

/-- The transported boundary `(C', p', f ∂φ f^*)` of `∂C`, an `N`-dimensional Poincaré
complex (no support hypothesis on `C`). -/
@[simps, implicit_reducible]
def bdTBd (hp' : p' ≫ p' = p') (hs : SupportedIn p' 0 N) : SymPoincare J N where
  C := C'
  p := p'
  p_idem := hp'
  support := hs
  φ := dualHom J N e.f ≫ X.bdφ ≫ e.f
  φ_kar := by simp only [assoc, e.fp]; rw [← assoc, ← dualHom_comp, e.fp]
  symm := X.bdφ_symm.conj e.f
  poincare := (e.dual J N).isKarEquiv.comp (IsKarEquiv.comp X.bdφ_poincare e.isKarEquiv
    (dualHom_idem X.bdP_idem) X.bdP_idem hp') (dualHom_idem hp') (dualHom_idem X.bdP_idem) hp'

/-- **Ranicki's boundary pair transported along `e : (∂C, p_∂) ≃ (C', p')`**:
`(g j : C' ⟶ C^{N+1-*}, (j W j^*, f ∂φ f^*))`.  Unlike `boundaryPair` (which needs `C` in
`[1, N+1]` so that `∂C` lies in `[0, N]`), only the target `(C', p')` of `e` must lie in
`[0, N]`; `C` may live in `[0, N+1]` (then `∂C` lives in `[-1, N+1]`). -/
@[simps, implicit_reducible]
def bdTransport (hp' : p' ≫ p' = p') (hs : SupportedIn p' 0 N) (hX : SupportedIn X.p 0 (N + 1)) :
    SymPair J N where
  bd := X.bdTBd e hp' hs
  D := dualComplex J (N + 1) X.C
  pD := dualHom J (N + 1) X.p
  pD_idem := X.dualHom_p_idem
  support := (hX.dualHom (J := J) (N := N + 1)).mono (by omega) (by omega)
  j := e.g ≫ X.bdJ
  j_kar := by simp
  δφ := X.bdTδφ e
  δφ_kar := X.bdTδφ_kar e
  symm := X.isSymmHomotopy_bdTδφ e
  poincare := X.isKarEquiv_bdT e hp'

end BdTransport

/-! ### Truncating `∂C` to `[0, N]` -/

section Trunc

variable {V : Type*} [Category V] [Preadditive V] [HasBinaryBiproducts V]
  {J : StrictInvolution V} {N : ℤ} (X : SymComplex J (N + 1))

/-- The idempotent `p^* ⊕ p` of `Cone(φ)`; `bdP = Σ⁻¹ coneP`. -/
abbrev coneP : cone X.φ ⟶ cone X.φ := coneMap (dualHom J (N + 1) X.p) X.p X.comm

lemma coneP_idem : X.coneP ≫ X.coneP = X.coneP := coneMap_idem _ X.dualHom_p_idem X.p_idem

lemma bdP_eq : X.bdP = desuspMap X.coneP := rfl

variable (a : X.C.X 0 ⟶ (dualComplex J (N + 1) X.C).X 0) (b : X.C.X 0 ⟶ X.C.X 1)

/-- The bottom contraction `s₀ = (p^* ⊕ p)(a, b)π_C (p^* ⊕ p) : Cone(φ)_0 ⟶ Cone(φ)_1`. -/
def botS : (cone X.φ).X 0 ⟶ (cone X.φ).X 1 :=
  X.coneP.f 0 ≫ sndX X.φ 0 ≫ (a ≫ inlX X.φ 0 1 (by simp) + b ≫ inrX X.φ 1) ≫ X.coneP.f 1

lemma coneP_f_eq_zero (hX : SupportedIn X.p 0 (N + 1)) {k : ℤ} (hk : k < 0) :
    X.coneP.f k = 0 := by
  rw [coneMap_f _ k (k - 1) (by simp)]
  simp [hX k (by omega), hX (N + 1 - (k - 1)) (by omega)]

lemma botS_kar : X.coneP.f 0 ≫ X.botS a b ≫ X.coneP.f 1 = X.botS a b := by
  simp only [botS, ← assoc, ← comp_f, X.coneP_idem]
  simp only [assoc, ← comp_f, X.coneP_idem]

lemma botS_d (hX : SupportedIn X.p 0 (N + 1))
    (hab : X.p.f 0 ≫ (a ≫ X.φ.f 0 + b ≫ X.C.d 1 0) ≫ X.p.f 0 = X.p.f 0) :
    X.botS a b ≫ (cone X.φ).d 1 0 = X.coneP.f 0 := by
  have h1 : X.coneP.f 1 ≫ (cone X.φ).d 1 0 = (cone X.φ).d 1 0 ≫ X.coneP.f 0 := X.coneP.comm 1 0
  have hinl : inlX X.φ (-1) 0 (by simp) ≫ X.coneP.f 0 = 0 := by
    rw [inlX_coneMap_f _ 0 (-1) (by simp)]
    simp [hX (N + 1 - (-1)) (by omega)]
  have hd : (a ≫ inlX X.φ 0 1 (by simp) + b ≫ inrX X.φ 1) ≫ (cone X.φ).d 1 0 ≫ X.coneP.f 0 =
      (a ≫ X.φ.f 0 + b ≫ X.C.d 1 0) ≫ X.p.f 0 ≫ inrX X.φ 0 := by
    rw [homotopyCofiber_d, add_comp, assoc, assoc, inlX_d_assoc X.φ 1 0 (-1) (by simp) (by simp),
      inrX_d_assoc]
    simp [hinl]
  rw [botS, assoc, assoc, assoc, h1, hd, ← assoc (X.coneP.f 0), coneMap_f_sndX,
    assoc, reassoc_of% hab, coneMap_f _ 0 (-1) (by simp)]
  simp [hX (N + 1 - (-1)) (by omega)]

/-- The homotopy family supported in degrees `0 ⟶ 1`, given by `-s₀`. -/
def botFam (i j : ℤ) (_ : (ComplexShape.down ℤ).Rel j i) : (cone X.φ).X i ⟶ (cone X.φ).X j :=
  if h : i = 0 then ((cone X.φ).XIsoOfEq h).hom ≫ (-X.botS a b) ≫
    ((cone X.φ).XIsoOfEq (by simp at *; omega : (1 : ℤ) = j)).hom else 0

lemma botFam_zero : X.botFam a b 0 1 (by simp) = -X.botS a b := by
  simp [botFam]

lemma botFam_ne {i j : ℤ} (h : (ComplexShape.down ℤ).Rel j i) (hi : i ≠ 0) :
    X.botFam a b i j h = 0 := by
  simp [botFam, hi]

/-- `x = coneP - (d s₀ + s₀ d)`, homotopic to `coneP` and vanishing in degree `0`. -/
@[implicit_reducible]
def botX : cone X.φ ⟶ cone X.φ := Homotopy.nullHomotopicMap' (X.botFam a b) + X.coneP

/-- The homotopy `x ≃ coneP`. -/
def botHomotopy : Homotopy (X.botX a b) X.coneP :=
  homotopyCongr ((Homotopy.nullHomotopy' (X.botFam a b)).add (Homotopy.refl X.coneP)) rfl
    (zero_add _)

lemma botX_f_zero (hX : SupportedIn X.p 0 (N + 1))
    (hab : X.p.f 0 ≫ (a ≫ X.φ.f 0 + b ≫ X.C.d 1 0) ≫ X.p.f 0 = X.p.f 0) :
    (X.botX a b).f 0 = 0 := by
  rw [botX, add_f_apply, Homotopy.nullHomotopicMap'_f (show (ComplexShape.down ℤ).Rel 1 0 by simp)
    (show (ComplexShape.down ℤ).Rel 0 (-1) by simp), X.botFam_ne a b _ (by omega : (-1 : ℤ) ≠ 0),
    botFam_zero, comp_zero, zero_add, neg_comp, X.botS_d a b hX hab, neg_add_cancel]

lemma botX_f_neg (hX : SupportedIn X.p 0 (N + 1)) {k : ℤ} (hk : k < 0) : (X.botX a b).f k = 0 := by
  rw [botX, add_f_apply, Homotopy.nullHomotopicMap'_f (show (ComplexShape.down ℤ).Rel (k + 1) k by
    simp) (show (ComplexShape.down ℤ).Rel k (k - 1) by simp), X.botFam_ne a b _ (by omega),
    X.botFam_ne a b _ (by omega), X.coneP_f_eq_zero hX hk]
  simp

lemma botHomotopy_hom (i j : ℤ) : (X.botHomotopy a b).hom i j =
    if h : i + 1 = j then X.botFam a b i j h else 0 := by
  by_cases h : i + 1 = j <;> simp [botHomotopy, Homotopy.nullHomotopy'_hom, h]

lemma botHomotopy_kar (i j : ℤ) :
    X.coneP.f i ≫ (X.botHomotopy a b).hom i j ≫ X.coneP.f j = (X.botHomotopy a b).hom i j := by
  rw [botHomotopy_hom]
  split_ifs with h
  · by_cases hi : i = 0
    · subst hi
      obtain rfl : j = 1 := by simp at h; omega
      rw [botFam_zero]
      simp only [comp_neg, neg_comp, X.botS_kar]
    · rw [X.botFam_ne a b h hi]; simp
  · simp

/-- **Bottom truncation**: if `p (a φ + b d) p = p` in degree `0` (the bottom differential of
`∂C` is split, "connectivity"), then `(∂C, p_∂)` is Kar-equivalent to `(∂C, q)` with `q`
concentrated in `[0, N+1]`. -/
theorem exists_truncLo (hX : SupportedIn X.p 0 (N + 1))
    (hab : X.p.f 0 ≫ (a ≫ X.φ.f 0 + b ≫ X.C.d 1 0) ≫ X.p.f 0 = X.p.f 0) :
    ∃ q : X.bdC ⟶ X.bdC, q ≫ q = q ∧ SupportedIn q 0 (N + 1) ∧ Nonempty (KarHtpyEquiv X.bdP q) := by
  let H : Homotopy (desuspMap (X.botX a b)) X.bdP := desuspHomotopy (X.botHomotopy a b)
  have hH : ∀ i j, X.bdP.f i ≫ H.hom i j ≫ X.bdP.f j = H.hom i j := fun i j ↦ by
    show X.coneP.f (i + 1) ≫ (-(X.botHomotopy a b).hom (i + 1) (j + 1)) ≫ X.coneP.f (j + 1) =
      -(X.botHomotopy a b).hom (i + 1) (j + 1)
    rw [neg_comp, comp_neg, X.botHomotopy_kar]
  have hx : ∀ r, r < 0 → (desuspMap (X.botX a b)).f r = 0 := fun r hr ↦ by
    show (X.botX a b).f (r + 1) = 0
    rcases lt_or_eq_of_le (show r + 1 ≤ 0 by omega) with h | h
    · exact X.botX_f_neg a b hX h
    · rw [h]; exact X.botX_f_zero a b hX hab
  refine ⟨truncLo H 0, truncLo_idem X.bdP_idem hH hx, fun r hr ↦ ?_,
    ⟨truncLoEquiv X.bdP_idem hH hx⟩⟩
  rcases hr with hr | hr
  · exact truncLo_f_below H (hx r hr) hr
  · rw [← truncLo_comp_p X.bdP_idem hH hx, comp_f]
    have : X.bdP.f r = 0 := by
      show X.coneP.f (r + 1) = 0
      rw [coneMap_f _ (r + 1) r (by simp)]
      simp [hX (r + 1) (by omega), hX (N + 1 - r) (by omega)]
    rw [this, comp_zero]

/-- **Top truncation by duality**: a Kar complex `(∂C, q₁)` Kar-equivalent to `(∂C, p_∂)` and
concentrated in `[0, N+1]` is Kar-equivalent to a sub-idempotent `q ≤ q₁` concentrated in
`[0, N]`, since `∂φ` makes `(∂C, q₁)` equivalent to its dual `(∂C^{N-*}, q₁^*)`, which lives in
`[-1, N]` (`KarHtpyEquiv.trunc`). -/
theorem exists_truncHi {q₁ : X.bdC ⟶ X.bdC} (e₁ : KarHtpyEquiv X.bdP q₁) (hq₁ : q₁ ≫ q₁ = q₁)
    (hs₁ : SupportedIn q₁ 0 (N + 1)) :
    ∃ q : X.bdC ⟶ X.bdC, q ≫ q = q ∧ SupportedIn q 0 N ∧ Nonempty (KarHtpyEquiv X.bdP q) := by
  let φ₁ := dualHom J N e₁.f ≫ X.bdφ ≫ e₁.f
  have hP : IsKarEquiv (dualHom J N q₁) q₁ φ₁ :=
    (e₁.dual J N).isKarEquiv.comp (IsKarEquiv.comp X.bdφ_poincare e₁.isKarEquiv
      (dualHom_idem X.bdP_idem) X.bdP_idem hq₁) (dualHom_idem hq₁) (dualHom_idem X.bdP_idem) hq₁
  have hk : dualHom J N q₁ ≫ φ₁ ≫ q₁ = φ₁ := by
    simp only [φ₁, assoc, e₁.fp]; rw [← assoc, ← dualHom_comp, e₁.fp]
  let ed := KarHtpyEquiv.ofIsKarEquiv hP hk (dualHom_idem hq₁) hq₁
  have hsd : SupportedIn (dualHom J N q₁) (-1) N := (hs₁.dualHom (J := J) (N := N)).mono
    (by omega) (by omega)
  refine ⟨ed.truncIdem hq₁ (-1) N hsd, ed.truncIdem_idem hq₁ (-1) N hsd, fun r hr ↦ ?_,
    ⟨e₁.trans (ed.symm.trans (ed.trunc hq₁ (-1) N hsd))⟩⟩
  rcases hr with hr | hr
  · rw [← ed.p_comp_truncIdem hq₁ (-1) N hsd, comp_f, hs₁ r (Or.inl hr), zero_comp]
  · exact ed.supportedIn_truncIdem hq₁ (-1) N hsd r (Or.inr hr)

/-- **`∂C` truncated to `[0, N]`**: for `C` in `[0, N+1]` with split bottom differential of
`∂C` (`hab`), `(∂C, p_∂)` (which lives in `[-1, N+1]`) is Kar-equivalent to a Kar complex
`(∂C, q)` concentrated in `[0, N]`. -/
theorem exists_trunc (hX : SupportedIn X.p 0 (N + 1))
    (hab : X.p.f 0 ≫ (a ≫ X.φ.f 0 + b ≫ X.C.d 1 0) ≫ X.p.f 0 = X.p.f 0) :
    ∃ q : X.bdC ⟶ X.bdC, q ≫ q = q ∧ SupportedIn q 0 N ∧ Nonempty (KarHtpyEquiv X.bdP q) := by
  obtain ⟨q₁, hq₁, hs₁, ⟨e₁⟩⟩ := X.exists_truncLo a b hX hab
  exact X.exists_truncHi e₁ hq₁ hs₁

end Trunc

end SymComplex

/-! ### Bottom compression of a lift: splitting the bottom differential of `∂C''` -/

namespace KaroubiFiltration.QuotPoincare

variable {A : InvCat} {F : KaroubiFiltration A} {M : ℤ} (L : F.QuotPoincare M)
  (ε : L.C.X 0 ⟶ L.C.X 0)

/-- `ε` in degree `0`, `0` elsewhere. -/
def epsF (r : ℤ) : L.C.X r ⟶ L.C.X r :=
  if h : r = 0 then (L.C.XIsoOfEq h).hom ≫ ε ≫ (L.C.XIsoOfEq h.symm).hom else 0

@[simp] lemma epsF_zero : L.epsF ε 0 = ε := by simp [epsF]

lemma epsF_ne {r : ℤ} (h : r ≠ 0) : L.epsF ε r = 0 := by simp [epsF, h]

/-- The compressed idempotent `q = p - ε` (`ε` only in degree `0`). -/
def qF (r : ℤ) : L.C.X r ⟶ L.C.X r := L.p.f r - L.epsF ε r

lemma qF_ne {r : ℤ} (h : r ≠ 0) : L.qF ε r = L.p.f r := by simp [qF, L.epsF_ne ε h]

lemma qF_zero : L.qF ε 0 = L.p.f 0 - ε := by simp [qF]

variable {L ε} (hp0 : L.p.f 0 = 𝟙 _) (hε : ε ≫ ε = ε)

omit hp0 in
include L in
lemma qF_neg_one : L.qF ε (-1) = 0 := by
  rw [L.qF_ne ε (by omega), L.support (-1) (by omega)]

include hp0 in
lemma p_qF (r : ℤ) : L.p.f r ≫ L.qF ε r = L.qF ε r := by
  by_cases h : r = 0
  · subst h; rw [hp0, id_comp]
  · rw [L.qF_ne ε h, f_idem L.p L.p_idem]

include hp0 in
lemma qF_p (r : ℤ) : L.qF ε r ≫ L.p.f r = L.qF ε r := by
  by_cases h : r = 0
  · subst h; rw [hp0, comp_id]
  · rw [L.qF_ne ε h, f_idem L.p L.p_idem]

include hp0 in
lemma d_neg_one : L.C.d 0 (-1) = 0 := by
  rw [← id_comp (L.C.d 0 (-1)), ← hp0, L.p.comm, L.support (-1) (by omega), comp_zero]

include hp0 hε in
lemma qF_idem (r : ℤ) : L.qF ε r ≫ L.qF ε r = L.qF ε r := by
  by_cases h : r = 0
  · subst h; simp [qF_zero, hp0, hε]
  · rw [L.qF_ne ε h, f_idem L.p L.p_idem]

lemma map_qF (hU : FactorsThrough F.U ε) (r : ℤ) :
    F.proj.F.map (L.qF ε r) = F.proj.F.map (L.p.f r) := by
  rw [F.proj_map_eq_iff, qF, sub_sub_cancel_left]
  by_cases h : r = 0
  · subst h; simpa using hU.neg
  · rw [L.epsF_ne ε h, neg_zero]; exact FactorsThrough.zero

variable (L ε)

/-- **The compressed complex** `C♭ = (C, p d q)`: same objects as `C`, with the `ε`-part of
degree `0` cut off from the image of `d`. -/
@[simps, implicit_reducible]
def flatC : ChainComplex A ℤ where
  X := L.C.X
  d i j := L.p.f i ≫ L.C.d i j ≫ L.qF ε j
  shape i j h := by simp [L.C.shape i j h]
  d_comp_d' i j k _ hjk := by
    by_cases h : j = 0
    · subst h
      obtain rfl : k = -1 := by simp at hjk; omega
      simp [qF_neg_one]
    · simp only [assoc, L.qF_ne ε h, f_idem_assoc L.p L.p_idem, L.p.comm_assoc j k,
        HomologicalComplex.d_comp_d_assoc, zero_comp, comp_zero]

/-- `τ = q : (C, p) ⟶ (C♭, q)`, an honest chain map. -/
@[simps]
def flatTo : L.C ⟶ L.flatC ε where
  f r := L.qF ε r
  comm' i j hij := by
    by_cases h : i = 0
    · subst h
      obtain rfl : j = -1 := by simp at hij; omega
      simp [qF_neg_one]
    · simp only [flatC_d]
      rw [L.qF_ne ε h, ← assoc, f_idem L.p L.p_idem, L.p.comm_assoc, p_qF hp0]

/-- The idempotent `q` of `C♭`. -/
@[simps]
def flatP : L.flatC ε ⟶ L.flatC ε where
  f r := L.qF ε r
  comm' i j hij := by
    by_cases h : i = 0
    · subst h
      obtain rfl : j = -1 := by simp at hij; omega
      simp [qF_neg_one]
    · simp only [flatC_d]
      rw [L.qF_ne ε h, ← assoc, f_idem L.p L.p_idem, assoc, assoc, qF_idem hp0 hε]

lemma flatP_idem : L.flatP ε hp0 hε ≫ L.flatP ε hp0 hε = L.flatP ε hp0 hε := by
  ext r; exact qF_idem hp0 hε r

lemma flatTo_flatP : L.flatTo ε hp0 ≫ L.flatP ε hp0 hε = L.flatTo ε hp0 := by
  ext r; exact qF_idem hp0 hε r

lemma flatP_support (hM : 0 ≤ M) : SupportedIn (L.flatP ε hp0 hε) 0 M := fun r hr ↦ by
  rw [flatP_f, L.qF_ne ε (by omega), L.support r hr]

/-- The structure `φ♭ = τ φ τ^*` of `C♭`. -/
abbrev flatφ : dualComplex A.inv M (L.flatC ε) ⟶ L.flatC ε :=
  dualHom A.inv M (L.flatTo ε hp0) ≫ L.φ ≫ L.flatTo ε hp0

lemma flatφ_kar : dualHom A.inv M (L.flatP ε hp0 hε) ≫ L.flatφ ε hp0 ≫ L.flatP ε hp0 hε =
    L.flatφ ε hp0 := by
  simp only [flatφ, assoc, flatTo_flatP]
  rw [← assoc, ← dualHom_comp, flatTo_flatP]

lemma flatφ_f (r : ℤ) : (L.flatφ ε hp0).f r =
    A.inv.star (L.qF ε (M - r)) ≫ L.φ.f r ≫ L.qF ε r := rfl

variable (hU : FactorsThrough F.U ε)

include hU in
lemma map_flatφ_f (r : ℤ) : F.proj.F.map ((L.flatφ ε hp0).f r) = F.proj.F.map (L.φ.f r) := by
  have hk : A.inv.star (L.p.f (M - r)) ≫ L.φ.f r ≫ L.p.f r = L.φ.f r := by
    simpa using congrArg (fun f ↦ f.f r) L.φ_kar
  rw [flatφ_f, Functor.map_comp, Functor.map_comp, F.proj.map_star, map_qF hU, map_qF hU,
    ← F.proj.map_star, ← Functor.map_comp, ← Functor.map_comp, hk]

/-- The comparison `C♭ ⟶ C` modulo `U` (componentwise `[q] = [p]`); not a chain map in `A`. -/
@[simps]
def flatFrom : F.projF.mapC (L.flatC ε) ⟶ F.projF.mapC L.C where
  f r := F.proj.F.map (L.qF ε r)
  comm' i j _ := by
    have h : L.p.f i ≫ L.C.d i j ≫ L.p.f j ≫ L.p.f j = L.p.f i ≫ L.C.d i j := by
      rw [f_idem L.p L.p_idem, ← L.p.comm, f_idem_assoc L.p L.p_idem]
    simp only [Functor.mapHomologicalComplex_obj_d, flatC_d, Functor.map_comp, map_qF hU]
    simp only [← Functor.map_comp, assoc]
    rw [h]

lemma flat_fg : L.flatFrom ε hU ≫ F.projF.mapH (L.flatTo ε hp0) =
    F.projF.mapH (L.flatP ε hp0 hε) := by
  ext r
  simp only [comp_f, flatFrom_f, InvFunctor.mapH, Functor.mapHomologicalComplex_map_f, flatTo_f,
    flatP_f, ← Functor.map_comp, qF_idem hp0 hε]

lemma flat_gf : F.projF.mapH (L.flatTo ε hp0) ≫ L.flatFrom ε hU = F.projF.mapH L.p := by
  ext r
  simp only [comp_f, flatFrom_f, InvFunctor.mapH, Functor.mapHomologicalComplex_map_f, flatTo_f,
    ← Functor.map_comp, map_qF hU]
  rw [f_idem L.p L.p_idem]

lemma flat_pf : F.projF.mapH (L.flatP ε hp0 hε) ≫ L.flatFrom ε hU = L.flatFrom ε hU := by
  ext r
  simp only [comp_f, flatFrom_f, InvFunctor.mapH, Functor.mapHomologicalComplex_map_f, flatP_f,
    ← Functor.map_comp, qF_idem hp0 hε]

lemma flat_gp : F.projF.mapH L.p ≫ F.projF.mapH (L.flatTo ε hp0) =
    F.projF.mapH (L.flatTo ε hp0) := by
  rw [← Functor.map_comp]; congr 1; ext r; exact p_qF hp0 r

lemma flat_conj : dualHom F.quot.inv M (L.flatFrom ε hU) ≫ F.projF.mapDual (L.flatφ ε hp0) ≫
    L.flatFrom ε hU = F.projF.mapDual L.φ := by
  have hk (r : ℤ) : A.inv.star (L.p.f (M - r)) ≫ L.φ.f r ≫ L.p.f r = L.φ.f r := by
    simpa using congrArg (fun f ↦ f.f r) L.φ_kar
  ext r
  have e₁ : (dualHom F.quot.inv M (L.flatFrom ε hU) ≫ F.projF.mapDual (L.flatφ ε hp0) ≫
      L.flatFrom ε hU).f r = F.quot.inv.star (F.proj.F.map (L.qF ε (M - r))) ≫
        F.proj.F.map ((L.flatφ ε hp0).f r) ≫ F.proj.F.map (L.qF ε r) := rfl
  rw [e₁, L.map_flatφ_f ε hp0 hU, map_qF hU, map_qF hU, ← F.proj.map_star, ← Functor.map_comp,
    ← Functor.map_comp, hk]
  rfl

/-- **The compressed lift** `L♭ = (C♭, q, φ♭)`: a `QuotPoincare` whose image is strictly
isometric to that of `L` (`flatIso`). -/
@[simps]
def flat (hM : 0 ≤ M) : F.QuotPoincare M where
  C := L.flatC ε
  p := L.flatP ε hp0 hε
  p_idem := L.flatP_idem ε hp0 hε
  support := L.flatP_support ε hp0 hε hM
  φ := L.flatφ ε hp0
  φ_kar := L.flatφ_kar ε hp0 hε
  symm := L.symm.conj _
  poincare := isPoincare_of_strict L.toQuot (F.projF.mapDual_kar (L.flatφ_kar ε hp0 hε))
    (L.flatFrom ε hU) (F.projF.mapH (L.flatTo ε hp0)) (L.flat_fg ε hp0 hε hU)
    (L.flat_gf ε hp0 hU) (L.flat_pf ε hp0 hε hU) (L.flat_conj ε hp0 hU)

/-- `L♭` and `L` have strictly isometric images in `A/U`. -/
def flatIso (hM : 0 ≤ M) :
    SymPoincare.HomotopyIsometry (L.flat ε hp0 hε hU hM).toQuot L.toQuot :=
  strictIsometry (L.flatFrom ε hU) (F.projF.mapH (L.flatTo ε hp0)) (L.flat_fg ε hp0 hε hU)
    (L.flat_gf ε hp0 hU) (L.flat_pf ε hp0 hε hU) (L.flat_gp ε hp0) (L.flat_conj ε hp0 hU)

end KaroubiFiltration.QuotPoincare

namespace KaroubiFiltration.QuotPoincare

variable {A : InvCat} {F : KaroubiFiltration A} {M : ℤ}

/-- **Connected lifts** (the bottom of `∂C''` splits).  If `L` is free in degree `0`
(`p₀ = 1`) and `M ≥ 1`, there is a lift `L♭` with the same image in `A/U` (up to strict
isometry) and maps `a, b` with `q₀ (a φ♭₀ + b d♭) q₀ = q₀`.  In `A/U`, Poincaré duality gives
`ψ₀ φ₀ - h d = 1` in degree `0`; lifting, `u = ψ̃ φ₀ - h̃ d - 1` lies in `I_U`, hence factors
through the `E`-part of a splitting `σ` of `C₀` (`u ε = u`, `ε = σ.idem`); compressing degree `0`
to `1 - ε` (`flat`) kills the defect.  This is the input of `SymComplex.exists_trunc`
(the "connectivity" of Ranicki's boundary construction, [Ran80I, §3]: `∂C''` is then equivalent
to a complex in `[0, M-1]`). -/
theorem exists_flat (L : F.QuotPoincare M) (hM : 1 ≤ M) (hp0 : L.p.f 0 = 𝟙 _) :
    ∃ (L' : F.QuotPoincare M) (a : L'.C.X 0 ⟶ (dualComplex A.inv M L'.C).X 0)
      (b : L'.C.X 0 ⟶ L'.C.X 1),
      L'.p.f 0 ≫ (a ≫ L'.φ.f 0 + b ≫ L'.C.d 1 0) ≫ L'.p.f 0 = L'.p.f 0 ∧
        Nonempty (SymPoincare.HomotopyIsometry L'.toQuot L.toQuot) := by
  obtain ⟨ψ, -, ⟨H₁⟩, -⟩ := L.poincare
  let ψ' : L.C.X 0 ⟶ L.C.X (M - 0) := F.liftQuotHom (ψ.f 0)
  let h' : L.C.X 0 ⟶ L.C.X 1 := F.liftQuotHom (H₁.hom 0 1)
  have hc := homotopy_comm H₁ 0 (-1) 1 (by simp) (by simp)
  have key : F.proj.F.map (ψ' ≫ L.φ.f 0 - h' ≫ L.C.d 1 0) = F.proj.F.map (𝟙 _) := by
    rw [Functor.map_sub, Functor.map_comp, Functor.map_comp, map_liftQuotHom, map_liftQuotHom,
      CategoryTheory.Functor.map_id]
    simp only [comp_f, InvFunctor.mapDual_f, Functor.mapHomologicalComplex_obj_d,
      Functor.mapHomologicalComplex_map_f, d_neg_one hp0, Functor.map_zero, zero_comp, zero_add,
      hp0, CategoryTheory.Functor.map_id] at hc
    rw [sub_eq_iff_eq_add, add_comm]
    exact hc
  have hu : FactorsThrough F.U (ψ' ≫ L.φ.f 0 - h' ≫ L.C.d 1 0 - 𝟙 _) :=
    (F.proj_map_eq_iff _ _).mp key
  obtain ⟨σ, hσ, g, hg⟩ := (F.factorsThrough_iff_target _).mp hu
  have hε : σ.idem ≫ σ.idem = σ.idem := Casc.idem_idem σ
  have hεU : FactorsThrough F.U σ.idem := FactorsThrough.of_mem (F.filt.mem _ σ hσ) σ.πE σ.ιE
  have huε : (ψ' ≫ L.φ.f 0 - h' ≫ L.C.d 1 0 - 𝟙 _) ≫ σ.idem =
      ψ' ≫ L.φ.f 0 - h' ≫ L.C.d 1 0 - 𝟙 _ := by
    rw [hg, assoc, Casc.ιE_idem]
  refine ⟨L.flat σ.idem hp0 hε hεU (by omega), ψ', -h', ?_,
    ⟨L.flatIso σ.idem hp0 hε hεU (by omega)⟩⟩
  have hk : dualHom A.inv M L.p ≫ L.φ = L.φ := kar_left (dualHom_idem L.p_idem) L.φ_kar
  have h1 : A.inv.star (L.qF σ.idem (M - 0)) ≫ L.φ.f 0 = L.φ.f 0 := by
    rw [L.qF_ne σ.idem (by omega)]
    simpa using congrArg (fun f ↦ f.f 0) hk
  have h2 : L.p.f 1 ≫ L.C.d 1 0 = L.C.d 1 0 := by rw [L.p.comm, hp0, comp_id]
  have h3 : (ψ' ≫ L.φ.f 0 - h' ≫ L.C.d 1 0) ≫ L.qF σ.idem 0 = L.qF σ.idem 0 := by
    have e : ψ' ≫ L.φ.f 0 - h' ≫ L.C.d 1 0 =
        (ψ' ≫ L.φ.f 0 - h' ≫ L.C.d 1 0 - 𝟙 _) + 𝟙 _ := by abel
    rw [e, add_comp, id_comp, qF_zero, hp0, comp_sub, comp_id, huε, sub_self, zero_add]
  show L.qF σ.idem 0 ≫ (ψ' ≫ (A.inv.star (L.qF σ.idem (M - 0)) ≫ L.φ.f 0 ≫ L.qF σ.idem 0) +
    (-h') ≫ (L.p.f 1 ≫ L.C.d 1 0 ≫ L.qF σ.idem 0)) ≫ L.qF σ.idem 0 = L.qF σ.idem 0
  rw [reassoc_of% h1, reassoc_of% h2, neg_comp, ← sub_eq_add_neg, ← assoc ψ', ← assoc h',
    ← sub_comp, h3, qF_idem hp0 hε, qF_idem hp0 hε]

end KaroubiFiltration.QuotPoincare

/-! ### Kar(U) model of the truncated boundary -/

namespace KaroubiFiltration

variable {A : InvCat} {F : KaroubiFiltration A}

/-- Contractibility modulo `U` is invariant under Kar homotopy equivalence. -/
lemma ContractibleMod.of_karHtpyEquiv {D D' : ChainComplex A ℤ} {p : D ⟶ D} {p' : D' ⟶ D'}
    (h : F.ContractibleMod p) (e : KarHtpyEquiv p p') : F.ContractibleMod p' := by
  obtain ⟨u, -, hU, ⟨H⟩⟩ := h
  refine ⟨e.g ≫ u ≫ e.f, by simp, fun r ↦ ?_, ⟨?_⟩⟩
  · rw [comp_f, comp_f, ← assoc]; exact ((hU r).comp_left _).comp_right _
  · exact (homotopyCongr ((Homotopy.refl e.g).comp (H.comp (Homotopy.refl e.f))) rfl
      (by simp)).trans e.gf

variable {N : ℤ}

/-- **Kar(U) model of `∂C`** in the general case (plan (L1-iii)–(L1-v)): if `φ` is Poincaré in
`Kar(A/U)` and `(∂C, p_∂)` is Kar-equivalent to `(∂C, q)` with `q` concentrated in `[0, N]`, then
`(∂C, p_∂)` is Kar-equivalent to the image of a Poincaré complex of `U`. -/
theorem _root_.HSFormal.LTheory.SymComplex.exists_sub_of_trunc (X : SymComplex A.inv (N + 1))
    (hX : IsPoincare F.quot.inv (N + 1) (F.projI.mapH X.p) (F.projI.mapDual X.φ))
    {q : X.bdC ⟶ X.bdC} (e : KarHtpyEquiv X.bdP q) (hq : q ≫ q = q) (hs : SupportedIn q 0 N) :
    ∃ Q : SymPoincare F.sub.inv N, Nonempty (KarHtpyEquiv X.bdP (Q.map F.inclI).p) := by
  have hc : F.ContractibleMod (X.bdTBd e hq hs).p :=
    (contractibleMod_bd X.p_idem X.φ_kar X.comm hX).of_karHtpyEquiv e
  obtain ⟨Q, ⟨i⟩⟩ := SymPoincare.exists_sub _ hc
  exact ⟨Q, ⟨e.trans i.toKarHtpyEquiv⟩⟩

end KaroubiFiltration

end

end HSFormal.LTheory
