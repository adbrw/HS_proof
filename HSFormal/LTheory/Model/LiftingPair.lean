import HSFormal.LTheory.Model.LiftingPairAux

/-!
# Lifting pairs (lower L-theory model, module 16, core)

`blueprint/lower-L-construction.md` §3.2 ("Lifting pairs (definition of ∂)", "(L1) Existence")
and §4 row 16, for a Karoubi filtration `F : U ⊂ A` (any `InvCat`, so it applies verbatim at every
level `C_ℤ^{∘j}` with the filtration `C_ℤ^{∘j} F`).

## Main definitions and results

* `KaroubiFiltration.LiftingPair D'` (deliverable (a)), for a closed `(N+1)`-dimensional Poincaré
  complex `D'` of `Kar(A/U)` (the target is a parameter; module 16's final form takes
  `D' = D ⊗ ℝ^{j-k}`): a pair `X = (Y ⟶ W) : SymPair A.inv N` of `Kar A`, a proof `mem` that all
  chain objects of `Y` lie in `U` (the hypothesis of `SymPair.toQuot`/`SymPair.bdLift`), and a
  homotopy isometry `iso : X.toQuot F mem ≃ D'`.  `LiftingPair.bd = X.bdLift F mem` is `Y` as a
  Poincaré complex of `U`; `LiftingPair.bdCls = Lconc.cls bd` is the candidate value of `∂[D']`.
* Existence (deliverable (b)):
  - `nonempty_liftingPair_of_free` : `0 ≤ N`, `D'.p = 1` on `[0, N+1]`, `SupportedIn D'.p 0 (N+1)`
    `→ Nonempty (F.LiftingPair D')` (free complexes: chain objects of `A/U`, i.e. of `A`);
  - `nonempty_liftingPair` : the same for `D'` free and concentrated in `[1, N+1]` (no compression
    needed, `N` arbitrary);
  - `nonempty_liftingPair_of_isometric(_free)` : for `D'` isometric to such a free complex;
  - `QuotPoincare.bdPairConj`/`bdPair_isometric(_neg)` : for an honest lift `L` and **any** Kar(U)
    model `e : (∂L, p_∂) ≃ incl(Q)` of its boundary, Ranicki's boundary pair transported along `e`
    (`bdPair`) represents `(-1)^N L` in `A/U` (sign computed, not assumed).
* H2 (deliverable (c)): `SymPair.liftingPair X hU : F.LiftingPair (X.toQuot F hU)` (identity
  isometry) with `bd = X.bdLift F hU` (`liftingPair_bd`, `rfl`).
* Naturality (deliverable (d)): `LiftingPair.map Φ : F'.LiftingPair (D'.map Φ.quot)` for
  `Φ : FiltrationHom F F'`, with `(P.map Φ).bd = P.bd.map Φ.sub` (`rfl`) and
  `bdCls_map`; also `ofIsometry`, `neg` (`neg_bdCls : P.neg.bdCls = -P.bdCls`).

## The sign `bsign` (H2)

`bdry_pair` (Interface.lean) reads
`bdry F N (cls (Lconc.cls (X.toQuot F hU))) = bsign N • cls (Lconc.cls (X.bdLift F hU))`.
By `SymPair.liftingPair`, `X` itself is a lifting pair of `X.toQuot` at level `0` with boundary
`X.bdLift`, so if `∂` is defined by `∂(ι_k [D']) := ι_k (σ_k • [Y])` for lifting pairs at level
`k`, then `bsign N = σ_0` and the lifting-pair notion introduces **no** sign: with the
normalisation `σ_0 = 1` one gets `bsign = 1`.  A sign can only enter through the transitions:
if `X ⊗ ℝ` (LineComplex) has `(X ⊗ ℝ).toQuot ≃ t_N • (X.toQuot ⊗ ℝ)` and
`(X ⊗ ℝ).bd = s_N • (X.bd ⊗ ℝ)`, well-definedness on the colimit forces
`σ_{k+1} = s t σ_k` (module 18); taking `σ_0 = 1` keeps `bsign = 1`.  The sign `(-1)^N` of the
boundary construction (`bdPairConj`) is absorbed in the existence proof (it is applied to `-D'`
for odd `N`) and does not affect `∂`.

## Deviation from the blueprint: the degree `-1` of Ranicki's boundary

Plan (L1-iii) applies Ranicki's boundary construction to the honest lift `C''` of `D'`.  For
`C''` in `[0, N+1]` (which is where free models of `D ⊗ ℝ` live: their degree-`0` part is
`C_0 ⊗ ℝ_0 ≠ 0`, and it cannot be removed since `ℝ_1 ⟶ ℝ_0` has no bounded splitting in `C_ℤ`),
`∂C'' = Σ⁻¹Cone(φ'')` lives in `[-1, N+1]` (`∂C''_{-1} = C''_0`, `∂C''_{N+1} = C''^0`), while
`SymPoincare`/`SymPair` require `[0, N]`; `boundaryPair` therefore assumes `C''` in `[1, N+1]`.
Worse, `∂C''` need **not** be homotopy equivalent (in `Kar A`) to a complex in `[0, N]`: with
`ψ̃, h̃` lifts of a Poincaré inverse and its homotopy in degree `0`, the defect
`u = ψ̃ φ''₀ - h̃ d - 1 ∈ I_U` obstructs splitting `∂C''_0 ⟶ ∂C''_{-1}` (e.g. `C''_0 = Y ⊕ E`,
`φ''₀ = 1 - e_E`); the obstruction is a homotopy invariant, so the Kar(U) model of `∂C''` would
also live in `[-1, N+1]`.  **Fix (implemented here):** compress degree `0` of the lift by
`1 - ε` with `ε ∈ I_U` an idempotent and `u ε = u` (`QuotPoincare.exists_flat`; `ε` comes from a
splitting of the filtration), which makes the bottom of `∂C''` split; truncate `∂C''` to
`[0, N]` (`SymComplex.exists_trunc`: bottom via the splitting, top by Poincaré duality of `∂φ`);
take the Kar(U) model of the truncation (`SymComplex.exists_sub_of_trunc`: domination + BS01);
and transport Ranicki's pair along the composite (`SymComplex.bdTransport`, which never forms the
untruncated pair).  Further deviations: existence needs `N ≥ 0` in the free `[0, N+1]` case (for
`N = -1` a form over `A/U` need not lift; module 18 only uses levels with `n + j ≥ 0`), and the
boundary pair represents `(-1)^N L`, not `L`.

## Interface needed from FreeLine / LineComplex (to finish module 16)

For a closed Kar complex `D` of `C_ℤ^{∘k}(A/U)` of dimension `n + 1 + k`, module 16's final
existence statement needs, at some level `j > k` with `N := n + j ≥ 0` and the filtration
`F_j := C_ℤ^{∘j} F` (via the strict isos `(CZ F).quot ≅ CZ F.quot` of CZFiltration):
a complex `D'' : SymPoincare F_j.quot.inv (N + 1)` with `D''.p.f r = 𝟙` for `0 ≤ r ≤ N + 1`,
`SupportedIn D''.p 0 (N + 1)`, and `SymPoincare.Isometric D'' (D ⊗ ℝ^{j-k})`.  Then
`nonempty_liftingPair_of_isometric_free` gives a lifting pair of `D ⊗ ℝ^{j-k}`.  (A free model
in `[1, N+1]` cannot be asked for, see above.)  For H2 at higher levels LineComplex must supply
`X ⊗ ℝ` for pairs with `(X ⊗ ℝ).bd` lying in `U` and the two signs `s_N`, `t_N` above.

## What module 17 (uniqueness, L2) needs

`P₁ P₂ : F.LiftingPair D' → Lconc.cls P₁.bd = Lconc.cls P₂.bd` (possibly after `⊗ ℝ`), i.e.
`Cobordant P₁.bd P₂.bd` (`Lconc.cls_eq_cls_iff`).  Inputs: the isometry
`P₁.iso.trans P₂.iso.symm : X₁.toQuot ≃ X₂.toQuot` (a cylinder over `A/U`), the relative lift of
a free pair rel its frozen boundary (`exists_quotPair`/`exists_relLift` of LiftComplex), the
relative boundary construction of an `(N+2)`-pair (triads; BoundaryConstructionRel), and unions
(Glue).  The degree problem above recurs relatively: the interior of the relative lift must be
compressed in degree `0` (`exists_flat` relative to the boundary) and the third face truncated
(`exists_trunc`), so relative versions of `QuotPoincare.flat`, `SymComplex.exists_trunc` and
`SymComplex.bdTransport` are needed.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression
  homotopyCofiber LiftComplex

noncomputable section

attribute [local implicit_reducible] SymPair.map SymPair.closedOfIsZero SymPair.neg

namespace KaroubiFiltration

variable {A : InvCat} {F : KaroubiFiltration A} {N : ℤ}

namespace QuotPoincare

variable (L : F.QuotPoincare (N + 1))

/-- The underlying `(N+1)`-dimensional strictly symmetric complex `(C'', p, φ'')` of `A`. -/
@[simps, implicit_reducible]
def toSymComplex : SymComplex A.inv (N + 1) where
  C := L.C
  p := L.p
  p_idem := L.p_idem
  φ := L.φ
  φ_kar := L.φ_kar
  symm := L.symm

/-- **The lifting pair of `L` along a Kar(U) model** `e : (∂C'', p_∂) ≃ incl(Q)` of the
boundary (plan (L1-iii)–(L1-v)): Ranicki's boundary pair `(∂C'' ⟶ C''^{N+1-*}, (0, ∂φ''))`
transported along `e` (`SymComplex.bdTransport`), a pair of `Kar A` whose boundary has all
chain objects in `U`.  No support hypothesis beyond `L.support` (`[0, N+1]`) is needed here;
the boundary `∂C''` itself lives in `[-1, N+1]`, and only `Q` must lie in `[0, N]`. -/
abbrev bdPair (Q : SymPoincare F.sub.inv N)
    (e : KarHtpyEquiv L.toSymComplex.bdP (Q.map F.inclI).p) : SymPair A.inv N :=
  L.toSymComplex.bdTransport e (Q.map F.inclI).p_idem (Q.map F.inclI).support L.support

variable (Q : SymPoincare F.sub.inv N) (e : KarHtpyEquiv L.toSymComplex.bdP (Q.map F.inclI).p)

/-- The boundary of `bdPair` has all chain objects in `U`. -/
lemma bdPair_mem (r : ℤ) : F.U ((L.bdPair Q e).bd.C.X r) := (Q.C.X r).2

/-- **The structure of the lifting pair modulo `U`**: under `φ'' : C''^{N+1-*} ⟶ C''`, the
closed complex `(bdPair).toQuot = (C''^{N+1-*}, p^*, δφ)` is carried to `(-1)^N φ''`.

Proof (in `A/U`, writing `j : ∂C ⟶ C^{N+1-*}`, `j' = g j`, `c = g ⊕ p^* : Cone(j') ⟶ Cone(j)`):
`c^* Ψ' ≃ Ψ` (`bdTRelHomotopy`), `Ψ' = [inr]^* δφ` since the boundary of the transported
pair vanishes in `A/U` (`mapDual_Ψ_eq`), `Ψ = (-1)^{N+1} (p ι)^*` (`relDuality_bdRel`), and
`π inr = -φ`, `ι π = 1`, `inr c = p^* inr`.  Precomposing with `[π]^*` gives
`-[φ]^* δφ ≃ (-1)^{N+1} [p]^*`. -/
def bdPairConj :
    Homotopy (dualHom F.quot.inv (N + 1) (F.projF.mapH L.φ) ≫
      ((L.bdPair Q e).toQuot F (L.bdPair_mem Q e)).φ ≫ F.projF.mapH L.φ)
      (N.negOnePow • F.projF.mapDual L.φ) := by
  let X := L.toSymComplex
  have HA : Homotopy (dualHom A.inv (N + 1) (X.bdTCone e) ≫ (L.bdPair Q e).Ψ)
      (relDuality X.bdRel) := X.bdTRelHomotopy e
  have HC := ((F.projF.mapDualHomotopy HA).compLeft
    (dualHom F.quot.inv (N + 1) (F.projF.mapH X.coneπ))).compRight (F.projF.mapH L.φ)
  have k1 : inr (L.bdPair Q e).j ≫ X.bdTCone e ≫ X.coneπ = -L.φ := by
    rw [← assoc]
    erw [X.inr_comp_bdTCone e]
    rw [assoc, X.inr_comp_coneπ, comp_neg]
    exact congrArg Neg.neg X.dualHom_p_comp_φ
  have k2 : dualHom F.quot.inv (N + 1) (F.projF.mapH X.coneπ) ≫
      dualHom F.quot.inv (N + 1) (F.projF.mapH (X.bdTCone e)) ≫
        dualHom F.quot.inv (N + 1) (F.projF.mapH (inr (L.bdPair Q e).j)) =
      -dualHom F.quot.inv (N + 1) (F.projF.mapH L.φ) := by
    rw [← dualHom_comp, ← dualHom_comp, ← Functor.map_comp, ← Functor.map_comp, assoc, k1,
      Functor.map_neg, dualHom_neg]
  have k3 : X.p ≫ X.coneι ≫ X.coneπ = X.p := by rw [X.coneι_coneπ, comp_id]
  refine homotopyCongr (HC.smul (-1 : ℤ)) ?_ ?_
  · rw [F.projF.mapDual_dualHom_comp, SymPair.mapDual_Ψ_eq F (L.bdPair Q e) (L.bdPair_mem Q e)]
    simp only [assoc]
    rw [reassoc_of% k2]
    simp
  · rw [X.relDuality_bdRel, F.projF.mapDual_units_smul, Linear.comp_units_smul,
      Linear.units_smul_comp, assoc, ← F.projF.mapDual_comp, ← F.projF.mapDual_dualHom_comp,
      ← assoc, ← dualHom_comp, assoc, k3]
    rw [show dualHom A.inv (N + 1) X.p ≫ L.φ = L.φ from X.dualHom_p_comp_φ,
      Int.negOnePow_succ]
    simp [Units.smul_def]

lemma bdPair_f_kar :
    ((L.bdPair Q e).toQuot F (L.bdPair_mem Q e)).p ≫ F.projF.mapH L.φ ≫ L.toQuot.p =
      F.projF.mapH L.φ := by
  show F.projF.mapH (dualHom A.inv (N + 1) L.p) ≫ F.projF.mapH L.φ ≫ F.projF.mapH L.p = _
  rw [← Functor.map_comp, ← Functor.map_comp, L.φ_kar]

/-- **(L1) for a lift, even sign**: if `N` is even, `bdPair` represents `L` in `A/U`, via
`φ'' : C''^{N+1-*} ⟶ C''`. -/
theorem bdPair_isometric (hN : N.negOnePow = 1) :
    Nonempty (SymPoincare.HomotopyIsometry ((L.bdPair Q e).toQuot F (L.bdPair_mem Q e))
      L.toQuot) :=
  SymPoincare.HomotopyIsometry.nonempty_of_conj (F.projF.mapH L.φ) (L.bdPair_f_kar Q e)
    (isKarEquiv_mapH_of_isPoincare L.poincare)
    (homotopyCongr (L.bdPairConj Q e) rfl (by rw [hN, one_smul]; rfl))

/-- **(L1) for a lift, odd sign**: if `N` is odd, `bdPair` represents `-L`. -/
theorem bdPair_isometric_neg (hN : N.negOnePow = -1) :
    Nonempty (SymPoincare.HomotopyIsometry ((L.bdPair Q e).toQuot F (L.bdPair_mem Q e))
      L.toQuot.neg) :=
  SymPoincare.HomotopyIsometry.nonempty_of_conj (F.projF.mapH L.φ) (L.bdPair_f_kar Q e)
    (isKarEquiv_mapH_of_isPoincare L.poincare)
    (homotopyCongr (L.bdPairConj Q e) rfl (by rw [hN, Units.neg_smul, one_smul]; rfl))

/-- The boundary of `bdPair` is `∂C''` transported along `e`; it is homotopy isometric (in `A`) to
the image of `Q` whenever `e` comes from an isometry. -/
lemma bdPair_bd : (L.bdPair Q e).bd = L.toSymComplex.bdTBd e (Q.map F.inclI).p_idem
    (Q.map F.inclI).support := rfl

/-- **Existence of a lifting pair of `L` up to sign**: `L` (or `-L`, by the parity of `N`) has
a lifting pair as soon as `∂C''` has a Kar(U) model. -/
theorem exists_bdPair_isometric (Q : SymPoincare F.sub.inv N)
    (e : KarHtpyEquiv L.toSymComplex.bdP (Q.map F.inclI).p) :
    ∃ (X : SymPair A.inv N) (hU : ∀ r, F.U (X.bd.C.X r)),
      Nonempty (SymPoincare.HomotopyIsometry (X.toQuot F hU)
        (if N.negOnePow = 1 then L.toQuot else L.toQuot.neg)) := by
  refine ⟨L.bdPair Q e, L.bdPair_mem Q e, ?_⟩
  split_ifs with hN
  · exact L.bdPair_isometric Q e hN
  · exact L.bdPair_isometric_neg Q e ((Int.units_eq_one_or _).resolve_left hN)

/-! #### The case `C''` concentrated in `[1, N+1]` -/

variable (h : SupportedIn L.p 1 (N + 1))

/-- Plan (L1-iii)–(L1-v): if `C''` lies in `[1, N+1]`, the boundary `∂C''` lies in `[0, N]` and
is homotopy isometric to the image of a Poincaré complex of `U`
(`SymComplex.exists_sub_boundary`: domination and BS01). -/
theorem exists_subBoundary : ∃ Q : SymPoincare F.sub.inv N,
    Nonempty (SymPoincare.HomotopyIsometry (L.toSymComplex.boundary h) (Q.map F.inclI)) :=
  L.toSymComplex.exists_sub_boundary h L.poincare

/-- The chosen Kar(U) model of `∂C''`. -/
def subBd : SymPoincare F.sub.inv N := (L.exists_subBoundary h).choose

/-- The chosen isometry `∂C'' ≃ incl(subBd)`. -/
def subBdIso :
    SymPoincare.HomotopyIsometry (L.toSymComplex.boundary h) ((L.subBd h).map F.inclI) :=
  (L.exists_subBoundary h).choose_spec.some

/-- **The lifting pair of `L`** for `C''` in `[1, N+1]`. -/
abbrev liftPair : SymPair A.inv N := L.bdPair (L.subBd h) (L.subBdIso h).toKarHtpyEquiv

end QuotPoincare

/-! ### Lifting pairs -/

variable (F) in
/-- **A lifting pair of `D'`** (plan §3.2, "definition of `∂`"), for a closed
`(N+1)`-dimensional Poincaré complex `D'` of `Kar(A/U)`: a Poincaré pair `X = (Y ⟶ W)` of
`Kar A` whose boundary `Y = X.bd` has all chain objects in `U` (the hypothesis of
`SymPair.toQuot`/`SymPair.bdLift`, so that `Y` vanishes objectwise in `A/U`), with an isometry
`X.toQuot ≃ D'` (the closed complex `(W, δφ)` of `A/U`, R3).  Its boundary class
`Lconc.cls (X.bdLift F mem)` is the candidate for `∂[D']`.  The target `D'` is a parameter, so
that module 16's final form takes `D' = D ⊗ ℝ^{j-k}` over `C_ℤ^{∘j}(A/U)`. -/
structure LiftingPair (D' : SymPoincare F.quot.inv (N + 1)) where
  /-- The pair `(Y ⟶ W, (δφ, φ))` of `Kar A`. -/
  X : SymPair A.inv N
  /-- All chain objects of the boundary `Y` lie in `U`. -/
  mem : ∀ r, F.U (X.bd.C.X r)
  /-- `W.toQuot ≃ D'` in `Kar(A/U)`. -/
  iso : SymPoincare.HomotopyIsometry (X.toQuot F mem) D'

namespace LiftingPair

variable {D' D'' : SymPoincare F.quot.inv (N + 1)} (P : F.LiftingPair D')

/-- The boundary `Y`, as an `N`-dimensional Poincaré complex of `U`. -/
abbrev bd : SymPoincare F.sub.inv N := P.X.bdLift F P.mem

@[simp]
lemma map_incl_bd : P.bd.map F.incl = P.X.bd := rfl

/-- The boundary class `[Y] ∈ Lconc U N` (the value of `∂[D']`). -/
abbrev bdCls : Lconc F.sub N := Lconc.cls P.bd

/-- Change of target along an isometry `D' ≃ D''`. -/
@[simps]
def ofIsometry (e : SymPoincare.HomotopyIsometry D' D'') : F.LiftingPair D'' where
  X := P.X
  mem := P.mem
  iso := P.iso.trans e

@[simp]
lemma ofIsometry_bd (e : SymPoincare.HomotopyIsometry D' D'') : (P.ofIsometry e).bd = P.bd := rfl

end LiftingPair

/-! ### Existence (L1) -/

/-- **Existence of lifting pairs (L1)** for free complexes concentrated in `[1, N+1]`: if the
idempotent of `D'` is `1` on `[1, N+1]` and `0` elsewhere (chain objects of `A/U`, hence of `A`),
then `D'` has a lifting pair.  Chain: honest strict self-dual lift `L` (L1-ii,
`exists_quotPoincare_of_supportedIn`) → Ranicki's boundary pair of `L` (L1-iii) → Kar(U) model
of `∂L` by domination and BS01 (L1-iv, v) → transport of the pair (`QuotPoincare.liftPair`).
The pair represents `(-1)^N L` (`bdPairConj`), so for odd `N` the construction is applied to
`-D'`. -/
theorem nonempty_liftingPair (D' : SymPoincare F.quot.inv (N + 1))
    (hp : ∀ r, 1 ≤ r → r ≤ N + 1 → D'.p.f r = 𝟙 _) (hs : SupportedIn D'.p 1 (N + 1)) :
    Nonempty (F.LiftingPair D') := by
  rcases Int.units_eq_one_or N.negOnePow with hN | hN
  · obtain ⟨L, hL, -, ⟨eL⟩⟩ := exists_quotPoincare_of_supportedIn 1 zero_le_one D' hp hs
    obtain ⟨e₁⟩ := L.bdPair_isometric _ (L.subBdIso hL).toKarHtpyEquiv hN
    exact ⟨⟨L.liftPair hL, L.bdPair_mem _ _, e₁.trans eL⟩⟩
  · obtain ⟨L, hL, -, ⟨eL⟩⟩ := exists_quotPoincare_of_supportedIn 1 zero_le_one D'.neg hp hs
    obtain ⟨e₁⟩ := L.bdPair_isometric_neg _ (L.subBdIso hL).toKarHtpyEquiv hN
    have e₂ := eL.neg
    rw [SymPoincare.neg_neg] at e₂
    exact ⟨⟨L.liftPair hL, L.bdPair_mem _ _, e₁.trans e₂⟩⟩

/-- The general free case, one sign at a time: a lift `L` of `D''` together with a Kar(U)
model of `∂L` (after compressing degree `0` (`exists_flat`) and truncating `∂L` to `[0, N]`
(`SymComplex.exists_trunc`)). -/
theorem exists_lift_with_subModel (D'' : SymPoincare F.quot.inv (N + 1)) (hN : 0 ≤ N)
    (hp : ∀ r, 0 ≤ r → r ≤ N + 1 → D''.p.f r = 𝟙 _) (hs : SupportedIn D''.p 0 (N + 1)) :
    ∃ (L : F.QuotPoincare (N + 1)) (Q : SymPoincare F.sub.inv N)
      (_ : KarHtpyEquiv L.toSymComplex.bdP (Q.map F.inclI).p),
      Nonempty (SymPoincare.HomotopyIsometry L.toQuot D'') := by
  obtain ⟨L, -, hL1, ⟨eL⟩⟩ := exists_quotPoincare_of_supportedIn 0 le_rfl D'' hp hs
  obtain ⟨L', a, b, hab, ⟨e'⟩⟩ := QuotPoincare.exists_flat L (by omega) (hL1 0 le_rfl (by omega))
  obtain ⟨q, hq, hsq, ⟨eq⟩⟩ := L'.toSymComplex.exists_trunc a b L'.support hab
  obtain ⟨Q, ⟨eQ⟩⟩ := L'.toSymComplex.exists_sub_of_trunc L'.poincare eq hq hsq
  exact ⟨L', Q, eQ, ⟨e'.trans eL⟩⟩

/-- **Existence of lifting pairs (L1), general free case**: if the idempotent of `D'` is `1` on
`[0, N+1]` and `0` elsewhere (a free complex: chain objects of `A/U`, hence of `A`) and
`N ≥ 0`, then `D'` has a lifting pair.  Chain: honest strict self-dual lift `L` (L1-ii) →
compression of degree `0` making the bottom of `∂L` split (`exists_flat`) → Ranicki's boundary
pair of `L` (L1-iii), whose boundary `∂L` lives in `[-1, N+1]` → truncation of `∂L` to `[0, N]`
(`exists_trunc`: bottom by the splitting, top by Poincaré duality) → Kar(U) model by domination
and BS01 (L1-iv, v) → transport of the boundary pair (`SymComplex.bdTransport`).  The pair
represents `(-1)^N L` (`bdPairConj`), so for odd `N` the construction is applied to `-D'`. -/
theorem nonempty_liftingPair_of_free (D' : SymPoincare F.quot.inv (N + 1)) (hN : 0 ≤ N)
    (hp : ∀ r, 0 ≤ r → r ≤ N + 1 → D'.p.f r = 𝟙 _) (hs : SupportedIn D'.p 0 (N + 1)) :
    Nonempty (F.LiftingPair D') := by
  rcases Int.units_eq_one_or N.negOnePow with hN' | hN'
  · obtain ⟨L, Q, e, ⟨eL⟩⟩ := exists_lift_with_subModel D' hN hp hs
    obtain ⟨e₁⟩ := L.bdPair_isometric Q e hN'
    exact ⟨⟨L.bdPair Q e, L.bdPair_mem Q e, e₁.trans eL⟩⟩
  · obtain ⟨L, Q, e, ⟨eL⟩⟩ := exists_lift_with_subModel D'.neg hN hp hs
    obtain ⟨e₁⟩ := L.bdPair_isometric_neg Q e hN'
    have e₂ := eL.neg
    rw [SymPoincare.neg_neg] at e₂
    exact ⟨⟨L.bdPair Q e, L.bdPair_mem Q e, e₁.trans e₂⟩⟩

/-- Existence of lifting pairs for complexes isometric to free ones (general case). -/
theorem nonempty_liftingPair_of_isometric_free {D' D'' : SymPoincare F.quot.inv (N + 1)}
    (hN : 0 ≤ N) (hp : ∀ r, 0 ≤ r → r ≤ N + 1 → D''.p.f r = 𝟙 _)
    (hs : SupportedIn D''.p 0 (N + 1)) (e : SymPoincare.Isometric D'' D') :
    Nonempty (F.LiftingPair D') :=
  let ⟨P⟩ := nonempty_liftingPair_of_free D'' hN hp hs
  let ⟨e⟩ := e
  ⟨P.ofIsometry e⟩

/-- Existence of lifting pairs for complexes isometric to free ones concentrated in `[1, N+1]`. -/
theorem nonempty_liftingPair_of_isometric {D' D'' : SymPoincare F.quot.inv (N + 1)}
    (hp : ∀ r, 1 ≤ r → r ≤ N + 1 → D''.p.f r = 𝟙 _) (hs : SupportedIn D''.p 1 (N + 1))
    (e : SymPoincare.Isometric D'' D') : Nonempty (F.LiftingPair D') :=
  let ⟨P⟩ := nonempty_liftingPair D'' hp hs
  let ⟨e⟩ := e
  ⟨P.ofIsometry e⟩

end KaroubiFiltration

/-! ### H2: pairs over `A` are lifting pairs of their images -/

namespace SymPair

variable {A : InvCat} (F : KaroubiFiltration A) {N : ℤ}

/-- **H2 compatibility**: a Poincaré pair `X` of `Kar A` whose boundary has chain objects in `U`
is a lifting pair of its own image `X.toQuot` (identity isometry), with boundary
`X.bdLift`.  Hence `∂[X.toQuot] = [X.bdLift]` for `∂` defined by lifting pairs, with sign `+1`
(see the module docstring for `bsign`). -/
@[simps]
def liftingPair (X : SymPair A.inv N) (hU : ∀ r, F.U (X.bd.C.X r)) :
    F.LiftingPair (X.toQuot F hU) where
  X := X
  mem := hU
  iso := .refl _

@[simp]
lemma liftingPair_bd (X : SymPair A.inv N) (hU : ∀ r, F.U (X.bd.C.X r)) :
    (X.liftingPair F hU).bd = X.bdLift F hU := rfl

lemma liftingPair_bdCls (X : SymPair A.inv N) (hU : ∀ r, F.U (X.bd.C.X r)) :
    (X.liftingPair F hU).bdCls = Lconc.cls (X.bdLift F hU) := rfl

end SymPair

/-! ### Naturality -/


namespace KaroubiFiltration.LiftingPair

variable {A B : InvCat} {F : KaroubiFiltration A} {F' : KaroubiFiltration B} {N : ℤ}
  {D' : SymPoincare F.quot.inv (N + 1)} (P : F.LiftingPair D') (Φ : FiltrationHom F F')

/-- **Naturality of lifting pairs** under maps of filtrations `Φ : (A, U) ⟶ (B, U')`:
`Φ X` is a lifting pair of `Φ_{A/U} D'`, with boundary `Φ_U Y`. -/
def map : F'.LiftingPair (D'.map Φ.quot) where
  X := P.X.map Φ.toHom
  mem r := Φ.map_mem _ (P.mem r)
  iso := (SymPoincare.HomotopyIsometry.ofEq'
    (P.X.toQuot_map F P.mem Φ fun r ↦ Φ.map_mem _ (P.mem r)).symm).trans (P.iso.map Φ.quot)

@[simp]
lemma map_X : (P.map Φ).X = P.X.map Φ.toHom := rfl

@[simp]
lemma map_bd : (P.map Φ).bd = P.bd.map Φ.sub := rfl

lemma map_bdCls : (P.map Φ).bdCls = Lconc.map Φ.sub P.bdCls := by
  rw [Lconc.map_cls]; rfl

end KaroubiFiltration.LiftingPair

/-! ### Negation -/

namespace SymPair

variable {A : InvCat} (F : KaroubiFiltration A) {N : ℤ}

/-- `toQuot` commutes with negation of pairs. -/
lemma toQuot_neg (X : SymPair A.inv N) (hU : ∀ r, F.U (X.bd.C.X r)) :
    X.neg.toQuot F hU = (X.toQuot F hU).neg := by
  have ht (r : ℤ) : X.neg.top r = -X.top r := by simp [SymPair.top, relTop]; rfl
  refine SymPoincare.ext_of_φ rfl HEq.rfl (heq_of_eq ?_)
  ext r
  rw [SymPoincare.neg_φ, neg_f_apply, toClosed_φ_f, toClosed_φ_f, ht, Functor.map_neg]

/-- `bdLift` commutes with negation of pairs. -/
lemma bdLift_neg (X : SymPair A.inv N) (hU : ∀ r, F.U (X.bd.C.X r)) :
    X.neg.bdLift F hU = (X.bdLift F hU).neg := by
  refine SymPoincare.ext_of_φ rfl HEq.rfl (heq_of_eq ?_)
  ext r
  rfl

end SymPair

namespace KaroubiFiltration.LiftingPair

variable {A : InvCat} {F : KaroubiFiltration A} {N : ℤ} {D' : SymPoincare F.quot.inv (N + 1)}
  (P : F.LiftingPair D')

/-- A lifting pair of `-D'`: the negated pair `-X`, with boundary `-Y`. -/
def neg : F.LiftingPair D'.neg where
  X := P.X.neg
  mem := P.mem
  iso := (SymPoincare.HomotopyIsometry.ofEq' (P.X.toQuot_neg F P.mem)).trans P.iso.neg

lemma neg_bd : P.neg.bd = P.bd.neg := P.X.bdLift_neg F P.mem

lemma neg_bdCls : P.neg.bdCls = -P.bdCls := by
  rw [bdCls, neg_bd, Lconc.cls_neg]

end KaroubiFiltration.LiftingPair

end

end HSFormal.LTheory
