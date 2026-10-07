import HSFormal.LTheory.Model.Triads
import HSFormal.LTheory.Model.LiftingPairAux

/-!
# The relative boundary construction (L-model module 10)

`blueprint/lower-L-construction.md` §3.2 ((L1)(iii), (L2)), §4 row 10.  Input: an `N`-dimensional
Poincaré complex `P`, a Poincaré pair `W = (j : C ⟶ D, (δφ_W, φ))` on `P`, and a triad
`T = (E; W, ∅; P) : TriadOn W (PairData.zero P)` (an `(N+2)`-dimensional pair `i : D ⟶ E` whose
boundary is the pair `W`, `j i = 0`, top structure `δφ : i δφ_W i^* ≃ 0`; the output shape of
`TriadOn.ofRel`), **not** assumed Poincaré.

## The construction (all on the nose, in `Kar V`)

* `Ψ₀ : Cone(i)^{N+2-*} ⟶ E` (top duality), `Φ = TΨ₀ : E^{N+2-*} ⟶ Cone(i)`,
  `Φ(β) = (-δφ_W i^* β, δφ β)`.
* **The new face** `Z = (j_Z : C ⟶ Z_D)`, `Z_D = Σ⁻¹Cone(Φ)` (`(Z_D)_r = E^{N+2-r} ⊕ D_r ⊕ E_{r+1}`),
  `j_Z c = (0, jc, 0)`, relative structure `δφ_Z` with top `R ≫ p_Z`,
  `R(a', x', e') = ((-1)^{k+1} e', δφ_W x', τ_k a')` (`R_comm`: `j_Z φ j_Z^* = δR + Rd`, strictly
  symmetric, Kar).  Its boundary is **exactly `P`** (no sign, unlike the absolute case).
* `isKarEquiv_δφZ`: **`Z` is Poincaré as soon as `W` is** (ladder `Σ⁻¹Cone(Ψ_W i) ⟶ Cone(j_Z)^* ⟶
  E^{N+2-*}` against `desuspConeKarSplit Φ`, `isKarEquiv_middle_of_comm`); no hypothesis on `T`.
* `contractibleMod_pZ`: **`Z_D` is contractible modulo `U`** if the top of `T` is Poincaré modulo
  `U` (`IsPoincareTopMod`: `[Ψ₀]` a Kar equivalence in `A/U`).
* **The trace** `T.trace : TriadOn W (T.relBdData hE)`, the triad `(M; W, Z; P)` with
  `M = Σ⁻¹Cone(Φ_W)`, `Φ_W = κΦ : E^{N+2-*} ⟶ ΣD` (`M_r = E^{N+2-r} ⊕ D_r`), `i₀' x = (0, x)`,
  `i₁'(a, x, e) = (a, x)`; the triad cycle vanishes on the nose, so the top structure is `0`.
  `trace_isPoincareTop`: its top is Poincaré (both `Cone(i₀')^{N+2-*}` and `Cone(i₁')` are
  Kar-equivalent to `E`, via `β_S^*` and `i_T`, with contractible complements `Cone(p_D)^*`,
  `Cone(p_M)`; `β_S^* Ψ = -(bidual) i_T`).  Hence `relCobordant_relBd : W ∼ Z` rel `P`.

## Degrees

`Z_D` lives in `[-1, N + 2]`.  If `p_E` lives in `[1, N + 2]` (`hE`), `Z_D` lives in `[0, N + 1]`
(`relBd : PairOn P`, `trace`).  In general (`p_E` in `[0, N + 2]`) the face is cut to `[0, N + 1]`
up to Kar equivalence (`exists_relBd`): the bottom by a Kar splitting `hab` of the bottom
differential `E^{N+2} ⊕ D_0 ⊕ E_1 ⟶ E_0` (`exists_truncBot`), the top by Poincaré duality
(`RelRawPair.truncTop`, after `RelRawPair.transportD`).  `hab` is produced by the **relative bottom
compression** `TriadOn.flat`/`exists_flat` (relative version of `QuotPoincare.exists_flat`): if the
top is Poincaré modulo `U` and `p_E = 1` in degree `0`, compressing `E_0` by `1 - ε`
(`ε ∈ I_U` killing the lifted duality defect) splits the bottom, and `isPoincareTopMod_flat`.

## Lifting from `A/U`

* `quotData`, `isPoincareTopMod_iff`: the top modulo `U` is a pair of `A/U` on the closed
  complex `quotBd = W/U`; `T.IsPoincareTopMod F ↔ (T.quotData F hW hP).IsPoincare`.
* `RelLift.ofQuotFam`, `exists_relLiftFam`: relative lift on a frozen boundary whose structure is
  only a family `ψ = relTop δφ_W` (a chain map modulo `U`), with `p_B j'' = j''` and the cascade
  chosen to kill `j_W j''` (`RelLift.exists_cascade_comp_jHom`: this gives `hi : j_W i = 0`).
* `exists_of_quotPair`: a Poincaré pair `Y` of `A/U` on `W/U` (idempotent `1` on `[lo, N + 2]`,
  `0` elsewhere) lifts to a triad `T` with top Poincaré modulo `U`, `p_E = 1_{[lo, N+2]}`.

## Consumer theorems (module 17)

* `nullCobordant_lift_of_quotPair` (`LiftingPairNull`): `P` in `U`, `W` Poincaré on `P`, `W/U`
  bounds `Y` over `A/U` (free on `[0, N + 2]`) ⟹ `NullCobordant (P.lift hP)` over `Kar(U)`
  (lift, compress, cut, dominate: `PairOn.nullCobordant_lift_of_contractibleMod`).  Variants:
  `nullCobordant_lift_of_isPoincareTopMod`, `nullCobordant_lift_of_relBd(')`.
* `exists_relCobordant_of_quotPair` (`LiftingClosedSub`, connected case `Y` in `[1, N + 2]`):
  `W` is cobordant rel `P` (a Poincaré triad, the trace) to a Poincaré pair `Z` on `P` whose top is
  contractible modulo `U`.

## Deviations from the blueprint

* The output triad has face `W` itself (`W' = W`) and top `M = Σ⁻¹Cone(Φ_W)` (not `E`); `∂Z = P`
  on the nose.  The Wall two-out-of-three is not used: each Poincaré condition is proved directly.
* The triad (trace) is only built when `p_E` lives in `[1, N + 2]`; in general degrees only the
  face `Z` is produced (up to Kar equivalence), which is all that `LiftingPairNull` needs.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex homotopyCofiber
  HSFormal.Compression BoundaryConstruction

noncomputable section

attribute [local implicit_reducible] PairData.toPairOn PairOn.toPair SymPair.map SymPair.closedOfIsZero
  TriadOn.ofRel

variable {V : Type*} [Category V] [Preadditive V] [HasBinaryBiproducts V] {J : StrictInvolution V}
  {N : ℤ} {P : SymPoincare J N} {W : PairData P}

/-! ### Duals of cone differentials -/

section ConeStarD

variable {A B : ChainComplex V ℤ} (f : A ⟶ B)

@[reassoc]
lemma bcrel_star_fstX_star_d (i i' k : ℤ) (hi : (ComplexShape.down ℤ).Rel i i')
    (hk : (ComplexShape.down ℤ).Rel i' k) :
    J.star (fstX f i' k hk) ≫ J.star (homotopyCofiber.d f i i') =
      -J.star (A.d i' k) ≫ J.star (fstX f i i' hi) :=
  cone.star_fstX_d f i i' k hi hk

@[reassoc]
lemma bcrel_star_sndX_star_d (i i' : ℤ) (hi : (ComplexShape.down ℤ).Rel i i') :
    J.star (sndX f i') ≫ J.star (homotopyCofiber.d f i i') =
      J.star (f.f i') ≫ J.star (fstX f i i' hi) + J.star (B.d i i') ≫ J.star (sndX f i) :=
  cone.star_sndX_d f i i' hi

@[reassoc]
lemma star_fstX_star_inlX_of_eq {i k k' : ℤ} (h : (ComplexShape.down ℤ).Rel i k)
    (h' : (ComplexShape.down ℤ).Rel i k') :
    J.star (fstX f i k h) ≫ J.star (inlX f k' i h') =
      (A.XIsoOfEq (by simp only [ComplexShape.down_Rel] at h h'; omega)).hom :=
  cone.star_fstX_inlX' f h h'

lemma star_fstX_eq {i k k' : ℤ} (h : (ComplexShape.down ℤ).Rel i k)
    (h' : (ComplexShape.down ℤ).Rel i k') :
    J.star (fstX f i k' h') = (A.XIsoOfEq (by simp only [ComplexShape.down_Rel] at h h'; omega :
      k' = k)).hom ≫ J.star (fstX f i k h) := by
  obtain rfl : k' = k := by simp only [ComplexShape.down_Rel] at h h'; omega
  simp

end ConeStarD

section ConeMapStar

variable {B D B' D' : ChainComplex V ℤ} {j : B ⟶ D} {j' : B' ⟶ D'} {m : B ⟶ B'} {n : D ⟶ D'}
  (hmn : m ≫ j' = j ≫ n)

@[reassoc (attr := simp)]
lemma star_coneMap_f_star_inrX (i : ℤ) :
    J.star ((coneMap m n hmn).f i) ≫ J.star (inrX j i) = J.star (inrX j' i) ≫ J.star (n.f i) := by
  rw [← J.star_comp, ← J.star_comp, inrX_coneMap_f]

@[reassoc (attr := simp)]
lemma star_coneMap_f_star_inlX (i k : ℤ) (hk : (ComplexShape.down ℤ).Rel i k) :
    J.star ((coneMap m n hmn).f i) ≫ J.star (inlX j k i hk) =
      J.star (inlX j' k i hk) ≫ J.star (m.f k) := by
  rw [← J.star_comp, ← J.star_comp, inlX_coneMap_f]
end ConeMapStar

/-! ### Homotopy relations in top-component form -/

section HTopComm

variable {D : ChainComplex V ℤ} {M : ℤ} {f : dualComplex J M D ⟶ D}

omit [HasBinaryBiproducts V] in
/-- The homotopy relation `f = δ H + H d` of `H : f ≃ 0` in terms of top components. -/
lemma hTop_hom_comm (H : Homotopy f 0) (i : ℤ) : f.f i =
    i.negOnePow • J.star (D.d (M - i + 1) (M - i)) ≫
      (D.XIsoOfEq (by omega : M - i + 1 = M + 1 - i)).hom ≫ hTop H i +
    (D.XIsoOfEq (by omega : M - i = M + 1 - (i + 1))).hom ≫ hTop H (i + 1) ≫ D.d (i + 1) i := by
  have h := H.comm i
  rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel i (i - 1) by simp),
    prevD_eq _ (show (ComplexShape.down ℤ).Rel (i + 1) i by simp), zero_f, add_zero] at h
  rw [h, hTop_eq H (i - 1) i (by omega), hTop_eq H i (i + 1) rfl]
  simp only [dualComplex_d, Linear.units_smul_comp, assoc, XIsoOfEq_hom_comp_XIsoOfEq_hom_assoc,
    XIsoOfEq_rfl, Iso.refl_hom, id_comp]
  rw [star_d_XIsoOfEq_assoc D (M - i) (by omega : M - i + 1 = M - (i - 1))]

end HTopComm

/-! ### Generic Kar lemmas -/

section GenericKar

/-- Maps into a cone object are determined by the dual projections `inlX^*`, `inrX^*`. -/
lemma cone_ext_to_star {B D : ChainComplex V ℤ} (j : B ⟶ D) {A : V} (i k : ℤ)
    (h : (ComplexShape.down ℤ).Rel i k) {f g : A ⟶ (cone j).X i}
    (h₁ : f ≫ J.star (inlX j k i h) = g ≫ J.star (inlX j k i h))
    (h₂ : f ≫ J.star (inrX j i) = g ≫ J.star (inrX j i)) : f = g := by
  have e : 𝟙 ((cone j).X i) = J.star (inlX j k i h) ≫ J.star (fstX j i k h) +
      J.star (inrX j i) ≫ J.star (sndX j i) := by
    rw [← J.star_comp, ← J.star_comp, ← J.star_add, ← cone.id_X j i k h]
    simp
  rw [← comp_id f, ← comp_id g, e]
  simp only [comp_add, ← assoc, h₁, h₂]

variable {K M Q : ChainComplex V ℤ} {eK : K ⟶ K} {eM : M ⟶ M} {eQ : Q ⟶ Q} {i : K ⟶ M}
  {q : M ⟶ Q}

omit [HasBinaryBiproducts V] in
/-- A degreewise split sequence whose maps commute with idempotents is a Kar split sequence. -/
def KarSplit.ofDegreewise (S : DegreewiseSplit i q) (heK : eK ≫ eK = eK) (heM : eM ≫ eM = eM)
    (heQ : eQ ≫ eQ = eQ) (hi : eK ≫ i = i ≫ eM) (hq : eM ≫ q = q ≫ eQ) :
    KarSplit eK eM eQ i q where
  t n := eM.f n ≫ S.t n ≫ eK.f n
  s n := eQ.f n ≫ S.s n ≫ eM.f n
  t_kar n := by simp only [← assoc, idem_f heM]; simp only [assoc, idem_f heK]
  s_kar n := by simp only [← assoc, idem_f heQ]; simp only [assoc, idem_f heM]
  it n := by
    have h : i.f n ≫ eM.f n = eK.f n ≫ i.f n := by rw [← comp_f, ← comp_f, hi]
    rw [reassoc_of% h, S.it_assoc, idem_f heK]
  sq n := by
    have h : eM.f n ≫ q.f n = q.f n ≫ eQ.f n := by rw [← comp_f, ← comp_f, hq]
    rw [assoc, assoc, h, S.sq_assoc, idem_f heQ]
  total n := by
    have h₁ : i.f n ≫ eM.f n = eK.f n ≫ i.f n := by rw [← comp_f, ← comp_f, hi]
    have h₂ : eM.f n ≫ q.f n = q.f n ≫ eQ.f n := by rw [← comp_f, ← comp_f, hq]
    have e : eM.f n ≫ (S.t n ≫ i.f n + q.f n ≫ S.s n) ≫ eM.f n = eM.f n := by
      rw [S.total, id_comp, idem_f heM]
    simp only [comp_add, add_comp, assoc] at e ⊢
    rw [← h₁, ← reassoc_of% h₂]
    exact e

/-- The Kar split sequence `0 ⟶ Σ⁻¹D ⟶ Σ⁻¹Cone(j) ⟶ B ⟶ 0`. -/
def desuspConeKarSplit {B D : ChainComplex V ℤ} (j : B ⟶ D) {pB : B ⟶ B} {pD : D ⟶ D}
    (hB : pB ≫ pB = pB) (hD : pD ≫ pD = pD) (h : pB ≫ j = j ≫ pD) :
    KarSplit (desuspMap pD) (desuspMap (coneMap pB pD h)) pB (desuspMap (inr j)) (coneFst j) :=
  KarSplit.ofDegreewise (coneSplit j) (by rw [← desuspMap_comp, hD])
    (by rw [← desuspMap_comp, coneMap_idem _ hB hD]) hB
    (by rw [← desuspMap_comp, ← desuspMap_comp]; congr 1; ext n; simp)
    (by ext n; simp)

omit [HasBinaryBiproducts V] in
lemma IsKarEquiv.desuspMap' {X Y : ChainComplex V ℤ} {e : X ⟶ X} {e' : Y ⟶ Y} {f : X ⟶ Y}
    (h : IsKarEquiv e e' f) : IsKarEquiv (desuspMap e) (desuspMap e') (desuspMap f) := by
  obtain ⟨g, hg, ⟨H₁⟩, ⟨H₂⟩⟩ := h
  exact ⟨desuspMap g, by rw [← desuspMap_comp, ← desuspMap_comp, hg],
    ⟨homotopyCongr (desuspHomotopy H₁) rfl rfl⟩, ⟨homotopyCongr (desuspHomotopy H₂) rfl rfl⟩⟩

section DesuspCone

variable {B D : ChainComplex V ℤ} (j : B ⟶ D) {pB : B ⟶ B} {pD : D ⟶ D} (h : pB ≫ j = j ≫ pD)

lemma desuspMap_inr_comm :
    desuspMap pD ≫ desuspMap (inr j) = desuspMap (inr j) ≫ desuspMap (coneMap pB pD h) := by
  rw [← desuspMap_comp, ← desuspMap_comp]; congr 1; ext n; simp

lemma coneFst_comm : desuspMap (coneMap pB pD h) ≫ coneFst j = coneFst j ≫ pB := by
  ext n; simp
end DesuspCone


end GenericKar

namespace TriadOn

variable (T : TriadOn W (PairData.zero P))

omit [HasBinaryBiproducts V] in
lemma i₁_eq_zero : T.i₁ = 0 := by
  have h := T.i₁_kar
  simp only [PairData.zero_pD, zero_comp] at h
  exact h.symm

omit [HasBinaryBiproducts V] in
@[reassoc (attr := simp)]
lemma j_comp_i₀ : W.j ≫ T.i₀ = 0 := by
  have h := T.comm
  simpa using h

omit [HasBinaryBiproducts V] in
@[reassoc (attr := simp)]
lemma j_f_comp_i₀_f (r : ℤ) : W.j.f r ≫ T.i₀.f r = 0 := by
  rw [← comp_f, T.j_comp_i₀, zero_f]

/-- The chain map `Cone(i₁ = 0) ⟶ E`, `(x, e) ↦ e`. -/
def coneSnd : cone T.i₁ ⟶ T.E :=
  desc T.i₁ (𝟙 T.E) (Homotopy.ofEq (by rw [comp_id]; exact T.i₁_eq_zero))

@[reassoc (attr := simp)]
lemma inrX_coneSnd_f (r : ℤ) : inrX T.i₁ r ≫ T.coneSnd.f r = 𝟙 _ := by
  simp [coneSnd]

@[reassoc (attr := simp)]
lemma inlX_coneSnd_f (r k : ℤ) (h : (ComplexShape.down ℤ).Rel k r) :
    inlX T.i₁ r k h ≫ T.coneSnd.f k = 0 := by
  simp [coneSnd, Homotopy.ofEq]

/-- The top duality of the triad with empty second face, `Ψ₀ : Cone(i)^{N+2-*} ⟶ E`,
`Ψ₀(α, β) = δφ β + (-1)^{r+1} i δφ_W α`. -/
def Ψ₀ : dualComplex J (N + 1 + 1) (cone T.i₀) ⟶ T.E := T.Ψ ≫ T.coneSnd

lemma Ψ₀_f (r : ℤ) : T.Ψ₀.f r = J.star (inrX T.i₀ (N + 1 + 1 - r)) ≫ T.top r +
    (r + 1).negOnePow • J.star (inlX T.i₀ (N + 1 - r) (N + 1 + 1 - r) (down_rel_sub (N + 1) r)) ≫
      relTop W.δφ r ≫ T.i₀.f r := by
  simp [Ψ₀, ΨF]

/-- `Φ = TΨ₀ : E^{N+2-*} ⟶ Cone(i)`, `Φ(β) = (-δφ_W i^* β, δφ β)`. -/
def Φ : dualComplex J (N + 1 + 1) T.E ⟶ cone T.i₀ := transposeHom J (N + 1 + 1) T.Ψ₀

@[reassoc (attr := simp)]
lemma Φ_f_sndX (r : ℤ) : T.Φ.f r ≫ sndX T.i₀ r = T.top r := by
  rw [Φ, transposeHom_f, Linear.units_smul_comp, assoc,
    eqToHom_sndX (sub_sub_cancel (N + 1 + 1) r), Ψ₀_f]
  simp only [J.star_add, J.star_comp, J.star_star, J.star_units_smul, add_comp, assoc,
    inrX_sndX_assoc, Linear.units_smul_comp, inlX_sndX_assoc, zero_comp, comp_zero, smul_zero,
    add_zero]
  exact hTop_transpose T.δφ T.symm r

@[reassoc (attr := simp)]
lemma Φ_f_fstX (r : ℤ) : T.Φ.f r ≫ fstX T.i₀ r (r - 1) (down_rel_pred r) =
    -(J.star (T.i₀.f (N + 1 + 1 - r)) ≫
      (W.D.XIsoOfEq (by omega : N + 1 + 1 - r = N + 1 - (r - 1))).hom ≫ relTop W.δφ (r - 1)) := by
  rw [Φ, transposeHom_f, Linear.units_smul_comp, assoc,
    eqToHom_fstX (sub_sub_cancel (N + 1 + 1) r) _ (down_rel_sub (N + 1) (N + 1 + 1 - r)), Ψ₀_f]
  simp only [J.star_add, J.star_comp, J.star_star, J.star_units_smul, add_comp, assoc,
    inrX_fstX_assoc, Linear.units_smul_comp, inlX_fstX_assoc, zero_comp, comp_zero, zero_add]
  rw [relTop_eq_hTop, star_hTop W.δφ W.symm (N + 1 + 1 - r) (r - 1) (by omega)]
  simp only [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul, assoc]
  simp only [XIsoOfEq, eqToIso.hom, eqToHom_trans, eqToHom_refl, comp_id]
  conv_rhs => rw [← one_smul ℤˣ (J.star _ ≫ _), ← Units.neg_smul]
  congr 1
  triad_sign_tac

@[reassoc (attr := simp)]
lemma Φ_f_fstX' (r k : ℤ) (h : (ComplexShape.down ℤ).Rel r k) : T.Φ.f r ≫ fstX T.i₀ r k h =
    -(J.star (T.i₀.f (N + 1 + 1 - r)) ≫
      (W.D.XIsoOfEq (by simp at h; omega : N + 1 + 1 - r = N + 1 - k)).hom ≫ relTop W.δφ k) := by
  obtain rfl : k = r - 1 := by simp at h; omega
  exact T.Φ_f_fstX r

@[reassoc]
lemma star_fstX_star_Φ_f (r k : ℤ) (h : (ComplexShape.down ℤ).Rel r k) :
    J.star (fstX T.i₀ r k h) ≫ J.star (T.Φ.f r) =
      -(J.star (relTop W.δφ k) ≫ (W.D.XIsoOfEq (by simp at h; omega : N + 1 - k =
        N + 1 + 1 - r)).hom ≫ T.i₀.f (N + 1 + 1 - r)) := by
  rw [← J.star_comp, Φ_f_fstX']
  simp [J.star_comp]

@[reassoc]
lemma star_sndX_star_Φ_f (r : ℤ) : J.star (sndX T.i₀ r) ≫ J.star (T.Φ.f r) = J.star (T.top r) := by
  rw [← J.star_comp, Φ_f_sndX]

lemma Φ_f (r : ℤ) : T.Φ.f r = T.top r ≫ inrX T.i₀ r -
    (J.star (T.i₀.f (N + 1 + 1 - r)) ≫
      (W.D.XIsoOfEq (by omega : N + 1 + 1 - r = N + 1 - (r - 1))).hom ≫ relTop W.δφ (r - 1)) ≫
        inlX T.i₀ (r - 1) r (down_rel_pred r) := by
  apply ext_to_X T.i₀ r (r - 1) (down_rel_pred r) <;> simp

/-- `Ψ₀` is a Kar morphism `(Cone(i)^{N+2-*}, (p_D ⊕ p_E)^*) ⟶ (E, p_E)`. -/
lemma Ψ₀_kar : dualHom J (N + 1 + 1) T.coneIdem₀ ≫ T.Ψ₀ ≫ T.pE = T.Ψ₀ := by
  have h : T.coneIdem₁ ≫ T.coneSnd = T.coneSnd ≫ T.pE := by
    ext n
    apply ext_from_X T.i₁ (n - 1) n (down_rel_pred n) <;> simp
  have hΨ := T.Ψ_kar
  rw [Ψ₀, assoc, ← h, ← assoc T.Ψ, ← assoc, hΨ]

/-- `Φ` is a Kar morphism `(E^{N+2-*}, p_E^*) ⟶ (Cone(i), p_D ⊕ p_E)`. -/
lemma Φ_kar : dualHom J (N + 1 + 1) T.pE ≫ T.Φ ≫ T.coneIdem₀ = T.Φ :=
  transposeHom_kar T.Ψ₀_kar

lemma Φ_comm : dualHom J (N + 1 + 1) T.pE ≫ T.Φ = T.Φ ≫ T.coneIdem₀ :=
  comm_of_kar (dualHom_idem T.pE_idem) (coneMap_idem _ W.pD_idem T.pE_idem) T.Φ_kar

/-! ### The new face `Z = (j_Z : C ⟶ Σ⁻¹Cone(Φ))` -/

/-- **The new face** `Z_D = Σ⁻¹Cone(Φ)`: `(Z_D)_r = E^{N+2-r} ⊕ D_r ⊕ E_{r+1}`, with
`d(a, x, e) = (δa, δφ_W i^* a + dx, -δφ a - ix - de)`. -/
abbrev ZD : ChainComplex V ℤ := desusp (cone T.Φ)

/-- The Kar idempotent `p_E^* ⊕ p_D ⊕ p_E` of `Z_D`. -/
abbrev pZ : T.ZD ⟶ T.ZD := desuspMap (coneMap (dualHom J (N + 1 + 1) T.pE) T.coneIdem₀ T.Φ_comm)

lemma pZ_idem : T.pZ ≫ T.pZ = T.pZ := by
  rw [← desuspMap_comp, coneMap_idem _ (dualHom_idem T.pE_idem)
    (coneMap_idem _ W.pD_idem T.pE_idem)]

/-- The boundary map `j_Z : C ⟶ Z_D`, `c ↦ (0, jc, 0)` (a chain map since `j i = 0`). -/
def jZ : P.C ⟶ T.ZD where
  f r := W.j.f r ≫ inlX T.i₀ r (r + 1) (down_rel_succ r) ≫ inrX T.Φ (r + 1)
  comm' r r' h := by
    obtain rfl : r = r' + 1 := by simp at h; omega
    simp [inlX_d_assoc T.i₀ (r' + 1 + 1) (r' + 1) r' (down_rel_succ _) (down_rel_succ _)]

@[simp]
lemma jZ_f (r : ℤ) : (T.jZ).f r = W.j.f r ≫ inlX T.i₀ r (r + 1) (down_rel_succ r) ≫
    inrX T.Φ (r + 1) := rfl

/-- The sign `τ_k = (-1)^{k + (k+1)(N-k)}` of the `E_{k+1}`-component of the relative structure. -/
abbrev τ (N k : ℤ) : ℤˣ := (k + (k + 1) * (N - k)).negOnePow

/-- The top component `R : Z_D^{N+1-k} ⟶ (Z_D)_k` (source `(Z_D)_s`, `s + k = N + 1`) of the
relative structure of `Z`: in the dual coordinates `(a', x', e') ∈ E_{k+1} ⊕ D^{N+1-k} ⊕ E^{N+2-k}`
of `(Z_D)_s`, `R(a', x', e') = ((-1)^{k+1} e', δφ_W x', τ_k a')`. -/
def R (s k : ℤ) (h : s + k = N + 1) : T.ZD.X s ⟶ T.ZD.X k :=
  (k + 1).negOnePow • (J.star (inrX T.Φ (s + 1)) ≫ J.star (inrX T.i₀ (s + 1)) ≫
      (T.E.XIsoOfEq (by omega : s + 1 = N + 1 + 1 - k)).hom ≫
        inlX T.Φ k (k + 1) (down_rel_succ k)) +
    J.star (inrX T.Φ (s + 1)) ≫ J.star (inlX T.i₀ s (s + 1) (down_rel_succ s)) ≫
      (W.D.XIsoOfEq (by omega : s = N + 1 - k)).hom ≫ relTop W.δφ k ≫
        inlX T.i₀ k (k + 1) (down_rel_succ k) ≫ inrX T.Φ (k + 1) +
    τ N k • (J.star (inlX T.Φ s (s + 1) (down_rel_succ s)) ≫
      (T.E.XIsoOfEq (by omega : N + 1 + 1 - s = k + 1)).hom ≫ inrX T.i₀ (k + 1) ≫
        inrX T.Φ (k + 1))

set_option maxHeartbeats 400000 in
/-- The relative cycle condition for `R`: `j_Z φ j_Z^* = δ R + R d`. -/
lemma R_comm (i : ℤ) : (dualHom J N T.jZ ≫ P.φ ≫ T.jZ).f i =
    ((dualComplex J N T.ZD).d i (i - 1) ≫ T.R (N - (i - 1)) i (by omega) :
      T.ZD.X (N - i) ⟶ T.ZD.X i) + T.R (N - i) (i + 1) (by omega) ≫ T.ZD.d (i + 1) i := by
  have hs : (ComplexShape.down ℤ).Rel (N - (i - 1) + 1) (N - i + 1) := by simp; omega
  apply cone.ext_star (J := J) T.Φ (N - i + 1) (N - i) (down_rel_succ _)
  · apply ext_to_X T.Φ (i + 1) i (down_rel_succ _)
    · simp [R]
    · apply ext_to_X T.i₀ (i + 1) i (down_rel_succ _)
      · simp [R, J.star_comp]
      · simp [R, J.star_comp, bcrel_star_fstX_star_d_assoc _ _ _ _ hs (down_rel_succ _),
          star_fstX_star_inlX_of_eq_assoc,
          ]
        simp only [dualComplex_XIsoOfEq_hom, XIsoOfEq_hom_comp_XIsoOfEq_hom, d_comp_XIsoOfEq_hom,
          smul_smul]
        rw [eq_comm, ← sub_eq_add_neg, sub_eq_zero]
        congr 1
        triad_sign_tac
  · apply cone.ext_star (J := J) T.i₀ (N - i + 1) (N - i) (down_rel_succ _)
    · apply ext_to_X T.Φ (i + 1) i (down_rel_succ _)
      · simp [R]
      · apply ext_to_X T.i₀ (i + 1) i (down_rel_succ _)
        · simp [R, J.star_comp, bcrel_star_sndX_star_d_assoc _ _ _ hs,
            bcrel_star_fstX_star_d_assoc _ _ _ _ hs (down_rel_succ _),
            star_fstX_star_inlX_of_eq_assoc,
            d_fstX T.i₀ (i + 1 + 1) (i + 1) i (down_rel_succ _) (down_rel_succ _),
            star_fstX_star_Φ_f_assoc]
          exact hTop_hom_comm W.δφ i
        · simp [R, J.star_comp, bcrel_star_sndX_star_d_assoc _ _ _ hs,
            bcrel_star_fstX_star_d_assoc _ _ _ _ hs (down_rel_succ _),
            star_fstX_star_inlX_of_eq_assoc,
            d_sndX T.i₀ (i + 1 + 1) (i + 1) (down_rel_succ _),
            star_fstX_star_Φ_f_assoc]
          rw [relTop_eq_hTop, star_hTop W.δφ W.symm (N - i) (i + 1) (by omega)]
          simp only [Linear.units_smul_comp, assoc, smul_smul,
            dualComplex_XIsoOfEq_hom, XIsoOfEq_hom_comp_XIsoOfEq_hom_assoc,
            XIsoOfEq_hom_comp_XIsoOfEq_hom, XIsoOfEq_comp_f_comp_XIsoOfEq]
          rw [show τ N i * (i.negOnePow * ((i + 1) * (N + 1 - (i + 1))).negOnePow) = 1 by
            simp only [τ]; triad_sign_tac]
          simp
    · apply ext_to_X T.Φ (i + 1) i (down_rel_succ _)
      · simp [R, J.star_comp, bcrel_star_sndX_star_d_assoc _ _ _ hs,
          star_fstX_star_inlX_of_eq_assoc,
          d_fstX T.Φ (i + 1 + 1) (i + 1) i (down_rel_succ _) (down_rel_succ _)]
        simp only [star_d_XIsoOfEq, smul_smul]
        rw [show (i + 1).negOnePow * i.negOnePow = -1 by triad_sign_tac,
          show (i + 1 + 1).negOnePow * (i + 1).negOnePow = -1 by triad_sign_tac]
        simp
      · apply ext_to_X T.i₀ (i + 1) i (down_rel_succ _)
        · simp [R, J.star_comp, bcrel_star_sndX_star_d_assoc _ _ _ hs,
            star_fstX_star_inlX_of_eq_assoc,
            d_sndX_assoc T.Φ (i + 1 + 1) (i + 1) (down_rel_succ _),
            d_fstX T.i₀ (i + 1 + 1) (i + 1) i (down_rel_succ _) (down_rel_succ _),
            star_sndX_star_Φ_f_assoc]
          simp only [← star_f_XIsoOfEq_assoc, XIsoOfEq_hom_comp_XIsoOfEq_hom_assoc]
          rw [show (i + 1 + 1).negOnePow = i.negOnePow by
            rw [Int.negOnePow_succ, Int.negOnePow_succ, neg_neg]]
          simp
        · simp [R, J.star_comp, bcrel_star_sndX_star_d_assoc _ _ _ hs,
            star_fstX_star_inlX_of_eq_assoc,
            d_sndX_assoc T.Φ (i + 1 + 1) (i + 1) (down_rel_succ _),
            d_sndX T.i₀ (i + 1 + 1) (i + 1) (down_rel_succ _),
            star_sndX_star_Φ_f_assoc]
          rw [star_hTop T.δφ T.symm (N - i + 1) (i + 1) (by omega)]
          simp only [Linear.units_smul_comp, assoc, smul_smul,
            dualComplex_XIsoOfEq_hom, 
            XIsoOfEq_hom_comp_XIsoOfEq_hom, XIsoOfEq_rfl, Iso.refl_hom, comp_id]
          rw [show τ N i * (i.negOnePow * ((i + 1) * (N + 1 + 1 - (i + 1))).negOnePow) =
            -(i + 1 + 1).negOnePow by simp only [τ]; triad_sign_tac]
          simp

/-- `R` is self-transposed: `R^* = (-1)^{k(N+1-k)} R`. -/
lemma star_R (s k : ℤ) (h : s + k = N + 1) :
    J.star (T.R s k h) = (k * (N + 1 - k)).negOnePow • T.R k s (by omega) := by
  obtain rfl : s = N + 1 - k := by omega
  apply cone.ext_star (J := J) T.Φ (k + 1) k (down_rel_succ _)
  · apply ext_to_X T.Φ (N + 1 - k + 1) (N + 1 - k) (down_rel_succ _)
    · simp [R, J.star_comp, J.star_add, J.star_units_smul]
    · apply ext_to_X T.i₀ (N + 1 - k + 1) (N + 1 - k) (down_rel_succ _)
      · simp [R, J.star_comp, J.star_add, J.star_units_smul]
      · simp [R, J.star_comp, J.star_add, J.star_units_smul, smul_smul]
        congr 1
        simp only [τ]
        triad_sign_tac
  · apply cone.ext_star (J := J) T.i₀ (k + 1) k (down_rel_succ _)
    · apply ext_to_X T.Φ (N + 1 - k + 1) (N + 1 - k) (down_rel_succ _)
      · simp [R, J.star_comp, J.star_add, J.star_units_smul]
      · apply ext_to_X T.i₀ (N + 1 - k + 1) (N + 1 - k) (down_rel_succ _)
        · simp [R, J.star_comp, J.star_add, J.star_units_smul]
          rw [relTop_eq_hTop, star_hTop W.δφ W.symm k (N + 1 - k) (by omega)]
          simp only [XIsoOfEq, eqToIso.hom, eqToHom_refl, comp_id]
          congr 1
          congr 1
          ring
        · simp [R, J.star_comp, J.star_add, J.star_units_smul]
    · apply ext_to_X T.Φ (N + 1 - k + 1) (N + 1 - k) (down_rel_succ _)
      · simp [R, J.star_comp, J.star_add, J.star_units_smul, smul_smul]
        congr 1
        simp only [τ]
        triad_sign_tac
      · apply ext_to_X T.i₀ (N + 1 - k + 1) (N + 1 - k) (down_rel_succ _)
        · simp [R, J.star_comp, J.star_add, J.star_units_smul]
        · simp [R, J.star_comp, J.star_add, J.star_units_smul]

/-- `R` commutes with the Kar idempotents. -/
@[reassoc]
lemma R_comm_pZ (s k : ℤ) (h : s + k = N + 1) :
    J.star (T.pZ.f s) ≫ T.R s k h = T.R s k h ≫ T.pZ.f k := by
  simp [R, star_f_XIsoOfEq_assoc, XIsoOfEq_hom_naturality_assoc]

@[reassoc]
lemma R_cast (s s' k : ℤ) (hs : s = s') (h : s + k = N + 1) (h' : s' + k = N + 1) :
    (T.ZD.XIsoOfEq hs).hom ≫ T.R s' k h' = T.R s k h := by
  subst hs; simp

lemma R_pZ_eqToHom (s k k' : ℤ) (hk : k = k') (h : s + k = N + 1) (h' : s + k' = N + 1) :
    T.R s k h ≫ T.pZ.f k ≫ eqToHom (congrArg T.ZD.X hk) = T.R s k' h' ≫ T.pZ.f k' := by
  subst hk; simp

@[reassoc (attr := simp)]
lemma jZ_pZ : T.jZ ≫ T.pZ = T.jZ := by
  ext r
  simp

@[reassoc (attr := simp)]
lemma jZ_f_pZ_f (r : ℤ) : T.jZ.f r ≫ T.pZ.f r = T.jZ.f r := by
  rw [← comp_f, jZ_pZ]

@[reassoc (attr := simp)]
lemma p_jZ : P.p ≫ T.jZ = T.jZ := by
  ext r
  simp

lemma jZ_kar : P.p ≫ T.jZ ≫ T.pZ = T.jZ := by simp

/-- **The relative structure of the new face** `δφ_Z : j_Z φ j_Z^* ≃ 0`, with top components
`R ≫ p_Z`. -/
def δφZ : Homotopy (dualHom J N T.jZ ≫ P.φ ≫ T.jZ) 0 where
  hom s k := if h : s + 1 = k then T.R (N - s) k (by omega) ≫ T.pZ.f k else 0
  zero s k hsk := dif_neg (by simp at hsk; omega)
  comm i := by
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel i (i - 1) by simp),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (i + 1) i by simp),
      dif_pos (by omega : i - 1 + 1 = i), dif_pos rfl, zero_f, add_zero]
    have hp : T.pZ.f (i + 1) ≫ T.ZD.d (i + 1) i = T.ZD.d (i + 1) i ≫ T.pZ.f i := T.pZ.comm _ _
    have hj : (dualHom J N T.jZ ≫ P.φ ≫ T.jZ).f i ≫ T.pZ.f i =
        (dualHom J N T.jZ ≫ P.φ ≫ T.jZ).f i := by
      simp
    rw [assoc, hp, ← hj, T.R_comm i]
    simp only [add_comp, assoc]

lemma δφZ_hom_succ (s : ℤ) : T.δφZ.hom s (s + 1) = T.R (N - s) (s + 1) (by omega) ≫ T.pZ.f (s + 1) :=
  dif_pos rfl

lemma relTop_δφZ (r : ℤ) : relTop T.δφZ r = T.R (N + 1 - r) r (by omega) ≫ T.pZ.f r := by
  rw [relTop, show T.δφZ.hom (r - 1) r = T.R (N - (r - 1)) r (by omega) ≫ T.pZ.f r from
    dif_pos (by omega), R_cast_assoc]

lemma δφZ_kar (r r' : ℤ) :
    (dualHom J N T.pZ).f r ≫ T.δφZ.hom r r' ≫ T.pZ.f r' = T.δφZ.hom r r' := by
  by_cases h : r + 1 = r'
  · simp only [δφZ, dif_pos h, dualHom_f, assoc, idem_f T.pZ_idem]
    rw [← assoc, R_comm_pZ, assoc, idem_f T.pZ_idem]
  · simp [δφZ, dif_neg h]

lemma δφZ_symm : IsSymmHomotopy J N T.δφZ := by
  rw [IsSymmHomotopy, transposeHomotopy_hom]
  funext r r'
  simp only [transposeHomFamily]
  by_cases h : r + 1 = r'
  · subst h
    rw [show T.δφZ.hom (N - (r + 1)) (N - r) =
      T.R (N - (N - (r + 1))) (N - r) (by omega) ≫ T.pZ.f (N - r) from dif_pos (by omega),
      δφZ_hom_succ]
    conv_lhs => rw [J.star_comp, star_R, Linear.comp_units_smul, R_comm_pZ, bidual_hom_f,
      Linear.comp_units_smul]
    simp only [assoc, Linear.units_smul_comp, smul_smul]
    rw [R_pZ_eqToHom (h' := by omega), show (r + 1).negOnePow * (((r + 1) * (N - (r + 1))).negOnePow *
      ((N - r) * (N + 1 - (N - r))).negOnePow) = 1 by triad_sign_tac, one_smul]
    omega
  · have h' : ¬ N - r' + 1 = N - r := by omega
    simp [δφZ, dif_neg h, dif_neg h']

/-! ### Poincaré duality of the new face -/

/-- The inclusion `(Cone(j)^{N+1-*})_r ⟶ (Cone(j_Z)^{N+1-*})_r`, `(γ, x') ↦ (γ, (0, x', 0))`. -/
def ιC (r : ℤ) : (cone W.j).X (N + 1 - r) ⟶ (cone T.jZ).X (N + 1 - r) :=
  J.star (inlX W.j (N - r) (N + 1 - r) (down_rel_sub N r)) ≫
      J.star (fstX T.jZ (N + 1 - r) (N - r) (down_rel_sub N r)) +
    J.star (inrX W.j (N + 1 - r)) ≫ J.star (fstX T.i₀ (N + 1 - r + 1) (N + 1 - r) (down_rel_succ _)) ≫
      J.star (sndX T.Φ (N + 1 - r + 1)) ≫ J.star (sndX T.jZ (N + 1 - r))

/-- The inclusion `E_{r+1} ⟶ (Cone(j_Z)^{N+1-*})_r` of the `a'`-coordinate. -/
def ιE (r : ℤ) : T.E.X (r + 1) ⟶ (cone T.jZ).X (N + 1 - r) :=
  (T.E.XIsoOfEq (by omega : r + 1 = N + 1 + 1 - (N + 1 - r))).hom ≫
    J.star (fstX T.Φ (N + 1 - r + 1) (N + 1 - r) (down_rel_succ _)) ≫ J.star (sndX T.jZ (N + 1 - r))

/-- `i_K : Σ⁻¹Cone(Ψ_W i) ⟶ Cone(j_Z)^{N+1-*}`. -/
def iKF (r : ℤ) : (desusp (cone (relDuality W.δφ ≫ T.i₀))).X r ⟶
    (dualComplex J (N + 1) (cone T.jZ)).X r :=
  fstX (relDuality W.δφ ≫ T.i₀) (r + 1) r (down_rel_succ r) ≫ T.ιC r +
    τ N r • sndX (relDuality W.δφ ≫ T.i₀) (r + 1) ≫ T.ιE r

abbrev ψi : dualComplex J (N + 1) (cone W.j) ⟶ T.E := relDuality W.δφ ≫ T.i₀

lemma iKF_comm_γ (r : ℤ) :
    J.star (fstX W.j (N + 1 - (r + 1)) (N - (r + 1)) (down_rel_sub N (r + 1))) ≫
      inlX T.ψi (r + 1) (r + 1 + 1) (down_rel_succ _) ≫ T.iKF (r + 1) ≫
        (dualComplex J (N + 1) (cone T.jZ)).d (r + 1) r =
    J.star (fstX W.j (N + 1 - (r + 1)) (N - (r + 1)) (down_rel_sub N (r + 1))) ≫
      inlX T.ψi (r + 1) (r + 1 + 1) (down_rel_succ _) ≫
        (desusp (cone T.ψi)).d (r + 1) r ≫ T.iKF r := by
  have h1 : (ComplexShape.down ℤ).Rel (N + 1 - r) (N + 1 - (r + 1)) := by simp; omega
  have h2 : (ComplexShape.down ℤ).Rel (N + 1 - r + 1) (N + 1 - (r + 1) + 1) := by simp; omega
  apply cone_ext_to_star (J := J) T.jZ (N + 1 - r) (N - r) (down_rel_sub N r)
  · simp [iKF, ιC, ιE, J.star_comp, d_fstX_assoc _ _ _ _ (down_rel_succ (r + 1)) (down_rel_succ r),
      d_sndX_assoc _ _ _ (down_rel_succ (r + 1)),
      bcrel_star_fstX_star_d_assoc _ _ _ _ h1 (down_rel_sub N (r + 1)), 
      bcrel_star_fstX_star_d_assoc _ _ _ _ h2 (down_rel_succ _), bcrel_star_sndX_star_d_assoc _ _ _ h2,
      star_fstX_star_inlX_of_eq_assoc,
      bcrel_star_fstX_star_d _ _ _ _ h1 (down_rel_sub N (r + 1)), bcrel_star_sndX_star_d _ _ _ h1,
      star_fstX_star_inlX_of_eq, star_fstX_star_Φ_f_assoc,
      star_fstX_eq T.i₀ (down_rel_succ (N + 1 - r)) h2, star_fstX_eq T.Φ (down_rel_succ (N + 1 - r)) h2]
  · simp [iKF, ιC, ιE, J.star_comp, d_fstX_assoc _ _ _ _ (down_rel_succ (r + 1)) (down_rel_succ r),
      d_sndX_assoc _ _ _ (down_rel_succ (r + 1)),
      bcrel_star_fstX_star_d_assoc _ _ _ _ h1 (down_rel_sub N (r + 1)), 
      bcrel_star_fstX_star_d_assoc _ _ _ _ h2 (down_rel_succ _), bcrel_star_sndX_star_d_assoc _ _ _ h2,
      star_fstX_star_inlX_of_eq_assoc,
      bcrel_star_fstX_star_d _ _ _ _ h1 (down_rel_sub N (r + 1)), bcrel_star_sndX_star_d _ _ _ h1,
      star_fstX_star_Φ_f_assoc,
      star_fstX_eq T.i₀ (down_rel_succ (N + 1 - r)) h2, star_fstX_eq T.Φ (down_rel_succ (N + 1 - r)) h2]

set_option maxHeartbeats 400000 in
lemma iKF_comm_x (r : ℤ) :
    J.star (sndX W.j (N + 1 - (r + 1))) ≫
      inlX T.ψi (r + 1) (r + 1 + 1) (down_rel_succ _) ≫ T.iKF (r + 1) ≫
        (dualComplex J (N + 1) (cone T.jZ)).d (r + 1) r =
    J.star (sndX W.j (N + 1 - (r + 1))) ≫
      inlX T.ψi (r + 1) (r + 1 + 1) (down_rel_succ _) ≫
        (desusp (cone T.ψi)).d (r + 1) r ≫ T.iKF r := by
  have h1 : (ComplexShape.down ℤ).Rel (N + 1 - r) (N + 1 - (r + 1)) := by simp; omega
  have h2 : (ComplexShape.down ℤ).Rel (N + 1 - r + 1) (N + 1 - (r + 1) + 1) := by simp; omega
  apply cone_ext_to_star (J := J) T.jZ (N + 1 - r) (N - r) (down_rel_sub N r)
  · simp [iKF, ιC, ιE, J.star_comp, d_fstX_assoc _ _ _ _ (down_rel_succ (r + 1)) (down_rel_succ r),
      d_sndX_assoc _ _ _ (down_rel_succ (r + 1)),
      bcrel_star_sndX_star_d_assoc _ _ _ h1,
      bcrel_star_fstX_star_d_assoc _ _ _ _ h2 (down_rel_succ _), bcrel_star_sndX_star_d_assoc _ _ _ h2,
      star_fstX_star_inlX_of_eq_assoc,
      bcrel_star_fstX_star_d _ _ _ _ h1 (down_rel_sub N (r + 1)), bcrel_star_sndX_star_d _ _ _ h1,
      star_fstX_star_inlX_of_eq, star_fstX_star_Φ_f_assoc,
      star_fstX_eq T.i₀ (down_rel_succ (N + 1 - r)) h2, star_fstX_eq T.Φ (down_rel_succ (N + 1 - r)) h2]
  · simp [iKF, ιC, ιE, J.star_comp, d_fstX_assoc _ _ _ _ (down_rel_succ (r + 1)) (down_rel_succ r),
      d_sndX_assoc _ _ _ (down_rel_succ (r + 1)),
      bcrel_star_sndX_star_d_assoc _ _ _ h1,
      bcrel_star_fstX_star_d_assoc _ _ _ _ h2 (down_rel_succ _), bcrel_star_sndX_star_d_assoc _ _ _ h2,
      star_fstX_star_inlX_of_eq_assoc,
      bcrel_star_fstX_star_d _ _ _ _ h1 (down_rel_sub N (r + 1)), bcrel_star_sndX_star_d _ _ _ h1,
      star_fstX_star_Φ_f_assoc,
      star_fstX_eq T.i₀ (down_rel_succ (N + 1 - r)) h2, star_fstX_eq T.Φ (down_rel_succ (N + 1 - r)) h2]
    simp only [star_d_XIsoOfEq_assoc]
    rw [relTop_eq_hTop, star_hTop W.δφ W.symm (N + 1 - (r + 1)) (r + 1) (by omega)]
    simp only [Linear.units_smul_comp, assoc, smul_smul,
      XIsoOfEq_hom_comp_XIsoOfEq_hom_assoc, dualComplex_XIsoOfEq_hom,
      ← XIsoOfEq_hom_naturality_assoc, XIsoOfEq_rfl, Iso.refl_hom, id_comp]
    congr 1
    rw [← Units.neg_smul]
    congr 1
    simp only [τ]
    triad_sign_tac

set_option maxHeartbeats 400000 in
lemma iKF_comm_e (r : ℤ) :
    inrX T.ψi (r + 1 + 1) ≫ T.iKF (r + 1) ≫ (dualComplex J (N + 1) (cone T.jZ)).d (r + 1) r =
    inrX T.ψi (r + 1 + 1) ≫ (desusp (cone T.ψi)).d (r + 1) r ≫ T.iKF r := by
  have h1 : (ComplexShape.down ℤ).Rel (N + 1 - r) (N + 1 - (r + 1)) := by simp; omega
  have h2 : (ComplexShape.down ℤ).Rel (N + 1 - r + 1) (N + 1 - (r + 1) + 1) := by simp; omega
  apply cone_ext_to_star (J := J) T.jZ (N + 1 - r) (N - r) (down_rel_sub N r)
  · simp [iKF, ιC, ιE, J.star_comp, d_fstX_assoc _ _ _ _ (down_rel_succ (r + 1)) (down_rel_succ r),
      d_sndX_assoc _ _ _ (down_rel_succ (r + 1)),
      bcrel_star_fstX_star_d_assoc _ _ _ _ h2 (down_rel_succ _), bcrel_star_sndX_star_d_assoc _ _ _ h2,
      bcrel_star_fstX_star_d _ _ _ _ h1 (down_rel_sub N (r + 1)), bcrel_star_sndX_star_d _ _ _ h1,
      star_fstX_star_Φ_f_assoc,
      star_fstX_eq T.i₀ (down_rel_succ (N + 1 - r)) h2, star_fstX_eq T.Φ (down_rel_succ (N + 1 - r)) h2]
  · simp [iKF, ιC, ιE, J.star_comp, d_fstX_assoc _ _ _ _ (down_rel_succ (r + 1)) (down_rel_succ r),
      d_sndX_assoc _ _ _ (down_rel_succ (r + 1)),
      bcrel_star_fstX_star_d_assoc _ _ _ _ h2 (down_rel_succ _), bcrel_star_sndX_star_d_assoc _ _ _ h2,
      bcrel_star_fstX_star_d _ _ _ _ h1 (down_rel_sub N (r + 1)), bcrel_star_sndX_star_d _ _ _ h1,
      star_fstX_star_Φ_f_assoc,
      star_fstX_eq T.i₀ (down_rel_succ (N + 1 - r)) h2, star_fstX_eq T.Φ (down_rel_succ (N + 1 - r)) h2]
    simp only [dualComplex_XIsoOfEq_hom, d_comp_XIsoOfEq_hom_assoc, smul_smul]
    rw [← Units.neg_smul]
    congr 1
    simp only [τ]
    triad_sign_tac

/-- `i_K` as a chain map. -/
def iK : desusp (cone T.ψi) ⟶ dualComplex J (N + 1) (cone T.jZ) where
  f := T.iKF
  comm' r r' h := by
    obtain rfl : r = r' + 1 := by simp at h; omega
    apply ext_from_X T.ψi (r' + 1) (r' + 1 + 1) (down_rel_succ _)
    · apply cone.ext_star (J := J) W.j (N + 1 - (r' + 1)) (N - (r' + 1)) (down_rel_sub N (r' + 1))
      · simpa only [assoc] using T.iKF_comm_γ r'
      · simpa only [assoc] using T.iKF_comm_x r'
    · simpa only [assoc] using T.iKF_comm_e r'

/-- The projection `q_S : Cone(j_Z)^{N+1-*} ⟶ E^{N+2-*}` onto the `e'`-coordinate. -/
def qSF (r : ℤ) : (dualComplex J (N + 1) (cone T.jZ)).X r ⟶ (dualComplex J (N + 1 + 1) T.E).X r :=
  (r + 1).negOnePow • (J.star (inrX T.jZ (N + 1 - r)) ≫ J.star (inrX T.Φ (N + 1 - r + 1)) ≫
    J.star (inrX T.i₀ (N + 1 - r + 1)) ≫ (T.E.XIsoOfEq (by omega : N + 1 - r + 1 = N + 1 + 1 - r)).hom)

set_option maxHeartbeats 400000 in
lemma qSF_comm (r : ℤ) : T.qSF (r + 1) ≫ (dualComplex J (N + 1 + 1) T.E).d (r + 1) r =
    (dualComplex J (N + 1) (cone T.jZ)).d (r + 1) r ≫ T.qSF r := by
  have h1 : (ComplexShape.down ℤ).Rel (N + 1 - r) (N + 1 - (r + 1)) := by simp; omega
  have h2 : (ComplexShape.down ℤ).Rel (N + 1 - r + 1) (N + 1 - (r + 1) + 1) := by simp; omega
  apply cone.ext_star (J := J) T.jZ (N + 1 - (r + 1)) (N - (r + 1)) (down_rel_sub N (r + 1))
  · simp [qSF]
  · apply cone.ext_star (J := J) T.Φ (N + 1 - (r + 1) + 1) (N + 1 - (r + 1)) (down_rel_succ _)
    · simp [qSF, 
        ]
    · apply cone.ext_star (J := J) T.i₀ (N + 1 - (r + 1) + 1) (N + 1 - (r + 1)) (down_rel_succ _)
      · simp [qSF, 
          ]
      · simp [qSF, 
          ]
        simp only [star_d_XIsoOfEq, smul_smul]
        rw [← Units.neg_smul]
        congr 1
        triad_sign_tac

/-- `q_S` as a chain map. -/
def qS : dualComplex J (N + 1) (cone T.jZ) ⟶ dualComplex J (N + 1 + 1) T.E where
  f := T.qSF
  comm' r r' h := by
    obtain rfl : r = r' + 1 := by simp at h; omega
    exact T.qSF_comm r'

/-- The projection `(Cone(j_Z)^{N+1-*})_r ⟶ (Cone(j)^{N+1-*})_r`. -/
def πC (r : ℤ) : (cone T.jZ).X (N + 1 - r) ⟶ (cone W.j).X (N + 1 - r) :=
  J.star (inlX T.jZ (N - r) (N + 1 - r) (down_rel_sub N r)) ≫
      J.star (fstX W.j (N + 1 - r) (N - r) (down_rel_sub N r)) +
    J.star (inrX T.jZ (N + 1 - r)) ≫ J.star (inrX T.Φ (N + 1 - r + 1)) ≫
      J.star (inlX T.i₀ (N + 1 - r) (N + 1 - r + 1) (down_rel_succ _)) ≫ J.star (sndX W.j (N + 1 - r))

/-- The projection onto the `a'`-coordinate. -/
def πE (r : ℤ) : (cone T.jZ).X (N + 1 - r) ⟶ T.E.X (r + 1) :=
  J.star (inrX T.jZ (N + 1 - r)) ≫ J.star (inlX T.Φ (N + 1 - r) (N + 1 - r + 1) (down_rel_succ _)) ≫
    (T.E.XIsoOfEq (by omega : N + 1 + 1 - (N + 1 - r) = r + 1)).hom

def tF (r : ℤ) : (dualComplex J (N + 1) (cone T.jZ)).X r ⟶ (desusp (cone T.ψi)).X r :=
  T.πC r ≫ inlX T.ψi r (r + 1) (down_rel_succ r) + τ N r • T.πE r ≫ inrX T.ψi (r + 1)

def sF (r : ℤ) : (dualComplex J (N + 1 + 1) T.E).X r ⟶ (dualComplex J (N + 1) (cone T.jZ)).X r :=
  (r + 1).negOnePow • ((T.E.XIsoOfEq (by omega : N + 1 + 1 - r = N + 1 - r + 1)).hom ≫
    J.star (sndX T.i₀ (N + 1 - r + 1)) ≫ J.star (sndX T.Φ (N + 1 - r + 1)) ≫
      J.star (sndX T.jZ (N + 1 - r)))

lemma iKF_tF (r : ℤ) : T.iKF r ≫ T.tF r = 𝟙 _ := by
  apply ext_from_X T.ψi r (r + 1) (down_rel_succ r)
  · apply cone.ext_star (J := J) W.j (N + 1 - r) (N - r) (down_rel_sub N r)
    · apply ext_to_X T.ψi (r + 1) r (down_rel_succ r)
      · apply cone_ext_to_star (J := J) W.j (N + 1 - r) (N - r) (down_rel_sub N r)
        · simp [iKF, tF, ιC, ιE, πC, πE]
        · simp [iKF, tF, ιC, ιE, πC, πE]
      · simp [iKF, tF, ιC, ιE, πC, πE]
    · apply ext_to_X T.ψi (r + 1) r (down_rel_succ r)
      · apply cone_ext_to_star (J := J) W.j (N + 1 - r) (N - r) (down_rel_sub N r)
        · simp [iKF, tF, ιC, ιE, πC, πE]
        · simp [iKF, tF, ιC, ιE, πC, πE]
      · simp [iKF, tF, ιC, ιE, πC, πE]
  · apply ext_to_X T.ψi (r + 1) r (down_rel_succ r)
    · apply cone_ext_to_star (J := J) W.j (N + 1 - r) (N - r) (down_rel_sub N r)
      · simp [iKF, tF, ιC, ιE, πC, πE]
      · simp [iKF, tF, ιC, ιE, πC, πE]
    · simp [iKF, tF, ιC, ιE, πC, πE, smul_smul]

lemma sF_qSF (r : ℤ) : T.sF r ≫ T.qSF r = 𝟙 _ := by
  simp [sF, qSF, smul_smul]

lemma tF_iKF_add (r : ℤ) : T.tF r ≫ T.iKF r + T.qSF r ≫ T.sF r = 𝟙 _ := by
  apply cone.ext_star (J := J) T.jZ (N + 1 - r) (N - r) (down_rel_sub N r)
  · simp [iKF, tF, ιC, ιE, πC, πE, qSF, sF]
  · apply cone.ext_star (J := J) T.Φ (N + 1 - r + 1) (N + 1 - r) (down_rel_succ _)
    · simp [iKF, tF, ιC, ιE, πC, πE, qSF, sF, smul_smul]
    · apply cone.ext_star (J := J) T.i₀ (N + 1 - r + 1) (N + 1 - r) (down_rel_succ _)
      · simp [iKF, tF, ιC, ιE, πC, πE, qSF, sF]
      · simp [iKF, tF, ιC, ιE, πC, πE, qSF, sF, smul_smul]

/-- The degreewise splitting `0 ⟶ Σ⁻¹Cone(Ψ_W i) ⟶ Cone(j_Z)^{N+1-*} ⟶ E^{N+2-*} ⟶ 0`. -/
def split : DegreewiseSplit T.iK T.qS where
  t := T.tF
  s := T.sF
  it := T.iKF_tF
  sq := T.sF_qSF
  total := T.tF_iKF_add

lemma ψi_comm : dualHom J (N + 1) W.coneIdem ≫ T.ψi = T.ψi ≫ T.pE := by
  rw [ψi, ← assoc, dualHom_coneMap_comp_relDuality _ _ P.dualHom_p_comp_φ
    W.dualHom_pD_comp_δφ_hom, assoc, T.i₀_comp_pE]

/-- The idempotent of `Σ⁻¹Cone(Ψ_W i)`. -/
abbrev eK : desusp (cone T.ψi) ⟶ desusp (cone T.ψi) :=
  desuspMap (coneMap (dualHom J (N + 1) W.coneIdem) T.pE T.ψi_comm)

/-- The idempotent `(p ⊕ p_Z)^*` of `Cone(j_Z)^{N+1-*}`. -/
abbrev eS : dualComplex J (N + 1) (cone T.jZ) ⟶ dualComplex J (N + 1) (cone T.jZ) :=
  dualHom J (N + 1) (coneMap P.p T.pZ (comm_of_kar P.p_idem T.pZ_idem T.jZ_kar))

lemma eK_iK : T.eK ≫ T.iK = T.iK ≫ T.eS := by
  ext r
  apply ext_from_X T.ψi r (r + 1) (down_rel_succ r)
  · apply cone.ext_star (J := J) W.j (N + 1 - r) (N - r) (down_rel_sub N r)
    · apply cone_ext_to_star (J := J) T.jZ (N + 1 - r) (N - r) (down_rel_sub N r)
      · simp [iK, iKF, ιC, ιE, XIsoOfEq_hom_naturality_assoc]
      · simp [iK, iKF, ιC, ιE, XIsoOfEq_hom_naturality_assoc]
    · apply cone_ext_to_star (J := J) T.jZ (N + 1 - r) (N - r) (down_rel_sub N r)
      · simp [iK, iKF, ιC, ιE, XIsoOfEq_hom_naturality_assoc]
      · simp [iK, iKF, ιC, ιE, XIsoOfEq_hom_naturality_assoc]
  · apply cone_ext_to_star (J := J) T.jZ (N + 1 - r) (N - r) (down_rel_sub N r)
    · simp [iK, iKF, ιC, ιE, XIsoOfEq_hom_naturality_assoc]
    · simp [iK, iKF, ιC, ιE, XIsoOfEq_hom_naturality_assoc]

lemma eS_qS : T.eS ≫ T.qS = T.qS ≫ dualHom J (N + 1 + 1) T.pE := by
  ext r
  simp [qS, qSF, star_f_XIsoOfEq]

/-- The comparison `Σ⁻¹(Ψ_W ⊕ p_E) : Σ⁻¹Cone(Ψ_W i) ⟶ Σ⁻¹Cone(i)`. -/
abbrev lK : desusp (cone T.ψi) ⟶ desusp (cone T.i₀) :=
  desuspMap (coneMap (relDuality W.δφ) T.pE (by simp [ψi]))

set_option maxHeartbeats 400000 in
lemma iK_relDuality : T.iK ≫ relDuality T.δφZ = T.lK ≫ desuspMap (inr T.Φ) := by
  ext r
  apply ext_from_X T.ψi r (r + 1) (down_rel_succ r)
  · apply cone.ext_star (J := J) W.j (N + 1 - r) (N - r) (down_rel_sub N r)
    · apply ext_to_X T.Φ (r + 1) r (down_rel_succ r)
      · simp [iK, iKF, ιC, ιE, relTop_δφZ, R]
      · apply ext_to_X T.i₀ (r + 1) r (down_rel_succ r)
        · simp [iK, iKF, ιC, ιE, relTop_δφZ, R]
        · simp [iK, iKF, ιC, ιE, relTop_δφZ, R]
    · apply ext_to_X T.Φ (r + 1) r (down_rel_succ r)
      · simp [iK, iKF, ιC, ιE, relTop_δφZ, R]
      · apply ext_to_X T.i₀ (r + 1) r (down_rel_succ r)
        · simp [iK, iKF, ιC, ιE, relTop_δφZ, R]
        · simp [iK, iKF, ιC, ιE, relTop_δφZ, R]
  · apply ext_to_X T.Φ (r + 1) r (down_rel_succ r)
    · simp [iK, iKF, ιC, ιE, relTop_δφZ, R]
    · apply ext_to_X T.i₀ (r + 1) r (down_rel_succ r)
      · simp [iK, iKF, ιC, ιE, relTop_δφZ, R]
      · simp [iK, iKF, ιC, ιE, relTop_δφZ, R, smul_smul, Int.units_mul_self]

lemma qS_relDuality : T.qS ≫ dualHom J (N + 1 + 1) T.pE = relDuality T.δφZ ≫ coneFst T.Φ := by
  ext r
  apply cone.ext_star (J := J) T.jZ (N + 1 - r) (N - r) (down_rel_sub N r)
  · simp [qS, qSF, relTop_δφZ, R]
  · apply cone.ext_star (J := J) T.Φ (N + 1 - r + 1) (N + 1 - r) (down_rel_succ _)
    · simp [qS, qSF, relTop_δφZ, R]
    · apply cone.ext_star (J := J) T.i₀ (N + 1 - r + 1) (N + 1 - r) (down_rel_succ _)
      · simp [qS, qSF, relTop_δφZ, R]
      · simp [qS, qSF, relTop_δφZ, R]

section Poincare

variable [HasFiniteBiproducts V]

/-- **The new face is a Poincaré pair**: `Ψ_Z : (Cone(j_Z)^{N+1-*}, (p ⊕ p_Z)^*) ⟶ (Z_D, p_Z)` is a
Kar equivalence whenever `W` is a Poincaré pair (R2 on the ladder
`Σ⁻¹Cone(Ψ_W i) ⟶ Cone(j_Z)^{N+1-*} ⟶ E^{N+2-*}` over `Σ⁻¹Cone(i) ⟶ Z_D ⟶ E^{N+2-*}`, whose
left vertical `Σ⁻¹(Ψ_W ⊕ 1)` is an equivalence by the five lemma for cones). -/
theorem isKarEquiv_δφZ (hW : W.IsPoincare) : IsKarEquiv T.eS T.pZ (relDuality T.δφZ) := by
  have hcW : W.coneIdem ≫ W.coneIdem = W.coneIdem := W.coneIdem_idem
  have heK : T.eK ≫ T.eK = T.eK := by
    rw [← desuspMap_comp, coneMap_idem _ (dualHom_idem hcW) T.pE_idem]
  have heM : T.eS ≫ T.eS = T.eS := dualHom_idem (coneMap_idem _ P.p_idem T.pZ_idem)
  have heQ : dualHom J (N + 1 + 1) T.pE ≫ dualHom J (N + 1 + 1) T.pE =
      dualHom J (N + 1 + 1) T.pE := dualHom_idem T.pE_idem
  have heK' : desuspMap T.coneIdem₀ ≫ desuspMap T.coneIdem₀ = desuspMap T.coneIdem₀ := by
    rw [← desuspMap_comp, coneMap_idem _ W.pD_idem T.pE_idem]
  have hΨl : dualHom J (N + 1) W.coneIdem ≫ relDuality W.δφ = relDuality W.δφ :=
    dualHom_coneMap_comp_relDuality _ _ P.dualHom_p_comp_φ W.dualHom_pD_comp_δφ_hom
  have hΨr : relDuality W.δφ ≫ W.pD = relDuality W.δφ :=
    relDuality_comp_pD W.j_comp_pD _ W.δφ_hom_comp_pD
  have hm : dualHom J (N + 1) W.coneIdem ≫ relDuality W.δφ ≫ W.pD = relDuality W.δφ := by
    rw [hΨr, hΨl]
  have hj : dualHom J (N + 1) W.coneIdem ≫ T.ψi ≫ T.pE = T.ψi := by
    simp only [ψi, assoc, T.i₀_comp_pE]
    rw [← assoc, hΨl]
  have el : IsKarEquiv T.eK (desuspMap T.coneIdem₀) T.lK :=
    (isKarEquiv_coneMap (dualHom_idem hcW) T.pE_idem W.pD_idem T.pE_idem hj T.i₀_kar hm
      (by simp) _ hW (KarHtpyEquiv.refl T.pE_idem).isKarEquiv).desuspMap'
  refine isKarEquiv_middle_of_comm heK heM heQ heK' T.pZ_idem heQ T.eK_iK T.eS_qS
    (desuspMap_inr_comm T.Φ T.Φ_comm) (coneFst_comm T.Φ T.Φ_comm)
    (KarSplit.ofDegreewise T.split heK heM heQ T.eK_iK T.eS_qS)
    (desuspConeKarSplit T.Φ (dualHom_idem T.pE_idem) (coneMap_idem _ W.pD_idem T.pE_idem)
      T.Φ_comm) ?_ ?_ (by rw [heQ, heQ]) T.iK_relDuality T.qS_relDuality el
    (KarHtpyEquiv.refl (dualHom_idem T.pE_idem)).isKarEquiv
  · rw [← desuspMap_comp, ← desuspMap_comp, coneMap_comp, coneMap_comp]
    congr 1
    exact coneMap_eq_of_eq _ _ (by rw [hm]) (by simp)
  · exact relDuality_kar T.δφZ T.pZ_idem _ T.jZ_pZ P.dualHom_p_comp_φ T.δφZ_kar

end Poincare

/-- Support of `p_Z`: if `p_E` is concentrated in `[lo, N + 2]` (`lo ∈ {0, 1}`), then `p_Z` is
concentrated in `[lo - 1, N + 2 - lo]`. -/
lemma pZ_support {lo : ℤ} (h : SupportedIn T.pE lo (N + 1 + 1)) (hlo : 0 ≤ lo) (hlo' : lo ≤ 1) :
    SupportedIn T.pZ (lo - 1) (N + 1 + 1 - lo) := by
  intro r hr
  have h₁ : T.pE.f (N + 1 + 1 - r) = 0 := h _ (by omega)
  have h₂ : W.pD.f r = 0 := W.support r (by omega)
  have h₃ : T.pE.f (r + 1) = 0 := h _ (by omega)
  rw [desuspMap_f, coneMap_f _ (r + 1) r (down_rel_succ r)]
  simp [coneMap_f _ (r + 1) r (down_rel_succ r), h₁, h₂, h₃]

/-- **The new face as pair data** (`p_E` concentrated in `[1, N + 2]`, so that `Z_D` lies in
`[0, N + 1]`). -/
@[simps, implicit_reducible]
def relBdData (hE : SupportedIn T.pE 1 (N + 1 + 1)) : PairData P where
  D := T.ZD
  pD := T.pZ
  pD_idem := T.pZ_idem
  support := by simpa using T.pZ_support hE (by omega) le_rfl
  j := T.jZ
  j_kar := T.jZ_kar
  δφ := T.δφZ
  δφ_kar := T.δφZ_kar
  symm := T.δφZ_symm

variable [HasFiniteBiproducts V]

lemma relBdData_isPoincare (hW : W.IsPoincare) (hE : SupportedIn T.pE 1 (N + 1 + 1)) :
    (T.relBdData hE).IsPoincare :=
  T.isKarEquiv_δφZ hW

/-- **The relative boundary construction** (`p_E` in `[1, N + 2]`): a Poincaré pair `Z` with
boundary exactly `P`. -/
def relBd (hW : W.IsPoincare) (hE : SupportedIn T.pE 1 (N + 1 + 1)) : PairOn P :=
  (T.relBdData hE).toPairOn (T.relBdData_isPoincare hW hE)

@[simp] lemma relBd_D (hW : W.IsPoincare) (hE : SupportedIn T.pE 1 (N + 1 + 1)) :
    (T.relBd hW hE).D = T.ZD := rfl

@[simp] lemma relBd_pD (hW : W.IsPoincare) (hE : SupportedIn T.pE 1 (N + 1 + 1)) :
    (T.relBd hW hE).pD = T.pZ := rfl

end TriadOn

/-! ### The trace: the Poincaré triad `(M; W, Z; P)` -/

section Trace

variable [HasFiniteBiproducts V]

/-! ### Kar split sequences with a contractible end -/

section KarSplitContr

variable {K M Q : ChainComplex V ℤ} {eK : K ⟶ K} {eM : M ⟶ M} {eQ : Q ⟶ Q} {i : K ⟶ M}
  {q : M ⟶ Q}

omit [HasBinaryBiproducts V] [HasFiniteBiproducts V] in
lemma KarSplit.i_comp_q (S : KarSplit eK eM eQ i q) (hi : eK ≫ i = i) (hi' : i ≫ eM = i)
    (hq : q ≫ eQ = q) : i ≫ q = 0 := by
  have h₁ (n : ℤ) : i.f n ≫ q.f n ≫ S.s n = 0 := by
    have e := congrArg (fun x ↦ i.f n ≫ x) (S.total n)
    simp only [comp_add] at e
    rw [← assoc, S.it, ← comp_f, ← comp_f, hi, hi'] at e
    rw [← assoc]
    simpa using e
  ext n
  have e : i.f n ≫ q.f n = i.f n ≫ q.f n ≫ eQ.f n := by rw [← comp_f q eQ, hq]
  rw [comp_f, zero_f, e, ← S.sq n, ← assoc, ← assoc, assoc (i.f n), h₁, zero_comp]

omit [HasBinaryBiproducts V] in
/-- In a Kar split sequence `K ⟶ M ⟶ Q` with `Q` contractible, `i` is a Kar equivalence. -/
lemma KarSplit.isKarEquiv_i (S : KarSplit eK eM eQ i q) (heK : eK ≫ eK = eK)
    (heM : eM ≫ eM = eM) (heQ : eQ ≫ eQ = eQ) (hi : eK ≫ i = i ≫ eM) (hq : eM ≫ q = q ≫ eQ)
    (hik : eK ≫ i = i) (hqk : q ≫ eQ = q) (hQ : Homotopy eQ 0) : IsKarEquiv eK eM i := by
  have hi' : i ≫ eM = i := by rw [← hi, hik]
  have hiq := S.i_comp_q hik hi' hqk
  let S₀ : KarSplit eK eK (0 : K ⟶ K) (𝟙 K) (0 : K ⟶ K) :=
    { t := fun n ↦ eK.f n
      s := fun _ ↦ 0
      t_kar := fun n ↦ by rw [← comp_f, ← comp_f, heK, heK]
      s_kar := fun n ↦ by simp
      it := fun n ↦ by simp
      sq := fun n ↦ by simp
      total := fun n ↦ by simp }
  have h := isKarEquiv_middle_of_comm heK heK (show (0 : K ⟶ K) ≫ 0 = 0 by simp) heK heM heQ
    (by simp) (by simp) hi hq S₀ S (l := eK) (m := eK ≫ i) (r := 0) (by simp [heK])
    (by simp only [assoc, hi', reassoc_of% heK]) (by simp) (by simp) (by simp [hiq])
    (KarHtpyEquiv.refl heK).isKarEquiv (isKarEquiv_of_contractible _ (Homotopy.refl 0) hQ)
  rwa [hik] at h

omit [HasBinaryBiproducts V] in
/-- In a Kar split sequence `K ⟶ M ⟶ Q` with `K` contractible, `q` is a Kar equivalence. -/
lemma KarSplit.isKarEquiv_q (S : KarSplit eK eM eQ i q) (heK : eK ≫ eK = eK)
    (heM : eM ≫ eM = eM) (heQ : eQ ≫ eQ = eQ) (hi : eK ≫ i = i ≫ eM) (hq : eM ≫ q = q ≫ eQ)
    (hik : eK ≫ i = i) (hqk : q ≫ eQ = q) (hK : Homotopy eK 0) : IsKarEquiv eM eQ q := by
  have hi' : i ≫ eM = i := by rw [← hi, hik]
  have hiq := S.i_comp_q hik hi' hqk
  let S₀ : KarSplit (0 : Q ⟶ Q) eQ eQ (0 : Q ⟶ Q) (𝟙 Q) :=
    { t := fun _ ↦ 0
      s := fun n ↦ eQ.f n
      t_kar := fun n ↦ by simp
      s_kar := fun n ↦ by rw [← comp_f, ← comp_f, heQ, heQ]
      it := fun n ↦ by simp
      sq := fun n ↦ by simp
      total := fun n ↦ by simp }
  have h := isKarEquiv_middle_of_comm heK heM heQ (show (0 : Q ⟶ Q) ≫ 0 = 0 by simp) heQ heQ
    hi hq (by simp) (by simp) S S₀ (l := 0) (m := q) (r := eQ) (by simp)
    (by rw [← assoc, hq, assoc, heQ, hqk]) (by simp [heQ]) (by simp [hiq]) (by simp [hqk])
    (isKarEquiv_of_contractible _ hK (Homotopy.refl 0)) (KarHtpyEquiv.refl heQ).isKarEquiv
  exact h

end KarSplitContr

/-- `Cone(p_D) = (Cone(1_D), p_D ⊕ p_D)` is contractible. -/
def PairData.coneSelfContr (X : PairData P) :
    Homotopy (coneMap (j := 𝟙 X.D) (j' := 𝟙 X.D) X.pD X.pD (by simp)) 0 :=
  homotopyCongr (coneNullHomotopy (j := 𝟙 X.D) (j' := 𝟙 X.D) X.pD)
    (coneMap_eq_of_eq _ _ (by simp) (by simp)) rfl

namespace TriadOn

variable (T : TriadOn W (PairData.zero P))

/-! ### The trace of the relative boundary construction -/

/-- The zero complex. -/
abbrev Z0 : ChainComplex V ℤ := HomologicalComplex.zero

/-- `κ : Cone(i) ⟶ Cone(D ⟶ 0) = ΣD`, `(x, e) ↦ x`. -/
abbrev κ : cone T.i₀ ⟶ cone (0 : W.D ⟶ Z0) := coneMap (𝟙 W.D) 0 (by simp)

/-- `Φ_W = κ Φ : E^{N+2-*} ⟶ ΣD`, `β ↦ -δφ_W i^* β`. -/
abbrev ΦW : dualComplex J (N + 1 + 1) T.E ⟶ cone (0 : W.D ⟶ Z0) := T.Φ ≫ T.κ

/-- **The top of the trace**: `M = Σ⁻¹Cone(Φ_W)`, `M_r = E^{N+2-r} ⊕ D_r` (`Z_D` with the summand
`E_{r+1}` removed). -/
abbrev MD : ChainComplex V ℤ := desusp (cone T.ΦW)

lemma κ_comm : T.coneIdem₀ ≫ T.κ = T.κ ≫ coneMap W.pD (0 : Z0 ⟶ (Z0 : ChainComplex V ℤ)) (by simp) := by
  rw [coneMap_comp, coneMap_comp]
  exact coneMap_eq_of_eq _ _ (by simp) (by simp)

lemma ΦW_comm : dualHom J (N + 1 + 1) T.pE ≫ T.ΦW =
    T.ΦW ≫ coneMap W.pD (0 : Z0 ⟶ (Z0 : ChainComplex V ℤ)) (by simp) := by
  rw [← assoc, T.Φ_comm, assoc, T.κ_comm, assoc]

/-- The Kar idempotent `p_E^* ⊕ p_D` of `M`. -/
abbrev pM : T.MD ⟶ T.MD :=
  desuspMap (coneMap (dualHom J (N + 1 + 1) T.pE) (coneMap W.pD (0 : Z0 ⟶ (Z0 : ChainComplex V ℤ)) (by simp))
    T.ΦW_comm)

lemma pM_idem : T.pM ≫ T.pM = T.pM := by
  rw [← desuspMap_comp, coneMap_idem _ (dualHom_idem T.pE_idem)
    (coneMap_idem _ W.pD_idem (by simp))]

lemma pM_support : SupportedIn T.pM 0 (N + 1 + 1) := by
  intro r hr
  have h₁ : T.pE.f (N + 1 + 1 - r) = 0 := T.support _ (by omega)
  have h₂ : W.pD.f r = 0 := W.support _ (by omega)
  dsimp only [pM, desuspMap]
  rw [coneMap_f _ (r + 1) r (down_rel_succ r), coneMap_f _ (r + 1) r (down_rel_succ r)]
  simp [h₁, h₂]

/-- `κ_p = p_D ⊕ 0 : Cone(i) ⟶ ΣD`. -/
abbrev κp : cone T.i₀ ⟶ cone (0 : W.D ⟶ Z0) := coneMap W.pD 0 (by simp)

lemma κ_pS : T.κ ≫ coneMap W.pD (0 : Z0 ⟶ (Z0 : ChainComplex V ℤ)) (by simp) = T.κp := by
  rw [coneMap_comp]
  exact coneMap_eq_of_eq _ _ (by simp) (by simp)

lemma Φ_κp : dualHom J (N + 1 + 1) T.pE ≫ T.ΦW = T.Φ ≫ T.κp := by
  rw [T.ΦW_comm, assoc, T.κ_pS]

/-- `i₀' : D ⟶ M`, `x ↦ (0, p_D x)`. -/
def i₀' : W.D ⟶ T.MD where
  f r := W.pD.f r ≫ inlX (0 : W.D ⟶ Z0) r (r + 1) (down_rel_succ r) ≫ inrX T.ΦW (r + 1)
  comm' r r' h := by
    obtain rfl : r = r' + 1 := by simp at h; omega
    simp [inlX_d_assoc (0 : W.D ⟶ Z0) (r' + 1 + 1) (r' + 1) r' (down_rel_succ _) (down_rel_succ _),
      W.pD.comm_assoc]

@[simp]
lemma i₀'_f (r : ℤ) : T.i₀'.f r =
    W.pD.f r ≫ inlX (0 : W.D ⟶ Z0) r (r + 1) (down_rel_succ r) ≫ inrX T.ΦW (r + 1) := rfl

/-- `i₁' : Z_D ⟶ M`, `(a, x, e) ↦ (p_E^* a, p_D x)`. -/
abbrev i₁' : T.ZD ⟶ T.MD := desuspMap (coneMap (dualHom J (N + 1 + 1) T.pE) T.κp T.Φ_κp)

lemma i₀'_kar : W.pD ≫ T.i₀' ≫ T.pM = T.i₀' := by
  ext r
  simp [desuspMap, LiftComplex.f_idem_assoc W.pD W.pD_idem]

lemma i₁'_kar : T.pZ ≫ T.i₁' ≫ T.pM = T.i₁' := by
  rw [← desuspMap_comp, ← desuspMap_comp, coneMap_comp, coneMap_comp]
  congr 1
  exact coneMap_eq_of_eq _ _ (by simp [dualHom_idem T.pE_idem])
    (by rw [coneMap_comp, coneMap_comp]; exact coneMap_eq_of_eq _ _ (by simp) (by simp))

lemma trace_comm : W.j ≫ T.i₀' = T.jZ ≫ T.i₁' := by
  ext r
  simp [desuspMap]

omit [HasFiniteBiproducts V] in
@[reassoc]
lemma star_fstX_R (s k : ℤ) (h : s + k = N + 1) :
    J.star (fstX T.Φ (s + 1) s (down_rel_succ s)) ≫ T.R s k h =
      τ N k • ((T.E.XIsoOfEq (by omega : N + 1 + 1 - s = k + 1)).hom ≫ inrX T.i₀ (k + 1) ≫
        inrX T.Φ (k + 1)) := by
  simp [R]

omit [HasFiniteBiproducts V] in
@[reassoc]
lemma star_sndX_R (s k : ℤ) (h : s + k = N + 1) :
    J.star (sndX T.Φ (s + 1)) ≫ T.R s k h =
      (k + 1).negOnePow • (J.star (inrX T.i₀ (s + 1)) ≫
        (T.E.XIsoOfEq (by omega : s + 1 = N + 1 + 1 - k)).hom ≫
          inlX T.Φ k (k + 1) (down_rel_succ k)) +
      J.star (inlX T.i₀ s (s + 1) (down_rel_succ s)) ≫
        (W.D.XIsoOfEq (by omega : s = N + 1 - k)).hom ≫ relTop W.δφ k ≫
          inlX T.i₀ k (k + 1) (down_rel_succ k) ≫ inrX T.Φ (k + 1) := by
  simp [R]

/-- **The triad cycle of the trace vanishes**: `i₁' δφ_Z i₁'^* = i₀' δφ_W i₀'^*`. -/
lemma trace_cycle (s k : ℤ) (h : s + k = N + 1) :
    J.star (T.i₁'.f s) ≫ T.R s k h ≫ T.pZ.f k ≫ T.i₁'.f k =
      J.star (T.i₀'.f s) ≫ (W.D.XIsoOfEq (by omega : s = N + 1 - k)).hom ≫ relTop W.δφ k ≫
        T.i₀'.f k := by
  have e₁ : J.star (fstX T.ΦW (s + 1) s (down_rel_succ s)) ≫ J.star (T.i₁'.f s) =
      J.star ((dualHom J (N + 1 + 1) T.pE).f s) ≫ J.star (fstX T.Φ (s + 1) s (down_rel_succ s)) := by
    rw [← J.star_comp, ← J.star_comp, desuspMap_f, coneMap_f_fstX]
  have e₂ : J.star (sndX T.ΦW (s + 1)) ≫ J.star (T.i₁'.f s) =
      J.star (T.κp.f (s + 1)) ≫ J.star (sndX T.Φ (s + 1)) := by
    rw [← J.star_comp, ← J.star_comp, desuspMap_f, coneMap_f_sndX]
  have e₃ : J.star (fstX T.ΦW (s + 1) s (down_rel_succ s)) ≫ J.star (T.i₀'.f s) = 0 := by
    rw [← J.star_comp, i₀'_f]; simp
  have e₄ : J.star (sndX T.ΦW (s + 1)) ≫ J.star (T.i₀'.f s) =
      J.star (inlX (0 : W.D ⟶ Z0) s (s + 1) (down_rel_succ s)) ≫ J.star (W.pD.f s) := by
    rw [← J.star_comp, ← J.star_comp, i₀'_f]; simp
  apply cone.ext_star (J := J) T.ΦW (s + 1) s (down_rel_succ s)
  · rw [reassoc_of% e₁, reassoc_of% e₃, star_fstX_R_assoc]
    simp [desuspMap_f]
  · rw [reassoc_of% e₂, reassoc_of% e₄, star_sndX_R_assoc]
    simp [desuspMap_f]

variable (hE : SupportedIn T.pE 1 (N + 1 + 1))

lemma trace_triadCycle :
    triadCycle W (T.relBdData hE) T.i₀' T.i₁' T.trace_comm = 0 := by
  ext r
  rw [triadCycle_f, zero_f, relBdData_δφ, relTop_δφZ, assoc,
    T.trace_cycle (N + 1 - r) r (by omega)]
  simp

/-- **The trace of the relative boundary construction**: the triad `(M; W, Z; P)` with
`M = Σ⁻¹Cone(Φ_W)`, `i₀' x = (0, x)`, `i₁'(a, x, e) = (a, x)` and top structure `0` (the triad
cycle vanishes on the nose). -/
@[implicit_reducible]
def trace : TriadOn W (T.relBdData hE) where
  E := T.MD
  pE := T.pM
  pE_idem := T.pM_idem
  support := T.pM_support
  i₀ := T.i₀'
  i₀_kar := T.i₀'_kar
  i₁ := T.i₁'
  i₁_kar := T.i₁'_kar
  comm := T.trace_comm
  δφ := Homotopy.ofEq (T.trace_triadCycle hE)
  δφ_kar r r' := by simp [Homotopy.ofEq]
  symm := by
    rw [IsSymmHomotopy, transposeHomotopy_hom]
    funext r r'
    simp [Homotopy.ofEq, transposeHomFamily]

@[simp] lemma trace_E : (T.trace hE).E = T.MD := rfl
@[simp] lemma trace_pE : (T.trace hE).pE = T.pM := rfl
@[simp] lemma trace_i₀ : (T.trace hE).i₀ = T.i₀' := rfl
@[simp] lemma trace_i₁ : (T.trace hE).i₁ = T.i₁' := rfl

lemma trace_top (r : ℤ) : (T.trace hE).top r = 0 := by
  simp [top, hTop, trace, Homotopy.ofEq]

/-! #### The source `Cone(i₀')^{N+2-*}` -/

@[reassoc (attr := simp)]
lemma pD_i₀' : W.pD ≫ T.i₀' = T.i₀' := kar_left W.pD_idem T.i₀'_kar

@[reassoc (attr := simp)]
lemma i₀'_pM : T.i₀' ≫ T.pM = T.i₀' := kar_right T.pM_idem T.i₀'_kar

/-- `α_S = p_D ⊕ i₀' : Cone(1_D) ⟶ Cone(i₀')`. -/
abbrev αS : cone (𝟙 W.D) ⟶ cone T.i₀' := coneMap W.pD T.i₀' (by simp)

lemma i₀'_coneFst : T.i₀' ≫ coneFst T.ΦW ≫ dualHom J (N + 1 + 1) T.pE = 0 := by
  ext r; simp [coneFst]

/-- `β_S : Cone(i₀') ⟶ E^{N+2-*}`, `(x, (a, y)) ↦ p_E^* a`. -/
abbrev βS : cone T.i₀' ⟶ dualComplex J (N + 1 + 1) T.E :=
  desc T.i₀' (coneFst T.ΦW ≫ dualHom J (N + 1 + 1) T.pE) (Homotopy.ofEq T.i₀'_coneFst)

/-- The idempotent `p_D ⊕ p_M` of `Cone(i₀')` (the `coneIdem₀` of the trace). -/
abbrev eMS : cone T.i₀' ⟶ cone T.i₀' :=
  coneMap W.pD T.pM (comm_of_kar W.pD_idem T.pM_idem T.i₀'_kar)

lemma eKS_αS : coneMap W.pD W.pD (by simp) ≫ T.αS = T.αS := by
  rw [coneMap_comp]; exact coneMap_eq_of_eq _ _ (by simp) (by simp)

lemma αS_eMS : T.αS ≫ T.eMS = T.αS := by
  rw [coneMap_comp]; exact coneMap_eq_of_eq _ _ (by simp) (by simp)

lemma eMS_idem : T.eMS ≫ T.eMS = T.eMS := coneMap_idem _ W.pD_idem T.pM_idem

lemma βS_eQS : T.βS ≫ dualHom J (N + 1 + 1) T.pE = T.βS := by
  have h : dualHom J (N + 1 + 1) T.pE ≫ dualHom J (N + 1 + 1) T.pE = dualHom J (N + 1 + 1) T.pE :=
    dualHom_idem T.pE_idem
  ext n
  apply ext_from_X T.i₀' (n - 1) n (down_rel_pred n)
  · simp [inlX_desc_f_assoc _ _ _ _ _ (down_rel_pred n), inlX_desc_f _ _ _ _ _ (down_rel_pred n),
      Homotopy.ofEq]
  · simp only [comp_f, inrX_desc_f_assoc, inrX_desc_f, assoc]
    rw [← comp_f, h]

lemma eMS_βS : T.eMS ≫ T.βS = T.βS ≫ dualHom J (N + 1 + 1) T.pE := by
  have h : dualHom J (N + 1 + 1) T.pE ≫ dualHom J (N + 1 + 1) T.pE = dualHom J (N + 1 + 1) T.pE :=
    dualHom_idem T.pE_idem
  have hc := coneFst_comm T.ΦW (pB := dualHom J (N + 1 + 1) T.pE)
    (pD := coneMap W.pD (0 : Z0 ⟶ (Z0 : ChainComplex V ℤ)) (by simp)) T.ΦW_comm
  ext n
  apply ext_from_X T.i₀' (n - 1) n (down_rel_pred n)
  · simp [inlX_desc_f_assoc _ _ _ _ _ (down_rel_pred n), inlX_desc_f _ _ _ _ _ (down_rel_pred n),
      Homotopy.ofEq]
  · simp only [comp_f, inrX_desc_f_assoc, inrX_desc_f, assoc, inrX_coneMap_f_assoc]
    have := congrArg (fun f ↦ f.f n) hc
    simp only [comp_f] at this
    rw [reassoc_of% this, ← comp_f, h]

omit [HasBinaryBiproducts V] [HasFiniteBiproducts V] in
@[reassoc (attr := simp)]
lemma pE_idem_f (k : ℤ) : T.pE.f k ≫ T.pE.f k = T.pE.f k := by rw [← comp_f, T.pE_idem]

omit [HasBinaryBiproducts V] [HasFiniteBiproducts V] in
@[reassoc (attr := simp)]
lemma star_pE_f_idem (k : ℤ) : J.star (T.pE.f k) ≫ J.star (T.pE.f k) = J.star (T.pE.f k) := by
  rw [← J.star_comp, ← comp_f, T.pE_idem]

/-- The degreewise retraction `(x, (a, y, 0)) ↦ (x, y)` of `α_S`. -/
def tS₀ (n : ℤ) : (cone T.i₀').X n ⟶ (cone (𝟙 W.D)).X n :=
  fstX T.i₀' n (n - 1) (down_rel_pred n) ≫ inlX (𝟙 W.D) (n - 1) n (down_rel_pred n) +
    sndX T.i₀' n ≫ sndX T.ΦW (n + 1) ≫ fstX (0 : W.D ⟶ Z0) (n + 1) n (down_rel_succ n) ≫
      inrX (𝟙 W.D) n

/-- The degreewise section `a ↦ (0, (a, 0))` of `β_S`. -/
def sS₀ (n : ℤ) : (dualComplex J (N + 1 + 1) T.E).X n ⟶ (cone T.i₀').X n :=
  inlX T.ΦW n (n + 1) (down_rel_succ n) ≫ inrX T.i₀' n

lemma αS_tS₀ (n : ℤ) : T.αS.f n ≫ T.tS₀ n ≫ (coneMap W.pD W.pD (by simp) :
    cone (𝟙 W.D) ⟶ cone (𝟙 W.D)).f n = (coneMap W.pD W.pD (by simp) :
    cone (𝟙 W.D) ⟶ cone (𝟙 W.D)).f n := by
  apply ext_from_X (𝟙 W.D) (n - 1) n (down_rel_pred n) <;>
    simp [tS₀, LiftComplex.f_idem_assoc W.pD W.pD_idem]

lemma sS₀_βS (n : ℤ) : T.sS₀ n ≫ T.βS.f n = (dualHom J (N + 1 + 1) T.pE).f n := by
  simp [sS₀, coneFst]

lemma tS₀_sS₀_total (n : ℤ) : (T.tS₀ n ≫ T.αS.f n + T.βS.f n ≫ T.sS₀ n) ≫ T.eMS.f n =
    T.eMS.f n := by
  apply ext_from_X T.i₀' (n - 1) n (down_rel_pred n)
  · simp [tS₀, sS₀, inlX_desc_f_assoc _ _ _ _ _ (down_rel_pred n), Homotopy.ofEq,
      LiftComplex.f_idem_assoc W.pD W.pD_idem]
  · apply ext_from_X T.ΦW n (n + 1) (down_rel_succ n)
    · simp [tS₀, sS₀, coneFst, star_pE_f_idem_assoc]
    · apply ext_from_X (0 : W.D ⟶ Z0) n (n + 1) (down_rel_succ n)
      · simp [tS₀, sS₀, coneFst]
      · exact (isZero_zero V).eq_of_src _ _

lemma eMS_βS' : T.eMS ≫ T.βS = T.βS := by rw [T.eMS_βS, T.βS_eQS]

/-- **The Kar split sequence** `Cone(p_D) ⟶ Cone(i₀') ⟶ E^{N+2-*}` (`α_S`, `β_S`). -/
def splitS : KarSplit (coneMap W.pD W.pD (by simp) : cone (𝟙 W.D) ⟶ cone (𝟙 W.D)) T.eMS
    (dualHom J (N + 1 + 1) T.pE) T.αS T.βS where
  t n := T.eMS.f n ≫ T.tS₀ n ≫ (coneMap W.pD W.pD (by simp) : cone (𝟙 W.D) ⟶ cone (𝟙 W.D)).f n
  s n := (dualHom J (N + 1 + 1) T.pE).f n ≫ T.sS₀ n ≫ T.eMS.f n
  t_kar n := by
    have h₁ := congrArg (fun f ↦ f.f n) T.eMS_idem
    have h₂ := congrArg (fun f ↦ f.f n) (coneMap_idem
      (by simp : W.pD ≫ 𝟙 W.D = 𝟙 W.D ≫ W.pD) W.pD_idem W.pD_idem)
    simp only [comp_f] at h₁ h₂
    simp only [assoc, h₂, reassoc_of% h₁]
  s_kar n := by
    have h₁ := congrArg (fun f ↦ f.f n) T.eMS_idem
    have h₂ := congrArg (fun f ↦ f.f n) (dualHom_idem (J := J) (N := N + 1 + 1) T.pE_idem)
    simp only [comp_f] at h₁ h₂
    simp only [assoc, h₁, reassoc_of% h₂]
  it n := by
    have h := congrArg (fun f ↦ f.f n) T.αS_eMS
    simp only [comp_f] at h
    rw [reassoc_of% h, αS_tS₀]
  sq n := by
    have h := congrArg (fun f ↦ f.f n) T.eMS_βS'
    have h₂ := congrArg (fun f ↦ f.f n) (dualHom_idem (J := J) (N := N + 1 + 1) T.pE_idem)
    simp only [comp_f] at h h₂
    rw [assoc, assoc, h, sS₀_βS, h₂]
  total n := by
    have h₁ := congrArg (fun f ↦ f.f n) T.eKS_αS
    have h₂ := congrArg (fun f ↦ f.f n) T.αS_eMS
    have h₃ := congrArg (fun f ↦ f.f n) T.βS_eQS
    have h₄ := congrArg (fun f ↦ f.f n) T.eMS_βS'
    have h₅ := congrArg (fun f ↦ f.f n) T.eMS_idem
    simp only [comp_f] at h₁ h₂ h₃ h₄ h₅
    have e := T.tS₀_sS₀_total n
    calc (T.eMS.f n ≫ T.tS₀ n ≫ (coneMap W.pD W.pD (by simp) :
          cone (𝟙 W.D) ⟶ cone (𝟙 W.D)).f n) ≫ T.αS.f n +
        T.βS.f n ≫ (dualHom J (N + 1 + 1) T.pE).f n ≫ T.sS₀ n ≫ T.eMS.f n =
        T.eMS.f n ≫ T.tS₀ n ≫ T.αS.f n + T.βS.f n ≫ T.sS₀ n ≫ T.eMS.f n := by
          rw [assoc, assoc, h₁, ← assoc (T.βS.f n), h₃]
      _ = T.eMS.f n ≫ (T.tS₀ n ≫ T.αS.f n + T.βS.f n ≫ T.sS₀ n) ≫ T.eMS.f n := by
          simp only [comp_add, add_comp, assoc, h₂, reassoc_of% h₄]
      _ = T.eMS.f n := by rw [e, h₅]

/-- **`β_S` is a Kar equivalence** `(Cone(i₀'), p_D ⊕ p_M) ≃ (E^{N+2-*}, p_E^*)` (its kernel
`Cone(p_D)` is contractible). -/
lemma isKarEquiv_βS : IsKarEquiv T.eMS (dualHom J (N + 1 + 1) T.pE) T.βS :=
  T.splitS.isKarEquiv_q (coneMap_idem _ W.pD_idem W.pD_idem) T.eMS_idem
    (dualHom_idem T.pE_idem) (by rw [T.eKS_αS, T.αS_eMS]) (by rw [T.eMS_βS])
    T.eKS_αS T.βS_eQS W.coneSelfContr

/-! #### The target `Cone(i₁')` -/

/-- The inclusion `E_n ⟶ Cone(i₁')_n` of the `E`-coordinate of `Z_D` (any `k` with `n = k + 1`). -/
def ιT (n k : ℤ) (h : n = k + 1) : T.E.X n ⟶ (cone T.i₁').X n :=
  T.pE.f n ≫ (T.E.XIsoOfEq h).hom ≫ inrX T.i₀ (k + 1) ≫ inrX T.Φ (k + 1) ≫
    inlX T.i₁' k n (by simp; omega)

lemma ιT_eq (n k k' : ℤ) (h : n = k + 1) (h' : n = k' + 1) : T.ιT n k h = T.ιT n k' h' := by
  obtain rfl : k = k' := by omega
  rfl

/-- `i_T : E ⟶ Cone(i₁')`, `e ↦ ((0, 0, p_E e), 0)`. -/
def iT : T.E ⟶ cone T.i₁' where
  f n := T.ιT n (n - 1) (by omega)
  comm' n n' h := by
    obtain rfl : n = n' + 1 := by simp at h; omega
    rw [T.ιT_eq (n' + 1) (n' + 1 - 1) n' (by omega) rfl]
    simp only [ιT, assoc, homotopyCofiber_d, inlX_d T.i₁' (n' + 1) n' (n' - 1) (by simp)
      (by simp), comp_add, desusp_d, neg_comp, neg_neg, desuspMap_f]
    simp [inrX_d_assoc, T.pE.comm_assoc, XIsoOfEq_rfl]
    rw [XIsoOfEq_hom_naturality_assoc T.pE, d_comp_XIsoOfEq_hom_assoc]

lemma iT_f (n : ℤ) : T.iT.f n = T.ιT n (n - 1) (by omega) := rfl

@[reassoc (attr := simp)]
lemma pZ_i₁' : T.pZ ≫ T.i₁' = T.i₁' := kar_left T.pZ_idem T.i₁'_kar

@[reassoc (attr := simp)]
lemma i₁'_pM : T.i₁' ≫ T.pM = T.i₁' := kar_right T.pM_idem T.i₁'_kar

/-- `q_T = i₁' ⊕ p_M : Cone(i₁') ⟶ Cone(1_M)`. -/
abbrev qT : cone T.i₁' ⟶ cone (𝟙 T.MD) := coneMap T.i₁' T.pM (by simp)

/-- The idempotent `p_Z ⊕ p_M` of `Cone(i₁')` (the `coneIdem₁` of the trace). -/
abbrev eMT : cone T.i₁' ⟶ cone T.i₁' :=
  coneMap T.pZ T.pM (comm_of_kar T.pZ_idem T.pM_idem T.i₁'_kar)

/-- The idempotent `p_M ⊕ p_M` of `Cone(1_M)`. -/
abbrev eQT : cone (𝟙 T.MD) ⟶ cone (𝟙 T.MD) := coneMap T.pM T.pM (by simp)

lemma eMT_idem : T.eMT ≫ T.eMT = T.eMT := coneMap_idem _ T.pZ_idem T.pM_idem

lemma eQT_idem : T.eQT ≫ T.eQT = T.eQT := coneMap_idem _ T.pM_idem T.pM_idem

lemma eMT_qT : T.eMT ≫ T.qT = T.qT := by
  rw [coneMap_comp]; exact coneMap_eq_of_eq _ _ (by simp) (by simp [T.pM_idem])

lemma qT_eQT : T.qT ≫ T.eQT = T.qT := by
  rw [coneMap_comp]; exact coneMap_eq_of_eq _ _ (by simp) (by simp [T.pM_idem])

lemma pE_iT : T.pE ≫ T.iT = T.iT := by
  ext n; simp [iT_f, ιT]

lemma iT_eMT : T.iT ≫ T.eMT = T.iT := by
  ext n
  simp [iT_f, ιT, desuspMap_f, XIsoOfEq_hom_naturality_assoc T.pE]

/-- `Cone(p_M)` is contractible. -/
def eQT_contr : Homotopy T.eQT 0 :=
  homotopyCongr (coneNullHomotopy (j := 𝟙 T.MD) (j' := 𝟙 T.MD) T.pM)
    (coneMap_eq_of_eq _ _ (by simp) (by simp)) rfl

/-- The degreewise section `(a, y, 0) ↦ (a, y, 0)` of `i₁'`. -/
def σT (k : ℤ) : T.MD.X k ⟶ T.ZD.X k :=
  fstX T.ΦW (k + 1) k (down_rel_succ k) ≫ inlX T.Φ k (k + 1) (down_rel_succ k) +
    sndX T.ΦW (k + 1) ≫ fstX (0 : W.D ⟶ Z0) (k + 1) k (down_rel_succ k) ≫
      inlX T.i₀ k (k + 1) (down_rel_succ k) ≫ inrX T.Φ (k + 1)

lemma σT_i₁' (k : ℤ) : T.σT k ≫ T.i₁'.f k = T.pM.f k := by
  apply ext_from_X T.ΦW k (k + 1) (down_rel_succ k)
  · simp [σT, desuspMap_f]
  · apply ext_from_X (0 : W.D ⟶ Z0) k (k + 1) (down_rel_succ k)
    · simp [σT, desuspMap_f]
    · exact (isZero_zero V).eq_of_src _ _

/-- The degreewise retraction `((a, x, e), m) ↦ e` of `i_T`. -/
def tT₀ (n : ℤ) : (cone T.i₁').X n ⟶ T.E.X n :=
  fstX T.i₁' n (n - 1) (down_rel_pred n) ≫ sndX T.Φ (n - 1 + 1) ≫ sndX T.i₀ (n - 1 + 1) ≫
    (T.E.XIsoOfEq (by omega : n - 1 + 1 = n)).hom

/-- The degreewise section `(m', m) ↦ (σ m', m)` of `q_T`. -/
def sT₀ (n : ℤ) : (cone (𝟙 T.MD)).X n ⟶ (cone T.i₁').X n :=
  fstX (𝟙 T.MD) n (n - 1) (down_rel_pred n) ≫ T.σT (n - 1) ≫
      inlX T.i₁' (n - 1) n (down_rel_pred n) +
    sndX (𝟙 T.MD) n ≫ inrX T.i₁' n

lemma iT_tT₀ (n : ℤ) : T.iT.f n ≫ T.tT₀ n ≫ T.pE.f n = T.pE.f n := by
  simp [iT_f, ιT, tT₀, XIsoOfEq_hom_naturality_assoc T.pE]

lemma sT₀_qT (n : ℤ) : T.sT₀ n ≫ T.qT.f n = T.eQT.f n := by
  apply ext_from_X (𝟙 T.MD) (n - 1) n (down_rel_pred n)
  · have h := T.σT_i₁' (n - 1)
    simp only [desuspMap_f] at h
    simp [sT₀, reassoc_of% h]
  · simp [sT₀]

lemma tT₀_sT₀_total (n : ℤ) : (T.tT₀ n ≫ T.iT.f n + T.qT.f n ≫ T.sT₀ n) ≫ T.eMT.f n =
    T.eMT.f n := by
  apply ext_from_X T.i₁' (n - 1) n (down_rel_pred n)
  · apply ext_from_X T.Φ (n - 1) (n - 1 + 1) (down_rel_succ (n - 1))
    · simp [tT₀, sT₀, σT, iT_f, ιT, desuspMap_f]
    · apply ext_from_X T.i₀ (n - 1) (n - 1 + 1) (down_rel_succ (n - 1))
      · simp [tT₀, sT₀, σT, iT_f, ιT, desuspMap_f]
      · simp [tT₀, sT₀, σT, iT_f, ιT, desuspMap_f]
  · have h := congrArg (fun f ↦ f.f n) T.pM_idem
    simp only [comp_f, desuspMap_f] at h
    simp [tT₀, sT₀, σT, iT_f, ιT, desuspMap_f, reassoc_of% h]

/-- **The Kar split sequence** `E ⟶ Cone(i₁') ⟶ Cone(1_M)` (`i_T`, `q_T`). -/
def splitT : KarSplit T.pE T.eMT T.eQT T.iT T.qT where
  t n := T.eMT.f n ≫ T.tT₀ n ≫ T.pE.f n
  s n := T.eQT.f n ≫ T.sT₀ n ≫ T.eMT.f n
  t_kar n := by
    have h₁ := congrArg (fun f ↦ f.f n) T.eMT_idem
    simp only [comp_f] at h₁
    simp only [assoc, T.pE_idem_f, reassoc_of% h₁]
  s_kar n := by
    have h₁ := congrArg (fun f ↦ f.f n) T.eMT_idem
    have h₂ := congrArg (fun f ↦ f.f n) T.eQT_idem
    simp only [comp_f] at h₁ h₂
    simp only [assoc, h₁, reassoc_of% h₂]
  it n := by
    have h := congrArg (fun f ↦ f.f n) T.iT_eMT
    simp only [comp_f] at h
    rw [reassoc_of% h, iT_tT₀]
  sq n := by
    have h := congrArg (fun f ↦ f.f n) T.eMT_qT
    have h₂ := congrArg (fun f ↦ f.f n) T.eQT_idem
    simp only [comp_f] at h h₂
    rw [assoc, assoc, h, sT₀_qT, h₂]
  total n := by
    have h₁ := congrArg (fun f ↦ f.f n) T.pE_iT
    have h₂ := congrArg (fun f ↦ f.f n) T.iT_eMT
    have h₃ := congrArg (fun f ↦ f.f n) T.qT_eQT
    have h₄ := congrArg (fun f ↦ f.f n) T.eMT_qT
    have h₅ := congrArg (fun f ↦ f.f n) T.eMT_idem
    simp only [comp_f] at h₁ h₂ h₃ h₄ h₅
    have e := T.tT₀_sT₀_total n
    calc (T.eMT.f n ≫ T.tT₀ n ≫ T.pE.f n) ≫ T.iT.f n +
        T.qT.f n ≫ T.eQT.f n ≫ T.sT₀ n ≫ T.eMT.f n =
        T.eMT.f n ≫ T.tT₀ n ≫ T.iT.f n + T.qT.f n ≫ T.sT₀ n ≫ T.eMT.f n := by
          rw [assoc, assoc, h₁, ← assoc (T.qT.f n), h₃]
      _ = T.eMT.f n ≫ (T.tT₀ n ≫ T.iT.f n + T.qT.f n ≫ T.sT₀ n) ≫ T.eMT.f n := by
          simp only [comp_add, add_comp, assoc, h₂, reassoc_of% h₄]
      _ = T.eMT.f n := by rw [e, h₅]

/-- **`i_T` is a Kar equivalence** `(E, p_E) ≃ (Cone(i₁'), p_Z ⊕ p_M)` (its cokernel `Cone(p_M)`
is contractible). -/
lemma isKarEquiv_iT : IsKarEquiv T.pE T.eMT T.iT :=
  T.splitT.isKarEquiv_i T.pE_idem T.eMT_idem T.eQT_idem (by rw [T.pE_iT, T.iT_eMT])
    (by rw [T.eMT_qT, T.qT_eQT]) T.pE_iT T.qT_eQT T.eQT_contr

/-! #### The square and Poincaré duality of the trace -/

@[reassoc (attr := simp)]
lemma inlX_βS (k' k : ℤ) (h : (ComplexShape.down ℤ).Rel k k') :
    inlX T.i₀' k' k h ≫ T.βS.f k = 0 := by
  simp [inlX_desc_f _ _ _ _ _ h, Homotopy.ofEq]

@[reassoc (attr := simp)]
lemma inrX_βS (k : ℤ) : inrX T.i₀' k ≫ T.βS.f k =
    fstX T.ΦW (k + 1) k (down_rel_succ k) ≫ (dualHom J (N + 1 + 1) T.pE).f k := by
  simp [coneFst]

@[reassoc (attr := simp)]
lemma star_βS_star_inlX (k' k : ℤ) (h : (ComplexShape.down ℤ).Rel k k') :
    J.star (T.βS.f k) ≫ J.star (inlX T.i₀' k' k h) = 0 := by
  rw [← J.star_comp, inlX_βS, J.star_zero]

@[reassoc (attr := simp)]
lemma star_βS_star_inrX (k : ℤ) : J.star (T.βS.f k) ≫ J.star (inrX T.i₀' k) =
    T.pE.f (N + 1 + 1 - k) ≫ J.star (fstX T.ΦW (k + 1) k (down_rel_succ k)) := by
  rw [← J.star_comp, inrX_βS, J.star_comp, dualHom_f, J.star_star]

@[reassoc (attr := simp)]
lemma star_fstX_star_i₁' (k : ℤ) : J.star (fstX T.ΦW (k + 1) k (down_rel_succ k)) ≫
    J.star (T.i₁'.f k) = J.star (J.star (T.pE.f (N + 1 + 1 - k))) ≫
      J.star (fstX T.Φ (k + 1) k (down_rel_succ k)) := by
  rw [← J.star_comp, ← J.star_comp, desuspMap_f, coneMap_f_fstX, dualHom_f]

/-- `l = -(bidual ≫ p_E) : E^{**} ⟶ E`. -/
abbrev lT : dualComplex J (N + 1 + 1) (dualComplex J (N + 1 + 1) T.E) ⟶ T.E :=
  -((bidual J (N + 1 + 1) T.E).hom ≫ T.pE)

lemma trace_square : dualHom J (N + 1 + 1) T.βS ≫ (T.trace hE).Ψ = T.lT ≫ T.iT := by
  ext r
  apply ext_to_X T.i₁' r (r - 1) (down_rel_pred r)
  · simp [Ψ_f, ΨF, iT_f, ιT, trace_top]
    rw [relTop_δφZ]
    erw [R_cast_assoc (h := by omega)]
    rw [star_fstX_R_assoc]
    simp only [desuspMap_f, Linear.units_smul_comp, assoc, Linear.comp_units_smul]
    rw [← reassoc_of% (f_comp_eqToHom T.pE (sub_sub_cancel (N + 1 + 1) r))]
    simp only [XIsoOfEq, eqToIso.hom, eqToHom_trans_assoc, ← Units.neg_smul]
    congr 1
    · simp only [τ]
      triad_sign_tac
    · simp only [inrX_coneMap_f, inrX_coneMap_f_assoc]
      rw [← reassoc_of% (f_comp_eqToHom T.pE
        (show N + 1 + 1 - (N + 1 + 1 - r) = r - 1 + 1 by omega)), T.pE_idem_f_assoc]
  · simp [Ψ_f, ΨF, iT_f, ιT, trace_top]

omit [HasBinaryBiproducts V] [HasFiniteBiproducts V] in
lemma isKarEquiv_lT :
    IsKarEquiv (dualHom J (N + 1 + 1) (dualHom J (N + 1 + 1) T.pE)) T.pE T.lT :=
  ((isKarEquiv_bidual T.pE_idem).comp (KarHtpyEquiv.refl T.pE_idem).isKarEquiv
    (dualHom_idem (dualHom_idem T.pE_idem)) T.pE_idem T.pE_idem).neg

/-- **The top of the trace is Poincaré**: `Ψ : Cone(i₀')^{N+2-*} ⟶ Cone(i₁')` is a Kar
equivalence.  Both sides are Kar-equivalent to `E` (`β_S^*` and `i_T`; the complements
`Cone(p_D)^*` and `Cone(p_M)` are contractible), and `β_S^* Ψ = -(bidual) i_T`. -/
theorem trace_isPoincareTop : (T.trace hE).IsPoincareTop := by
  have h₁ : IsKarEquiv (dualHom J (N + 1 + 1) (dualHom J (N + 1 + 1) T.pE))
      (dualHom J (N + 1 + 1) T.eMS) (dualHom J (N + 1 + 1) T.βS) := T.isKarEquiv_βS.dualHom
  have h₂ := T.isKarEquiv_lT.comp T.isKarEquiv_iT (dualHom_idem (dualHom_idem T.pE_idem))
    T.pE_idem T.eMT_idem
  rw [← T.trace_square hE] at h₂
  have hβ : T.eMS ≫ T.βS ≫ dualHom J (N + 1 + 1) T.pE = T.βS := by
    rw [T.βS_eQS, T.eMS_βS']
  exact IsKarEquiv.of_comp_left h₁ (dualHom_kar hβ) h₂ (T.trace hE).Ψ_kar
    (dualHom_idem (dualHom_idem T.pE_idem)) (dualHom_idem T.eMS_idem) T.eMT_idem

/-- **The trace is a Poincaré triad** `(M; W, Z; P)`: a cobordism rel `P` from `W` to the new
face `Z` (module 10, `p_E` in `[1, N + 2]`). -/
theorem trace_isPoincare (hW : W.IsPoincare) : (T.trace hE).IsPoincare :=
  ⟨hW, T.relBdData_isPoincare hW hE, T.trace_isPoincareTop hE⟩

/-- `W` and the new face `Z = T.relBd` are cobordant rel `P`. -/
theorem relCobordant_relBd (hW : W.IsPoincare) :
    (W.toPairOn hW).RelCobordant (T.relBd hW hE) :=
  ⟨T.trace hE, T.trace_isPoincareTop hE⟩

end TriadOn

end Trace

/-! ### Cutting the bottom degree of a desuspended complex -/

section BotTrunc

variable {K : ChainComplex V ℤ} (p : K ⟶ K) (s : K.X 0 ⟶ K.X 1)

/-- The homotopy family supported in degrees `0 ⟶ 1`, given by `-s`. -/
def botFam' (i j : ℤ) (_ : (ComplexShape.down ℤ).Rel j i) : K.X i ⟶ K.X j :=
  if h : i = 0 then (K.XIsoOfEq h).hom ≫ (-s) ≫
    (K.XIsoOfEq (by simp at *; omega : (1 : ℤ) = j)).hom else 0

omit [HasBinaryBiproducts V] in
lemma botFam'_zero : botFam' s 0 1 (by simp) = -s := by simp [botFam']

omit [HasBinaryBiproducts V] in
lemma botFam'_ne {i j : ℤ} (h : (ComplexShape.down ℤ).Rel j i) (hi : i ≠ 0) :
    botFam' s i j h = 0 := by simp [botFam', hi]

/-- `x = p - (d s + s d)`-type modification, homotopic to `p`. -/
@[implicit_reducible]
def botX' : K ⟶ K := Homotopy.nullHomotopicMap' (botFam' s) + p

/-- The homotopy `x ≃ p`. -/
def botHomotopy' : Homotopy (botX' p s) p :=
  homotopyCongr ((Homotopy.nullHomotopy' (botFam' s)).add (Homotopy.refl p)) rfl (zero_add _)

omit [HasBinaryBiproducts V] in
lemma botX'_f_zero (hsd : s ≫ K.d 1 0 = p.f 0) : (botX' p s).f 0 = 0 := by
  rw [botX', add_f_apply, Homotopy.nullHomotopicMap'_f (show (ComplexShape.down ℤ).Rel 1 0 by simp)
    (show (ComplexShape.down ℤ).Rel 0 (-1) by simp), botFam'_ne s _ (by omega : (-1 : ℤ) ≠ 0),
    botFam'_zero, comp_zero, zero_add, neg_comp, hsd, neg_add_cancel]

omit [HasBinaryBiproducts V] in
lemma botX'_f_neg (hneg : ∀ k, k < 0 → p.f k = 0) {k : ℤ} (hk : k < 0) : (botX' p s).f k = 0 := by
  rw [botX', add_f_apply, Homotopy.nullHomotopicMap'_f (show (ComplexShape.down ℤ).Rel (k + 1) k by
    simp) (show (ComplexShape.down ℤ).Rel k (k - 1) by simp), botFam'_ne s _ (by omega),
    botFam'_ne s _ (by omega), hneg k hk]
  simp

omit [HasBinaryBiproducts V] in
lemma botHomotopy'_kar (hs : p.f 0 ≫ s ≫ p.f 1 = s) (i j : ℤ) :
    p.f i ≫ (botHomotopy' p s).hom i j ≫ p.f j = (botHomotopy' p s).hom i j := by
  have e : (botHomotopy' p s).hom i j = if h : i + 1 = j then botFam' s i j h else 0 := by
    by_cases h : i + 1 = j <;> simp [botHomotopy', Homotopy.nullHomotopy'_hom, h]
  rw [e]
  split_ifs with h
  · by_cases hi : i = 0
    · subst hi
      obtain rfl : j = 1 := by omega
      rw [botFam'_zero, neg_comp, comp_neg, hs]
    · rw [botFam'_ne s h hi]; simp
  · simp

omit [HasBinaryBiproducts V] in
/-- **Cutting the bottom**: if `(K, p)` vanishes below `0` and the bottom differential is split
by `s` (`s d = p_0`), then `(Σ⁻¹K, Σ⁻¹p)` (which lives in degrees `≥ -1`) is Kar-equivalent to
`(Σ⁻¹K, q)` with `q ≤ Σ⁻¹p` vanishing below `0`. -/
theorem exists_truncBot (hp : p ≫ p = p) (hneg : ∀ k, k < 0 → p.f k = 0)
    (hs : p.f 0 ≫ s ≫ p.f 1 = s) (hsd : s ≫ K.d 1 0 = p.f 0) :
    ∃ q : desusp K ⟶ desusp K, q ≫ q = q ∧ (∀ r, r < 0 → q.f r = 0) ∧ q ≫ desuspMap p = q ∧
      Nonempty (KarHtpyEquiv (desuspMap p) q) := by
  let H : Homotopy (desuspMap (botX' p s)) (desuspMap p) := desuspHomotopy (botHomotopy' p s)
  have hp' : desuspMap p ≫ desuspMap p = desuspMap p := by rw [← desuspMap_comp, hp]
  have hH : ∀ i j, (desuspMap p).f i ≫ H.hom i j ≫ (desuspMap p).f j = H.hom i j := fun i j ↦ by
    show p.f (i + 1) ≫ (-(botHomotopy' p s).hom (i + 1) (j + 1)) ≫ p.f (j + 1) =
      -(botHomotopy' p s).hom (i + 1) (j + 1)
    rw [neg_comp, comp_neg, botHomotopy'_kar p s hs]
  have hx : ∀ r, r < 0 → (desuspMap (botX' p s)).f r = 0 := fun r hr ↦ by
    show (botX' p s).f (r + 1) = 0
    rcases lt_or_eq_of_le (show r + 1 ≤ 0 by omega) with h | h
    · exact botX'_f_neg p s hneg h
    · rw [h]; exact botX'_f_zero p s hsd
  exact ⟨truncLo H 0, truncLo_idem hp' hH hx, fun r hr ↦ truncLo_f_below H (hx r hr) hr,
    truncLo_comp_p hp' hH hx, ⟨truncLoEquiv hp' hH hx⟩⟩

end BotTrunc

/-! ### Raw Poincaré pairs (no support condition) and their transport -/

/-- A strictly symmetric Poincaré pair on the boundary `P` **without** the support condition on
the top (the new face `Z_D` of the relative boundary construction lives in `[-1, N + 2]`). -/
structure RelRawPair (P : SymPoincare J N) where
  D : ChainComplex V ℤ
  pD : D ⟶ D
  pD_idem : pD ≫ pD = pD
  j : P.C ⟶ D
  j_kar : P.p ≫ j ≫ pD = j
  δφ : Homotopy (dualHom J N j ≫ P.φ ≫ j) 0
  δφ_kar : ∀ r r', (dualHom J N pD).f r ≫ δφ.hom r r' ≫ pD.f r' = δφ.hom r r'
  symm : IsSymmHomotopy J N δφ
  poincare : IsKarEquiv (dualHom J (N + 1) (coneMap P.p pD (comm_of_kar P.p_idem pD_idem j_kar)))
    pD (relDuality δφ)

namespace RelRawPair

variable {P : SymPoincare J N} (X : RelRawPair P)

/-- A raw pair whose top is concentrated in `[0, N + 1]` is a Poincaré pair. -/
@[simps, implicit_reducible]
def toPairOn (hs : SupportedIn X.pD 0 (N + 1)) : PairOn P :=
  ⟨X.D, X.pD, X.pD_idem, hs, X.j, X.j_kar, X.δφ, X.δφ_kar, X.symm, X.poincare⟩

lemma j_comp_pD : X.j ≫ X.pD = X.j := kar_right X.pD_idem X.j_kar

lemma p_comp_j : P.p ≫ X.j = X.j := kar_left P.p_idem X.j_kar

variable {D' : ChainComplex V ℤ} {pD' : D' ⟶ D'} (e : KarHtpyEquiv X.pD pD')

/-- The relative structure `f δφ f^*` on `j f`. -/
def transportDδφ : Homotopy (dualHom J N (X.j ≫ e.f) ≫ P.φ ≫ X.j ≫ e.f) 0 :=
  homotopyCongr ((X.δφ.compRight e.f).compLeft (dualHom J N e.f)) (by simp) (by simp)

lemma transportDδφ_hom (r r' : ℤ) : (X.transportDδφ e).hom r r' =
    (dualHom J N e.f).f r ≫ X.δφ.hom r r' ≫ e.f.f r' := rfl

lemma relDuality_transportDδφ (hc : P.p ≫ X.j ≫ e.f = X.j ≫ e.f) :
    relDuality (X.transportDδφ e) =
      dualHom J (N + 1) (coneMap P.p e.f hc) ≫ relDuality X.δφ ≫ e.f := by
  ext r
  have hφ : J.star (P.p.f (N - r)) ≫ P.φ.f r = P.φ.f r := by
    rw [← dualHom_f, ← comp_f, P.dualHom_p_comp_φ]
  simp [star_coneMap_f hc _ _ (down_rel_sub N r), relTop, transportDδφ_hom, reassoc_of% hφ,
    add_comm, star_f_XIsoOfEq_assoc]

/-- The source `(Cone(j)^{N+1-*}, (p ⊕ p_D)^*)` of `Ψ` lives in `[-1, N + 1]` if `p_D` lives in
`[0, N + 2]`. -/
lemma supportedIn_coneIdem (hs : SupportedIn X.pD 0 (N + 1 + 1)) :
    SupportedIn (dualHom J (N + 1) (coneMap P.p X.pD (comm_of_kar P.p_idem X.pD_idem X.j_kar)))
      (-1) (N + 1) := by
  intro r hr
  rw [dualHom_f, coneMap_f _ (N + 1 - r) (N - r) (down_rel_sub N r)]
  simp [P.support (N - r) (by omega), hs (N + 1 - r) (by omega)]

variable [HasFiniteBiproducts V]

/-- **Transport of a raw pair along a target equivalence** `e : (D, p_D) ≃ (D', p_D')`. -/
@[simps, implicit_reducible]
def transportD (hpD' : pD' ≫ pD' = pD') : RelRawPair P where
  D := D'
  pD := pD'
  pD_idem := hpD'
  j := X.j ≫ e.f
  j_kar := by simp [reassoc_of% X.p_comp_j]
  δφ := X.transportDδφ e
  δφ_kar r r' := by
    have h₁ : (dualHom J N pD').f r ≫ (dualHom J N e.f).f r = (dualHom J N e.f).f r := by
      rw [← comp_f, ← dualHom_comp, e.fp]
    have h₂ : e.f.f r' ≫ pD'.f r' = e.f.f r' := by rw [← comp_f, e.fp]
    simp only [transportDδφ_hom, assoc, h₂, reassoc_of% h₁]
  symm := by
    rw [IsSymmHomotopy, transposeHomotopy_hom]
    have e₁ : (X.transportDδφ e).hom =
        fun r r' ↦ (dualHom J N e.f).f r ≫ X.δφ.hom r r' ≫ e.f.f r' := rfl
    rw [e₁, transposeHomFamily_conj', transposeHomFamily_eq X.symm]
  poincare := by
    have hc : P.p ≫ X.j ≫ e.f = X.j ≫ e.f := by simp [reassoc_of% X.p_comp_j]
    rw [relDuality_transportDδφ X e hc]
    have hC := isKarEquiv_coneMap P.p_idem X.pD_idem P.p_idem hpD' X.j_kar
      (j' := X.j ≫ e.f) (by simp [reassoc_of% X.p_comp_j]) (by simp) e.f_kar hc
      (KarHtpyEquiv.refl P.p_idem).isKarEquiv e.isKarEquiv
    exact hC.dualHom.comp (X.poincare.comp e.isKarEquiv
      (dualHom_idem (coneMap_idem _ P.p_idem X.pD_idem)) X.pD_idem hpD')
      (dualHom_idem (coneMap_idem _ P.p_idem hpD'))
      (dualHom_idem (coneMap_idem _ P.p_idem X.pD_idem)) hpD'

/-- The Kar equivalence `Ψ : (Cone(j)^{N+1-*}, (p ⊕ p_D)^*) ≃ (D, p_D)`. -/
def ΨEquiv : KarHtpyEquiv
    (dualHom J (N + 1) (coneMap P.p X.pD (comm_of_kar P.p_idem X.pD_idem X.j_kar))) X.pD :=
  KarHtpyEquiv.ofIsKarEquiv X.poincare
    (relDuality_kar X.δφ X.pD_idem _ X.j_comp_pD P.dualHom_p_comp_φ X.δφ_kar)
    (dualHom_idem (coneMap_idem _ P.p_idem X.pD_idem)) X.pD_idem

/-- **Cutting the top by Poincaré duality**: if `p_D` lives in `[0, N + 2]`, then `(D, p_D)` is
Kar-equivalent to `(D, q)` with `q ≤ p_D` concentrated in `[0, N + 1]` (`(D, p_D)` is equivalent
to `(Cone(j)^{N+1-*}, (p ⊕ p_D)^*)`, which lives in `[-1, N + 1]`). -/
abbrev truncTopIdem (hs : SupportedIn X.pD 0 (N + 1 + 1)) : X.D ⟶ X.D :=
  X.ΨEquiv.truncIdem X.pD_idem (-1) (N + 1) (X.supportedIn_coneIdem hs)

omit [HasFiniteBiproducts V] in
lemma truncTopIdem_idem (hs : SupportedIn X.pD 0 (N + 1 + 1)) :
    X.truncTopIdem hs ≫ X.truncTopIdem hs = X.truncTopIdem hs :=
  X.ΨEquiv.truncIdem_idem X.pD_idem _ _ _

omit [HasFiniteBiproducts V] in
lemma supportedIn_truncTopIdem (hs : SupportedIn X.pD 0 (N + 1 + 1)) :
    SupportedIn (X.truncTopIdem hs) 0 (N + 1) := by
  intro r hr
  rcases hr with hr | hr
  · show (X.ΨEquiv.truncIdem X.pD_idem (-1) (N + 1) (X.supportedIn_coneIdem hs)).f r = 0
    rw [← X.ΨEquiv.p_comp_truncIdem X.pD_idem (-1) (N + 1) (X.supportedIn_coneIdem hs), comp_f,
      hs r (Or.inl hr), zero_comp]
  · exact X.ΨEquiv.supportedIn_truncIdem X.pD_idem _ _ _ r (Or.inr hr)

/-- The equivalence `(D, p_D) ≃ (D, q)`. -/
def truncTopEquiv (hs : SupportedIn X.pD 0 (N + 1 + 1)) : KarHtpyEquiv X.pD (X.truncTopIdem hs) :=
  X.ΨEquiv.symm.trans (X.ΨEquiv.trunc X.pD_idem _ _ _)

/-- **The top-truncated pair**: a Poincaré pair on `P` (support `[0, N + 1]`). -/
def truncTop (hs : SupportedIn X.pD 0 (N + 1 + 1)) : PairOn P :=
  (X.transportD (X.truncTopEquiv hs) (X.truncTopIdem_idem hs)).toPairOn
    (X.supportedIn_truncTopIdem hs)

@[simp]
lemma truncTop_pD (hs : SupportedIn X.pD 0 (N + 1 + 1)) :
    (X.truncTop hs).pD = X.truncTopIdem hs := rfl

end RelRawPair

/-! ### The relative boundary construction in general degrees -/

namespace TriadOn

variable {P : SymPoincare J N} {W : PairData P} (T : TriadOn W (PairData.zero P))

/-- The idempotent `p_E^* ⊕ p_D ⊕ p_E` of `Cone(Φ)` (so `p_Z = Σ⁻¹ pZc`). -/
abbrev pZc : cone T.Φ ⟶ cone T.Φ := coneMap (dualHom J (N + 1 + 1) T.pE) T.coneIdem₀ T.Φ_comm

lemma pZc_idem : T.pZc ≫ T.pZc = T.pZc :=
  coneMap_idem _ (dualHom_idem T.pE_idem) (coneMap_idem _ W.pD_idem T.pE_idem)

lemma pZc_f_neg {k : ℤ} (hk : k < 0) : T.pZc.f k = 0 := by
  have h₁ : T.pE.f (N + 1 + 1 - (k - 1)) = 0 := T.support _ (by omega)
  have h₂ : W.pD.f (k - 1) = 0 := W.support _ (by omega)
  have h₃ : T.pE.f k = 0 := T.support _ (by omega)
  rw [coneMap_f _ k (k - 1) (by simp)]
  simp [coneMap_f _ k (k - 1) (by simp), h₁, h₂, h₃]

lemma pZc_f_zero : T.pZc.f 0 =
    sndX T.Φ 0 ≫ sndX T.i₀ 0 ≫ T.pE.f 0 ≫ inrX T.i₀ 0 ≫ inrX T.Φ 0 := by
  have h₁ : T.pE.f (N + 1 + 1 - -1) = 0 := T.support _ (by omega)
  have h₂ : W.pD.f (-1) = 0 := W.support _ (by omega)
  rw [coneMap_f _ 0 (-1) (by simp)]
  simp [coneMap_f _ 0 (-1) (by simp), h₁, h₂]

variable (a : T.E.X 0 ⟶ T.E.X (N + 1 + 1 - 0)) (b : T.E.X 0 ⟶ W.D.X 0) (c : T.E.X 0 ⟶ T.E.X 1)

/-- The bottom contraction of `Cone(Φ)`: `e ↦ (a e, b e, c e)` on `E_0` (compressed). -/
def botS : (cone T.Φ).X 0 ⟶ (cone T.Φ).X 1 :=
  T.pZc.f 0 ≫ sndX T.Φ 0 ≫ sndX T.i₀ 0 ≫ (a ≫ inlX T.Φ 0 1 (by simp) +
    b ≫ inlX T.i₀ 0 1 (by simp) ≫ inrX T.Φ 1 + c ≫ inrX T.i₀ 1 ≫ inrX T.Φ 1) ≫ T.pZc.f 1

lemma botS_kar : T.pZc.f 0 ≫ T.botS a b c ≫ T.pZc.f 1 = T.botS a b c := by
  simp only [botS, ← assoc, idem_f T.pZc_idem]
  simp only [assoc, idem_f T.pZc_idem]

lemma botS_d (hab : T.pE.f 0 ≫ (a ≫ T.top 0 + b ≫ T.i₀.f 0 + c ≫ T.E.d 1 0) ≫ T.pE.f 0 =
    T.pE.f 0) : T.botS a b c ≫ (cone T.Φ).d 1 0 = T.pZc.f 0 := by
  have h1 : T.pZc.f 1 ≫ (cone T.Φ).d 1 0 = (cone T.Φ).d 1 0 ≫ T.pZc.f 0 := T.pZc.comm 1 0
  have key : (a ≫ inlX T.Φ 0 1 (by simp) + b ≫ inlX T.i₀ 0 1 (by simp) ≫ inrX T.Φ 1 +
      c ≫ inrX T.i₀ 1 ≫ inrX T.Φ 1) ≫ (cone T.Φ).d 1 0 ≫ sndX T.Φ 0 ≫ sndX T.i₀ 0 =
      a ≫ T.top 0 + b ≫ T.i₀.f 0 + c ≫ T.E.d 1 0 := by
    simp [d_sndX_assoc T.Φ 1 0 (by simp), d_sndX T.i₀ 1 0 (by simp), add_assoc]
  have hp0 : T.pZc.f 0 ≫ sndX T.Φ 0 ≫ sndX T.i₀ 0 = sndX T.Φ 0 ≫ sndX T.i₀ 0 ≫ T.pE.f 0 := by
    rw [pZc_f_zero]; simp
  calc T.botS a b c ≫ (cone T.Φ).d 1 0 = (T.pZc.f 0 ≫ sndX T.Φ 0 ≫ sndX T.i₀ 0) ≫
        ((a ≫ inlX T.Φ 0 1 (by simp) + b ≫ inlX T.i₀ 0 1 (by simp) ≫ inrX T.Φ 1 +
          c ≫ inrX T.i₀ 1 ≫ inrX T.Φ 1) ≫ (cone T.Φ).d 1 0 ≫ sndX T.Φ 0 ≫ sndX T.i₀ 0) ≫
          T.pE.f 0 ≫ inrX T.i₀ 0 ≫ inrX T.Φ 0 := by
        simp only [botS, assoc]
        rw [h1, pZc_f_zero]
    _ = T.pZc.f 0 := by
        rw [key, hp0, assoc, assoc, reassoc_of% hab, pZc_f_zero]

section General

variable [HasFiniteBiproducts V]

/-- The new face as a raw Poincaré pair (`Z_D` in `[-1, N + 2]`, no support condition). -/
@[simps, implicit_reducible]
def relBdRaw (hW : W.IsPoincare) : RelRawPair P where
  D := T.ZD
  pD := T.pZ
  pD_idem := T.pZ_idem
  j := T.jZ
  j_kar := T.jZ_kar
  δφ := T.δφZ
  δφ_kar := T.δφZ_kar
  symm := T.δφZ_symm
  poincare := T.isKarEquiv_δφZ hW

/-- **The relative boundary construction in general degrees** (`E` in `[0, N + 2]`): if the
bottom differential `E^{N+2} ⊕ D_0 ⊕ E_1 ⟶ E_0` of `Z_D` is Kar-split (`hab`; the relative
"connectivity" condition, cf. `QuotPoincare.exists_flat`), then there is a Poincaré pair `Z` on
`P` (support `[0, N + 1]`) with `(Z_D, p_Z) ≃ (Z.D, Z.p_D)`: cut the bottom of `Z_D` by the
splitting (`exists_truncBot`), transport, and cut the top by Poincaré duality
(`RelRawPair.truncTop`). -/
theorem exists_relBd (hW : W.IsPoincare)
    (hab : T.pE.f 0 ≫ (a ≫ T.top 0 + b ≫ T.i₀.f 0 + c ≫ T.E.d 1 0) ≫ T.pE.f 0 = T.pE.f 0) :
    ∃ Z : PairOn P, Nonempty (KarHtpyEquiv T.pZ Z.pD) := by
  obtain ⟨q₁, hq₁, hneg, hle, ⟨e₁⟩⟩ := exists_truncBot T.pZc (T.botS a b c) T.pZc_idem
    (fun k hk ↦ T.pZc_f_neg hk) (T.botS_kar a b c) (T.botS_d a b c hab)
  have hs₁ : SupportedIn q₁ 0 (N + 1 + 1) := by
    intro r hr
    rcases hr with hr | hr
    · exact hneg r hr
    · rw [← hle, comp_f, T.pZ_support T.support le_rfl (by omega) r (Or.inr (by omega)),
        comp_zero]
  let X₁ := (T.relBdRaw hW).transportD e₁ hq₁
  exact ⟨X₁.truncTop hs₁, ⟨e₁.trans (X₁.truncTopEquiv hs₁)⟩⟩

end General

end TriadOn

/-! ### Contractibility modulo `U` -/

namespace TriadOn

variable {A : InvCat} {F : KaroubiFiltration A} {P : SymPoincare A.inv N} {W : PairData P}
  (T : TriadOn W (PairData.zero P))

variable (F) in
/-- The top of the triad with empty second face is **Poincaré modulo `U`**: `Ψ₀` is a Kar
equivalence in `Kar(A/U)`. -/
def IsPoincareTopMod : Prop :=
  IsKarEquiv (dualHom F.quot.inv (N + 1 + 1) (F.projF.mapH T.coneIdem₀)) (F.projF.mapH T.pE)
    (F.projF.mapDual T.Ψ₀)

/-- If the top is Poincaré modulo `U`, then `Φ = TΨ₀` is a Kar equivalence in `A/U`. -/
lemma isKarEquiv_mapH_Φ (hT : T.IsPoincareTopMod F) :
    IsKarEquiv (F.projF.mapH (dualHom A.inv (N + 1 + 1) T.pE)) (F.projF.mapH T.coneIdem₀)
      (F.projF.mapH T.Φ) := by
  have hc : F.projF.mapH T.coneIdem₀ ≫ F.projF.mapH T.coneIdem₀ = F.projF.mapH T.coneIdem₀ := by
    rw [← Functor.map_comp, coneMap_idem _ W.pD_idem T.pE_idem]
  have he : F.projF.mapH T.pE ≫ F.projF.mapH T.pE = F.projF.mapH T.pE := by
    rw [← Functor.map_comp, T.pE_idem]
  have h₁ := IsKarEquiv.transposeHom hc he hT
  rw [InvFunctor.transposeHom_mapDual] at h₁
  have h₂ := h₁.conjIso (F.projF.mapDualIso (N + 1 + 1) T.E).symm
  have e₁ : (F.projF.mapDualIso (N + 1 + 1) T.E).symm.inv ≫ dualHom F.quot.inv (N + 1 + 1)
      (F.projF.mapH T.pE) ≫ (F.projF.mapDualIso (N + 1 + 1) T.E).symm.hom =
      F.projF.mapH (dualHom A.inv (N + 1 + 1) T.pE) := by
    rw [F.projF.dualHom_mapH]; simp
  have e₂ : (F.projF.mapDualIso (N + 1 + 1) T.E).symm.inv ≫
      F.projF.mapDual (transposeHom A.inv (N + 1 + 1) T.Ψ₀) = F.projF.mapH T.Φ := by
    rw [F.projF.mapDual_eq]; simp [Φ]
  rwa [e₁, e₂] at h₂

/-- **The new face is contractible modulo `U`** if the top is Poincaré modulo `U`. -/
theorem contractibleMod_pZ (hT : T.IsPoincareTopMod F) : F.ContractibleMod T.pZ :=
  KaroubiFiltration.contractibleMod_desusp_cone (dualHom_idem T.pE_idem)
    (coneMap_idem _ W.pD_idem T.pE_idem) T.Φ_kar (T.isKarEquiv_mapH_Φ hT)

end TriadOn

/-! ### Supports: the new face over `U` -/

namespace TriadOn

variable {A : InvCat} (F : KaroubiFiltration A) {P : SymPoincare A.inv N} {W : PairData P}
  (T : TriadOn W (PairData.zero P))

/-- **Domination of a face**: a Poincaré pair `Z` on `P` (all chain objects of `P` in `U`) whose
top is contractible modulo `U` makes `P` null-cobordant over `Kar(U)`: transport `Z` to the Kar(U)
model of its top (`exists_subModel`, `SymPair.transportD`) and lift (`SymPair.nullCobordant_lift`). -/
theorem _root_.HSFormal.LTheory.PairOn.nullCobordant_lift_of_contractibleMod (Z : PairOn P)
    (hP : ∀ r, F.U (P.C.X r)) (hc : F.ContractibleMod Z.pD) :
    NullCobordant (P.lift (U := F.U) hP) := by
  obtain ⟨M⟩ := KaroubiFiltration.exists_subModel Z.pD_idem Z.support hc
  have hp' : F.inclI.mapH M.e ≫ F.inclI.mapH M.e = F.inclI.mapH M.e := by
    rw [← Functor.map_comp, M.e_idem]
  have hs' : SupportedIn (F.inclI.mapH M.e) 0 (N + 1) := fun r hr ↦ by
    change F.inclI.F.map (M.e.f r) = 0
    rw [M.support r hr, Functor.map_zero]
  exact (Z.toPair.transportD M.equiv hp' hs').nullCobordant_lift hP fun r ↦ (M.X.X r).2

/-- **The boundary is null-cobordant over `Kar(U)`** (the consumer form for (L2), `p_E` in
`[1, N + 2]`): if `P` has all chain objects in `U`, `W` is a Poincaré pair on `P`, and the triad
`T = (E; W, ∅; P)` is Poincaré modulo `U`, then the new face `T.relBd` (a Poincaré pair on `P`,
contractible modulo `U`) dominated by `U` is a null-cobordism of `P` in `U`. -/
theorem nullCobordant_lift_of_relBd (hP : ∀ r, F.U (P.C.X r)) (hW : W.IsPoincare)
    (hT : T.IsPoincareTopMod F) (hE : SupportedIn T.pE 1 (N + 1 + 1)) :
    NullCobordant (P.lift (U := F.U) hP) :=
  (T.relBd hW hE).nullCobordant_lift_of_contractibleMod F hP (T.contractibleMod_pZ hT)

/-- **The boundary is null-cobordant over `Kar(U)`**, general degrees (`p_E` in `[0, N + 2]`,
bottom splitting `hab` of the new face, see `exists_relBd`). -/
theorem nullCobordant_lift_of_relBd' (hP : ∀ r, F.U (P.C.X r)) (hW : W.IsPoincare)
    (hT : T.IsPoincareTopMod F) (a : T.E.X 0 ⟶ T.E.X (N + 1 + 1 - 0)) (b : T.E.X 0 ⟶ W.D.X 0)
    (c : T.E.X 0 ⟶ T.E.X 1)
    (hab : T.pE.f 0 ≫ (a ≫ T.top 0 + b ≫ T.i₀.f 0 + c ≫ T.E.d 1 0) ≫ T.pE.f 0 = T.pE.f 0) :
    NullCobordant (P.lift (U := F.U) hP) := by
  obtain ⟨Z, ⟨e⟩⟩ := T.exists_relBd a b c hW hab
  exact Z.nullCobordant_lift_of_contractibleMod F hP ((T.contractibleMod_pZ hT).of_karHtpyEquiv e)

end TriadOn


/-! ### Addendum to the relative cascade: killing the boundary of the frozen boundary -/

namespace KaroubiFiltration

variable {A : InvCat} {F : KaroubiFiltration A} {N : ℤ}

/-- **Relative cascades killing a further `I_U`-family** (addendum to `RelLift.nonempty_cascade`):
for maps `k_r : K_r ⟶ X̃_r` factoring through `U`, the relative cascade can be chosen with
`k_r ≫ πU = 0` in every degree. -/
theorem RelLift.exists_cascade_kill (R : F.RelLift N) {K : ℤ → A} (k : ∀ r, K r ⟶ R.X r)
    (hk : ∀ r, FactorsThrough F.U (k r)) : ∃ c : R.Cascade, ∀ r, k r ≫ (c.σ r).πU = 0 := by
  obtain ⟨c, hc⟩ := R.toSymLift.exists_cascade_with
    (fun r τ ↦ ((R.j (r + 1) ≫ R.d (r + 1) r - R.B.d (r + 1) r ≫ R.j r) ≫ τ.πU = 0 ∧
      (A.inv.star (R.j (N - r)) ≫ R.ψ r ≫ R.j r -
        (R.dualD r (r - 1) ≫ R.H (r - 1) r + R.H r (r + 1) ≫ R.d (r + 1) r)) ≫ τ.πU = 0) ∧
      k r ≫ τ.πU = 0)
    fun r ↦ ((eventually_comp_πU (R.j_comm _ _)).and (eventually_comp_πU (R.H_comm r))).and
      (eventually_comp_πU (hk r))
  refine ⟨⟨c, fun i k ↦ ?_, fun r ↦ (hc r).1.2⟩, fun r ↦ (hc r).2⟩
  by_cases h : i = k + 1
  · subst h; exact (hc k).1.1
  · rw [R.shape i k (by simp; omega), R.B.shape i k (by simp; omega)]; simp

/-- **The boundary of the frozen boundary dies** (the `hi : j_W i = 0` input of `TriadOn.ofRel`):
if `g : C ⟶ B` has source with all objects in `U` (e.g. `g = j_W : ∂W ⟶ W`, `∂W` in `U`), the
relative cascade can be chosen so that `g ≫ j'' = 0` on the nose. -/
theorem RelLift.exists_cascade_comp_jHom (R : F.RelLift N) {C : ChainComplex A ℤ} (g : C ⟶ R.B)
    (hC : ∀ r, F.U (C.X r)) : ∃ c : R.Cascade, g ≫ c.jHom = 0 := by
  obtain ⟨c, hc⟩ := R.exists_cascade_kill (fun r ↦ g.f r ≫ R.j r)
    fun r ↦ by simpa using FactorsThrough.of_mem (hC r) (𝟙 _) (g.f r ≫ R.j r)
  exact ⟨c, by ext r; simpa using hc r⟩

end KaroubiFiltration

/-! ### The top modulo `U` as a pair of `A/U` -/

namespace TriadOn

variable {A : InvCat} {F : KaroubiFiltration A} {N : ℤ} {P : SymPoincare A.inv N}
  {W : PairData P} (T : TriadOn W (PairData.zero P))

variable (F) in
/-- The closed `(N+1)`-dimensional complex `W/U` of `A/U` (the face `W` with its boundary `P`
killed). -/
abbrev quotBd (hW : W.IsPoincare) (hP : ∀ r, F.U (P.C.X r)) : SymPoincare F.quot.inv (N + 1) :=
  (W.toPairOn hW).toPair.toQuot F hP

lemma quotBd_φ_f (hW : W.IsPoincare) (hP : ∀ r, F.U (P.C.X r)) (r : ℤ) :
    (quotBd F hW hP).φ.f r = F.proj.F.map (relTop W.δφ r) :=
  SymPair.toClosed_φ_f _ _ _ r

lemma quot_triadCycle (hW : W.IsPoincare) (hP : ∀ r, F.U (P.C.X r)) :
    (F.proj.mapDualIso (N + 1) T.E).inv ≫
      F.proj.mapH (triadCycle W (PairData.zero P) T.i₀ T.i₁ T.comm) =
    dualHom F.quot.inv (N + 1) (F.proj.mapH T.i₀) ≫ (quotBd F hW hP).φ ≫ F.proj.mapH T.i₀ := by
  ext r
  simp only [comp_f, InvFunctor.mapDualIso_inv_f, id_comp, InvFunctor.mapH,
    Functor.mapHomologicalComplex_map_f, triadCycle_f, T.i₁_eq_zero, zero_f,
    A.inv.star_zero, zero_comp, sub_zero, dualHom_f, quotBd_φ_f, Functor.map_comp,
    F.proj.map_star]

variable (F) in
/-- **The top of `T` modulo `U`**, as an `(N+2)`-dimensional pair `(W/U ⟶ E/U)` of `A/U` on the
closed complex `W/U` (the boundary `P` lies in `U`). -/
@[simps, implicit_reducible]
def quotData (hW : W.IsPoincare) (hP : ∀ r, F.U (P.C.X r)) : PairData (quotBd F hW hP) where
  D := F.proj.mapC T.E
  pD := F.proj.mapH T.pE
  pD_idem := by rw [← Functor.map_comp, T.pE_idem]
  support r hr := by
    change F.proj.F.map (T.pE.f r) = 0
    rw [T.support r hr, Functor.map_zero]
  j := F.proj.mapH T.i₀
  j_kar := by
    change F.proj.mapH W.pD ≫ _ ≫ _ = _
    simp only [← Functor.map_comp, T.i₀_kar]
  δφ := homotopyCongr ((F.proj.F.mapHomotopy T.δφ).compLeft (F.proj.mapDualIso (N + 1) T.E).inv)
    (T.quot_triadCycle hW hP) (by simp)
  δφ_kar r r' := by
    simp only [homotopyCongr_hom, Homotopy.compLeft_hom, Functor.mapHomotopy_hom,
      InvFunctor.mapDualIso_inv_f, id_comp, dualHom_f, InvFunctor.mapH,
      Functor.mapHomologicalComplex_map_f, ← F.proj.map_star, ← Functor.map_comp]
    rw [← dualHom_f, T.δφ_kar]
  symm := by
    have e : ((F.proj.F.mapHomotopy T.δφ).compLeft (F.proj.mapDualIso (N + 1) T.E).inv).hom =
        fun r r' ↦ F.proj.F.map (T.δφ.hom r r') := by
      funext r r'; simp <;> exact Category.id_comp _
    have hs := T.symm
    rw [IsSymmHomotopy, transposeHomotopy_hom] at hs ⊢
    change transposeHomFamily F.quot.inv (N + 1)
      ((F.proj.F.mapHomotopy T.δφ).compLeft (F.proj.mapDualIso (N + 1) T.E).inv).hom =
        ((F.proj.F.mapHomotopy T.δφ).compLeft (F.proj.mapDualIso (N + 1) T.E).inv).hom
    rw [e, F.proj.transposeHomFamily_map, hs]

lemma quotData_δφ_hom (hW : W.IsPoincare) (hP : ∀ r, F.U (P.C.X r)) (r r' : ℤ) :
    (T.quotData F hW hP).δφ.hom r r' = F.proj.F.map (T.δφ.hom r r') := by
  simp [quotData] <;> exact Category.id_comp _

lemma relTop_quotData (hW : W.IsPoincare) (hP : ∀ r, F.U (P.C.X r)) (r : ℤ) :
    relTop (T.quotData F hW hP).δφ r = F.proj.F.map (T.top r) := by
  simp only [relTop, top, hTop, quotData_δφ_hom, XIsoOfEq, eqToIso.hom, Functor.map_comp,
    eqToHom_map]

/-- **`Ψ₀` modulo `U` is the relative duality of the top modulo `U`**, under the cone comparison
isomorphism. -/
lemma dualHom_coneComparison_comp_relDuality (hW : W.IsPoincare) (hP : ∀ r, F.U (P.C.X r)) :
    dualHom F.quot.inv (N + 1 + 1) (F.proj.coneComparison T.i₀) ≫
      relDuality (T.quotData F hW hP).δφ = F.proj.mapDual T.Ψ₀ := by
  ext r
  have h₁ := congrArg F.quot.inv.star (F.proj.inrX_coneComparison_f T.i₀ (N + 1 + 1 - r))
  have h₂ := congrArg F.quot.inv.star
    (F.proj.inlX_coneComparison_f T.i₀ _ _ (down_rel_sub (N + 1) r))
  simp only [F.quot.inv.star_comp] at h₁ h₂
  rw [comp_f, dualHom_f, relDuality_f, relTop_quotData, quotBd_φ_f, InvFunctor.mapDual_f, Ψ₀_f,
    comp_add, reassoc_of% h₁, Linear.comp_units_smul, reassoc_of% h₂]
  simp only [InvFunctor.mapH, Functor.mapHomologicalComplex_map_f, Functor.map_add,
    Functor.map_comp, Functor.map_units_smul, F.proj.map_star]

/-- **The top is Poincaré modulo `U` iff the top modulo `U` is a Poincaré pair** on `W/U`. -/
theorem isPoincareTopMod_iff (hW : W.IsPoincare) (hP : ∀ r, F.U (P.C.X r)) :
    T.IsPoincareTopMod F ↔ (T.quotData F hW hP).IsPoincare := by
  set c := F.proj.coneComparison T.i₀
  have e₀ := F.proj.coneComparison_comp_map_coneMap T.i₀
    (comm_of_kar W.pD_idem T.pE_idem T.i₀_kar)
  have hR := T.dualHom_coneComparison_comp_relDuality hW hP
  have hc : (T.quotData F hW hP).coneIdem = c ≫ F.proj.mapH T.coneIdem₀ ≫ inv c := by
    rw [← assoc, e₀, assoc, IsIso.hom_inv_id, comp_id]; rfl
  have e₁ : dualHom F.quot.inv (N + 1 + 1) (inv c) ≫
      dualHom F.quot.inv (N + 1 + 1) (F.proj.mapH T.coneIdem₀) ≫ dualHom F.quot.inv (N + 1 + 1) c =
      dualHom F.quot.inv (N + 1 + 1) (T.quotData F hW hP).coneIdem := by
    rw [hc, dualHom_comp, dualHom_comp, assoc]
  have e₂ : dualHom F.quot.inv (N + 1 + 1) (inv c) ≫ F.proj.mapDual T.Ψ₀ =
      relDuality (T.quotData F hW hP).δφ := by
    rw [← hR, ← assoc, ← dualHom_comp, IsIso.hom_inv_id, dualHom_id, id_comp]
  have e₃ : dualHom F.quot.inv (N + 1 + 1) c ≫
      dualHom F.quot.inv (N + 1 + 1) (T.quotData F hW hP).coneIdem ≫
        dualHom F.quot.inv (N + 1 + 1) (inv c) =
      dualHom F.quot.inv (N + 1 + 1) (F.proj.mapH T.coneIdem₀) := by
    rw [← dualHom_comp, ← dualHom_comp, hc]
    congr 1
    simp
  unfold IsPoincareTopMod PairData.IsPoincare
  change IsKarEquiv (dualHom F.quot.inv (N + 1 + 1) (F.proj.mapH T.coneIdem₀)) (F.proj.mapH T.pE)
    (F.proj.mapDual T.Ψ₀) ↔ _
  constructor
  · intro h
    have h₁ := h.conjIso (dualIso F.quot.inv (N + 1 + 1) (asIso c))
    simp only [dualIso_inv, dualIso_hom, asIso_inv, asIso_hom] at h₁
    rw [e₁, e₂] at h₁
    exact h₁
  · intro h
    have h₁ := h.conjIso (dualIso F.quot.inv (N + 1 + 1) (asIso c)).symm
    simp only [Iso.symm_inv, Iso.symm_hom, dualIso_inv, dualIso_hom, asIso_inv, asIso_hom] at h₁
    rw [e₃, hR] at h₁
    exact h₁

end TriadOn

/-! ### Relative bottom compression -/

namespace TriadOn

variable {A : InvCat} {F : KaroubiFiltration A} {N : ℤ} {P : SymPoincare A.inv N}
  {W : PairData P} (T : TriadOn W (PairData.zero P)) (ε : T.E.X 0 ⟶ T.E.X 0)

/-- `ε` in degree `0`, `0` elsewhere. -/
def epsF (r : ℤ) : T.E.X r ⟶ T.E.X r :=
  if h : r = 0 then (T.E.XIsoOfEq h).hom ≫ ε ≫ (T.E.XIsoOfEq h.symm).hom else 0

@[simp] lemma epsF_zero : T.epsF ε 0 = ε := by simp [epsF]

lemma epsF_ne {r : ℤ} (h : r ≠ 0) : T.epsF ε r = 0 := by simp [epsF, h]

/-- The compressed idempotent `q = p_E - ε` (`ε` only in degree `0`). -/
def qF (r : ℤ) : T.E.X r ⟶ T.E.X r := T.pE.f r - T.epsF ε r

lemma qF_ne {r : ℤ} (h : r ≠ 0) : T.qF ε r = T.pE.f r := by simp [qF, T.epsF_ne ε h]

lemma qF_zero : T.qF ε 0 = T.pE.f 0 - ε := by simp [qF]

@[reassoc]
lemma pE_f_idem (r : ℤ) : T.pE.f r ≫ T.pE.f r = T.pE.f r := by rw [← comp_f, T.pE_idem]

variable {T ε} (hp0 : T.pE.f 0 = 𝟙 _) (hε : ε ≫ ε = ε)

lemma qF_neg_one : T.qF ε (-1) = 0 := by
  rw [T.qF_ne ε (by omega), T.support (-1) (by omega)]

include hp0 in
lemma p_qF (r : ℤ) : T.pE.f r ≫ T.qF ε r = T.qF ε r := by
  by_cases h : r = 0
  · subst h; rw [hp0, id_comp]
  · rw [T.qF_ne ε h, T.pE_f_idem]

include hp0 in
lemma qF_p (r : ℤ) : T.qF ε r ≫ T.pE.f r = T.qF ε r := by
  by_cases h : r = 0
  · subst h; rw [hp0, comp_id]
  · rw [T.qF_ne ε h, T.pE_f_idem]

include hp0 in
lemma d_zero_neg_one : T.E.d 0 (-1) = 0 := by
  rw [← id_comp (T.E.d 0 (-1)), ← hp0, T.pE.comm, T.support (-1) (by omega), comp_zero]

include hp0 hε in
@[reassoc]
lemma qF_idem (r : ℤ) : T.qF ε r ≫ T.qF ε r = T.qF ε r := by
  by_cases h : r = 0
  · subst h; simp [qF_zero, hp0, hε]
  · rw [T.qF_ne ε h, T.pE_f_idem]

lemma map_qF (hU : FactorsThrough F.U ε) (r : ℤ) :
    F.proj.F.map (T.qF ε r) = F.proj.F.map (T.pE.f r) := by
  rw [F.proj_map_eq_iff, qF, sub_sub_cancel_left]
  by_cases h : r = 0
  · subst h; simpa using hU.neg
  · rw [T.epsF_ne ε h, neg_zero]; exact FactorsThrough.zero

variable (T ε)

/-- **The compressed top** `E♭ = (E, p_E d q)`: the `ε`-part of `E_0` cut off from the image
of `d`. -/
@[simps, implicit_reducible]
def flatE : ChainComplex A ℤ where
  X := T.E.X
  d i j := T.pE.f i ≫ T.E.d i j ≫ T.qF ε j
  shape i j h := by simp [T.E.shape i j h]
  d_comp_d' i j k _ hjk := by
    by_cases h : j = 0
    · subst h
      obtain rfl : k = -1 := by simp at hjk; omega
      simp [qF_neg_one]
    · simp only [assoc, T.qF_ne ε h, T.pE_f_idem_assoc, T.pE.comm_assoc j k,
        HomologicalComplex.d_comp_d_assoc, zero_comp, comp_zero]

/-- `τ = q : (E, p_E) ⟶ (E♭, q)`, an honest chain map. -/
@[simps]
def flatTo : T.E ⟶ T.flatE ε where
  f r := T.qF ε r
  comm' i j hij := by
    by_cases h : i = 0
    · subst h
      obtain rfl : j = -1 := by simp at hij; omega
      simp [qF_neg_one]
    · simp only [flatE_d]
      rw [T.qF_ne ε h, ← assoc, T.pE_f_idem, T.pE.comm_assoc, p_qF hp0]

/-- The idempotent `q` of `E♭`. -/
@[simps]
def flatP : T.flatE ε ⟶ T.flatE ε where
  f r := T.qF ε r
  comm' i j hij := by
    by_cases h : i = 0
    · subst h
      obtain rfl : j = -1 := by simp at hij; omega
      simp [qF_neg_one]
    · simp only [flatE_d]
      rw [T.qF_ne ε h, ← assoc, T.pE_f_idem, assoc, assoc, qF_idem hp0 hε]

lemma flatP_idem : T.flatP ε hp0 hε ≫ T.flatP ε hp0 hε = T.flatP ε hp0 hε := by
  ext r; exact qF_idem hp0 hε r

lemma flatTo_flatP : T.flatTo ε hp0 ≫ T.flatP ε hp0 hε = T.flatTo ε hp0 := by
  ext r; exact qF_idem hp0 hε r

lemma flatP_support (hN : 0 ≤ N + 1) : SupportedIn (T.flatP ε hp0 hε) 0 (N + 1 + 1) :=
  fun r hr ↦ by rw [flatP_f, T.qF_ne ε (by omega), T.support r hr]

lemma flat_comm : W.j ≫ T.i₀ ≫ T.flatTo ε hp0 = (PairData.zero P).j ≫ 0 := by
  rw [← assoc, T.j_comp_i₀, zero_comp, comp_zero]

lemma flat_triadCycle : dualHom A.inv (N + 1) (T.flatTo ε hp0) ≫
    triadCycle W (PairData.zero P) T.i₀ T.i₁ T.comm ≫ T.flatTo ε hp0 =
    triadCycle W (PairData.zero P) (T.i₀ ≫ T.flatTo ε hp0) 0 (T.flat_comm ε hp0) := by
  ext r
  simp [triadCycle_f, T.i₁_eq_zero, A.inv.star_comp]

/-- The structure `τ δφ τ^*` of the compressed triad. -/
def flatδφ : Homotopy (triadCycle W (PairData.zero P) (T.i₀ ≫ T.flatTo ε hp0) 0
    (T.flat_comm ε hp0)) 0 :=
  homotopyCongr ((T.δφ.compRight (T.flatTo ε hp0)).compLeft
    (dualHom A.inv (N + 1) (T.flatTo ε hp0))) (T.flat_triadCycle ε hp0) (by simp)

lemma flatδφ_hom (r r' : ℤ) : (T.flatδφ ε hp0).hom r r' =
    (dualHom A.inv (N + 1) (T.flatTo ε hp0)).f r ≫ T.δφ.hom r r' ≫ (T.flatTo ε hp0).f r' := rfl

/-- **The compressed triad** `T♭ = (E♭; W, ∅; P)`: `i♭ = i τ`, `δφ♭ = τ δφ τ^*`. -/
@[implicit_reducible]
def flat (hN : 0 ≤ N + 1) : TriadOn W (PairData.zero P) where
  E := T.flatE ε
  pE := T.flatP ε hp0 hε
  pE_idem := T.flatP_idem ε hp0 hε
  support := T.flatP_support ε hp0 hε hN
  i₀ := T.i₀ ≫ T.flatTo ε hp0
  i₀_kar := by rw [assoc, T.flatTo_flatP ε hp0 hε, ← assoc, T.pD_comp_i₀]
  i₁ := 0
  i₁_kar := by simp
  comm := T.flat_comm ε hp0
  δφ := T.flatδφ ε hp0
  δφ_kar r r' := by
    have h₁ : (dualHom A.inv (N + 1) (T.flatP ε hp0 hε)).f r ≫
        (dualHom A.inv (N + 1) (T.flatTo ε hp0)).f r = (dualHom A.inv (N + 1) (T.flatTo ε hp0)).f r := by
      rw [← comp_f, ← dualHom_comp, T.flatTo_flatP ε hp0 hε]
    have h₂ : (T.flatTo ε hp0).f r' ≫ (T.flatP ε hp0 hε).f r' = (T.flatTo ε hp0).f r' := by
      rw [← comp_f, T.flatTo_flatP ε hp0 hε]
    simp only [flatδφ_hom, assoc, h₂, reassoc_of% h₁]
  symm := by
    rw [IsSymmHomotopy, transposeHomotopy_hom]
    have e₁ : (T.flatδφ ε hp0).hom = fun r r' ↦ (dualHom A.inv (N + 1) (T.flatTo ε hp0)).f r ≫
          T.δφ.hom r r' ≫ (T.flatTo ε hp0).f r' := rfl
    rw [e₁, transposeHomFamily_conj', transposeHomFamily_eq T.symm]

lemma flat_δφ_hom (hN : 0 ≤ N + 1) (r r' : ℤ) : (T.flat ε hp0 hε hN).δφ.hom r r' =
    A.inv.star (T.qF ε (N + 1 - r)) ≫ T.δφ.hom r r' ≫ T.qF ε r' := rfl

omit hp0 in
@[reassoc]
lemma XIsoOfEq_star_qF {a a' : ℤ} (h : a = a') :
    (T.E.XIsoOfEq h).hom ≫ A.inv.star (T.qF ε a') = A.inv.star (T.qF ε a) ≫ (T.E.XIsoOfEq h).hom := by
  subst h; simp

lemma flat_top (hN : 0 ≤ N + 1) (r : ℤ) : (T.flat ε hp0 hε hN).top r =
    A.inv.star (T.qF ε (N + 1 + 1 - r)) ≫ T.top r ≫ T.qF ε r := by
  rw [top, hTop, flat_δφ_hom, top, hTop]
  change (T.E.XIsoOfEq (by omega : N + 1 + 1 - r = N + 1 - (r - 1))).hom ≫ _ = _
  rw [T.XIsoOfEq_star_qF_assoc ε]
  simp only [assoc]

/-- The comparison `E♭ ⟶ E` modulo `U` (componentwise `[q] = [p_E]`); not a chain map in `A`. -/
@[simps]
def flatFrom (hU : FactorsThrough F.U ε) : F.proj.mapC (T.flatE ε) ⟶ F.proj.mapC T.E where
  f r := F.proj.F.map (T.qF ε r)
  comm' i j _ := by
    have h : T.pE.f i ≫ T.E.d i j ≫ T.pE.f j ≫ T.pE.f j = T.pE.f i ≫ T.E.d i j := by
      rw [T.pE_f_idem, ← T.pE.comm, T.pE_f_idem_assoc]
    simp only [Functor.mapHomologicalComplex_obj_d, flatE_d, Functor.map_comp, map_qF hU]
    simp only [← Functor.map_comp, assoc]
    rw [h]

/-- **Compression preserves Poincaré duality of the top modulo `U`** (`E♭ ≅ E` strictly in
`A/U`, compatibly with `i` and `δφ`). -/
theorem isPoincareTopMod_flat (hW : W.IsPoincare) (hP : ∀ r, F.U (P.C.X r))
    (hU : FactorsThrough F.U ε) (hN : 0 ≤ N + 1) (hT : T.IsPoincareTopMod F) :
    (T.flat ε hp0 hε hN).IsPoincareTopMod F := by
  rw [isPoincareTopMod_iff _ hW hP] at hT ⊢
  have hfg : T.flatFrom ε hU ≫ F.proj.mapH (T.flatTo ε hp0) = F.proj.mapH (T.flatP ε hp0 hε) := by
    ext r
    simp only [comp_f, flatFrom_f, InvFunctor.mapH, Functor.mapHomologicalComplex_map_f,
      flatTo_f, flatP_f, ← Functor.map_comp, qF_idem hp0 hε]
  have hgf : F.proj.mapH (T.flatTo ε hp0) ≫ T.flatFrom ε hU = F.proj.mapH T.pE := by
    ext r
    simp only [comp_f, flatFrom_f, InvFunctor.mapH, Functor.mapHomologicalComplex_map_f,
      flatTo_f]
    rw [← Functor.map_comp, qF_idem hp0 hε, map_qF hU]
  have hfk : F.proj.mapH (T.flatP ε hp0 hε) ≫ T.flatFrom ε hU ≫ F.proj.mapH T.pE =
      T.flatFrom ε hU := by
    ext r
    simp only [comp_f, flatFrom_f, InvFunctor.mapH, Functor.mapHomologicalComplex_map_f,
      flatP_f, ← Functor.map_comp, qF_idem hp0 hε, qF_p hp0]
  have hj : F.proj.mapH (T.i₀ ≫ T.flatTo ε hp0) ≫ T.flatFrom ε hU = F.proj.mapH T.i₀ := by
    ext r
    simp only [comp_f, flatFrom_f, InvFunctor.mapH, Functor.mapHomologicalComplex_map_f,
      flatTo_f, Functor.map_comp, assoc, map_qF hU]
    rw [← Functor.map_comp, T.pE_f_idem, ← Functor.map_comp, T.i₀_f_comp_pE_f]
  have hH (r r' : ℤ) : (dualHom F.quot.inv (N + 1) (F.proj.mapH (T.flatTo ε hp0))).f r ≫
      (T.quotData F hW hP).δφ.hom r r' ≫ (F.proj.mapH (T.flatTo ε hp0)).f r' =
      ((T.flat ε hp0 hε hN).quotData F hW hP).δφ.hom r r' := by
    simp only [quotData_δφ_hom, flat_δφ_hom, dualHom_f, InvFunctor.mapH,
      Functor.mapHomologicalComplex_map_f, flatTo_f, Functor.map_comp, F.proj.map_star]
  exact LiftComplex.isKarEquiv_relDuality_of_strict (quotBd F hW hP).p_idem
    (T.quotData F hW hP).pD_idem ((T.flat ε hp0 hε hN).quotData F hW hP).pD_idem
    (T.quotData F hW hP).j_kar ((T.flat ε hp0 hε hN).quotData F hW hP).j_kar _ _
    (quotBd F hW hP).dualHom_p_comp_φ (T.flatFrom ε hU) (F.proj.mapH (T.flatTo ε hp0)) hfg hgf
    hfk hj hH hT

/-- **Connected relative lifts** (the bottom of the new face splits; relative version of
`QuotPoincare.exists_flat`).  If the top of `T` is Poincaré modulo `U` and `p_E = 1` in degree
`0`, then for some idempotent `ε ∈ I_U` of `E_0` the compressed triad `T♭` has a Kar-split bottom
differential of its new face (`hab` of `exists_relBd`): in `A/U`, `ψ Ψ₀ - h d = 1` in degree `0`;
lifting, `u = ψ̃ Ψ₀ - h̃ d - 1 ∈ I_U` factors through the `E`-part `ε` of a splitting of `E_0`,
and compressing `E_0` to `1 - ε` kills it. -/
theorem exists_flat (hT : T.IsPoincareTopMod F) (hp0 : T.pE.f 0 = 𝟙 _) (hN : 0 ≤ N + 1) :
    ∃ (ε : T.E.X 0 ⟶ T.E.X 0) (hε : ε ≫ ε = ε), FactorsThrough F.U ε ∧
      ∃ (a : T.E.X 0 ⟶ T.E.X (N + 1 + 1 - 0)) (b : T.E.X 0 ⟶ W.D.X 0) (c : T.E.X 0 ⟶ T.E.X 1),
        (T.flat ε hp0 hε hN).pE.f 0 ≫ (a ≫ (T.flat ε hp0 hε hN).top 0 +
          b ≫ (T.flat ε hp0 hε hN).i₀.f 0 + c ≫ (T.flat ε hp0 hε hN).E.d 1 0) ≫
            (T.flat ε hp0 hε hN).pE.f 0 = (T.flat ε hp0 hε hN).pE.f 0 := by
  obtain ⟨ψ, -, ⟨H₁⟩, -⟩ := hT
  let ψ' : T.E.X 0 ⟶ (cone T.i₀).X (N + 1 + 1 - 0) := F.liftQuotHom (ψ.f 0)
  let h' : T.E.X 0 ⟶ T.E.X 1 := F.liftQuotHom (H₁.hom 0 1)
  have hc := homotopy_comm H₁ 0 (-1) 1 (by simp) (by simp)
  dsimp only [KaroubiFiltration.projF] at hc
  have key : F.proj.F.map (ψ' ≫ T.Ψ₀.f 0 - h' ≫ T.E.d 1 0) = F.proj.F.map (𝟙 _) := by
    rw [Functor.map_sub, Functor.map_comp, Functor.map_comp, KaroubiFiltration.map_liftQuotHom,
      KaroubiFiltration.map_liftQuotHom,
      CategoryTheory.Functor.map_id]
    simp only [comp_f, InvFunctor.mapDual_f, Functor.mapHomologicalComplex_obj_d,
      Functor.mapHomologicalComplex_map_f, d_zero_neg_one hp0, Functor.map_zero, zero_comp,
      zero_add, hp0, CategoryTheory.Functor.map_id] at hc
    rw [sub_eq_iff_eq_add, hc, add_comm]
  have hu : FactorsThrough F.U (ψ' ≫ T.Ψ₀.f 0 - h' ≫ T.E.d 1 0 - 𝟙 _) :=
    (F.proj_map_eq_iff _ _).mp key
  obtain ⟨σ, hσ, g, hg⟩ := (F.factorsThrough_iff_target _).mp hu
  have hε : σ.idem ≫ σ.idem = σ.idem := Casc.idem_idem σ
  have hεU : FactorsThrough F.U σ.idem := FactorsThrough.of_mem (F.filt.mem _ σ hσ) σ.πE σ.ιE
  have huε : (ψ' ≫ T.Ψ₀.f 0 - h' ≫ T.E.d 1 0 - 𝟙 _) ≫ σ.idem =
      ψ' ≫ T.Ψ₀.f 0 - h' ≫ T.E.d 1 0 - 𝟙 _ := by
    rw [hg, assoc, Casc.ιE_idem]
  refine ⟨σ.idem, hε, hεU, ψ' ≫ A.inv.star (inrX T.i₀ (N + 1 + 1 - 0)),
    ψ' ≫ (((0 : ℤ) + 1).negOnePow • (A.inv.star (inlX T.i₀ (N + 1 - 0) (N + 1 + 1 - 0)
      (down_rel_sub (N + 1) 0)) ≫ relTop W.δφ 0)), -h', ?_⟩
  have h1 : A.inv.star (T.qF σ.idem (N + 1 + 1 - 0)) ≫ T.top 0 = T.top 0 := by
    rw [T.qF_ne _ (by omega), star_pE_comp_top]
  have h2 : T.pE.f 1 ≫ T.E.d 1 0 = T.E.d 1 0 := by rw [T.pE.comm, hp0, comp_id]
  have h3 : (ψ' ≫ T.Ψ₀.f 0 - h' ≫ T.E.d 1 0) ≫ T.qF σ.idem 0 = T.qF σ.idem 0 := by
    have e : ψ' ≫ T.Ψ₀.f 0 - h' ≫ T.E.d 1 0 =
        (ψ' ≫ T.Ψ₀.f 0 - h' ≫ T.E.d 1 0 - 𝟙 _) + 𝟙 _ := by abel
    rw [e, add_comp, id_comp, qF_zero, hp0, comp_sub, comp_id, huε, sub_self, zero_add]
  rw [flat_top]
  change T.qF σ.idem 0 ≫ ((ψ' ≫ A.inv.star (inrX T.i₀ (N + 1 + 1 - 0))) ≫
    (A.inv.star (T.qF σ.idem (N + 1 + 1 - 0)) ≫ T.top 0 ≫ T.qF σ.idem 0) +
    (ψ' ≫ (((0 : ℤ) + 1).negOnePow • (A.inv.star (inlX T.i₀ (N + 1 - 0) (N + 1 + 1 - 0)
      (down_rel_sub (N + 1) 0)) ≫ relTop W.δφ 0))) ≫ (T.i₀.f 0 ≫ T.qF σ.idem 0) +
    (-h') ≫ (T.pE.f 1 ≫ T.E.d 1 0 ≫ T.qF σ.idem 0)) ≫ T.qF σ.idem 0 = T.qF σ.idem 0
  have e : (ψ' ≫ A.inv.star (inrX T.i₀ (N + 1 + 1 - 0))) ≫
      (A.inv.star (T.qF σ.idem (N + 1 + 1 - 0)) ≫ T.top 0 ≫ T.qF σ.idem 0) +
      (ψ' ≫ (((0 : ℤ) + 1).negOnePow • (A.inv.star (inlX T.i₀ (N + 1 - 0) (N + 1 + 1 - 0)
        (down_rel_sub (N + 1) 0)) ≫ relTop W.δφ 0))) ≫ (T.i₀.f 0 ≫ T.qF σ.idem 0) +
      (-h') ≫ (T.pE.f 1 ≫ T.E.d 1 0 ≫ T.qF σ.idem 0) =
      (ψ' ≫ T.Ψ₀.f 0 - h' ≫ T.E.d 1 0) ≫ T.qF σ.idem 0 := by
    rw [Ψ₀_f, reassoc_of% h1, reassoc_of% h2]
    simp only [comp_add, add_comp, sub_comp, assoc, Linear.comp_units_smul,
      Linear.units_smul_comp, neg_comp]
    abel
  rw [e, h3, qF_idem hp0 hε, qF_idem hp0 hε]

end TriadOn

/-! ### Relative lifts on a frozen boundary with a non-closed structure -/

namespace KaroubiFiltration

open LiftComplex

variable {A : InvCat} (F : KaroubiFiltration A)

variable (N : ℤ) in
/-- Relative lifting data from `A/U` on a frozen honest boundary `B` whose structure is only a
family `ψ` (the top `relTop δφ_W` of a face, a chain map modulo `U` only): as `RelLift.ofQuot`,
with `j̃ = p_B [j]~` (so that `p_B j'' = j''` on the nose) and `H̃` the symmetrized lift of `δφ`. -/
@[simps, implicit_reducible]
def RelLift.ofQuotFam (B : ChainComplex A ℤ) (pB : B ⟶ B) (ψ : ∀ r, B.X (N - r) ⟶ B.X r)
    (φ : dualComplex F.quot.inv N (F.proj.mapC B) ⟶ F.proj.mapC B)
    (hφ : ∀ r, φ.f r = F.proj.F.map (ψ r))
    (D : ChainComplex F.quot ℤ) (top : ℤ) (hD : ∀ i k, top < i → D.d i k = 0)
    (j : F.proj.mapC B ⟶ D) (hj : F.proj.mapH pB ≫ j = j)
    (δφ : Homotopy (dualHom F.quot.inv N j ≫ φ ≫ j) 0)
    (hδφ : IsSymmHomotopy F.quot.inv N δφ) : F.RelLift N where
  X r := (D.X r).as
  d i k := F.liftQuotHom (D.d i k)
  shape i k h := F.liftQuotHom_zero (D.shape i k h)
  d_comp_d i k l := by
    simpa using (F.proj_map_eq_iff (F.liftQuotHom (D.d i k) ≫ F.liftQuotHom (D.d k l)) 0).mp
      (by rw [Functor.map_comp, map_liftQuotHom, map_liftQuotHom, D.d_comp_d, Functor.map_zero])
  top := top
  d_eq_zero i k h := F.liftQuotHom_zero (hD i k h)
  B := B
  ψ := ψ
  j r := pB.f r ≫ F.liftQuotHom (j.f r)
  j_comm i k := (F.proj_map_eq_iff _ _).mp (by
    have h := (F.proj.mapH pB ≫ j).comm i k
    simp only [comp_f, InvFunctor.mapH, Functor.mapHomologicalComplex_map_f,
      Functor.mapHomologicalComplex_obj_d, assoc] at h
    simp only [Functor.map_comp, map_liftQuotHom, assoc]
    rw [h, ← assoc, ← Functor.map_comp, ← pB.comm, Functor.map_comp, assoc])
  H := F.liftFamily D δφ.hom
  H_shape := liftFamily_shape δφ.hom δφ.zero
  H_comm r := (F.proj_map_eq_iff _ _).mp (by
    have hs : transposeHomFamily F.quot.inv N δφ.hom = δφ.hom := by
      rw [← transposeHomotopy_hom]; exact hδφ
    have hj' (k : ℤ) : F.proj.F.map (pB.f k) ≫ j.f k = j.f k := congrArg (fun f ↦ f.f k) hj
    have hjs (k : ℤ) : F.proj.F.map (A.inv.star (pB.f k ≫ F.liftQuotHom (j.f k))) =
        F.quot.inv.star (j.f k) := by
      rw [F.proj.map_star, Functor.map_comp, map_liftQuotHom, hj']
    have hjm (k : ℤ) : F.proj.F.map (pB.f k ≫ F.liftQuotHom (j.f k)) = j.f k := by
      rw [Functor.map_comp, map_liftQuotHom, hj']
    have := δφ.comm r
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel r (r - 1) by simp),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (r + 1) r by simp)] at this
    rw [Functor.map_comp, Functor.map_comp, hjs, hjm, ← hφ]
    simp only [Functor.map_comp, Functor.map_add, Casc.map_units_smul, F.proj.map_star,
      map_liftQuotHom, map_liftFamily δφ.hom hs]
    simpa using this)

variable {F}

/-- The represented interior of `ofQuotFam` is `D` (identity components). -/
def RelLift.ofQuotFamIso {N : ℤ} (B : ChainComplex A ℤ) (pB : B ⟶ B)
    (ψ : ∀ r, B.X (N - r) ⟶ B.X r) (φ : dualComplex F.quot.inv N (F.proj.mapC B) ⟶ F.proj.mapC B)
    (hφ : ∀ r, φ.f r = F.proj.F.map (ψ r))
    (D : ChainComplex F.quot ℤ) (top : ℤ) (hD : ∀ i k, top < i → D.d i k = 0)
    (j : F.proj.mapC B ⟶ D) (hj : F.proj.mapH pB ≫ j = j)
    (δφ : Homotopy (dualHom F.quot.inv N j ≫ φ ≫ j) 0) (hδφ : IsSymmHomotopy F.quot.inv N δφ) :
    (RelLift.ofQuotFam F N B pB ψ φ hφ D top hD j hj δφ hδφ).toSymLift.quotComplex ≅ D :=
  Hom.isoOfComponents (fun _ ↦ Iso.refl _) (fun i k _ ↦ by
    simp only [Iso.refl_hom, id_comp, comp_id, SymLift.quotComplex_d, RelLift.toSymLift,
      RelLift.ofQuotFam_d, map_liftQuotHom])

/-- **Relative honest lift on a frozen boundary with a non-closed structure** (plan (L2), the
input of the relative boundary construction).  Given an honest boundary `B` with a family
`ψ_r : B_{N-r} ⟶ B_r` whose image `φ = [ψ]` is a chain map of `A/U`, and over `A/U` a complex
`D` bounded above, a chain map `j : B ⟶ D` with `[p_B] j = j` and a symmetric relative structure
`δφ : j^* φ j ≃ 0`, there are an honest complex `D''`, an honest chain map `j'' : B ⟶ D''` with
`p_B j'' = j''` and **`g j'' = 0` for a prescribed `g : C ⟶ B` from a complex of `U`**, and an
honest strictly symmetric family `H` with `j''^* ψ j'' = δH + Hd` on the nose, with an isomorphism
`e : D'' ≅ D` in `A/U` carrying `j''` to `j` and `H` to `δφ`. -/
theorem exists_relLiftFam {N : ℤ} (B : ChainComplex A ℤ) (pB : B ⟶ B) (hpB : pB ≫ pB = pB)
    (ψ : ∀ r, B.X (N - r) ⟶ B.X r) (φ : dualComplex F.quot.inv N (F.proj.mapC B) ⟶ F.proj.mapC B)
    (hφ : ∀ r, φ.f r = F.proj.F.map (ψ r))
    (D : ChainComplex F.quot ℤ) (top : ℤ) (hD : ∀ i k, top < i → D.d i k = 0)
    (j : F.proj.mapC B ⟶ D) (hj : F.proj.mapH pB ≫ j = j)
    (δφ : Homotopy (dualHom F.quot.inv N j ≫ φ ≫ j) 0) (hδφ : IsSymmHomotopy F.quot.inv N δφ)
    {C : ChainComplex A ℤ} (g : C ⟶ B) (hC : ∀ r, F.U (C.X r)) :
    ∃ (D'' : ChainComplex A ℤ) (j'' : B ⟶ D'')
      (H : ∀ r r', (dualComplex A.inv N D'').X r ⟶ D''.X r') (e : F.proj.mapC D'' ≅ D),
      pB ≫ j'' = j'' ∧ g ≫ j'' = 0 ∧
      (∀ r r', ¬ (ComplexShape.down ℤ).Rel r' r → H r r' = 0) ∧
      (∀ r, A.inv.star (j''.f (N - r)) ≫ ψ r ≫ j''.f r =
        (dualComplex A.inv N D'').d r (r - 1) ≫ H (r - 1) r + H r (r + 1) ≫ D''.d (r + 1) r) ∧
      transposeHomFamily A.inv N (C := D'') (D := D'') H = H ∧
      F.proj.mapH j'' ≫ e.hom = j ∧
      (∀ r r', (dualHom F.quot.inv N e.hom).f r ≫ F.proj.F.map (H r r') ≫ e.hom.f r' =
        δφ.hom r r') ∧
      (∀ i k, D.d i k = 0 → D''.d i k = 0) ∧ (∀ r, j.f r = 0 → j''.f r = 0) ∧
      (∀ r r', δφ.hom r r' = 0 → δφ.hom (N - r') (N - r) = 0 → H r r' = 0) := by
  have hs : transposeHomFamily F.quot.inv N δφ.hom = δφ.hom := by
    rw [← transposeHomotopy_hom]; exact hδφ
  obtain ⟨c, hc⟩ := (RelLift.ofQuotFam F N B pB ψ φ hφ D top hD j hj δφ hδφ).exists_cascade_comp_jHom
    g hC
  refine ⟨c.complex, c.jHom, c.relH,
    c.toSymCascade.quotIso ≪≫ RelLift.ofQuotFamIso B pB ψ φ hφ D top hD j hj δφ hδφ, ?_, hc,
    fun r r' h ↦ ?_, c.relH_comm, c.relH_symm (liftFamily_symm δφ.hom δφ.zero).symm, ?_, ?_,
    fun i k h ↦ c.toSymCascade.complex_d_eq_zero (F.liftQuotHom_zero h),
    fun r h ↦ by simp [F.liftQuotHom_zero h], fun r r' h₁ h₂ ↦ ?_⟩
  · ext r
    simp only [comp_f, RelLift.Cascade.jHom_f, RelLift.ofQuotFam_j]
    rw [← assoc, ← assoc, f_idem pB hpB]
  · simp [RelLift.Cascade.relH, liftFamily_shape δφ.hom δφ.zero r r' h]
  · ext r
    simp only [Iso.trans_hom, comp_f, InvFunctor.mapH, Functor.mapHomologicalComplex_map_f]
    erw [c.quot_jHom_assoc r]
    simp only [RelLift.ofQuotFam_j, RelLift.ofQuotFamIso, Hom.isoOfComponents_hom_f,
      Iso.refl_hom]
    erw [comp_id]
    rw [Functor.map_comp, map_liftQuotHom]
    exact congrArg (fun f ↦ f.f r) hj
  · intro r r'
    have := c.quot_relH r r'
    simp only [Iso.trans_hom, dualHom_comp, comp_f, assoc, RelLift.ofQuotFamIso,
      Hom.isoOfComponents_hom_f, Iso.refl_hom, dualHom_f] at this ⊢
    erw [F.quot.inv.star_id, id_comp, comp_id, this]
    exact map_liftFamily δφ.hom hs r r'
  · simp [RelLift.Cascade.relH, liftFamily_eq_zero δφ.hom h₁ h₂]

end KaroubiFiltration

/-! ### The relative lift of a null-cobordism of `W/U` -/


namespace TriadOn

open LiftComplex

variable {A : InvCat} {F : KaroubiFiltration A} {N : ℤ} {P : SymPoincare A.inv N}
  {W : PairData P}

/-- **Relative lift of a null-cobordism of `W/U`** (plan (L2)): if `P` lies in `U`, `W` is a
Poincaré pair on `P`, and the closed complex `W/U` of `A/U` bounds a Poincaré pair `Y` of `A/U`
whose idempotent is concentrated in `[lo, N + 2]` and `1` there, then there is an honest triad
`T = (E; W, ∅; P)` with top Poincaré modulo `U` and `p_E` the degree truncation to `[lo, N + 2]`:
lift `Y` relative to the frozen face `W` (`exists_relLiftFam`, with the cascade killing
`j_W j''`), truncate by degrees, and transport the duality of `Y` along the strict isomorphism
`E ≅ Y_D` of `A/U`. -/
theorem exists_of_quotPair (hW : W.IsPoincare) (hP : ∀ r, F.U (P.C.X r))
    (Y : PairOn (quotBd F hW hP)) (lo : ℤ) (hlo : 0 ≤ lo) (hsY : SupportedIn Y.pD lo (N + 1 + 1))
    (hpY : ∀ r, lo ≤ r → r ≤ N + 1 + 1 → Y.pD.f r = 𝟙 _) :
    ∃ T : TriadOn W (PairData.zero P), T.IsPoincareTopMod F ∧ SupportedIn T.pE lo (N + 1 + 1) ∧
      ∀ r, lo ≤ r → r ≤ N + 1 + 1 → T.pE.f r = 𝟙 _ := by
  obtain ⟨D, pD, pD_idem, support, j, j_kar, δφ, δφ_kar, symm, poincare⟩ := Y
  dsimp only at hpY hsY ⊢
  have hp0 : ∀ r, ¬ (lo ≤ r ∧ r ≤ N + 1 + 1) → pD.f r = 0 := fun r h ↦ hsY r (by omega)
  have hjp : j ≫ pD = j := kar_right pD_idem j_kar
  have hpj : (quotBd F hW hP).p ≫ j = j := kar_left (quotBd F hW hP).p_idem j_kar
  let δφ' : Homotopy (dualHom F.quot.inv (N + 1) (j ≫ karTruncTo pD pD_idem) ≫
      (quotBd F hW hP).φ ≫ (j ≫ karTruncTo pD pD_idem)) 0 :=
    homotopyCongr ((δφ.compRight (karTruncTo pD pD_idem)).compLeft
      (dualHom F.quot.inv (N + 1) (karTruncTo pD pD_idem)))
      (by rw [dualHom_comp]; simp only [assoc]) (by simp)
  have hδ : ∀ r r', δφ'.hom r r' = δφ.hom r r' := fun r r' ↦ δφ_kar r r'
  have hδ' : ∀ a b, (¬ (lo ≤ N + 1 - a ∧ N + 1 - a ≤ N + 1 + 1) ∨ ¬ (lo ≤ b ∧ b ≤ N + 1 + 1)) →
      δφ'.hom a b = 0 := fun a b h ↦ by
    change (dualHom F.quot.inv (N + 1) pD).f a ≫ δφ.hom a b ≫ pD.f b = 0
    rcases h with h | h
    · rw [dualHom_f, hp0 _ h, StrictInvolution.star_zero, zero_comp]
    · rw [hp0 _ h, comp_zero, comp_zero]
  have hsymm' : IsSymmHomotopy F.quot.inv (N + 1) δφ' := by
    rw [IsSymmHomotopy, transposeHomotopy_hom] at symm ⊢
    rw [show δφ'.hom = δφ.hom from funext₂ hδ]
    exact symm
  have hj' : F.proj.mapH W.pD ≫ j ≫ karTruncTo pD pD_idem = j ≫ karTruncTo pD pD_idem := by
    rw [← assoc]; exact congrArg (· ≫ _) hpj
  obtain ⟨D'', j'', H, e, hpj'', hgj, hHs, hHc, hHsymm, hje, hHe, hdd, hj0, hH0⟩ :=
    F.exists_relLiftFam W.D W.pD W.pD_idem (fun r ↦ relTop W.δφ r) (quotBd F hW hP).φ
      (quotBd_φ_f hW hP) (karTrunc pD pD_idem) (N + 1 + 1)
      (fun i k h ↦ by rw [karTrunc_d, hp0 i (by omega), zero_comp])
      (j ≫ karTruncTo pD pD_idem) hj' δφ' hsymm' W.j hP
  have hd'' : ∀ i k, ¬ (lo ≤ i ∧ i ≤ N + 1 + 1 ∧ lo ≤ k ∧ k ≤ N + 1 + 1) → D''.d i k = 0 :=
    fun i k h ↦ hdd i k (by
      rw [karTrunc_d]
      by_cases hi : lo ≤ i ∧ i ≤ N + 1 + 1
      · rw [pD.comm, hp0 k (by omega), comp_zero]
      · rw [hp0 i hi, zero_comp])
  set τ := degTrunc D'' lo (N + 1 + 1) hd''
  have hjr : ∀ r, ¬ (lo ≤ r ∧ r ≤ N + 1) → j''.f r = 0 := fun r h ↦ by
    by_cases h₀ : 0 ≤ r ∧ r ≤ N + 1
    · refine hj0 r ?_
      rw [comp_f, ← hjp, comp_f, hp0 r (by omega), comp_zero, zero_comp]
    · rw [← hpj'', comp_f, W.support r (by omega), zero_comp]
  have hi_kar : W.pD ≫ j'' ≫ τ = j'' := by
    ext r
    simp only [comp_f]
    by_cases h : lo ≤ r ∧ r ≤ N + 1
    · rw [degTrunc_f_of_mem hd'' ⟨h.1, by omega⟩, comp_id, ← comp_f, hpj'']
    · rw [hjr r h, zero_comp, comp_zero]
  have hHr : ∀ r r', (¬ (lo ≤ N + 1 - r ∧ N + 1 - r ≤ N + 1 + 1) ∨ ¬ (lo ≤ r' ∧ r' ≤ N + 1 + 1)) →
      H r r' = 0 := fun r r' h ↦ hH0 r r' (hδ' r r' h) (hδ' _ _ (by omega))
  have H_kar : ∀ r r', (dualHom A.inv (N + 1) τ).f r ≫ H r r' ≫ τ.f r' = H r r' := fun r r' ↦ by
    by_cases h : (lo ≤ N + 1 - r ∧ N + 1 - r ≤ N + 1 + 1) ∧ (lo ≤ r' ∧ r' ≤ N + 1 + 1)
    · rw [dualHom_f, degTrunc_f_of_mem hd'' h.1, degTrunc_f_of_mem hd'' h.2]
      erw [A.inv.star_id]
      rw [id_comp, comp_id]
    · rw [hHr r r' (by tauto)]; simp
  let T : TriadOn W (PairData.zero P) := ofRel (X₀ := W) j'' τ (degTrunc_idem hd'')
    (fun r hr ↦ supportedIn_degTrunc hd'' r (by omega)) hi_kar hgj H hHs hHc H_kar hHsymm
  refine ⟨T, ?_, supportedIn_degTrunc hd'', fun r h₁ h₂ ↦ degTrunc_f_of_mem hd'' ⟨h₁, h₂⟩⟩
  rw [isPoincareTopMod_iff T hW hP]
  have hτ : ∀ r, F.proj.F.map (τ.f r) = if lo ≤ r ∧ r ≤ N + 1 + 1 then 𝟙 _ else 0 := fun r ↦ by
    by_cases h : lo ≤ r ∧ r ≤ N + 1 + 1
    · rw [degTrunc_f_of_mem hd'' h, if_pos h, CategoryTheory.Functor.map_id]
    · rw [degTrunc_f_of_not_mem hd'' h, if_neg h, Functor.map_zero]
  have hfg : (e.hom ≫ karTruncFrom pD pD_idem) ≫ karTruncTo pD pD_idem ≫ e.inv =
      F.proj.mapH τ := by
    ext r
    simp only [comp_f, karTruncFrom_f, karTruncTo_f, InvFunctor.mapH,
      Functor.mapHomologicalComplex_map_f, hτ]
    split_ifs with h
    · rw [hpY r h.1 h.2]; erw [comp_id, id_comp]; exact KaroubiFiltration.iso_hom_inv_f e r
    · rw [hp0 r h]; simp
  have hgf : (karTruncTo pD pD_idem ≫ e.inv) ≫ e.hom ≫ karTruncFrom pD pD_idem = pD := by
    ext r; simp
  have hfk : F.proj.mapH τ ≫ (e.hom ≫ karTruncFrom pD pD_idem) ≫ pD =
      e.hom ≫ karTruncFrom pD pD_idem := by
    ext r
    simp only [comp_f, karTruncFrom_f, InvFunctor.mapH, Functor.mapHomologicalComplex_map_f, hτ,
      assoc, f_idem pD pD_idem]
    split_ifs with h
    · erw [id_comp]
    · rw [hp0 r h]; simp
  have hj : F.proj.mapH j'' ≫ e.hom ≫ karTruncFrom pD pD_idem = j := by
    rw [← assoc, hje, assoc, karTruncTo_comp_from, hjp]
  exact isKarEquiv_relDuality_of_strict (quotBd F hW hP).p_idem pD_idem
    (T.quotData F hW hP).pD_idem j_kar (T.quotData F hW hP).j_kar δφ (T.quotData F hW hP).δφ
    (quotBd F hW hP).dualHom_p_comp_φ _ _ hfg hgf hfk hj (fun r r' ↦ by
      have h₁ : (dualHom F.quot.inv (N + 1) e.inv).f r ≫ (dualHom F.quot.inv (N + 1) e.hom).f r =
          𝟙 _ := by
        rw [← comp_f, ← dualHom_comp, e.hom_inv_id, dualHom_id, id_f]
      have hk : ∀ {Z} (x : D.X r' ⟶ Z), (dualHom F.quot.inv (N + 1) (karTruncTo pD pD_idem)).f r ≫
          δφ.hom r r' ≫ (karTruncTo pD pD_idem).f r' ≫ x = δφ.hom r r' ≫ x :=
        fun x ↦ (reassoc_of% (δφ_kar r r')) x
      have hT : T.δφ.hom r r' = H r r' := rfl
      rw [quotData_δφ_hom, hT, dualHom_comp, comp_f, comp_f]
      simp only [assoc]
      rw [hk, ← hδ, ← hHe r r']
      simp only [assoc]
      rw [reassoc_of% h₁, KaroubiFiltration.iso_hom_inv_f]
      erw [comp_id]) poincare

/-- **The boundary is null-cobordant over `Kar(U)`** for a triad whose top is Poincaré modulo
`U` and free in degree `0`: compress (`exists_flat`), then `nullCobordant_lift_of_relBd'`. -/
theorem nullCobordant_lift_of_isPoincareTopMod (T : TriadOn W (PairData.zero P))
    (hP : ∀ r, F.U (P.C.X r)) (hW : W.IsPoincare) (hT : T.IsPoincareTopMod F)
    (hp0 : T.pE.f 0 = 𝟙 _) (hN : 0 ≤ N + 1) : NullCobordant (P.lift (U := F.U) hP) := by
  obtain ⟨ε, hε, hU, a, b, c, hab⟩ := T.exists_flat hT hp0 hN
  exact (T.flat ε hp0 hε hN).nullCobordant_lift_of_relBd' F hP hW
    (T.isPoincareTopMod_flat ε hp0 hε hW hP hU hN hT) a b c hab

/-- **(L2) for lifting pairs, relative boundary construction (consumer form).**  Let `P` be a
Poincaré complex of `A` with all chain objects in `U`, `W` a Poincaré pair on `P`, and suppose the
closed `(N+1)`-dimensional complex `W/U` of `A/U` bounds a Poincaré pair `Y` of `A/U` whose
idempotent is `1` on `[0, N + 2]`.  Then `P` is null-cobordant over `Kar(U)`. -/
theorem nullCobordant_lift_of_quotPair (hP : ∀ r, F.U (P.C.X r)) (hW : W.IsPoincare)
    (Y : PairOn (quotBd F hW hP)) (hpY : ∀ r, 0 ≤ r → r ≤ N + 1 + 1 → Y.pD.f r = 𝟙 _)
    (hN : 0 ≤ N + 1) : NullCobordant (P.lift (U := F.U) hP) := by
  obtain ⟨T, hT, -, hp0⟩ := exists_of_quotPair hW hP Y 0 le_rfl Y.support hpY
  exact T.nullCobordant_lift_of_isPoincareTopMod hP hW hT (hp0 0 le_rfl (by omega)) hN

/-- **(L2), the cobordism form** (connected case, for `LiftingClosedSub`): if moreover `Y` is
concentrated in `[1, N + 2]`, then `W` is cobordant rel `P` (the trace `T.trace`, a Poincaré triad)
to a Poincaré pair `Z` on `P` whose top is contractible modulo `U`. -/
theorem exists_relCobordant_of_quotPair (hP : ∀ r, F.U (P.C.X r)) (hW : W.IsPoincare)
    (Y : PairOn (quotBd F hW hP)) (hsY : SupportedIn Y.pD 1 (N + 1 + 1))
    (hpY : ∀ r, 1 ≤ r → r ≤ N + 1 + 1 → Y.pD.f r = 𝟙 _) :
    ∃ Z : PairOn P, (W.toPairOn hW).RelCobordant Z ∧ F.ContractibleMod Z.pD := by
  obtain ⟨T, hT, hs, -⟩ := exists_of_quotPair hW hP Y 1 zero_le_one hsY hpY
  exact ⟨T.relBd hW hs, T.relCobordant_relBd hs hW, T.contractibleMod_pZ hT⟩

end TriadOn

end

end HSFormal.LTheory
