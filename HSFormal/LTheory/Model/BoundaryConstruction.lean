import HSFormal.LTheory.BoundaryPoincare

/-!
# The boundary construction ([Ran80I, Prop. 3.4], absolute case; L-model module 9)

For an `(N+1)`-dimensional strictly symmetric complex `X = (C, p, φ)` in `Kar V` which is **not**
assumed Poincaré (`SymComplex`; in the paper's use `φ` is only an equivalence modulo `U`):

* `bdC = ∂C := Σ⁻¹ Cone(φ)` (mathlib's `homotopyCofiber`, `desusp` of `BoundaryPoincare`):
  `(∂C)_r = C^{N+1-r} ⊞ C_{r+1}` (`fstX`/`sndX` of `Cone(φ)_{r+1}`), `d(x, c) = (δx, -φx - dc)`,
  with Kar idempotent `bdP = p^* ⊕ p`.
* `bdφ = ∂φ₀ p_∂`, where `∂φ₀ = bdSwap` is, in the dual coordinates `(α, β) ∈ C_{r+1} ⊕ C^{N+1-r}`
  of `(∂C)^{N-r}` (`α = inlX^*`, `β = inrX^*`), the swap `∂φ₀(α, β) = ((-1)^{N+r} β, (-1)^{rN} α)`.
  Since `Tφ = φ` the structure is strictly symmetric with Ranicki's `φ_1 = 0`, so `∂φ_s = 0` for
  `s ≥ 1`.  `∂φ₀` is a chain **isomorphism** (`IsIso bdSwap`), hence `bdφ_poincare`.
* `bdJ = j : ∂C ⟶ C^{N+1-*}`, `(x, c) ↦ p^* x`, with `j ∂φ j^* = 0` strictly, so the relative
  boundary is `bdRel = 0`; `boundaryPair` is the `(N+1)`-dimensional Poincaré pair
  `(j : ∂C ⟶ C^{N+1-*}, (0, ∂φ))`: its relative duality map is `Ψ = (-1)^{N+1} (p ι)^*`
  (`relDuality_bdRel`) for `ι : C ⟶ Cone(j)`, `c ↦ ((0, c), 0)`, which has the strict left
  inverse `π((x, c), e) = c - φe` with `π ι ≃ 1` via `h((x, c), e) = ((e, 0), 0)`.
* Naturality: `mapBdIso : F(∂C) ≅ ∂(FC)` intertwines `p_∂`, `∂φ` and `j`; `boundaryMap` is the
  resulting strict isometry `F(∂X) ≃ ∂(FX)`.

**Sign conventions** (all checked by the identities, not cited).  Dual complex
`δ_r = (-1)^r d^*` and `(Tφ)_r = (-1)^{r(N-r)} φ_{N-r}^*` as in `SymmetricComplex`; mathlib cone
`d(x, c) = (-dx, φx + dc)`, `Σ⁻¹`: `d ↦ -d`.  Writing `∂φ₀(α, β) = (b_r β, a_r α)`, the chain map
condition forces `b_r = -b_{r-1}`, `a_r = (-1)^N a_{r-1}` and (with `Tφ = φ`)
`b_r = (-1)^{r + r(N+1-r)} a_{r-1}`; strict symmetry forces `b_r = (-1)^{r(N-r)} a_{N-r}`.  The
only free choice is the global sign `a_0`; we take `a_0 = 1`, i.e. `a_r = (-1)^{rN}`,
`b_r = (-1)^{N+r}`.  Under `diag(1, (-1)^r)` on `C^{n-r} ⊕ C_{r+1}` (`n = N + 1`), which converts
Ranicki's `d_{∂C} = [[d, (-)^r φ₀], [0, (-)^r d^*]]` into ours, this becomes the entries `1` on
`C^{n-r}` and `(-1)^{r(n-r-1)}` on `C_{r+1}` of Ranicki's `∂φ₀` (with `φ_1 = 0`).

**Support.**  `∂C_r` lives in `[-1, N+1]` (`∂C_{-1} = C_0`, `∂C_{N+1} = C^0`), as for Ranicki
(whose `∂C` is `N`-dimensional only for connected `C`).  `SymPoincare`/`SymPair` require
`[0, N]`, so `boundary`/`boundaryPair` assume `SupportedIn p 1 (N + 1)`; all raw statements
(`bdφ_poincare`, `isKarEquiv_relDuality`, …) hold without support hypotheses.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression
  homotopyCofiber

noncomputable section

universe v v' u u'

variable {V : Type u} [Category.{v} V] [Preadditive V] (J : StrictInvolution V) (N : ℤ)

/-- An `N`-dimensional strictly symmetric complex in `Kar V`, **not** necessarily Poincaré:
the data of `SymPoincare` without `support` and `poincare`. -/
structure SymComplex where
  C : ChainComplex V ℤ
  p : C ⟶ C
  p_idem : p ≫ p = p
  φ : dualComplex J N C ⟶ C
  φ_kar : dualHom J N p ≫ φ ≫ p = φ
  symm : IsStrictSymm J N φ

/-- Closes `u = v` for products and negations of `Int.negOnePow`s by parity. -/
macro "bd_sign_tac" : tactic =>
  `(tactic| (simp only [← Int.negOnePow_add, ← Int.negOnePow_succ, neg_neg]
             rw [Int.negOnePow_eq_iff]
             simp [parity_simps, ← Int.not_even_iff_odd]
             try tauto))

namespace SymComplex

variable {J N} (X : SymComplex J N)

attribute [reassoc (attr := simp)] p_idem

@[reassoc (attr := simp)]
lemma φ_comp_p : X.φ ≫ X.p = X.φ := by
  rw [← X.φ_kar]; simp

@[reassoc (attr := simp)]
lemma dualHom_p_comp_φ : dualHom J N X.p ≫ X.φ = X.φ := by
  conv_lhs => rw [← X.φ_kar]
  rw [← assoc, ← dualHom_comp, X.p_idem, X.φ_kar]

lemma comm : dualHom J N X.p ≫ X.φ = X.φ ≫ X.p := by simp

@[reassoc (attr := simp)]
lemma star_p_f_comp_φ_f (k : ℤ) : J.star (X.p.f (N - k)) ≫ X.φ.f k = X.φ.f k := by
  rw [← dualHom_f, ← comp_f, X.dualHom_p_comp_φ]

@[reassoc (attr := simp)]
lemma star_p_f_idem (k : ℤ) : J.star (X.p.f k) ≫ J.star (X.p.f k) = J.star (X.p.f k) := by
  rw [← J.star_comp, ← comp_f, X.p_idem]

@[reassoc (attr := simp)]
lemma φ_f_comp_p_f (k : ℤ) : X.φ.f k ≫ X.p.f k = X.φ.f k := by
  rw [← comp_f, X.φ_comp_p]

@[reassoc (attr := simp)]
lemma dualHom_p_idem : dualHom J N X.p ≫ dualHom J N X.p = dualHom J N X.p := by
  rw [← dualHom_comp, X.p_idem]

end SymComplex

/-- A Poincaré complex is in particular a symmetric complex. -/
@[simps]
def SymPoincare.toSymComplex {J : StrictInvolution V} {N : ℤ} (P : SymPoincare J N) :
    SymComplex J N :=
  ⟨P.C, P.p, P.p_idem, P.φ, P.φ_kar, P.symm⟩

namespace BoundaryConstruction

/-! Generic helpers (casts, stars of cone structure maps). -/

variable {J N} in
lemma dualComplex_XIsoOfEq_hom (K : ChainComplex V ℤ) {a b : ℤ} (h : a = b) :
    ((dualComplex J N K).XIsoOfEq h).hom = (K.XIsoOfEq (by omega : N - a = N - b)).hom := by
  subst h; simp

variable {J} in
@[simp]
lemma star_XIsoOfEq_hom (K : ChainComplex V ℤ) {a b : ℤ} (h : a = b) :
    J.star (K.XIsoOfEq h).hom = (K.XIsoOfEq h.symm).hom := by
  subst h; simp

variable {J} in
@[reassoc (attr := simp)]
lemma XIsoOfEq_hom_star_d (K : ChainComplex V ℤ) {b b' : ℤ} (h : b = b') (a : ℤ) :
    (K.XIsoOfEq h).hom ≫ J.star (K.d a b') = J.star (K.d a b) := by
  subst h; simp

@[reassoc (attr := simp)]
lemma XIsoOfEq_comp_f_comp_XIsoOfEq {K L : ChainComplex V ℤ} (f : K ⟶ L) {n n' : ℤ} (h : n = n')
    (h' : n' = n) : (K.XIsoOfEq h).hom ≫ f.f n' ≫ (L.XIsoOfEq h').hom = f.f n := by
  subst h; simp

section ConeStar

variable {J} [HasBinaryBiproducts V] {A B : ChainComplex V ℤ} (f : A ⟶ B)

@[reassoc (attr := simp)]
lemma star_d_star_inrX (i j : ℤ) :
    J.star (homotopyCofiber.d f i j) ≫ J.star (inrX f i) =
      J.star (inrX f j) ≫ J.star (B.d i j) := by
  rw [← J.star_comp, ← J.star_comp, inrX_d]

@[reassoc]
lemma star_d_star_inlX (i j k : ℤ) (hij : (ComplexShape.down ℤ).Rel i j)
    (hjk : (ComplexShape.down ℤ).Rel j k) :
    J.star (homotopyCofiber.d f i j) ≫ J.star (inlX f j i hij) =
      -(J.star (inlX f k j hjk) ≫ J.star (A.d j k)) + J.star (inrX f j) ≫ J.star (f.f j) := by
  rw [← J.star_comp, inlX_d f i j k hij hjk, J.star_add, J.star_neg, J.star_comp, J.star_comp]

@[reassoc (attr := simp)]
lemma eqToHom_desusp_fstX {a b : ℤ} (h : a = b) (k : ℤ) (hk : (ComplexShape.down ℤ).Rel (b + 1) k) :
    eqToHom (congrArg (desusp (cone f)).X h) ≫ fstX f (b + 1) k hk =
      fstX f (a + 1) k (by simp at hk ⊢; omega) := by
  subst h; simp

@[reassoc (attr := simp)]
lemma eqToHom_desusp_sndX {a b : ℤ} (h : a = b) :
    eqToHom (congrArg (desusp (cone f)).X h) ≫ sndX f (b + 1) =
      sndX f (a + 1) ≫ (B.XIsoOfEq (by rw [h])).hom := by
  subst h; simp

@[reassoc (attr := simp)]
lemma inlX_fstX_of_rel {a b c : ℤ} (h : (ComplexShape.down ℤ).Rel c a)
    (h' : (ComplexShape.down ℤ).Rel c b) :
    inlX f a c h ≫ fstX f c b h' = (A.XIsoOfEq (by simp at h h'; omega : a = b)).hom := by
  obtain rfl : b = a := by simp at h h'; omega
  simp

variable {B' D' : ChainComplex V ℤ} {j : A ⟶ B} {j' : D' ⟶ B'} {m : A ⟶ D'} {n : B ⟶ B'}
  (hmn : m ≫ j' = j ≫ n)

@[reassoc (attr := simp)]
lemma star_fstX_star_coneMap (i k : ℤ) (hk : (ComplexShape.down ℤ).Rel i k) :
    J.star (fstX j' i k hk) ≫ J.star ((coneMap m n hmn).f i) =
      J.star (m.f k) ≫ J.star (fstX j i k hk) := by
  rw [← J.star_comp, ← J.star_comp, coneMap_f_fstX]

@[reassoc (attr := simp)]
lemma star_sndX_star_coneMap (i : ℤ) :
    J.star (sndX j' i) ≫ J.star ((coneMap m n hmn).f i) = J.star (n.f i) ≫ J.star (sndX j i) := by
  rw [← J.star_comp, ← J.star_comp, coneMap_f_sndX]

end ConeStar

end BoundaryConstruction

open BoundaryConstruction

variable {J N} in
/-- A chain isomorphism `φ : C^{N-*} ≅ C` commuting with an idempotent `p` gives the Kar
equivalence `φ p : (C^{N-*}, p^*) ⟶ (C, p)`, with inverse `p φ⁻¹ p^*`. -/
lemma isPoincare_comp_of_isIso {C : ChainComplex V ℤ} {p : C ⟶ C} (hp : p ≫ p = p)
    (φ : dualComplex J N C ⟶ C) [IsIso φ] (h : dualHom J N p ≫ φ = φ ≫ p) :
    IsPoincare J N p (φ ≫ p) := by
  have hp' : dualHom J N p ≫ dualHom J N p = dualHom J N p := by rw [← dualHom_comp, hp]
  have hi : p ≫ inv φ = inv φ ≫ dualHom J N p := by
    rw [← cancel_epi φ, IsIso.hom_inv_id_assoc, ← reassoc_of% h, IsIso.hom_inv_id, comp_id]
  refine ⟨p ≫ inv φ ≫ dualHom J N p, by simp [reassoc_of% hp, hp'], ⟨Homotopy.ofEq ?_⟩,
    ⟨Homotopy.ofEq ?_⟩⟩
  · simp [reassoc_of% h, hp]
  · rw [assoc, reassoc_of% hp, reassoc_of% hi, IsIso.hom_inv_id_assoc, hp']

namespace SymComplex

variable {J N} [HasBinaryBiproducts V] (X : SymComplex J (N + 1))

/-- `∂C = Σ⁻¹ Cone(φ₀)`: `(∂C)_r = C^{N+1-r} ⊞ C_{r+1}` (`fstX`- and `sndX`-summand of
`Cone(φ)_{r+1}`), `d(x, c) = (δx, -φx - dc)`. -/
abbrev bdC : ChainComplex V ℤ := desusp (cone X.φ)

/-- The Kar idempotent `p^* ⊕ p` of `∂C`. -/
abbrev bdP : X.bdC ⟶ X.bdC := desuspMap (coneMap (dualHom J (N + 1) X.p) X.p X.comm)

lemma bdP_idem : X.bdP ≫ X.bdP = X.bdP := by
  rw [← desuspMap_comp, coneMap_idem _ X.dualHom_p_idem X.p_idem]

/-- The components of the uncompressed structure `∂φ₀ : ∂C^{N-*} ⟶ ∂C`: in the dual coordinates
`(α, β) ∈ C_{r+1} ⊕ C^{N+1-r}` of `∂C^{N-r}`, `∂φ₀(α, β) = ((-1)^{N+r} β, (-1)^{rN} α)`. -/
def swapF (r : ℤ) : (dualComplex J N X.bdC).X r ⟶ X.bdC.X r :=
  (r * N).negOnePow • (J.star (inlX X.φ (N - r) (N - r + 1) (down_rel_succ _)) ≫
      (X.C.XIsoOfEq (by omega : N + 1 - (N - r) = r + 1)).hom ≫ inrX X.φ (r + 1)) +
    (N + r).negOnePow • (J.star (inrX X.φ (N - r + 1)) ≫
      (X.C.XIsoOfEq (by omega : N - r + 1 = N + 1 - r)).hom ≫
        inlX X.φ r (r + 1) (down_rel_succ r))

@[reassoc]
lemma star_fstX_swapF (r b : ℤ) (h : (ComplexShape.down ℤ).Rel (N - r + 1) b) :
    J.star (fstX X.φ (N - r + 1) b h) ≫ X.swapF r = (r * N).negOnePow •
      ((X.C.XIsoOfEq (by simp at h; omega : N + 1 - b = r + 1)).hom ≫ inrX X.φ (r + 1)) := by
  obtain rfl : b = N - r := by simp at h; omega
  simp [swapF]

@[reassoc]
lemma star_sndX_swapF (r : ℤ) :
    J.star (sndX X.φ (N - r + 1)) ≫ X.swapF r = (N + r).negOnePow •
      ((X.C.XIsoOfEq (by omega : N - r + 1 = N + 1 - r)).hom ≫
        inlX X.φ r (r + 1) (down_rel_succ r)) := by
  simp [swapF]

@[reassoc]
lemma swapF_fstX (r c : ℤ) (h : (ComplexShape.down ℤ).Rel (r + 1) c) :
    X.swapF r ≫ fstX X.φ (r + 1) c h = (N + r).negOnePow •
      (J.star (inrX X.φ (N - r + 1)) ≫
        (X.C.XIsoOfEq (by simp at h; omega : N - r + 1 = N + 1 - c)).hom) := by
  obtain rfl : c = r := by simp at h; omega
  simp [swapF]

@[reassoc]
lemma swapF_sndX (r b : ℤ) (h : (ComplexShape.down ℤ).Rel (N - r + 1) b) :
    X.swapF r ≫ sndX X.φ (r + 1) = (r * N).negOnePow •
      (J.star (inlX X.φ b (N - r + 1) h) ≫
        (X.C.XIsoOfEq (by simp at h; omega : N + 1 - b = r + 1)).hom) := by
  obtain rfl : b = N - r := by simp at h; omega
  simp [swapF]

omit [HasBinaryBiproducts V] in
/-- Strict symmetry `Tφ = φ` in components: `φ_a^* = (-1)^{s(N+1-s)} φ_s` for `a + s = N + 1`. -/
@[reassoc]
lemma star_φ_f_XIsoOfEq (a s : ℤ) (h : N + 1 - a = s) :
    J.star (X.φ.f a) ≫ (X.C.XIsoOfEq h).hom = (s * (N + 1 - s)).negOnePow •
      ((X.C.XIsoOfEq (by omega : a = N + 1 - s)).hom ≫ X.φ.f s) := by
  have hs := congrArg (fun f ↦ f.f s) X.symm
  simp only [transposeHom_f] at hs
  obtain rfl : a = N + 1 - s := by omega
  rw [← hs]
  simp [smul_smul, XIsoOfEq]

lemma star_swapF (r : ℤ) :
    J.star (X.swapF r) = (r * N).negOnePow • (J.star (inrX X.φ (r + 1)) ≫
      (X.C.XIsoOfEq (by omega : r + 1 = N + 1 - (N - r))).hom ≫
        inlX X.φ (N - r) (N - r + 1) (down_rel_succ _)) +
    (N + r).negOnePow • (J.star (inlX X.φ r (r + 1) (down_rel_succ r)) ≫
      (X.C.XIsoOfEq (by omega : N + 1 - r = N - r + 1)).hom ≫ inrX X.φ (N - r + 1)) := by
  simp [swapF, J.star_add, J.star_comp, star_XIsoOfEq_hom]

/-- `∂φ₀` is a chain map. -/
def bdSwap : dualComplex J N X.bdC ⟶ X.bdC where
  f := X.swapF
  comm' r r' h := by
    obtain rfl : r = r' + 1 := by simp at h; omega
    apply ext_to_X X.φ (r' + 1) r' (down_rel_succ r')
    · simp [d_fstX X.φ (r' + 1 + 1) (r' + 1) r' (down_rel_succ _) (down_rel_succ _), swapF_fstX,
        swapF_fstX_assoc, star_d_XIsoOfEq]
      simp only [smul_smul, ← Units.neg_smul]
      congr 1
      bd_sign_tac
    · simp [d_sndX X.φ (r' + 1 + 1) (r' + 1) (down_rel_succ _), swapF_fstX_assoc,
        swapF_sndX_assoc X (r' + 1) (N - (r' + 1)) (down_rel_succ _),
        swapF_sndX X r' (N - (r' + 1) + 1) (by simp; omega),
        star_d_star_inlX_assoc X.φ (N - r' + 1) (N - (r' + 1) + 1) (N - (r' + 1)) (by simp; omega)
          (down_rel_succ _), star_φ_f_XIsoOfEq, smul_smul]
      simp only [← Units.neg_smul]
      refine Eq.trans (add_comm _ _) ?_
      congr 1 <;> congr 1 <;> bd_sign_tac

@[simp]
lemma bdSwap_f (r : ℤ) : X.bdSwap.f r = X.swapF r := rfl

/-- `∂φ₀` is strictly symmetric: `T ∂φ₀ = ∂φ₀`. -/
lemma bdSwap_symm : IsStrictSymm J N X.bdSwap := by
  ext r
  apply ext_to_X X.φ (r + 1) r (down_rel_succ r)
  · apply cone.ext_star (J := J) X.φ (N - r + 1) (N - r) (down_rel_succ _)
    · simp [transposeHom_f, swapF_fstX, star_swapF]
    · simp [transposeHom_f, swapF_fstX, star_swapF, smul_smul]
      simp only [XIsoOfEq, eqToIso.hom, eqToHom_trans]
      congr 1
      bd_sign_tac
  · apply cone.ext_star (J := J) X.φ (N - r + 1) (N - r) (down_rel_succ _)
    · simp [transposeHom_f, swapF_sndX X r (N - r) (down_rel_succ _), star_swapF, smul_smul]
      simp only [XIsoOfEq, eqToIso.hom, eqToHom_trans]
      congr 1
      bd_sign_tac
    · simp [transposeHom_f, swapF_sndX X r (N - r) (down_rel_succ _), star_swapF]

/-- `∂φ₀` commutes with the Kar idempotents: `p_∂^* ∂φ₀ = ∂φ₀ p_∂`. -/
lemma dualHom_bdP_comp_bdSwap : dualHom J N X.bdP ≫ X.bdSwap = X.bdSwap ≫ X.bdP := by
  ext r
  apply ext_to_X X.φ (r + 1) r (down_rel_succ r) <;>
    apply cone.ext_star (J := J) X.φ (N - r + 1) (N - r) (down_rel_succ _)
  · simp [star_fstX_swapF_assoc, swapF_fstX]
  · simp [star_sndX_swapF_assoc, swapF_fstX, star_f_XIsoOfEq]
  · simp [star_fstX_swapF_assoc, swapF_sndX X r (N - r) (down_rel_succ _), XIsoOfEq_hom_naturality]
  · simp [star_sndX_swapF_assoc, swapF_sndX X r (N - r) (down_rel_succ _)]

/-- The inverse components `(x, c) ↦ (α, β) = ((-1)^{rN} c, (-1)^{N+r} x)`. -/
def swapInvF (r : ℤ) : X.bdC.X r ⟶ (dualComplex J N X.bdC).X r :=
  (r * N).negOnePow • (sndX X.φ (r + 1) ≫
      (X.C.XIsoOfEq (by omega : r + 1 = N + 1 - (N - r))).hom ≫
        J.star (fstX X.φ (N - r + 1) (N - r) (down_rel_succ _))) +
    (N + r).negOnePow • (fstX X.φ (r + 1) r (down_rel_succ r) ≫
      (X.C.XIsoOfEq (by omega : N + 1 - r = N - r + 1)).hom ≫ J.star (sndX X.φ (N - r + 1)))

instance : IsIso X.bdSwap := by
  have (r : ℤ) : IsIso (X.bdSwap.f r) := by
    refine ⟨X.swapInvF r, ?_, ?_⟩
    · apply cone.ext_star (J := J) X.φ (N - r + 1) (N - r) (down_rel_succ _)
      · simp [star_fstX_swapF_assoc, swapInvF, smul_smul]
      · simp [star_sndX_swapF_assoc, swapInvF, smul_smul]
    · apply ext_to_X X.φ (r + 1) r (down_rel_succ r)
      · simp [swapF_fstX, swapInvF, smul_smul]
      · simp [swapF_sndX X r (N - r) (down_rel_succ _), swapInvF, smul_smul]
  exact Hom.isIso_of_components _

/-- **The boundary structure** `∂φ = ∂φ₀ p_∂ : (∂C^{N-*}, p_∂^*) ⟶ (∂C, p_∂)` (`φ_1 = 0` since `φ`
is strictly symmetric, so `∂φ` is Ranicki's `∂φ₀` and `∂φ_s = 0` for `s ≥ 1`). -/
@[implicit_reducible] def bdφ : dualComplex J N X.bdC ⟶ X.bdC := X.bdSwap ≫ X.bdP

lemma bdφ_kar : dualHom J N X.bdP ≫ X.bdφ ≫ X.bdP = X.bdφ := by
  rw [bdφ, assoc, reassoc_of% X.dualHom_bdP_comp_bdSwap, X.bdP_idem, X.bdP_idem]

lemma bdφ_symm : IsStrictSymm J N X.bdφ := by
  have h := transposeHom_comp (J := J) (N := N) (𝟙 X.bdC) X.bdSwap X.bdP
  simp only [dualHom_id, id_comp, comp_id] at h
  rw [IsStrictSymm, bdφ, h, X.bdSwap_symm, X.dualHom_bdP_comp_bdSwap]

/-- **∂C is Poincaré** ([Ran80I, Prop. 3.4]): `∂φ₀` is even a chain isomorphism. -/
lemma bdφ_poincare : IsPoincare J N X.bdP X.bdφ :=
  isPoincare_comp_of_isIso X.bdP_idem X.bdSwap X.dualHom_bdP_comp_bdSwap

/-- `p_∂` is compatible with the projection `∂C = Σ⁻¹Cone(φ) ⟶ C^{N+1-*}`. -/
@[reassoc]
lemma bdP_comp_coneFst : X.bdP ≫ coneFst X.φ = coneFst X.φ ≫ dualHom J (N + 1) X.p := by
  ext n; simp

/-- The relative boundary vanishes strictly: `i ∂φ₀ i^* = 0` for the projection `i`. -/
lemma dualHom_coneFst_comp_bdSwap_comp_coneFst :
    dualHom J N (coneFst X.φ) ≫ X.bdSwap ≫ coneFst X.φ = 0 := by
  ext r
  simp [star_fstX_swapF_assoc]

/-- **The boundary map** `j = i p^* : ∂C ⟶ C^{N+1-*}`, `(x, c) ↦ p^* x`. -/
def bdJ : X.bdC ⟶ dualComplex J (N + 1) X.C := coneFst X.φ ≫ dualHom J (N + 1) X.p

@[simp]
lemma bdJ_f (n : ℤ) :
    X.bdJ.f n = fstX X.φ (n + 1) n (down_rel_succ n) ≫ (dualHom J (N + 1) X.p).f n := rfl

lemma bdJ_kar : X.bdP ≫ X.bdJ ≫ dualHom J (N + 1) X.p = X.bdJ := by
  simp [bdJ, X.bdP_comp_coneFst_assoc]

lemma bdJ_rel : dualHom J N X.bdJ ≫ X.bdφ ≫ X.bdJ = 0 := by
  rw [bdJ, bdφ, dualHom_comp]
  simp only [assoc, X.bdP_comp_coneFst_assoc,
    reassoc_of% X.dualHom_coneFst_comp_bdSwap_comp_coneFst, zero_comp, comp_zero]

/-- The relative boundary `δ∂φ = 0` (a pair `(0, ∂φ)` as in [Ran80I, Prop. 3.4]). -/
def bdRel : Homotopy (dualHom J N X.bdJ ≫ X.bdφ ≫ X.bdJ) 0 := Homotopy.ofEq X.bdJ_rel

/-- `ι : C ⟶ Cone(j)`, `c ↦ ((0, c), 0)`. -/
def coneι : X.C ⟶ cone X.bdJ where
  f s := (X.C.XIsoOfEq (by omega : s = s - 1 + 1)).hom ≫ inrX X.φ (s - 1 + 1) ≫
    inlX X.bdJ (s - 1) s (down_rel_pred s)
  comm' s s' h := by
    obtain rfl : s' = s - 1 := by simp at h; omega
    apply ext_to_X X.bdJ (s - 1) (s - 1 - 1) (down_rel_pred _)
    · simp [inlX_d_assoc X.bdJ s (s - 1) (s - 1 - 1) (down_rel_pred s) (down_rel_pred _)]
    · simp [d_sndX X.bdJ s (s - 1) (down_rel_pred s)]

/-- `π : Cone(j) ⟶ C`, `((x, c), e) ↦ c - φ e`. -/
def coneπ : cone X.bdJ ⟶ X.C where
  f s := fstX X.bdJ s (s - 1) (down_rel_pred s) ≫ sndX X.φ (s - 1 + 1) ≫
      (X.C.XIsoOfEq (by omega : s - 1 + 1 = s)).hom - sndX X.bdJ s ≫ X.φ.f s
  comm' s s' h := by
    obtain rfl : s' = s - 1 := by simp at h; omega
    apply ext_from_X X.bdJ (s - 1) s (down_rel_pred s)
    · apply ext_from_X X.φ (s - 1) (s - 1 + 1) (down_rel_succ _)
      · simp [inlX_d_assoc X.bdJ s (s - 1) (s - 1 - 1) (down_rel_pred s) (down_rel_pred _),
          d_sndX_assoc X.φ (s - 1 + 1) (s - 1 - 1 + 1) (by simp)]
      · simp [inlX_d_assoc X.bdJ s (s - 1) (s - 1 - 1) (down_rel_pred s) (down_rel_pred _),
          d_sndX_assoc X.φ (s - 1 + 1) (s - 1 - 1 + 1) (by simp)]
    · simp

@[simp]
lemma coneι_f (s : ℤ) : X.coneι.f s = (X.C.XIsoOfEq (by omega : s = s - 1 + 1)).hom ≫
    inrX X.φ (s - 1 + 1) ≫ inlX X.bdJ (s - 1) s (down_rel_pred s) := rfl

@[simp]
lemma coneπ_f (s : ℤ) : X.coneπ.f s = fstX X.bdJ s (s - 1) (down_rel_pred s) ≫
    sndX X.φ (s - 1 + 1) ≫ (X.C.XIsoOfEq (by omega : s - 1 + 1 = s)).hom -
      sndX X.bdJ s ≫ X.φ.f s := rfl

@[reassoc (attr := simp)]
lemma coneι_coneπ : X.coneι ≫ X.coneπ = 𝟙 X.C := by
  ext s; simp

lemma bdP_comp_bdJ : X.bdP ≫ X.bdJ = X.bdJ ≫ dualHom J (N + 1) X.p := by
  simp [bdJ, X.bdP_comp_coneFst_assoc]

/-- The Kar idempotent `p_∂ ⊕ p^*` of `Cone(j)`. -/
abbrev coneIdem : cone X.bdJ ⟶ cone X.bdJ := coneMap X.bdP (dualHom J (N + 1) X.p) X.bdP_comp_bdJ

lemma coneIdem_comp_coneπ : X.coneIdem ≫ X.coneπ = X.coneπ ≫ X.p := by
  ext n
  apply ext_from_X X.bdJ (n - 1) n (down_rel_pred n)
  · apply ext_from_X X.φ (n - 1) (n - 1 + 1) (down_rel_succ _) <;>
      simp [XIsoOfEq_hom_naturality]
  · simp

set_option linter.unusedSimpArgs false in
/-- `coneIdem ≃ coneIdem π ι` via `h((x, c), e) = ((e, 0), 0)`. -/
def coneHomotopy : Homotopy X.coneIdem (X.coneIdem ≫ X.coneπ ≫ X.coneι) :=
  homotopyCongr ((Homotopy.nullHomotopy' (C := cone X.bdJ) (D := cone X.bdJ) fun a b h ↦
    sndX X.bdJ a ≫ inlX X.φ a (a + 1) (down_rel_succ a) ≫ inlX X.bdJ a b h).add
      (Homotopy.refl (X.coneIdem ≫ X.coneπ ≫ X.coneι))) (by
    ext n
    rw [add_f_apply, Homotopy.nullHomotopicMap'_f (down_rel_succ n) (down_rel_pred n)]
    have h₁ := d_sndX X.bdJ n (n - 1) (down_rel_pred n)
    have h₂ := inlX_d X.bdJ (n + 1) n (n - 1) (down_rel_succ n) (down_rel_pred n)
    have h₃ := d_fstX X.φ (n + 1) (n - 1 + 1) (n - 1) (by simp) (down_rel_succ _)
    have h₄ := d_sndX X.φ (n + 1) (n - 1 + 1) (by simp)
    apply ext_from_X X.bdJ (n - 1) n (down_rel_pred n)
    · apply ext_from_X X.φ (n - 1) (n - 1 + 1) (down_rel_succ _) <;>
        apply ext_to_X X.bdJ n (n - 1) (down_rel_pred n) <;>
        (try apply ext_to_X X.φ (n - 1 + 1) (n - 1) (down_rel_succ _)) <;>
        simp [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, reassoc_of% h₄,
          XIsoOfEq_hom_naturality]
    · apply ext_to_X X.bdJ n (n - 1) (down_rel_pred n) <;>
        (try apply ext_to_X X.φ (n - 1 + 1) (n - 1) (down_rel_succ _)) <;>
        simp [h₁, h₂, h₃, h₄, reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, reassoc_of% h₄,
          XIsoOfEq_hom_naturality, dualComplex_XIsoOfEq_hom]) (zero_add _)

@[simp]
lemma relTop_bdRel (r : ℤ) : relTop X.bdRel r = 0 := by
  simp [relTop, bdRel, Homotopy.ofEq]

@[reassoc]
lemma star_fstX_star_coneι (s k : ℤ) (h : (ComplexShape.down ℤ).Rel s k) :
    J.star (fstX X.bdJ s k h) ≫ J.star (X.coneι.f s) =
      J.star (inrX X.φ (k + 1)) ≫ (X.C.XIsoOfEq (by simp at h; omega : k + 1 = s)).hom := by
  obtain rfl : k = s - 1 := by simp at h; omega
  simp [← J.star_comp]
  simp [J.star_comp]

@[reassoc]
lemma star_sndX_star_coneι (s : ℤ) : J.star (sndX X.bdJ s) ≫ J.star (X.coneι.f s) = 0 := by
  simp [← J.star_comp]

/-- The relative duality map of the boundary pair is `(-1)^{N+1} (p ι)^*`. -/
lemma relDuality_bdRel :
    relDuality X.bdRel = (N + 1).negOnePow • dualHom J (N + 1) (X.p ≫ X.coneι) := by
  ext r
  apply cone.ext_star (J := J) X.bdJ (N + 1 - r) (N - r) (down_rel_sub N r)
  · simp [-coneι_f, bdφ, swapF_fstX_assoc, star_fstX_star_coneι_assoc, smul_smul]
    congr 1
    bd_sign_tac
  · simp [-coneι_f, bdφ, star_sndX_star_coneι_assoc]

/-- **The boundary pair is Poincaré** ([Ran80I, Prop. 3.4]): `Ψ = ±(p ι)^*` is a Kar equivalence,
with inverse `±(π p)^*`, since `ι π = 1` and `π ι ≃ 1` on `(Cone(j), p_∂ ⊕ p^*)`. -/
theorem isKarEquiv_relDuality :
    IsKarEquiv (dualHom J (N + 1) X.coneIdem) (dualHom J (N + 1) X.p) (relDuality X.bdRel) := by
  rw [relDuality_bdRel]
  suffices h : IsKarEquiv (dualHom J (N + 1) X.coneIdem) (dualHom J (N + 1) X.p)
      (dualHom J (N + 1) (X.p ≫ X.coneι)) by
    rcases Int.units_eq_one_or (N + 1).negOnePow with e | e <;> rw [e]
    · simpa using h
    · simpa using h.neg
  refine ⟨dualHom J (N + 1) (X.coneπ ≫ X.p), ?_, ⟨Homotopy.ofEq ?_⟩, ⟨homotopyCongr
    (dualHomotopy J (N + 1) X.coneHomotopy.symm) ?_ rfl⟩⟩
  · simp only [← dualHom_comp, assoc, reassoc_of% X.coneIdem_comp_coneπ, X.p_idem]
  · simp only [← dualHom_comp, assoc, X.coneι_coneπ_assoc, X.p_idem]
  · simp only [← dualHom_comp, assoc, reassoc_of% X.coneIdem_comp_coneπ, X.p_idem_assoc]

/-- Support: if `(C, p)` is concentrated in `[1, N+1]`, then `∂C` is concentrated in `[0, N]`.
(In general `∂C_r = C^{N+1-r} ⊕ C_{r+1}` lives in `[-1, N+1]`; Ranicki's `∂C` is
`(N)`-dimensional only up to the ends `C_0`, `C^0`.) -/
lemma bdP_support (h : SupportedIn X.p 1 (N + 1)) : SupportedIn X.bdP 0 N := by
  intro r hr
  rw [desuspMap_f, coneMap_f _ (r + 1) r (down_rel_succ r)]
  simp [h (r + 1) (by omega), h (N + 1 - r) (by omega)]

@[reassoc (attr := simp)]
lemma star_fstX_bdφ_f_fstX (r : ℤ) :
    J.star (fstX X.φ (N - r + 1) (N - r) (down_rel_succ _)) ≫ X.bdφ.f r ≫
      fstX X.φ (r + 1) r (down_rel_succ r) = 0 := by
  simp [bdφ, star_fstX_swapF_assoc]

@[reassoc (attr := simp)]
lemma star_fstX_bdφ_f_sndX (r : ℤ) :
    J.star (fstX X.φ (N - r + 1) (N - r) (down_rel_succ _)) ≫ X.bdφ.f r ≫ sndX X.φ (r + 1) =
      (r * N).negOnePow • ((X.C.XIsoOfEq (by omega : N + 1 - (N - r) = r + 1)).hom ≫
        X.p.f (r + 1)) := by
  simp [bdφ, star_fstX_swapF_assoc]

@[reassoc (attr := simp)]
lemma star_sndX_bdφ_f_fstX (r : ℤ) :
    J.star (sndX X.φ (N - r + 1)) ≫ X.bdφ.f r ≫ fstX X.φ (r + 1) r (down_rel_succ r) =
      (N + r).negOnePow • ((X.C.XIsoOfEq (by omega : N - r + 1 = N + 1 - r)).hom ≫
        J.star (X.p.f (N + 1 - r))) := by
  simp [bdφ, star_sndX_swapF_assoc]

@[reassoc (attr := simp)]
lemma star_sndX_bdφ_f_sndX (r : ℤ) :
    J.star (sndX X.φ (N - r + 1)) ≫ X.bdφ.f r ≫ sndX X.φ (r + 1) = 0 := by
  simp [bdφ, star_sndX_swapF_assoc]

/-- **The boundary** `∂(C, φ) = (∂C, p_∂, ∂φ)` ([Ran80I, Prop. 3.4]): an `N`-dimensional
strictly symmetric Poincaré complex (no Poincaré hypothesis on `φ`). -/
@[simps]
def boundary (h : SupportedIn X.p 1 (N + 1)) : SymPoincare J N where
  C := X.bdC
  p := X.bdP
  p_idem := X.bdP_idem
  support := X.bdP_support h
  φ := X.bdφ
  φ_kar := X.bdφ_kar
  symm := X.bdφ_symm
  poincare := X.bdφ_poincare

/-- **The boundary pair** `(j : ∂C ⟶ C^{N+1-*}, (0, ∂φ))` ([Ran80I, Prop. 3.4]): an
`(N+1)`-dimensional strictly symmetric Poincaré pair with boundary `∂(C, φ)`. -/
@[simps]
def boundaryPair (h : SupportedIn X.p 1 (N + 1)) : SymPair J N where
  bd := X.boundary h
  D := dualComplex J (N + 1) X.C
  pD := dualHom J (N + 1) X.p
  pD_idem := X.dualHom_p_idem
  support := (h.dualHom (J := J) (N := N + 1)).mono (by omega) (by omega)
  j := X.bdJ
  j_kar := X.bdJ_kar
  δφ := X.bdRel
  δφ_kar r r' := by simp [bdRel, Homotopy.ofEq]
  symm := by
    unfold IsSymmHomotopy
    erw [transposeHomotopy_hom]
    funext r r'
    simp [bdRel, Homotopy.ofEq, transposeHomFamily]
  poincare := X.isKarEquiv_relDuality

/-- `∂(C, φ)` is null-cobordant. -/
theorem nullCobordant_boundary (h : SupportedIn X.p 1 (N + 1)) :
    NullCobordant (X.boundary h) :=
  ⟨X.boundaryPair h, rfl⟩

end SymComplex

section Map

variable {J N} {W : Type u'} [Category.{v'} W] [Preadditive W] {J' : StrictInvolution W}
  (Φ : InvFunctor J J')

/-- The image `F(C, p, φ)` of a symmetric complex under a duality-preserving functor. -/
@[simps C p, implicit_reducible]
def SymComplex.map (X : SymComplex J N) : SymComplex J' N where
  C := Φ.mapC X.C
  p := Φ.mapH X.p
  p_idem := by rw [← Functor.map_comp, X.p_idem]
  φ := Φ.mapDual X.φ
  φ_kar := by
    rw [Φ.mapDual_eq, Φ.dualHom_mapH]
    simp only [assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, X.φ_kar]
  symm := by rw [IsStrictSymm, Φ.transposeHom_mapDual, X.symm]

lemma SymComplex.map_φ (X : SymComplex J N) : (X.map Φ).φ = Φ.mapDual X.φ := rfl

@[simp]
lemma SymComplex.map_φ_f (X : SymComplex J N) (r : ℤ) : (X.map Φ).φ.f r = Φ.F.map (X.φ.f r) := rfl

lemma SymPoincare.toSymComplex_map (P : SymPoincare J N) :
    (P.map Φ).toSymComplex = P.toSymComplex.map Φ := rfl

namespace BoundaryConstruction

lemma supportedIn_map {C : ChainComplex V ℤ} {p : C ⟶ C} {lo hi : ℤ} (h : SupportedIn p lo hi) :
    SupportedIn (Φ.mapH p) lo hi :=
  fun r hr ↦ by simp [h r hr]

@[simp]
lemma map_XIsoOfEq_hom (K : ChainComplex V ℤ) {a b : ℤ} (h : a = b) :
    Φ.F.map (K.XIsoOfEq h).hom = ((Φ.mapC K).XIsoOfEq h).hom := by
  subst h; simp

@[simp]
lemma map_units_smul {A B : V} (u : ℤˣ) (f : A ⟶ B) :
    Φ.F.map (u • f) = u • Φ.F.map f := by
  rw [Units.smul_def, Functor.map_zsmul, ← Units.smul_def]

variable [HasBinaryBiproducts V] {A B : ChainComplex V ℤ} (f : A ⟶ B)

@[reassoc (attr := simp)]
lemma map_inlX_fstX (i k : ℤ) (h : (ComplexShape.down ℤ).Rel i k) :
    Φ.F.map (inlX f k i h) ≫ Φ.F.map (fstX f i k h) = 𝟙 _ := by
  rw [← Φ.F.map_comp, inlX_fstX, Φ.F.map_id]

@[reassoc (attr := simp)]
lemma map_inlX_sndX (i k : ℤ) (h : (ComplexShape.down ℤ).Rel i k) :
    Φ.F.map (inlX f k i h) ≫ Φ.F.map (sndX f i) = 0 := by
  rw [← Φ.F.map_comp, inlX_sndX, Φ.F.map_zero]

@[reassoc (attr := simp)]
lemma map_inrX_fstX (i k : ℤ) (h : (ComplexShape.down ℤ).Rel i k) :
    Φ.F.map (inrX f i) ≫ Φ.F.map (fstX f i k h) = 0 := by
  rw [← Φ.F.map_comp, inrX_fstX, Φ.F.map_zero]

@[reassoc (attr := simp)]
lemma map_inrX_sndX (i : ℤ) : Φ.F.map (inrX f i) ≫ Φ.F.map (sndX f i) = 𝟙 _ := by
  rw [← Φ.F.map_comp, inrX_sndX, Φ.F.map_id]

lemma map_cone_ext_from (i k : ℤ) (h : (ComplexShape.down ℤ).Rel i k) {T : W}
    {a b : Φ.F.obj ((cone f).X i) ⟶ T}
    (h₁ : Φ.F.map (inlX f k i h) ≫ a = Φ.F.map (inlX f k i h) ≫ b)
    (h₂ : Φ.F.map (inrX f i) ≫ a = Φ.F.map (inrX f i) ≫ b) : a = b := by
  have e : 𝟙 (Φ.F.obj ((cone f).X i)) = Φ.F.map (fstX f i k h) ≫ Φ.F.map (inlX f k i h) +
      Φ.F.map (sndX f i) ≫ Φ.F.map (inrX f i) := by
    rw [← Φ.F.map_comp, ← Φ.F.map_comp, ← Φ.F.map_add, ← cone.id_X]
    exact (Φ.F.map_id _).symm
  rw [← id_comp a, ← id_comp b, e]
  simp only [add_comp, assoc, h₁, h₂]

end BoundaryConstruction

variable [HasBinaryBiproducts V]

variable [HasBinaryBiproducts W]

namespace SymComplex

variable (X : SymComplex J (N + 1))

/-- Components of the comparison `F(∂C) ≅ ∂(FC)`. -/
def mapBdIsoX (r : ℤ) : (Φ.mapC X.bdC).X r ≅ (X.map Φ).bdC.X r where
  hom := Φ.F.map (fstX X.φ (r + 1) r (down_rel_succ r)) ≫
      inlX (X.map Φ).φ r (r + 1) (down_rel_succ r) +
    Φ.F.map (sndX X.φ (r + 1)) ≫ inrX (X.map Φ).φ (r + 1)
  inv := fstX (X.map Φ).φ (r + 1) r (down_rel_succ r) ≫
      Φ.F.map (inlX X.φ r (r + 1) (down_rel_succ r)) +
    sndX (X.map Φ).φ (r + 1) ≫ Φ.F.map (inrX X.φ (r + 1))
  hom_inv_id := by
    apply map_cone_ext_from Φ X.φ (r + 1) r (down_rel_succ r) <;> simp
  inv_hom_id := by
    apply ext_from_X (X.map Φ).φ r (r + 1) (down_rel_succ r) <;> simp

@[reassoc (attr := simp)]
lemma map_inlX_mapBdIsoX (r : ℤ) : Φ.F.map (inlX X.φ r (r + 1) (down_rel_succ r)) ≫
    (X.mapBdIsoX Φ r).hom = inlX (X.map Φ).φ r (r + 1) (down_rel_succ r) := by
  simp [mapBdIsoX]

@[reassoc (attr := simp)]
lemma map_inrX_mapBdIsoX (r : ℤ) :
    Φ.F.map (inrX X.φ (r + 1)) ≫ (X.mapBdIsoX Φ r).hom = inrX (X.map Φ).φ (r + 1) := by
  simp [mapBdIsoX]

@[reassoc (attr := simp)]
lemma mapBdIsoX_fstX (r : ℤ) : (X.mapBdIsoX Φ r).hom ≫ fstX (X.map Φ).φ (r + 1) r
    (down_rel_succ r) = Φ.F.map (fstX X.φ (r + 1) r (down_rel_succ r)) := by
  simp [mapBdIsoX]

@[reassoc (attr := simp)]
lemma mapBdIsoX_sndX (r : ℤ) :
    (X.mapBdIsoX Φ r).hom ≫ sndX (X.map Φ).φ (r + 1) = Φ.F.map (sndX X.φ (r + 1)) := by
  simp [mapBdIsoX]

/-- **Naturality**: `F(∂C) ≅ ∂(FC)`. -/
def mapBdIso : Φ.mapC X.bdC ≅ (X.map Φ).bdC :=
  Hom.isoOfComponents (X.mapBdIsoX Φ) (fun r r' h ↦ by
    obtain rfl : r = r' + 1 := by simp at h; omega
    have h₁ := inlX_d (X.map Φ).φ (r' + 1 + 1) (r' + 1) r' (down_rel_succ _) (down_rel_succ _)
    have h₂ := inlX_d X.φ (r' + 1 + 1) (r' + 1) r' (down_rel_succ _) (down_rel_succ _)
    have h₃ := d_sndX (X.map Φ).φ (r' + 1 + 1) (r' + 1) (down_rel_succ _)
    have h₄ := d_sndX X.φ (r' + 1 + 1) (r' + 1) (down_rel_succ _)
    apply map_cone_ext_from Φ X.φ (r' + 1 + 1) (r' + 1) (down_rel_succ _) <;>
      apply ext_to_X (X.map Φ).φ (r' + 1) r' (down_rel_succ _) <;>
      simp <;> simp only [← Functor.map_comp] <;>
      simp [reassoc_of% h₁, reassoc_of% h₂, h₃, h₄, Φ.map_star])

@[simp]
lemma mapBdIso_hom_f (r : ℤ) : (X.mapBdIso Φ).hom.f r = (X.mapBdIsoX Φ r).hom := rfl

@[simp]
lemma mapBdIso_inv_f (r : ℤ) : (X.mapBdIso Φ).inv.f r = (X.mapBdIsoX Φ r).inv := rfl

@[reassoc (attr := simp)]
lemma star_fstX_star_mapBdIsoX (s : ℤ) :
    J'.star (fstX (X.map Φ).φ (s + 1) s (down_rel_succ s)) ≫ J'.star (X.mapBdIsoX Φ s).hom =
      Φ.F.map (J.star (fstX X.φ (s + 1) s (down_rel_succ s))) := by
  rw [← J'.star_comp, Φ.map_star]; congr 1; simp

@[reassoc (attr := simp)]
lemma star_sndX_star_mapBdIsoX (s : ℤ) :
    J'.star (sndX (X.map Φ).φ (s + 1)) ≫ J'.star (X.mapBdIsoX Φ s).hom =
      Φ.F.map (J.star (sndX X.φ (s + 1))) := by
  rw [← J'.star_comp, Φ.map_star]; congr 1; simp

lemma mapBdIso_hom_comp_bdP :
    (X.mapBdIso Φ).hom ≫ (X.map Φ).bdP = Φ.mapH X.bdP ≫ (X.mapBdIso Φ).hom := by
  ext r
  apply map_cone_ext_from Φ X.φ (r + 1) r (down_rel_succ r) <;>
    apply ext_to_X (X.map Φ).φ (r + 1) r (down_rel_succ r) <;>
    simp <;> simp only [← Functor.map_comp] <;> simp [Φ.map_star]

lemma mapBdIso_bdφ :
    dualHom J' N (X.mapBdIso Φ).hom ≫ Φ.mapDual X.bdφ ≫ (X.mapBdIso Φ).hom = (X.map Φ).bdφ := by
  ext r
  apply ext_to_X (X.map Φ).φ (r + 1) r (down_rel_succ r) <;>
    apply cone.ext_star (J := J') (X.map Φ).φ (N - r + 1) (N - r) (down_rel_succ _)
  all_goals simp
  all_goals simp only [← Functor.map_comp]
  all_goals simp [Φ.map_star]

/-- The boundary maps correspond: `F(j) = j_{FC}` under `F(∂C) ≅ ∂(FC)`. -/
lemma mapBdIso_hom_comp_bdJ :
    (X.mapBdIso Φ).hom ≫ (X.map Φ).bdJ = Φ.mapH X.bdJ ≫ (Φ.mapDualIso (N + 1) X.C).hom := by
  ext r
  simp [Φ.map_star]

/-- **Naturality of the boundary** under duality-preserving functors: `F(∂C, ∂φ)` and
`∂(FC, Fφ)` are (strictly) isometric. -/
def boundaryMap (h : SupportedIn X.p 1 (N + 1)) :
    SymPoincare.HomotopyIsometry ((X.boundary h).map Φ)
      ((X.map Φ).boundary (supportedIn_map Φ h)) :=
  .ofIso (X.mapBdIso Φ) (X.mapBdIso_hom_comp_bdP Φ) (X.mapBdIso_bdφ Φ)

lemma boundary_map_isometric (h : SupportedIn X.p 1 (N + 1)) :
    SymPoincare.Isometric ((X.boundary h).map Φ) ((X.map Φ).boundary (supportedIn_map Φ h)) :=
  ⟨X.boundaryMap Φ h⟩

@[simp]
lemma boundaryPair_map_bd (h : SupportedIn X.p 1 (N + 1)) :
    ((X.boundaryPair h).map Φ).bd = (X.boundary h).map Φ := rfl

end SymComplex

end Map

end

end HSFormal.LTheory
