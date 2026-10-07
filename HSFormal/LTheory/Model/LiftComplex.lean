import HSFormal.LTheory.Model.Cascade
import HSFormal.LTheory.Pairs

/-!
# Honest strict lifts of Kar complexes and pairs (lower L-theory model, module 13)

Plan (L1-ii) and its relative version for (L2), for a `KaroubiFiltration F : U ⊂ A`.

* **Kar truncation.**  For a chain idempotent `p`, `karTrunc p = (C, p d)` is a complex,
  `(C, p) ≅ (karTrunc p, p)` in `Kar`, and it vanishes where `p` does.  `degTrunc` is the strict
  chain idempotent `1_{[lo, hi]}` of a complex whose differential vanishes across `lo` and `hi`.
* **Absolute lift.**  `QuotPoincare F N`: an honest strictly symmetric Kar complex
  `(C, p, φ)` of `A`, supported in `[0, N]`, which is Poincaré modulo `U`; `toQuot` is its image.
  `exists_quotPoincare`: a Poincaré complex `P` of `A/U` whose idempotent is `1` on `[0, N]` (a
  free complex, e.g. after the free-ification (L1-i)) is strictly isometric to the image of a
  `QuotPoincare` whose idempotent is the degree truncation `degTrunc`.  (A general Kar idempotent
  of `A/U` does not lift: this is why (L1-i) precedes (L1-ii).)
* **Relative lift (boundary frozen).**  `RelLift`: an *honest* boundary `B` with a family
  `ψ_r : B_{N-r} ⟶ B_r` (e.g. a symmetric structure, or a non-closed one in a triad), and modulo
  `I_U` an interior `X`, a map `j̃ : B ⟶ X` and a relative structure `H̃` with
  `j̃^* ψ j̃ ≡ δ̃ H̃ + H̃ d̃`.  `SymLift.exists_cascade_with` extends `exists_cascade` by further
  eventual conditions; the frozen boundary only contributes such conditions on the splittings of
  the interior (`j̃ d̃ - d j̃` and the relative defect are killed), so no compatibility of the
  splittings with a subobject is needed.  (`exists_cascade_extend` instead freezes a partial
  cascade given in degrees `≥ r₀` and extends it downward.)  `RelLift.Cascade`: `j'' = j̃ πU` is
  an honest chain map `B ⟶ C''` and `H'' = ιU H̃ πU` satisfies `j''^* ψ j'' = δ H'' + H'' d`
  on the nose (`relH_comm`), symmetric if `H̃` is (`relH_symm`).  `exists_relLift`: the version
  over `A/U`.
* **Pairs.**  `QuotPair L`: an honest strictly symmetric pair of `A` on the frozen boundary `L`,
  Poincaré modulo `U`; `toQuot` is its image, a `SymPair` of `A/U` with boundary `L.toQuot`.
  `exists_quotPair`: a free Poincaré pair of `A/U` on `L.toQuot` is strictly isometric rel
  boundary to the image of a `QuotPair L` (Poincaré duality transported by
  `isKarEquiv_relDuality_of_strict`, via naturality of `relDuality` in the interior).

Module 16 consumes `exists_quotPoincare` (then (L1-iii) on `(L.C, L.p, L.φ)`; `L.poincare` makes
`∂C''` contractible modulo `U`); module 17 consumes `exists_quotPair` / `exists_relLift`.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression

noncomputable section

namespace LiftComplex

variable {V : Type*} [Category V] [Preadditive V]

/-! ### Kar and degree truncations -/

section Trunc

variable {C : ChainComplex V ℤ} (p : C ⟶ C)

@[reassoc]
lemma f_idem (hp : p ≫ p = p) (r : ℤ) : p.f r ≫ p.f r = p.f r := by rw [← comp_f, hp]

/-- `(C, p d)` for a chain idempotent `p`. -/
@[simps, implicit_reducible]
def karTrunc (hp : p ≫ p = p) : ChainComplex V ℤ where
  X := C.X
  d i j := p.f i ≫ C.d i j
  shape i j h := by rw [C.shape i j h, comp_zero]
  d_comp_d' i j k _ _ := by
    rw [assoc, ← p.comm_assoc, f_idem_assoc p hp, C.d_comp_d, comp_zero]

/-- `p : C ⟶ karTrunc p`. -/
@[simps]
def karTruncTo (hp : p ≫ p = p) : C ⟶ karTrunc p hp where
  f := p.f
  comm' i j _ := by simp only [karTrunc_d]; rw [f_idem_assoc p hp, p.comm]

/-- `p : karTrunc p ⟶ C`. -/
@[simps]
def karTruncFrom (hp : p ≫ p = p) : karTrunc p hp ⟶ C where
  f := p.f
  comm' i j _ := by simp only [karTrunc_d, assoc]; rw [← p.comm, f_idem_assoc p hp]

@[reassoc (attr := simp)]
lemma karTruncTo_comp_from (hp : p ≫ p = p) : karTruncTo p hp ≫ karTruncFrom p hp = p := by
  ext r; simp [f_idem p hp]

variable (C) (lo hi : ℤ) (hC : ∀ i j, ¬ (lo ≤ i ∧ i ≤ hi ∧ lo ≤ j ∧ j ≤ hi) → C.d i j = 0)

/-- The degree truncation `1_{[lo, hi]}`, a strict chain idempotent when `d` vanishes across the
boundary of `[lo, hi]`. -/
@[simps]
def degTrunc : C ⟶ C where
  f r := if lo ≤ r ∧ r ≤ hi then 𝟙 _ else 0
  comm' i j _ := by
    by_cases h : lo ≤ i ∧ i ≤ hi ∧ lo ≤ j ∧ j ≤ hi
    · simp [h.1, h.2.1, h.2.2.1, h.2.2.2]
    · rw [hC i j h]; simp

variable {C lo hi}

lemma degTrunc_f_of_mem {r : ℤ} (h : lo ≤ r ∧ r ≤ hi) : (degTrunc C lo hi hC).f r = 𝟙 _ :=
  if_pos h

lemma degTrunc_f_of_not_mem {r : ℤ} (h : ¬ (lo ≤ r ∧ r ≤ hi)) : (degTrunc C lo hi hC).f r = 0 :=
  if_neg h

lemma degTrunc_idem : degTrunc C lo hi hC ≫ degTrunc C lo hi hC = degTrunc C lo hi hC := by
  ext r; by_cases h : lo ≤ r ∧ r ≤ hi <;> simp [h]

lemma supportedIn_degTrunc : SupportedIn (degTrunc C lo hi hC) lo hi :=
  fun _ hr ↦ degTrunc_f_of_not_mem hC (by omega)

end Trunc

/-! ### Strict isometries -/

variable {J : StrictInvolution V} {N : ℤ}

/-- A Kar complex strictly isometric to a Poincaré complex is Poincaré. -/
lemma isPoincare_of_strict (P : SymPoincare J N) {C : ChainComplex V ℤ} {p : C ⟶ C}
    {φ : dualComplex J N C ⟶ C} (hφ : dualHom J N p ≫ φ ≫ p = φ) (f : C ⟶ P.C) (g : P.C ⟶ C)
    (hfg : f ≫ g = p) (hgf : g ≫ f = P.p) (hpf : p ≫ f = f)
    (hconj : dualHom J N f ≫ φ ≫ f = P.φ) : IsPoincare J N p φ := by
  obtain ⟨ψ, -, ⟨H₁⟩, ⟨H₂⟩⟩ := P.poincare
  have hfp : f ≫ P.p = f := by rw [← hgf, ← assoc, hfg, hpf]
  have h₁ : dualHom J N f ≫ φ = P.φ ≫ g := by
    calc dualHom J N f ≫ φ = dualHom J N (g ≫ f) ≫ (dualHom J N f ≫ φ ≫ f) ≫ g := by
          conv_lhs => rw [← hφ, ← hfg]
          simp only [dualHom_comp, assoc]
      _ = P.φ ≫ g := by rw [hgf, hconj, P.dualHom_p_comp_φ_assoc]
  have h₂ : φ ≫ f = dualHom J N g ≫ P.φ := by
    calc φ ≫ f = dualHom J N g ≫ (dualHom J N f ≫ φ ≫ f) ≫ g ≫ f := by
          conv_lhs => rw [← hφ, ← hfg]
          simp only [dualHom_comp, assoc]
      _ = dualHom J N g ≫ P.φ := by rw [hgf, hconj, P.φ_comp_p]
  refine ⟨f ≫ ψ ≫ dualHom J N f, ?_, ⟨homotopyCongr ((H₁.compRight g).compLeft f) ?_ ?_⟩,
    ⟨homotopyCongr ((H₂.compRight (dualHom J N f)).compLeft (dualHom J N g)) ?_ ?_⟩⟩
  · simp only [assoc, reassoc_of% hpf]; rw [← dualHom_comp, hpf]
  · simp only [assoc, h₁]
  · rw [reassoc_of% hfp, hfg]
  · rw [reassoc_of% h₂]; simp only [assoc]
  · rw [← dualHom_comp, ← dualHom_comp, hfp, hfg]

/-- A strict isometry `Q ≅ P` of Kar complexes. -/
def strictIsometry {P Q : SymPoincare J N} (f : Q.C ⟶ P.C) (g : P.C ⟶ Q.C) (hfg : f ≫ g = Q.p)
    (hgf : g ≫ f = P.p) (hpf : Q.p ≫ f = f) (hgp : P.p ≫ g = g)
    (hconj : dualHom J N f ≫ Q.φ ≫ f = P.φ) : SymPoincare.HomotopyIsometry Q P where
  f := f
  g := g
  f_kar := by rw [reassoc_of% hpf, ← hgf, ← assoc, hfg, hpf]
  g_kar := by rw [reassoc_of% hgp, ← hfg, ← assoc, hgf, hgp]
  fg := Homotopy.ofEq hfg
  gf := Homotopy.ofEq hgf
  conj := Homotopy.ofEq hconj

lemma _root_.HSFormal.LTheory.InvFunctor.mapDual_kar {W : Type*} [Category W] [Preadditive W]
    {J' : StrictInvolution W} (Φ : InvFunctor J J') {C : ChainComplex V ℤ} {p : C ⟶ C}
    {φ : dualComplex J N C ⟶ C} (h : dualHom J N p ≫ φ ≫ p = φ) :
    dualHom J' N (Φ.mapH p) ≫ Φ.mapDual φ ≫ Φ.mapH p = Φ.mapDual φ := by
  rw [Φ.mapDual_eq, Φ.dualHom_mapH]
  simp only [assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, h]

/-! ### Transposing families -/

/-- The complex with objects `X` and zero differential, to transpose families on `X`. -/
@[simps, implicit_reducible]
def zeroCx (X : ℤ → V) : ChainComplex V ℤ where
  X := X
  d _ _ := 0

/-- `T² = 1` on families `h_{r,r'} : X_{N-r} ⟶ X_{r'}` vanishing unless `r' = r + 1`. -/
lemma transposeHomFamily_zeroCx {X : ℤ → V} (h : ∀ i j, X (N - i) ⟶ X j)
    (hh : ∀ i j, ¬ (ComplexShape.down ℤ).Rel j i → h i j = 0) :
    transposeHomFamily J N (C := zeroCx X) (D := zeroCx X)
      (transposeHomFamily J N (C := zeroCx X) (D := zeroCx X) h) = h :=
  transposeHomFamily_transposeHomFamily (J := J) (N := N) (C := zeroCx X) (D := zeroCx X)
    (φ := 0) (φ' := 0)
    { hom := h
      zero := hh
      comm := fun i ↦ by
        rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel i (i - 1) by simp),
          prevD_eq _ (show (ComplexShape.down ℤ).Rel (i + 1) i by simp)]
        simp }

/-! ### Transport of pairs rel boundary -/

section Pairs

open homotopyCofiber

variable [HasBinaryBiproducts V] {B D D' : ChainComplex V ℤ} {φ : dualComplex J N B ⟶ B}
  {pB : B ⟶ B} {j : B ⟶ D} {j' : B ⟶ D'}

/-- Naturality of the relative duality map `Ψ` in the interior. -/
lemma dualHom_coneMap_comp_relDuality_comp (n : D ⟶ D') (h : pB ≫ j' = j ≫ n)
    (H : Homotopy (dualHom J N j ≫ φ ≫ j) 0) (H' : Homotopy (dualHom J N j' ≫ φ ≫ j') 0)
    (hφ : dualHom J N pB ≫ φ = φ) (hj : j ≫ n = j')
    (hH : ∀ r r', (dualHom J N n).f r ≫ H.hom r r' ≫ n.f r' = H'.hom r r') :
    dualHom J (N + 1) (coneMap pB n h) ≫ relDuality H ≫ n = relDuality H' := by
  have hφ' (r : ℤ) {Z : V} (g : B.X r ⟶ Z) : J.star (pB.f (N - r)) ≫ φ.f r ≫ g = φ.f r ≫ g := by
    rw [← dualHom_f, ← comp_f_assoc, hφ]
  have hj' (r : ℤ) : j.f r ≫ n.f r = j'.f r := by rw [← comp_f, hj]
  have hT (r : ℤ) : J.star (n.f (N + 1 - r)) ≫ relTop H r ≫ n.f r = relTop H' r := by
    rw [relTop, relTop]; simp only [assoc]
    rw [star_f_XIsoOfEq_assoc, ← hH (r - 1) r, dualHom_f]
  ext r
  simp [star_coneMap_f h _ _ (down_rel_sub N r), hφ', hj', hT]

omit [HasBinaryBiproducts V] in
lemma isKarEquiv_of_strict {X Y : ChainComplex V ℤ} {e : X ⟶ X} {e' : Y ⟶ Y} (u : X ⟶ Y)
    (v : Y ⟶ X) (huv : u ≫ v = e) (hvu : v ≫ u = e') (hv : e' ≫ v ≫ e = v) :
    IsKarEquiv e e' u :=
  ⟨v, hv, ⟨Homotopy.ofEq hvu⟩, ⟨Homotopy.ofEq huv⟩⟩

lemma coneMap_congr {m m' : B ⟶ B} {n n' : D ⟶ D'} (hm : m = m') (hn : n = n')
    (h : m ≫ j' = j ≫ n) (h' : m' ≫ j' = j ≫ n') : coneMap m n h = coneMap m' n' h' := by
  subst hm hn; rfl

/-- **Transport of Poincaré duality of pairs** along a strict Kar isomorphism `f, g` of the
interiors, rel the common boundary `(B, p_B, φ)`, compatible with `j` and `δφ`. -/
lemma isKarEquiv_relDuality_of_strict {pD : D ⟶ D} {pD' : D' ⟶ D'} (hB : pB ≫ pB = pB)
    (hD : pD ≫ pD = pD) (hD' : pD' ≫ pD' = pD') (hjk : pB ≫ j ≫ pD = j)
    (hjk' : pB ≫ j' ≫ pD' = j') (H : Homotopy (dualHom J N j ≫ φ ≫ j) 0)
    (H' : Homotopy (dualHom J N j' ≫ φ ≫ j') 0) (hφ : dualHom J N pB ≫ φ = φ) (f : D' ⟶ D)
    (g : D ⟶ D') (hfg : f ≫ g = pD') (hgf : g ≫ f = pD) (hfk : pD' ≫ f ≫ pD = f)
    (hj : j' ≫ f = j) (hH : ∀ r r', (dualHom J N g).f r ≫ H.hom r r' ≫ g.f r' = H'.hom r r')
    (hP : IsKarEquiv (dualHom J (N + 1) (coneMap pB pD (comm_of_kar hB hD hjk))) pD
      (relDuality H)) :
    IsKarEquiv (dualHom J (N + 1) (coneMap pB pD' (comm_of_kar hB hD' hjk'))) pD'
      (relDuality H') := by
  have e₁ : pB ≫ j' = j' := by
    conv_lhs => rw [← hjk']
    rw [reassoc_of% hB, hjk']
  have e₂ : pB ≫ j = j := by
    conv_lhs => rw [← hjk]
    rw [reassoc_of% hB, hjk]
  have e₃ : j' ≫ pD' = j' := by
    conv_lhs => rw [← hjk']
    rw [assoc, assoc, hD', hjk']
  have hjg : j ≫ g = j' := by rw [← hj, assoc, hfg, e₃]
  have h₁ : pB ≫ j' = j ≫ g := by rw [e₁, hjg]
  have h₂ : pB ≫ j = j' ≫ f := by rw [e₂, hj]
  have hu : IsKarEquiv (dualHom J (N + 1) (coneMap pB pD' (comm_of_kar hB hD' hjk')))
      (dualHom J (N + 1) (coneMap pB pD (comm_of_kar hB hD hjk)))
      (dualHom J (N + 1) (coneMap pB g h₁)) :=
    isKarEquiv_of_strict _ (dualHom J (N + 1) (coneMap pB f h₂))
      (by rw [← dualHom_comp, coneMap_comp, coneMap_congr hB hfg])
      (by rw [← dualHom_comp, coneMap_comp, coneMap_congr hB hgf])
      (by rw [← dualHom_comp, ← dualHom_comp, coneMap_comp, coneMap_comp,
        coneMap_congr (by rw [hB, hB]) (by rw [assoc, hfk])])
  have hidem {X : ChainComplex V ℤ} {e : X ⟶ X} (he : e ≫ e = e) :
      dualHom J (N + 1) e ≫ dualHom J (N + 1) e = dualHom J (N + 1) e := by
    rw [← dualHom_comp, he]
  refine ((hu.comp hP (hidem (coneMap_idem _ hB hD')) (hidem (coneMap_idem _ hB hD)) hD).comp
    (isKarEquiv_of_strict g f hgf hfg hfk) (hidem (coneMap_idem _ hB hD')) hD hD').of_eq ?_
  rw [assoc, dualHom_coneMap_comp_relDuality_comp g h₁ H H' hφ hjg hH]

end Pairs

end LiftComplex

open LiftComplex

/-! ### The absolute lift -/

namespace KaroubiFiltration

variable {A : InvCat} (F : KaroubiFiltration A) (N : ℤ)

/-- The projection `A → A/U` as a duality-preserving functor. -/
abbrev projF : InvFunctor A.inv F.quot.inv := F.proj

/-- An honest strictly symmetric Kar complex `(C, p, φ)` of `A`, supported in `[0, N]`, which is
Poincaré modulo `U` (plan (L1-ii); input of the boundary construction (L1-iii)). -/
structure QuotPoincare where
  C : ChainComplex A ℤ
  p : C ⟶ C
  p_idem : p ≫ p = p
  support : SupportedIn p 0 N
  φ : dualComplex A.inv N C ⟶ C
  φ_kar : dualHom A.inv N p ≫ φ ≫ p = φ
  symm : IsStrictSymm A.inv N φ
  poincare : IsPoincare F.quot.inv N (F.projF.mapH p) (F.projF.mapDual φ)

variable {F N}

/-- The image in `A/U`, a Poincaré complex. -/
@[simps, implicit_reducible]
def QuotPoincare.toQuot (L : F.QuotPoincare N) : SymPoincare F.quot.inv N where
  C := F.projF.mapC L.C
  p := F.projF.mapH L.p
  p_idem := by rw [← Functor.map_comp, L.p_idem]
  support r hr := by
    show F.proj.F.map (L.p.f r) = 0
    rw [L.support r hr, Functor.map_zero]
  φ := F.projF.mapDual L.φ
  φ_kar := F.projF.mapDual_kar L.φ_kar
  symm := by rw [IsStrictSymm, InvFunctor.transposeHom_mapDual, L.symm]
  poincare := L.poincare

lemma iso_hom_inv_f {V : Type*} [Category V] [Preadditive V] {C D : ChainComplex V ℤ}
    (e : C ≅ D) (r : ℤ) : e.hom.f r ≫ e.inv.f r = 𝟙 _ := by
  rw [← comp_f, e.hom_inv_id, id_f]

lemma iso_inv_hom_f {V : Type*} [Category V] [Preadditive V] {C D : ChainComplex V ℤ}
    (e : C ≅ D) (r : ℤ) : e.inv.f r ≫ e.hom.f r = 𝟙 _ := by
  rw [← comp_f, e.inv_hom_id, id_f]

/-- **Honest strict lift of a free Poincaré complex** (plan (L1-ii)).  If `P.p = 1` on
`[0, N]`, then `P` is strictly isometric to the image of a `QuotPoincare` whose idempotent is the
degree truncation onto `[0, N]` (`1` there, `0` elsewhere).  Construction: `exists_strictLift`
applied to `(karTrunc P.p, φ)`, whose vanishing clauses make `degTrunc` a chain idempotent. -/
theorem exists_quotPoincare (P : SymPoincare F.quot.inv N)
    (hp : ∀ r, 0 ≤ r → r ≤ N → P.p.f r = 𝟙 _) :
    ∃ L : F.QuotPoincare N, (∀ r, 0 ≤ r → r ≤ N → L.p.f r = 𝟙 _) ∧
      Nonempty (SymPoincare.HomotopyIsometry L.toQuot P) := by
  have hp0 : ∀ r, ¬ (0 ≤ r ∧ r ≤ N) → P.p.f r = 0 := fun r h ↦ P.support r (by omega)
  obtain ⟨C'', φ'', e, hsym, hconj, hd, hφ0⟩ := F.exists_strictLift (karTrunc P.p P.p_idem)
    (dualHom F.quot.inv N (karTruncTo P.p P.p_idem) ≫ P.φ ≫ karTruncTo P.p P.p_idem)
    (P.symm.conj (karTruncTo P.p P.p_idem)) N
    (fun i k h ↦ by rw [karTrunc_d, hp0 i (by omega), zero_comp])
  have hd' : ∀ i k, ¬ (0 ≤ i ∧ i ≤ N ∧ 0 ≤ k ∧ k ≤ N) → C''.d i k = 0 := fun i k h ↦ hd i k (by
    rw [karTrunc_d]
    by_cases hi : 0 ≤ i ∧ i ≤ N
    · rw [P.p.comm, hp0 k (by omega), comp_zero]
    · rw [hp0 i hi, zero_comp])
  set τ := degTrunc C'' 0 N hd'
  have hkar : dualHom A.inv N τ ≫ φ'' ≫ τ = φ'' := by
    ext r
    simp only [comp_f, dualHom_f]
    by_cases h : 0 ≤ r ∧ r ≤ N
    · rw [degTrunc_f_of_mem hd' h, degTrunc_f_of_mem hd' (by omega)]
      erw [A.inv.star_id]
      rw [id_comp, comp_id]
    · rw [hφ0 r (by simp [hp0 r h]), zero_comp, comp_zero]
  have hτ : ∀ r, F.proj.F.map (τ.f r) = if 0 ≤ r ∧ r ≤ N then 𝟙 _ else 0 := fun r ↦ by
    by_cases h : 0 ≤ r ∧ r ≤ N
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
  have hconj' : dualHom F.quot.inv N (e.hom ≫ karTruncFrom P.p P.p_idem) ≫
      F.projF.mapDual φ'' ≫ e.hom ≫ karTruncFrom P.p P.p_idem = P.φ := by
    rw [dualHom_comp]
    simp only [assoc]
    rw [reassoc_of% hconj, karTruncTo_comp_from, ← assoc (dualHom _ N (karTruncFrom P.p P.p_idem)),
      ← dualHom_comp, karTruncTo_comp_from, P.φ_kar]
  let L : F.QuotPoincare N :=
    { C := C''
      p := τ
      p_idem := degTrunc_idem hd'
      support := supportedIn_degTrunc hd'
      φ := φ''
      φ_kar := hkar
      symm := hsym
      poincare := isPoincare_of_strict P (F.projF.mapDual_kar hkar) _ _ hfg hgf hpf hconj' }
  exact ⟨L, fun r h h' ↦ degTrunc_f_of_mem hd' ⟨h, h'⟩,
    ⟨strictIsometry (Q := L.toQuot) _ _ hfg hgf hpf hgp hconj'⟩⟩

end KaroubiFiltration

/-! ### Cascades with frozen data -/

namespace KaroubiFiltration

variable {A : InvCat} {F : KaroubiFiltration A} {N : ℤ}

/-- **Cascades with extra conditions.**  A cascade adapted to `L` can be chosen to satisfy, in
each degree, any further condition holding eventually, e.g. killing the finitely many
`I_U`-maps contributed by a frozen boundary. -/
theorem SymLift.exists_cascade_with (L : F.SymLift N) (Q : ∀ r, Splitting (L.X r) → Prop)
    (hQ : ∀ r, ∀ᶠ σ in F.cofinal (L.X r), Q r σ) : ∃ c : L.Cascade, ∀ r, Q r (c.σ r) := by
  obtain ⟨c, hc⟩ := F.exists_cascade L.d L.top
    (fun r τ ↦ (L.d (r + 1 + 1) (r + 1) ≫ L.d (r + 1) r ≫ τ.πU = 0 ∧
      (L.φ (r + 1) ≫ L.d (r + 1) r - L.dualD (r + 1) r ≫ L.φ r) ≫ τ.πU = 0) ∧ Q r τ)
    L.shape L.d_eq_zero fun r ↦
      (((eventually_comp_πU (L.d_comp_d _ _ _)).mono fun τ h ↦ by rwa [assoc] at h).and
        (eventually_comp_πU (L.comm _ _))).and (hQ r)
  refine ⟨⟨c, fun i j k ↦ ?_, fun r r' ↦ ?_⟩, fun r ↦ (hc r).2⟩
  · by_cases hjk : j = k + 1
    · by_cases hij : i = j + 1
      · subst hjk hij; exact (hc k).1.1
      · rw [L.shape i j (by simp; omega)]; simp
    · rw [L.shape j k (by simp; omega)]; simp
  · by_cases h : r = r' + 1
    · subst h; exact (hc r').1.2
    · rw [L.shape r r' (by simp; omega), SymLift.dualD, L.shape (N - r') (N - r) (by simp; omega)]
      simp

section Extend

variable (F) {X : ℤ → A} (d : ∀ i j, X i ⟶ X j) (r₀ : ℤ) (σ₀ : ∀ r, Splitting (X r))
  (P : ∀ r, Splitting (X r) → Prop)

/-- The downward extension of splittings `σ₀` frozen in degrees `≥ r₀`. -/
def cascadeFrom (r : ℤ) : Splitting (X r) :=
  if r₀ ≤ r then σ₀ r
  else F.chooseSplitting fun τ ↦ P r τ ∧ (cascadeFrom (r + 1)).ιE ≫ d (r + 1) r ≫ τ.πU = 0
termination_by (r₀ - r).toNat
decreasing_by omega

/-- **Extending a partial cascade** (frozen splittings): splittings `σ₀` given in degrees `≥ r₀`,
in the families, with `E`-parts closed under `d` and satisfying `P` there, extend downward to a
cascade agreeing with `σ₀` in degrees `≥ r₀`. -/
theorem exists_cascade_extend (hshape : ∀ i j, ¬ (ComplexShape.down ℤ).Rel i j → d i j = 0)
    (hmem : ∀ r, r₀ ≤ r → σ₀ r ∈ F.filt.splittings (X r))
    (hcl : ∀ r, r₀ ≤ r → (σ₀ (r + 1)).ιE ≫ d (r + 1) r ≫ (σ₀ r).πU = 0)
    (hP₀ : ∀ r, r₀ ≤ r → P r (σ₀ r)) (hP : ∀ r, r < r₀ → ∀ᶠ σ in F.cofinal (X r), P r σ) :
    ∃ c : F.Cascade d, (∀ r, P r (c.σ r)) ∧ ∀ r, r₀ ≤ r → c.σ r = σ₀ r := by
  have hfro : ∀ r, r₀ ≤ r → F.cascadeFrom d r₀ σ₀ P r = σ₀ r := fun r h ↦ by
    rw [cascadeFrom, if_pos h]
  have mem : ∀ r, F.cascadeFrom d r₀ σ₀ P r ∈ F.filt.splittings (X r) := fun r ↦ by
    by_cases h : r₀ ≤ r
    · rw [hfro r h]; exact hmem r h
    · rw [cascadeFrom, if_neg h]; exact F.chooseSplitting_mem _
  have key : ∀ r, P r (F.cascadeFrom d r₀ σ₀ P r) ∧ (F.cascadeFrom d r₀ σ₀ P (r + 1)).ιE ≫
      d (r + 1) r ≫ (F.cascadeFrom d r₀ σ₀ P r).πU = 0 := fun r ↦ by
    by_cases h : r₀ ≤ r
    · rw [hfro r h, hfro (r + 1) (by omega)]; exact ⟨hP₀ r h, hcl r h⟩
    · rw [cascadeFrom, if_neg h]
      exact F.chooseSplitting_spec ((hP r (by omega)).and ((eventually_comp_πU
        (factorsThrough_ιE_comp (mem (r + 1)) (d (r + 1) r))).mono fun τ h ↦ by rwa [assoc] at h))
  refine ⟨⟨F.cascadeFrom d r₀ σ₀ P, mem, fun i j ↦ ?_⟩, fun r ↦ (key r).1, hfro⟩
  by_cases hij : i = j + 1
  · subst hij; exact (key j).2
  · rw [hshape i j (by simp; omega)]; simp

end Extend

/-! ### The relative lift (boundary frozen) -/

variable (F N) in
/-- Input of the relative lift (plan (L2)).  The boundary `B` is honest and frozen, `ψ` is any
family `B_{N-r} ⟶ B_r` (a symmetric structure, or the non-closed top structure of a face of a
triad).  Modulo `I_U`: the interior `X` with `d̃` (`d̃² ≡ 0`, bounded above), a chain map
`j̃ : B ⟶ X`, and a relative structure `H̃` with `j̃^* ψ j̃ ≡ δ̃ H̃ + H̃ d̃` (`Homotopy _ 0`
convention: `H̃_{r,r+1}`, `δ̃_r = (-1)^r d̃^*`). -/
structure RelLift where
  X : ℤ → A
  d : ∀ i j, X i ⟶ X j
  shape : ∀ i j, ¬ (ComplexShape.down ℤ).Rel i j → d i j = 0
  d_comp_d : ∀ i j k, FactorsThrough F.U (d i j ≫ d j k)
  top : ℤ
  d_eq_zero : ∀ i j, top < i → d i j = 0
  B : ChainComplex A ℤ
  ψ : ∀ r, B.X (N - r) ⟶ B.X r
  j : ∀ r, B.X r ⟶ X r
  j_comm : ∀ i k, FactorsThrough F.U (j i ≫ d i k - B.d i k ≫ j k)
  H : ∀ r r', X (N - r) ⟶ X r'
  H_shape : ∀ r r', ¬ (ComplexShape.down ℤ).Rel r' r → H r r' = 0
  H_comm : ∀ r, FactorsThrough F.U (A.inv.star (j (N - r)) ≫ ψ r ≫ j r -
    ((r.negOnePow • A.inv.star (d (N - (r - 1)) (N - r))) ≫ H (r - 1) r +
      H r (r + 1) ≫ d (r + 1) r))

namespace RelLift

variable (R : F.RelLift N)

/-- The interior as a `SymLift` (with `φ̃ = 0`). -/
abbrev toSymLift : F.SymLift N where
  X := R.X
  d := R.d
  shape := R.shape
  d_comp_d := R.d_comp_d
  top := R.top
  d_eq_zero := R.d_eq_zero
  φ _ := 0
  comm _ _ := by simp only [zero_comp, comp_zero, sub_zero]; exact FactorsThrough.zero

/-- `δ̃_{r,r'} = (-1)^r d̃^*_{N-r',N-r}`. -/
abbrev dualD (r r' : ℤ) : R.X (N - r) ⟶ R.X (N - r') := R.toSymLift.dualD r r'

/-- A cascade adapted to `R`: adapted to the interior, and killing the defects of `j̃`, `H̃`. -/
structure Cascade extends toSymCascade : R.toSymLift.Cascade where
  jcomm : ∀ i k, (R.j i ≫ R.d i k - R.B.d i k ≫ R.j k) ≫ (σ k).πU = 0
  Hcomm : ∀ r, (A.inv.star (R.j (N - r)) ≫ R.ψ r ≫ R.j r -
    (R.dualD r (r - 1) ≫ R.H (r - 1) r + R.H r (r + 1) ≫ R.d (r + 1) r)) ≫ (σ r).πU = 0

/-- **Relative cascade**: only the interior splittings are chosen; the boundary is frozen. -/
theorem nonempty_cascade : Nonempty R.Cascade := by
  obtain ⟨c, hc⟩ := R.toSymLift.exists_cascade_with
    (fun r τ ↦ (R.j (r + 1) ≫ R.d (r + 1) r - R.B.d (r + 1) r ≫ R.j r) ≫ τ.πU = 0 ∧
      (A.inv.star (R.j (N - r)) ≫ R.ψ r ≫ R.j r -
        (R.dualD r (r - 1) ≫ R.H (r - 1) r + R.H r (r + 1) ≫ R.d (r + 1) r)) ≫ τ.πU = 0)
    fun r ↦ (eventually_comp_πU (R.j_comm _ _)).and (eventually_comp_πU (R.H_comm r))
  refine ⟨⟨c, fun i k ↦ ?_, fun r ↦ (hc r).2⟩⟩
  by_cases h : i = k + 1
  · subst h; exact (hc k).1
  · rw [R.shape i k (by simp; omega), R.B.shape i k (by simp; omega)]; simp

namespace Cascade

variable {R} (c : R.Cascade)

/-- The honest interior `C'' = (U_σ, ιU d̃ πU)`. -/
abbrev complex : ChainComplex A ℤ := c.toSymCascade.complex

/-- The honest boundary map `j'' = j̃ πU : B ⟶ C''`. -/
@[simps]
def jHom : R.B ⟶ c.complex where
  f r := R.j r ≫ (c.σ r).πU
  comm' i k _ := by
    have h := c.jcomm i k
    rw [sub_comp, sub_eq_zero, assoc, assoc] at h
    simp only [KaroubiFiltration.Cascade.uComplex_d, assoc]
    rw [c.toCascade.πU_ιU_d_πU, h]

/-- The honest relative structure `H'' = ιU H̃ πU`. -/
def relH (r r' : ℤ) : (dualComplex A.inv N c.complex).X r ⟶ c.complex.X r' :=
  (c.σ (N - r)).ιU ≫ R.H r r' ≫ (c.σ r').πU

/-- **The relative cycle condition on the nose**: `j''^* ψ j'' = δ H'' + H'' d`. -/
theorem relH_comm (r : ℤ) :
    A.inv.star (c.jHom.f (N - r)) ≫ R.ψ r ≫ c.jHom.f r =
      (dualComplex A.inv N c.complex).d r (r - 1) ≫ c.relH (r - 1) r +
        c.relH r (r + 1) ≫ c.complex.d (r + 1) r := by
  have h := c.Hcomm r
  rw [sub_comp, sub_eq_zero] at h
  simp only [jHom_f, relH, dualComplex_d, KaroubiFiltration.Cascade.uComplex_d, A.inv.star_comp,
    star_πU (c.mem _), F.star_ιU _ _ (c.mem _), assoc, Linear.units_smul_comp, add_comp,
    RelLift.dualD, SymLift.dualD] at h ⊢
  rw [c.toCascade.ιU_star_d_πU_ιU_assoc, c.toCascade.πU_ιU_d_πU, h]
  simp only [comp_add, Linear.comp_units_smul]

/-- For `ψ = φ_B` a chain map, `H''` is a relative boundary `j''^* φ_B j'' ≃ 0` (`SymPair.δφ`). -/
def relHomotopy (φB : dualComplex A.inv N R.B ⟶ R.B) (hψ : ∀ r, R.ψ r = φB.f r) :
    Homotopy (dualHom A.inv N c.jHom ≫ φB ≫ c.jHom) 0 where
  hom := c.relH
  zero r r' h := by simp only [relH, R.H_shape r r' h, zero_comp, comp_zero]
  comm r := by
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel r (r - 1) by simp),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (r + 1) r by simp)]
    simp only [comp_f, dualHom_f, ← hψ, HomologicalComplex.zero_f, add_zero]
    exact c.relH_comm r

@[simp] lemma relHomotopy_hom (φB : dualComplex A.inv N R.B ⟶ R.B) (hψ : ∀ r, R.ψ r = φB.f r) :
    (c.relHomotopy φB hψ).hom = c.relH := rfl

/-- `H''` is symmetric if `H̃` is (self-duality of the splittings). -/
theorem relH_symm (hH : R.H = transposeHomFamily A.inv N (C := zeroCx R.X) (D := zeroCx R.X) R.H) :
    transposeHomFamily A.inv N (C := c.complex) (D := c.complex) c.relH = c.relH := by
  funext r r'
  conv_rhs => rw [relH, hH]
  simp only [transposeHomFamily, relH, bidual_hom_f, A.inv.star_comp, star_πU (c.mem _),
    F.star_ιU _ _ (c.mem _), assoc, Linear.comp_units_smul, Linear.units_smul_comp]
  rw [Casc.comp_eqToHom_fam (Y := c.complex.X) (fun k ↦ (c.σ k).πU) (sub_sub_cancel N r')]

/-- `[j''] = [j̃]` under `quotIso`. -/
@[reassoc]
lemma quot_jHom (r : ℤ) :
    F.proj.F.map (c.jHom.f r) ≫ c.toSymCascade.quotIso.hom.f r = F.proj.F.map (R.j r) := by
  rw [SymLift.Cascade.quotIso_hom_f, jHom_f, Functor.map_comp, assoc, proj_map_πU_ιU (c.mem r),
    comp_id]

/-- `[H''] = [H̃]` under `quotIso`. -/
lemma quot_relH (r r' : ℤ) :
    (dualHom F.quot.inv N c.toSymCascade.quotIso.hom).f r ≫ F.proj.F.map (c.relH r r') ≫
      c.toSymCascade.quotIso.hom.f r' = F.proj.F.map (R.H r r') := by
  simp only [dualHom_f, SymLift.Cascade.quotIso_hom_f, relH, ← F.proj.map_star,
    F.star_ιU _ _ (c.mem _), Functor.map_comp, assoc]
  rw [proj_map_πU_ιU_assoc (c.mem _), proj_map_πU_ιU (c.mem _), comp_id]

end Cascade

end RelLift

end KaroubiFiltration

/-! ### Relative lifts from `A/U` -/

namespace KaroubiFiltration

variable {A : InvCat} (F : KaroubiFiltration A) {N : ℤ}

/-- The objects of a complex of `A/U`, as a complex of `A` with zero differential. -/
abbrev objCx (D : ChainComplex F.quot ℤ) : ChainComplex A ℤ := zeroCx fun k ↦ (D.X k).as

/-- Componentwise lifts of a family `h_{r,r'} : D_{N-r} ⟶ D_{r'}` of `A/U`. -/
def liftFam (D : ChainComplex F.quot ℤ) (h : ∀ r r', D.X (N - r) ⟶ D.X r') (r r' : ℤ) :
    (dualComplex A.inv N (objCx F D)).X r ⟶ (objCx F D).X r' :=
  F.liftQuotHom (h r r')

/-- The symmetrized lift `H̃ = (h̃ + T h̃)/2` of a family `h_{r,r'} : D_{N-r} ⟶ D_{r'}` of `A/U`. -/
def liftFamily (D : ChainComplex F.quot ℤ) (h : ∀ r r', D.X (N - r) ⟶ D.X r') :
    ∀ r r', (dualComplex A.inv N (objCx F D)).X r ⟶ (objCx F D).X r' :=
  (1 / 2 : ℚ) • (F.liftFam D h + transposeHomFamily A.inv N (F.liftFam D h))

variable {F} {D : ChainComplex F.quot ℤ} (h : ∀ r r', D.X (N - r) ⟶ D.X r')

lemma liftFamily_eq_zero {r r' : ℤ} (h₁ : h r r' = 0) (h₂ : h (N - r') (N - r) = 0) :
    F.liftFamily D h r r' = 0 := by
  simp [liftFamily, transposeHomFamily, liftFam, F.liftQuotHom_zero h₁, F.liftQuotHom_zero h₂]

lemma liftFamily_shape (hh : ∀ r r', ¬ (ComplexShape.down ℤ).Rel r' r → h r r' = 0) (r r' : ℤ)
    (hr : ¬ (ComplexShape.down ℤ).Rel r' r) : F.liftFamily D h r r' = 0 :=
  liftFamily_eq_zero h (hh r r' hr) (hh _ _ (by simp only [ComplexShape.down_Rel] at hr ⊢; omega))

/-- The lift is strictly symmetric. -/
lemma liftFamily_symm (hh : ∀ r r', ¬ (ComplexShape.down ℤ).Rel r' r → h r r' = 0) :
    transposeHomFamily A.inv N (F.liftFamily D h) = F.liftFamily D h := by
  rw [liftFamily, transposeHomFamily_smul, transposeHomFamily_add,
    transposeHomFamily_zeroCx (X := fun k ↦ (D.X k).as) (F.liftFam D h)
      fun r r' hr ↦ F.liftQuotHom_zero (hh r r' hr), add_comm]

/-- The lift of a symmetric family lifts it. -/
lemma map_liftFamily (hs : transposeHomFamily F.quot.inv N (C := D) (D := D) h = h) (r r' : ℤ) :
    F.proj.F.map (F.liftFamily D h r r') = h r r' := by
  have := F.proj_linear
  have e := congrFun (congrFun (F.projF.transposeHomFamily_map (N := N) (C := objCx F D)
    (F.liftFam D h)) r) r'
  have e' : (fun r r' ↦ F.proj.F.map (F.liftFam D h r r')) = h := by
    funext r r'; exact map_liftQuotHom _ _
  rw [e'] at e
  simp only [liftFamily, Pi.smul_apply, Pi.add_apply, Functor.map_smul, Functor.map_add, ← e]
  rw [show transposeHomFamily F.quot.inv N (C := F.projF.mapC (objCx F D))
    (D := F.projF.mapC (objCx F D)) h r r' = h r r' from congrFun (congrFun hs r) r',
    liftFam]
  erw [map_liftQuotHom]
  rw [← two_smul ℚ (h r r'), smul_smul]
  norm_num

variable (F N) in
/-- Relative lifting data from `A/U`: lifts of `d`, `j` and the symmetrized lift of `δφ`. -/
@[simps]
def RelLift.ofQuot (B : ChainComplex A ℤ) (φB : dualComplex A.inv N B ⟶ B)
    (D : ChainComplex F.quot ℤ) (top : ℤ) (hD : ∀ i k, top < i → D.d i k = 0)
    (j : F.projF.mapC B ⟶ D) (δφ : Homotopy (dualHom F.quot.inv N j ≫ F.projF.mapDual φB ≫ j) 0)
    (hδφ : IsSymmHomotopy F.quot.inv N δφ) : F.RelLift N where
  X r := (D.X r).as
  d i k := F.liftQuotHom (D.d i k)
  shape i k h := F.liftQuotHom_zero (D.shape i k h)
  d_comp_d i k l := by
    simpa using (F.proj_map_eq_iff (F.liftQuotHom (D.d i k) ≫ F.liftQuotHom (D.d k l)) 0).mp
      (by erw [Functor.map_comp, map_liftQuotHom, map_liftQuotHom, D.d_comp_d, Functor.map_zero] <;> rfl)
  top := top
  d_eq_zero i k h := F.liftQuotHom_zero (hD i k h)
  B := B
  ψ r := φB.f r
  j r := F.liftQuotHom (j.f r)
  j_comm i k := (F.proj_map_eq_iff _ _).mp (by
    simp only [Functor.map_comp, map_liftQuotHom]
    exact j.comm i k)
  H := F.liftFamily D δφ.hom
  H_shape := liftFamily_shape δφ.hom δφ.zero
  H_comm r := (F.proj_map_eq_iff _ _).mp (by
    have hs : transposeHomFamily F.quot.inv N δφ.hom = δφ.hom := by
      rw [← transposeHomotopy_hom]; exact hδφ
    have := δφ.comm r
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel r (r - 1) by simp),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (r + 1) r by simp)] at this
    simp only [Functor.map_comp, Functor.map_add, Casc.map_units_smul, F.proj.map_star,
      map_liftQuotHom, map_liftFamily δφ.hom hs]
    simpa using this)

/-- The represented interior of `ofQuot` is `D` (identity components). -/
def RelLift.ofQuotIso (B : ChainComplex A ℤ) (φB : dualComplex A.inv N B ⟶ B)
    (D : ChainComplex F.quot ℤ) (top : ℤ) (hD : ∀ i k, top < i → D.d i k = 0)
    (j : F.projF.mapC B ⟶ D) (δφ : Homotopy (dualHom F.quot.inv N j ≫ F.projF.mapDual φB ≫ j) 0)
    (hδφ : IsSymmHomotopy F.quot.inv N δφ) :
    (RelLift.ofQuot F N B φB D top hD j δφ hδφ).toSymLift.quotComplex ≅ D :=
  Hom.isoOfComponents (fun _ ↦ Iso.refl _) (fun i k _ ↦ by
    simp only [Iso.refl_hom, SymLift.quotComplex_d, RelLift.toSymLift, RelLift.ofQuot_d]
    erw [id_comp, comp_id, map_liftQuotHom])

/-- **Relative honest lift** (plan (L2), boundary frozen).  Given an honest boundary
`(B, φ_B)` of `A`, and over `A/U` a complex `D` bounded above, a chain map `j : B ⟶ D` and a
symmetric relative structure `δφ : j^* φ_B j ≃ 0`, there are an honest complex `D''` of `A`, an
honest chain map `j'' : B ⟶ D''` and an honest symmetric relative structure
`δφ'' : j''^* φ_B j'' ≃ 0`, with an isomorphism `e : D'' ≅ D` in `A/U` carrying `j''` to `j` and
`δφ''` to `δφ`.  `D''`, `j''`, `δφ''` vanish wherever `D`, `j`, `δφ` (and its transpose) do. -/
theorem exists_relLift (B : ChainComplex A ℤ) (φB : dualComplex A.inv N B ⟶ B)
    (D : ChainComplex F.quot ℤ) (top : ℤ) (hD : ∀ i k, top < i → D.d i k = 0)
    (j : F.projF.mapC B ⟶ D) (δφ : Homotopy (dualHom F.quot.inv N j ≫ F.projF.mapDual φB ≫ j) 0)
    (hδφ : IsSymmHomotopy F.quot.inv N δφ) :
    ∃ (D'' : ChainComplex A ℤ) (j'' : B ⟶ D'')
      (δφ'' : Homotopy (dualHom A.inv N j'' ≫ φB ≫ j'') 0) (e : F.projF.mapC D'' ≅ D),
      IsSymmHomotopy A.inv N δφ'' ∧ F.projF.mapH j'' ≫ e.hom = j ∧
      (∀ r r', (dualHom F.quot.inv N e.hom).f r ≫ F.proj.F.map (δφ''.hom r r') ≫ e.hom.f r' =
        δφ.hom r r') ∧
      (∀ i k, D.d i k = 0 → D''.d i k = 0) ∧ (∀ r, j.f r = 0 → j''.f r = 0) ∧
      ∀ r r', δφ.hom r r' = 0 → δφ.hom (N - r') (N - r) = 0 → δφ''.hom r r' = 0 := by
  have hs : transposeHomFamily F.quot.inv N δφ.hom = δφ.hom := by
    rw [← transposeHomotopy_hom]; exact hδφ
  obtain ⟨c⟩ := (RelLift.ofQuot F N B φB D top hD j δφ hδφ).nonempty_cascade
  refine ⟨c.complex, c.jHom, c.relHomotopy φB fun _ ↦ rfl,
    c.toSymCascade.quotIso ≪≫ RelLift.ofQuotIso B φB D top hD j δφ hδφ, ?_, ?_, ?_,
    fun i k h ↦ c.toSymCascade.complex_d_eq_zero (F.liftQuotHom_zero h), fun r h ↦ ?_,
    fun r r' h₁ h₂ ↦ ?_⟩
  · unfold IsSymmHomotopy
    erw [transposeHomotopy_hom, RelLift.Cascade.relHomotopy_hom]
    exact c.relH_symm (liftFamily_symm δφ.hom δφ.zero).symm
  · ext r
    simp only [Iso.trans_hom, comp_f, InvFunctor.mapH, Functor.mapHomologicalComplex_map_f]
    erw [c.quot_jHom_assoc r]
    simp only [RelLift.ofQuot_j, map_liftQuotHom, RelLift.ofQuotIso, Hom.isoOfComponents_hom_f,
      Iso.refl_hom]
    erw [comp_id]
    exact F.map_liftQuotHom _
  · intro r r'
    have := c.quot_relH r r'
    simp only [Iso.trans_hom, dualHom_comp, comp_f, assoc, RelLift.ofQuotIso,
      Hom.isoOfComponents_hom_f, Iso.refl_hom, dualHom_f] at this ⊢
    erw [F.quot.inv.star_id, id_comp, comp_id, this]
    exact map_liftFamily δφ.hom hs r r'
  · simp [F.liftQuotHom_zero h] <;> exact zero_comp
  · erw [RelLift.Cascade.relHomotopy_hom]
    simp [RelLift.Cascade.relH, liftFamily_eq_zero δφ.hom h₁ h₂] <;>
      erw [zero_comp, comp_zero]

end KaroubiFiltration

/-! ### Lifting pairs on a frozen boundary -/

namespace KaroubiFiltration

variable {A : InvCat} {F : KaroubiFiltration A} {N : ℤ} (L : F.QuotPoincare N)

/-- An honest strictly symmetric pair of `A` on the frozen boundary `L`, Poincaré modulo `U`:
the data of a `SymPair` over `A` whose relative duality holds in `A/U` (plan (L2)). -/
structure QuotPair where
  D : ChainComplex A ℤ
  pD : D ⟶ D
  pD_idem : pD ≫ pD = pD
  support : SupportedIn pD 0 (N + 1)
  j : L.C ⟶ D
  j_kar : L.p ≫ j ≫ pD = j
  δφ : Homotopy (dualHom A.inv N j ≫ L.φ ≫ j) 0
  δφ_kar : ∀ r r', (dualHom A.inv N pD).f r ≫ δφ.hom r r' ≫ pD.f r' = δφ.hom r r'
  symm : IsSymmHomotopy A.inv N δφ
  poincare : IsKarEquiv (dualHom F.quot.inv (N + 1) (coneMap (F.projF.mapH L.p) (F.projF.mapH pD)
    (comm_of_kar L.toQuot.p_idem (by rw [← Functor.map_comp, pD_idem])
      (by simp only [← Functor.map_comp, j_kar])))) (F.projF.mapH pD)
    (relDuality (F.projF.mapRel δφ))

/-- The image in `A/U`, a Poincaré pair with boundary `L.toQuot`. -/
@[simps]
def QuotPair.toQuot {L : F.QuotPoincare N} (X : F.QuotPair L) : SymPair F.quot.inv N where
  bd := L.toQuot
  D := F.projF.mapC X.D
  pD := F.projF.mapH X.pD
  pD_idem := by rw [← Functor.map_comp, X.pD_idem]
  support r hr := by
    show F.proj.F.map (X.pD.f r) = 0
    rw [X.support r hr, Functor.map_zero]
  j := F.projF.mapH X.j
  j_kar := by simp only [QuotPoincare.toQuot_p, ← Functor.map_comp, X.j_kar]
  δφ := F.projF.mapRel X.δφ
  δφ_kar r r' := by
    simp only [InvFunctor.mapRel_hom, dualHom_f, InvFunctor.mapH,
      Functor.mapHomologicalComplex_map_f, ← F.projF.map_star, ← Functor.map_comp]
    rw [← dualHom_f, X.δφ_kar]
  symm := by
    have e : (F.projF.mapRel X.δφ).hom = fun r r' ↦ F.proj.F.map (X.δφ.hom r r') :=
      funext₂ fun _ _ ↦ InvFunctor.mapRel_hom _ _ _ _
    have hs := X.symm
    rw [IsSymmHomotopy, transposeHomotopy_hom] at hs ⊢
    rw [e, F.projF.transposeHomFamily_map, hs]
  poincare := X.poincare

/-- **Relative honest lift of pairs** (plan (L2), boundary frozen).  Let `L` be a `QuotPoincare`
whose idempotent is `1` on `[0, N]`, and `Y` a Poincaré pair of `A/U` on `L.toQuot` whose interior
idempotent is `1` on `[0, N + 1]`.  Then `Y` is strictly isometric rel boundary to the image of a
honest pair `X` of `A` on `L` itself (same `L.C`, `L.φ`), Poincaré modulo `U`. -/
theorem exists_quotPair (hL : ∀ r, 0 ≤ r → r ≤ N → L.p.f r = 𝟙 _) (Y : SymPair F.quot.inv N)
    (hY : Y.bd = L.toQuot) (hpD : ∀ r, 0 ≤ r → r ≤ N + 1 → Y.pD.f r = 𝟙 _) :
    ∃ X : F.QuotPair L, (∀ r, 0 ≤ r → r ≤ N + 1 → X.pD.f r = 𝟙 _) ∧
      ∃ (f : X.toQuot.D ⟶ Y.D) (g : Y.D ⟶ X.toQuot.D), f ≫ g = X.toQuot.pD ∧ g ≫ f = Y.pD ∧
        X.toQuot.pD ≫ f ≫ Y.pD = f ∧
        X.toQuot.j ≫ f = eqToHom (congrArg SymPoincare.C hY.symm) ≫ Y.j ∧
        ∀ r r', (dualHom F.quot.inv N f).f r ≫ X.toQuot.δφ.hom r r' ≫ f.f r' = Y.δφ.hom r r' := by
  obtain ⟨bd, D, pD, pD_idem, support, j, j_kar, δφ, δφ_kar, symm, poincare⟩ := Y
  dsimp only at hY hpD ⊢
  subst hY
  have hp0 : ∀ r, ¬ (0 ≤ r ∧ r ≤ N + 1) → pD.f r = 0 := fun r h ↦ support r (by omega)
  have hjp : j ≫ pD = j := by
    conv_lhs => rw [← j_kar]
    rw [assoc, assoc, pD_idem, j_kar]
  -- the truncated interior `(D, p d)` and the lifted relative data on it
  let δφ' : Homotopy (dualHom F.quot.inv N (j ≫ karTruncTo pD pD_idem) ≫ F.projF.mapDual L.φ ≫
      (j ≫ karTruncTo pD pD_idem)) 0 :=
    homotopyCongr ((δφ.compRight (karTruncTo pD pD_idem)).compLeft
      (dualHom F.quot.inv N (karTruncTo pD pD_idem))) (by rw [dualHom_comp]; simp only [assoc]; rfl)
      (by simp)
  have hδ : ∀ r r', δφ'.hom r r' = δφ.hom r r' := fun r r' ↦ δφ_kar r r'
  have hδ' : ∀ a b, (¬ (0 ≤ N - a ∧ N - a ≤ N + 1) ∨ ¬ (0 ≤ b ∧ b ≤ N + 1)) →
      δφ'.hom a b = 0 := fun a b h ↦ by
    change (dualHom F.quot.inv N pD).f a ≫ δφ.hom a b ≫ pD.f b = 0
    rcases h with h | h
    · rw [dualHom_f, hp0 _ h, StrictInvolution.star_zero, zero_comp]
    · rw [hp0 _ h, comp_zero, comp_zero]
  have hsymm' : IsSymmHomotopy F.quot.inv N δφ' := by
    rw [IsSymmHomotopy, transposeHomotopy_hom] at symm ⊢
    rw [show δφ'.hom = δφ.hom from funext₂ hδ]
    exact symm
  obtain ⟨D'', j'', δφ'', e, hsym, hj, hconj, hdd, hj0, hH0⟩ := F.exists_relLift L.C L.φ
    (karTrunc pD pD_idem) (N + 1) (fun i k h ↦ by rw [karTrunc_d, hp0 i (by omega), zero_comp])
    (j ≫ karTruncTo pD pD_idem) δφ' hsymm'
  have hd'' : ∀ i k, ¬ (0 ≤ i ∧ i ≤ N + 1 ∧ 0 ≤ k ∧ k ≤ N + 1) → D''.d i k = 0 :=
    fun i k h ↦ hdd i k (by
      rw [karTrunc_d]
      by_cases hi : 0 ≤ i ∧ i ≤ N + 1
      · rw [pD.comm, hp0 k (by omega), comp_zero]
      · rw [hp0 i hi, zero_comp])
  set τ := degTrunc D'' 0 (N + 1) hd''
  have hjr : ∀ r, ¬ (0 ≤ r ∧ r ≤ N) → j''.f r = 0 := fun r h ↦ hj0 r (by
    have := congrArg (fun x ↦ x.f r) j_kar
    simp only [comp_f] at this
    rw [comp_f, ← this]
    change (F.proj.F.map (L.p.f r) ≫ _) ≫ _ = 0
    rw [L.support r (by omega), Functor.map_zero, zero_comp, zero_comp])
  have hHr : ∀ r r', (¬ (0 ≤ N - r ∧ N - r ≤ N + 1) ∨ ¬ (0 ≤ r' ∧ r' ≤ N + 1)) →
      δφ''.hom r r' = 0 := fun r r' h ↦ hH0 r r' (hδ' r r' h) (hδ' _ _ (by omega))
  have hτ : ∀ r, F.proj.F.map (τ.f r) = if 0 ≤ r ∧ r ≤ N + 1 then 𝟙 _ else 0 := fun r ↦ by
    by_cases h : 0 ≤ r ∧ r ≤ N + 1
    · rw [degTrunc_f_of_mem hd'' h, if_pos h, CategoryTheory.Functor.map_id]
    · rw [degTrunc_f_of_not_mem hd'' h, if_neg h, Functor.map_zero]
  have hjk : L.p ≫ j'' ≫ τ = j'' := by
    ext r
    simp only [comp_f]
    by_cases h : 0 ≤ r ∧ r ≤ N
    · rw [hL r h.1 h.2, degTrunc_f_of_mem hd'' ⟨h.1, by omega⟩, id_comp, comp_id]
    · rw [L.support r (by omega), zero_comp, hjr r h]
  have hfg : (e.hom ≫ karTruncFrom pD pD_idem) ≫ karTruncTo pD pD_idem ≫ e.inv =
      F.projF.mapH τ := by
    ext r
    simp only [comp_f, karTruncFrom_f, karTruncTo_f, InvFunctor.mapH,
      Functor.mapHomologicalComplex_map_f, hτ]
    split_ifs with h
    · rw [hpD r h.1 h.2]; erw [comp_id, id_comp]; exact iso_hom_inv_f e r
    · rw [hp0 r h]; simp
  have hgf : (karTruncTo pD pD_idem ≫ e.inv) ≫ e.hom ≫ karTruncFrom pD pD_idem = pD := by
    ext r; simp
  have hfk : F.projF.mapH τ ≫ (e.hom ≫ karTruncFrom pD pD_idem) ≫ pD =
      e.hom ≫ karTruncFrom pD pD_idem := by
    ext r
    simp only [comp_f, karTruncFrom_f, InvFunctor.mapH, Functor.mapHomologicalComplex_map_f, hτ,
      assoc, f_idem pD pD_idem]
    split_ifs with h
    · erw [id_comp]
    · rw [hp0 r h]; simp
  have hj' : F.projF.mapH j'' ≫ e.hom ≫ karTruncFrom pD pD_idem = j := by
    rw [← assoc, hj, assoc, karTruncTo_comp_from, hjp]
  have hconj' : ∀ r r', (dualHom F.quot.inv N (e.hom ≫ karTruncFrom pD pD_idem)).f r ≫
      F.proj.F.map (δφ''.hom r r') ≫ (e.hom ≫ karTruncFrom pD pD_idem).f r' = δφ.hom r r' := by
    intro r r'
    rw [dualHom_comp, comp_f, comp_f]
    simp only [assoc]
    rw [reassoc_of% hconj r r', hδ]
    exact δφ_kar r r'
  let X : F.QuotPair L :=
    { D := D''
      pD := τ
      pD_idem := degTrunc_idem hd''
      support := supportedIn_degTrunc hd''
      j := j''
      j_kar := hjk
      δφ := δφ''
      δφ_kar := fun r r' ↦ by
        by_cases h : (0 ≤ N - r ∧ N - r ≤ N + 1) ∧ (0 ≤ r' ∧ r' ≤ N + 1)
        · rw [dualHom_f, degTrunc_f_of_mem hd'' h.1, degTrunc_f_of_mem hd'' h.2]
          erw [A.inv.star_id]
          rw [id_comp, comp_id]
        · rw [hHr r r' (by tauto)]; simp
      symm := hsym
      poincare := isKarEquiv_relDuality_of_strict L.toQuot.p_idem pD_idem
        (by rw [← Functor.map_comp, degTrunc_idem hd'']) j_kar
        (by simp only [QuotPoincare.toQuot_p, ← Functor.map_comp, hjk]) δφ (F.projF.mapRel δφ'')
        L.toQuot.dualHom_p_comp_φ _ _ hfg hgf hfk hj' (fun r r' ↦ by
          have h₁ : (dualHom F.quot.inv N e.inv).f r ≫ (dualHom F.quot.inv N e.hom).f r = 𝟙 _ := by
            rw [← comp_f, ← dualHom_comp, e.hom_inv_id, dualHom_id, id_f]
          have hk : ∀ {Z} (x : D.X r' ⟶ Z), (dualHom F.quot.inv N (karTruncTo pD pD_idem)).f r ≫
              δφ.hom r r' ≫ (karTruncTo pD pD_idem).f r' ≫ x = δφ.hom r r' ≫ x :=
            fun x ↦ (reassoc_of% (δφ_kar r r')) x
          rw [InvFunctor.mapRel_hom, dualHom_comp, comp_f, comp_f]
          simp only [assoc]
          rw [hk, ← hδ, ← hconj r r']
          simp only [assoc]
          rw [reassoc_of% h₁, iso_hom_inv_f]
          erw [comp_id]) poincare }
  refine ⟨X, fun r h h' ↦ degTrunc_f_of_mem hd'' ⟨h, h'⟩, e.hom ≫ karTruncFrom pD pD_idem,
    karTruncTo pD pD_idem ≫ e.inv, hfg, hgf, hfk, ?_, fun r r' ↦ ?_⟩
  · rw [eqToHom_refl, id_comp]; exact hj'
  · rw [QuotPair.toQuot_δφ, InvFunctor.mapRel_hom]; exact hconj' r r'

end KaroubiFiltration

end

end HSFormal.LTheory
