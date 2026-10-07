import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import TauCeti.AlgebraicTopology.Singular.Excision
import TauCeti.AlgebraicTopology.Singular.Triple
import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance

/-!
# N1. Local relative homology `H_i(X | L)` (Newman blueprint, module N1)

Thin wrapper API around TauCeti's relative singular homology, hiding `TopPair`, triples and
excision data behind three notions:

* `relH R X L i = H_i(X, X ∖ L; R)`, an object of `ModuleCat R` (`X : TopCat.{0}`, `L : Set X`);
* `push R f h i : H_i(X | L) ⟶ H_i(Y | L')` for `f : X ⟶ Y` with `f⁻¹ L' ⊆ L`;
* `res R h i = push R (𝟙 X) _ i : H_i(X | L) ⟶ H_i(X | L')` for `L' ⊆ L`.

Main results:
* functoriality: `push_id`, `push_comp`, `push_comp'`, `push_push_apply`, `res_res_apply`,
  `push_res_apply` (naturality of restriction), `push_congr`;
* `isZero_relH_empty : IsZero (relH R X ∅ i)` and `push_eq_zero_of_forall_notMem`;
* **excision** `isIso_push_of_isEmbedding` (for any embedding `f`, `L = f⁻¹ L'` and
  `closure L' ⊆ interior (range f)`), `isIso_push_of_isOpenEmbedding`, and `isIso_pushIncl`
  for the inclusion `pushIncl R O L i : H_i(O | O ∩ L) ⟶ H_i(X | L)` of an open `O ⊇ L`;
* homeomorphism invariance `relHIsoOfHomeomorph`, `isIso_push_of_homeomorph`;
* homotopy invariance `push_eq_of_homotopy`;
* the long exact sequence of the triple `(X, X ∖ L', X ∖ L)`, `L' ⊆ L`, in elementwise form:
  `exists_push_incl_eq_of_res_eq_zero` (exactness at `H_i(X | L)`) and `push_incl_injective`
  (injectivity of `H_i(X ∖ L' | L) ⟶ H_i(X | L)` when `H_{i+1}(X | L') = 0`).

## Deviations from the blueprint

* Coefficients are an arbitrary commutative ring `R : Type` (`coef R = ModuleCat.of R R`) instead
  of `ZMod p`; the application takes `R = ZMod p`. Nothing here needs a field.
* Excision is stated for an arbitrary embedding (`isIso_push_of_isEmbedding`), via TauCeti's
  `TopPair.isIso_singularHomologyMap_of_open_cover`; this removes all "subtype of subtype"
  plumbing: GL (N2) excises along `X ∖ L₁ ⟶ X ∖ (L₁ ∩ L₂)` directly.
* The triple wrappers use the triple `TopTriple.of (X ∖ L ⟶ X ∖ L') (X ∖ L' ⟶ X)`; its outer
  and total pairs are *definitionally* the pairs of `relH R X L'` and `relH R X L` (so `res` is
  definitionally the triple map `totalToOuter`), and only the inner pair needs the explicit pair
  isomorphism `complInnerHom`.
* Practical note: proofs mixing `ConcreteCategory.hom` and membership in preimages are fragile
  under `rw` (motives fail to typecheck at `implicit` transparency); use the `*_apply` lemmas in
  term mode (`.trans`) with explicit arguments, as in `HSFormal.Newman.eq_zero_of_res_eq_zero`.
-/

open CategoryTheory Limits Topology

namespace HSFormal.Newman

variable (R : Type) [CommRing R]

/-- The coefficient object `R` of `ModuleCat R`. -/
abbrev coef : ModuleCat.{0} R := ModuleCat.of R R

/-- `relH R X L i = H_i(X, X ∖ L; R)`. -/
noncomputable abbrev relH (X : TopCat.{0}) (L : Set X) (i : ℕ) : ModuleCat.{0} R :=
  (TopPair.ofSubset (X := X) Lᶜ).singularHomology (coef R) i

lemma mapsTo_compl_of {X Y : TopCat.{0}} (f : X ⟶ Y) {L : Set X} {L' : Set Y}
    (h : ∀ x, f x ∈ L' → x ∈ L) : Set.MapsTo f Lᶜ L'ᶜ :=
  fun x hx hfx => hx (h x hfx)

/-- The map `H_i(X | L) ⟶ H_i(Y | L')` induced by `f` when `f⁻¹ L' ⊆ L`. -/
noncomputable def push {X Y : TopCat.{0}} (f : X ⟶ Y) {L : Set X} {L' : Set Y}
    (h : ∀ x, f x ∈ L' → x ∈ L) (i : ℕ) : relH R X L i ⟶ relH R Y L' i :=
  TopPair.singularHomologyMap (TopPair.ofSubsetMap f (mapsTo_compl_of f h)) (coef R) i

/-- Restriction `H_i(X | L) ⟶ H_i(X | L')` for `L' ⊆ L`. -/
noncomputable abbrev res {X : TopCat.{0}} {L L' : Set X} (h : L' ⊆ L) (i : ℕ) :
    relH R X L i ⟶ relH R X L' i :=
  push R (𝟙 X) (fun _ hx => h hx) i

section Functoriality

variable {R} {X Y Z : TopCat.{0}}

/-- `push` only depends on the underlying function of `f`. -/
lemma push_congr {f g : X ⟶ Y} (hfg : f = g) {L : Set X} {L' : Set Y}
    (hf : ∀ x, f x ∈ L' → x ∈ L) (hg : ∀ x, g x ∈ L' → x ∈ L) (i : ℕ) :
    push R f hf i = push R g hg i := by
  subst hfg; rfl

@[simp]
lemma push_id {L : Set X} (h : ∀ x, (𝟙 X : X ⟶ X) x ∈ L → x ∈ L) (i : ℕ) :
    push R (𝟙 X) h i = 𝟙 _ := by
  unfold push
  rw [TopPair.ofSubsetMap_id]
  exact TopPair.singularHomologyMap_id _ _ _

lemma push_comp (f : X ⟶ Y) (g : Y ⟶ Z) {L : Set X} {L' : Set Y} {L'' : Set Z}
    (hf : ∀ x, f x ∈ L' → x ∈ L) (hg : ∀ y, g y ∈ L'' → y ∈ L')
    (hfg : ∀ x, (f ≫ g) x ∈ L'' → x ∈ L) (i : ℕ) :
    push R f hf i ≫ push R g hg i = push R (f ≫ g) hfg i := by
  unfold push
  rw [TopPair.ofSubsetMap_comp f g (mapsTo_compl_of f hf) (mapsTo_compl_of g hg)]
  exact (TopPair.singularHomologyMap_comp _ _ _ _).symm

/-- Composition of `push`es, for any factorisation `k = f ≫ g`. -/
lemma push_comp' (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (hk : f ≫ g = k) {L : Set X} {L' : Set Y}
    {L'' : Set Z} (hf : ∀ x, f x ∈ L' → x ∈ L) (hg : ∀ y, g y ∈ L'' → y ∈ L')
    (hk' : ∀ x, k x ∈ L'' → x ∈ L) (i : ℕ) :
    push R f hf i ≫ push R g hg i = push R k hk' i := by
  subst hk; exact push_comp f g hf hg hk' i

lemma push_push_apply (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (hk : f ≫ g = k) {L : Set X}
    {L' : Set Y} {L'' : Set Z} (hf : ∀ x, f x ∈ L' → x ∈ L) (hg : ∀ y, g y ∈ L'' → y ∈ L')
    (hk' : ∀ x, k x ∈ L'' → x ∈ L) (i : ℕ) (a : relH R X L i) :
    push R g hg i (push R f hf i a) = push R k hk' i a := by
  rw [← push_comp' f g k hk hf hg hk' i]; rfl

@[simp]
lemma res_self {L : Set X} (i : ℕ) : res R (subset_refl L) i = 𝟙 _ := push_id _ i

lemma res_res {L L' L'' : Set X} (h : L' ⊆ L) (h' : L'' ⊆ L') (i : ℕ) :
    res R h i ≫ res R h' i = res R (h'.trans h) i :=
  push_comp' _ _ _ (Category.id_comp _) _ _ _ i

lemma res_res_apply {L L' L'' : Set X} (h : L' ⊆ L) (h' : L'' ⊆ L') (i : ℕ) (a : relH R X L i) :
    res R h' i (res R h i a) = res R (h'.trans h) i a := by
  rw [← res_res h h' i]; rfl

/-- Naturality of restriction: `res ∘ push = push ∘ res`. -/
lemma push_res_apply (f : X ⟶ Y) {L₁ L₂ : Set X} {L₁' L₂' : Set Y} (h : L₂ ⊆ L₁)
    (h' : L₂' ⊆ L₁') (hf₁ : ∀ x, f x ∈ L₁' → x ∈ L₁) (hf₂ : ∀ x, f x ∈ L₂' → x ∈ L₂) (i : ℕ)
    (a : relH R X L₁ i) :
    res R h' i (push R f hf₁ i a) = push R f hf₂ i (res R h i a) := by
  rw [push_push_apply f (𝟙 Y) f (Category.comp_id f) hf₁ _ (fun x hx => h (hf₂ x hx)),
    push_push_apply (𝟙 X) f f (Category.id_comp f) _ hf₂ (fun x hx => h (hf₂ x hx))]

end Functoriality

section Zero

variable {R} {X Y : TopCat.{0}}

/-- `H_i(X | ∅) = H_i(X, X) = 0`. -/
lemma isZero_relH_empty (X : TopCat.{0}) (i : ℕ) : IsZero (relH R X ∅ i) := by
  let P := TopPair.ofSubset (X := X) (∅ : Set X)ᶜ
  have hP : IsIso P.map := TopCat.isIso_of_bijective_of_isOpenMap _
    ⟨Subtype.val_injective, fun x => ⟨⟨x, Set.notMem_empty x⟩, rfl⟩⟩
    (show IsOpenMap (Subtype.val : ((∅ : Set X)ᶜ : Set X) → X) from
      isClosed_empty.isOpen_compl.isOpenMap_subtype_val)
  have h1 : IsIso (TopCat.toSSet.map P.map) := Functor.map_isIso _ _
  have h1' : IsIso (TopPair.toSSetPair.obj P).hom := h1
  have h2 : IsIso (SSet.chainComplexMap (TopPair.toSSetPair.obj P).hom (coef R)) :=
    Functor.map_isIso _ _
  have hK := CokernelCofork.IsColimit.isZero_of_epi
    (P.isColimitCokernelCoforkSingularChainComplex (coef R))
  exact (HomologicalComplex.homologyFunctor _ _ i).map_isZero hK

/-- A map of pairs `(X, X ∖ L) ⟶ (Y, Y ∖ L')` whose image misses `L'` induces `0`: it factors
through `H_i(X | ∅) = 0`. -/
lemma push_eq_zero_of_forall_notMem {f : X ⟶ Y} {L : Set X} {L' : Set Y}
    (h : ∀ x, f x ∈ L' → x ∈ L) (hf : ∀ x, f x ∉ L') (i : ℕ) : push R f h i = 0 := by
  rw [← push_comp' (𝟙 X) f f (Category.id_comp f) (L' := (∅ : Set X)) (fun _ hx => hx.elim)
    (fun x hx => (hf x hx).elim) h i]
  rw [(isZero_relH_empty (R := R) X i).eq_of_tgt
    (push R (𝟙 X) (L := L) (L' := ∅) (fun _ hx => hx.elim) i) 0, zero_comp]

end Zero

section Excision

variable {R} {X Y : TopCat.{0}}

/-- **Excision** for `push`. Let `f : X ⟶ Y` be an embedding, `L = f⁻¹ L'`, and suppose the
closure of `L'` lies in the interior of the range of `f`. Then `push f` is an isomorphism
`H_i(X | L) ≅ H_i(Y | L')`. -/
theorem isIso_push_of_isEmbedding {f : X ⟶ Y} (hf : IsEmbedding f) {L : Set X} {L' : Set Y}
    (h : ∀ x, f x ∈ L' → x ∈ L) (h' : ∀ x ∈ L, f x ∈ L')
    (hcl : closure L' ⊆ interior (Set.range f)) (i : ℕ) : IsIso (push R f h i) := by
  refine TopPair.isIso_singularHomologyMap_of_open_cover (coef R)
    (TopPair.ofSubsetMap f (mapsTo_compl_of f h)) hf ?_
    (fun b : Bool => bif b then interior (Set.range f) else (closure L')ᶜ)
    (fun b => by cases b <;> [exact isClosed_closure.isOpen_compl; exact isOpen_interior]) ?_ ?_ i
  · rintro x ⟨⟨y, hy⟩, hxy⟩
    refine ⟨⟨x, fun hx => hy ?_⟩, rfl⟩
    have : y = f x := hxy
    exact this ▸ h' x hx
  · ext y
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    by_cases hy : y ∈ closure L'
    · exact ⟨true, hcl hy⟩
    · exact ⟨false, hy⟩
  · intro b
    cases b
    · left
      rintro y hy
      exact ⟨⟨y, fun hy' => hy (subset_closure hy')⟩, rfl⟩
    · right
      exact interior_subset

/-- **Excision** for an open embedding and a closed `L'` inside its range. -/
theorem isIso_push_of_isOpenEmbedding {f : X ⟶ Y} (hf : IsOpenEmbedding f) {L : Set X}
    {L' : Set Y} (h : ∀ x, f x ∈ L' → x ∈ L) (h' : ∀ x ∈ L, f x ∈ L') (hL' : IsClosed L')
    (hsub : L' ⊆ Set.range f) (i : ℕ) : IsIso (push R f h i) :=
  isIso_push_of_isEmbedding hf.isEmbedding h h'
    (by rw [hL'.closure_eq, hf.isOpen_range.interior_eq]; exact hsub) i

/-- The inclusion of an open subspace, as a morphism of `TopCat`. -/
abbrev incl {X : TopCat.{0}} (O : Set X) : TopCat.of O ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

lemma isOpenEmbedding_incl {O : Set X} (hO : IsOpen O) : IsOpenEmbedding (incl O) :=
  hO.isOpenEmbedding_subtypeVal

variable (R) in
/-- The map `H_i(O | O ∩ L) ⟶ H_i(X | L)` induced by the inclusion of a subspace `O`. -/
noncomputable abbrev pushIncl (O L : Set X) (i : ℕ) :
    relH R (TopCat.of O) (Subtype.val ⁻¹' L) i ⟶ relH R X L i :=
  push R (incl O) (L := Subtype.val ⁻¹' L) (L' := L)
    (fun _ hx => (hx : _ ∈ Subtype.val ⁻¹' L)) i

/-- **Excision** for an open subset `O ⊇ L` with `L` closed: `H_i(O | L) ≅ H_i(X | L)`. -/
theorem isIso_pushIncl {O : Set X} (hO : IsOpen O) {L : Set X} (hL : IsClosed L)
    (hLO : L ⊆ O) (i : ℕ) : IsIso (pushIncl R O L i) :=
  isIso_push_of_isOpenEmbedding (isOpenEmbedding_incl hO) _ (fun _ h => h) hL
    (fun x hx => ⟨⟨x, hLO hx⟩, rfl⟩) i

end Excision

section Homeomorph

variable {R} {X Y : TopCat.{0}}

/-- A homeomorphism `e` with `e⁻¹ L' = L` induces `H_i(X | L) ≅ H_i(Y | L')`. -/
noncomputable def relHIsoOfHomeomorph (e : X ≃ₜ Y) {L : Set X} {L' : Set Y}
    (hL : ∀ x, e x ∈ L' ↔ x ∈ L) (i : ℕ) : relH R X L i ≅ relH R Y L' i where
  hom := push R (TopCat.ofHom ⟨e, e.continuous⟩) (fun x hx => (hL x).1 hx) i
  inv := push R (TopCat.ofHom ⟨e.symm, e.symm.continuous⟩)
    (fun y hy => by simpa using (hL (e.symm y)).2 hy) i
  hom_inv_id := by
    rw [push_comp' _ _ (𝟙 X) (by ext x; simp) _ _ (fun _ hx => hx)]; exact push_id _ i
  inv_hom_id := by
    rw [push_comp' _ _ (𝟙 Y) (by ext x; simp) _ _ (fun _ hx => hx)]; exact push_id _ i

lemma relHIsoOfHomeomorph_hom (e : X ≃ₜ Y) {L : Set X} {L' : Set Y}
    (hL : ∀ x, e x ∈ L' ↔ x ∈ L) (i : ℕ) :
    (relHIsoOfHomeomorph (R := R) e hL i).hom =
      push R (TopCat.ofHom ⟨e, e.continuous⟩) (fun x hx => (hL x).1 hx) i := rfl

/-- `push` along a homeomorphism with `e⁻¹ L' = L` is an isomorphism. -/
lemma isIso_push_of_homeomorph {f : X ⟶ Y} (e : X ≃ₜ Y) (hfe : ∀ x, f x = e x) {L : Set X}
    {L' : Set Y} (h : ∀ x, f x ∈ L' → x ∈ L) (h' : ∀ x ∈ L, f x ∈ L') (i : ℕ) :
    IsIso (push R f h i) := by
  have hf : f = TopCat.ofHom ⟨e, e.continuous⟩ := by ext x; exact hfe x
  have hL : ∀ x, e x ∈ L' ↔ x ∈ L := fun x => by
    rw [← hfe]; exact ⟨h x, h' x⟩
  rw [push_congr hf h (fun x hx => (hL x).1 hx)]
  exact (relHIsoOfHomeomorph e hL i).isIso_hom

end Homeomorph

section Homotopy

variable {R} {X Y : TopCat.{0}}

/-- **Homotopy invariance** for `push`: maps joined by a homotopy `F` with `F_t⁻¹ L' ⊆ L` for
all `t` induce the same map `H_i(X | L) ⟶ H_i(Y | L')`. -/
theorem push_eq_of_homotopy {f g : X ⟶ Y} (F : f.hom.Homotopy g.hom) {L : Set X} {L' : Set Y}
    (hF : ∀ t x, F (t, x) ∈ L' → x ∈ L) (hf : ∀ x, f x ∈ L' → x ∈ L)
    (hg : ∀ x, g x ∈ L' → x ∈ L) (i : ℕ) : push R f hf i = push R g hg i :=
  TopPair.Homotopy.congr_singularHomologyMap
    (TopPair.ofSubsetHomotopy (B := Lᶜ) (B' := L'ᶜ) F fun t x hx hFx => hx (hF t x hFx))
    (coef R) i

end Homotopy

section Triple

/-! ### The long exact sequence of the triple `(X, X ∖ L', X ∖ L)`, for `L' ⊆ L`

Its outer and total pairs are, definitionally, the pairs of `relH R X L'` and `relH R X L`; its
inner pair `(X ∖ L', X ∖ L)` is identified with the pair of `relH R (X ∖ L') (X ∖ L' ∩ L)` by the
pair isomorphism `complInnerHom`. -/

variable {R : Type} [CommRing R] {X : TopCat.{0}}

noncomputable abbrev complTriple {L L' : Set X} (h : L' ⊆ L) : TauCeti.TopTriple.{0} :=
  TauCeti.TopTriple.of (B := TopCat.of ↥Lᶜ) (A := TopCat.of ↥L'ᶜ) (X := X)
    (TopCat.ofHom (ContinuousMap.inclusion (Set.compl_subset_compl.2 h))) (incl L'ᶜ)
    (IsEmbedding.inclusion (Set.compl_subset_compl.2 h)) IsEmbedding.subtypeVal

/-- The pair map `(X ∖ L', (X ∖ L') ∖ L) ⟶ (X ∖ L', X ∖ L)` -/
noncomputable def complInnerHom {L L' : Set X} (h : L' ⊆ L) :
    TopPair.ofSubset (X := TopCat.of ↥L'ᶜ) (Subtype.val ⁻¹' L)ᶜ ⟶
      TauCeti.TopTriple.innerPair.obj (complTriple h) :=
  TopPair.ofHom (𝟙 _) (TopCat.ofHom ⟨fun y => ⟨y.1.1, y.2⟩, by fun_prop⟩) (by ext; rfl)

instance isIso_complInnerHom {L L' : Set X} (h : L' ⊆ L) : IsIso (complInnerHom h) := by
  have : IsIso (TopPair.Hom.fst (complInnerHom h)) := inferInstanceAs (IsIso (𝟙 _))
  refine TopPair.isIso_of_isIso_fst_of_surjective_snd _ ?_
  rintro ⟨y, hy⟩
  exact ⟨⟨⟨y, fun hy' => hy (h hy')⟩, hy⟩, rfl⟩

lemma complInnerHom_comp_innerToTotal {L L' : Set X} (h : L' ⊆ L) :
    complInnerHom h ≫ TauCeti.TopTriple.innerToTotal.app (complTriple h) =
      TopPair.ofSubsetMap (incl L'ᶜ) (mapsTo_compl_of (incl L'ᶜ) (L := Subtype.val ⁻¹' L)
        (L' := L) fun _ hx => (hx : _ ∈ Subtype.val ⁻¹' L)) := by
  ext : 2 <;> rfl

lemma pushIncl_eq {L L' : Set X} (h : L' ⊆ L) (i : ℕ) :
    pushIncl R L'ᶜ L i =
      TopPair.singularHomologyMap (complInnerHom h) (coef R) i ≫
        TopPair.singularHomologyMap (TauCeti.TopTriple.innerToTotal.app (complTriple h)) (coef R) i := by
  rw [← TopPair.singularHomologyMap_comp, complInnerHom_comp_innerToTotal]; rfl

theorem exists_push_incl_eq_of_res_eq_zero {L L' : Set X} (h : L' ⊆ L) {i : ℕ}
    (α : relH R X L i) (hα : res R h i α = 0) :
    ∃ β : relH R (TopCat.of ↥L'ᶜ) (Subtype.val ⁻¹' L) i,
      pushIncl R L'ᶜ L i β = α := by
  have hex := TauCeti.TopTriple.singularHomology_exact_total (complTriple h) (coef R) i
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1 hex α hα
  set f := TopPair.singularHomologyMap (complInnerHom h) (coef R) i
  set g := TopPair.singularHomologyMap (TauCeti.TopTriple.innerToTotal.app (complTriple h))
    (coef R) i
  have hinv : f (inv f y) = y := by
    rw [← ConcreteCategory.comp_apply, IsIso.inv_hom_id, ConcreteCategory.id_apply]
  refine ⟨inv f y, (ConcreteCategory.congr_hom (pushIncl_eq h i) _).trans ?_⟩
  change g (f (inv f y)) = α
  rw [hinv]
  exact hy

theorem push_incl_injective {L L' : Set X} (h : L' ⊆ L) {i : ℕ}
    (hZ : IsZero (relH R X L' (i + 1))) :
    Function.Injective (pushIncl R L'ᶜ L i) := by
  have hex := TauCeti.TopTriple.singularHomology_exact_inner (complTriple h) (coef R) (i + 1) i
  have hm : Mono (TopPair.singularHomologyMap
      (TauCeti.TopTriple.innerToTotal.app (complTriple h)) (coef R) i) :=
    hex.mono_g (hZ.eq_of_src _ _)
  have hg := (ModuleCat.mono_iff_injective _).1 hm
  have hf := (ModuleCat.mono_iff_injective
    (TopPair.singularHomologyMap (complInnerHom h) (coef R) i)).1 inferInstance
  intro a b hab
  have e := fun z => ConcreteCategory.congr_hom (pushIncl_eq (R := R) h i) z
  rw [e a, e b] at hab
  exact hf (hg hab)

end Triple

end HSFormal.Newman
