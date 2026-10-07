import HSFormal.LTheory.ConeEquiv
import HSFormal.LTheory.Union

/-!
# The boundary of a Poincaré pair is Poincaré (R1)

[Ran80I, Prop. 3.4] for pairs `(j : C ⟶ D, (δφ, φ))` with `j` degreewise split (the case of
the cubical route: inclusions of based subcomplexes), proved by R2 on the strict ladder

  `0 ⟶ R^{N-*} ⟶ D^{N-*} ⟶ C^{N-*} ⟶ 0`  (dual of `0 ⟶ C ⟶ D ⟶ R ⟶ 0`)
  `0 ⟶ Σ⁻¹D ⟶ Σ⁻¹Cone(j) ⟶ C ⟶ 0`

with vertical maps `Σ⁻¹(Ψ q^*)`, `Σ⁻¹(TΨ)` and `-φ` (desuspension avoids index casts on `C`;
the squares commute strictly by `Tφ = φ` and `T δφ = δφ`).

* `boundaryHomotopyEquiv`, `isPoincare_of_degreewiseSplit`: R1.
* `SymPair.ofSplit`: based pairs (identity idempotents) whose relative duality map is an
  equivalence are `SymPair`s, the boundary being Poincaré by R1 (l. 1084).
* `isKarEquiv_relDuality_of_split`: `Ψ` is an equivalence iff the relative cap `Ψ q^*` is.
* `isKarEquiv_left`/`isKarEquiv_right`: R2 in `IsKarEquiv` form.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression
  homotopyCofiber

noncomputable section

universe v u

variable {V : Type u} [Category.{v} V] [Preadditive V]

section Desusp

variable {K L : ChainComplex V ℤ}

/-- The desuspension `Σ⁻¹K`: `(Σ⁻¹K)_n = K_{n+1}`, `d = -d`. -/
@[simps, reducible]
def desusp (K : ChainComplex V ℤ) : ChainComplex V ℤ where
  X n := K.X (n + 1)
  d n n' := -K.d (n + 1) (n' + 1)
  shape n n' h := by
    rw [K.shape, neg_zero]
    simp only [ComplexShape.down_Rel] at h ⊢
    omega
  d_comp_d' n n' n'' _ _ := by simp

/-- The desuspension of a chain map. -/
@[simps]
def desuspMap (f : K ⟶ L) : desusp K ⟶ desusp L where
  f n := f.f (n + 1)

@[simp]
lemma desuspMap_comp {M : ChainComplex V ℤ} (f : K ⟶ L) (g : L ⟶ M) :
    desuspMap (f ≫ g) = desuspMap f ≫ desuspMap g := rfl

@[simp]
lemma desuspMap_id (K : ChainComplex V ℤ) : desuspMap (𝟙 K) = 𝟙 _ := rfl

/-- The desuspension of a homotopy. -/
def desuspHomotopy {f g : K ⟶ L} (H : Homotopy f g) : Homotopy (desuspMap f) (desuspMap g) where
  hom n m := -H.hom (n + 1) (m + 1)
  zero n m h := by
    rw [H.zero, neg_zero]
    simp only [ComplexShape.down_Rel] at h ⊢
    omega
  comm n := by
    rw [dNext_eq _ (down_rel_pred n), prevD_eq _ (down_rel_succ n)]
    have h := homotopy_comm H (n + 1) (n - 1 + 1) (n + 1 + 1) (by simp) (by simp)
    simp only [desusp_d, desuspMap_f, neg_comp, comp_neg, neg_neg, h]

/-- The desuspension of a homotopy equivalence. -/
@[simps]
def desuspHomotopyEquiv (e : HomotopyEquiv K L) : HomotopyEquiv (desusp K) (desusp L) where
  hom := desuspMap e.hom
  inv := desuspMap e.inv
  homotopyHomInvId := homotopyCongr (desuspHomotopy e.homotopyHomInvId) rfl rfl
  homotopyInvHomId := homotopyCongr (desuspHomotopy e.homotopyInvHomId) rfl rfl

/-- The sign change `f ↦ -f` of a homotopy equivalence. -/
@[simps]
def HomotopyEquiv.negHom {X Y : ChainComplex V ℤ} (e : HomotopyEquiv X Y) : HomotopyEquiv X Y where
  hom := -e.hom
  inv := -e.inv
  homotopyHomInvId := homotopyCongr e.homotopyHomInvId (by simp) rfl
  homotopyInvHomId := homotopyCongr e.homotopyInvHomId (by simp) rfl

/-- A homotopy equivalence whose underlying map is replaced by a homotopic one. -/
@[simps]
def HomotopyEquiv.ofHomotopy {X Y : ChainComplex V ℤ} (e : HomotopyEquiv X Y) {f : X ⟶ Y}
    (H : Homotopy e.hom f) : HomotopyEquiv X Y where
  hom := f
  inv := e.inv
  homotopyHomInvId := (H.symm.compRight e.inv).trans e.homotopyHomInvId
  homotopyInvHomId := (H.symm.compLeft e.inv).trans e.homotopyInvHomId

variable (J : StrictInvolution V) (N : ℤ)

/-- `K^{N-*} ≅ Σ⁻¹ K^{N+1-*}`. -/
def dualDesuspIso (K : ChainComplex V ℤ) : dualComplex J N K ≅ desusp (dualComplex J (N + 1) K) :=
  Hom.isoOfComponents (fun n ↦ K.XIsoOfEq (by omega : N - n = N + 1 - (n + 1))) (fun n n' h ↦ by
    simp only [ComplexShape.down_Rel] at h
    simp only [dualComplex_d, desusp_d, Linear.units_smul_comp, Linear.comp_units_smul,
      Int.negOnePow_succ, Units.neg_smul, neg_neg]
    congr 1
    exact XIsoOfEq_star_d K (by omega) (by omega))

@[simp]
lemma dualDesuspIso_hom_f (K : ChainComplex V ℤ) (n : ℤ) :
    (dualDesuspIso J N K).hom.f n = (K.XIsoOfEq (by omega : N - n = N + 1 - (n + 1))).hom := rfl

@[reassoc]
lemma dualHom_comp_dualDesuspIso_hom (f : K ⟶ L) :
    dualHom J N f ≫ (dualDesuspIso J N K).hom =
      (dualDesuspIso J N L).hom ≫ desuspMap (dualHom J (N + 1) f) := by
  ext n
  simp only [comp_f, dualHom_f, dualDesuspIso_hom_f, desuspMap_f]
  exact star_f_XIsoOfEq f (by omega)

end Desusp

section BottomRow

variable [HasBinaryBiproducts V] {C D : ChainComplex V ℤ} (j : C ⟶ D)

/-- `Σ⁻¹Cone(j) ⟶ C`, `(x, c) ↦ c`. -/
@[simps]
def coneFst : desusp (cone j) ⟶ C where
  f n := fstX j (n + 1) n (down_rel_succ n)
  comm' n n' h := by
    obtain rfl : n = n' + 1 := by simp at h; omega
    simp [d_fstX j (n' + 1 + 1) (n' + 1) n' (down_rel_succ _) (down_rel_succ _)]

/-- The degreewise split sequence `0 ⟶ Σ⁻¹D ⟶ Σ⁻¹Cone(j) ⟶ C ⟶ 0`. -/
@[simps]
def coneSplit : DegreewiseSplit (desuspMap (inr j)) (coneFst j) where
  t n := sndX j (n + 1)
  s n := inlX j n (n + 1) (down_rel_succ n)
  it n := by simp
  sq n := by simp
  total n := by
    dsimp
    exact (add_comm _ _).trans (cone.id_X j (n + 1) n (down_rel_succ n)).symm

variable {j}

lemma inrX_eqToHom_fstX {a b k : ℤ} (h : a = b) (h' : (cone j).X a = (cone j).X b)
    (hb : (ComplexShape.down ℤ).Rel b k) :
    inrX j a ≫ eqToHom h' ≫ fstX j b k hb = 0 := by
  subst h; simp

lemma inlX_eqToHom_fstX {c a b k : ℤ} (hc : (ComplexShape.down ℤ).Rel a c) (h : a = b)
    (h' : (cone j).X a = (cone j).X b) (hb : (ComplexShape.down ℤ).Rel b k) :
    inlX j c a hc ≫ eqToHom h' ≫ fstX j b k hb =
      eqToHom (congrArg C.X (by simp at hc hb; omega : c = k)) := by
  subst h
  obtain rfl : c = k := by simp at hc hb; omega
  simp

end BottomRow

section R1

variable [HasBinaryBiproducts V] {J : StrictInvolution V} {N : ℤ} {C D R : ChainComplex V ℤ}
  {j : C ⟶ D} {q : D ⟶ R} (S : DegreewiseSplit j q) {φ : dualComplex J N C ⟶ C}
  (δφ : Homotopy (dualHom J N j ≫ φ ≫ j) 0)

omit [HasBinaryBiproducts V] in
include S in
@[reassoc (attr := simp)]
lemma star_q_star_j (n : ℤ) : J.star (q.f n) ≫ J.star (j.f n) = 0 := by
  rw [← J.star_comp, S.i_q, J.star_zero]

/-- The left square of the ladder, in dimension `N + 1`: `q^* ∘ TΨ = inr ∘ Ψ ∘ (Cone(j) ⟶ R)^*`. -/
lemma dualHom_comp_transposeHom_relDuality (hδφ : IsSymmHomotopy J N δφ) :
    dualHom J (N + 1) q ≫ transposeHom J (N + 1) (relDuality δφ) =
      dualHom J (N + 1) (coneToCoker S) ≫ relDuality δφ ≫ inr j := by
  ext n
  simp [transposeHom_f, J.star_comp, J.star_add, comp_add, add_comp, star_q_star_j_assoc S]
  rw [← relTop_transpose δφ hδφ n]
  simp

omit [HasBinaryBiproducts V] in
lemma XIsoOfEq_star_star_eqToHom {a b n : ℤ} (h : a = b) (h₁ : C.X (N - b) = C.X n)
    (h₂ : C.X (N - a) = C.X n) :
    (D.XIsoOfEq h).hom ≫ J.star (j.f b) ≫ J.star (φ.f b) ≫ eqToHom h₁ =
      J.star (j.f a) ≫ J.star (φ.f a) ≫ eqToHom h₂ := by
  subst h; simp

/-- The right square of the ladder: `Σ⁻¹(TΨ)` followed by `Σ⁻¹Cone(j) ⟶ C` is `-φ j^*`. -/
lemma dualDesuspIso_comp_transposeHom_relDuality (hφ : IsStrictSymm J N φ) :
    (dualDesuspIso J N D).hom ≫ desuspMap (transposeHom J (N + 1) (relDuality δφ)) ≫ coneFst j =
      dualHom J N j ≫ (-φ) := by
  ext n
  have hφn := congrArg (fun f ↦ f.f n) hφ
  simp only [transposeHom_f] at hφn
  simp [transposeHom_f, J.star_comp, J.star_add, comp_add, add_comp]
  rw [inrX_eqToHom_fstX (by omega), inlX_eqToHom_fstX _ (by omega), ← hφn, comp_zero, comp_zero,
    smul_zero, zero_add, XIsoOfEq_star_star_eqToHom (h₂ := congrArg C.X (by omega)), smul_smul,
    ← Int.negOnePow_add,
    negOnePow_eq_of_eq (N - n)
      (show (n + 1) * (N - n) + (N - n + 1) = n * (N - n) + 1 + 2 * (N - n) by ring),
    Int.negOnePow_succ]
  simp

/-- **R1** ([Ran80I, Prop. 3.4], degreewise split case): for a pair `(j : C ⟶ D, (δφ, φ))`
with `j` degreewise split (cokernel `R`), if the relative duality map
`Ψ : Cone(j)^{N+1-*} ⟶ D` is a homotopy equivalence, then so is the boundary
`φ : C^{N-*} ⟶ C`.  Proof: two-out-of-three (`homotopyEquivRight`) on the strict ladder from
`0 ⟶ R^{N-*} ⟶ D^{N-*} ⟶ C^{N-*} ⟶ 0` to `0 ⟶ Σ⁻¹D ⟶ Σ⁻¹Cone(j) ⟶ C ⟶ 0` with vertical maps
`Σ⁻¹(Ψ ∘ (Cone(j) ⟶ R)^*)`, `Σ⁻¹(TΨ)` and `-φ`. -/
def boundaryHomotopyEquiv (hφ : IsStrictSymm J N φ) (hδφ : IsSymmHomotopy J N δφ)
    (eΨ : HomotopyEquiv (dualComplex J (N + 1) (cone j)) D) (heΨ : eΨ.hom = relDuality δφ) :
    HomotopyEquiv (dualComplex J N C) C :=
  HomotopyEquiv.negHom <| homotopyEquivRight (S.dual J N) (coneSplit j)
    ((HomotopyEquiv.ofIso (dualDesuspIso J N R)).trans (desuspHomotopyEquiv
      ((dualHomotopyEquiv J (N + 1) (coneToCokerEquiv S)).trans eΨ)))
    ((HomotopyEquiv.ofIso (dualDesuspIso J N D)).trans (desuspHomotopyEquiv
      ((dualHomotopyEquiv J (N + 1) eΨ).trans (HomotopyEquiv.ofIso (bidual J (N + 1) (cone j))))))
    (-φ) (by
      dsimp only [HomotopyEquiv.trans, HomotopyEquiv.ofIso]
      simp only [desuspHomotopyEquiv_hom, dualHomotopyEquiv_hom]
      simp only [heΨ, dualHom_comp_dualDesuspIso_hom_assoc, assoc, ← desuspMap_comp]
      congr 2
      exact dualHom_comp_transposeHom_relDuality S δφ hδφ) (by
      dsimp only [HomotopyEquiv.trans, HomotopyEquiv.ofIso]
      simp only [desuspHomotopyEquiv_hom, dualHomotopyEquiv_hom]
      simp only [heΨ, assoc]
      exact (dualDesuspIso_comp_transposeHom_relDuality δφ hφ).symm)

@[simp]
lemma boundaryHomotopyEquiv_hom (hφ : IsStrictSymm J N φ) (hδφ : IsSymmHomotopy J N δφ)
    (eΨ : HomotopyEquiv (dualComplex J (N + 1) (cone j)) D) (heΨ : eΨ.hom = relDuality δφ) :
    (boundaryHomotopyEquiv S δφ hφ hδφ eΨ heΨ).hom = φ := by
  simp [boundaryHomotopyEquiv]

omit [HasBinaryBiproducts V] in
/-- With identity idempotents, a Kar equivalence is a homotopy equivalence. -/
lemma isKarEquiv_id_iff {X Y : ChainComplex V ℤ} (f : X ⟶ Y) :
    IsKarEquiv (𝟙 X) (𝟙 Y) f ↔ ∃ e : HomotopyEquiv X Y, e.hom = f :=
  ⟨fun ⟨g, _, ⟨H₁⟩, ⟨H₂⟩⟩ ↦ ⟨⟨f, g, H₂, H₁⟩, rfl⟩,
    fun ⟨e, he⟩ ↦ he ▸ ⟨e.inv, by simp, ⟨e.homotopyInvHomId⟩, ⟨e.homotopyHomInvId⟩⟩⟩

include S in
/-- **R1**, `IsPoincare` form: the boundary of a degreewise split pair with identity idempotents
whose relative duality map is an equivalence is Poincaré. -/
theorem isPoincare_of_degreewiseSplit (hφ : IsStrictSymm J N φ) (hδφ : IsSymmHomotopy J N δφ)
    (hΨ : IsKarEquiv (𝟙 _) (𝟙 D) (relDuality δφ)) : IsPoincare J N (𝟙 C) φ := by
  obtain ⟨eΨ, he⟩ := (isKarEquiv_id_iff _).mp hΨ
  rw [isPoincare_iff, dualHom_id]
  exact (isKarEquiv_id_iff _).mpr ⟨_, boundaryHomotopyEquiv_hom S δφ hφ hδφ eΨ he⟩

include S in
/-- For degreewise split `j`, the relative duality map `Ψ` is an equivalence as soon as the
relative cap `Ψ q^* : R^{N+1-*} ⟶ D` is (l. 1015: "`Ψq^*` is precisely cap from relative
cochains to absolute chains"). -/
theorem isKarEquiv_relDuality_of_split
    (h : IsKarEquiv (𝟙 _) (𝟙 D) (dualHom J (N + 1) (coneToCoker S) ≫ relDuality δφ)) :
    IsKarEquiv (𝟙 _) (𝟙 D) (relDuality δφ) := by
  obtain ⟨e, he⟩ := (isKarEquiv_id_iff _).mp h
  let e' := (dualHomotopyEquiv J (N + 1) (coneToCokerEquiv S)).symm.trans e
  have H : Homotopy e'.hom (relDuality δφ) := by
    refine homotopyCongr (((dualHomotopy J (N + 1)
      (coneToCokerEquiv S).homotopyHomInvId).compRight (relDuality δφ))) ?_ (by simp)
    simp [e', HomotopyEquiv.trans, HomotopyEquiv.symm, he, coneToCokerEquiv]
  exact (isKarEquiv_id_iff _).mpr ⟨HomotopyEquiv.ofHomotopy e' H, rfl⟩

end R1

section TwoOutOfThree

variable [HasBinaryBiproducts V] {K M Q K' M' Q' : ChainComplex V ℤ} {i : K ⟶ M} {q : M ⟶ Q}
  {i' : K' ⟶ M'} {q' : M' ⟶ Q'} (S : DegreewiseSplit i q) (S' : DegreewiseSplit i' q')
  {l : K ⟶ K'} {m : M ⟶ M'} {r : Q ⟶ Q'}

include S S' in
/-- **R2** in `IsKarEquiv` form (identity idempotents), left. -/
theorem isKarEquiv_left (h₁ : i ≫ m = l ≫ i') (h₂ : q ≫ r = m ≫ q')
    (hm : IsKarEquiv (𝟙 M) (𝟙 M') m) (hr : IsKarEquiv (𝟙 Q) (𝟙 Q') r) :
    IsKarEquiv (𝟙 K) (𝟙 K') l := by
  obtain ⟨em, rfl⟩ := (isKarEquiv_id_iff _).mp hm
  obtain ⟨er, rfl⟩ := (isKarEquiv_id_iff _).mp hr
  exact (isKarEquiv_id_iff _).mpr ⟨homotopyEquivLeft S S' em er l h₁ h₂, rfl⟩

include S S' in
/-- **R2** in `IsKarEquiv` form (identity idempotents), right. -/
theorem isKarEquiv_right (h₁ : i ≫ m = l ≫ i') (h₂ : q ≫ r = m ≫ q')
    (hl : IsKarEquiv (𝟙 K) (𝟙 K') l) (hm : IsKarEquiv (𝟙 M) (𝟙 M') m) :
    IsKarEquiv (𝟙 Q) (𝟙 Q') r := by
  obtain ⟨el, rfl⟩ := (isKarEquiv_id_iff _).mp hl
  obtain ⟨em, rfl⟩ := (isKarEquiv_id_iff _).mp hm
  exact (isKarEquiv_id_iff _).mpr ⟨homotopyEquivRight S S' el em r h₁ h₂, rfl⟩

end TwoOutOfThree

section OfSplit

variable [HasBinaryBiproducts V] {J : StrictInvolution V} {N : ℤ}

lemma coneMap_id {B D : ChainComplex V ℤ} (j : B ⟶ D) :
    coneMap (j := j) (j' := j) (𝟙 B) (𝟙 D) (by simp) = 𝟙 _ := by
  ext i
  apply ext_from_X j (i - 1) i (down_rel_pred i) <;> simp

/-- **Based Poincaré pairs (R1)**: a strictly symmetric pair `(j : C ⟶ D, (δφ, φ))` of complexes
with identity idempotents, `j` degreewise split, whose relative duality map `Ψ` is a homotopy
equivalence.  The boundary `(C, φ)` is Poincaré by `isPoincare_of_degreewiseSplit` (l. 1084:
"a closed controlled duality on each interface"), so this is a `SymPair`. -/
@[simps]
def SymPair.ofSplit {C D R : ChainComplex V ℤ} (hC : SupportedIn (𝟙 C) 0 N)
    (hD : SupportedIn (𝟙 D) 0 (N + 1)) (φ : dualComplex J N C ⟶ C) (hφ : IsStrictSymm J N φ)
    {j : C ⟶ D} {q : D ⟶ R} (S : DegreewiseSplit j q)
    (δφ : Homotopy (dualHom J N j ≫ φ ≫ j) 0) (hδφ : IsSymmHomotopy J N δφ)
    (hΨ : IsKarEquiv (𝟙 _) (𝟙 D) (relDuality δφ)) : SymPair J N where
  bd :=
    { C := C
      p := 𝟙 C
      p_idem := by simp
      support := hC
      φ := φ
      φ_kar := by simp
      symm := hφ
      poincare := isPoincare_of_degreewiseSplit S δφ hφ hδφ hΨ }
  D := D
  pD := 𝟙 D
  pD_idem := by simp
  support := hD
  j := j
  j_kar := by simp
  δφ := δφ
  δφ_kar r r' := by simp
  symm := hδφ
  poincare := by
    rw [coneMap_id, dualHom_id J (N + 1) (cone j)]
    exact hΨ

end OfSplit

end

end HSFormal.LTheory
