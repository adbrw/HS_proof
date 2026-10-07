import HSFormal.LTheory.Isometry
import Mathlib.Algebra.Homology.HomotopyCofiber

/-!
# Symmetric Poincaré pairs and cobordism (L-theory module M2)

Mapping cones, strictly symmetric Poincaré pairs `(j : C ⟶ D, (δφ, φ))` and their relative
duality map `Ψ` (manuscript l. 963–983), null-cobordisms and cobordisms, in the Karoubi model of
`blueprint/L-theory-design.md` §2.2.  A pair of dimension `N + 1` has boundary of dimension `N`
(design W8).

**Cone.** `cone j` is mathlib's `homotopyCofiber j`: `Cone(j)_r = B_{r-1} ⊞ D_r` with
`d(x, c) = (dx + jc, -dc)`, which is exactly l. 965 (`fstX`/`inlX` is the `B`-summand).

**Relative boundary sign (l. 966).** The paper's relation (its `N` is our `N + 1`)
`d_D δφ_r - (-1)^r δφ_{r-1} d_D^* = j φ_{r-1} j^*`
says, since `dualComplex J N D` has differential `δ_s = (-1)^s d^*`, that
`j φ j^* = d ∘ δφ + δφ ∘ δ` as maps `D^{N-*} ⟶ D`, with `δφ_{s+1} : D^{N-s} ⟶ D_{s+1}` of
degree `+1`.  Mathlib's `Homotopy f g` is `f - g = dH + Hd`, so the relative boundary is
*literally* `δφ : Homotopy (dualHom J N j ≫ φ ≫ j) 0` with `δφ.hom (r - 1) r = δφ_r` (no sign);
`relTop` is this component with the `(N+1)`-dual indexing, and `IsSymmHomotopy J N δφ` is
Ranicki's `T δφ = δφ` in dimension `N + 1`.  With these conventions the paper's
`Ψ_r = δφ_r ⊕ (-1)^{r+1} j φ_r` (l. 969) is a chain map (`relDuality`).
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression

noncomputable section

universe v v' u u'

variable {V : Type u} [Category.{v} V] [Preadditive V] (J : StrictInvolution V) (N : ℤ)

section KarEquiv

variable {X Y Z : ChainComplex V ℤ}

/-- `f : (X, e) ⟶ (Y, e')` is a chain homotopy equivalence in `Kar V` (homotopies in `V`, as in
`IsPoincare`). -/
def IsKarEquiv (e : X ⟶ X) (e' : Y ⟶ Y) (f : X ⟶ Y) : Prop :=
  ∃ g : Y ⟶ X, e' ≫ g ≫ e = g ∧ Nonempty (Homotopy (g ≫ f) e') ∧
    Nonempty (Homotopy (f ≫ g) e)

variable {J N} in
lemma isPoincare_iff {C : ChainComplex V ℤ} {p : C ⟶ C} {φ : dualComplex J N C ⟶ C} :
    IsPoincare J N p φ ↔ IsKarEquiv (dualHom J N p) p φ := Iff.rfl

namespace IsKarEquiv

variable {e : X ⟶ X} {e' : Y ⟶ Y} {e'' : Z ⟶ Z} {f f' : X ⟶ Y}

lemma of_homotopy (h : IsKarEquiv e e' f) (H : Homotopy f f') : IsKarEquiv e e' f' := by
  obtain ⟨g, hg, ⟨H₁⟩, ⟨H₂⟩⟩ := h
  exact ⟨g, hg, ⟨((Homotopy.refl g).comp H).symm.trans H₁⟩,
    ⟨(H.comp (Homotopy.refl g)).symm.trans H₂⟩⟩

lemma of_eq (h : IsKarEquiv e e' f) (hf : f = f') : IsKarEquiv e e' f' := hf ▸ h

lemma neg (h : IsKarEquiv e e' f) : IsKarEquiv e e' (-f) := by
  obtain ⟨g, hg, ⟨H₁⟩, ⟨H₂⟩⟩ := h
  exact ⟨-g, by simp [hg], ⟨homotopyCongr H₁ (by simp) rfl⟩,
    ⟨homotopyCongr H₂ (by simp) rfl⟩⟩

lemma comp {g : Y ⟶ Z} (hf : IsKarEquiv e e' f) (hg : IsKarEquiv e' e'' g) (he : e ≫ e = e)
    (he' : e' ≫ e' = e') (he'' : e'' ≫ e'' = e'') : IsKarEquiv e e'' (f ≫ g) := by
  obtain ⟨f', hf', ⟨F₁⟩, ⟨F₂⟩⟩ := hf
  obtain ⟨g', hg', ⟨G₁⟩, ⟨G₂⟩⟩ := hg
  have h₁ : f' ≫ e = f' := by rw [← hf']; simp [he]
  have h₂ : e' ≫ f' = f' := by rw [← hf', ← assoc, he']
  have h₃ : g' ≫ e' = g' := by rw [← hg']; simp [he']
  have h₄ : e'' ≫ g' = g' := by rw [← hg', ← assoc, he'']
  refine ⟨g' ≫ f', by simp [reassoc_of% h₄, h₁], ⟨?_⟩, ⟨?_⟩⟩
  · exact (homotopyCongr ((Homotopy.refl g').comp (F₁.comp (Homotopy.refl g))) (by simp)
      (by simp [reassoc_of% h₃])).trans G₁
  · exact (homotopyCongr ((Homotopy.refl f).comp (G₂.comp (Homotopy.refl f'))) (by simp)
      (by simp [h₂])).trans F₂

/-- Transport along an isomorphism of the source. -/
lemma conjIso (h : IsKarEquiv e e' f) {X' : ChainComplex V ℤ} (α : X ≅ X') :
    IsKarEquiv (α.inv ≫ e ≫ α.hom) e' (α.inv ≫ f) := by
  obtain ⟨g, hg, ⟨H₁⟩, ⟨H₂⟩⟩ := h
  refine ⟨g ≫ α.hom, by simp [reassoc_of% hg], ⟨homotopyCongr H₁ (by simp) rfl⟩,
    ⟨homotopyCongr ((H₂.compLeft α.inv).compRight α.hom) (by simp) (by simp)⟩⟩

lemma map {W : Type u'} [Category.{v'} W] [Preadditive W] (F : V ⥤ W) [F.Additive]
    (h : IsKarEquiv e e' f) :
    IsKarEquiv ((F.mapHomologicalComplex _).map e) ((F.mapHomologicalComplex _).map e')
      ((F.mapHomologicalComplex _).map f) := by
  obtain ⟨g, hg, ⟨H₁⟩, ⟨H₂⟩⟩ := h
  exact ⟨(F.mapHomologicalComplex _).map g, by simp only [← Functor.map_comp, hg],
    ⟨homotopyCongr (F.mapHomotopy H₁) (Functor.map_comp _ _ _) rfl⟩,
    ⟨homotopyCongr (F.mapHomotopy H₂) (Functor.map_comp _ _ _) rfl⟩⟩

end IsKarEquiv

end KarEquiv

section ConeLemmas

variable {J}

lemma star_injective {X Y : V} : Function.Injective (J.star : (X ⟶ Y) → (Y ⟶ X)) :=
  fun f g h ↦ by rw [← J.star_star f, h, J.star_star]

@[reassoc]
lemma star_f_XIsoOfEq {K L : ChainComplex V ℤ} (f : K ⟶ L) {a a' : ℤ} (h : a = a') :
    J.star (f.f a) ≫ (K.XIsoOfEq h).hom = (L.XIsoOfEq h).hom ≫ J.star (f.f a') := by
  subst h; simp

@[reassoc]
lemma star_d_XIsoOfEq (K : ChainComplex V ℤ) {a a' : ℤ} (b : ℤ) (h : a = a') :
    J.star (K.d a b) ≫ (K.XIsoOfEq h).hom = J.star (K.d a' b) := by
  subst h; simp

@[reassoc]
lemma XIsoOfEq_star_d (K : ChainComplex V ℤ) {a a' b b' : ℤ} (ha : a = a') (hb : b = b') :
    (K.XIsoOfEq hb).hom ≫ J.star (K.d a' b') = J.star (K.d a b) ≫ (K.XIsoOfEq ha).hom := by
  subst ha hb; simp

variable (J) in
/-- The dual `D^{N-*} ≅ C^{N-*}` of an isomorphism `C ≅ D`. -/
@[simps]
def dualIso {C D : ChainComplex V ℤ} (e : C ≅ D) : dualComplex J N D ≅ dualComplex J N C where
  hom := dualHom J N e.hom
  inv := dualHom J N e.inv
  hom_inv_id := by rw [← dualHom_comp, e.inv_hom_id, dualHom_id]
  inv_hom_id := by rw [← dualHom_comp, e.hom_inv_id, dualHom_id]

lemma down_rel_sub (r : ℤ) : (ComplexShape.down ℤ).Rel (N + 1 - r) (N - r) := by
  simp only [ComplexShape.down_Rel]; omega

lemma down_exists_rel (k : ℤ) : ∃ i, (ComplexShape.down ℤ).Rel i k := ⟨k + 1, rfl⟩

end ConeLemmas

section RelTop

variable {J N} {B D : ChainComplex V ℤ} {j : B ⟶ D} {φ : dualComplex J N B ⟶ B}

/-- The top component `δφ_r : D^{N+1-r} ⟶ D_r` of a relative boundary `δφ` (l. 966). -/
def relTop (H : Homotopy (dualHom J N j ≫ φ ≫ j) 0) (r : ℤ) : D.X (N + 1 - r) ⟶ D.X r :=
  (D.XIsoOfEq (by omega : N + 1 - r = N - (r - 1))).hom ≫ H.hom (r - 1) r

lemma relTop_eq (H : Homotopy (dualHom J N j ≫ φ ≫ j) 0) (s r : ℤ) (h : s + 1 = r) :
    relTop H r = (D.XIsoOfEq (by omega : N + 1 - r = N - s)).hom ≫ H.hom s r := by
  obtain rfl : s = r - 1 := by omega
  rfl

/-- The relative cycle condition (l. 966) in the `(N+1)`-dual indexing:
`δφ_r d = δ δφ_{r-1} + j φ_{r-1} j^*`. -/
lemma relTop_comm (H : Homotopy (dualHom J N j ≫ φ ≫ j) 0) (r r' : ℤ)
    (h : (ComplexShape.down ℤ).Rel r r') :
    relTop H r ≫ D.d r r' = ((dualComplex J (N + 1) D).d r r' ≫ relTop H r' :
      D.X (N + 1 - r) ⟶ D.X r') +
      (D.XIsoOfEq (by simp only [ComplexShape.down_Rel] at h; omega : N + 1 - r = N - r')).hom ≫
        (dualHom J N j ≫ φ ≫ j).f r' := by
  obtain rfl : r = r' + 1 := by simp only [ComplexShape.down_Rel] at h; omega
  have hc : H.hom r' (r' + 1) ≫ D.d (r' + 1) r' = (dualHom J N j ≫ φ ≫ j).f r' -
      (dualComplex J N D).d r' (r' - 1) ≫ H.hom (r' - 1) r' := by
    rw [H.comm r', dNext_eq _ (show (ComplexShape.down ℤ).Rel r' (r' - 1) by simp),
      prevD_eq _ h, zero_f, add_zero]
    abel
  rw [relTop_eq H r' _ rfl, relTop_eq H (r' - 1) r' (by omega), assoc, hc]
  simp only [dualComplex_d, comp_sub, Linear.units_smul_comp, Linear.comp_units_smul,
    XIsoOfEq_star_d_assoc D (show N + 1 - r' = N - (r' - 1) by omega)
      (show N + 1 - (r' + 1) = N - r' by omega)]
  rw [Int.negOnePow_succ, Units.neg_smul]
  abel

lemma star_comp_relTop (H : Homotopy (dualHom J N j ≫ φ ≫ j) 0) {pD : D ⟶ D}
    (hH : ∀ r r', (dualHom J N pD).f r ≫ H.hom r r' = H.hom r r') (r : ℤ) :
    J.star (pD.f (N + 1 - r)) ≫ relTop H r = relTop H r := by
  rw [relTop, star_f_XIsoOfEq_assoc, ← dualHom_f, hH]

end RelTop

section Cone

variable [HasBinaryBiproducts V] {B D B' D' B'' D'' : ChainComplex V ℤ} (j : B ⟶ D)

/-- The mapping cone `Cone(j)_r = B_{r-1} ⊞ D_r`, `d(x, c) = (dx + jc, -dc)` (l. 963–966):
mathlib's `homotopyCofiber`, whose `fstX`/`inlX` is the `B`-summand and `sndX`/`inrX` the
`D`-summand. -/
abbrev cone : ChainComplex V ℤ := homotopyCofiber j

namespace cone

open homotopyCofiber

variable {J}

lemma fstX_eq {i k k' : ℤ} (h : (ComplexShape.down ℤ).Rel i k)
    (h' : (ComplexShape.down ℤ).Rel i k') :
    fstX j i k' h' = fstX j i k h ≫
      (B.XIsoOfEq (by simp only [ComplexShape.down_Rel] at h h'; omega)).hom := by
  obtain rfl : k' = k := by simp only [ComplexShape.down_Rel] at h h'; omega
  simp

lemma inlX_eq {i k k' : ℤ} (h : (ComplexShape.down ℤ).Rel i k)
    (h' : (ComplexShape.down ℤ).Rel i k') :
    inlX j k' i h' = (B.XIsoOfEq (by simp only [ComplexShape.down_Rel] at h h'; omega)).hom ≫
      inlX j k i h := by
  obtain rfl : k' = k := by simp only [ComplexShape.down_Rel] at h h'; omega
  simp

lemma id_X (i k : ℤ) (h : (ComplexShape.down ℤ).Rel i k) :
    𝟙 ((cone j).X i) = fstX j i k h ≫ inlX j k i h + sndX j i ≫ inrX j i := by
  apply ext_to_X j i k h <;> simp

@[reassoc (attr := simp)]
lemma star_fstX_inlX (i k : ℤ) (h : (ComplexShape.down ℤ).Rel i k) :
    J.star (fstX j i k h) ≫ J.star (inlX j k i h) = 𝟙 _ := by
  rw [← J.star_comp, inlX_fstX, J.star_id]

@[reassoc (attr := simp)]
lemma star_fstX_inrX (i k : ℤ) (h : (ComplexShape.down ℤ).Rel i k) :
    J.star (fstX j i k h) ≫ J.star (inrX j i) = 0 := by
  rw [← J.star_comp, inrX_fstX, J.star_zero]

@[reassoc (attr := simp)]
lemma star_sndX_inlX (i k : ℤ) (h : (ComplexShape.down ℤ).Rel i k) :
    J.star (sndX j i) ≫ J.star (inlX j k i h) = 0 := by
  rw [← J.star_comp, inlX_sndX, J.star_zero]

@[reassoc (attr := simp)]
lemma star_sndX_inrX (i : ℤ) : J.star (sndX j i) ≫ J.star (inrX j i) = 𝟙 _ := by
  rw [← J.star_comp, inrX_sndX, J.star_id]

@[reassoc]
lemma star_fstX_inlX' {i k k' : ℤ} (h : (ComplexShape.down ℤ).Rel i k)
    (h' : (ComplexShape.down ℤ).Rel i k') :
    J.star (fstX j i k h) ≫ J.star (inlX j k' i h') =
      (B.XIsoOfEq (by simp only [ComplexShape.down_Rel] at h h'; omega)).hom := by
  obtain rfl : k' = k := by simp only [ComplexShape.down_Rel] at h h'; omega
  simp

/-- Maps out of `Cone(j)_i` are determined on the dual summands `fstX^*`, `sndX^*`. -/
lemma ext_star {A : V} (i k : ℤ) (h : (ComplexShape.down ℤ).Rel i k) {f g : (cone j).X i ⟶ A}
    (h₁ : J.star (fstX j i k h) ≫ f = J.star (fstX j i k h) ≫ g)
    (h₂ : J.star (sndX j i) ≫ f = J.star (sndX j i) ≫ g) : f = g := by
  have e (x : (cone j).X i ⟶ A) : x = J.star (inlX j k i h) ≫ J.star (fstX j i k h) ≫ x +
      J.star (inrX j i) ≫ J.star (sndX j i) ≫ x := by
    rw [← assoc, ← assoc, ← J.star_comp, ← J.star_comp, ← add_comp, ← J.star_add,
      ← id_X]
    simp
  rw [e f, e g, h₁, h₂]

@[reassoc]
lemma star_fstX_d (i i' k : ℤ) (hi : (ComplexShape.down ℤ).Rel i i')
    (hk : (ComplexShape.down ℤ).Rel i' k) :
    J.star (fstX j i' k hk) ≫ J.star ((cone j).d i i') =
      -J.star (B.d i' k) ≫ J.star (fstX j i i' hi) := by
  rw [← J.star_comp, homotopyCofiber_d, d_fstX j i i' k hi hk, J.star_neg, J.star_comp]

@[reassoc]
lemma star_sndX_d (i i' : ℤ) (hi : (ComplexShape.down ℤ).Rel i i') :
    J.star (sndX j i') ≫ J.star ((cone j).d i i') =
      J.star (j.f i') ≫ J.star (fstX j i i' hi) + J.star (D.d i i') ≫ J.star (sndX j i) := by
  rw [← J.star_comp, homotopyCofiber_d, d_sndX j i i' hi, J.star_add, J.star_comp, J.star_comp]

end cone

open homotopyCofiber

variable {J} {j} {j' : B' ⟶ D'} {j'' : B'' ⟶ D''}

/-- The chain map `diag(m, n) : Cone(j) ⟶ Cone(j')` of a square `m ≫ j' = j ≫ n`. -/
def coneMap (m : B ⟶ B') (n : D ⟶ D') (h : m ≫ j' = j ≫ n) : cone j ⟶ cone j' :=
  desc j (n ≫ inr j')
    (homotopyCongr ((inrCompHomotopy j' down_exists_rel).compLeft m) (by rw [reassoc_of% h])
      (by simp))

section coneMap

variable {m m' : B ⟶ B'} {n n' : D ⟶ D'} (h : m ≫ j' = j ≫ n) (h' : m' ≫ j' = j ≫ n')

@[reassoc (attr := simp)]
lemma inlX_coneMap_f (i k : ℤ) (hk : (ComplexShape.down ℤ).Rel i k) :
    inlX j k i hk ≫ (coneMap m n h).f i = m.f k ≫ inlX j' k i hk := by
  simp [coneMap, inlX_desc_f _ _ _ _ _ hk, inrCompHomotopy_hom _ _ _ _ hk]

@[reassoc (attr := simp)]
lemma inrX_coneMap_f (i : ℤ) : inrX j i ≫ (coneMap m n h).f i = n.f i ≫ inrX j' i := by
  simp [coneMap, inrX_desc_f]

@[reassoc (attr := simp)]
lemma coneMap_f_fstX (i k : ℤ) (hk : (ComplexShape.down ℤ).Rel i k) :
    (coneMap m n h).f i ≫ fstX j' i k hk = fstX j i k hk ≫ m.f k := by
  apply ext_from_X j k i hk <;> simp

@[reassoc (attr := simp)]
lemma coneMap_f_sndX (i : ℤ) : (coneMap m n h).f i ≫ sndX j' i = sndX j i ≫ n.f i := by
  apply ext_from_X j (i - 1) i (by simp) <;> simp

lemma coneMap_f (i k : ℤ) (hk : (ComplexShape.down ℤ).Rel i k) :
    (coneMap m n h).f i =
      fstX j i k hk ≫ m.f k ≫ inlX j' k i hk + sndX j i ≫ n.f i ≫ inrX j' i := by
  conv_lhs => rw [← id_comp ((coneMap m n h).f i), cone.id_X j i k hk]
  simp

lemma star_coneMap_f (i k : ℤ) (hk : (ComplexShape.down ℤ).Rel i k) :
    J.star ((coneMap m n h).f i) = J.star (inlX j' k i hk) ≫ J.star (m.f k) ≫
      J.star (fstX j i k hk) + J.star (inrX j' i) ≫ J.star (n.f i) ≫ J.star (sndX j i) := by
  rw [coneMap_f h i k hk]
  simp only [J.star_add, J.star_comp, assoc]

@[reassoc]
lemma coneMap_comp {m₂ : B' ⟶ B''} {n₂ : D' ⟶ D''} (h₂ : m₂ ≫ j'' = j' ≫ n₂) :
    coneMap m n h ≫ coneMap m₂ n₂ h₂ =
      coneMap (m ≫ m₂) (n ≫ n₂) (by rw [assoc, h₂, reassoc_of% h]) := by
  ext i
  apply ext_from_X j (i - 1) i (by simp) <;> simp

lemma coneMap_idem {m : B ⟶ B} {n : D ⟶ D} (h : m ≫ j = j ≫ n) (hm : m ≫ m = m)
    (hn : n ≫ n = n) : coneMap m n h ≫ coneMap m n h = coneMap m n h := by
  simp [coneMap_comp, hm, hn]

lemma coneMap_add :
    coneMap (m + m') (n + n') (by simp [h, h']) = coneMap m n h + coneMap m' n' h' := by
  ext i
  apply ext_from_X j (i - 1) i (by simp) <;> simp

lemma coneMap_zero :
    coneMap (0 : B ⟶ B') (0 : D ⟶ D') (by simp) = (0 : cone j ⟶ cone j') := by
  ext i
  apply ext_from_X j (i - 1) i (by simp) <;> simp

end coneMap

variable (j j') in
/-- For a chain map `t : D ⟶ B'`, `h(x, c) = (0, t x)` is a null-homotopy of
`diag(j ≫ t, t ≫ j') : Cone(j) ⟶ Cone(j')`. -/
def coneNullHomotopy (t : D ⟶ B') :
    Homotopy (coneMap (j := j) (j' := j') (j ≫ t) (t ≫ j') (by simp)) 0 where
  hom i i' :=
    if hi : (ComplexShape.down ℤ).Rel i' i then sndX j i ≫ t.f i ≫ inlX j' i i' hi else 0
  zero i i' hi := dite_eq_right hi
  comm i := by
    have h₁ : (ComplexShape.down ℤ).Rel i (i - 1) := by simp
    have h₂ : (ComplexShape.down ℤ).Rel (i - 1) (i - 1 - 1) := by simp
    rw [dNext_eq _ h₁, prevD_eq _ (show (ComplexShape.down ℤ).Rel (i + 1) i by simp),
      dite_eq_left h₁, dite_eq_left (show (ComplexShape.down ℤ).Rel (i + 1) i by simp)]
    apply ext_from_X j (i - 1) i h₁
    · simp [homotopyCofiber_d, inlX_d_assoc j i (i - 1) (i - 1 - 1) h₁ h₂]
    · simp only [homotopyCofiber_d, inrX_d_assoc, assoc, inrX_coneMap_f, comp_f, zero_f,
        add_zero, comp_add, inrX_sndX_assoc]
      rw [inlX_d j' (i + 1) i (i - 1) (by simp) h₁, comp_add, comp_neg, t.comm_assoc]
      abel

/-- `diag(j ≫ t + m', t ≫ j' + n') ≃ diag(m', n')`. -/
def coneHomotopy (t : D ⟶ B') {m m' : B ⟶ B'} {n n' : D ⟶ D'} (h : m ≫ j' = j ≫ n)
    (h' : m' ≫ j' = j ≫ n') (hm : m = j ≫ t + m') (hn : n = t ≫ j' + n') :
    Homotopy (coneMap m n h) (coneMap m' n' h') :=
  homotopyCongr ((coneNullHomotopy j j' t).add (Homotopy.refl (coneMap m' n' h')))
    (by subst hm hn; rw [coneMap_add]) (zero_add _)

end Cone

section Dual

variable [HasBinaryBiproducts V] {B D K B' D' : ChainComplex V ℤ} (j : B ⟶ D)

open homotopyCofiber

variable {J N}

/-- The boundary inclusion `ι : B^{N-*} ⟶ Cone(j)^{N+1-*}`, `ι_r = (-1)^r fstX^*` (the dual of
the projection `Cone(j) ⟶ ΣB`). -/
def bdInc : dualComplex J N B ⟶ dualComplex J (N + 1) (cone j) where
  f r := r.negOnePow • J.star (fstX j (N + 1 - r) (N - r) (down_rel_sub N r))
  comm' r r' h := by
    obtain rfl : r = r' + 1 := by simp only [ComplexShape.down_Rel] at h; omega
    apply star_injective (J := J)
    simp only [dualComplex_d, J.star_comp, J.star_units_smul, J.star_star, Linear.units_smul_comp,
      Linear.comp_units_smul, smul_smul, homotopyCofiber_d]
    rw [d_fstX j _ _ _ (by simp only [ComplexShape.down_Rel]; omega),
      cone.fstX_eq j (down_rel_sub N r') (by simp only [ComplexShape.down_Rel]; omega), assoc,
      XIsoOfEq_hom_comp_d, Int.negOnePow_succ]
    simp

@[simp]
lemma bdInc_f (r : ℤ) :
    (bdInc (J := J) (N := N) j).f r =
      r.negOnePow • J.star (fstX j (N + 1 - r) (N - r) (down_rel_sub N r)) :=
  rfl

variable {j} in
@[reassoc]
lemma bdInc_comp_dualHom_coneMap {j' : B' ⟶ D'} {m : B ⟶ B'} {n : D ⟶ D'}
    (h : m ≫ j' = j ≫ n) :
    bdInc (J := J) (N := N) j' ≫ dualHom J (N + 1) (coneMap m n h) =
      dualHom J N m ≫ bdInc j := by
  ext r
  simp only [comp_f, bdInc_f, dualHom_f, Linear.units_smul_comp, Linear.comp_units_smul,
    ← J.star_comp, coneMap_f_fstX]

/-- For `k : K ⟶ B` with `k ≫ j = 0`, `λ_r = (-1)^r inlX^* k^* : Cone(j)^{N+1-*} ⟶ K^{N-*}`
(the dual of `ΣK ⟶ Cone(j)`). -/
def coneDualFst (k : K ⟶ B) (hk : k ≫ j = 0) :
    dualComplex J (N + 1) (cone j) ⟶ dualComplex J N K where
  f r := r.negOnePow • J.star (inlX j (N - r) (N + 1 - r) (down_rel_sub N r)) ≫ J.star (k.f (N - r))
  comm' r r' h := by
    obtain rfl : r = r' + 1 := by simp only [ComplexShape.down_Rel] at h; omega
    have hk' (i : ℤ) {Z : V} (g : D.X i ⟶ Z) : k.f i ≫ j.f i ≫ g = 0 := by
      rw [← comp_f_assoc, hk, zero_f, zero_comp]
    have hij : (ComplexShape.down ℤ).Rel (N + 1 - r') (N + 1 - (r' + 1)) := by
      simp only [ComplexShape.down_Rel]; omega
    apply star_injective (J := J)
    simp only [dualComplex_d, J.star_comp, J.star_units_smul, J.star_star, Linear.units_smul_comp,
      Linear.comp_units_smul, smul_smul, homotopyCofiber_d, assoc]
    rw [cone.inlX_eq j hij (down_rel_sub N r')]
    simp only [assoc]
    rw [XIsoOfEq_hom_naturality_assoc, inlX_d j _ _ _ hij (down_rel_sub N (r' + 1))]
    simp only [comp_add, comp_neg, hk', add_zero, k.comm_assoc, XIsoOfEq_hom_comp_d_assoc,
      Int.negOnePow_succ]
    simp

@[simp]
lemma coneDualFst_f (k : K ⟶ B) (hk : k ≫ j = 0) (r : ℤ) :
    (coneDualFst (J := J) (N := N) j k hk).f r =
      r.negOnePow • J.star (inlX j (N - r) (N + 1 - r) (down_rel_sub N r)) ≫ J.star (k.f (N - r)) :=
  rfl

@[reassoc (attr := simp)]
lemma bdInc_comp_coneDualFst (k : K ⟶ B) (hk : k ≫ j = 0) :
    bdInc (J := J) (N := N) j ≫ coneDualFst j k hk = dualHom J N k := by
  ext r
  simp [smul_smul]

lemma coneDualFst_comp_bdInc (k : K ⟶ B) (hk : k ≫ j = 0) (m : B ⟶ K) :
    coneDualFst (J := J) (N := N) j k hk ≫ dualHom J N m ≫ bdInc j =
      dualHom J (N + 1) (coneMap (j := j) (j' := j) (m ≫ k) 0 (by simp [hk])) := by
  ext r
  simp [star_coneMap_f _ (N + 1 - r) (N - r) (down_rel_sub N r), smul_smul, J.star_comp]

variable {j} {φ : dualComplex J N B ⟶ B}

/-- The relative duality map `Ψ : Cone(j)^{N+1-*} ⟶ D`,
`Ψ_r(α, β) = δφ_r α + (-1)^{r+1} j φ_r β` (l. 969). -/
def relDuality (H : Homotopy (dualHom J N j ≫ φ ≫ j) 0) :
    dualComplex J (N + 1) (cone j) ⟶ D where
  f r := J.star (inrX j (N + 1 - r)) ≫ relTop H r +
    (r + 1).negOnePow • J.star (inlX j (N - r) (N + 1 - r) (down_rel_sub N r)) ≫ φ.f r ≫ j.f r
  comm' r r' h := by
    have hr : r = r' + 1 := by simp only [ComplexShape.down_Rel] at h; omega
    apply cone.ext_star (J := J) j _ _ (down_rel_sub N r)
    · simp only [dualComplex_d, comp_add, add_comp, assoc, Linear.comp_units_smul,
        Linear.units_smul_comp, cone.star_fstX_inrX_assoc, cone.star_fstX_inlX_assoc, zero_comp,
        zero_add, cone.star_fstX_d_assoc j _ _ _ (show (ComplexShape.down ℤ).Rel (N + 1 - r')
          (N + 1 - r) by simp only [ComplexShape.down_Rel]; omega), neg_comp,
        cone.star_fstX_inlX'_assoc j _ (down_rel_sub N r'), Hom.comm, φ.comm_assoc, comp_zero,
        neg_zero, star_d_XIsoOfEq_assoc]
      subst hr
      simp [Int.negOnePow_succ]
    · simp only [dualComplex_d, comp_add, add_comp, assoc, Linear.comp_units_smul,
        Linear.units_smul_comp, cone.star_sndX_inrX_assoc, cone.star_sndX_inlX_assoc, zero_comp,
        add_zero, cone.star_sndX_d_assoc j _ _ (show (ComplexShape.down ℤ).Rel (N + 1 - r')
          (N + 1 - r) by simp only [ComplexShape.down_Rel]; omega),
        cone.star_fstX_inlX'_assoc j _ (down_rel_sub N r'), cone.star_fstX_inrX_assoc,
        relTop_comm H r r' h, comp_zero, smul_zero, add_zero, zero_add, comp_f, dualHom_f,
        star_f_XIsoOfEq_assoc]
      subst hr
      simp [Int.negOnePow_succ, smul_smul]

@[simp]
lemma relDuality_f (H : Homotopy (dualHom J N j ≫ φ ≫ j) 0) (r : ℤ) :
    (relDuality H).f r = J.star (inrX j (N + 1 - r)) ≫ relTop H r +
      (r + 1).negOnePow • J.star (inlX j (N - r) (N + 1 - r) (down_rel_sub N r)) ≫ φ.f r ≫
        j.f r :=
  rfl

/-- On the boundary summand, `Ψ ι = -φ j` (l. 969: the `β`-component of `Ψ`). -/
@[reassoc (attr := simp)]
lemma bdInc_comp_relDuality (H : Homotopy (dualHom J N j ≫ φ ≫ j) 0) :
    bdInc j ≫ relDuality H = -(φ ≫ j) := by
  ext r
  simp [smul_smul, Int.negOnePow_succ]

/-- `Ψ` is a Kar-morphism `(Cone(j)^{N+1-*}, (p_B ⊕ p_D)^*) ⟶ (D, p_D)` (source side). -/
lemma dualHom_coneMap_comp_relDuality {pB : B ⟶ B} {pD : D ⟶ D} (h : pB ≫ j = j ≫ pD)
    (H : Homotopy (dualHom J N j ≫ φ ≫ j) 0) (hφ : dualHom J N pB ≫ φ = φ)
    (hH : ∀ r r', (dualHom J N pD).f r ≫ H.hom r r' = H.hom r r') :
    dualHom J (N + 1) (coneMap pB pD h) ≫ relDuality H = relDuality H := by
  have hφ' (r : ℤ) {Z : V} (g : B.X r ⟶ Z) :
      J.star (pB.f (N - r)) ≫ φ.f r ≫ g = φ.f r ≫ g := by
    rw [← dualHom_f, ← comp_f_assoc, hφ]
  ext r
  simp [star_coneMap_f h _ _ (down_rel_sub N r), star_comp_relTop H hH, hφ']

end Dual

lemma comm_of_kar {B D : ChainComplex V ℤ} {pB : B ⟶ B} {pD : D ⟶ D} {j : B ⟶ D}
    (hB : pB ≫ pB = pB) (hD : pD ≫ pD = pD) (hj : pB ≫ j ≫ pD = j) :
    pB ≫ j = j ≫ pD := by
  have h₁ : pB ≫ j = j := by conv_lhs => rw [← hj]
                             rw [reassoc_of% hB, hj]
  have h₂ : j ≫ pD = j := by conv_lhs => rw [← hj]
                             rw [assoc, assoc, hD, hj]
  rw [h₁, h₂]

variable [HasBinaryBiproducts V]

/-- An `(N+1)`-dimensional strictly symmetric Poincaré pair `(j : C ⟶ D, (δφ, φ))` in `Kar V`
(l. 963–983; [Ran80I, §3] over `ℚ`, design §2.1 (ii)): the boundary `bd = (C, p_C, φ)` is an
`N`-dimensional Poincaré complex, `(D, p_D)` is concentrated in `[0, N+1]`, `j` is a Kar chain
map, `δφ` is the relative boundary `j φ j^* = dδφ + δφδ` (l. 966; see the module docstring
for the sign), strictly symmetric and Kar, and the relative duality map
`Ψ : (Cone(j)^{N+1-*}, (p_C ⊕ p_D)^*) ⟶ (D, p_D)` is a homotopy equivalence in `Kar V`.
Ranicki's definition only asks for the last condition; it implies that the boundary is Poincaré
[Ran80I, Prop. 3.4], so recording `bd` as a `SymPoincare` is no restriction. -/
structure SymPair where
  bd : SymPoincare J N
  D : ChainComplex V ℤ
  pD : D ⟶ D
  pD_idem : pD ≫ pD = pD
  support : SupportedIn pD 0 (N + 1)
  j : bd.C ⟶ D
  j_kar : bd.p ≫ j ≫ pD = j
  δφ : Homotopy (dualHom J N j ≫ bd.φ ≫ j) 0
  δφ_kar : ∀ r r', (dualHom J N pD).f r ≫ δφ.hom r r' ≫ pD.f r' = δφ.hom r r'
  symm : IsSymmHomotopy J N δφ
  poincare : IsKarEquiv (dualHom J (N + 1) (coneMap bd.p pD (comm_of_kar bd.p_idem pD_idem j_kar)))
    pD (relDuality δφ)

namespace SymPair

variable {J N} (X : SymPair J N)

attribute [reassoc (attr := simp)] pD_idem

/-- The Kar idempotent `p_C ⊕ p_D` of `Cone(j)`. -/
abbrev coneIdem : cone X.j ⟶ cone X.j :=
  coneMap X.bd.p X.pD (comm_of_kar X.bd.p_idem X.pD_idem X.j_kar)

/-- The relative duality map `Ψ` (l. 969). -/
abbrev Ψ : dualComplex J (N + 1) (cone X.j) ⟶ X.D := relDuality X.δφ

@[reassoc (attr := simp)]
lemma p_comp_j : X.bd.p ≫ X.j = X.j := by
  conv_lhs => rw [← X.j_kar]
  rw [X.bd.p_idem_assoc, X.j_kar]

@[reassoc (attr := simp)]
lemma j_comp_pD : X.j ≫ X.pD = X.j := by
  conv_lhs => rw [← X.j_kar]
  rw [assoc, assoc, X.pD_idem, X.j_kar]

lemma coneIdem_idem : X.coneIdem ≫ X.coneIdem = X.coneIdem :=
  coneMap_idem _ X.bd.p_idem X.pD_idem

lemma dualHom_coneIdem_idem :
    dualHom J (N + 1) X.coneIdem ≫ dualHom J (N + 1) X.coneIdem =
      dualHom J (N + 1) X.coneIdem := by
  rw [← dualHom_comp, X.coneIdem_idem]

lemma dualHom_pD_comp_δφ_hom (r r' : ℤ) :
    (dualHom J N X.pD).f r ≫ X.δφ.hom r r' = X.δφ.hom r r' := by
  conv_lhs => rw [← X.δφ_kar]
  rw [← assoc, ← comp_f, ← dualHom_comp, X.pD_idem, X.δφ_kar]

@[reassoc (attr := simp)]
lemma dualHom_coneIdem_comp_Ψ : dualHom J (N + 1) X.coneIdem ≫ X.Ψ = X.Ψ :=
  dualHom_coneMap_comp_relDuality _ _ X.bd.dualHom_p_comp_φ X.dualHom_pD_comp_δφ_hom

@[reassoc (attr := simp)]
lemma bdInc_comp_Ψ : bdInc X.j ≫ X.Ψ = -(X.bd.φ ≫ X.j) := bdInc_comp_relDuality _

lemma δφ_hom_comp_pD (r r' : ℤ) : X.δφ.hom r r' ≫ X.pD.f r' = X.δφ.hom r r' := by
  conv_lhs => rw [← X.δφ_kar]
  rw [assoc, assoc, ← comp_f, X.pD_idem, X.δφ_kar]

/-- `Ψ` is a Kar-morphism (target side). -/
@[reassoc (attr := simp)]
lemma Ψ_comp_pD : X.Ψ ≫ X.pD = X.Ψ := by
  have hj (i : ℤ) : X.j.f i ≫ X.pD.f i = X.j.f i := by rw [← comp_f, X.j_comp_pD]
  ext r
  simp [relTop, X.δφ_hom_comp_pD, hj]

/-- The relative top structure `δφ_r : D^{N+1-r} ⟶ D_r`. -/
abbrev top (r : ℤ) : X.D.X (N + 1 - r) ⟶ X.D.X r := relTop X.δφ r

/-- The relative cycle condition `δφ_r d = δ δφ_{r-1} + j φ_{r-1} j^*` (l. 966). -/
lemma top_comm (r r' : ℤ) (h : (ComplexShape.down ℤ).Rel r r') :
    X.top r ≫ X.D.d r r' = ((dualComplex J (N + 1) X.D).d r r' ≫ X.top r' :
      X.D.X (N + 1 - r) ⟶ X.D.X r') +
      (X.D.XIsoOfEq (by simp only [ComplexShape.down_Rel] at h; omega : N + 1 - r = N - r')).hom ≫
        (dualHom J N X.j ≫ X.bd.φ ≫ X.j).f r' :=
  relTop_comm X.δφ r r' h

/-- `-(C ⊂ D, (δφ, φ)) = (C ⊂ D, (-δφ, -φ))`, a pair with boundary `-∂`. -/
@[simps]
def neg : SymPair J N where
  bd := X.bd.neg
  D := X.D
  pD := X.pD
  pD_idem := X.pD_idem
  support := X.support
  j := X.j
  j_kar := X.j_kar
  δφ := homotopyCongr (X.δφ.smul (-1 : ℤ)) (by simp) (by simp)
  δφ_kar r r' := by
    change _ ≫ ((-1 : ℤ) • X.δφ.hom r r') ≫ _ = (-1 : ℤ) • X.δφ.hom r r'
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, X.δφ_kar]
  symm := by
    have := X.symm
    rw [IsSymmHomotopy, transposeHomotopy_hom] at this ⊢
    funext r r'
    simpa [transposeHomFamily] using congrFun (congrFun this r) r'
  poincare := X.poincare.neg.of_eq (by ext r; simp [relTop]; abel)

end SymPair

variable {J N}

/-- `P` is null-cobordant: it is the boundary of a Poincaré pair. -/
def NullCobordant (P : SymPoincare J N) : Prop :=
  ∃ X : SymPair J N, X.bd = P

/-- `P` and `Q` are cobordant: `P ⊕ -Q` (block sum along unitary bicones) bounds a Poincaré
pair. -/
def Cobordant (P Q : SymPoincare J N) : Prop :=
  ∃ b : ∀ r, UnitaryBicone J (P.C.X r) (Q.C.X r),
    NullCobordant (P.sum Q.neg fun r ↦ (b r).toBinaryBicone)

lemma NullCobordant.neg {P : SymPoincare J N} (h : NullCobordant P) : NullCobordant P.neg := by
  obtain ⟨X, rfl⟩ := h
  exact ⟨X.neg, rfl⟩

section Map

open homotopyCofiber

variable {W : Type u'} [Category.{v'} W] [Preadditive W] [HasBinaryBiproducts W]
  {J' : StrictInvolution W} (Φ : InvFunctor J J') {B D : ChainComplex V ℤ}

namespace InvFunctor

/-- The comparison `Cone(F j) ⟶ F(Cone j)`, an isomorphism (`F` preserves biproducts). -/
def coneComparison (j : B ⟶ D) : cone (Φ.mapH j) ⟶ Φ.mapC (cone j) :=
  desc (Φ.mapH j) (Φ.mapH (inr j))
    (homotopyCongr (Φ.F.mapHomotopy (inrCompHomotopy j down_exists_rel)) (Functor.map_comp _ _ _)
      (Functor.map_zero _ _ _))

variable (j : B ⟶ D)

@[reassoc (attr := simp)]
lemma inlX_coneComparison_f (i k : ℤ) (hk : (ComplexShape.down ℤ).Rel i k) :
    inlX (Φ.mapH j) k i hk ≫ (Φ.coneComparison j).f i = Φ.F.map (inlX j k i hk) := by
  simp [coneComparison, inlX_desc_f _ _ _ _ _ hk, inrCompHomotopy_hom _ _ _ _ hk]

@[reassoc (attr := simp)]
lemma inrX_coneComparison_f (i : ℤ) :
    inrX (Φ.mapH j) i ≫ (Φ.coneComparison j).f i = Φ.F.map (inrX j i) := by
  simp [coneComparison, inrX_desc_f]

instance (i : ℤ) : IsIso ((Φ.coneComparison j).f i) := by
  have hi : (ComplexShape.down ℤ).Rel i (i - 1) := by simp
  refine ⟨Φ.F.map (fstX j i (i - 1) hi) ≫ inlX (Φ.mapH j) (i - 1) i hi +
    Φ.F.map (sndX j i) ≫ inrX (Φ.mapH j) i, ?_, ?_⟩
  · apply ext_from_X (Φ.mapH j) (i - 1) i hi <;>
      simp [← Functor.map_comp_assoc]
  · simp only [add_comp, assoc, inlX_coneComparison_f, inrX_coneComparison_f,
      ← Functor.map_comp]
    rw [← Φ.F.map_add, ← cone.id_X j i (i - 1) hi]
    exact Φ.F.map_id _

instance : IsIso (Φ.coneComparison j) := HomologicalComplex.Hom.isIso_of_components _

@[reassoc]
lemma coneComparison_comp_map_coneMap {pB : B ⟶ B} {pD : D ⟶ D} (h : pB ≫ j = j ≫ pD) :
    Φ.coneComparison j ≫ Φ.mapH (coneMap pB pD h) =
      coneMap (Φ.mapH pB) (Φ.mapH pD) (by simp only [← Functor.map_comp, h]) ≫
        Φ.coneComparison j := by
  ext i
  apply ext_from_X (Φ.mapH j) (i - 1) i (by simp) <;>
    simp [← Functor.map_comp]

variable {φ : dualComplex J N B ⟶ B} {j}

/-- The image `F δφ` of a relative boundary. -/
def mapRel (H : Homotopy (dualHom J N j ≫ φ ≫ j) 0) :
    Homotopy (dualHom J' N (Φ.mapH j) ≫ Φ.mapDual φ ≫ Φ.mapH j) 0 :=
  homotopyCongr ((Φ.F.mapHomotopy H).compLeft (Φ.mapDualIso N D).inv)
    (by ext; simp [Φ.map_star]) (by simp)

omit [HasBinaryBiproducts V] [HasBinaryBiproducts W] in
@[simp]
lemma mapRel_hom (H : Homotopy (dualHom J N j ≫ φ ≫ j) 0) (r r' : ℤ) :
    (Φ.mapRel H).hom r r' = Φ.F.map (H.hom r r') := by
  simp [mapRel]

omit [HasBinaryBiproducts V] [HasBinaryBiproducts W] in
lemma relTop_mapRel (H : Homotopy (dualHom J N j ≫ φ ≫ j) 0) (r : ℤ) :
    relTop (Φ.mapRel H) r = Φ.F.map (relTop H r) := by
  simp [relTop, XIsoOfEq, eqToHom_map]

lemma dualHom_coneComparison_comp_relDuality (H : Homotopy (dualHom J N j ≫ φ ≫ j) 0) :
    dualHom J' (N + 1) (Φ.coneComparison j) ≫ relDuality (Φ.mapRel H) =
      Φ.mapDual (relDuality H) := by
  ext r
  have h₁ := congrArg J'.star (Φ.inrX_coneComparison_f j (N + 1 - r))
  have h₂ := congrArg J'.star (Φ.inlX_coneComparison_f j _ _ (down_rel_sub N r))
  simp only [J'.star_comp, ← Φ.map_star] at h₁ h₂
  simp [relTop_mapRel, reassoc_of% h₁, reassoc_of% h₂, Φ.map_star]

omit [HasBinaryBiproducts V] [HasBinaryBiproducts W] in
lemma transposeHomFamily_map {C : ChainComplex V ℤ}
    (h : ∀ i k, (dualComplex J N C).X i ⟶ C.X k) :
    transposeHomFamily J' N (C := Φ.mapC C) (D := Φ.mapC C) (fun r r' ↦ Φ.F.map (h r r')) =
      fun r r' ↦ Φ.F.map (transposeHomFamily J N h r r') := by
  funext r r'
  simp [transposeHomFamily, Φ.map_star, eqToHom_map]

end InvFunctor

namespace SymPair

/-- The image `F(C ⊂ D, (δφ, φ))` of a Poincaré pair under a duality-preserving functor. -/
@[simps]
def map (X : SymPair J N) : SymPair J' N where
  bd := X.bd.map Φ
  D := Φ.mapC X.D
  pD := Φ.mapH X.pD
  pD_idem := by rw [← Functor.map_comp, X.pD_idem]
  support r hr := by simp [X.support r hr]
  j := Φ.mapH X.j
  j_kar := by simp only [SymPoincare.map_p, ← Functor.map_comp, X.j_kar]
  δφ := Φ.mapRel X.δφ
  δφ_kar r r' := by
    simp only [InvFunctor.mapRel_hom, dualHom_f, InvFunctor.mapH,
      Functor.mapHomologicalComplex_map_f, ← Φ.map_star, ← Functor.map_comp]
    rw [← dualHom_f, X.δφ_kar]
  symm := by
    have e : (Φ.mapRel X.δφ).hom = fun r r' ↦ Φ.F.map (X.δφ.hom r r') :=
      funext₂ fun _ _ ↦ InvFunctor.mapRel_hom _ _ _ _
    have hs := X.symm
    rw [IsSymmHomotopy, transposeHomotopy_hom] at hs ⊢
    rw [e, Φ.transposeHomFamily_map, hs]
  poincare := by
    have h := (X.poincare.map Φ.F).conjIso (Φ.mapDualIso (N + 1) (cone X.j))
    rw [← Φ.dualHom_mapH, ← Φ.mapDual_eq,
      ← Φ.dualHom_coneComparison_comp_relDuality] at h
    have h' := h.conjIso (dualIso J' (N + 1) (asIso (Φ.coneComparison X.j)))
    simp only [dualIso_hom, dualIso_inv, asIso_hom, asIso_inv, ← assoc, ← dualHom_comp,
      IsIso.hom_inv_id, dualHom_id, id_comp] at h'
    convert h' using 2
    rw [assoc, Φ.coneComparison_comp_map_coneMap_assoc, IsIso.hom_inv_id, comp_id]

end SymPair

/-- Null-cobordant complexes map to null-cobordant complexes. -/
lemma NullCobordant.map {P : SymPoincare J N} (h : NullCobordant P) : NullCobordant (P.map Φ) := by
  obtain ⟨X, rfl⟩ := h
  exact ⟨X.map Φ, rfl⟩

end Map

end

end HSFormal.LTheory
