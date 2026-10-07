import HSFormal.Compression
import Mathlib.Algebra.Homology.Linear
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
# Strictly symmetric Poincaré complexes (L-theory module M1)

Ranicki's transposition `(Tφ)_r = (-1)^{r(N-r)} φ_{N-r}^*` (manuscript l. 245–253) on chain maps
`φ : C^{N-*} ⟶ D`, with the sign conventions of `Compression.lean`
(`δ_r = (-1)^r d^*_{N-r+1}`).  Strictly symmetric `N`-dimensional Poincaré complexes are encoded in
the Karoubi model of `blueprint/L-theory-design.md` §2.2: a complex `C` in `V` with a chain
idempotent `p` (an object of `Kar (ChainComplex V ℤ) ≌ ChainComplex (Kar V) ℤ`), a Kar-morphism
`φ : (C^{N-*}, p^*) ⟶ (C, p)` with `Tφ = φ`, which is a chain homotopy equivalence in `Kar V`.
Over `ℚ`, strict symmetry loses nothing (design §2.1, manuscript l. 266–275): symmetric
homotopies are obtained by averaging with the transpose (`symmHomotopy`).
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression

noncomputable section

universe v u

variable {V : Type u} [Category.{v} V] [Preadditive V] (J : StrictInvolution V) (N : ℤ)

section Lemmas

lemma negOnePow_eq_of_eq {a b : ℤ} (k : ℤ) (h : a = b + 2 * k) : a.negOnePow = b.negOnePow := by
  rw [h, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]

omit [Preadditive V] in
lemma eqToHom_naturality₂ {X Y : ℤ → V} (F : ∀ i j, X i ⟶ Y j) {a a' b b' : ℤ} (ha : a = a')
    (hb : b = b') : F a b ≫ eqToHom (congrArg Y hb) = eqToHom (congrArg X ha) ≫ F a' b' := by
  subst ha hb; simp

lemma f_comp_eqToHom {C D : ChainComplex V ℤ} (f : C ⟶ D) {a b : ℤ} (h : a = b) :
    f.f a ≫ eqToHom (congrArg D.X h) = eqToHom (congrArg C.X h) ≫ f.f b := by
  subst h; simp

lemma star_eqToHom {X Y : V} (h : X = Y) : J.star (eqToHom h) = eqToHom h.symm := by
  subst h; simp

lemma star_rat_smul [Linear ℚ V] {X Y : V} (q : ℚ) (f : X ⟶ Y) : J.star (q • f) = q • J.star f :=
  map_rat_smul (J.starHom X Y) q f

lemma units_smul_rat_smul [Linear ℚ V] {X Y : V} (u : ℤˣ) (q : ℚ) (f : X ⟶ Y) :
    u • q • f = q • u • f := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp

/-- Transport a homotopy along equalities of its endpoints, keeping `hom`. -/
@[simps]
def homotopyCongr {ι : Type*} {c : ComplexShape ι} {C D : HomologicalComplex V c}
    {f g f' g' : C ⟶ D} (H : Homotopy f g) (hf : f = f') (hg : g = g') : Homotopy f' g' where
  hom := H.hom
  zero := H.zero
  comm i := by subst hf hg; exact H.comm i

variable {C D : ChainComplex V ℤ}

@[simp]
lemma dualHom_add (f g : C ⟶ D) : dualHom J N (f + g) = dualHom J N f + dualHom J N g := by
  ext; simp [J.star_add]

@[simp]
lemma dualHom_zero : dualHom J N (0 : C ⟶ D) = 0 := by ext; simp

@[simp]
lemma dualHom_neg (f : C ⟶ D) : dualHom J N (-f) = -dualHom J N f := by ext; simp

@[simp]
lemma dualHom_smul [Linear ℚ V] (q : ℚ) (f : C ⟶ D) : dualHom J N (q • f) = q • dualHom J N f := by
  ext; simp [star_rat_smul]

end Lemmas

section Transpose

/-- The bidual chain isomorphism `C^{N-(N-*)} ≅ C`, multiplication by `ε_r = (-1)^{r(N-r)}` in
degree `r` (l. 251–253). -/
def bidual (C : ChainComplex V ℤ) : dualComplex J N (dualComplex J N C) ≅ C :=
  Hom.isoOfComponents
    (fun r ↦
      { hom := (r * (N - r)).negOnePow • eqToHom (congrArg C.X (sub_sub_cancel N r))
        inv := (r * (N - r)).negOnePow • eqToHom (congrArg C.X (sub_sub_cancel N r)).symm
        hom_inv_id := by simp [smul_smul]
        inv_hom_id := by simp [smul_smul] })
    (fun r r' h ↦ by
      obtain rfl : r = r' + 1 := by simp at h; omega
      simp only [dualComplex_d, J.star_units_smul, J.star_star, Linear.units_smul_comp,
        Linear.comp_units_smul, smul_smul]
      rw [eqToHom_naturality₂ C.d (sub_sub_cancel N (r' + 1)) (sub_sub_cancel N r')]
      congr 1
      rw [← Int.negOnePow_add, ← Int.negOnePow_add]
      exact negOnePow_eq_of_eq (-(r' + 1)) (by ring))

@[simp]
lemma bidual_hom_f (C : ChainComplex V ℤ) (r : ℤ) :
    (bidual J N C).hom.f r =
      (r * (N - r)).negOnePow • eqToHom (congrArg C.X (sub_sub_cancel N r)) := rfl

@[simp]
lemma bidual_inv_f (C : ChainComplex V ℤ) (r : ℤ) :
    (bidual J N C).inv.f r =
      (r * (N - r)).negOnePow • eqToHom (congrArg C.X (sub_sub_cancel N r)).symm := rfl

/-- Naturality of the bidual isomorphism. -/
@[reassoc]
lemma dualHom_dualHom_comp_bidual_hom {C D : ChainComplex V ℤ} (f : C ⟶ D) :
    dualHom J N (dualHom J N f) ≫ (bidual J N D).hom = (bidual J N C).hom ≫ f := by
  ext r
  simp only [comp_f, dualHom_f, J.star_star, bidual_hom_f, Linear.comp_units_smul,
    Linear.units_smul_comp]
  rw [f_comp_eqToHom f (sub_sub_cancel N r)]

/-- The triangle identity `ε_r ε_{N-r} = 1` of the bidual isomorphism. -/
@[reassoc (attr := simp)]
lemma dualHom_bidual_hom_comp_bidual_hom (C : ChainComplex V ℤ) :
    dualHom J N (bidual J N C).hom ≫ (bidual J N (dualComplex J N C)).hom = 𝟙 _ := by
  ext r
  simp only [comp_f, dualHom_f, bidual_hom_f, J.star_units_smul, star_eqToHom,
    Linear.units_smul_comp, Linear.comp_units_smul, eqToHom_trans, smul_smul, id_f]
  rw [← Int.negOnePow_add, show r * (N - r) + (N - r) * (N - (N - r)) = 2 * (r * (N - r)) by ring,
    Int.negOnePow_two_mul, one_smul, eqToHom_refl]

@[reassoc]
lemma dualHom_bidual_hom_f_comp_bidual_hom_f (C : ChainComplex V ℤ) (r : ℤ) :
    (dualHom J N (bidual J N C).hom).f r ≫ (bidual J N (dualComplex J N C)).hom.f r = 𝟙 _ := by
  rw [← comp_f, dualHom_bidual_hom_comp_bidual_hom, id_f]

/-- Ranicki's transposition of `φ : C^{N-*} ⟶ D`: `Tφ = φ^{N-*} ≫ ε : D^{N-*} ⟶ C`, i.e.
`(Tφ)_r = (-1)^{r(N-r)} φ_{N-r}^*` (l. 247). -/
def transposeHom {C D : ChainComplex V ℤ} (φ : dualComplex J N C ⟶ D) : dualComplex J N D ⟶ C :=
  dualHom J N φ ≫ (bidual J N C).hom

variable {J N} {C D : ChainComplex V ℤ}

lemma transposeHom_f (φ : dualComplex J N C ⟶ D) (r : ℤ) :
    (transposeHom J N φ).f r = (r * (N - r)).negOnePow •
      (J.star (φ.f (N - r)) ≫ eqToHom (congrArg C.X (sub_sub_cancel N r))) := by
  simp [transposeHom]

lemma transposeHom_f_eq_transposeFamily (φ : dualComplex J N C ⟶ C) (r : ℤ) :
    (transposeHom J N φ).f r = transposeFamily J N C.X (fun s ↦ φ.f s) r :=
  transposeHom_f φ r

/-- `T² = 1` (l. 253). -/
@[simp]
lemma transposeHom_transposeHom (φ : dualComplex J N C ⟶ D) :
    transposeHom J N (transposeHom J N φ) = φ := by
  simp only [transposeHom, dualHom_comp, assoc, dualHom_dualHom_comp_bidual_hom,
    dualHom_bidual_hom_comp_bidual_hom_assoc]

lemma transposeHom_injective : Function.Injective (transposeHom J N : (dualComplex J N C ⟶ D) → _) :=
  fun φ φ' h ↦ by rw [← transposeHom_transposeHom φ, h, transposeHom_transposeHom]

/-- `T(a^* φ g) = g^* (Tφ) a`. -/
lemma transposeHom_comp {C' D' : ChainComplex V ℤ} (a : C ⟶ C') (φ : dualComplex J N C ⟶ D)
    (g : D ⟶ D') :
    transposeHom J N (dualHom J N a ≫ φ ≫ g) = dualHom J N g ≫ transposeHom J N φ ≫ a := by
  simp only [transposeHom, dualHom_comp, assoc, dualHom_dualHom_comp_bidual_hom]

/-- `T(f φ f^*) = f (Tφ) f^*` (l. 253), diagrammatically. -/
lemma transposeHom_conj {C' : ChainComplex V ℤ} (f : C ⟶ C') (φ : dualComplex J N C ⟶ C) :
    transposeHom J N (dualHom J N f ≫ φ ≫ f) = dualHom J N f ≫ transposeHom J N φ ≫ f :=
  transposeHom_comp f φ f

@[simp]
lemma transposeHom_add (φ φ' : dualComplex J N C ⟶ D) :
    transposeHom J N (φ + φ') = transposeHom J N φ + transposeHom J N φ' := by
  simp [transposeHom]

@[simp]
lemma transposeHom_neg (φ : dualComplex J N C ⟶ D) :
    transposeHom J N (-φ) = -transposeHom J N φ := by
  simp [transposeHom]

@[simp]
lemma transposeHom_zero : transposeHom J N (0 : dualComplex J N C ⟶ D) = 0 := by
  simp [transposeHom]

@[simp]
lemma transposeHom_smul [Linear ℚ V] (q : ℚ) (φ : dualComplex J N C ⟶ D) :
    transposeHom J N (q • φ) = q • transposeHom J N φ := by
  simp [transposeHom]

variable (J N) in
/-- Strict symmetry `Tφ = φ` (l. 253). -/
def IsStrictSymm (φ : dualComplex J N C ⟶ C) : Prop :=
  transposeHom J N φ = φ

lemma IsStrictSymm.conj {C' : ChainComplex V ℤ} {φ : dualComplex J N C ⟶ C}
    (h : IsStrictSymm J N φ) (f : C ⟶ C') : IsStrictSymm J N (dualHom J N f ≫ φ ≫ f) := by
  rw [IsStrictSymm, transposeHom_conj, h]

lemma IsStrictSymm.add {φ φ' : dualComplex J N C ⟶ C} (h : IsStrictSymm J N φ)
    (h' : IsStrictSymm J N φ') : IsStrictSymm J N (φ + φ') := by
  rw [IsStrictSymm, transposeHom_add, h, h']

lemma IsStrictSymm.neg {φ : dualComplex J N C ⟶ C} (h : IsStrictSymm J N φ) :
    IsStrictSymm J N (-φ) := by
  rw [IsStrictSymm, transposeHom_neg, h]

variable (J N) in
/-- The symmetrization `(φ + Tφ)/2` (l. 271). -/
def symmetrize [Linear ℚ V] (φ : dualComplex J N C ⟶ C) : dualComplex J N C ⟶ C :=
  (1 / 2 : ℚ) • (φ + transposeHom J N φ)

lemma isStrictSymm_symmetrize [Linear ℚ V] (φ : dualComplex J N C ⟶ C) :
    IsStrictSymm J N (symmetrize J N φ) := by
  simp [IsStrictSymm, symmetrize, add_comm]

lemma IsStrictSymm.symmetrize_eq [Linear ℚ V] {φ : dualComplex J N C ⟶ C}
    (h : IsStrictSymm J N φ) : symmetrize J N φ = φ := by
  rw [symmetrize, show transposeHom J N φ = φ from h, ← two_smul ℚ φ, smul_smul]; norm_num

end Transpose

section HomotopyTranspose

variable {J N} {C D : ChainComplex V ℤ}

variable (J N) in
/-- Ranicki's `T` on degree-`(N+1)` elements of the Hom complex `M(C)` (l. 262–266):
`(Th)_{r,r'} = (-1)^{r+1} ε_{r'} h_{N-r',N-r}^*`; for `r' = r+1` the sign is `(-1)^{r'(N+1-r')}`. -/
def transposeHomFamily (h : ∀ i j, (dualComplex J N C).X i ⟶ D.X j) :
    ∀ i j, (dualComplex J N D).X i ⟶ C.X j :=
  fun r r' ↦ (r + 1).negOnePow • J.star (h (N - r') (N - r)) ≫ (bidual J N C).hom.f r'

variable (J N) in
/-- The transpose of a homotopy `φ ≃ φ'` is a homotopy `Tφ ≃ Tφ'`. -/
def transposeHomotopy {φ φ' : dualComplex J N C ⟶ D} (H : Homotopy φ φ') :
    Homotopy (transposeHom J N φ) (transposeHom J N φ') :=
  (dualHomotopy J N H).compRight (bidual J N C).hom

lemma transposeHomotopy_hom {φ φ' : dualComplex J N C ⟶ D} (H : Homotopy φ φ') :
    (transposeHomotopy J N H).hom = transposeHomFamily J N H.hom := by
  funext r r'
  simp [transposeHomotopy, transposeHomFamily, smul_smul, mul_comm]

lemma dualHomotopy_compRight_hom {E : ChainComplex V ℤ} {f g : C ⟶ D} (H : Homotopy f g)
    (e : D ⟶ E) (r r' : ℤ) :
    (dualHomotopy J N (H.compRight e)).hom r r' =
      (dualHom J N e).f r ≫ (dualHomotopy J N H).hom r r' := by
  simp [J.star_comp]

/-- Naturality of the bidual isomorphism for homotopies. -/
lemma dualHomotopy_dualHomotopy_hom_comp {f g : C ⟶ D} (H : Homotopy f g) (r r' : ℤ) :
    (dualHomotopy J N (dualHomotopy J N H)).hom r r' ≫ (bidual J N D).hom.f r' =
      (bidual J N C).hom.f r ≫ H.hom r r' := by
  simp only [dualHomotopy_hom, J.star_units_smul, J.star_star, bidual_hom_f,
    Linear.units_smul_comp, Linear.comp_units_smul, smul_smul]
  rw [eqToHom_naturality₂ H.hom (sub_sub_cancel N r) (sub_sub_cancel N r')]
  by_cases h : r' = r + 1
  · subst h
    congr 1
    rw [← Int.negOnePow_add, ← Int.negOnePow_add]
    exact negOnePow_eq_of_eq (N - r) (by ring)
  · rw [H.zero r r' (by simp; omega), comp_zero, smul_zero, smul_zero]

/-- `T² = 1` on homotopies. -/
@[simp]
lemma transposeHomotopy_transposeHomotopy_hom {φ φ' : dualComplex J N C ⟶ D}
    (H : Homotopy φ φ') : (transposeHomotopy J N (transposeHomotopy J N H)).hom = H.hom := by
  funext r r'
  simp only [transposeHomotopy, Homotopy.compRight_hom]
  erw [dualHomotopy_compRight_hom]
  simp only [assoc, dualHomotopy_dualHomotopy_hom_comp,
    dualHom_bidual_hom_f_comp_bidual_hom_f_assoc]

lemma transposeHomFamily_transposeHomFamily {φ φ' : dualComplex J N C ⟶ D} (H : Homotopy φ φ') :
    transposeHomFamily J N (transposeHomFamily J N H.hom) = H.hom := by
  rw [← transposeHomotopy_hom, ← transposeHomotopy_hom, transposeHomotopy_transposeHomotopy_hom]

lemma transposeHomFamily_add (h h' : ∀ i j, (dualComplex J N C).X i ⟶ D.X j) :
    transposeHomFamily J N (h + h') = transposeHomFamily J N h + transposeHomFamily J N h' := by
  funext r r'
  simp [transposeHomFamily, J.star_add]

lemma transposeHomFamily_smul [Linear ℚ V] (q : ℚ) (h : ∀ i j, (dualComplex J N C).X i ⟶ D.X j) :
    transposeHomFamily J N (q • h) = q • transposeHomFamily J N h := by
  funext r r'
  simp [transposeHomFamily, star_rat_smul, units_smul_rat_smul]

variable (J N) in
/-- A homotopy between maps `C^{N-*} ⟶ C` is symmetric if it is `T`-invariant, i.e. an element
of `M(C)^{ℤ/2}_{N+1}`. -/
def IsSymmHomotopy {φ φ' : dualComplex J N C ⟶ C} (H : Homotopy φ φ') : Prop :=
  (transposeHomotopy J N H).hom = H.hom

variable [Linear ℚ V]

/-- Averaging a homotopy between strict structures with its transpose (design §2.1 (iii); l. 272:
"an invariant boundary has an invariant primitive obtained by averaging any primitive"). -/
def symmHomotopy {φ φ' : dualComplex J N C ⟶ C} (hφ : IsStrictSymm J N φ)
    (hφ' : IsStrictSymm J N φ') (H : Homotopy φ φ') : Homotopy φ φ' :=
  homotopyCongr ((H.add (transposeHomotopy J N H)).smul (1 / 2 : ℚ))
    (by rw [show transposeHom J N φ = φ from hφ, ← two_smul ℚ φ, smul_smul]; norm_num)
    (by rw [show transposeHom J N φ' = φ' from hφ', ← two_smul ℚ φ', smul_smul]; norm_num)

lemma symmHomotopy_hom {φ φ' : dualComplex J N C ⟶ C} (hφ : IsStrictSymm J N φ)
    (hφ' : IsStrictSymm J N φ') (H : Homotopy φ φ') :
    (symmHomotopy hφ hφ' H).hom = (1 / 2 : ℚ) • (H.hom + transposeHomFamily J N H.hom) := by
  funext r r'
  simp [symmHomotopy, transposeHomotopy_hom]

lemma isSymmHomotopy_symmHomotopy {φ φ' : dualComplex J N C ⟶ C} (hφ : IsStrictSymm J N φ)
    (hφ' : IsStrictSymm J N φ') (H : Homotopy φ φ') :
    IsSymmHomotopy J N (symmHomotopy hφ hφ' H) := by
  rw [IsSymmHomotopy, transposeHomotopy_hom, symmHomotopy_hom, transposeHomFamily_smul,
    transposeHomFamily_add, transposeHomFamily_transposeHomFamily, add_comm]

/-- Over `ℚ`, homotopic strict structures are homotopic through a symmetric homotopy
([Ran80I, Prop. 3.3]; design §2.1). -/
theorem exists_symm_homotopy {φ φ' : dualComplex J N C ⟶ C} (hφ : IsStrictSymm J N φ)
    (hφ' : IsStrictSymm J N φ') (H : Homotopy φ φ') :
    ∃ H' : Homotopy φ φ', IsSymmHomotopy J N H' :=
  ⟨_, isSymmHomotopy_symmHomotopy hφ hφ' H⟩

/-- If `φ ≃ Tφ` (a symmetric structure with `φ_1 = H`), then `φ ≃ (φ + Tφ)/2`
(design §2.1 (i)). -/
def homotopySymmetrize {φ : dualComplex J N C ⟶ C} (H : Homotopy φ (transposeHom J N φ)) :
    Homotopy φ (symmetrize J N φ) :=
  homotopyCongr (((Homotopy.refl φ).add H).smul (1 / 2 : ℚ))
    (by rw [← two_smul ℚ φ, smul_smul]; norm_num) rfl

end HomotopyTranspose

section Kar

variable {J N} {C D : ChainComplex V ℤ}

/-- The Kar complex `(C, p)` is concentrated in degrees `[lo, hi]`. -/
def SupportedIn (p : C ⟶ C) (lo hi : ℤ) : Prop :=
  ∀ r, r < lo ∨ hi < r → p.f r = 0

lemma SupportedIn.mono {p : C ⟶ C} {lo hi lo' hi' : ℤ} (h : SupportedIn p lo hi) (hlo : lo' ≤ lo)
    (hhi : hi ≤ hi') : SupportedIn p lo' hi' :=
  fun r hr ↦ h r (by omega)

lemma SupportedIn.dualHom {p : C ⟶ C} {lo hi : ℤ} (h : SupportedIn p lo hi) :
    SupportedIn (dualHom J N p) (N - hi) (N - lo) :=
  fun r hr ↦ by rw [dualHom_f, h (N - r) (by omega), J.star_zero]

/-- A Kar-morphism out of a complex supported in `[lo, hi]` vanishes outside `[lo, hi]`. -/
lemma SupportedIn.f_eq_zero {p : C ⟶ C} {lo hi : ℤ} (h : SupportedIn p lo hi) {f : C ⟶ D}
    (hf : p ≫ f = f) (r : ℤ) (hr : r < lo ∨ hi < r) : f.f r = 0 := by
  rw [← hf, comp_f, h r hr, zero_comp]

/-- A Kar-morphism into a complex supported in `[lo, hi]` vanishes outside `[lo, hi]`. -/
lemma SupportedIn.f_eq_zero' {q : D ⟶ D} {lo hi : ℤ} (h : SupportedIn q lo hi) {f : C ⟶ D}
    (hf : f ≫ q = f) (r : ℤ) (hr : r < lo ∨ hi < r) : f.f r = 0 := by
  rw [← hf, comp_f, h r hr, comp_zero]

/-- A homotopy between Kar-morphisms `(C, p) ⟶ (D, q)` compresses to the Kar-homotopy `pHq`
(design §2.2: no compression defect, since `p` and `q` commute with `d`). -/
@[simps!]
def karHomotopy {p : C ⟶ C} {q : D ⟶ D} {f g : C ⟶ D} (H : Homotopy f g)
    (hf : p ≫ f ≫ q = f) (hg : p ≫ g ≫ q = g) : Homotopy f g :=
  homotopyCongr ((H.compRight q).compLeft p) hf hg

variable (J N) in
/-- `φ : (C^{N-*}, p^*) ⟶ (C, p)` is a chain homotopy equivalence in `Kar V`.  Homotopies are
taken in `V`: since `p` commutes with `d`, `pHp` is then a homotopy in `Kar V` (design §2.2). -/
def IsPoincare (p : C ⟶ C) (φ : dualComplex J N C ⟶ C) : Prop :=
  ∃ ψ : C ⟶ dualComplex J N C, p ≫ ψ ≫ dualHom J N p = ψ ∧
    Nonempty (Homotopy (ψ ≫ φ) p) ∧ Nonempty (Homotopy (φ ≫ ψ) (dualHom J N p))

lemma IsPoincare.of_homotopy {p : C ⟶ C} {φ φ' : dualComplex J N C ⟶ C}
    (h : IsPoincare J N p φ) (H : Homotopy φ φ') : IsPoincare J N p φ' := by
  obtain ⟨ψ, hψ, ⟨H₁⟩, ⟨H₂⟩⟩ := h
  exact ⟨ψ, hψ, ⟨((Homotopy.refl ψ).comp H).symm.trans H₁⟩,
    ⟨(H.comp (Homotopy.refl ψ)).symm.trans H₂⟩⟩

lemma IsPoincare.neg {p : C ⟶ C} {φ : dualComplex J N C ⟶ C} (h : IsPoincare J N p φ) :
    IsPoincare J N p (-φ) := by
  obtain ⟨ψ, hψ, ⟨H₁⟩, ⟨H₂⟩⟩ := h
  exact ⟨-ψ, by simp [hψ], ⟨homotopyCongr H₁ (by simp) rfl⟩, ⟨homotopyCongr H₂ (by simp) rfl⟩⟩

variable (J N) in
/-- An `N`-dimensional strictly symmetric Poincaré complex in `Kar V` (design §2.2, M1): the Kar
complex `(C, p)` is concentrated in `[0, N]`, `φ : (C^{N-*}, p^*) ⟶ (C, p)` is a Kar chain map
with `Tφ = φ` (the symmetric structure `(φ, 0, 0, …)`), and `φ` is a homotopy equivalence. -/
structure SymPoincare where
  C : ChainComplex V ℤ
  p : C ⟶ C
  p_idem : p ≫ p = p
  support : SupportedIn p 0 N
  φ : dualComplex J N C ⟶ C
  φ_kar : dualHom J N p ≫ φ ≫ p = φ
  symm : IsStrictSymm J N φ
  poincare : IsPoincare J N p φ

namespace SymPoincare

attribute [reassoc (attr := simp)] p_idem

variable (P Q : SymPoincare J N)

@[reassoc (attr := simp)]
lemma φ_comp_p : P.φ ≫ P.p = P.φ := by
  rw [← P.φ_kar]; simp

@[reassoc (attr := simp)]
lemma dualHom_p_comp_φ : dualHom J N P.p ≫ P.φ = P.φ := by
  conv_lhs => rw [← P.φ_kar]
  rw [← assoc, ← dualHom_comp, P.p_idem, P.φ_kar]

@[simp]
lemma transposeHom_φ : transposeHom J N P.φ = P.φ := P.symm

/-- `-(C, φ) = (C, -φ)`. -/
@[simps, reducible]
def neg : SymPoincare J N where
  C := P.C
  p := P.p
  p_idem := P.p_idem
  support := P.support
  φ := -P.φ
  φ_kar := by simp
  symm := P.symm.neg
  poincare := P.poincare.neg

@[simp]
lemma neg_neg : P.neg.neg = P := by
  cases P; simp only [neg]; congr 1; exact _root_.neg_neg _

/-- Replace a Kar-compatible Poincaré map `φ` with `φ ≃ Tφ` by its symmetrization
`(φ + Tφ)/2` (design §2.1 (i)). -/
@[simps]
def ofHomotopySymm [Linear ℚ V] (C : ChainComplex V ℤ) (p : C ⟶ C) (p_idem : p ≫ p = p)
    (support : SupportedIn p 0 N) (φ : dualComplex J N C ⟶ C) (φ_kar : dualHom J N p ≫ φ ≫ p = φ)
    (H : Homotopy φ (transposeHom J N φ)) (poincare : IsPoincare J N p φ) : SymPoincare J N where
  C := C
  p := p
  p_idem := p_idem
  support := support
  φ := symmetrize J N φ
  φ_kar := by
    have := transposeHom_comp p φ p
    rw [φ_kar] at this
    simp only [symmetrize, Linear.comp_smul, Linear.smul_comp, comp_add, add_comp, φ_kar,
      ← this]
  symm := isStrictSymm_symmetrize φ
  poincare := poincare.of_homotopy (homotopySymmetrize H)

end SymPoincare

end Kar

section Sum

variable {C D : ChainComplex V ℤ} (b : ∀ r, BinaryBicone (C.X r) (D.X r))

/-- The degreewise direct sum of two complexes along chosen binary bicones. -/
@[simps, reducible]
def sumComplex : ChainComplex V ℤ where
  X r := (b r).pt
  d r r' := (b r).fst ≫ C.d r r' ≫ (b r').inl + (b r).snd ≫ D.d r r' ≫ (b r').inr
  shape r r' h := by simp [C.shape r r' h, D.shape r r' h]
  d_comp_d' r r' r'' _ _ := by simp

/-- The inclusion of the first summand. -/
@[simps]
def sumInl : C ⟶ sumComplex b where
  f r := (b r).inl

/-- The inclusion of the second summand. -/
@[simps]
def sumInr : D ⟶ sumComplex b where
  f r := (b r).inr

/-- The projection to the first summand. -/
@[simps]
def sumFst : sumComplex b ⟶ C where
  f r := (b r).fst

/-- The projection to the second summand. -/
@[simps]
def sumSnd : sumComplex b ⟶ D where
  f r := (b r).snd

@[reassoc (attr := simp)]
lemma sumInl_sumFst : sumInl b ≫ sumFst b = 𝟙 C := by ext; simp

@[reassoc (attr := simp)]
lemma sumInl_sumSnd : sumInl b ≫ sumSnd b = 0 := by ext; simp

@[reassoc (attr := simp)]
lemma sumInr_sumFst : sumInr b ≫ sumFst b = 0 := by ext; simp

@[reassoc (attr := simp)]
lemma sumInr_sumSnd : sumInr b ≫ sumSnd b = 𝟙 D := by ext; simp

@[reassoc (attr := simp)]
lemma dualHom_sumFst_dualHom_sumInl : dualHom J N (sumFst b) ≫ dualHom J N (sumInl b) = 𝟙 _ := by
  rw [← dualHom_comp, sumInl_sumFst, dualHom_id]

@[reassoc (attr := simp)]
lemma dualHom_sumSnd_dualHom_sumInl : dualHom J N (sumSnd b) ≫ dualHom J N (sumInl b) = 0 := by
  rw [← dualHom_comp, sumInl_sumSnd, dualHom_zero]

@[reassoc (attr := simp)]
lemma dualHom_sumFst_dualHom_sumInr : dualHom J N (sumFst b) ≫ dualHom J N (sumInr b) = 0 := by
  rw [← dualHom_comp, sumInr_sumFst, dualHom_zero]

@[reassoc (attr := simp)]
lemma dualHom_sumSnd_dualHom_sumInr : dualHom J N (sumSnd b) ≫ dualHom J N (sumInr b) = 𝟙 _ := by
  rw [← dualHom_comp, sumInr_sumSnd, dualHom_id]

end Sum

/-- A bilimit binary bicone whose inclusions are the duals of its projections. -/
structure UnitaryBicone (X Y : V) extends BinaryBicone X Y where
  isBilimit : toBinaryBicone.IsBilimit
  star_inl : J.star inl = fst
  star_inr : J.star inr = snd

namespace SymPoincare

variable {J N}

/-- The direct sum `(C ⊕ C', φ ⊕ φ')` along degreewise bicones `b`; its structure is
`inl^* φ inl + inr^* φ' inr`, which for unitary bicones is the block matrix
`fst φ inl + snd φ' inr` (`sum_φ_f_of_unitary`). -/
@[simps, reducible]
def sum (P Q : SymPoincare J N) (b : ∀ r, BinaryBicone (P.C.X r) (Q.C.X r)) :
    SymPoincare J N where
  C := sumComplex b
  p := sumFst b ≫ P.p ≫ sumInl b + sumSnd b ≫ Q.p ≫ sumInr b
  p_idem := by simp
  support r hr := by simp [P.support r hr, Q.support r hr]
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

lemma sum_φ_f_of_unitary (P Q : SymPoincare J N) (b : ∀ r, UnitaryBicone J (P.C.X r) (Q.C.X r))
    (r : ℤ) :
    (sum P Q fun r ↦ (b r).toBinaryBicone).φ.f r =
      (b (N - r)).fst ≫ P.φ.f r ≫ (b r).inl + (b (N - r)).snd ≫ Q.φ.f r ≫ (b r).inr := by
  simp [sum, (b _).star_inl, (b _).star_inr]

end SymPoincare

end

end HSFormal.LTheory
