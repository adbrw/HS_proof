import HSFormal.LTheory.Cylinder
import HSFormal.LTheory.KaroubiFiltration

/-!
# Pairs with boundary in `U` become closed in `A/U`; excision (L-theory module M3)

* `SymPair.closedOfIsZero`: a Poincaré pair whose boundary objects vanish is a closed
  `(N+1)`-dimensional Poincaré complex `(D, p_D, δφ)`; `relTop_transpose` is `T δφ = δφ` in
  dimension `N + 1`.
* `SymPair.toClosed Φ`: the same after a duality-preserving functor `Φ` killing the boundary;
  `SymPair.toQuot F` for `Φ = A ⟶ A/U` ("a pair with boundary in `U` becomes closed in `A/U`",
  l. 217–237, the representative of H2) and `SymPair.bdLift F` (the boundary in `U`), with
  naturality under maps of filtrations (`toQuot_map`, `bdLift_map`).
* **R3** `isometric_toClosed`/`isometric_toQuot`(`_of_split`): a map `D ⟶ P` from the top of a
  pair into a closed complex which is an equivalence modulo `U` and preserves the structure
  modulo `U` is a homotopy isometry in `A/U`.

**Decision on unions.** The union `𝒰 = V_A ∪_P V_B` of l. 1045–1071 and its collapse
comparison l. 1059–1080 are *not* formalized: on the cubical route (simplicial-design F29, C8)
Lemma 4.1 is applied to the closed manifold complex `W` itself, whose image in `𝒬/𝒜_B` is
identified with the `A`-pair representative by R3, after which H2 computes the boundary.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression

noncomputable section

universe v v' u u'

variable {V : Type u} [Category.{v} V] [Preadditive V] {J : StrictInvolution V} {N : ℤ}

section RelTopSymm

variable {B D : ChainComplex V ℤ} {j : B ⟶ D} {φ : dualComplex J N B ⟶ B}

@[reassoc]
lemma eqToHom_comp_star_homotopy_hom {X Y : ChainComplex V ℤ} {f g : X ⟶ Y} (H : Homotopy f g)
    (a b b' : ℤ) (h : b = b') :
    eqToHom (congrArg Y.X h) ≫ J.star (H.hom a b') = J.star (H.hom a b) := by
  subst h; simp

/-- A symmetric relative boundary gives a strictly symmetric top structure in dimension `N + 1`:
`T δφ = δφ` (Ranicki's `T` in dimension `N + 1`). -/
lemma relTop_transpose (H : Homotopy (dualHom J N j ≫ φ ≫ j) 0) (hH : IsSymmHomotopy J N H)
    (r : ℤ) : (r * (N + 1 - r)).negOnePow •
      (J.star (relTop H (N + 1 - r)) ≫ eqToHom (congrArg D.X (sub_sub_cancel (N + 1) r))) =
      relTop H r := by
  rw [IsSymmHomotopy, transposeHomotopy_hom] at hH
  have h := congrFun (congrFun hH (r - 1)) r
  rw [relTop_eq H (N - r) (N + 1 - r) (by omega), relTop, ← h]
  simp only [transposeHomFamily, bidual_hom_f, J.star_comp, XIsoOfEq, eqToIso.hom, star_eqToHom,
    Linear.comp_units_smul, smul_smul, assoc, eqToHom_trans]
  rw [eqToHom_comp_star_homotopy_hom_assoc H _ _ _ (by omega : N + 1 - r = N - (r - 1)),
    ← Int.negOnePow_add]
  congr 1
  exact negOnePow_eq_of_eq 0 (by ring)

end RelTopSymm

namespace SymPair

open homotopyCofiber

variable [HasBinaryBiproducts V] (X : SymPair J N)

section IsZero

variable (hZ : ∀ r, IsZero (X.bd.C.X r))
include hZ

lemma j_f_eq_zero (r : ℤ) : X.j.f r = 0 := (hZ r).eq_of_src _ _

/-- With vanishing boundary, the relative top `δφ` is a chain map `D^{N+1-*} ⟶ D` (l. 966). -/
@[simps]
def topHom : dualComplex J (N + 1) X.D ⟶ X.D where
  f r := X.top r
  comm' r r' h := by simp [X.top_comm r r' h, X.j_f_eq_zero hZ]

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
    inr X.j ≫ X.coneIdem ≫ X.coneSnd hZ = X.pD := by
  ext; simp

/-- **A pair whose boundary vanishes is closed**: the top `(D, p_D, δφ)` is an
`(N+1)`-dimensional strictly symmetric Poincaré complex, since `Ψ = δφ ∘ inr^*` with
`inr : D ≅ Cone(j)`. -/
@[simps]
def closedOfIsZero : SymPoincare J (N + 1) where
  C := X.D
  p := X.pD
  p_idem := X.pD_idem
  support := X.support
  φ := X.topHom hZ
  φ_kar := by
    ext r
    simp only [comp_f, dualHom_f, topHom_f, top]
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

end IsZero

end SymPair

/-- Poincaré complexes with the same underlying Kar complex and structure are equal. -/
lemma SymPoincare.ext_of_φ {P Q : SymPoincare J N} (hC : P.C = Q.C) (hp : HEq P.p Q.p)
    (hφ : HEq P.φ Q.φ) : P = Q := by
  cases P; cases Q; cases hC; cases hp; cases hφ; rfl

/-- An isomorphism is a Kar equivalence between the identity idempotents. -/
lemma IsKarEquiv.of_isIso {X Y : ChainComplex V ℤ} (f : X ⟶ Y) [IsIso f] :
    IsKarEquiv (𝟙 X) (𝟙 Y) f :=
  ⟨inv f, by simp, ⟨Homotopy.ofEq (by simp)⟩, ⟨Homotopy.ofEq (by simp)⟩⟩

section ToClosed

variable [HasBinaryBiproducts V] {W : Type u'} [Category.{v'} W] [Preadditive W]
  [HasBinaryBiproducts W] {J' : StrictInvolution W}

namespace SymPair

variable (X : SymPair J N) (Φ : InvFunctor J J') (hZ : ∀ r, IsZero (Φ.F.obj (X.bd.C.X r)))

/-- **A pair whose boundary is killed by `Φ` becomes closed** (l. 230: "P has become zero"):
the image `(Φ D, Φ p_D, Φ δφ)` of the top is an `(N+1)`-dimensional Poincaré complex. -/
abbrev toClosed : SymPoincare J' (N + 1) := (X.map Φ).closedOfIsZero hZ

@[simp]
lemma map_top (r : ℤ) : (X.map Φ).top r = Φ.F.map (X.top r) :=
  InvFunctor.relTop_mapRel Φ X.δφ r

include hZ in
lemma toClosed_φ_f (r : ℤ) : (X.toClosed Φ hZ).φ.f r = Φ.F.map (X.top r) :=
  X.map_top Φ r

/-- `toClosed` is natural in the functor. -/
theorem toClosed_map {W' : Type*} [Category W'] [Preadditive W'] [HasBinaryBiproducts W']
    {J'' : StrictInvolution W'} (Ψ : InvFunctor J' J'')
    (hZ' : ∀ r, IsZero ((Φ.comp Ψ).F.obj (X.bd.C.X r))) :
    (X.toClosed Φ hZ).map Ψ = X.toClosed (Φ.comp Ψ) hZ' := by
  refine SymPoincare.ext_of_φ rfl HEq.rfl (heq_of_eq ?_)
  ext r
  simp only [SymPoincare.map_φ, InvFunctor.mapDual_f, toClosed_φ_f]
  rfl

/-- `toClosed` of a composite functor. -/
theorem toClosed_comp {W' : Type*} [Category W'] [Preadditive W'] [HasBinaryBiproducts W']
    {J'' : StrictInvolution W'} (Ψ : InvFunctor J' J'')
    (hZ' : ∀ r, IsZero ((Φ.comp Ψ).F.obj (X.bd.C.X r))) :
    X.toClosed (Φ.comp Ψ) hZ' = (X.map Φ).toClosed Ψ hZ' := by
  refine SymPoincare.ext_of_φ rfl HEq.rfl (heq_of_eq ?_)
  ext r
  erw [toClosed_φ_f, toClosed_φ_f, map_top]
  rfl

/-- **Excision isometry (R3)**, replacing the union of l. 1045–1080: if `i : D ⟶ P` from the
top of a pair into a closed complex becomes a Kar homotopy equivalence after `Φ`, and its cap
defect `i δφ i^* - φ_P` is killed by `Φ`, then `Φ P` is homotopy isometric to the closed complex
`X.toClosed Φ` (on the cubical route: `D_A ⟶ D_W` in `Q/𝒜_B`). -/
theorem isometric_toClosed (P : SymPoincare J (N + 1)) (i : X.D ⟶ P.C)
    (hi : X.pD ≫ i ≫ P.p = i) (hiso : IsKarEquiv (Φ.mapH X.pD) (Φ.mapH P.p) (Φ.mapH i))
    (hcap : ∀ r, Φ.F.map ((dualHom J (N + 1) i).f r ≫ X.top r ≫ i.f r) = Φ.F.map (P.φ.f r)) :
    SymPoincare.Isometric (X.toClosed Φ hZ) (P.map Φ) := by
  obtain ⟨g, hg, ⟨H₁⟩, ⟨H₂⟩⟩ := hiso
  refine ⟨⟨Φ.mapH i, g, ?_, hg, H₂, H₁, Homotopy.ofEq ?_⟩⟩
  · change Φ.mapH X.pD ≫ Φ.mapH i ≫ Φ.mapH P.p = Φ.mapH i
    simp only [← Functor.map_comp, hi]
  · ext r
    simp [map_top, ← hcap, Φ.map_star]
    erw [HomologicalComplex.comp_f, toClosed_φ_f]
    rfl

end SymPair

end ToClosed

section Lift

variable (U : ObjectProperty V)

/-- A complex with objects in `U`, as a complex in the full subcategory. -/
@[simps]
def liftComplex (C : ChainComplex V ℤ) (h : ∀ r, U (C.X r)) :
    ChainComplex U.FullSubcategory ℤ where
  X r := ⟨C.X r, h r⟩
  d r r' := ObjectProperty.homMk (C.d r r')
  shape r r' hr := ObjectProperty.hom_ext _ (C.shape r r' hr)
  d_comp_d' r r' r'' _ _ := ObjectProperty.hom_ext _ (C.d_comp_d r r' r'')

variable {U}

@[simp]
lemma ObjectProperty.units_smul_hom {X Y : U.FullSubcategory} (u : ℤˣ) (f : X ⟶ Y) :
    (u • f).hom = u • f.hom := rfl

omit [Preadditive V] in
lemma ObjectProperty.eqToHom_hom {X Y : U.FullSubcategory} (h : X = Y) :
    (eqToHom h).hom = eqToHom (congrArg ObjectProperty.FullSubcategory.obj h) := by
  subst h; rfl

/-- Lift a family of maps between complexes in `U` to a chain map. -/
@[simps]
def liftHom {K L : ChainComplex U.FullSubcategory ℤ}
    (f : (U.ι.mapHomologicalComplex _).obj K ⟶ (U.ι.mapHomologicalComplex _).obj L) : K ⟶ L where
  f r := ObjectProperty.homMk (f.f r)
  comm' r r' _ := ObjectProperty.hom_ext _ (f.comm r r')

/-- The inclusion of `U` reflects homotopies. -/
def liftHomotopy {K L : ChainComplex U.FullSubcategory ℤ} {f g : K ⟶ L}
    (H : Homotopy ((U.ι.mapHomologicalComplex _).map f) ((U.ι.mapHomologicalComplex _).map g)) :
    Homotopy f g where
  hom i j := ObjectProperty.homMk (H.hom i j)
  zero i j h := ObjectProperty.hom_ext _ (H.zero i j h)
  comm i := ObjectProperty.hom_ext _ (by
    have h := H.comm i
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel i (i - 1) by simp),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (i + 1) i by simp)] at h ⊢
    exact h)

variable (J U) in
/-- The restricted involution on `U` is the involution of `A.sub U`. -/
abbrev subInv : StrictInvolution U.FullSubcategory := subInvolution J U

/-- Lift a Poincaré complex with objects in `U` to the full subcategory `U`. -/
def SymPoincare.lift (P : SymPoincare J N) (h : ∀ r, U (P.C.X r)) : SymPoincare (subInv J U) N where
  C := liftComplex U P.C h
  p := liftHom P.p
  p_idem := by ext r; exact congrArg (fun f ↦ f.f r) P.p_idem
  support r hr := ObjectProperty.hom_ext _ (P.support r hr)
  φ := liftHom (L := liftComplex U P.C h) P.φ
  φ_kar := by ext r; exact congrArg (fun f ↦ f.f r) P.φ_kar
  symm := by
    ext r
    have h' := congrArg (fun f ↦ f.f r) P.symm
    simp only [transposeHom_f] at h' ⊢
    simp [ObjectProperty.eqToHom_hom]
    exact h'
  poincare := by
    obtain ⟨ψ, hψ, ⟨H₁⟩, ⟨H₂⟩⟩ := P.poincare
    exact ⟨liftHom (K := liftComplex U P.C h) ψ, by ext r; exact congrArg (fun f ↦ f.f r) hψ,
      ⟨liftHomotopy H₁⟩, ⟨liftHomotopy H₂⟩⟩

/-- Including the lift recovers the complex. -/
@[simp]
lemma SymPoincare.map_lift (P : SymPoincare J N) (h : ∀ r, U (P.C.X r)) :
    (P.lift h).map ⟨U.ι, fun _ ↦ rfl⟩ = P := rfl

end Lift

section Quot

variable {A : InvCat} (F : KaroubiFiltration A)

/-- Objects of `U` vanish in `A/U`. -/
lemma KaroubiFiltration.isZero_proj_obj {Y : A} (hY : F.U Y) : IsZero (F.proj.F.obj Y) := by
  rw [IsZero.iff_id_eq_zero, ← F.proj.F.map_id, ← F.proj.F.map_zero]
  exact (F.proj_map_eq_iff _ _).mpr (by simpa using FactorsThrough.of_mem hY (𝟙 Y) (𝟙 Y))

/-- A split mono whose complement lies in `U` becomes an isomorphism in `A/U`. -/
lemma KaroubiFiltration.isIso_proj_map {Y Z : A} (f : Y ⟶ Z) (t : Z ⟶ Y) (h₁ : f ≫ t = 𝟙 Y)
    (h₂ : FactorsThrough F.U (𝟙 Z - t ≫ f)) : IsIso (F.proj.F.map f) :=
  ⟨F.proj.F.map t, by rw [← F.proj.F.map_comp, h₁, F.proj.F.map_id],
    by rw [← F.proj.F.map_comp, ← F.proj.F.map_id]; exact ((F.proj_map_eq_iff _ _).mpr h₂).symm⟩

namespace SymPair

variable (X : SymPair A.inv N) (hU : ∀ r, F.U (X.bd.C.X r))

/-- **`P.toQuot`** (design §3, H2): a Poincaré pair whose boundary lies in `U` represents the
closed `(N+1)`-dimensional complex `(D, p_D, δφ)` in `A/U` (l. 217–237, [CP95, proof of
Thm. 4.1]). -/
abbrev toQuot : SymPoincare F.quot.inv (N + 1) :=
  X.toClosed F.proj fun r ↦ F.isZero_proj_obj (hU r)

/-- **`P.bdLift`** (design §3, H2): the boundary of a pair with boundary in `U`, as a
Poincaré complex in `U`. -/
abbrev bdLift : SymPoincare F.sub.inv N := X.bd.lift hU

@[simp]
lemma map_incl_bdLift : (X.bdLift F hU).map F.incl = X.bd := rfl

/-- **Excision isometry (R3)** in `A/U`: a map `i : D ⟶ P` into a closed complex which is a
Kar equivalence in `A/U` and whose cap defect `i δφ i^* - φ_P` factors through `U` (on the
cubical route: `D_A ⟶ D_W`, with cokernel and defect `B`-supported) identifies `[P]` with the
pair representative `X.toQuot` in `A/U`. -/
theorem isometric_toQuot (P : SymPoincare A.inv (N + 1)) (i : X.D ⟶ P.C)
    (hi : X.pD ≫ i ≫ P.p = i)
    (hiso : IsKarEquiv (F.proj.mapH X.pD) (F.proj.mapH P.p) (F.proj.mapH i))
    (hcap : ∀ r, FactorsThrough F.U ((dualHom A.inv (N + 1) i).f r ≫ X.top r ≫ i.f r - P.φ.f r)) :
    SymPoincare.Isometric (X.toQuot F hU) (P.map F.proj) :=
  X.isometric_toClosed _ _ P i hi hiso fun r ↦ (F.proj_map_eq_iff _ _).mpr (hcap r)

/-- **R3 for based complexes**: with identity idempotents, `i : D ⟶ P` degreewise split by
`t` with complement in `U` (`1 - t i` factors through `U`) and cap defect in `U`. -/
theorem isometric_toQuot_of_split (P : SymPoincare A.inv (N + 1)) (i : X.D ⟶ P.C)
    (hpD : X.pD = 𝟙 _) (hp : P.p = 𝟙 _) (t : ∀ r, P.C.X r ⟶ X.D.X r)
    (ht : ∀ r, i.f r ≫ t r = 𝟙 _) (hc : ∀ r, FactorsThrough F.U (𝟙 _ - t r ≫ i.f r))
    (hcap : ∀ r, FactorsThrough F.U ((dualHom A.inv (N + 1) i).f r ≫ X.top r ≫ i.f r - P.φ.f r)) :
    SymPoincare.Isometric (X.toQuot F hU) (P.map F.proj) := by
  refine X.isometric_toQuot F hU P i (by simp [hpD, hp]) ?_ hcap
  haveI : ∀ r, IsIso ((F.proj.mapH i).f r) := fun r ↦ F.isIso_proj_map _ (t r) (ht r) (hc r)
  haveI := Hom.isIso_of_components (F.proj.mapH i)
  rw [hpD, hp, InvFunctor.mapH, CategoryTheory.Functor.map_id, InvFunctor.mapH,
    CategoryTheory.Functor.map_id]
  exact IsKarEquiv.of_isIso _

variable {B : InvCat} {F' : KaroubiFiltration B} (Φ : FiltrationHom F F')

/-- Naturality of the pair representative under maps of filtrations (with H1's
`bdry_natural`, this is how Lemma 4.1 passes through the excision (4.3)). -/
theorem toQuot_map (hU' : ∀ r, F'.U ((X.map Φ.toHom).bd.C.X r)) :
    (X.toQuot F hU).map Φ.quot = (X.map Φ.toHom).toQuot F' hU' :=
  (toClosed_map X F.proj _ Φ.quot fun r ↦ F'.isZero_proj_obj (hU' r)).trans
    (toClosed_comp X Φ.toHom F'.proj fun r ↦ F'.isZero_proj_obj (hU' r))

/-- Naturality of the boundary lift under maps of filtrations. -/
theorem bdLift_map (hU' : ∀ r, F'.U ((X.map Φ.toHom).bd.C.X r)) :
    (X.bdLift F hU).map Φ.sub = (X.map Φ.toHom).bdLift F' hU' := rfl

end SymPair

end Quot

end

end HSFormal.LTheory
