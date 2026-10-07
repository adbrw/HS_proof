import HSFormal.LTheory.Model.HalfLineRel
import HSFormal.LTheory.Model.LinePairs

/-!
# Abstract half-line data (half-line splitting of the line complex, part 2)

The cellular half-line `(-∞, 0]` (or `[0, ∞)`) is encoded abstractly, in the style of
`LineData` (`Model/LineComplex.lean`), by **half-line data** `H = (E, V, O, u, w, β)`:
duality-preserving functors `E, V, O : A ⟶ B` (edges, vertices, the boundary point) with natural
transformations `u, w : E ⟶ V` and `β : O ⟶ V` such that `u` is unitary, `w` is an isometry
and `β` is an isometry onto the orthogonal complement of the image of `w`:
`u u^* = 1`, `u^* u = 1`, `w w^* = 1`, `β β^* = 1`, `w β^* = 0`, `w^* w + β^* β = 1`
(diagrammatic order).  For the negative half-line `u` is the shift `e_v ↦ v_{v+1}` and `w` the
inclusion `e_v ↦ v_v`; for the positive half-line `u` is the identity and `w` the shift.

For a complex `C` over `A`, the half-line complex is `H.cx C = Cone(u - w : EC ⟶ VC)`, and
`H.jC C : OC ⟶ H.cx C` is the inclusion of the boundary vertex.

* `H.T a b M C r` is the analogue of `LineData.θ` with coefficients `a u^* + b w^*` on dual
  vertices and `a w + b u` on dual edges; `T_comm` is the relative cycle condition (the
  boundary term is `(a + b) β^* β`, from `w^* w + β^* β = 1`), so `H.δH` is a heterogeneous
  relative boundary of `j_C^* ι j_{C^{M-*}}` (`a + b = 1`).
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression
  homotopyCofiber

noncomputable section

/-! ### Natural transformations between duality-preserving functors -/

namespace InvNat

variable {A B : InvCat} {Φ Ψ : A ⟶ B} (α : Φ.F ⟶ Ψ.F)

@[reassoc]
lemma app_map {X Y : A} (f : X ⟶ Y) : α.app X ≫ Ψ.F.map f = Φ.F.map f ≫ α.app Y :=
  (α.naturality f).symm

@[reassoc]
lemma app_star_map {X Y : A} (f : X ⟶ Y) :
    α.app Y ≫ B.inv.star (Ψ.F.map f) = B.inv.star (Φ.F.map f) ≫ α.app X := by
  rw [← Ψ.map_star, ← Φ.map_star]; exact (α.naturality _).symm

@[reassoc]
lemma star_app_map {X Y : A} (f : X ⟶ Y) :
    B.inv.star (α.app X) ≫ Φ.F.map f = Ψ.F.map f ≫ B.inv.star (α.app Y) := by
  have h := congrArg B.inv.star (α.naturality (A.inv.star f))
  rw [B.inv.star_comp, B.inv.star_comp, ← Φ.map_star, ← Ψ.map_star, A.inv.star_star] at h
  exact h

@[reassoc]
lemma star_app_star_map {X Y : A} (f : X ⟶ Y) :
    B.inv.star (α.app Y) ≫ B.inv.star (Φ.F.map f) = B.inv.star (Ψ.F.map f) ≫
      B.inv.star (α.app X) := by
  rw [← B.inv.star_comp, ← B.inv.star_comp, α.naturality]

@[reassoc]
lemma app_XIsoOfEq (C : ChainComplex A ℤ) {a b : ℤ} (h : a = b) :
    α.app (C.X a) ≫ ((Ψ.mapC C).XIsoOfEq h).hom = ((Φ.mapC C).XIsoOfEq h).hom ≫ α.app (C.X b) := by
  subst h; simp

@[reassoc]
lemma star_app_XIsoOfEq (C : ChainComplex A ℤ) {a b : ℤ} (h : a = b) :
    B.inv.star (α.app (C.X a)) ≫ ((Φ.mapC C).XIsoOfEq h).hom =
      ((Ψ.mapC C).XIsoOfEq h).hom ≫ B.inv.star (α.app (C.X b)) := by
  subst h; simp

end InvNat

namespace InvFunctor

variable {A B : InvCat} (Φ : A ⟶ B)

@[reassoc]
lemma XIsoOfEq_map' {C D : ChainComplex A ℤ} (f : C ⟶ D) {a b : ℤ} (h : a = b) :
    ((Φ.mapC C).XIsoOfEq h).hom ≫ Φ.F.map (f.f b) =
      Φ.F.map (f.f a) ≫ ((Φ.mapC D).XIsoOfEq h).hom := by
  subst h; simp

@[reassoc]
lemma XIsoOfEq_star_map' {C D : ChainComplex A ℤ} (f : C ⟶ D) {a b : ℤ} (h : a = b) :
    ((Φ.mapC D).XIsoOfEq h).hom ≫ B.inv.star (Φ.F.map (f.f b)) =
      B.inv.star (Φ.F.map (f.f a)) ≫ ((Φ.mapC C).XIsoOfEq h).hom := by
  subst h; simp

@[reassoc]
lemma XIsoOfEq_map_fam' {C D : ChainComplex A ℤ} (F : ∀ i j, C.X i ⟶ D.X j) {a a' : ℤ}
    (h : a = a') (b : ℤ) :
    ((Φ.mapC C).XIsoOfEq h).hom ≫ Φ.F.map (F a' b) = Φ.F.map (F a b) := by
  subst h; simp

@[reassoc]
lemma map_fam_XIsoOfEq' {C D : ChainComplex A ℤ} (F : ∀ i j, C.X i ⟶ D.X j) (a : ℤ) {b b' : ℤ}
    (h : b = b') :
    Φ.F.map (F a b) ≫ ((Φ.mapC D).XIsoOfEq h).hom = Φ.F.map (F a b') := by
  subst h; simp

@[reassoc]
lemma XIsoOfEq_star_map_fam' {C D : ChainComplex A ℤ} (F : ∀ i j, C.X i ⟶ D.X j) {b b' : ℤ}
    (h : b = b') (a : ℤ) :
    ((Φ.mapC D).XIsoOfEq h).hom ≫ B.inv.star (Φ.F.map (F a b')) =
      B.inv.star (Φ.F.map (F a b)) := by
  subst h; simp

@[reassoc]
lemma star_map_fam_XIsoOfEq' {C D : ChainComplex A ℤ} (F : ∀ i j, C.X i ⟶ D.X j) (b : ℤ)
    {a a' : ℤ} (h : a = a') :
    B.inv.star (Φ.F.map (F a b)) ≫ ((Φ.mapC C).XIsoOfEq h).hom =
      B.inv.star (Φ.F.map (F a' b)) := by
  subst h; simp

lemma map_eqToHom_X' (C : ChainComplex A ℤ) {a b : ℤ} (h : a = b) :
    Φ.F.map (eqToHom (congrArg C.X h)) = ((Φ.mapC C).XIsoOfEq h).hom := by
  subst h; simp

lemma mapC_dual_XIsoOfEq' {M : ℤ} (C : ChainComplex A ℤ) {a b : ℤ} (h : a = b) :
    (Φ.mapC (dualComplex A.inv M C)).XIsoOfEq h =
      (Φ.mapC C).XIsoOfEq (show M - a = M - b by omega) := by
  subst h; rfl

lemma mapC_dual_d' (M : ℤ) (C : ChainComplex A ℤ) (r r' : ℤ) :
    (Φ.mapC (dualComplex A.inv M C)).d r r' =
      r.negOnePow • B.inv.star ((Φ.mapC C).d (M - r') (M - r)) := by
  simp [Functor.map_units_smul, Φ.map_star]

end InvFunctor

/-! ### Half-line data -/

/-- **Half-line data** `(E, V, O, u, w, β)`: `u : E ⟶ V` unitary, `w : E ⟶ V` an isometry and
`β : O ⟶ V` an isometry onto the complement of the image of `w`. -/
structure HalfLineData (A B : InvCat) where
  /-- The edges. -/
  E : A ⟶ B
  /-- The vertices. -/
  V : A ⟶ B
  /-- The boundary point. -/
  O : A ⟶ B
  /-- The unitary edge-vertex incidence. -/
  u : E.F ⟶ V.F
  /-- The isometric edge-vertex incidence. -/
  w : E.F ⟶ V.F
  /-- The boundary vertex. -/
  β : O.F ⟶ V.F
  u_star : ∀ X, u.app X ≫ B.inv.star (u.app X) = 𝟙 _
  star_u : ∀ X, B.inv.star (u.app X) ≫ u.app X = 𝟙 _
  w_star : ∀ X, w.app X ≫ B.inv.star (w.app X) = 𝟙 _
  β_star : ∀ X, β.app X ≫ B.inv.star (β.app X) = 𝟙 _
  w_star_β : ∀ X, w.app X ≫ B.inv.star (β.app X) = 0
  total : ∀ X, B.inv.star (w.app X) ≫ w.app X + B.inv.star (β.app X) ≫ β.app X = 𝟙 _

namespace HalfLineData

variable {A B : InvCat} (H : HalfLineData A B)

attribute [reassoc (attr := simp)] u_star star_u w_star β_star w_star_β

@[reassoc (attr := simp)]
lemma β_star_w (X : A) : H.β.app X ≫ B.inv.star (H.w.app X) = 0 := by
  rw [← B.inv.star_star (H.β.app X), ← B.inv.star_comp, H.w_star_β, B.inv.star_zero]

@[reassoc]
lemma star_β_β' (X : A) : B.inv.star (H.β.app X) ≫ H.β.app X =
    𝟙 _ - B.inv.star (H.w.app X) ≫ H.w.app X := by
  rw [← H.total X]; abel

/-! ### The half-line complex -/

/-- `u - w : EC ⟶ VC`, the differential of the half-line. -/
def g (C : ChainComplex A ℤ) : H.E.mapC C ⟶ H.V.mapC C where
  f i := H.u.app (C.X i) - H.w.app (C.X i)
  comm' i j _ := by
    simp only [Functor.mapHomologicalComplex_obj_d, comp_sub, sub_comp, InvNat.app_map]

@[simp] lemma g_f (C : ChainComplex A ℤ) (i : ℤ) :
    (H.g C).f i = H.u.app (C.X i) - H.w.app (C.X i) := rfl

/-- **The half-line complex** `Cone(u - w : EC ⟶ VC)`. -/
abbrev cx (C : ChainComplex A ℤ) : ChainComplex B ℤ := cone (H.g C)

lemma mapH_comp_g {C D : ChainComplex A ℤ} (f : C ⟶ D) :
    H.E.mapH f ≫ H.g D = H.g C ≫ H.V.mapH f := by
  ext i; simp [sub_comp, comp_sub, InvNat.app_map, -NatTrans.naturality, -NatTrans.naturality_assoc]

/-- A chain map acts diagonally on the half-line complexes. -/
def map {C D : ChainComplex A ℤ} (f : C ⟶ D) : H.cx C ⟶ H.cx D :=
  coneMap (H.E.mapH f) (H.V.mapH f) (H.mapH_comp_g f)

variable {H}

@[reassoc (attr := simp)]
lemma inlX_map {C D : ChainComplex A ℤ} (f : C ⟶ D) (i k : ℤ)
    (hk : (ComplexShape.down ℤ).Rel i k) :
    inlX (H.g C) k i hk ≫ (H.map f).f i = H.E.F.map (f.f k) ≫ inlX (H.g D) k i hk :=
  inlX_coneMap_f _ i k hk

@[reassoc (attr := simp)]
lemma inrX_map {C D : ChainComplex A ℤ} (f : C ⟶ D) (i : ℤ) :
    inrX (H.g C) i ≫ (H.map f).f i = H.V.F.map (f.f i) ≫ inrX (H.g D) i :=
  inrX_coneMap_f _ i

@[reassoc (attr := simp)]
lemma map_fstX {C D : ChainComplex A ℤ} (f : C ⟶ D) (i k : ℤ)
    (hk : (ComplexShape.down ℤ).Rel i k) :
    (H.map f).f i ≫ fstX (H.g D) i k hk = fstX (H.g C) i k hk ≫ H.E.F.map (f.f k) :=
  coneMap_f_fstX _ i k hk

@[reassoc (attr := simp)]
lemma map_sndX {C D : ChainComplex A ℤ} (f : C ⟶ D) (i : ℤ) :
    (H.map f).f i ≫ sndX (H.g D) i = sndX (H.g C) i ≫ H.V.F.map (f.f i) :=
  coneMap_f_sndX _ i

variable (H)

@[reassoc (attr := simp)]
lemma map_comp {C D E : ChainComplex A ℤ} (f : C ⟶ D) (f' : D ⟶ E) :
    H.map (f ≫ f') = H.map f ≫ H.map f' := by
  rw [map, map, map, coneMap_comp]
  exact coneMap_congr _ (Functor.map_comp _ _ _) (Functor.map_comp _ _ _)

@[simp]
lemma map_id (C : ChainComplex A ℤ) : H.map (𝟙 C) = 𝟙 _ := by
  rw [map, coneMap_congr _ ((H.E.F.mapHomologicalComplex _).map_id C)
    ((H.V.F.mapHomologicalComplex _).map_id C)]
  exact coneMap_id _

/-- A homotopy acts diagonally on the half-line complexes. -/
def htpy {C D : ChainComplex A ℤ} {f f' : C ⟶ D} (Hf : Homotopy f f') :
    Homotopy (H.map f) (H.map f') :=
  coneMapHomotopy _ _ (H.E.F.mapHomotopy Hf) (H.V.F.mapHomotopy Hf) fun i k ↦ by
    simp [sub_comp, comp_sub, InvNat.app_map, -NatTrans.naturality, -NatTrans.naturality_assoc]

lemma map_supportedIn {C : ChainComplex A ℤ} {p : C ⟶ C} {lo hi : ℤ}
    (hp : SupportedIn p lo hi) : SupportedIn (H.map p) lo (hi + 1) := fun r hr ↦ by
  apply ext_from_X (H.g C) (r - 1) r (by simp)
  · simp [hp (r - 1) (by omega)]
  · simp [hp r (by omega)]

/-! ### The boundary vertex -/

/-- `β : OC ⟶ VC` as a chain map. -/
def βC (C : ChainComplex A ℤ) : H.O.mapC C ⟶ H.V.mapC C where
  f i := H.β.app (C.X i)
  comm' i j _ := by simp [InvNat.app_map, -NatTrans.naturality, -NatTrans.naturality_assoc]

/-- The inclusion `j_C = inr ∘ β : OC ⟶ H.cx C` of the boundary vertex. -/
def jC (C : ChainComplex A ℤ) : H.O.mapC C ⟶ H.cx C := H.βC C ≫ inr (H.g C)

@[simp]
lemma jC_f (C : ChainComplex A ℤ) (i : ℤ) : (H.jC C).f i = H.β.app (C.X i) ≫ inrX (H.g C) i := by
  simp [jC, βC]

lemma jC_natural {C D : ChainComplex A ℤ} (f : C ⟶ D) :
    H.O.mapH f ≫ H.jC D = H.jC C ≫ H.map f := by
  ext i; simp [InvNat.app_map_assoc, -NatTrans.naturality, -NatTrans.naturality_assoc]

variable {H} in
@[reassoc]
lemma star_fstX_star_map {C D : ChainComplex A ℤ} (f : C ⟶ D) {i k : ℤ}
    (hk : (ComplexShape.down ℤ).Rel i k) :
    B.inv.star (fstX (H.g D) i k hk) ≫ B.inv.star ((H.map f).f i) =
      B.inv.star (H.E.F.map (f.f k)) ≫ B.inv.star (fstX (H.g C) i k hk) := by
  rw [← B.inv.star_comp, map_fstX, B.inv.star_comp]

variable {H} in
@[reassoc]
lemma star_sndX_star_map {C D : ChainComplex A ℤ} (f : C ⟶ D) (i : ℤ) :
    B.inv.star (sndX (H.g D) i) ≫ B.inv.star ((H.map f).f i) =
      B.inv.star (H.V.F.map (f.f i)) ≫ B.inv.star (sndX (H.g C) i) := by
  rw [← B.inv.star_comp, map_sndX, B.inv.star_comp]

end HalfLineData

/-- Normal form for components of maps between half-line complexes and their duals. -/
macro "half_simp_core" : tactic => `(tactic|
  simp (disch := down_rel) only [dualComplex_d, homotopyCofiber_d, comp_add, add_comp, assoc,
    comp_sub, sub_comp, Linear.comp_units_smul, Linear.units_smul_comp, Linear.comp_smul,
    Linear.smul_comp, neg_comp, comp_neg, zero_comp, comp_zero, smul_zero, smul_neg, zero_add,
    add_zero, neg_zero, neg_neg, id_comp, comp_id, sub_self, zero_smul, one_smul, smul_add,
    smul_sub, add_smul, Units.neg_smul, units_smul_units_smul_self, units_smul_rat_smul,
    negOnePow_sub_one', Int.negOnePow_succ, neg_add_rev, sub_neg_eq_add, sub_zero, zero_sub,
    cone.star_fstX_inlX_assoc, cone.star_fstX_inlX, cone.star_fstX_inrX_assoc,
    cone.star_fstX_inrX, cone.star_sndX_inlX_assoc, cone.star_sndX_inlX,
    cone.star_sndX_inrX_assoc, cone.star_sndX_inrX, cone.star_fstX_inlX'_assoc,
    cone.star_fstX_inlX', star_fstX_star_d_assoc, star_fstX_star_d, star_sndX_star_d_assoc,
    star_sndX_star_d, inlX_fstX_assoc, inlX_fstX, inlX_sndX_assoc, inlX_sndX, inrX_fstX_assoc,
    inrX_fstX, inrX_sndX_assoc, inrX_sndX, inlX_fstX'_assoc, inlX_fstX', d_fstX_assoc, d_fstX,
    d_sndX_assoc, d_sndX, inlX_d''_assoc, inlX_d'', inrX_d_assoc, inrX_d,
    StrictInvolution.star_sub, StrictInvolution.star_neg, StrictInvolution.star_add,
    StrictInvolution.star_id, StrictInvolution.star_zero, star_rat_smul,
    StrictInvolution.star_units_smul, StrictInvolution.star_star, StrictInvolution.star_comp,
    Functor.map_neg, Functor.map_add, Functor.map_sub, Functor.map_zero,
    star_d_XIsoOfEq_assoc, star_d_XIsoOfEq,
    XIsoOfEq_comp_star_d_assoc, XIsoOfEq_comp_star_d,
    Iso.inv_hom_id, Iso.hom_inv_id, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
    InvFunctor.map_star, dualHom_f, comp_f, bidual_hom_f, Functor.map_units_smul,
    star_XIsoOfEq_hom, star_XIsoOfEq_inv,
    XIsoOfEq_inv_eq, XIsoOfEq_hom_comp_XIsoOfEq_hom_assoc, XIsoOfEq_hom_comp_XIsoOfEq_hom,
    XIsoOfEq_rfl, Iso.refl_hom, XIsoOfEq_star_inrX_assoc, XIsoOfEq_star_inrX,
    XIsoOfEq_star_inlX_assoc, XIsoOfEq_star_inlX, star_sndX_XIsoOfEq_assoc, star_sndX_XIsoOfEq,
    star_fstX_XIsoOfEq_assoc, star_fstX_XIsoOfEq,
    HalfLineData.g_f, HalfLineData.jC_f, InvFunctor.mapDualIso_inv_f,
    InvFunctor.mapDualIso_hom_f, Functor.mapHomologicalComplex_obj_d,
    Functor.mapHomologicalComplex_map_f,
    InvNat.app_map_assoc, InvNat.app_map, InvNat.app_star_map_assoc, InvNat.app_star_map,
    InvNat.star_app_map_assoc, InvNat.star_app_map, InvNat.star_app_star_map_assoc,
    InvNat.star_app_star_map, InvNat.app_XIsoOfEq_assoc, InvNat.app_XIsoOfEq,
    InvNat.star_app_XIsoOfEq_assoc, InvNat.star_app_XIsoOfEq,
    HalfLineData.u_star_assoc, HalfLineData.u_star, HalfLineData.star_u_assoc,
    HalfLineData.star_u, HalfLineData.w_star_assoc, HalfLineData.w_star,
    HalfLineData.β_star_assoc, HalfLineData.β_star, HalfLineData.w_star_β_assoc,
    HalfLineData.w_star_β, HalfLineData.β_star_w_assoc, HalfLineData.β_star_w,
    InvFunctor.XIsoOfEq_map'_assoc, InvFunctor.XIsoOfEq_map',
    InvFunctor.XIsoOfEq_star_map'_assoc, InvFunctor.XIsoOfEq_star_map',
    InvFunctor.XIsoOfEq_map_fam'_assoc, InvFunctor.XIsoOfEq_map_fam',
    InvFunctor.map_fam_XIsoOfEq'_assoc, InvFunctor.map_fam_XIsoOfEq',
    InvFunctor.XIsoOfEq_star_map_fam'_assoc, InvFunctor.XIsoOfEq_star_map_fam',
    InvFunctor.star_map_fam_XIsoOfEq'_assoc, InvFunctor.star_map_fam_XIsoOfEq',
    InvFunctor.map_eqToHom_X', InvFunctor.mapC_dual_XIsoOfEq', InvFunctor.mapC_dual_d',
    HalfLineData.inlX_map_assoc, HalfLineData.inlX_map, HalfLineData.inrX_map_assoc,
    HalfLineData.inrX_map, HalfLineData.map_fstX_assoc, HalfLineData.map_fstX,
    HalfLineData.map_sndX_assoc, HalfLineData.map_sndX,
    HalfLineData.star_fstX_star_map_assoc, HalfLineData.star_fstX_star_map,
    HalfLineData.star_sndX_star_map_assoc, HalfLineData.star_sndX_star_map])

/-- `half_simp_core`, then normalize objects and repeat. -/
macro "half_simp" : tactic => `(tactic| (
  (try half_simp_core) <;>
  (try dsimp only [dualComplex_X, Functor.mapHomologicalComplex_obj_X, homotopyCofiber_X]) <;>
  (try half_simp_core) <;>
  (try (dsimp only [dualComplex_X, InvFunctor.mapC, Functor.mapHomologicalComplex_obj_X,
    homotopyCofiber_X]; done))))

namespace HalfLineData

variable {A B : InvCat} (H : HalfLineData A B)

/-! ### The duality of the half-line -/

variable (a b : ℚ)

/-- The coefficient `a u^* + b w^* : V ⟶ E` on dual vertices. -/
abbrev cf' (X : A) : H.V.F.obj X ⟶ H.E.F.obj X :=
  a • B.inv.star (H.u.app X) + b • B.inv.star (H.w.app X)

/-- The coefficient `a w + b u : E ⟶ V` on dual edges. -/
abbrev cf (X : A) : H.E.F.obj X ⟶ H.V.F.obj X := a • H.w.app X + b • H.u.app X

variable (M : ℤ)

/-- The top family `(e', v') ↦ ((a u^* + b w^*) v', (-1)^r (a w + b u) e')` of the relative
duality of the half-line (the analogue of `LineData.θ`). -/
def T (C : ChainComplex A ℤ) (r : ℤ) :
    (H.cx C).X (M + 1 - r) ⟶ (H.cx (dualComplex A.inv M C)).X r :=
  B.inv.star (inrX (H.g C) (M + 1 - r)) ≫
      ((H.V.mapC C).XIsoOfEq (show M + 1 - r = M - (r - 1) by omega)).hom ≫
        H.cf' a b (C.X (M - (r - 1))) ≫ inlX (H.g (dualComplex A.inv M C)) (r - 1) r (by simp) +
    r.negOnePow • (B.inv.star (inlX (H.g C) (M - r) (M + 1 - r) (down_rel_sub M r)) ≫
      H.cf a b (C.X (M - r)) ≫ inrX (H.g (dualComplex A.inv M C)) r)

/-- The boundary term `j_C^* ι j_{C^{M-*}}` of the relative cycle condition. -/
abbrev bdF (C : ChainComplex A ℤ) :
    dualComplex B.inv M (H.cx C) ⟶ H.cx (dualComplex A.inv M C) :=
  dualHom B.inv M (H.jC C) ≫ (H.O.mapDualIso M C).inv ≫ H.jC (dualComplex A.inv M C)

lemma T_comm (hab : a + b = 1) (C : ChainComplex A ℤ) (r r' : ℤ)
    (h : (ComplexShape.down ℤ).Rel r r') :
    H.T a b M C r ≫ (H.cx (dualComplex A.inv M C)).d r r' =
      ((dualComplex B.inv (M + 1) (H.cx C)).d r r' ≫ H.T a b M C r' :
        (H.cx C).X (M + 1 - r) ⟶ _) +
      ((H.cx C).XIsoOfEq (by simp only [ComplexShape.down_Rel] at h; omega :
        M + 1 - r = M - r')).hom ≫ (H.bdF M C).f r' := by
  obtain rfl : r' = r - 1 := by simp only [ComplexShape.down_Rel] at h; omega
  apply cone.ext_star (J := B.inv) (H.g C) _ _ (down_rel_sub M r)
  all_goals apply ext_to_X (H.g (dualComplex A.inv M C)) (r - 1) (r - 1 - 1) (by simp)
  all_goals simp only [T, bdF]
  all_goals half_simp
  all_goals simp only [star_β_β', comp_sub, comp_id]
  all_goals obtain rfl : b = 1 - a := by linarith
  all_goals simp only [sub_smul, one_smul]
  all_goals abel

/-- The heterogeneous relative boundary of the half-line duality (`a + b = 1`). -/
def δH (hab : a + b = 1) (C : ChainComplex A ℤ) : Homotopy (H.bdF M C) 0 :=
  homotopyOfTop _ (H.T a b M C) (H.T_comm a b M hab C)

lemma relTopH_δH (hab : a + b = 1) (C : ChainComplex A ℤ) (r : ℤ) :
    relTopH (H.δH a b M hab C) r = H.T a b M C r :=
  relTopH_homotopyOfTop _ _ r

/-- **The duality of the half-line** `Θ : Cone(j_C)^{M+1-*} ⟶ H.cx (C^{M-*})`. -/
def Θ (hab : a + b = 1) (C : ChainComplex A ℤ) :
    dualComplex B.inv (M + 1) (cone (H.jC C)) ⟶ H.cx (dualComplex A.inv M C) :=
  relDualityH (H.δH a b M hab C)

lemma Θ_f (hab : a + b = 1) (C : ChainComplex A ℤ) (r : ℤ) :
    (H.Θ a b M hab C).f r = B.inv.star (inrX (H.jC C) (M + 1 - r)) ≫ H.T a b M C r +
      (r + 1).negOnePow • (B.inv.star (inlX (H.jC C) (M - r) (M + 1 - r) (down_rel_sub M r)) ≫
        H.β.app (C.X (M - r)) ≫ inrX (H.g (dualComplex A.inv M C)) r :
          _ ⟶ (H.cx (dualComplex A.inv M C)).X r) := by
  simp [Θ, relTopH_δH]

@[reassoc]
lemma T_natural {C D : ChainComplex A ℤ} (f : C ⟶ D) (r : ℤ) :
    B.inv.star ((H.map f).f (M + 1 - r)) ≫ H.T a b M C r =
      H.T a b M D r ≫ (H.map (dualHom A.inv M f)).f r := by
  apply cone.ext_star (J := B.inv) (H.g D) _ _ (down_rel_sub M r)
  all_goals apply ext_to_X (H.g (dualComplex A.inv M C)) r (r - 1) (by simp)
  all_goals simp only [T]
  all_goals half_simp

/-- Naturality of `Θ`. -/
lemma Θ_natural (hab : a + b = 1) {C D : ChainComplex A ℤ} (f : C ⟶ D) :
    dualHom B.inv (M + 1) (coneMap (H.O.mapH f) (H.map f) (H.jC_natural f)) ≫
        H.Θ a b M hab C = H.Θ a b M hab D ≫ H.map (dualHom A.inv M f) := by
  ext r
  simp only [comp_f, dualHom_f, Θ_f, star_coneMap_f (H.jC_natural f) _ _ (down_rel_sub M r),
    add_comp, comp_add, assoc, cone.star_fstX_inrX_assoc, cone.star_fstX_inlX_assoc,
    cone.star_sndX_inrX_assoc, cone.star_sndX_inlX_assoc, Linear.comp_units_smul,
    Linear.units_smul_comp, zero_comp, comp_zero, add_zero, zero_add,
    T_natural]
  half_simp

/-! ### `Θ` with coefficients `(1, 0)` is an isomorphism -/

lemma one_add_zero : (1 : ℚ) + 0 = 1 := by norm_num

/-- The inverse of `Θ_{1,0}`: `e ↦ u e` (dual vertex), `v ↦ (-1)^r w^* v` (dual edge)
`+ (-1)^{r+1} β^* v` (cone coordinate). -/
def Θinvf (C : ChainComplex A ℤ) (r : ℤ) :
    (H.cx (dualComplex A.inv M C)).X r ⟶ (cone (H.jC C)).X (M + 1 - r) :=
  fstX (H.g (dualComplex A.inv M C)) r (r - 1) (by simp) ≫ H.u.app (C.X (M - (r - 1))) ≫
      ((H.V.mapC C).XIsoOfEq (show M - (r - 1) = M + 1 - r by omega)).hom ≫
        B.inv.star (sndX (H.g C) (M + 1 - r)) ≫ B.inv.star (sndX (H.jC C) (M + 1 - r)) +
    sndX (H.g (dualComplex A.inv M C)) r ≫
      (r.negOnePow • (B.inv.star (H.w.app (C.X (M - r))) ≫
          B.inv.star (fstX (H.g C) (M + 1 - r) (M - r) (down_rel_sub M r)) ≫
            B.inv.star (sndX (H.jC C) (M + 1 - r))) +
        (r + 1).negOnePow • (B.inv.star (H.β.app (C.X (M - r))) ≫
          B.inv.star (fstX (H.jC C) (M + 1 - r) (M - r) (down_rel_sub M r))))

set_option maxHeartbeats 400000 in
lemma Θ_Θinvf (C : ChainComplex A ℤ) (r : ℤ) :
    (H.Θ 1 0 M one_add_zero C).f r ≫ H.Θinvf M C r = 𝟙 _ := by
  apply cone.ext_star (J := B.inv) (H.jC C) _ _ (down_rel_sub M r)
  · apply ext_to_star (H.jC C) B.inv (down_rel_sub M r)
    · simp only [Θ_f, Θinvf, T]; half_simp
    · apply ext_to_star (H.g C) B.inv (down_rel_sub M r)
      all_goals simp only [Θ_f, Θinvf, T]; half_simp
  · apply cone.ext_star (J := B.inv) (H.g C) _ _ (down_rel_sub M r)
    all_goals apply ext_to_star (H.jC C) B.inv (down_rel_sub M r)
    · simp only [Θ_f, Θinvf, T]; half_simp
    · apply ext_to_star (H.g C) B.inv (down_rel_sub M r)
      all_goals simp only [Θ_f, Θinvf, T]; half_simp
    · simp only [Θ_f, Θinvf, T]; half_simp
    · apply ext_to_star (H.g C) B.inv (down_rel_sub M r)
      · simp only [Θ_f, Θinvf, T]; half_simp
      · simp only [Θ_f, Θinvf, T]; half_simp

lemma Θinvf_Θ (C : ChainComplex A ℤ) (r : ℤ) :
    H.Θinvf M C r ≫ (H.Θ 1 0 M one_add_zero C).f r = 𝟙 _ := by
  apply ext_from_X (H.g (dualComplex A.inv M C)) (r - 1) r (by simp)
  all_goals apply ext_to_X (H.g (dualComplex A.inv M C)) r (r - 1) (by simp)
  all_goals simp only [Θ_f, Θinvf, T]
  all_goals half_simp
  all_goals simp only [star_β_β']
  all_goals abel

/-- **`Θ_{1,0}` is an isomorphism.** -/
def ΘIso (C : ChainComplex A ℤ) :
    dualComplex B.inv (M + 1) (cone (H.jC C)) ≅ H.cx (dualComplex A.inv M C) :=
  Hom.isoOfComponents (fun r ↦ ⟨(H.Θ 1 0 M one_add_zero C).f r, H.Θinvf M C r,
    H.Θ_Θinvf M C r, H.Θinvf_Θ M C r⟩) (fun r r' _ ↦ (H.Θ 1 0 M one_add_zero C).comm r r')

@[simp]
lemma ΘIso_hom (C : ChainComplex A ℤ) : (H.ΘIso M C).hom = H.Θ 1 0 M one_add_zero C := by
  ext; rfl

/-! ### `Θ_{a,b} ≃ Θ_{1,0}` -/

/-- The difference `T_{a,b} - T_{1,0}` is null-homotopic via `(e', v') ↦ ((-1)^r b e', 0)`. -/
def TdiffHtpy (hab : a + b = 1) (C : ChainComplex A ℤ) :
    Homotopy (relTopDiffH (H.δH a b M hab C) (H.δH 1 0 M one_add_zero C)) 0 where
  hom r r' := if hr : (ComplexShape.down ℤ).Rel r' r then
      b • r.negOnePow • (B.inv.star (inlX (H.g C) (M - r) (M + 1 - r) (down_rel_sub M r)) ≫
        inlX (H.g (dualComplex A.inv M C)) r r' hr)
    else 0
  zero r r' hr := dif_neg hr
  comm r := by
    have h₀ : (ComplexShape.down ℤ).Rel r (r - 1) := by simp
    have h₃ : (ComplexShape.down ℤ).Rel (r + 1) r := by simp
    rw [dNext_eq _ h₀, prevD_eq _ h₃, dif_pos h₀, dif_pos h₃]
    simp only [relTopDiffH_f, relTopH_δH, zero_f, add_zero]
    obtain rfl : a = 1 - b := by linarith
    apply cone.ext_star (J := B.inv) (H.g C) _ _ (down_rel_sub M r)
    all_goals apply ext_to_X (H.g (dualComplex A.inv M C)) r (r - 1) h₀
    all_goals simp only [T]
    all_goals half_simp
    all_goals (try simp only [sub_smul, one_smul])
    all_goals abel

/-- **`Θ_{a,b} ≃ Θ_{1,0}`** (for `a + b = 1`). -/
def ΘHtpy (hab : a + b = 1) (C : ChainComplex A ℤ) :
    Homotopy (H.Θ a b M hab C) (H.Θ 1 0 M one_add_zero C) :=
  relDualityHHomotopy _ _ (H.TdiffHtpy a b M hab C)

end HalfLineData

end

end HSFormal.LTheory
