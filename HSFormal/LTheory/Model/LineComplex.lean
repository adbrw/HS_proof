import HSFormal.LTheory.Model.CZFunctor
import HSFormal.LTheory.BoundaryPoincare
import HSFormal.LTheory.ConcreteL

/-!
# Tensoring with the cellular real line (lower L-theory model, module 4)

Abstractly, the cellular line is encoded by **line data** `L = (Δ, s)`: a duality-preserving
functor `Δ : A ⟶ B` with a unitary natural automorphism `s` (the shift of the line).  For
`C_ℤ(A)` this is the constant functor and the shift by one (`CZ.lineData`).

For a complex `C` over `A`, `L.cx C = Cone(s - 1 : ΔC ⟶ ΔC)` is `C ⊗ C(ℝ)`: the `ΔC` summand of
the cone is the vertex part `v ⊗ C`, the shifted summand the edge part `e ⊗ C`.  Chain maps and
homotopies act diagonally (`L.map`, `L.htpy`).

The duality of the line enters through the chain maps
`L.θ a b M C : (L.cx C)^{M+1-*} ⟶ L.cx (C^{M-*})`, `(e', v') ↦ (x s⁻¹ v', (-1)^r x e')` for
`x = a + b s` (`cf`, `cf'`): natural (`θ_natural`), with transpose `θ b a` (`θ_transpose`);
`θ 1 0` is an isomorphism (`θIso`) and `θ a b ≃ θ (a + b) 0` (`θHtpy`).  The strictly
symmetric choice `a = b = ½` (`L.θs`) is the `ℚ`-averaged duality `½([v-1, v] + [v, v+1])`.

`L.sym P = (L.cx P.C, L.map P.p, θs ≫ L.map P.φ)` is `P ⊗ ℝ` (Poincaré via `θ 1 0`), with
`symSumIsometry : (P ⊕ Q) ⊗ ℝ ≃ P ⊗ ℝ ⊕ Q ⊗ ℝ`.  Component identities are proved by the
normal-form tactic `line_simp`.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression
  homotopyCofiber

noncomputable section

/-! ### Homotopies of cone maps -/

section ConeHomotopy

variable {V : Type*} [Category V] [Preadditive V] [HasBinaryBiproducts V]
  {K L K' L' : ChainComplex V ℤ} {a : K ⟶ L} {b : K' ⟶ L'}
  {m m' : K ⟶ K'} {n n' : L ⟶ L'} (h : m ≫ b = a ≫ n) (h' : m' ≫ b = a ≫ n')

/-- Compatible homotopies of the components of two squares give a homotopy of the induced maps
of cones, `(x, y) ↦ (-H_m x, H_n y)`. -/
def coneMapHomotopy (Hm : Homotopy m m') (Hn : Homotopy n n')
    (hc : ∀ i k, Hm.hom i k ≫ b.f k = a.f i ≫ Hn.hom i k) :
    Homotopy (coneMap m n h) (coneMap m' n' h') where
  hom i i' := if hi : (ComplexShape.down ℤ).Rel i' i then
      -(fstX a i (i - 1) (by simp) ≫ Hm.hom (i - 1) i ≫ inlX b i i' hi) +
        sndX a i ≫ Hn.hom i i' ≫ inrX b i'
    else 0
  zero i i' hi := dif_neg hi
  comm i := by
    have h₁ : (ComplexShape.down ℤ).Rel i (i - 1) := by simp
    have h₂ : (ComplexShape.down ℤ).Rel (i - 1) (i - 1 - 1) := by simp
    have h₃ : (ComplexShape.down ℤ).Rel (i + 1) i := by simp
    rw [dNext_eq _ h₁, prevD_eq _ h₃, dif_pos h₁, dif_pos h₃]
    have em := Hm.comm (i - 1)
    have en := Hn.comm i
    rw [dNext_eq _ h₂, prevD_eq _ h₁] at em
    rw [dNext_eq _ h₁, prevD_eq _ h₃] at en
    apply ext_from_X a (i - 1) i h₁
    · apply ext_to_X b i (i - 1) h₁
      · simp only [homotopyCofiber_d, inlX_coneMap_f_assoc, coneMap_f_fstX, add_comp, assoc,
          comp_add, inlX_d_assoc a i (i - 1) (i - 1 - 1) h₁ h₂, neg_comp, inlX_fstX_assoc,
          inlX_sndX_assoc, zero_comp, add_zero, inrX_fstX_assoc, neg_add_rev, neg_neg, comp_neg,
          d_fstX b (i + 1) i (i - 1) h₃ h₁, inlX_fstX, inrX_d_assoc, comp_zero, neg_zero,
          zero_add]
        rw [em]
        simp only [comp_id, inrX_sndX_assoc, inrX_fstX, comp_zero, add_zero]
      · simp only [homotopyCofiber_d, inlX_coneMap_f_assoc, coneMap_f_sndX, add_comp, assoc,
          comp_add, inlX_d_assoc a i (i - 1) (i - 1 - 1) h₁ h₂, neg_comp, inlX_fstX_assoc,
          inlX_sndX_assoc, zero_comp, add_zero, inrX_fstX_assoc, comp_neg,
          d_sndX b (i + 1) i h₃, inlX_sndX, inrX_d_assoc, inrX_sndX_assoc, comp_zero,
          neg_zero, zero_add, inrX_sndX, inlX_fstX, comp_id]
        rw [hc, add_neg_cancel]
    · apply ext_to_X b i (i - 1) h₁
      · simp only [homotopyCofiber_d, inrX_coneMap_f_assoc, coneMap_f_fstX, add_comp, assoc,
          comp_add, inrX_d_assoc, inrX_fstX_assoc, zero_comp, neg_comp, inrX_sndX_assoc,
          comp_neg, d_fstX b (i + 1) i (i - 1) h₃ h₁, inrX_fstX, comp_zero, neg_zero,
          zero_add, add_zero]
      · simp only [homotopyCofiber_d, inrX_coneMap_f_assoc, coneMap_f_sndX, add_comp, assoc,
          comp_add, inrX_d_assoc, inrX_fstX_assoc, zero_comp, neg_comp, inrX_sndX_assoc,
          comp_neg, d_sndX b (i + 1) i h₃, inrX_sndX, comp_zero, neg_zero, zero_add, add_zero,
          comp_id, inrX_fstX]
        exact en

end ConeHomotopy

lemma coneMap_congr {V : Type*} [Category V] [Preadditive V] [HasBinaryBiproducts V]
    {K L K' L' : ChainComplex V ℤ} {a : K ⟶ L} {b : K' ⟶ L'} {m m' : K ⟶ K'} {n n' : L ⟶ L'}
    (h : m ≫ b = a ≫ n) (hm : m = m') (hn : n = n') :
    coneMap m n h = coneMap m' n' (hm ▸ hn ▸ h) := by
  subst hm hn; rfl



lemma negOnePow_sub_one' (r : ℤ) : (r - 1).negOnePow = -r.negOnePow := by
  rw [show r = r - 1 + 1 by ring, Int.negOnePow_succ]; simp

@[simp]
lemma units_smul_units_smul_self {V : Type*} [Category V] [Preadditive V] {X Y : V} (u : ℤˣ)
    (f : X ⟶ Y) : u • u • f = f := by
  rw [smul_smul, Int.units_mul_self, one_smul]

@[reassoc]
lemma XIsoOfEq_comp_star_d {V : Type*} [Category V] [Preadditive V] (J : StrictInvolution V)
    (K : ChainComplex V ℤ) (a : ℤ) {b b' : ℤ} (h : b = b') :
    (K.XIsoOfEq h).hom ≫ J.star (K.d a b') = J.star (K.d a b) := by
  subst h; simp


@[simp]
lemma star_XIsoOfEq_hom {V : Type*} [Category V] [Preadditive V] (J : StrictInvolution V)
    (K : ChainComplex V ℤ) {a b : ℤ} (h : a = b) : J.star (K.XIsoOfEq h).hom = (K.XIsoOfEq h).inv := by
  subst h; simp

@[simp]
lemma star_XIsoOfEq_inv {V : Type*} [Category V] [Preadditive V] (J : StrictInvolution V)
    (K : ChainComplex V ℤ) {a b : ℤ} (h : a = b) : J.star (K.XIsoOfEq h).inv = (K.XIsoOfEq h).hom := by
  subst h; simp

lemma XIsoOfEq_inv_eq {V : Type*} [Category V] [Preadditive V]
    (K : ChainComplex V ℤ) {a b : ℤ} (h : a = b) : (K.XIsoOfEq h).inv = (K.XIsoOfEq h.symm).hom := by
  subst h; simp

section ConeIdx

variable {V : Type*} [Category V] [Preadditive V] [HasBinaryBiproducts V]
  {K L' : ChainComplex V ℤ} (φ : K ⟶ L')

@[reassoc (attr := simp)]
lemma inlX_fstX' {i k k' : ℤ} (h : (ComplexShape.down ℤ).Rel i k)
    (h' : (ComplexShape.down ℤ).Rel i k') :
    inlX φ k i h ≫ fstX φ i k' h' =
      (K.XIsoOfEq (by simp only [ComplexShape.down_Rel] at h h'; omega)).hom := by
  obtain rfl : k' = k := by simp only [ComplexShape.down_Rel] at h h'; omega
  simp

/-- `inlX_d` with the next index fixed to `j - 1`. -/
@[reassoc]
lemma inlX_d'' {i j : ℤ} (hij : (ComplexShape.down ℤ).Rel i j) :
    inlX φ j i hij ≫ homotopyCofiber.d φ i j =
      -K.d j (j - 1) ≫ inlX φ (j - 1) j (by simp) + φ.f j ≫ inrX φ j :=
  inlX_d φ i j (j - 1) hij (by simp)

variable (J : StrictInvolution V)

@[reassoc]
lemma star_fstX_star_d {i i' k : ℤ} (hi : (ComplexShape.down ℤ).Rel i i')
    (hk : (ComplexShape.down ℤ).Rel i' k) :
    J.star (fstX φ i' k hk) ≫ J.star (homotopyCofiber.d φ i i') =
      -(J.star (K.d i' k) ≫ J.star (fstX φ i i' hi)) := by
  rw [← J.star_comp, d_fstX φ i i' k hi hk, J.star_neg, J.star_comp]

@[reassoc]
lemma star_sndX_star_d {i i' : ℤ} (hi : (ComplexShape.down ℤ).Rel i i') :
    J.star (sndX φ i') ≫ J.star (homotopyCofiber.d φ i i') =
      J.star (φ.f i') ≫ J.star (fstX φ i i' hi) + J.star (L'.d i i') ≫ J.star (sndX φ i) := by
  rw [← J.star_comp, d_sndX φ i i' hi, J.star_add, J.star_comp, J.star_comp]

/-- Maps into `Cone(φ)_i` seen as a dual object are determined by `inlX^*`, `inrX^*`. -/
lemma ext_to_star {i k : ℤ} (h : (ComplexShape.down ℤ).Rel i k) {Z : V}
    {f g : Z ⟶ (homotopyCofiber φ).X i}
    (h₁ : f ≫ J.star (inlX φ k i h) = g ≫ J.star (inlX φ k i h))
    (h₂ : f ≫ J.star (inrX φ i) = g ≫ J.star (inrX φ i)) : f = g := by
  have e (x : Z ⟶ (homotopyCofiber φ).X i) : x = x ≫ J.star (inlX φ k i h) ≫
      J.star (fstX φ i k h) + x ≫ J.star (inrX φ i) ≫ J.star (sndX φ i) := by
    rw [← J.star_comp, ← J.star_comp, ← comp_add, ← J.star_add, ← cone.id_X]
    simp
  rw [e f, e g, reassoc_of% h₁, reassoc_of% h₂]

end ConeIdx


section ConeEqToHom

variable {V : Type*} [Category V] [Preadditive V] [HasBinaryBiproducts V]
  {K L' : ChainComplex V ℤ} (φ : K ⟶ L')

@[reassoc]
lemma inrX_eqToHom' {i i' : ℤ} (h : i = i') :
    inrX φ i ≫ eqToHom (congrArg (homotopyCofiber φ).X h) = (L'.XIsoOfEq h).hom ≫ inrX φ i' := by
  subst h; simp

@[reassoc]
lemma inlX_eqToHom' {k i i' : ℤ} (hk : (ComplexShape.down ℤ).Rel i k) (h : i = i') :
    inlX φ k i hk ≫ eqToHom (congrArg (homotopyCofiber φ).X h) =
      (K.XIsoOfEq (show k = i' - 1 by simp only [ComplexShape.down_Rel] at hk; omega)).hom ≫
        inlX φ (i' - 1) i' (by simp) := by
  subst h
  obtain rfl : k = i - 1 := by simp only [ComplexShape.down_Rel] at hk; omega
  simp

end ConeEqToHom

/-- Discharger for the shape side conditions `(ComplexShape.down ℤ).Rel i j`. -/
macro "down_rel" : tactic => `(tactic| first | omega | (simp only [ComplexShape.down_Rel]; omega))


/-! ### Line data and the line complex -/

/-- **Line data** `(Δ, s)`: a duality-preserving functor with a unitary natural automorphism
(the shift of the cellular line). -/
structure LineData (A B : InvCat) where
  /-- The functor placing an object along the line. -/
  Δ : A ⟶ B
  /-- The shift by one cell. -/
  s : InvCat.UnitaryIso Δ Δ

namespace LineData

variable {A B : InvCat} (L : LineData A B)

@[reassoc (attr := simp)]
lemma s_hom_inv (X : A) : L.s.iso.hom.app X ≫ L.s.iso.inv.app X = 𝟙 _ :=
  L.s.iso.hom_inv_id_app X

@[reassoc (attr := simp)]
lemma s_inv_hom (X : A) : L.s.iso.inv.app X ≫ L.s.iso.hom.app X = 𝟙 _ :=
  L.s.iso.inv_hom_id_app X

@[reassoc (attr := simp)]
lemma s_hom_nat {X Y : A} (f : X ⟶ Y) :
    L.Δ.F.map f ≫ L.s.iso.hom.app Y = L.s.iso.hom.app X ≫ L.Δ.F.map f :=
  L.s.iso.hom.naturality f

@[reassoc (attr := simp)]
lemma s_inv_nat {X Y : A} (f : X ⟶ Y) :
    L.Δ.F.map f ≫ L.s.iso.inv.app Y = L.s.iso.inv.app X ≫ L.Δ.F.map f :=
  L.s.iso.inv.naturality f

@[simp]
lemma star_s_hom (X : A) : B.inv.star (L.s.iso.hom.app X) = L.s.iso.inv.app X :=
  L.s.star_hom X

@[simp]
lemma star_s_inv (X : A) : B.inv.star (L.s.iso.inv.app X) = L.s.iso.hom.app X :=
  L.s.star_inv X

/-- `s - 1 : ΔC ⟶ ΔC`, the differential of the line. -/
def g (C : ChainComplex A ℤ) : L.Δ.mapC C ⟶ L.Δ.mapC C where
  f i := L.s.iso.hom.app (C.X i) - 𝟙 _
  comm' i j _ := by simp [sub_comp, comp_sub]

@[simp] lemma g_f (C : ChainComplex A ℤ) (i : ℤ) :
    (L.g C).f i = L.s.iso.hom.app (C.X i) - 𝟙 _ := rfl

/-- **The line complex** `C ⊗ C(ℝ) = Cone(s - 1 : ΔC ⟶ ΔC)`. -/
abbrev cx (C : ChainComplex A ℤ) : ChainComplex B ℤ := cone (L.g C)

lemma mapH_comp_g {C D : ChainComplex A ℤ} (f : C ⟶ D) :
    L.Δ.mapH f ≫ L.g D = L.g C ≫ L.Δ.mapH f := by
  ext i; simp [sub_comp, comp_sub]

/-- A chain map acts diagonally on the line complexes. -/
def map {C D : ChainComplex A ℤ} (f : C ⟶ D) : L.cx C ⟶ L.cx D :=
  coneMap (L.Δ.mapH f) (L.Δ.mapH f) (L.mapH_comp_g f)

variable {L}

@[reassoc (attr := simp)]
lemma inlX_map {C D : ChainComplex A ℤ} (f : C ⟶ D) (i k : ℤ)
    (hk : (ComplexShape.down ℤ).Rel i k) :
    inlX (L.g C) k i hk ≫ (L.map f).f i = L.Δ.F.map (f.f k) ≫ inlX (L.g D) k i hk :=
  inlX_coneMap_f _ i k hk

@[reassoc (attr := simp)]
lemma inrX_map {C D : ChainComplex A ℤ} (f : C ⟶ D) (i : ℤ) :
    inrX (L.g C) i ≫ (L.map f).f i = L.Δ.F.map (f.f i) ≫ inrX (L.g D) i :=
  inrX_coneMap_f _ i

@[reassoc (attr := simp)]
lemma map_fstX {C D : ChainComplex A ℤ} (f : C ⟶ D) (i k : ℤ)
    (hk : (ComplexShape.down ℤ).Rel i k) :
    (L.map f).f i ≫ fstX (L.g D) i k hk = fstX (L.g C) i k hk ≫ L.Δ.F.map (f.f k) :=
  coneMap_f_fstX _ i k hk

@[reassoc (attr := simp)]
lemma map_sndX {C D : ChainComplex A ℤ} (f : C ⟶ D) (i : ℤ) :
    (L.map f).f i ≫ sndX (L.g D) i = sndX (L.g C) i ≫ L.Δ.F.map (f.f i) :=
  coneMap_f_sndX _ i

variable (L)

@[reassoc (attr := simp)]
lemma map_comp {C D E : ChainComplex A ℤ} (f : C ⟶ D) (f' : D ⟶ E) :
    L.map (f ≫ f') = L.map f ≫ L.map f' := by
  rw [map, map, map, coneMap_comp]
  exact coneMap_congr _ (Functor.map_comp _ _ _) (Functor.map_comp _ _ _)

@[simp]
lemma map_id (C : ChainComplex A ℤ) : L.map (𝟙 C) = 𝟙 _ := by
  rw [map, coneMap_congr _ ((L.Δ.F.mapHomologicalComplex _).map_id C)
    ((L.Δ.F.mapHomologicalComplex _).map_id C)]
  exact coneMap_id _

@[simp]
lemma map_add {C D : ChainComplex A ℤ} (f f' : C ⟶ D) :
    L.map (f + f') = L.map f + L.map f' := by
  rw [map, map, map, ← coneMap_add]
  exact coneMap_congr _ (Functor.map_add _) (Functor.map_add _)

@[simp]
lemma map_zero (C D : ChainComplex A ℤ) : L.map (0 : C ⟶ D) = 0 := by
  rw [map, ← coneMap_zero]
  exact coneMap_congr _ (Functor.map_zero _ _ _) (Functor.map_zero _ _ _)

@[simp]
lemma map_neg {C D : ChainComplex A ℤ} (f : C ⟶ D) : L.map (-f) = -L.map f := by
  rw [eq_neg_iff_add_eq_zero, ← map_add, neg_add_cancel, map_zero]

/-- A homotopy acts diagonally on the line complexes. -/
def htpy {C D : ChainComplex A ℤ} {f f' : C ⟶ D} (H : Homotopy f f') :
    Homotopy (L.map f) (L.map f') :=
  coneMapHomotopy _ _ (L.Δ.F.mapHomotopy H) (L.Δ.F.mapHomotopy H) fun i k ↦ by
    simp [sub_comp, comp_sub]


@[reassoc]
lemma s_hom_XIsoOfEq (C : ChainComplex A ℤ) {a b : ℤ} (h : a = b) :
    L.s.iso.hom.app (C.X a) ≫ ((L.Δ.mapC C).XIsoOfEq h).hom =
      ((L.Δ.mapC C).XIsoOfEq h).hom ≫ L.s.iso.hom.app (C.X b) := by
  subst h; simp

@[reassoc]
lemma s_inv_XIsoOfEq (C : ChainComplex A ℤ) {a b : ℤ} (h : a = b) :
    L.s.iso.inv.app (C.X a) ≫ ((L.Δ.mapC C).XIsoOfEq h).hom =
      ((L.Δ.mapC C).XIsoOfEq h).hom ≫ L.s.iso.inv.app (C.X b) := by
  subst h; simp

@[reassoc]
lemma s_hom_XIsoOfEq_inv (C : ChainComplex A ℤ) {a b : ℤ} (h : b = a) :
    L.s.iso.hom.app (C.X a) ≫ ((L.Δ.mapC C).XIsoOfEq h).inv =
      ((L.Δ.mapC C).XIsoOfEq h).inv ≫ L.s.iso.hom.app (C.X b) := by
  subst h; simp

@[reassoc]
lemma s_inv_XIsoOfEq_inv (C : ChainComplex A ℤ) {a b : ℤ} (h : b = a) :
    L.s.iso.inv.app (C.X a) ≫ ((L.Δ.mapC C).XIsoOfEq h).inv =
      ((L.Δ.mapC C).XIsoOfEq h).inv ≫ L.s.iso.inv.app (C.X b) := by
  subst h; simp

@[reassoc]
lemma s_hom_map {X Y : A} (f : X ⟶ Y) :
    L.s.iso.hom.app X ≫ L.Δ.F.map f = L.Δ.F.map f ≫ L.s.iso.hom.app Y :=
  (L.s.iso.hom.naturality f).symm

@[reassoc]
lemma s_inv_map {X Y : A} (f : X ⟶ Y) :
    L.s.iso.inv.app X ≫ L.Δ.F.map f = L.Δ.F.map f ≫ L.s.iso.inv.app Y :=
  (L.s.iso.inv.naturality f).symm

@[reassoc]
lemma s_hom_star_map {X Y : A} (f : X ⟶ Y) :
    L.s.iso.hom.app Y ≫ B.inv.star (L.Δ.F.map f) = B.inv.star (L.Δ.F.map f) ≫ L.s.iso.hom.app X := by
  rw [← L.Δ.map_star]; exact (L.s.iso.hom.naturality _).symm

@[reassoc]
lemma s_inv_star_map {X Y : A} (f : X ⟶ Y) :
    L.s.iso.inv.app Y ≫ B.inv.star (L.Δ.F.map f) = B.inv.star (L.Δ.F.map f) ≫ L.s.iso.inv.app X := by
  rw [← L.Δ.map_star]; exact (L.s.iso.inv.naturality _).symm

@[reassoc]
lemma XIsoOfEq_map {C D : ChainComplex A ℤ} (f : C ⟶ D) {a b : ℤ} (h : a = b) :
    ((L.Δ.mapC C).XIsoOfEq h).hom ≫ L.Δ.F.map (f.f b) =
      L.Δ.F.map (f.f a) ≫ ((L.Δ.mapC D).XIsoOfEq h).hom := by
  subst h; simp

@[reassoc]
lemma XIsoOfEq_star_map {C D : ChainComplex A ℤ} (f : C ⟶ D) {a b : ℤ} (h : a = b) :
    ((L.Δ.mapC D).XIsoOfEq h).hom ≫ B.inv.star (L.Δ.F.map (f.f b)) =
      B.inv.star (L.Δ.F.map (f.f a)) ≫ ((L.Δ.mapC C).XIsoOfEq h).hom := by
  subst h; simp

@[reassoc]
lemma XIsoOfEq_inv_star_map {C D : ChainComplex A ℤ} (f : C ⟶ D) {a b : ℤ} (h : b = a) :
    ((L.Δ.mapC D).XIsoOfEq h).inv ≫ B.inv.star (L.Δ.F.map (f.f b)) =
      B.inv.star (L.Δ.F.map (f.f a)) ≫ ((L.Δ.mapC C).XIsoOfEq h).inv := by
  subst h; simp

@[reassoc]
lemma XIsoOfEq_inv_map {C D : ChainComplex A ℤ} (f : C ⟶ D) {a b : ℤ} (h : b = a) :
    ((L.Δ.mapC C).XIsoOfEq h).inv ≫ L.Δ.F.map (f.f b) =
      L.Δ.F.map (f.f a) ≫ ((L.Δ.mapC D).XIsoOfEq h).inv := by
  subst h; simp

variable {L} in
@[reassoc]
lemma star_fstX_star_map {C D : ChainComplex A ℤ} (f : C ⟶ D) {i k : ℤ}
    (hk : (ComplexShape.down ℤ).Rel i k) :
    B.inv.star (fstX (L.g D) i k hk) ≫ B.inv.star ((L.map f).f i) =
      B.inv.star (L.Δ.F.map (f.f k)) ≫ B.inv.star (fstX (L.g C) i k hk) := by
  rw [← B.inv.star_comp, map_fstX, B.inv.star_comp]

variable {L} in
@[reassoc]
lemma star_sndX_star_map {C D : ChainComplex A ℤ} (f : C ⟶ D) (i : ℤ) :
    B.inv.star (sndX (L.g D) i) ≫ B.inv.star ((L.map f).f i) =
      B.inv.star (L.Δ.F.map (f.f i)) ≫ B.inv.star (sndX (L.g C) i) := by
  rw [← B.inv.star_comp, map_sndX, B.inv.star_comp]

@[reassoc]
lemma XIsoOfEq_map_fam {C D : ChainComplex A ℤ} (F : ∀ i j, C.X i ⟶ D.X j) {a a' : ℤ}
    (h : a = a') (b : ℤ) :
    ((L.Δ.mapC C).XIsoOfEq h).hom ≫ L.Δ.F.map (F a' b) = L.Δ.F.map (F a b) := by
  subst h; simp

@[reassoc]
lemma map_fam_XIsoOfEq {C D : ChainComplex A ℤ} (F : ∀ i j, C.X i ⟶ D.X j) (a : ℤ) {b b' : ℤ}
    (h : b = b') :
    L.Δ.F.map (F a b) ≫ ((L.Δ.mapC D).XIsoOfEq h).hom = L.Δ.F.map (F a b') := by
  subst h; simp

@[reassoc]
lemma XIsoOfEq_star_map_fam {C D : ChainComplex A ℤ} (F : ∀ i j, C.X i ⟶ D.X j) {b b' : ℤ}
    (h : b = b') (a : ℤ) :
    ((L.Δ.mapC D).XIsoOfEq h).hom ≫ B.inv.star (L.Δ.F.map (F a b')) =
      B.inv.star (L.Δ.F.map (F a b)) := by
  subst h; simp

@[reassoc]
lemma star_map_fam_XIsoOfEq {C D : ChainComplex A ℤ} (F : ∀ i j, C.X i ⟶ D.X j) (b : ℤ)
    {a a' : ℤ} (h : a = a') :
    B.inv.star (L.Δ.F.map (F a b)) ≫ ((L.Δ.mapC C).XIsoOfEq h).hom =
      B.inv.star (L.Δ.F.map (F a' b)) := by
  subst h; simp


lemma mapC_dual_XIsoOfEq (C : ChainComplex A ℤ) {a b : ℤ} (h : a = b) :
    (L.Δ.mapC (dualComplex A.inv M C)).XIsoOfEq h =
      (L.Δ.mapC C).XIsoOfEq (show M - a = M - b by omega) := by
  subst h; rfl

lemma map_eqToHom_X (C : ChainComplex A ℤ) {a b : ℤ} (h : a = b) :
    L.Δ.F.map (eqToHom (congrArg C.X h)) = ((L.Δ.mapC C).XIsoOfEq h).hom := by
  subst h; simp

lemma mapC_dual_d (M : ℤ) (C : ChainComplex A ℤ) (r r' : ℤ) :
    (L.Δ.mapC (dualComplex A.inv M C)).d r r' =
      r.negOnePow • B.inv.star ((L.Δ.mapC C).d (M - r') (M - r)) := by
  simp [Functor.map_units_smul, L.Δ.map_star]


@[reassoc]
lemma s_hom_star_d (C : ChainComplex A ℤ) (a b : ℤ) :
    L.s.iso.hom.app (C.X b) ≫ B.inv.star ((L.Δ.mapC C).d a b) =
      B.inv.star ((L.Δ.mapC C).d a b) ≫ L.s.iso.hom.app (C.X a) := by
  simp only [InvFunctor.mapC, Functor.mapHomologicalComplex_obj_d, ← L.Δ.map_star]
  exact (L.s.iso.hom.naturality _).symm

@[reassoc]
lemma s_inv_star_d (C : ChainComplex A ℤ) (a b : ℤ) :
    L.s.iso.inv.app (C.X b) ≫ B.inv.star ((L.Δ.mapC C).d a b) =
      B.inv.star ((L.Δ.mapC C).d a b) ≫ L.s.iso.inv.app (C.X a) := by
  simp only [InvFunctor.mapC, Functor.mapHomologicalComplex_obj_d, ← L.Δ.map_star]
  exact (L.s.iso.inv.naturality _).symm

/-! ### The duality of the line -/

variable (a b : ℚ)

/-- The coefficient `a + b s`. -/
abbrev cf (X : A) : L.Δ.F.obj X ⟶ L.Δ.F.obj X := a • 𝟙 _ + b • L.s.iso.hom.app X

/-- The coefficient `(a + b s) s⁻¹ = a s⁻¹ + b`. -/
abbrev cf' (X : A) : L.Δ.F.obj X ⟶ L.Δ.F.obj X := a • L.s.iso.inv.app X + b • 𝟙 _

variable (M : ℤ)

/-- `θ_{a+bs} : (C ⊗ ℝ)^{M+1-*} ⟶ C^{M-*} ⊗ ℝ`, `(e', v') ↦ ((a + bs)s⁻¹ v', (-1)^r (a + bs) e')`:
the dual of the line, with the cap `e^* ↦ (a + b s) v`. -/
def θ (C : ChainComplex A ℤ) :
    dualComplex B.inv (M + 1) (L.cx C) ⟶ L.cx (dualComplex A.inv M C) where
  f r := B.inv.star (inrX (L.g C) (M + 1 - r)) ≫
      ((L.Δ.mapC C).XIsoOfEq (show M + 1 - r = M - (r - 1) by omega)).hom ≫
        L.cf' a b (C.X (M - (r - 1))) ≫ inlX (L.g (dualComplex A.inv M C)) (r - 1) r (by simp) +
    r.negOnePow • (B.inv.star (inlX (L.g C) (M - r) (M + 1 - r) (down_rel_sub M r)) ≫
      L.cf a b (C.X (M - r)) ≫ inrX (L.g (dualComplex A.inv M C)) r)
  comm' r r' h := by
    obtain rfl : r' = r - 1 := by simp only [ComplexShape.down_Rel] at h; omega
    have h₁ : (ComplexShape.down ℤ).Rel (M + 1 - (r - 1)) (M + 1 - r) := by
      simp only [ComplexShape.down_Rel]; omega
    have h₂ : (ComplexShape.down ℤ).Rel (r - 1) (r - 1 - 1) := by simp
    apply cone.ext_star (J := B.inv) (L.g C) _ _ (down_rel_sub M r)
    all_goals apply ext_to_X (L.g (dualComplex A.inv M C)) (r - 1) (r - 1 - 1) h₂
    all_goals simp only [dualComplex_d, comp_add, add_comp, assoc, Linear.comp_units_smul,
          Linear.units_smul_comp, cone.star_fstX_inrX_assoc, cone.star_fstX_inlX_assoc,
          cone.star_sndX_inrX_assoc, cone.star_sndX_inlX_assoc,
          cone.star_fstX_d_assoc _ _ _ _ h₁ (down_rel_sub M r),
          cone.star_sndX_d_assoc _ _ _ h₁,
          cone.star_fstX_inlX'_assoc (L.g C) h₁ (down_rel_sub M (r - 1)), neg_comp, zero_comp,
          comp_zero, smul_zero, zero_add, add_zero]
    all_goals simp only [homotopyCofiber_d, comp_add, add_comp, assoc,
          inlX_d_assoc _ r (r - 1) (r - 1 - 1) h h₂, inrX_d_assoc, inrX_fstX, inrX_sndX,
          inlX_fstX, inlX_sndX, inrX_fstX_assoc, inrX_sndX_assoc,
          inlX_fstX_assoc, inlX_sndX_assoc, d_fstX _ _ _ _ h h₂, d_sndX _ _ _ h, Linear.smul_comp,
          id_comp, comp_id, Linear.comp_smul, Linear.comp_units_smul, Linear.units_smul_comp,
          neg_comp, zero_comp, comp_neg, comp_zero, smul_zero, zero_add, add_zero, smul_neg,
          neg_zero, mapC_dual_d, g_f, B.inv.star_sub, star_s_hom, B.inv.star_id, sub_comp,
          comp_sub]
    all_goals dsimp only [dualComplex_X, InvFunctor.mapC, Functor.mapHomologicalComplex_obj_X]
    all_goals simp only [comp_id, id_comp, B.inv.star_id, sub_self, smul_zero, zero_add, add_zero,
      star_d_XIsoOfEq, star_d_XIsoOfEq_assoc, s_hom_XIsoOfEq_assoc, s_inv_XIsoOfEq_assoc,
      s_hom_star_d_assoc, s_inv_star_d_assoc, s_inv_hom, s_hom_inv, s_inv_hom_assoc,
      s_hom_inv_assoc, s_hom_star_d, s_inv_star_d, s_hom_XIsoOfEq, s_inv_XIsoOfEq,
      XIsoOfEq_comp_star_d, XIsoOfEq_comp_star_d_assoc, negOnePow_sub_one', Units.neg_smul,
      units_smul_units_smul_self, neg_neg, smul_neg, smul_add, smul_sub, neg_add_rev]
    all_goals (try erw [Category.comp_id]); abel

@[simp]
lemma θ_f (C : ChainComplex A ℤ) (r : ℤ) :
    (L.θ a b M C).f r = B.inv.star (inrX (L.g C) (M + 1 - r)) ≫
      ((L.Δ.mapC C).XIsoOfEq (show M + 1 - r = M - (r - 1) by omega)).hom ≫
        L.cf' a b (C.X (M - (r - 1))) ≫ inlX (L.g (dualComplex A.inv M C)) (r - 1) r (by simp) +
    r.negOnePow • (B.inv.star (inlX (L.g C) (M - r) (M + 1 - r) (down_rel_sub M r)) ≫
      L.cf a b (C.X (M - r)) ≫ inrX (L.g (dualComplex A.inv M C)) r) := rfl

/-- `θ_{a+bs} ≃ θ_{a+b}`: the difference `b θ_{s-1}` is null-homotopic via
`(e', v') ↦ ((-1)^r b e', 0)`. -/
def θHtpy (C : ChainComplex A ℤ) : Homotopy (L.θ a b M C) (L.θ (a + b) 0 M C) where
  hom r r' := if hr : (ComplexShape.down ℤ).Rel r' r then
      b • r.negOnePow • (B.inv.star (inlX (L.g C) (M - r) (M + 1 - r) (down_rel_sub M r)) ≫
        inlX (L.g (dualComplex A.inv M C)) r r' hr)
    else 0
  zero r r' hr := dif_neg hr
  comm r := by
    have h₀ : (ComplexShape.down ℤ).Rel r (r - 1) := by simp
    have h₃ : (ComplexShape.down ℤ).Rel (r + 1) r := by simp
    have h₁ : (ComplexShape.down ℤ).Rel (M + 1 - (r - 1)) (M + 1 - r) := by
      simp only [ComplexShape.down_Rel]; omega
    have h₁' : (ComplexShape.down ℤ).Rel (M + 1 - r) (M + 1 - (r + 1)) := by
      simp only [ComplexShape.down_Rel]; omega
    rw [dNext_eq _ h₀, prevD_eq _ h₃, dif_pos h₀, dif_pos h₃]
    apply cone.ext_star (J := B.inv) (L.g C) _ _ (down_rel_sub M r)
    all_goals apply ext_to_X (L.g (dualComplex A.inv M C)) r (r - 1) h₀
    all_goals simp only [dualComplex_d, comp_add, add_comp, assoc, Linear.comp_units_smul,
          Linear.units_smul_comp, Linear.comp_smul, Linear.smul_comp, θ_f,
          cone.star_fstX_inrX_assoc, cone.star_fstX_inlX_assoc,
          cone.star_sndX_inrX_assoc, cone.star_sndX_inlX_assoc,
          cone.star_fstX_d_assoc _ _ _ _ h₁ (down_rel_sub M r),
          cone.star_sndX_d_assoc _ _ _ h₁,
          cone.star_fstX_inlX'_assoc (L.g C) h₁ (down_rel_sub M (r - 1)), neg_comp, zero_comp,
          comp_zero, smul_zero, zero_add, add_zero]
    all_goals simp only [homotopyCofiber_d, comp_add, add_comp, assoc,
          inlX_d_assoc _ (r + 1) r (r - 1) h₃ h₀, inrX_d_assoc, inrX_fstX, inrX_sndX,
          inlX_fstX, inlX_sndX, inrX_fstX_assoc, inrX_sndX_assoc,
          inlX_fstX_assoc, inlX_sndX_assoc, d_fstX _ _ _ _ h₃ h₀, d_sndX _ _ _ h₃, Linear.smul_comp,
          id_comp, comp_id, Linear.comp_smul, Linear.comp_units_smul, Linear.units_smul_comp,
          neg_comp, zero_comp, comp_neg, comp_zero, smul_zero, zero_add, add_zero, smul_neg,
          neg_zero, mapC_dual_d, g_f, B.inv.star_sub, star_s_hom, B.inv.star_id, sub_comp,
          comp_sub, zero_smul]
    all_goals try dsimp only [dualComplex_X, Functor.mapHomologicalComplex_obj_X]
    all_goals try simp only [comp_id, id_comp, B.inv.star_id, sub_self, smul_zero, zero_add, add_zero,
      star_d_XIsoOfEq, star_d_XIsoOfEq_assoc, s_hom_XIsoOfEq_assoc, s_inv_XIsoOfEq_assoc,
      s_hom_star_d_assoc, s_inv_star_d_assoc, s_inv_hom, s_hom_inv, s_inv_hom_assoc,
      s_hom_inv_assoc, s_hom_star_d, s_inv_star_d, s_hom_XIsoOfEq, s_inv_XIsoOfEq,
      XIsoOfEq_comp_star_d, XIsoOfEq_comp_star_d_assoc, negOnePow_sub_one', Units.neg_smul,
      units_smul_units_smul_self, neg_neg, smul_neg, smul_add, smul_sub, neg_add_rev, add_smul,
      units_smul_rat_smul]
    all_goals abel

/-- Normal form for components of maps between line complexes and their duals: expand
compositions into cone coordinates, move shifts to the right and absorb index casts. -/
macro "line_simp_core" : tactic => `(tactic|
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
    LineData.g_f, LineData.mapC_dual_d, StrictInvolution.star_sub, StrictInvolution.star_neg,
    LineData.star_s_hom, LineData.star_s_inv, StrictInvolution.star_id,
    StrictInvolution.star_zero, star_d_XIsoOfEq_assoc, star_d_XIsoOfEq,
    XIsoOfEq_comp_star_d_assoc, XIsoOfEq_comp_star_d, LineData.s_hom_XIsoOfEq_assoc,
    LineData.s_hom_XIsoOfEq, LineData.s_inv_XIsoOfEq_assoc, LineData.s_inv_XIsoOfEq,
    LineData.s_hom_star_d_assoc, LineData.s_hom_star_d, LineData.s_inv_star_d_assoc,
    LineData.s_inv_star_d, LineData.s_hom_inv_assoc, LineData.s_hom_inv,
    LineData.s_inv_hom_assoc, LineData.s_inv_hom, LineData.s_hom_XIsoOfEq_inv_assoc,
    LineData.s_hom_XIsoOfEq_inv, LineData.s_inv_XIsoOfEq_inv_assoc, LineData.s_inv_XIsoOfEq_inv,
    Iso.inv_hom_id, Iso.hom_inv_id, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
    LineData.s_hom_map_assoc, LineData.s_hom_map, LineData.s_inv_map_assoc, LineData.s_inv_map,
    LineData.s_hom_star_map_assoc, LineData.s_hom_star_map, LineData.s_inv_star_map_assoc,
    LineData.s_inv_star_map, LineData.XIsoOfEq_map_assoc, LineData.XIsoOfEq_map,
    LineData.XIsoOfEq_star_map_assoc, LineData.XIsoOfEq_star_map,
    LineData.XIsoOfEq_inv_star_map_assoc, LineData.XIsoOfEq_inv_star_map,
    LineData.XIsoOfEq_inv_map_assoc, LineData.XIsoOfEq_inv_map,
    LineData.star_fstX_star_map_assoc, LineData.star_fstX_star_map,
    LineData.star_sndX_star_map_assoc, LineData.star_sndX_star_map,
    LineData.inlX_map_assoc, LineData.inlX_map, LineData.inrX_map_assoc, LineData.inrX_map,
    LineData.map_fstX_assoc, LineData.map_fstX, LineData.map_sndX_assoc, LineData.map_sndX,
    InvFunctor.map_star, dualHom_f, comp_f, bidual_hom_f, Functor.map_units_smul,
    LineData.map_eqToHom_X, LineData.mapC_dual_XIsoOfEq, star_XIsoOfEq_hom, star_XIsoOfEq_inv,
    XIsoOfEq_inv_eq, XIsoOfEq_hom_comp_XIsoOfEq_hom_assoc, XIsoOfEq_hom_comp_XIsoOfEq_hom,
    XIsoOfEq_rfl, Iso.refl_hom, LineData.XIsoOfEq_map_fam_assoc, LineData.XIsoOfEq_map_fam,
    LineData.map_fam_XIsoOfEq_assoc, LineData.map_fam_XIsoOfEq,
    LineData.XIsoOfEq_star_map_fam_assoc, LineData.XIsoOfEq_star_map_fam,
    LineData.star_map_fam_XIsoOfEq_assoc, LineData.star_map_fam_XIsoOfEq])

/-- `line_simp_core`, then normalize objects and repeat. -/
macro "line_simp" : tactic => `(tactic| (
  (try line_simp_core) <;>
  (try dsimp only [dualComplex_X, Functor.mapHomologicalComplex_obj_X, homotopyCofiber_X]) <;>
  (try line_simp_core) <;>
  (try (dsimp only [dualComplex_X, InvFunctor.mapC, Functor.mapHomologicalComplex_obj_X,
    homotopyCofiber_X]; done))))

/-- The inverse of `θ_1`: `(e, v) ↦ ((-1)^r v, s e)`. -/
def θinvf (C : ChainComplex A ℤ) (r : ℤ) :
    (L.cx (dualComplex A.inv M C)).X r ⟶ (dualComplex B.inv (M + 1) (L.cx C)).X r :=
  r.negOnePow • (sndX (L.g (dualComplex A.inv M C)) r ≫
      B.inv.star (fstX (L.g C) (M + 1 - r) (M - r) (down_rel_sub M r))) +
    fstX (L.g (dualComplex A.inv M C)) r (r - 1) (by simp) ≫
      ((L.Δ.mapC C).XIsoOfEq (show M + 1 - r = M - (r - 1) by omega)).inv ≫
        L.s.iso.hom.app (C.X (M + 1 - r)) ≫ B.inv.star (sndX (L.g C) (M + 1 - r))

lemma θ_θinvf (C : ChainComplex A ℤ) (r : ℤ) : (L.θ 1 0 M C).f r ≫ L.θinvf M C r = 𝟙 _ := by
  apply cone.ext_star (J := B.inv) (L.g C) _ _ (down_rel_sub M r)
  all_goals apply ext_to_star (L.g C) B.inv (down_rel_sub M r)
  all_goals simp only [θ_f, θinvf]
  all_goals line_simp

lemma θinvf_θ (C : ChainComplex A ℤ) (r : ℤ) : L.θinvf M C r ≫ (L.θ 1 0 M C).f r = 𝟙 _ := by
  apply ext_from_X (L.g (dualComplex A.inv M C)) (r - 1) r (by simp)
  all_goals apply ext_to_X (L.g (dualComplex A.inv M C)) r (r - 1) (by simp)
  all_goals simp only [θ_f, θinvf]
  all_goals line_simp

/-- `θ_1` is an isomorphism. -/
def θIso (C : ChainComplex A ℤ) :
    dualComplex B.inv (M + 1) (L.cx C) ≅ L.cx (dualComplex A.inv M C) :=
  Hom.isoOfComponents (fun r ↦ ⟨(L.θ 1 0 M C).f r, L.θinvf M C r, L.θ_θinvf M C r,
    L.θinvf_θ M C r⟩) (fun r r' _ ↦ (L.θ 1 0 M C).comm r r')

@[simp]
lemma θIso_hom (C : ChainComplex A ℤ) : (L.θIso M C).hom = L.θ 1 0 M C := by ext; rfl

/-- Naturality of `θ`. -/
lemma θ_natural {C D : ChainComplex A ℤ} (f : C ⟶ D) :
    dualHom B.inv (M + 1) (L.map f) ≫ L.θ a b M C = L.θ a b M D ≫ L.map (dualHom A.inv M f) := by
  ext r
  apply cone.ext_star (J := B.inv) (L.g D) _ _ (down_rel_sub M r)
  all_goals apply ext_to_X (L.g (dualComplex A.inv M C)) r (r - 1) (by simp)
  all_goals simp only [comp_f, dualHom_f, θ_f]
  all_goals line_simp

lemma θ_natural_assoc {C D : ChainComplex A ℤ} (f : C ⟶ D) {Z : ChainComplex B ℤ}
    (h : L.cx (dualComplex A.inv M C) ⟶ Z) :
    dualHom B.inv (M + 1) (L.map f) ≫ L.θ a b M C ≫ h =
      L.θ a b M D ≫ L.map (dualHom A.inv M f) ≫ h := by
  rw [← assoc, θ_natural, assoc]


/-- The transpose of `θ_{a+bs}` is `θ_{b+as}`. -/
lemma θ_transpose (C : ChainComplex A ℤ) :
    dualHom B.inv (M + 1) (L.θ a b M C) ≫ (bidual B.inv (M + 1) (L.cx C)).hom =
      L.θ b a M (dualComplex A.inv M C) ≫ L.map (bidual A.inv M C).hom := by
  ext r
  apply cone.ext_star (J := B.inv) (L.g (dualComplex A.inv M C)) _ _ (down_rel_sub M r)
  all_goals apply ext_to_X (L.g C) r (r - 1) (by simp)
  all_goals simp only [comp_f, dualHom_f, θ_f, bidual_hom_f, B.inv.star_add, B.inv.star_comp,
    B.inv.star_units_smul, B.inv.star_star, star_rat_smul, Linear.units_smul_comp,
    Linear.comp_units_smul, assoc, add_comp, Linear.smul_comp, Linear.comp_smul]
  all_goals simp (disch := down_rel) only [inrX_eqToHom'_assoc, inlX_eqToHom'_assoc,
    Functor.map_units_smul, map_eqToHom_X, mapC_dual_XIsoOfEq]
  all_goals line_simp
  · rw [show (r * (M + 1 - r)).negOnePow = r.negOnePow * (r * (M - r)).negOnePow by
      rw [← Int.negOnePow_add]; congr 1; ring]
    simp only [mul_smul]
    abel
  · have e : (r * (M + 1 - r)).negOnePow * (M + 1 - r).negOnePow =
        ((r - 1) * (M - (r - 1))).negOnePow := by
      rw [← Int.negOnePow_add]; exact negOnePow_eq_of_eq (M + 1 - r) (by ring)
    simp only [smul_smul, e]
    abel

/-! ### The symmetric duality and Poincaré complexes over the line -/

/-- The strictly symmetric duality `θ_{(1+s)/2}` of the line. -/
abbrev θs (C : ChainComplex A ℤ) :
    dualComplex B.inv (M + 1) (L.cx C) ⟶ L.cx (dualComplex A.inv M C) :=
  L.θ (1 / 2) (1 / 2) M C

lemma θs_transpose (C : ChainComplex A ℤ) :
    dualHom B.inv (M + 1) (L.θs M C) ≫ (bidual B.inv (M + 1) (L.cx C)).hom =
      L.θs M (dualComplex A.inv M C) ≫ L.map (bidual A.inv M C).hom :=
  L.θ_transpose _ _ M C

/-- `θ_{(1+s)/2} ≃ θ_1`. -/
def θsHtpy (C : ChainComplex A ℤ) : Homotopy (L.θs M C) (L.θ 1 0 M C) :=
  homotopyCongr (L.θHtpy (1 / 2) (1 / 2) M C) rfl (by norm_num)

lemma transposeHom_θs_map {C : ChainComplex A ℤ} {N : ℤ} (φ : dualComplex A.inv N C ⟶ C) :
    transposeHom B.inv (N + 1) (L.θs N C ≫ L.map φ) =
      L.θs N C ≫ L.map (transposeHom A.inv N φ) := by
  rw [transposeHom, dualHom_comp, assoc, θs_transpose, θ_natural_assoc, ← map_comp,
    transposeHom]

lemma map_supportedIn {C : ChainComplex A ℤ} {p : C ⟶ C} {lo hi : ℤ}
    (hp : SupportedIn p lo hi) : SupportedIn (L.map p) lo (hi + 1) := fun r hr ↦ by
  apply ext_from_X (L.g C) (r - 1) r (by simp)
  · simp [hp (r - 1) (by omega)]
  · simp [hp r (by omega)]

/-- The inverse of `θ_1` is natural. -/
@[reassoc]
lemma θIso_inv_natural {C D : ChainComplex A ℤ} (f : C ⟶ D) :
    (L.θIso M D).inv ≫ dualHom B.inv (M + 1) (L.map f) =
      L.map (dualHom A.inv M f) ≫ (L.θIso M C).inv := by
  rw [Iso.inv_comp_eq, ← assoc, Iso.eq_comp_inv, θIso_hom, θIso_hom, θ_natural]

variable {M} in
/-- `θ_1 ≫ Φ` is a Kar equivalence when `Φ` is. -/
lemma isKarEquiv_θ_map {C D : ChainComplex A ℤ} {e : dualComplex A.inv M C ⟶ dualComplex A.inv M C}
    {e' : D ⟶ D} {Ψ : dualComplex A.inv M C ⟶ D} (h : IsKarEquiv e e' Ψ) :
    IsKarEquiv (L.map e) (L.map e') (L.map Ψ) := by
  obtain ⟨g, hg, ⟨H₁⟩, ⟨H₂⟩⟩ := h
  exact ⟨L.map g, by rw [← map_comp, ← map_comp, hg],
    ⟨homotopyCongr (L.htpy H₁) (map_comp _ _ _) rfl⟩,
    ⟨homotopyCongr (L.htpy H₂) (map_comp _ _ _) rfl⟩⟩

variable {N : ℤ}

/-- **`P ⊗ ℝ`**: the line complex of a Poincaré complex with the averaged duality
`θ_{(1+s)/2} ≫ (φ ⊗ 1)`. -/
@[implicit_reducible]
def sym (P : SymPoincare A.inv N) : SymPoincare B.inv (N + 1) where
  C := L.cx P.C
  p := L.map P.p
  p_idem := by rw [← map_comp, P.p_idem]
  support := L.map_supportedIn P.support
  φ := L.θs N P.C ≫ L.map P.φ
  φ_kar := by simp only [assoc]; rw [θ_natural_assoc, ← map_comp, ← map_comp, P.φ_kar]
  symm := by rw [IsStrictSymm, transposeHom_θs_map, P.transposeHom_φ]
  poincare := by
    obtain ⟨ψ, hψ, ⟨H₁⟩, ⟨H₂⟩⟩ := P.poincare
    refine IsPoincare.of_homotopy (φ := L.θ 1 0 N P.C ≫ L.map P.φ) ?_
      (((L.θsHtpy N P.C).compRight (L.map P.φ)).symm)
    refine ⟨L.map ψ ≫ (L.θIso N P.C).inv, ?_, ⟨?_⟩, ⟨?_⟩⟩
    · rw [assoc, θIso_inv_natural, ← map_comp_assoc, ← map_comp_assoc, assoc, hψ]
    · refine homotopyCongr (L.htpy H₁) ?_ rfl
      rw [map_comp, assoc, ← θIso_hom, Iso.inv_hom_id_assoc]
    · refine homotopyCongr (((L.htpy H₂).compLeft (L.θIso N P.C).hom).compRight
        (L.θIso N P.C).inv) ?_ ?_
      · simp only [θIso_hom, map_comp, assoc]
      · rw [θIso_hom, ← θ_natural, assoc, ← θIso_hom, Iso.hom_inv_id, comp_id]

@[simp] lemma sym_C (P : SymPoincare A.inv N) : (L.sym P).C = L.cx P.C := rfl
@[simp] lemma sym_p (P : SymPoincare A.inv N) : (L.sym P).p = L.map P.p := rfl
@[simp] lemma sym_φ (P : SymPoincare A.inv N) : (L.sym P).φ = L.θs N P.C ≫ L.map P.φ := rfl

/-- The underlying complex of `P ⊕ Q` (the `simps` lemma `SymPoincare.sum_C` of v4.27; on v4.35
`sumComplex` is reducible and `simps` only generates `sum_C_X`, `sum_C_d`). -/
lemma _root_.HSFormal.LTheory.SymPoincare.sum_C {V : Type*} [Category V] [Preadditive V]
    {J : StrictInvolution V} {N : ℤ} (P Q : SymPoincare J N)
    (b : ∀ r, BinaryBicone (P.C.X r) (Q.C.X r)) : (P.sum Q b).C = sumComplex b := rfl

/-- `(P ⊕ Q) ⊗ ℝ ≃ P ⊗ ℝ ⊕ Q ⊗ ℝ`. -/
def symSumIsometry (P Q : SymPoincare A.inv N) (b : ∀ r, BinaryBicone (P.C.X r) (Q.C.X r))
    (b' : ∀ r, BinaryBicone ((L.sym P).C.X r) ((L.sym Q).C.X r)) :
    (L.sym (P.sum Q b)).HomotopyIsometry ((L.sym P).sum (L.sym Q) b') := by
  have hθ {X Y : ChainComplex A ℤ} (x : X ⟶ Y) {Z : ChainComplex B ℤ} (y : _ ⟶ Z) :
      dualHom B.inv (N + 1) (L.map x) ≫ L.θs N X ≫ y =
        L.θs N Y ≫ L.map (dualHom A.inv N x) ≫ y := θ_natural_assoc _ _ _ _ _ _
  refine .ofEq (L.map (sumFst b ≫ P.p) ≫ sumInl b' + L.map (sumSnd b ≫ Q.p) ≫ sumInr b')
    (sumFst b' ≫ L.map (P.p ≫ sumInl b) + sumSnd b' ≫ L.map (Q.p ≫ sumInr b)) ?_ ?_ ?_ ?_ ?_
  · simp only [sym_p, SymPoincare.sum_p, add_comp, comp_add, assoc, sumInl_sumFst_assoc,
      sumInl_sumSnd_assoc, sumInr_sumFst_assoc, sumInr_sumSnd_assoc, zero_comp, comp_zero,
      add_zero, zero_add, ← map_comp_assoc, ← map_comp, P.p_idem, Q.p_idem, sumInl_sumFst,
      sumInl_sumSnd, sumInr_sumFst, sumInr_sumSnd, comp_id, map_zero, P.p_idem_assoc,
      Q.p_idem_assoc]
  · simp only [sym_p, SymPoincare.sum_p, add_comp, comp_add, assoc, sumInl_sumFst_assoc,
      sumInl_sumSnd_assoc, sumInr_sumFst_assoc, sumInr_sumSnd_assoc, zero_comp, comp_zero,
      add_zero, zero_add, ← map_comp_assoc, ← map_comp, P.p_idem, Q.p_idem, sumInl_sumFst,
      sumInl_sumSnd, sumInr_sumFst, sumInr_sumSnd, comp_id, map_zero, P.p_idem_assoc,
      Q.p_idem_assoc, id_comp]
  · simp only [sym_p, SymPoincare.sum_p, add_comp, comp_add, assoc, sumInl_sumFst_assoc,
      sumInl_sumSnd_assoc, sumInr_sumFst_assoc, sumInr_sumSnd_assoc, zero_comp, comp_zero,
      add_zero, zero_add, ← map_comp_assoc, ← map_comp, P.p_idem, Q.p_idem, sumInl_sumFst,
      sumInl_sumSnd, sumInr_sumFst, sumInr_sumSnd, comp_id, map_zero, P.p_idem_assoc,
      Q.p_idem_assoc, map_add]
  · simp only [sym_p, SymPoincare.sum_p, add_comp, comp_add, assoc, sumInl_sumFst_assoc,
      sumInl_sumSnd_assoc, sumInr_sumFst_assoc, sumInr_sumSnd_assoc, zero_comp, comp_zero,
      add_zero, zero_add, ← map_comp_assoc, ← map_comp, P.p_idem, Q.p_idem, sumInl_sumFst,
      sumInl_sumSnd, sumInr_sumFst, sumInr_sumSnd, comp_id, map_zero, P.p_idem_assoc,
      Q.p_idem_assoc]
  · simp only [sym_φ, SymPoincare.sum_φ, SymPoincare.sum_C, dualHom_add, dualHom_comp, add_comp, comp_add, assoc,
      hθ, ← map_comp, ← map_comp_assoc, dualHom_sumFst_dualHom_sumInl_assoc,
      dualHom_sumSnd_dualHom_sumInl_assoc, dualHom_sumFst_dualHom_sumInr_assoc,
      dualHom_sumSnd_dualHom_sumInr_assoc, sumInl_sumFst_assoc, sumInl_sumSnd_assoc,
      sumInr_sumFst_assoc, sumInr_sumSnd_assoc, zero_comp, comp_zero, add_zero, zero_add,
      map_add, map_zero, P.φ_comp_p_assoc, Q.φ_comp_p_assoc, P.φ_comp_p, Q.φ_comp_p,
      SymPoincare.dualHom_p_comp_φ_assoc, SymPoincare.dualHom_p_comp_φ, id_comp, sumInl_sumFst,
      sumInr_sumSnd, comp_id, dualHom_sumFst_dualHom_sumInl, dualHom_sumSnd_dualHom_sumInr]

end LineData

/-! ### The line data of `C_ℤ(A)` -/

namespace CZ

variable (A : InvCat)

/-- The constant object at `X`. -/
abbrev constObj (X : A) : Obj A := ⟨fun _ ↦ X⟩

/-- The constant functor `A ⥤ C_ℤ(A)`: constant objects and diagonal matrices. -/
@[implicit_reducible]
def constFunctor : A ⥤ Obj A where
  obj := constObj A
  map {X Y} f := diag (X := constObj A X) (Y := constObj A Y) fun _ ↦ f
  map_id X := diag_id _
  map_comp {X Y Z} f g :=
    (diag_comp_diag (X := constObj A X) (Y := constObj A Y) (Z := constObj A Z) _ _).symm

@[simp] lemma constFunctor_obj (X : A) : (constFunctor A).obj X = constObj A X := rfl

lemma constFunctor_map {X Y : A} (f : X ⟶ Y) :
    (constFunctor A).map f = diag (X := constObj A X) (Y := constObj A Y) fun _ ↦ f := rfl

/-- The constant functor as a duality-preserving functor `A ⟶ C_ℤ(A)`. -/
@[implicit_reducible]
def const : A ⟶ A.cz where
  F := constFunctor A
  additive := ⟨fun {X Y f g} ↦ diag_add (X := constObj A X) (Y := constObj A Y)
    (fun _ ↦ f) (fun _ ↦ g)⟩
  map_star {X Y} f := (star_diag (X := constObj A X) (Y := constObj A Y) fun _ ↦ f).symm

variable {A}

/-- The shift matrix `(w, v) ↦ [w = v + k]`. -/
def shiftMat (k : ℤ) (X : A) : Mat (constObj A X) (constObj A X) :=
  fun w v ↦ if w = v + k then 𝟙 X else 0

lemma propLE_shiftMat (k : ℤ) (X : A) : PropLE (shiftMat k X) k.natAbs := fun w v h ↦ by
  simp only [shiftMat]
  rw [if_neg]
  intro hw
  subst hw
  simp at h

/-- The shift by `k` positions. -/
def constShift (k : ℤ) (X : A) : constObj A X ⟶ constObj A X :=
  homMk (shiftMat k X) _ (propLE_shiftMat k X)

@[simp] lemma shift_apply (k : ℤ) (X : A) (w v : ℤ) :
    (constShift k X).1 w v = if w = v + k then 𝟙 X else 0 := rfl

lemma shift_comp_shift (k l : ℤ) (X : A) : constShift k X ≫ constShift l X = constShift (k + l) X := by
  ext w v
  rw [comp_apply, finsum_eq_single _ (v + k) fun u hu ↦ by simp [hu]]
  simp only [shift_apply, if_true, id_comp, add_assoc]

lemma shift_zero (X : A) : constShift 0 X = 𝟙 _ := by
  ext w v
  rw [shift_apply, id_mat, matId, diagMat]
  by_cases h : v = w
  · subst h; simp
  · rw [if_neg (by omega), dif_neg h]

@[reassoc]
lemma shift_natural (k : ℤ) {X Y : A} (f : X ⟶ Y) :
    (constFunctor A).map f ≫ constShift k Y = constShift k X ≫ (constFunctor A).map f := by
  ext w v
  rw [constFunctor_map, diag_comp_apply, comp_diag_apply, shift_apply, shift_apply]
  split_ifs <;> simp

lemma star_shift (k : ℤ) (X : A) : involution.star (constShift k X) = constShift (-k) X := by
  ext w v
  rw [star_apply, shift_apply, shift_apply]
  by_cases h : v = w + k
  · rw [if_pos h, if_pos (by omega), A.inv.star_id]
  · rw [if_neg h, if_neg (by omega), A.inv.star_zero]

variable (A)

/-- **The line data of `C_ℤ(A)`**: the constant functor with the shift by one. -/
def lineData : LineData A A.cz where
  Δ := const A
  s :=
    { iso := NatIso.ofComponents
        (fun X ↦ ⟨constShift 1 X, constShift (-1) X, by rw [shift_comp_shift]; exact shift_zero X,
          by rw [shift_comp_shift]; exact shift_zero X⟩)
        fun f ↦ shift_natural 1 f
      star_hom := fun X ↦ star_shift 1 X }

@[simp] lemma lineData_Δ_obj (X : A) : ((lineData A).Δ.F.obj X).obj = fun _ ↦ X := rfl

@[simp] lemma lineData_s_hom (X : A) : (lineData A).s.iso.hom.app X = constShift 1 X := rfl

@[simp] lemma lineData_s_inv (X : A) : (lineData A).s.iso.inv.app X = constShift (-1) X := rfl

end CZ

end

end HSFormal.LTheory
