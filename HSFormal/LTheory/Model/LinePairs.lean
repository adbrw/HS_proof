import HSFormal.LTheory.Model.LineComplex

/-!
# Poincaré pairs over the line and the transfer (lower L-theory model, module 5)

For a Poincaré pair `X = (j : C ⟶ D, (δφ, φ))` over `A`, `L.pair X` is the pair
`(j ⊗ 1 : C ⊗ ℝ ⟶ D ⊗ ℝ, (θ ≫ δφ ⊗ 1, θ ≫ φ ⊗ 1))` over `B` (`pairδφ`, symmetric by
`θ_natural_htpy`), whose boundary is *exactly* `L.sym X.bd` (`pair_bd`; boundary sign `+1`).
Its relative duality map is `-(κ^* ≫ θ ≫ Ψ ⊗ 1)` (`relDuality_pair`) for the cone interchange
`κ : Cone(j) ⊗ ℝ ≅ Cone(j ⊗ 1)`, hence a Kar equivalence: `P ↦ P ⊗ ℝ` preserves
null-cobordisms (`NullCobordant.sym`).

`L.transfer N : Lconc A N →+ Lconc B (N + 1)`, `[P] ↦ [P ⊗ ℝ]`, descends along `Lconc.lift`
(sums: `symSumIsometry`); for `C_ℤ(A)` it is `Lconc.tensorLine A N` (naturality:
`Lconc.tensorLine_map` in `LineNatural.lean`).
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression
  homotopyCofiber

noncomputable section

namespace LineData

variable {A B : InvCat} (L : LineData A B)

/-! ### Maps out of and into `Δ(Cone j)` -/

section DeltaCone

variable {C D : ChainComplex A ℤ} (j : C ⟶ D)

lemma ext_from_map_cone {i k : ℤ} (h : (ComplexShape.down ℤ).Rel i k) {Z : B}
    {f g : L.Δ.F.obj ((cone j).X i) ⟶ Z}
    (h₁ : L.Δ.F.map (inlX j k i h) ≫ f = L.Δ.F.map (inlX j k i h) ≫ g)
    (h₂ : L.Δ.F.map (inrX j i) ≫ f = L.Δ.F.map (inrX j i) ≫ g) : f = g := by
  have e (x : L.Δ.F.obj ((cone j).X i) ⟶ Z) : x = L.Δ.F.map (fstX j i k h) ≫
      L.Δ.F.map (inlX j k i h) ≫ x + L.Δ.F.map (sndX j i) ≫ L.Δ.F.map (inrX j i) ≫ x := by
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, ← add_comp, ← Functor.map_add,
      ← cone.id_X]
    simp
  rw [e f, e g, h₁, h₂]

lemma ext_to_map_cone {i k : ℤ} (h : (ComplexShape.down ℤ).Rel i k) {Z : B}
    {f g : Z ⟶ L.Δ.F.obj ((cone j).X i)}
    (h₁ : f ≫ L.Δ.F.map (fstX j i k h) = g ≫ L.Δ.F.map (fstX j i k h))
    (h₂ : f ≫ L.Δ.F.map (sndX j i) = g ≫ L.Δ.F.map (sndX j i)) : f = g := by
  have e (x : Z ⟶ L.Δ.F.obj ((cone j).X i)) : x = x ≫ L.Δ.F.map (fstX j i k h) ≫
      L.Δ.F.map (inlX j k i h) + x ≫ L.Δ.F.map (sndX j i) ≫ L.Δ.F.map (inrX j i) := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← comp_add, ← Functor.map_add, ← cone.id_X]
    simp
  rw [e f, e g, reassoc_of% h₁, reassoc_of% h₂]

lemma ext_from_map_cone' (i : ℤ) {Z : B} {f g : L.Δ.F.obj ((cone j).X i) ⟶ Z}
    (h₁ : L.Δ.F.map (inlX j (i - 1) i (by simp)) ≫ f = L.Δ.F.map (inlX j (i - 1) i (by simp)) ≫ g)
    (h₂ : L.Δ.F.map (inrX j i) ≫ f = L.Δ.F.map (inrX j i) ≫ g) : f = g :=
  L.ext_from_map_cone j _ h₁ h₂

lemma ext_to_map_cone' (i : ℤ) {Z : B} {f g : Z ⟶ L.Δ.F.obj ((cone j).X i)}
    (h₁ : f ≫ L.Δ.F.map (fstX j i (i - 1) (by simp)) = g ≫ L.Δ.F.map (fstX j i (i - 1) (by simp)))
    (h₂ : f ≫ L.Δ.F.map (sndX j i) = g ≫ L.Δ.F.map (sndX j i)) : f = g :=
  L.ext_to_map_cone j _ h₁ h₂

end DeltaCone

end LineData

/-- Normal form for components of maps between line complexes of cones. -/
macro "kappa_simp_core" : tactic => `(tactic|
  simp (disch := down_rel) only [homotopyCofiber_d, Functor.mapHomologicalComplex_obj_d,
    InvFunctor.mapC, comp_add, add_comp, assoc, neg_comp, comp_neg, zero_comp, comp_zero,
    add_zero, zero_add, neg_zero, neg_neg, sub_comp, comp_sub, id_comp, comp_id, neg_add_rev,
    inlX_fstX_assoc, inlX_fstX, inlX_sndX_assoc, inlX_sndX, inrX_fstX_assoc, inrX_fstX,
    inrX_sndX_assoc, inrX_sndX, inlX_fstX'_assoc, inlX_fstX', d_fstX_assoc, d_fstX,
    d_sndX_assoc, d_sndX, inlX_d''_assoc, inlX_d'', inrX_d_assoc, inrX_d,
    LineData.inlX_map_assoc, LineData.inlX_map, LineData.inrX_map_assoc, LineData.inrX_map,
    LineData.map_fstX_assoc, LineData.map_fstX, LineData.map_sndX_assoc, LineData.map_sndX,
    LineData.g_f, LineData.s_hom_map_assoc, LineData.s_hom_map, ← Functor.map_comp,
    ← Functor.map_comp_assoc, Functor.map_add, Functor.map_neg, Functor.map_zero,
    Functor.map_sub, CategoryTheory.Functor.map_id, Functor.mapHomologicalComplex_map_f,
    InvFunctor.mapH, Iso.hom_inv_id, Iso.inv_hom_id, Iso.hom_inv_id_assoc,
    Iso.inv_hom_id_assoc, XIsoOfEq_hom_comp_XIsoOfEq_hom, XIsoOfEq_hom_comp_XIsoOfEq_hom_assoc,
    XIsoOfEq_rfl, Iso.refl_hom, sub_self, sub_zero, zero_sub, inlX_coneMap_f_assoc,
    inlX_coneMap_f, inrX_coneMap_f_assoc, inrX_coneMap_f, coneMap_f_fstX_assoc, coneMap_f_fstX,
    coneMap_f_sndX_assoc, coneMap_f_sndX])

/-- `kappa_simp_core`, then normalize objects and repeat. -/
macro "kappa_simp" : tactic => `(tactic| (
  (try kappa_simp_core) <;>
  (try dsimp only [Functor.mapHomologicalComplex_obj_X, homotopyCofiber_X]) <;>
  (try kappa_simp_core) <;>
  (try (dsimp only [dualComplex_X, InvFunctor.mapC, Functor.mapHomologicalComplex_obj_X,
    homotopyCofiber_X]; done)) <;>
  (try (first | (erw [Category.comp_id]; done) | (erw [Category.id_comp]; done)))))


section ConeCast

variable {V : Type*} [Category V] [Preadditive V] [HasBinaryBiproducts V]
  {K L' : ChainComplex V ℤ} (φ : K ⟶ L') (J : StrictInvolution V)

@[reassoc]
lemma XIsoOfEq_star_inrX {i i' : ℤ} (h : i = i') :
    ((homotopyCofiber φ).XIsoOfEq h).hom ≫ J.star (inrX φ i') =
      J.star (inrX φ i) ≫ (L'.XIsoOfEq h).hom := by
  subst h; simp

@[reassoc]
lemma XIsoOfEq_star_inlX {i i' k' : ℤ} (h : i = i') (hk' : (ComplexShape.down ℤ).Rel i' k') :
    ((homotopyCofiber φ).XIsoOfEq h).hom ≫ J.star (inlX φ k' i' hk') =
      J.star (inlX φ (i - 1) i (by simp)) ≫
        (K.XIsoOfEq (by simp only [ComplexShape.down_Rel] at hk'; omega)).hom := by
  subst h
  obtain rfl : k' = i - 1 := by simp only [ComplexShape.down_Rel] at hk'; omega
  simp

@[reassoc]
lemma star_sndX_XIsoOfEq {i i' : ℤ} (h : i = i') :
    J.star (sndX φ i) ≫ ((homotopyCofiber φ).XIsoOfEq h).hom =
      (L'.XIsoOfEq h).hom ≫ J.star (sndX φ i') := by
  subst h; simp

@[reassoc]
lemma star_fstX_XIsoOfEq {i i' k : ℤ} (hk : (ComplexShape.down ℤ).Rel i k) (h : i = i') :
    J.star (fstX φ i k hk) ≫ ((homotopyCofiber φ).XIsoOfEq h).hom =
      (K.XIsoOfEq (show k = i' - 1 by simp only [ComplexShape.down_Rel] at hk; omega)).hom ≫
        J.star (fstX φ i' (i' - 1) (by simp)) := by
  subst h
  obtain rfl : k = i - 1 := by simp only [ComplexShape.down_Rel] at hk; omega
  simp

end ConeCast

namespace LineData

variable {A B : InvCat} (L : LineData A B)

section Kappa

variable {C D : ChainComplex A ℤ} (j : C ⟶ D)

/-- The cone interchange `Cone(j) ⊗ ℝ ⟶ Cone(j ⊗ 1)`,
`(c_e, d_e, c_v, d_v) ↦ ((-c_e, c_v), (d_e, d_v))`. -/
def κf (r : ℤ) : (L.cx (cone j)).X r ⟶ (cone (L.map j)).X r :=
  -(fstX (L.g (cone j)) r (r - 1) (by simp) ≫ L.Δ.F.map (fstX j (r - 1) (r - 1 - 1) (by simp)) ≫
      inlX (L.g C) (r - 1 - 1) (r - 1) (by simp) ≫ inlX (L.map j) (r - 1) r (by simp)) +
    sndX (L.g (cone j)) r ≫ L.Δ.F.map (fstX j r (r - 1) (by simp)) ≫ inrX (L.g C) (r - 1) ≫
      inlX (L.map j) (r - 1) r (by simp) +
    fstX (L.g (cone j)) r (r - 1) (by simp) ≫ L.Δ.F.map (sndX j (r - 1)) ≫
      inlX (L.g D) (r - 1) r (by simp) ≫ inrX (L.map j) r +
    sndX (L.g (cone j)) r ≫ L.Δ.F.map (sndX j r) ≫ inrX (L.g D) r ≫ inrX (L.map j) r

/-- The inverse cone interchange. -/
def κinvf (r : ℤ) : (cone (L.map j)).X r ⟶ (L.cx (cone j)).X r :=
  -(fstX (L.map j) r (r - 1) (by simp) ≫ fstX (L.g C) (r - 1) (r - 1 - 1) (by simp) ≫
      L.Δ.F.map (inlX j (r - 1 - 1) (r - 1) (by simp)) ≫ inlX (L.g (cone j)) (r - 1) r (by simp)) +
    fstX (L.map j) r (r - 1) (by simp) ≫ sndX (L.g C) (r - 1) ≫
      L.Δ.F.map (inlX j (r - 1) r (by simp)) ≫ inrX (L.g (cone j)) r +
    sndX (L.map j) r ≫ fstX (L.g D) r (r - 1) (by simp) ≫ L.Δ.F.map (inrX j (r - 1)) ≫
      inlX (L.g (cone j)) (r - 1) r (by simp) +
    sndX (L.map j) r ≫ sndX (L.g D) r ≫ L.Δ.F.map (inrX j r) ≫ inrX (L.g (cone j)) r


lemma inlX_κf_κinvf (r : ℤ) :
    inlX (L.g (cone j)) (r - 1) r (by simp) ≫ L.κf j r ≫ L.κinvf j r =
      inlX (L.g (cone j)) (r - 1) r (by simp) := by
  apply L.ext_from_map_cone' j (r - 1) <;> apply ext_to_X (L.g (cone j)) r (r - 1) (by simp)
  · apply L.ext_to_map_cone' j (r - 1) <;> (simp only [κf, κinvf]; kappa_simp)
  · apply L.ext_to_map_cone' j r <;> (simp only [κf, κinvf]; kappa_simp)
  · apply L.ext_to_map_cone' j (r - 1) <;> (simp only [κf, κinvf]; kappa_simp)
  · apply L.ext_to_map_cone' j r <;> (simp only [κf, κinvf]; kappa_simp)

lemma inrX_κf_κinvf (r : ℤ) :
    inrX (L.g (cone j)) r ≫ L.κf j r ≫ L.κinvf j r = inrX (L.g (cone j)) r := by
  apply L.ext_from_map_cone' j r <;> apply ext_to_X (L.g (cone j)) r (r - 1) (by simp)
  · apply L.ext_to_map_cone' j (r - 1) <;> (simp only [κf, κinvf]; kappa_simp)
  · apply L.ext_to_map_cone' j r <;> (simp only [κf, κinvf]; kappa_simp)
  · apply L.ext_to_map_cone' j (r - 1) <;> (simp only [κf, κinvf]; kappa_simp)
  · apply L.ext_to_map_cone' j r <;> (simp only [κf, κinvf]; kappa_simp)

lemma κf_κinvf (r : ℤ) : L.κf j r ≫ L.κinvf j r = 𝟙 _ := by
  apply ext_from_X (L.g (cone j)) (r - 1) r (by simp)
  · rw [inlX_κf_κinvf]; erw [comp_id]
  · rw [inrX_κf_κinvf]; erw [comp_id]

lemma inlX_κinvf_κf (r : ℤ) :
    inlX (L.map j) (r - 1) r (by simp) ≫ L.κinvf j r ≫ L.κf j r =
      inlX (L.map j) (r - 1) r (by simp) := by
  apply ext_from_X (L.g C) (r - 1 - 1) (r - 1) (by simp) <;>
    apply ext_to_X (L.map j) r (r - 1) (by simp)
  · apply ext_to_X (L.g C) (r - 1) (r - 1 - 1) (by simp) <;> (simp only [κf, κinvf]; kappa_simp)
  · apply ext_to_X (L.g D) r (r - 1) (by simp) <;> (simp only [κf, κinvf]; kappa_simp)
  · apply ext_to_X (L.g C) (r - 1) (r - 1 - 1) (by simp) <;> (simp only [κf, κinvf]; kappa_simp)
  · apply ext_to_X (L.g D) r (r - 1) (by simp) <;> (simp only [κf, κinvf]; kappa_simp)

lemma inrX_κinvf_κf (r : ℤ) :
    inrX (L.map j) r ≫ L.κinvf j r ≫ L.κf j r = inrX (L.map j) r := by
  apply ext_from_X (L.g D) (r - 1) r (by simp) <;>
    apply ext_to_X (L.map j) r (r - 1) (by simp)
  · apply ext_to_X (L.g C) (r - 1) (r - 1 - 1) (by simp) <;> (simp only [κf, κinvf]; kappa_simp)
  · apply ext_to_X (L.g D) r (r - 1) (by simp) <;> (simp only [κf, κinvf]; kappa_simp)
  · apply ext_to_X (L.g C) (r - 1) (r - 1 - 1) (by simp) <;> (simp only [κf, κinvf]; kappa_simp)
  · apply ext_to_X (L.g D) r (r - 1) (by simp) <;> (simp only [κf, κinvf]; kappa_simp)

lemma κinvf_κf (r : ℤ) : L.κinvf j r ≫ L.κf j r = 𝟙 _ := by
  apply ext_from_X (L.map j) (r - 1) r (by simp)
  · rw [inlX_κinvf_κf]; erw [comp_id]
  · rw [inrX_κinvf_κf]; erw [comp_id]

lemma inlX_κf_comm (r : ℤ) :
    inlX (L.g (cone j)) (r - 1) r (by simp) ≫ L.κf j r ≫ (cone (L.map j)).d r (r - 1) =
      inlX (L.g (cone j)) (r - 1) r (by simp) ≫ (L.cx (cone j)).d r (r - 1) ≫
        L.κf j (r - 1) := by
  apply L.ext_from_map_cone' j (r - 1) <;>
    apply ext_to_X (L.map j) (r - 1) (r - 1 - 1) (by simp)
  · apply ext_to_X (L.g C) (r - 1 - 1) (r - 1 - 1 - 1) (by simp) <;> (simp only [κf]; kappa_simp)
  · apply ext_to_X (L.g D) (r - 1) (r - 1 - 1) (by simp) <;> (simp only [κf]; kappa_simp)
  · apply ext_to_X (L.g C) (r - 1 - 1) (r - 1 - 1 - 1) (by simp) <;> (simp only [κf]; kappa_simp)
  · apply ext_to_X (L.g D) (r - 1) (r - 1 - 1) (by simp) <;> (simp only [κf]; kappa_simp)

lemma inrX_κf_comm (r : ℤ) :
    inrX (L.g (cone j)) r ≫ L.κf j r ≫ (cone (L.map j)).d r (r - 1) =
      inrX (L.g (cone j)) r ≫ (L.cx (cone j)).d r (r - 1) ≫ L.κf j (r - 1) := by
  apply L.ext_from_map_cone' j r <;>
    apply ext_to_X (L.map j) (r - 1) (r - 1 - 1) (by simp)
  · apply ext_to_X (L.g C) (r - 1 - 1) (r - 1 - 1 - 1) (by simp) <;> (simp only [κf]; kappa_simp)
  · apply ext_to_X (L.g D) (r - 1) (r - 1 - 1) (by simp) <;> (simp only [κf]; kappa_simp)
  · apply ext_to_X (L.g C) (r - 1 - 1) (r - 1 - 1 - 1) (by simp) <;> (simp only [κf]; kappa_simp)
  · apply ext_to_X (L.g D) (r - 1) (r - 1 - 1) (by simp) <;> (simp only [κf]; kappa_simp)

/-- **The cone interchange** `κ : Cone(j) ⊗ ℝ ≅ Cone(j ⊗ 1)`. -/
def κ : L.cx (cone j) ≅ cone (L.map j) :=
  Hom.isoOfComponents (fun r ↦ ⟨L.κf j r, L.κinvf j r, L.κf_κinvf j r, L.κinvf_κf j r⟩)
    fun r r' h ↦ by
      obtain rfl : r' = r - 1 := by simp only [ComplexShape.down_Rel] at h; omega
      exact ext_from_X (L.g (cone j)) (r - 1) r (by simp) (by simpa using L.inlX_κf_comm j r)
        (by simpa using L.inrX_κf_comm j r)

@[simp] lemma κ_hom_f (r : ℤ) : (L.κ j).hom.f r = L.κf j r := rfl

@[simp] lemma κ_inv_f (r : ℤ) : (L.κ j).inv.f r = L.κinvf j r := rfl

section Natural

variable {C' D' : ChainComplex A ℤ} {j' : C' ⟶ D'} {m : C ⟶ C'} {n : D ⟶ D'}
  (h : m ≫ j' = j ≫ n)

include h in
lemma map_comp_map_eq : L.map m ≫ L.map j' = L.map j ≫ L.map n := by
  rw [← map_comp, h, map_comp]

lemma inlX_map_coneMap_κf (r : ℤ) :
    inlX (L.g (cone j)) (r - 1) r (by simp) ≫ (L.map (coneMap m n h)).f r ≫ L.κf j' r =
      inlX (L.g (cone j)) (r - 1) r (by simp) ≫ L.κf j r ≫
        (coneMap (L.map m) (L.map n) (L.map_comp_map_eq j h)).f r := by
  apply L.ext_from_map_cone' j (r - 1) <;> apply ext_to_X (L.map j') r (r - 1) (by simp)
  · apply ext_to_X (L.g C') (r - 1) (r - 1 - 1) (by simp) <;> (simp only [κf]; kappa_simp)
  · apply ext_to_X (L.g D') r (r - 1) (by simp) <;> (simp only [κf]; kappa_simp)
  · apply ext_to_X (L.g C') (r - 1) (r - 1 - 1) (by simp) <;> (simp only [κf]; kappa_simp)
  · apply ext_to_X (L.g D') r (r - 1) (by simp) <;> (simp only [κf]; kappa_simp)

lemma inrX_map_coneMap_κf (r : ℤ) :
    inrX (L.g (cone j)) r ≫ (L.map (coneMap m n h)).f r ≫ L.κf j' r =
      inrX (L.g (cone j)) r ≫ L.κf j r ≫
        (coneMap (L.map m) (L.map n) (L.map_comp_map_eq j h)).f r := by
  apply L.ext_from_map_cone' j r <;> apply ext_to_X (L.map j') r (r - 1) (by simp)
  · apply ext_to_X (L.g C') (r - 1) (r - 1 - 1) (by simp) <;> (simp only [κf]; kappa_simp)
  · apply ext_to_X (L.g D') r (r - 1) (by simp) <;> (simp only [κf]; kappa_simp)
  · apply ext_to_X (L.g C') (r - 1) (r - 1 - 1) (by simp) <;> (simp only [κf]; kappa_simp)
  · apply ext_to_X (L.g D') r (r - 1) (by simp) <;> (simp only [κf]; kappa_simp)

/-- Naturality of the cone interchange. -/
lemma κ_natural : L.map (coneMap m n h) ≫ (L.κ j').hom =
    (L.κ j).hom ≫ coneMap (L.map m) (L.map n) (L.map_comp_map_eq j h) := by
  ext r
  apply ext_from_X (L.g (cone j)) (r - 1) r (by simp)
  · simpa using L.inlX_map_coneMap_κf j h r
  · simpa using L.inrX_map_coneMap_κf j h r

end Natural

end Kappa

/-! ### Homotopies over the line -/

section Htpy

variable (a b : ℚ) (M : ℤ)

lemma htpy_hom {C D : ChainComplex A ℤ} {f f' : C ⟶ D} (H : Homotopy f f') (i i' : ℤ) :
    (L.htpy H).hom i i' = if hi : (ComplexShape.down ℤ).Rel i' i then
      -(fstX (L.g C) i (i - 1) (by simp) ≫ L.Δ.F.map (H.hom (i - 1) i) ≫ inlX (L.g D) i i' hi) +
        sndX (L.g C) i ≫ L.Δ.F.map (H.hom i i') ≫ inrX (L.g D) i'
    else 0 := rfl

lemma htpy_hom_succ {C D : ChainComplex A ℤ} {f f' : C ⟶ D} (H : Homotopy f f') (i : ℤ) :
    (L.htpy H).hom i (i + 1) =
      -(fstX (L.g C) i (i - 1) (by simp) ≫ L.Δ.F.map (H.hom (i - 1) i) ≫
        inlX (L.g D) i (i + 1) (by simp)) +
        sndX (L.g C) i ≫ L.Δ.F.map (H.hom i (i + 1)) ≫ inrX (L.g D) (i + 1) := by
  rw [htpy_hom, dif_pos (by simp)]

lemma htpy_hom_eq_zero {C D : ChainComplex A ℤ} {f f' : C ⟶ D} (H : Homotopy f f') {i i' : ℤ}
    (h : ¬ (ComplexShape.down ℤ).Rel i' i) : (L.htpy H).hom i i' = 0 := by
  rw [htpy_hom, dif_neg h]

/-- `L.htpy` only depends on the homotopy family. -/
lemma htpy_hom_congr {C D : ChainComplex A ℤ} {f f' g g' : C ⟶ D} {H : Homotopy f f'}
    {H' : Homotopy g g'} (h : H.hom = H'.hom) : (L.htpy H).hom = (L.htpy H').hom := by
  funext i i'; simp only [htpy_hom, h]

set_option maxHeartbeats 400000 in
/-- Naturality of `θ` for homotopies. -/
lemma θ_natural_htpy {C D : ChainComplex A ℤ} {f f' : C ⟶ D} (H : Homotopy f f') (r r' : ℤ) :
    (dualHomotopy B.inv (M + 1) (L.htpy H)).hom r r' ≫ (L.θ a b M C).f r' =
      (L.θ a b M D).f r ≫ (L.htpy (dualHomotopy A.inv M H)).hom r r' := by
  by_cases hr : (ComplexShape.down ℤ).Rel r' r
  · obtain rfl : r' = r + 1 := by simp only [ComplexShape.down_Rel] at hr; omega
    rw [dualHomotopy_hom, htpy_hom_succ, htpy_hom, dif_pos (by down_rel)]
    apply cone.ext_star (J := B.inv) (L.g D) _ _ (down_rel_sub M r)
    all_goals apply ext_to_X (L.g (dualComplex A.inv M C)) (r + 1) r (by simp)
    all_goals simp only [θ_f, dualHomotopy_hom, B.inv.star_add, B.inv.star_neg, B.inv.star_comp,
      B.inv.star_units_smul, B.inv.star_star]
    all_goals line_simp
    all_goals try simp only [Functor.map_neg, Functor.map_units_smul, InvFunctor.map_star, smul_neg,
      units_smul_units_smul_self, neg_neg, Linear.smul_comp, Linear.units_smul_comp, neg_comp]
    all_goals abel
  · rw [(dualHomotopy B.inv (M + 1) (L.htpy H)).zero r r' hr,
      (L.htpy (dualHomotopy A.inv M H)).zero r r' hr, zero_comp, comp_zero]

/-- `L.htpy` commutes with pre- and post-composition. -/
lemma htpy_comp_hom {C D C' D' : ChainComplex A ℤ} {f f' : C ⟶ D} (H : Homotopy f f')
    (e : C' ⟶ C) (e' : D ⟶ D') (i i' : ℤ) :
    (L.map e).f i ≫ (L.htpy H).hom i i' ≫ (L.map e').f i' =
      (L.htpy ((H.compRight e').compLeft e)).hom i i' := by
  by_cases hi : (ComplexShape.down ℤ).Rel i' i
  · obtain rfl : i' = i + 1 := by simp only [ComplexShape.down_Rel] at hi; omega
    rw [htpy_hom_succ, htpy_hom_succ]
    apply ext_from_X (L.g C') (i - 1) i (by simp)
    all_goals apply ext_to_X (L.g D') (i + 1) i (by simp)
    all_goals simp only [Homotopy.compLeft_hom, Homotopy.compRight_hom, comp_add, add_comp,
      assoc, comp_neg, neg_comp, inlX_map_assoc, inrX_map_assoc, map_fstX, map_sndX,
      inlX_fstX_assoc, inlX_sndX_assoc, inrX_fstX_assoc, inrX_sndX_assoc, inlX_fstX, inlX_sndX,
      inrX_fstX, inrX_sndX, zero_comp, comp_zero, add_zero, zero_add, neg_zero, comp_id,
      Functor.map_comp, Functor.mapHomologicalComplex_map_f, InvFunctor.mapH]
    all_goals erw [comp_id]
  · rw [htpy_hom_eq_zero _ _ hi, htpy_hom_eq_zero _ _ hi, zero_comp, comp_zero]

end Htpy

/-! ### Homotopy families over the line -/

lemma htpy_hom_of_rel {C D : ChainComplex A ℤ} {f f' : C ⟶ D} (H : Homotopy f f') {i i' : ℤ}
    (hi : (ComplexShape.down ℤ).Rel i' i) :
    (L.htpy H).hom i i' =
      -(fstX (L.g C) i (i - 1) (by simp) ≫ L.Δ.F.map (H.hom (i - 1) i) ≫ inlX (L.g D) i i' hi) +
        sndX (L.g C) i ≫ L.Δ.F.map (H.hom i i') ≫ inrX (L.g D) i' := by
  rw [htpy_hom, dif_pos hi]

lemma htpy_compRight_hom {C D D' : ChainComplex A ℤ} {f f' : C ⟶ D} (H : Homotopy f f')
    (e : D ⟶ D') (i i' : ℤ) :
    (L.htpy H).hom i i' ≫ (L.map e).f i' = (L.htpy (H.compRight e)).hom i i' := by
  have := L.htpy_comp_hom H (𝟙 C) e i i'
  rw [map_id, id_f] at this
  erw [id_comp] at this
  rw [this]
  exact congrFun (congrFun (L.htpy_hom_congr (by ext; simp)) i) i'

variable {N : ℤ}

/-- The relative structure `θ ≫ δφ ⊗ 1` of the pair `X ⊗ ℝ`. -/
def pairδφ (X : SymPair A.inv N) :
    Homotopy (dualHom B.inv (N + 1) (L.map X.j) ≫ (L.sym X.bd).φ ≫ L.map X.j) 0 :=
  homotopyCongr ((L.htpy X.δφ).compLeft (L.θs N X.D))
    (by simp only [sym_φ, map_comp, assoc]; rw [θ_natural_assoc])
    (by rw [map_zero, comp_zero])

lemma pairδφ_hom (X : SymPair A.inv N) (r r' : ℤ) :
    (L.pairδφ X).hom r r' = (L.θs N X.D).f r ≫ (L.htpy X.δφ).hom r r' := rfl

lemma pairδφ_kar (X : SymPair A.inv N) (r r' : ℤ) :
    (dualHom B.inv (N + 1) (L.map X.pD)).f r ≫ (L.pairδφ X).hom r r' ≫ (L.map X.pD).f r' =
      (L.pairδφ X).hom r r' := by
  have e := congrArg (fun φ ↦ φ.f r) (L.θ_natural (1 / 2) (1 / 2) N X.pD)
  simp only [comp_f] at e
  rw [pairδφ_hom]
  dsimp only [θs] at e ⊢
  simp only [assoc]
  rw [reassoc_of% e, L.htpy_comp_hom]
  congr 1
  refine congrFun (congrFun (L.htpy_hom_congr ?_) r) r'
  funext i k
  simp only [Homotopy.compLeft_hom, Homotopy.compRight_hom, assoc]
  exact X.δφ_kar i k


lemma mapC_XIsoOfEq_hom (C : ChainComplex A ℤ) {a b : ℤ} (h : a = b) :
    ((L.Δ.mapC C).XIsoOfEq h).hom = L.Δ.F.map (C.XIsoOfEq h).hom := by
  subst h; simp

/-- Normal form for the comparison of relative duality maps. -/
macro "pair_simp_core" : tactic => `(tactic|
  simp (disch := down_rel) only [comp_add, add_comp, assoc, neg_comp, comp_neg, zero_comp,
    comp_zero, add_zero, zero_add, neg_zero, neg_neg, sub_comp, comp_sub, id_comp, comp_id,
    neg_add_rev, smul_add, smul_neg, smul_zero, Linear.comp_units_smul, Linear.units_smul_comp,
    Linear.comp_smul, Linear.smul_comp, one_smul, zero_smul, add_smul,
    StrictInvolution.star_add, StrictInvolution.star_neg, StrictInvolution.star_comp,
    StrictInvolution.star_units_smul, StrictInvolution.star_star, star_rat_smul,
    StrictInvolution.star_zero, StrictInvolution.star_id, star_XIsoOfEq_hom, star_XIsoOfEq_inv,
    XIsoOfEq_inv_eq,
    inlX_fstX_assoc, inlX_fstX, inlX_sndX_assoc, inlX_sndX, inrX_fstX_assoc, inrX_fstX,
    inrX_sndX_assoc, inrX_sndX, inlX_fstX'_assoc, inlX_fstX',
    cone.star_fstX_inlX_assoc, cone.star_fstX_inlX, cone.star_fstX_inrX_assoc,
    cone.star_fstX_inrX, cone.star_sndX_inlX_assoc, cone.star_sndX_inlX,
    cone.star_sndX_inrX_assoc, cone.star_sndX_inrX, cone.star_fstX_inlX'_assoc,
    cone.star_fstX_inlX', XIsoOfEq_star_inrX_assoc, XIsoOfEq_star_inrX,
    XIsoOfEq_star_inlX_assoc, XIsoOfEq_star_inlX,
    LineData.inlX_map_assoc, LineData.inlX_map, LineData.inrX_map_assoc, LineData.inrX_map,
    LineData.map_fstX_assoc, LineData.map_fstX, LineData.map_sndX_assoc, LineData.map_sndX,
    LineData.star_fstX_star_map_assoc, LineData.star_fstX_star_map,
    LineData.star_sndX_star_map_assoc, LineData.star_sndX_star_map,
    ← InvFunctor.map_star, ← Functor.map_comp, ← Functor.map_comp_assoc, Functor.map_add,
    Functor.map_neg, Functor.map_zero, Functor.map_units_smul, CategoryTheory.Functor.map_id,
    LineData.mapC_XIsoOfEq_hom, LineData.s_hom_map_assoc, LineData.s_hom_map,
    LineData.s_inv_map_assoc, LineData.s_inv_map, LineData.s_hom_inv_assoc,
    LineData.s_hom_inv, LineData.s_inv_hom_assoc, LineData.s_inv_hom,
    XIsoOfEq_hom_comp_XIsoOfEq_hom, XIsoOfEq_hom_comp_XIsoOfEq_hom_assoc, XIsoOfEq_rfl,
    Iso.refl_hom, Int.negOnePow_succ, negOnePow_sub_one', Units.neg_smul,
    units_smul_units_smul_self, units_smul_rat_smul, dualHom_f, comp_f,
    star_sndX_XIsoOfEq_assoc, star_sndX_XIsoOfEq, star_fstX_XIsoOfEq_assoc, star_fstX_XIsoOfEq,
    LineData.htpy_hom_of_rel, relDuality_f, relTop])

/-- `pair_simp_core`, then normalize objects and repeat. -/
macro "pair_simp" : tactic => `(tactic| (
  (try pair_simp_core) <;>
  (try dsimp only [dualComplex_X, Functor.mapHomologicalComplex_obj_X, homotopyCofiber_X]) <;>
  (try pair_simp_core) <;>
  (try (dsimp only [dualComplex_X, InvFunctor.mapC, Functor.mapHomologicalComplex_obj_X,
    homotopyCofiber_X]; done)) <;>
  (try (first | (erw [Category.comp_id]; done) | (erw [Category.id_comp]; done)))))

set_option maxHeartbeats 400000 in
lemma relDuality_pair_fst (X : SymPair A.inv N) (r : ℤ) :
    B.inv.star (fstX (L.map X.j) (N + 1 + 1 - r) (N + 1 - r) (down_rel_sub (N + 1) r)) ≫
        (relDuality (L.pairδφ X)).f r =
      B.inv.star (fstX (L.map X.j) (N + 1 + 1 - r) (N + 1 - r) (down_rel_sub (N + 1) r)) ≫
        (-(dualHom B.inv (N + 1 + 1) (L.κ X.j).hom ≫ L.θs (N + 1) (cone X.j) ≫
          L.map (relDuality X.δφ))).f r := by
  apply cone.ext_star (J := B.inv) (L.g X.bd.C) _ _ (down_rel_sub N r) <;>
    apply ext_to_X (L.g X.D) r (r - 1) (by simp)
  all_goals simp only [relDuality_f, relTop, pairδφ_hom, sym_φ, θ_f, κ_hom_f, κf, cf, cf',
    neg_f_apply, comp_f, dualHom_f]
  all_goals pair_simp
  all_goals abel

set_option maxHeartbeats 400000 in
lemma relDuality_pair_snd (X : SymPair A.inv N) (r : ℤ) :
    B.inv.star (sndX (L.map X.j) (N + 1 + 1 - r)) ≫ (relDuality (L.pairδφ X)).f r =
      B.inv.star (sndX (L.map X.j) (N + 1 + 1 - r)) ≫
        (-(dualHom B.inv (N + 1 + 1) (L.κ X.j).hom ≫ L.θs (N + 1) (cone X.j) ≫
          L.map (relDuality X.δφ))).f r := by
  apply cone.ext_star (J := B.inv) (L.g X.D) _ _ (down_rel_sub (N + 1) r) <;>
    apply ext_to_X (L.g X.D) r (r - 1) (by simp)
  all_goals simp only [relDuality_f, relTop, pairδφ_hom, sym_φ, θ_f, κ_hom_f, κf, cf, cf',
    neg_f_apply, comp_f, dualHom_f]
  all_goals pair_simp
  all_goals abel

/-- **The relative duality map of `X ⊗ ℝ`** is `-(κ^* ≫ θ ≫ Ψ ⊗ 1)`. -/
lemma relDuality_pair (X : SymPair A.inv N) :
    relDuality (L.pairδφ X) = -(dualHom B.inv (N + 1 + 1) (L.κ X.j).hom ≫
      L.θs (N + 1) (cone X.j) ≫ L.map (relDuality X.δφ)) := by
  ext r
  exact cone.ext_star (J := B.inv) (L.map X.j) _ _ (down_rel_sub (N + 1) r)
    (L.relDuality_pair_fst X r) (L.relDuality_pair_snd X r)

lemma pairδφ_symm (X : SymPair A.inv N) : IsSymmHomotopy B.inv (N + 1) (L.pairδφ X) := by
  rw [IsSymmHomotopy, transposeHomotopy_hom]
  funext r r'
  have e₁ := congrArg (fun φ ↦ φ.f r') (L.θs_transpose N X.D)
  simp only [comp_f, dualHom_f] at e₁
  have e₂ := L.θ_natural_htpy (1 / 2) (1 / 2) N X.δφ r r'
  rw [dualHomotopy_hom] at e₂
  have e₃ := L.htpy_compRight_hom (dualHomotopy A.inv N X.δφ) (bidual A.inv N X.D).hom r r'
  have e₄ := congrFun (congrFun (L.htpy_hom_congr (H := (dualHomotopy A.inv N X.δφ).compRight
    (bidual A.inv N X.D).hom) (H' := X.δφ) (by rw [← X.symm, transposeHomotopy])) r) r'
  simp only [transposeHomFamily, pairδφ_hom, B.inv.star_comp, assoc, Linear.units_smul_comp]
  rw [e₁, ← Linear.units_smul_comp]
  dsimp only [θs] at e₂ ⊢
  rw [reassoc_of% e₂, e₃, e₄]

lemma θ_conj {M : ℤ} {C : ChainComplex A ℤ} (f : C ⟶ C) :
    L.θ 1 0 M C ≫ L.map (dualHom A.inv M f) ≫ (L.θIso M C).inv =
      dualHom B.inv (M + 1) (L.map f) := by
  rw [← θIso_inv_natural, ← θIso_hom, Iso.hom_inv_id_assoc]

/-- **`X ⊗ ℝ`**: the line pair of a Poincaré pair, with boundary `X.bd ⊗ ℝ`. -/
def pair (X : SymPair A.inv N) : SymPair B.inv (N + 1) where
  bd := L.sym X.bd
  D := L.cx X.D
  pD := L.map X.pD
  pD_idem := by rw [← map_comp, X.pD_idem]
  support := L.map_supportedIn X.support
  j := L.map X.j
  j_kar := by rw [sym_p, ← map_comp, ← map_comp, X.j_kar]
  δφ := L.pairδφ X
  δφ_kar := L.pairδφ_kar X
  symm := L.pairδφ_symm X
  poincare := by
    have h := ((((L.isKarEquiv_θ_map X.poincare).conjIso (L.θIso (N + 1) (cone X.j)).symm).of_homotopy
      (((L.θsHtpy (N + 1) (cone X.j)).symm).compRight
        (L.map (relDuality X.δφ)))).conjIso (dualIso B.inv (N + 1 + 1) (L.κ X.j)).symm).neg
    rw [Iso.symm_inv, dualIso_hom, ← relDuality_pair] at h
    convert h using 1
    simp only [Iso.symm_inv, Iso.symm_hom, dualIso_hom, dualIso_inv, θIso_hom, assoc, θ_conj,
      ← dualHom_comp]
    congr 1
    rw [L.κ_natural X.j (comm_of_kar X.bd.p_idem X.pD_idem X.j_kar), Iso.inv_hom_id_assoc]
    rfl

@[simp] lemma pair_bd (X : SymPair A.inv N) : (L.pair X).bd = L.sym X.bd := rfl

/-- `P ⊗ ℝ` is null-cobordant when `P` is. -/
lemma NullCobordant.sym {P : SymPoincare A.inv N} (h : NullCobordant P) :
    NullCobordant (L.sym P) := by
  obtain ⟨X, rfl⟩ := h
  exact ⟨L.pair X, rfl⟩

end LineData

/-! ### The transfer `[P] ↦ [P ⊗ ℝ]` -/

namespace LineData

variable {A B : InvCat} (L : LineData A B)

/-- **The transfer** `[P] ↦ [P ⊗ ℝ]`. -/
def transfer (N : ℤ) : Lconc A N →+ Lconc B (N + 1) :=
  Lconc.lift (fun P ↦ Lconc.cls (L.sym P))
    (fun P Q b ↦ by
      rw [Lconc.cls_eq_of_isometry (L.symSumIsometry P Q _
        fun r ↦ (Lconc.ub (L.sym P) (L.sym Q) r).toBinaryBicone), Lconc.cls_sum])
    (fun _ hP ↦ Lconc.cls_eq_zero (NullCobordant.sym L hP))

@[simp]
lemma transfer_cls {N : ℤ} (P : SymPoincare A.inv N) :
    L.transfer N (Lconc.cls P) = Lconc.cls (L.sym P) :=
  Lconc.lift_cls _ _ _ P

end LineData

/-- **The transition map** `Lconc A N → Lconc C_ℤ(A) (N+1)`, `[P] ↦ [P ⊗ ℝ]`. -/
def Lconc.tensorLine (A : InvCat) (N : ℤ) : Lconc A N →+ Lconc A.cz (N + 1) :=
  (CZ.lineData A).transfer N

@[simp]
lemma Lconc.tensorLine_cls {A : InvCat} {N : ℤ} (P : SymPoincare A.inv N) :
    Lconc.tensorLine A N (Lconc.cls P) = Lconc.cls ((CZ.lineData A).sym P) :=
  LineData.transfer_cls _ P

end

end HSFormal.LTheory
