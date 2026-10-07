import HSFormal.LTheory.Model.CutSurj
import HSFormal.LTheory.Model.BoundaryConstructionRel

/-!
# The germ at `-∞` modulo bounded objects (lower L-theory model, module 22, injectivity of
`tensorLine`, part 1)

**The lower germ functor.**  For `X : C_ℤ(A)` let `X⁻ = X|_{(-∞, 0)}` be the `E`-part of the cut
of `X` at `0` (`CZ.low X = cut X (· < 0)`).  In the quotient `C_ℤ(A)/C_ℤ^{bdd}(A)` by bounded
objects (`bddFiltration`), `X ↦ X⁻`, `f ↦ [ι_E f π_E]` is a strict duality-preserving additive
functor `CZ.lowGerm A : A.cz ⟶ (bddFiltration A).quot`: a map of propagation `b` from `X⁻` to
`Y|_{[0, ∞)}` is supported in the rows `[0, b]` and so factors through a bounded object
(`factorsThrough_low_cross`), which gives `map_comp`; `ι_E^* = π_E` gives `map_star`.  It kills
bounded objects and objects of the positive half-line (`isZero_lowGerm_obj_of_bdd`,
`isZero_lowGerm_obj_of_posHalf`), and on the negative half-line it is the projection up to the
natural unitary isomorphism `[ι_E] : X⁻ ≅ X` (`pr_πE_ιE`, `lowGerm_map_pr_ιE`).

**The `D_X`-block of a union** (any additive `ℚ`-linear `V`).  For pairs `X` on `B` and `Y` on
`-B`, the degreewise projection `unionπX : X ∪ Y = Cone(u) ⟶ D_X` (`sndX` followed by the first
projection) satisfies `π_X^* φ_∪ π_X = δφ_X` on the nose (`block_union_φ`): in the union
structure `½(Hns + T Hns)`, `Hns = ι_W δφ_X ι_W^* + G + ι_Y δφ_Y ι_Y^*`, the cross term `G`
contains the cone homotopy `K'` (whose components land in the `B`-summand, `K'_hom_unionπX`) on
one side, `ι_Y π_X = 0`, and `T` commutes with taking blocks (`blockFam_transpose`).

**Germs of unions.**
* `unionGermIso`: if `B` is bounded and `D_Y` lies in the positive half-line, the germ of the
  union `(X ∪ Y)⁻` is homotopy isometric (with strict identities) to the closed germ
  `X.toClosed lowGerm`; the defects of `[π_X]` factor through `B` and `D_Y`.
* `negGermIso`: if `D_X` lies in the negative half-line, `X.toClosed lowGerm` is homotopy
  isometric to `X.toQuot` (`X` modulo bounded objects), by `[ι_E]`, `[π_E]`.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression
  homotopyCofiber

noncomputable section

attribute [local implicit_reducible] PairOn.toPair SymPair.neg SymPair.toPairOn PairOn.union PairOn.glue
  SymPair.closedOfIsZero SymPair.map CZ.cut CZ.diagSplitting

universe v u

section Block

variable {V : Type u} [Category.{v} V] [Preadditive V] [HasBinaryBiproducts V]
  [HasFiniteBiproducts V] {J : StrictInvolution V} {N : ℤ}
  {B : SymPoincare J N} (X : PairOn B) (Y : PairOn B.neg)

/-- The projection of the union onto the `D_X` summand (degreewise). -/
def unionπX (r : ℤ) : (Glue.U (σU B) X Y).X r ⟶ X.D.X r :=
  sndX (Glue.u (σU B) X Y) r ≫ (sumFst (Glue.bS X Y)).f r

@[reassoc]
lemma ιW_f_unionπX (r : ℤ) : (Glue.ιW (σU B) X Y).f r ≫ unionπX X Y r = 𝟙 _ := by
  simp [unionπX, Glue.ιW]

lemma ιY_f_unionπX (r : ℤ) : (Glue.ιY (σU B) X Y).f r ≫ unionπX X Y r = 0 := by
  simp [unionπX, Glue.ιY]

@[reassoc (attr := simp)]
lemma K'_hom_unionπX (i k : ℤ) : (Glue.K' (σU B) X Y).hom i k ≫ unionπX X Y k = 0 := by
  by_cases h : (ComplexShape.down ℤ).Rel k i
  · rw [Glue.K'_hom, inrCompHomotopy_hom _ _ _ _ h]
    simp [unionπX]
  · rw [Glue.K'_hom, (inrCompHomotopy _ _).zero _ _ h, zero_comp]

@[reassoc (attr := simp)]
lemma star_unionπX_star_K'_hom (i k : ℤ) :
    J.star (unionπX X Y k) ≫ J.star ((Glue.K' (σU B) X Y).hom i k) = 0 := by
  rw [← J.star_comp, K'_hom_unionπX, J.star_zero]

/-- The cross term `G` of the union structure has zero `D_X`-block. -/
lemma block_G (i k : ℤ) :
    J.star (unionπX X Y (N - i)) ≫ (Glue.G (σU B) X Y).hom i k ≫ unionπX X Y k = 0 := by
  simp [Glue.G, conjHomotopy]

lemma block_HW (i k : ℤ) : J.star (unionπX X Y (N - i)) ≫ (Glue.HW (σU B) X Y).hom i k ≫
    unionπX X Y k = X.δφ.hom i k := by
  simp only [Glue.HW, Homotopy.compLeft_hom, Homotopy.compRight_hom, dualHom_f, assoc,
    ιW_f_unionπX, comp_id]
  rw [← assoc, ← J.star_comp, ιW_f_unionπX]
  erw [J.star_id, id_comp]

lemma block_HY (i k : ℤ) : J.star (unionπX X Y (N - i)) ≫ (Glue.HY (σU B) X Y).hom i k ≫
    unionπX X Y k = 0 := by
  simp [Glue.HY, ιY_f_unionπX]

/-- The `D_X`-block of the non-symmetrized union structure is `δφ_X`. -/
lemma block_Hns (i k : ℤ) : J.star (unionπX X Y (N - i)) ≫ (Glue.Hns (σU B) X Y).hom i k ≫
    unionπX X Y k = X.δφ.hom i k := by
  rw [Glue.Hns_hom]
  simp only [add_comp, comp_add, block_HW, block_HY, block_G, add_zero]

end Block

section BlockFam

variable {V : Type u} [Category.{v} V] [Preadditive V] {J : StrictInvolution V} {N : ℤ}
  {C D : ChainComplex V ℤ}

/-- The `π`-block `π h π^*` of a family `C^{N-*} ⟶ C` along degreewise maps `π : C ⟶ D`. -/
def blockFam (π : ∀ k, C.X k ⟶ D.X k) (h : ∀ i k, (dualComplex J N C).X i ⟶ C.X k) :
    ∀ i k, (dualComplex J N D).X i ⟶ D.X k :=
  fun i k ↦ J.star (π (N - i)) ≫ h i k ≫ π k

lemma fam_eqToHom (π : ∀ k, C.X k ⟶ D.X k) {a b : ℤ} (h : a = b) :
    π a ≫ eqToHom (congrArg D.X h) = eqToHom (congrArg C.X h) ≫ π b := by
  subst h; simp

lemma blockFam_transpose (π : ∀ k, C.X k ⟶ D.X k) (h : ∀ i k, (dualComplex J N C).X i ⟶ C.X k) :
    blockFam π (transposeHomFamily J N h) = transposeHomFamily J N (blockFam π h) := by
  funext i k
  simp only [blockFam, transposeHomFamily, bidual_hom_f, Linear.comp_units_smul,
    Linear.units_smul_comp, J.star_comp, J.star_star, assoc]
  rw [fam_eqToHom π (sub_sub_cancel N k)]

lemma blockFam_smul_add [Linear ℚ V] (π : ∀ k, C.X k ⟶ D.X k) (q : ℚ)
    (h h' : ∀ i k, (dualComplex J N C).X i ⟶ C.X k) :
    blockFam π (q • (h + h')) = q • (blockFam π h + blockFam π h') := by
  funext i k
  simp [blockFam, comp_add, add_comp, Linear.comp_smul, Linear.smul_comp, smul_add]

lemma star_fam_XIsoOfEq (π : ∀ k, C.X k ⟶ D.X k) {a b : ℤ} (h : a = b) :
    J.star (π a) ≫ (C.XIsoOfEq h).hom = (D.XIsoOfEq h).hom ≫ J.star (π b) := by
  subst h; simp

end BlockFam

section Block2

variable {V : Type u} [Category.{v} V] [Preadditive V] [HasBinaryBiproducts V]
  [HasFiniteBiproducts V] {J : StrictInvolution V} {N : ℤ}
  {B : SymPoincare J N} (X : PairOn B) (Y : PairOn B.neg)

section Linear

variable [Linear ℚ V]

lemma blockFam_δφZ : blockFam (J := J) (N := N) (C := Glue.U (σU B) X Y) (unionπX X Y)
    (Glue.δφZ (σU B) X Y).hom = X.δφ.hom := by
  have e₁ : blockFam (J := J) (N := N) (C := Glue.U (σU B) X Y) (unionπX X Y)
      (Glue.Hns (σU B) X Y).hom = X.δφ.hom := by
    funext i k; exact block_Hns X Y i k
  have e₂ : transposeHomFamily J N X.δφ.hom = X.δφ.hom := by
    have h := X.symm
    rwa [IsSymmHomotopy, transposeHomotopy_hom] at h
  rw [Glue.δφZ, symmHomotopy_hom, blockFam_smul_add, blockFam_transpose, e₁, e₂, ← two_smul ℚ,
    smul_smul]
  norm_num

lemma block_δφZ (i k : ℤ) : J.star (unionπX X Y (N - i)) ≫ (Glue.δφZ (σU B) X Y).hom i k ≫
    unionπX X Y k = X.δφ.hom i k :=
  congrFun (congrFun (blockFam_δφZ X Y) i) k

/-- **The `D_X`-block of the union structure is the top of `X`**. -/
lemma block_union_φ (r : ℤ) : J.star (unionπX X Y (N + 1 - r)) ≫ (X.union Y).φ.f r ≫
    unionπX X Y r = relTop X.δφ r := by
  rw [union_φ_f, relTop, relTop, assoc, ← assoc (J.star _),
    star_fam_XIsoOfEq (C := Glue.U (σU B) X Y) (unionπX X Y), assoc, block_δφZ]

end Linear

@[reassoc]
lemma ιW_f_pU_f (r : ℤ) : (Glue.ιW (σU B) X Y).f r ≫ (Glue.pU (σU B) X Y).f r =
    X.pD.f r ≫ (Glue.ιW (σU B) X Y).f r := by
  rw [← comp_f, Glue.ιW_pU, comp_f]

@[reassoc]
lemma pU_f_unionπX (r : ℤ) :
    (Glue.pU (σU B) X Y).f r ≫ unionπX X Y r = unionπX X Y r ≫ X.pD.f r := by
  simp [unionπX, Glue.pS]

/-- The union idempotent splits into its `B`-, `D_X`- and `D_Y`-parts. -/
lemma pU_f_decomp (r : ℤ) : (Glue.pU (σU B) X Y).f r =
    (fstX (Glue.u (σU B) X Y) r (r - 1) (by simp) ≫
        (B.p.f (r - 1) ≫ inlX (Glue.u (σU B) X Y) (r - 1) r (by simp)) :
          (Glue.U (σU B) X Y).X r ⟶ (Glue.U (σU B) X Y).X r) +
      unionπX X Y r ≫ X.pD.f r ≫ (Glue.ιW (σU B) X Y).f r +
      ((sndX (Glue.u (σU B) X Y) r ≫ (sumSnd (Glue.bS X Y)).f r) ≫
        (Y.pD.f r ≫ (Glue.ιY (σU B) X Y).f r) :
          (Glue.U (σU B) X Y).X r ⟶ (Glue.U (σU B) X Y).X r) := by
  conv_lhs => rw [← id_comp ((Glue.pU (σU B) X Y).f r),
    cone.id_X (Glue.u (σU B) X Y) r (r - 1) (by simp)]
  simp only [add_comp, assoc, inlX_coneMap_f, inrX_coneMap_f, unionπX, Glue.ιW, Glue.ιY,
    Glue.pS, comp_f, add_f_apply, sumFst_f, sumSnd_f, sumInl_f, sumInr_f, inr_f, comp_add]
  abel

end Block2

namespace CZ

variable {A : InvCat}

/-- The cut of `X : C_ℤ(A)` at `0`: `E = X|_{(-∞, 0)}`, `U = X|_{[0, ∞)}`. -/
abbrev low (X : A.cz) : Splitting X := cut X (fun v ↦ v < 0)

/-- The cut idempotent minus the identity, sandwiching `f`: entries vanish outside the rows
`[0, b]`. -/
lemma factorsThrough_idem_cross {X Y : A.cz} (f : X ⟶ Y) :
    FactorsThrough (bdd A) ((low X).idem ≫ f ≫ (𝟙 Y - (low Y).idem)) := by
  obtain ⟨b, hb⟩ := f.2
  refine factorsThrough_bdd_of_rows _ 0 b fun w v h ↦ ?_
  rw [cut_idem, cut_idem, comp_sub, comp_sub, comp_id, sub_apply, diag_comp_apply,
    diag_comp_apply, comp_diag_apply]
  by_cases hv : v < 0
  · by_cases hw : w < 0
    · simp [hv, hw]
    · rw [hb w v (by rw [lt_abs]; omega)]; simp
  · simp [hv]

/-- A map from the negative part of `X` to the nonnegative part of `Y` factors through a bounded
object (its entries live in the rows `[0, b]`). -/
lemma factorsThrough_low_cross {X Y : A.cz} (f : X ⟶ Y) :
    FactorsThrough (bdd A) ((low X).ιE ≫ f ≫ (low Y).πU) := by
  have e : (low X).ιE ≫ f ≫ (low Y).πU =
      (low X).ιE ≫ ((low X).idem ≫ f ≫ (𝟙 Y - (low Y).idem)) ≫ (low Y).πU := by
    have t : 𝟙 Y - (low Y).idem = (low Y).πU ≫ (low Y).ιU := by
      rw [Splitting.idem, ← (low Y).total]; abel
    rw [t, Splitting.idem]
    simp only [assoc, Splitting.ιU_πU, comp_id]
    rw [← assoc (low X).ιE (low X).πE, (low X).ιE_πE, id_comp]
  rw [e, ← assoc]
  exact ((factorsThrough_idem_cross f).comp_left _).comp_right _

lemma low_E_bdd_of_posHalf {X : A.cz} (hX : posHalf A X) : bdd A (low X).E := by
  obtain ⟨c, hc⟩ := hX
  refine bdd_iff.2 ⟨c, -1, fun v hv ↦ ?_⟩
  rcases hv with hv | hv
  · have h0 : IsZero (X.obj v) := hc v hv
    change IsZero (if v < 0 then splitE (X.obj v) else splitU (X.obj v)).E
    split_ifs
    · exact h0
    · exact isZero_zero _
  · exact isZero_cut_E X _ (by omega)

lemma low_E_bdd_of_bdd {X : A.cz} (hX : bdd A X) : bdd A (low X).E :=
  low_E_bdd_of_posHalf hX.1

lemma low_U_bdd_of_negHalf {X : A.cz} (hX : negHalf A X) : bdd A (low X).U := by
  obtain ⟨c, hc⟩ := hX
  refine bdd_iff.2 ⟨0, c, fun v hv ↦ ?_⟩
  change IsZero (if v < 0 then splitE (X.obj v) else splitU (X.obj v)).U
  split_ifs with h
  · exact isZero_zero _
  · rcases hv with hv | hv
    · omega
    · exact hc v hv

variable (A) in
/-- The bounded filtration of `C_ℤ(A)`. -/
abbrev bddF : KaroubiFiltration A.cz := bddFiltration A

/-- The projection `C_ℤ(A) ⟶ C_ℤ(A)/C_ℤ^{bdd}(A)` on morphisms. -/
abbrev pr {X Y : A.cz} (f : X ⟶ Y) := (bddF A).proj.F.map f

@[reassoc]
lemma pr_comp {X Y Z : A.cz} (f : X ⟶ Y) (g : Y ⟶ Z) : pr (f ≫ g) = pr f ≫ pr g :=
  (bddF A).proj.F.map_comp f g

lemma pr_eq_iff {X Y : A.cz} (f g : X ⟶ Y) : pr f = pr g ↔ FactorsThrough (bdd A) (f - g) :=
  (bddF A).proj_map_eq_iff f g

lemma pr_eq_zero {X Y : A.cz} {f : X ⟶ Y} (h : FactorsThrough (bdd A) f) : pr f = 0 := by
  rw [← (bddF A).proj.F.map_zero, pr_eq_iff, sub_zero]
  exact h

/-- On an object of the negative half-line, `π_E ι_E = 1` modulo bounded objects. -/
lemma proj_πE_ιE_of_negHalf {X : A.cz} (hX : negHalf A X) :
    pr ((low X).πE ≫ (low X).ιE) = 𝟙 _ := by
  rw [← (bddF A).proj.F.map_id, pr_eq_iff]
  have e : (low X).πE ≫ (low X).ιE - 𝟙 X = -((low X).πU ≫ (low X).ιU) := by
    rw [← (low X).total]; abel
  rw [e]
  exact (FactorsThrough.of_mem (low_U_bdd_of_negHalf hX) _ _).neg

/-- **The lower germ functor** on underlying categories. -/
@[simps, implicit_reducible]
def lowGermF : A.cz ⥤ (bddF A).quot where
  obj X := (bddF A).proj.F.obj (low X).E
  map {X Y} f := pr ((low X).ιE ≫ f ≫ (low Y).πE)
  map_id X := by
    rw [id_comp, (low X).ιE_πE]
    exact (bddF A).proj.F.map_id _
  map_comp {X Y Z} f g := by
    rw [← Functor.map_comp, pr_eq_iff]
    have e : (low X).ιE ≫ (f ≫ g) ≫ (low Z).πE -
        ((low X).ιE ≫ f ≫ (low Y).πE) ≫ (low Y).ιE ≫ g ≫ (low Z).πE =
        ((low X).ιE ≫ f ≫ (low Y).πU) ≫ (low Y).ιU ≫ g ≫ (low Z).πE := by
      have t := (low Y).total
      calc _ = (low X).ιE ≫ f ≫ ((low Y).πE ≫ (low Y).ιE + (low Y).πU ≫ (low Y).ιU) ≫ g ≫
            (low Z).πE - ((low X).ιE ≫ f ≫ (low Y).πE) ≫ (low Y).ιE ≫ g ≫ (low Z).πE := by
              rw [t, id_comp, assoc]
        _ = _ := by simp only [add_comp, comp_add, assoc]; abel
    rw [e]
    exact (factorsThrough_low_cross f).comp_right _

instance : (lowGermF (A := A)).Additive where
  map_add {X Y f g} := by
    simp only [lowGermF_map, add_comp, comp_add, Functor.map_add]

variable (A) in
/-- **The lower germ functor** `C_ℤ(A) ⟶ C_ℤ(A)/C_ℤ^{bdd}(A)`, `X ↦ X|_{(-∞,0)}`. -/
@[implicit_reducible]
def lowGerm : A.cz ⟶ (bddF A).quot where
  F := lowGermF
  map_star {X Y} f := by
    change pr _ = (quotInvolution A.cz.inv (bdd A)).star (pr _)
    erw [quotInvolution_star_map]
    congr 1
    rw [A.cz.inv.star_comp, A.cz.inv.star_comp, star_cut_ιE, star_cut_πE, assoc]

lemma lowGerm_map {X Y : A.cz} (f : X ⟶ Y) :
    (lowGerm A).F.map f = pr ((low X).ιE ≫ f ≫ (low Y).πE) := rfl

lemma lowGerm_obj (X : A.cz) : (lowGerm A).F.obj X = (bddF A).proj.F.obj (low X).E := rfl

lemma isZero_lowGerm_obj_of_bdd {X : A.cz} (hX : bdd A X) : IsZero ((lowGerm A).F.obj X) :=
  (bddF A).isZero_proj_obj (low_E_bdd_of_bdd hX)

lemma isZero_lowGerm_obj_of_posHalf {X : A.cz} (hX : posHalf A X) :
    IsZero ((lowGerm A).F.obj X) :=
  (bddF A).isZero_proj_obj (low_E_bdd_of_posHalf hX)

/-- A composite through an object killed by `lowGerm` is killed. -/
lemma lowGerm_map_comp_eq_zero {X Y Z : A.cz} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : IsZero ((lowGerm A).F.obj Y)) : (lowGerm A).F.map (f ≫ g) = 0 := by
  rw [Functor.map_comp, h.eq_of_src ((lowGerm A).F.map g) 0, comp_zero]

/-! ### Naturality of `[ι_E]`, `[π_E]` on the negative half-line -/

@[reassoc]
lemma pr_ιE_πE (X : A.cz) : pr (low X).ιE ≫ pr (low X).πE = 𝟙 _ := by
  rw [← Functor.map_comp, (low X).ιE_πE]; exact (bddF A).proj.F.map_id _

@[reassoc]
lemma pr_πE_ιE {X : A.cz} (hX : negHalf A X) : pr (low X).πE ≫ pr (low X).ιE = 𝟙 _ := by
  rw [← Functor.map_comp]; exact proj_πE_ιE_of_negHalf hX

@[reassoc]
lemma lowGerm_map_pr_ιE {X Y : A.cz} (hY : negHalf A Y) (f : X ⟶ Y) :
    (lowGerm A).F.map f ≫ pr (low Y).ιE = pr (low X).ιE ≫ pr f := by
  rw [lowGerm_map, pr_comp, pr_comp, assoc, assoc, pr_πE_ιE hY, comp_id]

@[reassoc]
lemma pr_πE_lowGerm_map {X Y : A.cz} (hX : negHalf A X) (f : X ⟶ Y) :
    pr (low X).πE ≫ (lowGerm A).F.map f = pr f ≫ pr (low Y).πE := by
  rw [lowGerm_map, pr_comp, pr_comp, pr_πE_ιE_assoc hX]

lemma star_pr {X Y : A.cz} (f : X ⟶ Y) : (bddF A).quot.inv.star (pr f) = pr (A.cz.inv.star f) :=
  ((bddF A).proj.map_star f).symm

/-! ### The germ of a closed complex in the negative half-line -/

section NegGerm

variable {N : ℤ} (Z : SymPair A.cz.inv N) (hU : ∀ r, bdd A (Z.bd.C.X r))
  (hD : ∀ r, negHalf A (Z.D.X r))

/-- `[ι_E] : D⁻ ⟶ D` modulo bounded objects, for `D` in the negative half-line. -/
def negGermι : (lowGerm A).mapC Z.D ⟶ (bddF A).proj.mapC Z.D where
  f r := pr (low (Z.D.X r)).ιE
  comm' r r' _ := by
    change _ = (lowGerm A).F.map _ ≫ _
    rw [lowGerm_map_pr_ιE (hD r')]
    rfl

/-- `[π_E] : D ⟶ D⁻` modulo bounded objects, for `D` in the negative half-line. -/
def negGermπ : (bddF A).proj.mapC Z.D ⟶ (lowGerm A).mapC Z.D where
  f r := pr (low (Z.D.X r)).πE
  comm' r r' _ := by
    change _ ≫ (lowGerm A).F.map _ = _
    rw [pr_πE_lowGerm_map (hD r)]
    rfl

lemma negGermι_f (r : ℤ) : (negGermι Z hD).f r = pr (low (Z.D.X r)).ιE := rfl

lemma negGermπ_f (r : ℤ) : (negGermπ Z hD).f r = pr (low (Z.D.X r)).πE := rfl

/-- **On the negative half-line, the germ at `-∞` of a pair with bounded boundary is its image
modulo bounded objects.** -/
def negGermIso : (Z.toClosed (lowGerm A) fun r ↦ isZero_lowGerm_obj_of_bdd (hU r)).HomotopyIsometry
    (Z.toQuot (bddF A) hU) where
  f := negGermι Z hD ≫ (bddF A).proj.mapH Z.pD
  g := negGermπ Z hD ≫ (lowGerm A).mapH Z.pD
  f_kar := by
    ext r
    simp only [SymPair.closedOfIsZero_p, SymPair.map_pD, comp_f, negGermι_f, InvFunctor.mapH,
      Functor.mapHomologicalComplex_map_f, assoc]
    rw [lowGerm_map_pr_ιE_assoc (hD r), ← Functor.map_comp, ← Functor.map_comp, ← comp_f,
      ← comp_f, Z.pD_idem, Z.pD_idem]
  g_kar := by
    ext r
    simp only [SymPair.closedOfIsZero_p, SymPair.map_pD, comp_f, negGermπ_f, InvFunctor.mapH,
      Functor.mapHomologicalComplex_map_f, assoc]
    rw [← pr_πE_lowGerm_map_assoc (hD r), ← Functor.map_comp, ← Functor.map_comp, ← comp_f,
      ← comp_f, Z.pD_idem, Z.pD_idem]
  fg := Homotopy.ofEq (by
    ext r
    simp only [SymPair.closedOfIsZero_p, SymPair.map_pD, comp_f, negGermπ_f, negGermι_f,
      InvFunctor.mapH, Functor.mapHomologicalComplex_map_f, assoc]
    rw [← pr_πE_lowGerm_map_assoc (hD r), pr_ιE_πE_assoc, ← Functor.map_comp, ← comp_f,
      Z.pD_idem])
  gf := Homotopy.ofEq (by
    ext r
    simp only [SymPair.closedOfIsZero_p, SymPair.map_pD, comp_f, negGermπ_f, negGermι_f,
      InvFunctor.mapH, Functor.mapHomologicalComplex_map_f, assoc]
    rw [lowGerm_map_pr_ιE_assoc (hD r), pr_πE_ιE_assoc (hD r), ← Functor.map_comp, ← comp_f,
      Z.pD_idem])
  conj := Homotopy.ofEq (by
    ext r
    simp only [SymPair.toClosed_φ_f, comp_f, dualHom_f, negGermι_f, InvFunctor.mapH,
      Functor.mapHomologicalComplex_map_f, assoc, (bddF A).quot.inv.star_comp, star_pr]
    erw [star_cut_ιE]
    rw [lowGerm_map_pr_ιE_assoc (hD r), pr_πE_ιE_assoc (hD _), ← Functor.map_comp,
      ← Functor.map_comp]
    congr 1
    exact (PairData.ofPairOn Z.toPairOn).star_pD_comp_relTop_assoc r _ |>.trans
      ((PairData.ofPairOn Z.toPairOn).relTop_comp_pD r))

end NegGerm

/-! ### The germ of a union at `-∞` -/

section UnionGerm

variable {N : ℤ} {B : SymPoincare A.cz.inv N} (X : PairOn B) (Y : PairOn B.neg)
  (hB : ∀ r, bdd A (B.C.X r)) (hY : ∀ r, posHalf A (Y.D.X r))

include hB in
/-- The germ `[π_X] : (X ∪ Y)⁻ ⟶ D_X⁻` of the projection onto the `D_X`-summand: a chain map
modulo bounded objects (its defect factors through the bounded boundary `B`). -/
def unionGermπ : (lowGerm A).mapC (X.union Y).C ⟶ (lowGerm A).mapC X.D where
  f r := (lowGerm A).F.map (unionπX X Y r)
  comm' r r' h := by
    dsimp only [InvFunctor.mapC, Functor.mapHomologicalComplex_obj_d]
    rw [← Functor.map_comp, ← Functor.map_comp]
    have e : (Glue.U (σU B) X Y).d r r' ≫ unionπX X Y r' =
        (fstX (Glue.u (σU B) X Y) r r' h ≫ ((Glue.u (σU B) X Y).f r' ≫
          (sumFst (Glue.bS X Y)).f r') : (Glue.U (σU B) X Y).X r ⟶ X.D.X r') +
            unionπX X Y r ≫ X.D.d r r' := by
      simp only [homotopyCofiber_d, unionπX, d_sndX_assoc _ _ _ h, add_comp,
        assoc]
      rw [(sumFst (Glue.bS X Y)).comm r r']
      simp
    rw [show (X.union Y).C.d r r' = (Glue.U (σU B) X Y).d r r' from rfl, e, Functor.map_add,
      lowGerm_map_comp_eq_zero _ _ (isZero_lowGerm_obj_of_bdd (hB r')),
      zero_add]

lemma unionGermπ_f (r : ℤ) : (unionGermπ X Y hB).f r = (lowGerm A).F.map (unionπX X Y r) := rfl

include hY in
/-- **The germ at `-∞` of the union `X ∪ Y` is the closed germ of `X`** (`D_X` with its top
structure), when the boundary is bounded and `Y` lies in the positive half-line. -/
def unionGermIso : ((X.union Y).map (lowGerm A)).HomotopyIsometry
    (X.toPair.toClosed (lowGerm A) fun r ↦ isZero_lowGerm_obj_of_bdd (hB r)) where
  f := unionGermπ X Y hB ≫ (lowGerm A).mapH X.pD
  g := (lowGerm A).mapH (X.pD ≫ Glue.ιW (σU B) X Y)
  f_kar := by
    ext r
    simp only [SymPoincare.map_p, SymPair.closedOfIsZero_p, SymPair.map_pD, comp_f,
      unionGermπ_f, InvFunctor.mapH, Functor.mapHomologicalComplex_map_f, ← Functor.map_comp,
      PairOn.toPair_pD, assoc]
    congr 1
    rw [union_p, pU_f_unionπX_assoc, X.pD_idem_f_assoc, X.pD_idem_f]
  g_kar := by
    ext r
    simp only [SymPoincare.map_p, SymPair.closedOfIsZero_p, SymPair.map_pD, comp_f,
      InvFunctor.mapH, Functor.mapHomologicalComplex_map_f, ← Functor.map_comp, PairOn.toPair_pD]
    congr 1
    rw [union_p, assoc, ιW_f_pU_f, X.pD_idem_f_assoc, X.pD_idem_f_assoc]
  fg := Homotopy.ofEq (by
    ext r
    simp only [SymPoincare.map_p, comp_f, unionGermπ_f, InvFunctor.mapH,
      Functor.mapHomologicalComplex_map_f, ← Functor.map_comp, union_p]
    rw [pU_f_decomp, Functor.map_add, Functor.map_add,
      lowGerm_map_comp_eq_zero _ _ (isZero_lowGerm_obj_of_bdd (hB (r - 1))),
      lowGerm_map_comp_eq_zero _ _ (isZero_lowGerm_obj_of_posHalf (hY r)), zero_add, add_zero]
    congr 1
    simp only [assoc, X.pD_idem_f_assoc])
  gf := Homotopy.ofEq (by
    ext r
    simp only [SymPair.closedOfIsZero_p, SymPair.map_pD, comp_f, unionGermπ_f, InvFunctor.mapH,
      Functor.mapHomologicalComplex_map_f, ← Functor.map_comp, PairOn.toPair_pD, assoc]
    congr 1
    rw [ιW_f_unionπX_assoc, X.pD_idem_f])
  conj := Homotopy.ofEq (by
    ext r
    simp only [SymPoincare.map_φ, InvFunctor.mapDual_f, SymPair.toClosed_φ_f, comp_f,
      dualHom_f, unionGermπ_f, InvFunctor.mapH, Functor.mapHomologicalComplex_map_f,
      ← (lowGerm A).map_star, ← Functor.map_comp]
    congr 1
    rw [A.cz.inv.star_comp]
    simp only [assoc]
    rw [reassoc_of% (block_union_φ X Y r)]
    exact (PairData.ofPairOn X).star_pD_comp_relTop_assoc r _ |>.trans
      ((PairData.ofPairOn X).relTop_comp_pD r))

end UnionGerm

end CZ

end

end HSFormal.LTheory
