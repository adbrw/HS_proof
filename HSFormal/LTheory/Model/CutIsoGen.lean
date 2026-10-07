import HSFormal.LTheory.Model.Cobordism
import HSFormal.LTheory.Model.Transport

/-!
# Pushing union structures forward (lower L-theory model, module 22, `cutUnion ≃ ±P`, general part)

General tools for comparing the union `X ∪ Y = PairOn.union` of two Poincaré pairs with other
closed complexes.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex homotopyCofiber
  HSFormal.Compression

noncomputable section

attribute [local implicit_reducible] PairOn.union PairOn.glue PairOn.toPair SymPair.closedOfIsZero

universe v u

variable {V : Type u} [Category.{v} V] [Preadditive V] {J : StrictInvolution V} {N : ℤ}

/-! ### A second-order homotopy -/

section SecondOrder

variable {B Z : ChainComplex V ℤ} {b₁ b₂ : B ⟶ Z} (Hd : Homotopy (b₁ + b₂) 0)
  {φ₁ φ₂ : dualComplex J N B ⟶ B} (W : Homotopy φ₁ φ₂)

/-- The second-order family `L = -(K^* W b₁ + b₂^* W K)` for `K : b₁ + b₂ ≃ 0`, `W : φ₁ ≃ φ₂`. -/
def soL (i k : ℤ) : (dualComplex J N Z).X i ⟶ Z.X k :=
  -((dualHomotopy J N Hd).hom i (i + 1) ≫ W.hom (i + 1) k ≫ b₁.f k +
    (dualHom J N b₂).f i ≫ W.hom i (i + 1) ≫ Hd.hom (i + 1) k)

/-- **The second-order identity**: `b₁ W b₁^* - b₂ W b₂^* - b₁ (φ₁ - φ₂) K^* + K (φ₁ - φ₂) b₂^*`
is the boundary `dL - Lδ` of `L = soL`. -/
lemma soL_spec (i i₀ i₁ i₂ : ℤ) (h₀ : i₀ + 1 = i) (h₁ : i + 1 = i₁) (h₂ : i₁ + 1 = i₂) :
    (dualHom J N b₁).f i ≫ W.hom i i₁ ≫ b₁.f i₁ - (dualHom J N b₂).f i ≫ W.hom i i₁ ≫ b₂.f i₁ -
        (dualHomotopy J N Hd).hom i i₁ ≫ (φ₁ - φ₂).f i₁ ≫ b₁.f i₁ +
        (dualHom J N b₂).f i ≫ (φ₁ - φ₂).f i ≫ Hd.hom i i₁ =
      soL Hd W i i₂ ≫ Z.d i₂ i₁ - (dualComplex J N Z).d i i₀ ≫ soL Hd W i₀ i₁ := by
  subst h₀ h₁ h₂
  have hW₀ := homotopy_comm W (i₀ + 1) i₀ (i₀ + 1 + 1) (by simp) (by simp)
  have hW₁ := homotopy_comm W (i₀ + 1 + 1) (i₀ + 1) (i₀ + 1 + 1 + 1) (by simp) (by simp)
  have hH := homotopy_comm Hd (i₀ + 1 + 1) (i₀ + 1) (i₀ + 1 + 1 + 1) (by simp) (by simp)
  have hD := homotopy_comm (dualHomotopy J N Hd) (i₀ + 1) i₀ (i₀ + 1 + 1) (by simp) (by simp)
  have c₁ : b₁.f (i₀ + 1 + 1 + 1) ≫ Z.d (i₀ + 1 + 1 + 1) (i₀ + 1 + 1) =
      B.d (i₀ + 1 + 1 + 1) (i₀ + 1 + 1) ≫ b₁.f (i₀ + 1 + 1) := b₁.comm _ _
  have c₂ : (dualComplex J N Z).d (i₀ + 1) i₀ ≫ (dualHom J N b₂).f i₀ =
      (dualHom J N b₂).f (i₀ + 1) ≫ (dualComplex J N B).d (i₀ + 1) i₀ :=
    ((dualHom J N b₂).comm _ _).symm
  simp only [add_f_apply, zero_f, add_zero, dualHom_add, dualHom_zero] at hW₀ hW₁ hH hD
  have eW₁ : W.hom (i₀ + 1 + 1) (i₀ + 1 + 1 + 1) ≫ B.d (i₀ + 1 + 1 + 1) (i₀ + 1 + 1) =
      φ₁.f (i₀ + 1 + 1) - φ₂.f (i₀ + 1 + 1) -
        (dualComplex J N B).d (i₀ + 1 + 1) (i₀ + 1) ≫ W.hom (i₀ + 1) (i₀ + 1 + 1) := by
    rw [hW₁]; abel
  have eW₀ : (dualComplex J N B).d (i₀ + 1) i₀ ≫ W.hom i₀ (i₀ + 1) =
      φ₁.f (i₀ + 1) - φ₂.f (i₀ + 1) - W.hom (i₀ + 1) (i₀ + 1 + 1) ≫ B.d (i₀ + 1 + 1) (i₀ + 1) := by
    rw [hW₀]; abel
  have eH : Hd.hom (i₀ + 1 + 1) (i₀ + 1 + 1 + 1) ≫ Z.d (i₀ + 1 + 1 + 1) (i₀ + 1 + 1) =
      b₁.f (i₀ + 1 + 1) + b₂.f (i₀ + 1 + 1) -
        B.d (i₀ + 1 + 1) (i₀ + 1) ≫ Hd.hom (i₀ + 1) (i₀ + 1 + 1) := by
    rw [hH]; abel
  have eD : (dualComplex J N Z).d (i₀ + 1) i₀ ≫ (dualHomotopy J N Hd).hom i₀ (i₀ + 1) =
      (dualHom J N b₁).f (i₀ + 1) + (dualHom J N b₂).f (i₀ + 1) -
        (dualHomotopy J N Hd).hom (i₀ + 1) (i₀ + 1 + 1) ≫
          (dualComplex J N B).d (i₀ + 1 + 1) (i₀ + 1) := by
    rw [hD]; simp
  simp only [soL, Preadditive.neg_comp, Preadditive.comp_neg, add_comp, comp_add, assoc]
  rw [c₁, ← assoc (W.hom (i₀ + 1 + 1) (i₀ + 1 + 1 + 1)), eW₁, eH,
    ← assoc ((dualComplex J N Z).d (i₀ + 1) i₀), eD, reassoc_of% c₂,
    ← assoc ((dualComplex J N B).d (i₀ + 1) i₀), eW₀]
  simp only [sub_f_apply, sub_comp, comp_sub, add_comp, comp_add, assoc]
  abel

end SecondOrder

/-! ### Chain maps `D^{N+1-*} ⟶ D` whose top families differ by a boundary -/

section TopDiff

variable {Z : ChainComplex V ℤ}

/-- If two chain maps `M₁, M₂ : Z^{N+1-*} ⟶ Z` have components `M_i.f r = h_i (r - 1) r` (up to
the cast `N + 1 - r = N - (r - 1)`) and `h₁ - h₂ = L d - δ L` for a degree-two family `L`, then
`M₁ ≃ M₂`. -/
def homotopyOfTopDiff (M₁ M₂ : dualComplex J (N + 1) Z ⟶ Z)
    (h₁ h₂ L : ∀ i k, (dualComplex J N Z).X i ⟶ Z.X k)
    (hM₁ : ∀ r, M₁.f r = (Z.XIsoOfEq (by omega : N + 1 - r = N - (r - 1))).hom ≫ h₁ (r - 1) r)
    (hM₂ : ∀ r, M₂.f r = (Z.XIsoOfEq (by omega : N + 1 - r = N - (r - 1))).hom ≫ h₂ (r - 1) r)
    (hL : ∀ i i₀ i₁ i₂, i₀ + 1 = i → i + 1 = i₁ → i₁ + 1 = i₂ →
      h₁ i i₁ - h₂ i i₁ = L i i₂ ≫ Z.d i₂ i₁ - (dualComplex J N Z).d i i₀ ≫ L i₀ i₁) :
    Homotopy M₁ M₂ :=
  Homotopy.equivSubZero.symm <| homotopyCongr (Homotopy.nullHomotopy' fun r r' _ ↦
    (Z.XIsoOfEq (by omega : N + 1 - r = N - (r - 1))).hom ≫ L (r - 1) r') (by
      ext r
      rw [Homotopy.nullHomotopicMap'_f (down_rel_succ r) (down_rel_pred r)]
      have h := hL (r - 1) (r - 1 - 1) r (r + 1) (by omega) (by omega) (by omega)
      have e := XIsoOfEq_star_d (J := J) Z (by omega : N + 1 - (r - 1) = N - (r - 1 - 1))
        (by omega : N + 1 - r = N - (r - 1))
      rw [sub_f_apply, hM₁, hM₂, ← comp_sub, h]
      simp only [comp_sub, dualComplex_d, Linear.units_smul_comp, Linear.comp_units_smul,
        reassoc_of% e]
      rw [show (r - 1).negOnePow = -r.negOnePow by rw [Int.negOnePow_sub, Int.negOnePow_one]; simp]
      simp only [Units.neg_smul, sub_neg_eq_add, assoc]
      abel) rfl

end TopDiff

/-! ### Pushing the union structure forward -/

section Push

variable [HasBinaryBiproducts V] [HasFiniteBiproducts V] [Linear ℚ V]

variable {B : SymPoincare J N} (X : PairOn B) (Y : PairOn B.neg)

/-- The splitting `B ≅ 0 ⊕ B` used by `PairOn.union`. -/
abbrev σU (B : SymPoincare J N) : BdSplit B zeroP B := BdSplit.ofRight B zeroP rfl

lemma union_φ_f (r : ℤ) : (X.union Y).φ.f r = relTop (Glue.δφZ (σU B) X Y) r := rfl

lemma union_p : (X.union Y).p = Glue.pU (σU B) X Y := rfl

/-- The union structure, typed on `Glue.U`. -/
abbrev unionφ : dualComplex J (N + 1) (Glue.U (σU B) X Y) ⟶ Glue.U (σU B) X Y := (X.union Y).φ

/-- The chain map `U^{N+1-*} ⟶ U` with the non-symmetrized union components `relTop Hns`. -/
def unionHns : dualComplex J (N + 1) (Glue.U (σU B) X Y) ⟶ Glue.U (σU B) X Y :=
  unionφ X Y - relTopDiff (Glue.δφZ (σU B) X Y) (Glue.Hns (σU B) X Y)

lemma unionHns_f (r : ℤ) : (unionHns X Y).f r = relTop (Glue.Hns (σU B) X Y) r := by
  rw [unionHns, sub_f_apply, relTopDiff_f, unionφ, union_φ_f]
  abel

/-- The symmetrized union structure is homotopic to the non-symmetrized one. -/
def unionφHomotopy : Homotopy (unionφ X Y) (unionHns X Y) :=
  Homotopy.equivSubZero.symm <| homotopyCongr (relTopDiffHomotopy (Glue.δφZ (σU B) X Y)
    (Glue.Hns (σU B) X Y) (fun i k ↦ (-(1 / 2 : ℚ)) • conjL (-B.φ) (Glue.K' (σU B) X Y) i k) (by
      intro i i₀ i₁ i₂ h₀ h₁ h₂
      have h := conjHomotopy_sub_transpose (-B.φ) (Glue.K' (σU B) X Y) B.symm.neg i i₀ i₁ i₂ h₀ h₁
        h₂
      rw [Glue.δφZ, symmHomotopy_hom, ← transposeHomotopy_hom]
      simp only [Pi.smul_apply, Pi.add_apply, Glue.transposeHomotopy_Hns_hom, Glue.Hns_hom]
      change (Glue.G (σU B) X Y).hom i i₁ - (transposeHomotopy J N (Glue.G (σU B) X Y)).hom i i₁ =
        _ at h
      rw [Linear.smul_comp, Linear.comp_smul, ← smul_sub, ← h]
      module)) (by simp [unionHns]) rfl

section RawFam

variable {Z Bc D₁ D₂ : ChainComplex V ℤ} (φc : dualComplex J N Bc ⟶ Bc)
  (j₁ : Bc ⟶ D₁) (j₂ : Bc ⟶ D₂) (a₁ : D₁ ⟶ Z) (a₂ : D₂ ⟶ Z)
  (δ₁ : ∀ i k, (dualComplex J N D₁).X i ⟶ D₁.X k) (δ₂ : ∀ i k, (dualComplex J N D₂).X i ⟶ D₂.X k)
  (Hd : Homotopy (j₁ ≫ a₁ + j₂ ≫ a₂) 0)

/-- The pushed-forward raw union family `-K^* φ b₁ + b₂^* φ K + a₁^* δ₁ a₁ + a₂^* δ₂ a₂`. -/
def rawFam (i k : ℤ) : (dualComplex J N Z).X i ⟶ Z.X k :=
  -((dualHomotopy J N Hd).hom i k ≫ φc.f k ≫ (j₁ ≫ a₁).f k) +
    (dualHom J N (j₂ ≫ a₂)).f i ≫ φc.f i ≫ Hd.hom i k +
    (dualHom J N a₁).f i ≫ δ₁ i k ≫ a₁.f k + (dualHom J N a₂).f i ≫ δ₂ i k ≫ a₂.f k

end RawFam

variable {X Y} {Z Bc : ChainComplex V ℤ} (F : Glue.U (σU B) X Y ⟶ Z)
  {φc : dualComplex J N Bc ⟶ Bc} (g : B.C ⟶ Bc) (W : Homotopy (dualHom J N g ≫ B.φ ≫ g) φc)
  (j₁ : Bc ⟶ X.D) (j₂ : Bc ⟶ Y.D) (a₁ : X.D ⟶ Z) (a₂ : Y.D ⟶ Z)
  (δ₁ : ∀ i k, (dualComplex J N X.D).X i ⟶ X.D.X k)
  (δ₂ : ∀ i k, (dualComplex J N Y.D).X i ⟶ Y.D.X k)
  (Hd : Homotopy (j₁ ≫ a₁ + j₂ ≫ a₂) 0)


omit [Linear ℚ V] in
lemma push_Hns_hom (hg : B.p ≫ g = g) (hj₁ : X.j = g ≫ j₁) (hj₂ : Y.j = g ≫ j₂)
    (hδ₁ : ∀ i k, X.δφ.hom i k = (dualHom J N j₁).f i ≫ W.hom i k ≫ j₁.f k + δ₁ i k)
    (hδ₂ : ∀ i k, Y.δφ.hom i k = -((dualHom J N j₂).f i ≫ W.hom i k ≫ j₂.f k) + δ₂ i k)
    (ha₁ : Glue.ιW (σU B) X Y ≫ F = a₁) (ha₂ : Glue.ιY (σU B) X Y ≫ F = a₂)
    (hK : ∀ i k, (Glue.K' (σU B) X Y).hom i k ≫ F.f k = g.f i ≫ Hd.hom i k) (i k : ℤ) :
    (dualHom J N F).f i ≫ (Glue.Hns (σU B) X Y).hom i k ≫ F.f k =
      (dualHom J N (j₁ ≫ a₁)).f i ≫ W.hom i k ≫ (j₁ ≫ a₁).f k -
        (dualHom J N (j₂ ≫ a₂)).f i ≫ W.hom i k ≫ (j₂ ≫ a₂).f k -
        (dualHomotopy J N Hd).hom i k ≫ (dualHom J N g ≫ B.φ ≫ g).f k ≫ (j₁ ≫ a₁).f k +
        (dualHom J N (j₂ ≫ a₂)).f i ≫ (dualHom J N g ≫ B.φ ≫ g).f i ≫ Hd.hom i k +
        (dualHom J N a₁).f i ≫ δ₁ i k ≫ a₁.f k + (dualHom J N a₂).f i ≫ δ₂ i k ≫ a₂.f k := by
  have eW (r : ℤ) : (dualHom J N F).f r ≫ (dualHom J N (Glue.ιW (σU B) X Y)).f r =
      (dualHom J N a₁).f r := by rw [← comp_f, ← dualHom_comp, ha₁]
  have eY (r : ℤ) : (dualHom J N F).f r ≫ (dualHom J N (Glue.ιY (σU B) X Y)).f r =
      (dualHom J N a₂).f r := by rw [← comp_f, ← dualHom_comp, ha₂]
  have eW' (r : ℤ) : (Glue.ιW (σU B) X Y).f r ≫ F.f r = a₁.f r := by rw [← comp_f, ha₁]
  have eY' (r : ℤ) : (Glue.ιY (σU B) X Y).f r ≫ F.f r = a₂.f r := by rw [← comp_f, ha₂]
  have eβ : Glue.β' (σU B) X Y ≫ F = g ≫ j₁ ≫ a₁ := by
    change ((B.p ≫ X.j) ≫ Glue.ιW (σU B) X Y) ≫ F = _
    rw [assoc, assoc, ha₁, hj₁, assoc, reassoc_of% hg]
  have ec : Glue.c' (σU B) X Y ≫ F = g ≫ j₂ ≫ a₂ := by
    simp only [Glue.c', Glue.jY, assoc, ha₂, hj₂]
  have eβ' (r : ℤ) : (Glue.β' (σU B) X Y).f r ≫ F.f r = g.f r ≫ j₁.f r ≫ a₁.f r := by
    rw [← comp_f, eβ]; simp
  have ec' (r : ℤ) : (dualHom J N F).f r ≫ (dualHom J N (Glue.c' (σU B) X Y)).f r =
      (dualHom J N (g ≫ j₂ ≫ a₂)).f r := by rw [← comp_f, ← dualHom_comp, ec]
  have eK : (dualHom J N F).f i ≫ (dualHomotopy J N (Glue.K' (σU B) X Y)).hom i k =
      (dualHomotopy J N Hd).hom i k ≫ (dualHom J N g).f k := by
    simp only [dualHomotopy_hom, dualHom_f, Linear.comp_units_smul, Linear.units_smul_comp,
      ← J.star_comp, hK]
  rw [Glue.Hns_hom]
  simp only [Glue.HW, Glue.HY, Glue.G, conjHomotopy_refl_hom, Homotopy.compLeft_hom,
    Homotopy.compRight_hom, comp_add, add_comp, assoc, hδ₁, hδ₂, reassoc_of% eW, reassoc_of% eY,
    eW', eY', reassoc_of% eK, eβ', dualHom_neg, neg_f_apply, Preadditive.neg_comp,
    Preadditive.comp_neg, reassoc_of% ec', hK]
  simp only [comp_f, dualHom_comp, dualHom_f, assoc]
  abel

/-- **Pushing the union structure forward.**  Let `F : X ∪ Y ⟶ Z` be a chain map out of the union
of two pairs on `B` and `-B` whose boundary maps factor as `j_X = g j₁`, `j_Y = g j₂` through a
chain map `g : C_B ⟶ B_c`, with `W : g φ_B g^* ≃ φ_c`, `δφ_X = j₁ W j₁^* + δ₁`,
`δφ_Y = -j₂ W j₂^* + δ₂`, `F ι_X = a₁`, `F ι_Y = a₂`, and `F` on the cone coordinate given by
`g` followed by a null-homotopy `K : j₁ a₁ + j₂ a₂ ≃ 0`.  Then the pushforward `F φ_∪ F^*` of the
union structure is homotopic to any chain map `R` whose components are the raw union family
`-K^* φ_c b₁ + b₂^* φ_c K + a₁^* δ₁ a₁ + a₂^* δ₂ a₂` (`rawFam`). -/
def pushHomotopy (hg : B.p ≫ g = g) (hj₁ : X.j = g ≫ j₁) (hj₂ : Y.j = g ≫ j₂)
    (hδ₁ : ∀ i k, X.δφ.hom i k = (dualHom J N j₁).f i ≫ W.hom i k ≫ j₁.f k + δ₁ i k)
    (hδ₂ : ∀ i k, Y.δφ.hom i k = -((dualHom J N j₂).f i ≫ W.hom i k ≫ j₂.f k) + δ₂ i k)
    (ha₁ : Glue.ιW (σU B) X Y ≫ F = a₁) (ha₂ : Glue.ιY (σU B) X Y ≫ F = a₂)
    (hK : ∀ i k, (Glue.K' (σU B) X Y).hom i k ≫ F.f k = g.f i ≫ Hd.hom i k)
    (R : dualComplex J (N + 1) Z ⟶ Z)
    (hR : ∀ r, R.f r = (Z.XIsoOfEq (by omega : N + 1 - r = N - (r - 1))).hom ≫
      rawFam φc j₁ j₂ a₁ a₂ δ₁ δ₂ Hd (r - 1) r) :
    Homotopy (dualHom J (N + 1) F ≫ unionφ X Y ≫ F) R :=
  (((unionφHomotopy X Y).compRight F).compLeft (dualHom J (N + 1) F)).trans <|
    homotopyOfTopDiff _ R (fun i k ↦ (dualHom J N F).f i ≫ (Glue.Hns (σU B) X Y).hom i k ≫ F.f k)
      _ (soL Hd W) (fun r ↦ by
        simp only [comp_f, dualHom_f, unionHns_f, relTop, assoc, ← star_f_XIsoOfEq_assoc]) hR
      (fun i i₀ i₁ i₂ h₀ h₁ h₂ ↦ by
        rw [← soL_spec Hd W i i₀ i₁ i₂ h₀ h₁ h₂]
        dsimp only
        rw [push_Hns_hom F g W j₁ j₂ a₁ a₂ δ₁ δ₂ Hd hg hj₁ hj₂ hδ₁ hδ₂ ha₁ ha₂ hK, rawFam]
        simp only [sub_f_apply, sub_comp, comp_sub]
        abel)

end Push

/-! ### Retargeting a pair along a boundary map with a structure homotopy -/

section Retarget

variable [HasBinaryBiproducts V] [HasFiniteBiproducts V] [Linear ℚ V]
  {B B' : SymPoincare J N} (X : PairOn B) (g : B'.C ⟶ B.C) (W : Homotopy (dualHom J N g ≫ B'.φ ≫ g) B.φ)

namespace PairOn

/-- The relative structure `j W j^* + δφ` for the boundary structure `g φ' g^*`. -/
def retargetδφ₀ : Homotopy (dualHom J N X.j ≫ (dualHom J N g ≫ B'.φ ≫ g) ≫ X.j) 0 :=
  ((W.compRight X.j).compLeft (dualHom J N X.j)).trans X.δφ

/-- The relative structure of the retargeted pair, on `j' = g j`. -/
def retargetδφ : Homotopy (dualHom J N (g ≫ X.j) ≫ B'.φ ≫ g ≫ X.j) 0 :=
  homotopyCongr (X.retargetδφ₀ g W) (by simp) rfl

lemma retargetδφ_hom : (X.retargetδφ g W).hom =
    (fun r r' ↦ (dualHom J N X.j).f r ≫ W.hom r r' ≫ X.j.f r') + X.δφ.hom := rfl

lemma retargetδφ_kar (r r' : ℤ) : (dualHom J N X.pD).f r ≫ (X.retargetδφ g W).hom r r' ≫
    X.pD.f r' = (X.retargetδφ g W).hom r r' := by
  have hjp : X.j ≫ X.pD = X.j := X.toPair.j_comp_pD
  have h₁ : (dualHom J N X.pD).f r ≫ (dualHom J N X.j).f r = (dualHom J N X.j).f r := by
    rw [← comp_f, ← dualHom_comp, hjp]
  have h₂ : X.j.f r' ≫ X.pD.f r' = X.j.f r' := by rw [← comp_f, hjp]
  simp only [retargetδφ_hom, Pi.add_apply, comp_add, add_comp, assoc, h₂, reassoc_of% h₁,
    X.δφ_kar]

variable {X g W}

lemma isSymmHomotopy_retargetδφ (hW : IsSymmHomotopy J N W) :
    IsSymmHomotopy J N (X.retargetδφ g W) := by
  rw [IsSymmHomotopy, transposeHomotopy_hom, retargetδφ_hom, transposeHomFamily_add,
    transposeHomFamily_conj', transposeHomFamily_eq hW, transposeHomFamily_eq X.symm]

lemma isKarEquiv_retarget (hgk : B'.p ≫ g ≫ B.p = g) (hg : IsKarEquiv B'.p B.p g)
    (hj : B'.p ≫ (g ≫ X.j) ≫ X.pD = g ≫ X.j) :
    IsKarEquiv (dualHom J (N + 1) (coneMap B'.p X.pD (comm_of_kar B'.p_idem X.pD_idem hj))) X.pD
      (relDuality (X.retargetδφ g W)) := by
  have hc : g ≫ X.j = (g ≫ X.j) ≫ X.pD := by simp
  have hC := isKarEquiv_coneMap B'.p_idem X.pD_idem B.p_idem X.pD_idem hj X.j_kar hgk
    (by simp) hc hg (KarHtpyEquiv.refl X.pD_idem).isKarEquiv
  have hl (r r' : ℤ) : (dualHom J N X.pD).f r ≫ (X.retargetδφ g W).hom r r' =
      (X.retargetδφ g W).hom r r' := by
    conv_lhs => rw [← X.retargetδφ_kar g W]
    rw [← assoc, ← comp_f, ← dualHom_comp, X.pD_idem, X.retargetδφ_kar]
  have hr (r r' : ℤ) : (X.retargetδφ g W).hom r r' ≫ X.pD.f r' = (X.retargetδφ g W).hom r r' := by
    conv_lhs => rw [← X.retargetδφ_kar g W]
    rw [assoc, assoc, ← comp_f, X.pD_idem, X.retargetδφ_kar]
  have hid : dualHom J (N + 1) (coneMap _ _ hc) ≫ relDuality (X.retargetδφ g W) =
      relDuality (X.retargetδφ₀ g W) := by
    ext r
    simp [star_coneMap_f hc _ _ (down_rel_sub N r), star_comp_relTop _ hl]
    rfl
  have hΨ := X.poincare.of_homotopy (homotopyCongr (transportRelDualityHomotopy W
    (X.retargetδφ₀ g W) X.δφ fun _ _ ↦ rfl).symm rfl hid.symm)
  refine IsKarEquiv.of_comp_left hC.dualHom (dualHom_kar ?_) hΨ ?_
    (dualHom_idem (Glue.coneIdem_idem X)) (dualHom_idem (coneMap_idem _ B'.p_idem X.pD_idem))
    X.pD_idem
  · rw [coneMap_comp, coneMap_comp]; congr 1; simp
  · rw [← assoc, dualHom_coneMap_comp_relDuality _ _ B'.dualHom_p_comp_φ hl,
      relDuality_comp_pD (by simp) _ hr]

variable (X g W)

lemma retarget_j_kar (hgk : B'.p ≫ g ≫ B.p = g) : B'.p ≫ (g ≫ X.j) ≫ X.pD = g ≫ X.j := by
  have hjp : X.j ≫ X.pD = X.j := X.toPair.j_comp_pD
  rw [assoc, hjp, ← assoc, kar_left B'.p_idem hgk]

/-- **Retargeting a pair** along a Kar equivalence `g : (C', p') ⟶ (C, p)` of boundaries and a
symmetric Kar homotopy `W : g φ' g^* ≃ φ`: the pair `(g j, (j W j^* + δφ, φ'))` on `B'`. -/
@[implicit_reducible]
def retarget (hgk : B'.p ≫ g ≫ B.p = g) (hg : IsKarEquiv B'.p B.p g)
    (hW : IsSymmHomotopy J N W) : PairOn B' where
  D := X.D
  pD := X.pD
  pD_idem := X.pD_idem
  support := X.support
  j := g ≫ X.j
  j_kar := X.retarget_j_kar g hgk
  δφ := X.retargetδφ g W
  δφ_kar := X.retargetδφ_kar g W
  symm := isSymmHomotopy_retargetδφ hW
  poincare := isKarEquiv_retarget hgk hg (X.retarget_j_kar g hgk)

end PairOn

/-! ### Retargeting both halves of a union -/

section RetargetUnion

variable {X} {Y : PairOn B.neg} {g W} (W' : Homotopy (dualHom J N g ≫ B'.neg.φ ≫ g) B.neg.φ)
  (hgk : B'.p ≫ g ≫ B.p = g) (hg : IsKarEquiv B'.p B.p g) (hW : IsSymmHomotopy J N W)
  (hW' : IsSymmHomotopy J N W') (hWW : ∀ i k, W'.hom i k = -W.hom i k)

/-- The pair `X` retargeted to `B'`. -/
abbrev rX : PairOn B' := X.retarget g W hgk hg hW

/-- The pair `Y` retargeted to `B'.neg`. -/
abbrev rY : PairOn B'.neg := Y.retarget g W' hgk hg hW'

lemma retarget_u : g ≫ Glue.u (σU B) X Y =
    Glue.u (σU B') (rX (X := X) (W := W) hgk hg hW) (rY (Y := Y) W' hgk hg hW') ≫ 𝟙 _ := by
  rw [comp_id]
  have h₁ : g ≫ B.p = g := kar_right B.p_idem hgk
  have h₂ : B'.p ≫ g = g := kar_left B'.p_idem hgk
  have h₃ : B.p ≫ X.j = X.j := X.toPair.p_comp_j
  simp only [Glue.u, Glue.β, Glue.jY, comp_add]
  change g ≫ (B.p ≫ X.j) ≫ _ + _ = (B'.p ≫ g ≫ X.j) ≫ _ + (g ≫ Y.j) ≫ _
  rw [reassoc_of% h₂, h₃]
  simp only [assoc]
  rfl

/-- The comparison `rX ∪ rY ⟶ X ∪ Y` before compression, `g ⊕ 1`. -/
abbrev retargetCmp₀ : Glue.U (σU B') (rX (X := X) (W := W) hgk hg hW) (rY (Y := Y) W' hgk hg hW') ⟶
    Glue.U (σU B) X Y :=
  coneMap g (𝟙 _) (retarget_u W' hgk hg hW hW')

/-- The cone null-homotopy of `u` on `X ∪ Y`, as `Homotopy (j_X ι_X + j_Y ι_Y) 0`. -/
def unionK : Homotopy (X.j ≫ Glue.ιW (σU B) X Y + Glue.jY Y ≫ Glue.ιY (σU B) X Y) 0 :=
  homotopyCongr (Homotopy.equivSubZero (Glue.K' (σU B) X Y))
    (by
      have h₃ : B.p ≫ X.j = X.j := X.toPair.p_comp_j
      simp only [Glue.β', Glue.β, Glue.c', Glue.jY, sub_neg_eq_add]
      change (B.p ≫ X.j) ≫ _ + _ = _
      rw [h₃]) rfl

lemma unionK_hom (i k : ℤ) : (unionK (X := X) (Y := Y)).hom i k = (Glue.K' (σU B) X Y).hom i k :=
  rfl

/-- **Retargeting both halves of a union does not change it**: the pushforward of the union
structure of `rX ∪ rY` along `g ⊕ 1` is homotopic to that of `X ∪ Y`. -/
def retargetConj : Homotopy (dualHom J (N + 1) (retargetCmp₀ W' hgk hg hW hW') ≫
    unionφ (rX (X := X) (W := W) hgk hg hW) (rY (Y := Y) W' hgk hg hW') ≫
      retargetCmp₀ W' hgk hg hW hW') (unionφ X Y) :=
  (pushHomotopy (retargetCmp₀ W' hgk hg hW hW') g W X.j (Glue.jY Y) (Glue.ιW (σU B) X Y)
    (Glue.ιY (σU B) X Y) X.δφ.hom Y.δφ.hom (unionK (X := X) (Y := Y)) (kar_left B'.p_idem hgk)
    rfl rfl
    (fun _ _ ↦ rfl)
    (fun i k ↦ by
      change (dualHom J N Y.j).f i ≫ W'.hom i k ≫ Y.j.f k + Y.δφ.hom i k = _
      rw [hWW]
      simp
      rfl)
    (by simp only [Glue.ιW, assoc, Glue.inr_coneMap, id_comp]; rfl)
    (by simp only [Glue.ιY, assoc, Glue.inr_coneMap, id_comp]; rfl)
    (fun i k ↦ by
      by_cases h : (ComplexShape.down ℤ).Rel k i
      · rw [Glue.K'_hom, inrCompHomotopy_hom _ _ _ _ h, unionK_hom, Glue.K'_hom,
          inrCompHomotopy_hom _ _ _ _ h, inlX_coneMap_f]
      · rw [Homotopy.zero _ _ _ h, Homotopy.zero _ _ _ h, zero_comp, comp_zero])
    (unionHns X Y) (fun r ↦ by
      rw [unionHns_f, relTop, rawFam, Glue.Hns_hom]
      simp only [Glue.HW, Glue.HY, Glue.G, conjHomotopy_refl_hom, Homotopy.compLeft_hom,
        Homotopy.compRight_hom, dualHomotopy_hom, unionK_hom]
      have h₃ : B.p ≫ X.j = X.j := X.toPair.p_comp_j
      have hβ : Glue.β' (σU B) X Y = X.j ≫ Glue.ιW (σU B) X Y := by
        change (B.p ≫ X.j) ≫ _ = _; rw [h₃]
      have hβf : (Glue.β' (σU B) X Y).f r = (X.j ≫ Glue.ιW (σU B) X Y).f r := by rw [hβ]
      have hcf : (dualHom J N (-Glue.c' (σU B) X Y)).f (r - 1) =
          -(dualHom J N (Glue.jY Y ≫ Glue.ιY (σU B) X Y)).f (r - 1) := by
        rw [dualHom_neg]; rfl
      simp only [hβf, hcf]
      simp only [dualHom_neg, neg_f_apply, SymPoincare.neg, comp_add, add_comp, comp_neg,
        neg_comp, Preadditive.neg_comp_neg, Preadditive.comp_neg, Preadditive.neg_comp]
      abel)).trans (unionφHomotopy X Y).symm

lemma glue_u_kar {C : SymPoincare J N} (X₀ : PairOn C) (Y₀ : PairOn C.neg) :
    Glue.u (σU C) X₀ Y₀ ≫ Glue.pS X₀ Y₀ = Glue.u (σU C) X₀ Y₀ := by
  have h₁ := Glue.β_pD (σU C) X₀
  have h₂ := Glue.Y_j_comp_pD Y₀
  simp only [Glue.u, Glue.pS, add_comp, comp_add, assoc, sumInl_sumFst_assoc,
    sumInl_sumSnd_assoc, sumInr_sumFst_assoc, sumInr_sumSnd_assoc, zero_comp, comp_zero, add_zero,
    zero_add, reassoc_of% h₁, reassoc_of% h₂]

lemma glue_p_u {C : SymPoincare J N} (X₀ : PairOn C) (Y₀ : PairOn C.neg) :
    C.p ≫ Glue.u (σU C) X₀ Y₀ = Glue.u (σU C) X₀ Y₀ := by
  rw [Glue.u_pS (σU C) X₀ Y₀, glue_u_kar]

lemma retarget_u_pS : g ≫ Glue.u (σU B) X Y =
    Glue.u (σU B') (rX (X := X) (W := W) hgk hg hW) (rY (Y := Y) W' hgk hg hW') ≫ Glue.pS X Y :=
  (retarget_u W' hgk hg hW hW').trans ((comp_id _).trans
    (glue_u_kar (rX (X := X) (W := W) hgk hg hW) (rY (Y := Y) W' hgk hg hW')).symm)

lemma retargetCmp₀_pU : retargetCmp₀ W' hgk hg hW hW' ≫ (X.union Y).p =
    coneMap g (Glue.pS X Y) (retarget_u_pS W' hgk hg hW hW') := by
  have h₁ (n : ℤ) : g.f n ≫ B.p.f n = g.f n := by rw [← comp_f, kar_right B.p_idem hgk]
  rw [union_p]
  ext n : 1
  apply ext_from_X (Glue.u (σU B') (rX (X := X) (W := W) hgk hg hW) (rY (Y := Y) W' hgk hg hW'))
    (n - 1) n (by simp)
  · simp only [comp_f, inlX_coneMap_f_assoc, inlX_coneMap_f, reassoc_of% h₁]
  · simp only [comp_f, inrX_coneMap_f_assoc, inrX_coneMap_f, id_f, id_comp]

lemma retarget_f_kar :
    ((rX (X := X) (W := W) hgk hg hW).union (rY (Y := Y) W' hgk hg hW')).p ≫
      (retargetCmp₀ W' hgk hg hW hW' ≫ (X.union Y).p) ≫ (X.union Y).p =
      retargetCmp₀ W' hgk hg hW hW' ≫ (X.union Y).p := by
  have h₁ (n : ℤ) : g.f n ≫ B.p.f n = g.f n := by rw [← comp_f, kar_right B.p_idem hgk]
  have h₂ (n : ℤ) : B'.p.f n ≫ g.f n = g.f n := by rw [← comp_f, kar_left B'.p_idem hgk]
  have h₃ (n : ℤ) : (Glue.pS X Y).f n ≫ (Glue.pS X Y).f n = (Glue.pS X Y).f n := by
    rw [← comp_f, Glue.pS_idem]
  rw [retargetCmp₀_pU, union_p, union_p]
  ext n : 1
  apply ext_from_X (Glue.u (σU B') (rX (X := X) (W := W) hgk hg hW) (rY (Y := Y) W' hgk hg hW'))
    (n - 1) n (by simp)
  · simp only [comp_f, inlX_coneMap_f_assoc, inlX_coneMap_f, reassoc_of% h₁, reassoc_of% h₂]
  · simp only [comp_f, inrX_coneMap_f_assoc, inrX_coneMap_f]
    rw [reassoc_of% h₃]
    erw [reassoc_of% (h₃ n)]

lemma isKarEquiv_retargetCmp :
    IsKarEquiv ((rX (X := X) (W := W) hgk hg hW).union (rY (Y := Y) W' hgk hg hW')).p
      (X.union Y).p (retargetCmp₀ W' hgk hg hW hW' ≫ (X.union Y).p) := by
  have hpS := Glue.pS_idem X Y
  have hj' : B'.p ≫ Glue.u (σU B') (rX (X := X) (W := W) hgk hg hW) (rY (Y := Y) W' hgk hg hW') ≫
      Glue.pS X Y = Glue.u (σU B') (rX (X := X) (W := W) hgk hg hW) (rY (Y := Y) W' hgk hg hW') :=
    (congrArg (B'.p ≫ ·) (glue_u_kar (rX (X := X) (W := W) hgk hg hW)
      (rY (Y := Y) W' hgk hg hW'))).trans (glue_p_u _ _)
  have hj : B.p ≫ Glue.u (σU B) X Y ≫ Glue.pS X Y = Glue.u (σU B) X Y := by
    rw [glue_u_kar, glue_p_u]
  rw [retargetCmp₀_pU]
  exact isKarEquiv_coneMap B'.p_idem hpS B.p_idem hpS hj' hj hgk (by simp [hpS])
    (retarget_u_pS W' hgk hg hW hW') hg (KarHtpyEquiv.refl hpS).isKarEquiv

include hWW in
/-- **Retargeting both halves of a union gives a homotopy isometric union.** -/
theorem nonempty_retarget_union_isometry :
    Nonempty (((rX (X := X) (W := W) hgk hg hW).union (rY (Y := Y) W' hgk hg hW')).HomotopyIsometry
      (X.union Y)) := by
  obtain ⟨g', hg', ⟨H₁⟩, ⟨H₂⟩⟩ := isKarEquiv_retargetCmp W' hgk hg hW hW'
  exact ⟨⟨_, g', retarget_f_kar W' hgk hg hW hW', hg', H₂, H₁,
    homotopyCongr (((retargetConj W' hgk hg hW hW' hWW).compRight
      (X.union Y).p).compLeft (dualHom J (N + 1) (X.union Y).p)) (by simp only [dualHom_comp,
        assoc]) (X.union Y).φ_kar⟩⟩

end RetargetUnion

/-! ### Retargeting along a homotopy isometry of boundaries -/

section IsoRetarget

variable {B B' : SymPoincare J N} (e : B.HomotopyIsometry B')

/-- The symmetrized structure homotopy `g φ' g^* ≃ φ` of an isometry `e : B ≃ B'` (`g = e.g`). -/
def isoW : Homotopy (dualHom J N e.g ≫ B'.φ ≫ e.g) B.φ :=
  symmHomotopy (B'.symm.conj e.g) B.symm e.symm.conj

lemma isoW_symm : IsSymmHomotopy J N (isoW e) := isSymmHomotopy_symmHomotopy _ _ _

/-- The negated structure homotopy, for `-B ≃ -B'`. -/
def isoWneg : Homotopy (dualHom J N e.g ≫ B'.neg.φ ≫ e.g) B.neg.φ :=
  homotopyCongr ((isoW e).smul (-1 : ℤ)) (by simp [SymPoincare.neg]) (by simp [SymPoincare.neg])

lemma isoWneg_hom (i k : ℤ) : (isoWneg e).hom i k = -(isoW e).hom i k := by
  simp [isoWneg]

lemma isoWneg_symm : IsSymmHomotopy J N (isoWneg e) := by
  have h := isoW_symm e
  rw [IsSymmHomotopy, transposeHomotopy_hom] at h ⊢
  funext r r'
  have h' := congrFun (congrFun h r) r'
  simp only [transposeHomFamily] at h' ⊢
  rw [isoWneg_hom, isoWneg_hom, ← h']
  simp [StrictInvolution.star_neg]

lemma iso_g_isKarEquiv : IsKarEquiv B'.p B.p e.g := e.symm.toKarHtpyEquiv.isKarEquiv

/-- A pair on `B`, retargeted to `B'` along `e`. -/
abbrev PairOn.retargetIso (X : PairOn B) : PairOn B' :=
  X.retarget e.g (isoW e) e.g_kar (iso_g_isKarEquiv e) (isoW_symm e)

/-- A pair on `-B`, retargeted to `-B'` along `e`. -/
abbrev PairOn.retargetIsoNeg (Y : PairOn B.neg) : PairOn B'.neg :=
  Y.retarget e.g (isoWneg e) e.g_kar (iso_g_isKarEquiv e) (isoWneg_symm e)

/-- **The union of two pairs retargeted along an isometry of boundaries is homotopy isometric to
the original union.** -/
theorem nonempty_union_retargetIso (X : PairOn B) (Y : PairOn B.neg) :
    Nonempty (((X.retargetIso e).union (Y.retargetIsoNeg e)).HomotopyIsometry (X.union Y)) :=
  nonempty_retarget_union_isometry (X := X) (Y := Y) (isoWneg e) e.g_kar (iso_g_isKarEquiv e)
    (isoW_symm e) (isoWneg_symm e) (isoWneg_hom e)

end IsoRetarget

end Retarget

end

end HSFormal.LTheory
