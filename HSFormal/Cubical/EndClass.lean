import HSFormal.Bridges
import HSFormal.Cubical.SeqDual
import HSFormal.Cubical.PinchCut
import HSFormal.LTheory.TailSignature

/-!
# The end class `[pt ⊗ CPcell]` and `σ_tail = 1` (manuscript (11.5), §12; S12a)

The last stage of the cube-cut iteration (`CubeCutSteps.last`, `PinchSignature.lean`): the class
of the constant sequence `pt ⊗ CPcell`, pushed to `𝒜_1(pt)` (scalar group `scalarHom H`), has
`σ_tail = 1`, for every `LowerLTheory`.

* `ControlledSeq.cpConst ℓ` / `cpConstDuality ℓ`: the constant sequence `CPcell` over `Y`, all
  cells of the `i`-th term at `ℓ i`, with `CPcell.duality` at every index.
* `SymDuality.symPoincare_map_forgetControl`: forgetting control of a chain model is the chain
  model with labels at the point (`toPt`), by `rfl`.
* `FreeQG.evalFactorIso`: `evalQG i ≫ factorFS i ≅ factor i` (unitary); `factorIsometry`: the
  `i`-th factor of a chain model over the point is the based realization (`matRealization`) of
  its `i`-th term in `Free(ℚ) = PermRep Unit Unit`.
* `SymDuality.basedSig`: the ordinary signature of a based `4`-dimensional symmetric duality;
  `CPcell.basedSig_duality : σ(CPcell) = 1` (`cpSymPoincare_unit_sign₄_one`), invariance under
  bijections of cells (`basedSig_eq_of_equiv`).
* **`σtail_forgetControl_symPoincare`**: `σ_tail` of a chain model over any `Y`, pushed to the
  point, is the germ of the signatures of its terms (`toPoint`, `σtail_toPoint`, `coord_cls`).
* **`endClass`**, **`σtail_endClass`** (`= 1`), **`endClass_isSignTail`**, and the forms used at
  the last stage of `CubeCutSteps`: `isSignTail_σtail_map_forgetControl(_cpConst)`.
-/

noncomputable section

namespace HSFormal.Cubical

open Filter Matrix CategoryTheory HSFormal.LTheory HSFormal.Compression AsymptoticCategory

namespace BasedComplex

/-- Every action on a point is isometric. -/
instance EndClass.isIsometricSMul_punit (H : Type*) [SMul H PUnit] [PseudoEMetricSpace PUnit] :
    IsIsometricSMul H PUnit := ⟨fun _ ↦ isometry_subsingleton⟩

namespace ControlledSeq

/-- Over a point every matrix sequence is controlled. -/
theorem PropTendsto.punit {C D : ℕ → BasedComplex} (u : ∀ i, Matrix (D i).X (C i).X ℚ)
    (a : ∀ i, (C i).X → PUnit.{1}) (b : ∀ i, (D i).X → PUnit.{1}) : PropTendsto u a b :=
  tendsto_zero_of_forall_eq_zero fun _ ↦ prop_punit _ _ _

variable {Y : Type} [PseudoEMetricSpace Y]

/-- Forgetting the control of a sequence: the same complexes, labelled by the point. -/
def toPt (A : ControlledSeq Y) : ControlledSeq PUnit.{1} where
  C := A.C
  label _ _ := PUnit.unit
  tendsto_d := PropTendsto.punit _ _ _

variable {A : ControlledSeq Y} {N : ℕ} {hN : A.DimLE N}

/-- The same symmetric duality on the sequence with forgotten control. -/
def SymDuality.toPt (P : A.SymDuality N hN) : A.toPt.SymDuality N hN :=
  SymDuality.ofSeq P.term (PropTendsto.punit _ _ _) (PropTendsto.punit _ _ _)
    (PropTendsto.punit _ _ _) (PropTendsto.punit _ _ _)

/-- Matrix sequences between cells all labelled by the same point `ℓ i` have propagation `0`. -/
theorem PropTendsto.const {C D : ℕ → BasedComplex} (u : ∀ i, Matrix (D i).X (C i).X ℚ)
    (ℓ : ℕ → Y) : PropTendsto u (fun i (_ : (C i).X) ↦ ℓ i) (fun i (_ : (D i).X) ↦ ℓ i) :=
  tendsto_zero_of_forall_eq_zero fun _ ↦
    le_antisymm (prop_le_iff.mpr fun _ _ _ ↦ by simp) bot_le

/-- **The constant sequence `pt ⊗ CPcell`** over `Y`, all cells of the `i`-th term at `ℓ i`. -/
def cpConst (ℓ : ℕ → Y) : ControlledSeq Y where
  C _ := CPcell
  label i _ := ℓ i
  tendsto_d := PropTendsto.const _ ℓ

theorem cpConst_dimLE (ℓ : ℕ → Y) : (cpConst ℓ).DimLE 4 := fun _ ↦ CPcell.dimLE

/-- Its symmetric duality, `CPcell.duality` at every index. -/
def cpConstDuality (ℓ : ℕ → Y) : (cpConst ℓ).SymDuality 4 (cpConst_dimLE ℓ) :=
  SymDuality.ofSeq (fun _ ↦ CPcell.duality) (PropTendsto.const _ ℓ) (PropTendsto.const _ ℓ)
    (PropTendsto.const _ ℓ) (PropTendsto.const _ ℓ)

variable {H : Type} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  (π : ∀ i, G i →* H) [MulAction H Y] [IsIsometricSMul H Y]

/-- Forgetting control on the controlled Poincaré complex of a chain model. -/
theorem SymDuality.symPoincare_map_forgetControl (P : A.SymDuality N hN) :
    (P.symPoincare π).map (forgetControl π Y) = P.toPt.symPoincare π :=
  rfl

end ControlledSeq

end BasedComplex
end HSFormal.Cubical

/-! ### The `i`-th factor through the coordinate projection -/

namespace HSFormal.LTheory.FreeQG

open CategoryTheory AsymptoticObject

variable {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)] [∀ i, DecidableEq (G i)]

lemma factor_map_idem_self (M : prodFreeQG G) (i : ℕ) :
    (factor G i).F.map (idem M {i}) = 𝟙 _ := by
  classical
  refine PermRep.hom_ext ?_
  change (idem M {i}).1 i = _
  rw [idem_val, if_pos (Set.mem_singleton i)]
  exact one_eq_one

/-- The coordinate projection followed by the factor `L^p_*(ℚ[Gᵢ]) → Free(ℚ[Gᵢ])` is unitarily
isomorphic to the `i`-th factor itself (via `inc`/`prj`). -/
def evalFactorIso (i : ℕ) :
    InvCat.UnitaryIso (evalQG G i ≫ factorFS G i) (factor G i) where
  iso := NatIso.ofComponents (fun M ↦
    { hom := (factor G i).F.map (inc M {i})
      inv := (factor G i).F.map (prj M {i})
      hom_inv_id := by
        erw [← CategoryTheory.Functor.map_comp, inc_prj]; exact (factor G i).F.map_id _
      inv_hom_id := by
        erw [← CategoryTheory.Functor.map_comp, prj_inc, factor_map_idem_self] })
    fun {M N} f ↦ by
      change (factor G i).F.map (inc M {i} ≫ f ≫ prj N {i}) ≫ (factor G i).F.map (inc N {i}) =
        (factor G i).F.map (inc M {i}) ≫ (factor G i).F.map f
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, Category.assoc,
        Category.assoc, prj_inc, ← idem_comm, ← Category.assoc, inc_idem]
  star_hom M := by
    change (PermRep.invCat (G i) (G i)).inv.star ((factor G i).F.map (inc M {i})) =
      (factor G i).F.map (prj M {i})
    rw [← (factor G i).map_star, star_inc]

end HSFormal.LTheory.FreeQG

/-! ### The factors of a sequence over a point are the based realizations -/

namespace HSFormal.Cubical.BasedComplex.ControlledSeq

open CategoryTheory HSFormal.LTheory HSFormal.LTheory.FreeQG HSFormal.Compression
open scoped Kronecker

/-- The trivial homomorphisms `Unit →* Unit` of `∏ᵢ Free(ℚ)`. -/
abbrev πpt : ∀ _ : ℕ, Unit →* Unit := fun _ ↦ 1

variable {A B : ControlledSeq PUnit.{1}}

/-- The `i`-th factor of a controlled matrix sequence over a point is the based realization
`blk u_i ⊗ 1` of its `i`-th term in `Free(ℚ) = PermRep Unit Unit`. -/
theorem factor_map_hom (u : ∀ i, Matrix (B.C i).X (A.C i).X ℚ) (hu : PropTendsto u A.label B.label)
    (r r' : ℤ) (i : ℕ) :
    (factor (fun _ ↦ Unit) i).F.map (hom πpt u hu r r') =
      (PermRep.matRealization Unit Unit).mat (MatRealization.blk (u i)
        (fun σ ↦ ((A.C i).deg σ : ℤ) = r) fun σ ↦ ((B.C i).deg σ : ℤ) = r') := by
  refine PermRep.hom_ext ?_
  ext ⟨k, ⟨⟩⟩ ⟨k', ⟨⟩⟩
  change (hom πpt u hu r r').1 i (k, ()) (k', ()) = PermRep.kronOne Unit _ (k, ()) (k', ())
  simp [hom_val, block, PermRep.kronOne, cellEquiv] <;> rfl

variable {N : ℕ} {hN : A.DimLE N}

/-- The controlled Poincaré complex of a chain model over a point, as a complex over
`∏ᵢ Free(ℚ)`. -/
abbrev SymDuality.prodSymPoincare (P : A.SymDuality N hN) :
    SymPoincare (prodFreeQG fun _ ↦ Unit).inv N :=
  P.symPoincareObj πpt

lemma SymDuality.prodSymPoincare_map_factor_p (P : A.SymDuality N hN) (i : ℕ) :
    (P.prodSymPoincare.map (factor (fun _ ↦ Unit) i)).p = 𝟙 _ := by
  ext r : 1
  exact (factor (fun _ ↦ Unit) i).F.map_id _

/-- **The `i`-th factor** of the controlled Poincaré complex of a chain model over a point is the
based realization of its `i`-th term in `Free(ℚ)` (identity components). -/
def SymDuality.factorIsometry (P : A.SymDuality N hN) (i : ℕ) :
    (P.prodSymPoincare.map (factor (fun _ ↦ Unit) i)).HomotopyIsometry
      ((PermRep.matRealization Unit Unit).symPoincare (P.term i)) := by
  let e : (P.prodSymPoincare.map (factor (fun _ ↦ Unit) i)).C ≅
      ((PermRep.matRealization Unit Unit).symPoincare (P.term i)).C :=
    HomologicalComplex.Hom.isoOfComponents (fun r ↦ Iso.refl _) fun r r' _ ↦ by
      change 𝟙 _ ≫ (PermRep.matRealization Unit Unit).mat _ =
        (factor _ i).F.map (hom πpt _ A.tendsto_d r r') ≫ 𝟙 _
      erw [factor_map_hom, Category.id_comp, Category.comp_id]
  have hp := P.prodSymPoincare_map_factor_p i
  have hp' : ((PermRep.matRealization Unit Unit).symPoincare (P.term i)).p = 𝟙 _ := rfl
  refine SymPoincare.HomotopyIsometry.ofEq e.hom e.inv ?_ ?_ ?_ ?_ ?_
  · rw [hp, hp', Category.id_comp, Category.comp_id]
  · rw [hp, hp', Category.id_comp, Category.comp_id]
  · rw [e.hom_inv_id, hp]
  · rw [e.inv_hom_id, hp']
  · ext r : 1
    change (PermRep.inv Unit Unit).star (𝟙 _) ≫ (factor _ i).F.map ((dualityMap πpt hN P.hom).f r) ≫
      𝟙 _ = ((PermRep.matRealization Unit Unit).dualityMap (P.term i).hom).f r
    erw [(PermRep.inv Unit Unit).star_id, Category.id_comp, Category.comp_id, dualityMap_f,
      MatRealization.dualityMap_f, factor_map_hom]
    rfl

end HSFormal.Cubical.BasedComplex.ControlledSeq

/-! ### `σ_tail` of a chain model over a point -/

namespace HSFormal.Cubical.BasedComplex

open HSFormal.LTheory

/-- The ordinary signature of a based `4`-dimensional symmetric duality, i.e. of its realization
in `Free(ℚ) = PermRep Unit Unit`. -/
def SymDuality.basedSig {C : BasedComplex} {hC : C.DimLE 4} (D : SymDuality C 4 hC) : ℤ :=
  PermRep.sigHom 2 (by norm_num) even_two
    (Lconc.cls ((PermRep.matRealization Unit Unit).symPoincare D))

/-- `σ(CPcell) = 1`. -/
theorem CPcell.basedSig_duality : CPcell.duality.basedSig = 1 := by
  apply Int.cast_injective (α := ℂ)
  rw [SymDuality.basedSig, ← PermRep.signHom_apply_one, PermRep.signHom_cls, Int.cast_one]
  exact PermRep.cpSymPoincare_unit_sign₄_one

end HSFormal.Cubical.BasedComplex

/-! ### Invariance of the based signature under bijections of cells -/

namespace HSFormal.Cubical

open Matrix CategoryTheory HSFormal.Compression HSFormal.LTheory

namespace BasedComplex

variable {C C' : BasedComplex}

/-- The permutation matrix `e_* : ℚ^{C.X} → ℚ^{C'.X}` of a bijection of cells. -/
def permMat (e : C.X ≃ C'.X) : Matrix C'.X C.X ℚ := Matrix.of fun a b ↦ if a = e b then 1 else 0

theorem mul_permMat (e : C.X ≃ C'.X) {κ : Type*} (M : Matrix κ C'.X ℚ) :
    M * permMat e = Matrix.of fun a b ↦ M a (e b) := by
  ext a b; simp [permMat, mul_apply]

theorem permMat_mul (e : C.X ≃ C'.X) {κ : Type*} (M : Matrix C.X κ ℚ) :
    permMat e * M = Matrix.of fun a b ↦ M (e.symm a) b := by
  ext a b
  simp only [permMat, mul_apply, of_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (e.symm a) (fun x _ hx ↦ if_neg fun h ↦ hx (by simp [h]))
    (by simp), if_pos (e.apply_symm_apply a).symm]

theorem permMat_transpose (e : C.X ≃ C'.X) : (permMat e)ᵀ = permMat e.symm := by
  ext a b; simp [permMat, Equiv.eq_symm_apply, eq_comm]

/-- The based isomorphism of a degree- and boundary-preserving bijection of cells. -/
def Hom.ofEquiv (e : C.X ≃ C'.X) (hdeg : ∀ σ, C'.deg (e σ) = C.deg σ)
    (hd : ∀ σ τ, C'.d (e σ) (e τ) = C.d σ τ) : Hom C C' where
  f := permMat e
  deg0 σ τ h := by
    obtain rfl : σ = e τ := by by_contra h'; exact h (by simp [permMat, h'])
    simp [hdeg]
  comm := by
    rw [mul_permMat, permMat_mul]
    ext a b
    simp only [of_apply]
    rw [← hd, e.apply_symm_apply]

end BasedComplex
end HSFormal.Cubical

namespace HSFormal.Cubical.MatRealization

open CategoryTheory Matrix HSFormal.Compression HSFormal.LTheory BasedComplex

universe v u

variable {V : Type u} [Category.{v} V] [Preadditive V] {J : StrictInvolution V}
  (R : MatRealization J) {N : ℕ} {C C' : BasedComplex} {hC : C.DimLE N} {hC' : C'.DimLE N}

/-- A based isomorphism `F` (exact inverse `G`) with `F φ Fᵀ = φ'` realizes to a homotopy
isometry of the realized symmetric Poincaré complexes. -/
def symPoincareIsometry (D : SymDuality C N hC) (D' : SymDuality C' N hC') (F : Hom C C')
    (G : Hom C' C) (hGF : G.f * F.f = 1) (hFG : F.f * G.f = 1)
    (hφ : F.f * D.hom.f * F.fᵀ = D'.hom.f) :
    (R.symPoincare D).HomotopyIsometry (R.symPoincare D') :=
  SymPoincare.HomotopyIsometry.ofEq (R.hom F) (R.hom G)
    (by change 𝟙 _ ≫ R.hom F ≫ 𝟙 _ = _; simp)
    (by change 𝟙 _ ≫ R.hom G ≫ 𝟙 _ = _; simp)
    (by erw [← R.hom_comp, show G.comp F = Hom.id C from Hom.ext hGF, R.hom_id]; rfl)
    (by erw [← R.hom_comp, show F.comp G = Hom.id C' from Hom.ext hFG, R.hom_id]; rfl)
    (by
      ext r
      simp only [HomologicalComplex.comp_f, dualHom_f, symPoincare_φ, dualityMap_f, hom_f,
        R.star_mat, blk_transpose]
      erw [← R.mat_mul, ← R.mat_mul, blk_mul _ _ fun κ σ h hσ ↦ ?_, blk_mul _ _ fun κ σ h hσ ↦ ?_,
        ← hφ, Matrix.mul_assoc]
      · have h₁ := F.deg0 σ κ h
        change (C'.deg σ : ℤ) = _ at hσ
        change (C.deg κ : ℤ) = _
        omega
      · have h₁ : (C.deg κ : ℤ) = ((N - C.deg σ : ℕ) : ℤ) + 0 := D.hom.deg0 κ σ h
        have h₂ := hC σ
        change (C.deg σ : ℤ) = _ at hσ
        change (C.deg κ : ℤ) = _
        omega)

end HSFormal.Cubical.MatRealization

namespace HSFormal.Cubical.BasedComplex

open Matrix HSFormal.LTheory

variable {C C' : BasedComplex}

theorem permMat_symm_mul (e : C.X ≃ C'.X) : permMat e.symm * permMat e = 1 := by
  rw [permMat_mul]
  ext a b
  simp [permMat, one_apply, e.injective.eq_iff]

/-- **Invariance of the based signature** under a bijection of cells preserving degrees, boundary
and duality. -/
theorem SymDuality.basedSig_eq_of_equiv {hC : C.DimLE 4} {hC' : C'.DimLE 4}
    (D : SymDuality C 4 hC) (D' : SymDuality C' 4 hC') (e : C.X ≃ C'.X)
    (hdeg : ∀ σ, C'.deg (e σ) = C.deg σ) (hd : ∀ σ τ, C'.d (e σ) (e τ) = C.d σ τ)
    (hφ : ∀ σ τ, D'.hom.f (e σ) (e τ) = D.hom.f σ τ) : D'.basedSig = D.basedSig := by
  have hdeg' (σ : C'.X) : C.deg (e.symm σ) = C'.deg σ := by
    rw [← hdeg, e.apply_symm_apply]
  have hd' (σ τ : C'.X) : C.d (e.symm σ) (e.symm τ) = C'.d σ τ := by
    rw [← hd, e.apply_symm_apply, e.apply_symm_apply]
  refine (congrArg (PermRep.sigHom 2 (by norm_num) even_two) (Lconc.cls_eq_of_isometry
    ((PermRep.matRealization Unit Unit).symPoincareIsometry D D' (Hom.ofEquiv e hdeg hd)
      (Hom.ofEquiv e.symm hdeg' hd') (permMat_symm_mul e) (by simpa [Hom.ofEquiv] using permMat_symm_mul e.symm)
      ?_))).symm
  have key (M : Matrix C.X C.X ℚ) :
      permMat e * M * (permMat e)ᵀ = of fun a b ↦ M (e.symm a) (e.symm b) := by
    rw [permMat_transpose, mul_permMat, permMat_mul]
    rfl
  refine (key D.hom.f).trans ?_
  ext a b
  rw [of_apply, ← hφ, e.apply_symm_apply, e.apply_symm_apply]

/-- A based symmetric duality isomorphic (by a bijection of cells) to `CPcell` has signature `1`. -/
theorem SymDuality.basedSig_eq_one_of_equiv_CPcell {hC' : C'.DimLE 4} (D' : SymDuality C' 4 hC')
    (e : CPcell.X ≃ C'.X) (hdeg : ∀ σ, C'.deg (e σ) = CPcell.deg σ)
    (hd : ∀ σ τ, C'.d (e σ) (e τ) = CPcell.d σ τ)
    (hφ : ∀ σ τ, D'.hom.f (e σ) (e τ) = CPcell.φ.f σ τ) : D'.basedSig = 1 :=
  (SymDuality.basedSig_eq_of_equiv CPcell.duality D' e hdeg hd hφ).trans CPcell.basedSig_duality

end HSFormal.Cubical.BasedComplex

namespace HSFormal.LTheory.LowerLTheory

open CategoryTheory Filter HSFormal.Cubical HSFormal.Cubical.BasedComplex
  HSFormal.Cubical.BasedComplex.ControlledSeq
  FreeQG AsymptoticCategory

variable (𝕃 : LowerLTheory) {H : Type} [Group H]

/-- **`σ_tail` of a chain model over a point** (scalar group): the sequence of the signatures of
its terms. -/
theorem σtail_symPoincare_pt {A : ControlledSeq PUnit.{1}} {hN : A.DimLE 4}
    (P : A.SymDuality 4 hN) :
    𝕃.σtail (scalarHom H) (𝕃.cls _ 4 (Lconc.cls (P.symPoincare (scalarHom H)))) =
      ((fun i ↦ (P.term i).basedSig : ℕ → ℤ) : Germ atTop ℤ) := by
  have h : P.symPoincare (scalarHom H) = P.prodSymPoincare.map (toPoint _ (scalarHom H)) := rfl
  rw [h, ← Lconc.map_cls, 𝕃.cls_map, σtail_toPoint]
  congr 1
  funext i
  rw [coord_cls, sigAt, AddMonoidHom.comp_apply, ← AddMonoidHom.comp_apply (Lconc.map _),
    ← Lconc.map_comp, Lconc.map_eq_of_unitaryIso (evalFactorIso i), Lconc.map_cls,
    Lconc.cls_eq_of_isometry (P.factorIsometry i)]
  rfl

/-- **`σ_tail` after forgetting control** (scalar group): for the controlled Poincaré complex of
a chain model over any `Y`, pushed to the point, `σ_tail` is the sequence of the signatures of
its terms. -/
theorem σtail_forgetControl_symPoincare {Y : Type} [PseudoEMetricSpace Y] [MulAction H Y]
    [IsIsometricSMul H Y] {A : ControlledSeq Y} {hN : A.DimLE 4} (P : A.SymDuality 4 hN) :
    𝕃.σtail (scalarHom H) (𝕃.map (forgetControl (scalarHom H) Y) 4
        (𝕃.cls _ 4 (Lconc.cls (P.symPoincare (scalarHom H))))) =
      ((fun i ↦ (P.term i).basedSig : ℕ → ℤ) : Germ atTop ℤ) := by
  erw [← 𝕃.cls_map, Lconc.map_cls, P.symPoincare_map_forgetControl, σtail_symPoincare_pt]
  rfl

/-- A chain model over `Y` whose terms have signature `±1` eventually has a sign tail after
forgetting control. -/
theorem isSignTail_σtail_forgetControl {Y : Type} [PseudoEMetricSpace Y] [MulAction H Y]
    [IsIsometricSMul H Y] {A : ControlledSeq Y} {hN : A.DimLE 4} (P : A.SymDuality 4 hN)
    (h : ∀ᶠ i in atTop, IsUnit (P.term i).basedSig) :
    IsSignTail (𝕃.σtail (scalarHom H) (𝕃.map (forgetControl (scalarHom H) Y) 4
        (𝕃.cls _ 4 (Lconc.cls (P.symPoincare (scalarHom H)))))) := by
  rw [σtail_forgetControl_symPoincare]
  exact isSignTail_coe.mpr h

/-! ### The end class `[pt ⊗ CPcell]` -/

variable (H) in
/-- **The end class** `[pt ⊗ CPcell] ∈ L_4(𝒜_1(pt))` of the cube-cut iteration (11.5): the class of
the constant sequence `CPcell` over the point (scalar group `1 → H`). -/
def endClass : 𝕃.L (asymptoticInvCat (scalarHom H) PUnit) 4 :=
  𝕃.cls _ 4 (Lconc.cls ((cpConstDuality fun _ ↦ PUnit.unit).symPoincare (scalarHom H)))

/-- Forgetting the control of the constant sequence `pt ⊗ CPcell` at points `ℓ i` of any `Y`
gives the end class. -/
theorem map_forgetControl_cpConst {Y : Type} [PseudoEMetricSpace Y] [MulAction H Y]
    [IsIsometricSMul H Y] (ℓ : ℕ → Y) :
    𝕃.map (forgetControl (scalarHom H) Y) 4
        (𝕃.cls _ 4 (Lconc.cls ((cpConstDuality ℓ).symPoincare (scalarHom H)))) =
      𝕃.endClass H := by
  rw [← 𝕃.cls_map, Lconc.map_cls]
  rfl

/-- **(11.5), equality form**: `σ_tail[pt ⊗ CPcell] = 1` (the constant germ `1`), for every
`LowerLTheory`. -/
theorem σtail_endClass : 𝕃.σtail (scalarHom H) (𝕃.endClass H) = 1 := by
  rw [endClass, σtail_symPoincare_pt]
  exact congrArg _ (funext fun _ ↦ CPcell.basedSig_duality)

/-- **(11.5)**: `σ_tail[pt ⊗ CPcell]` is a sign tail (the last stage of `CubeCutSteps`). -/
theorem endClass_isSignTail : IsSignTail (𝕃.σtail (scalarHom H) (𝕃.endClass H)) := by
  rw [σtail_endClass]
  exact isSignTail_coe.mpr (Eventually.of_forall fun _ ↦ isUnit_one)

/-- **The last stage of `CubeCutSteps`, general form**: if a class `z` maps (e.g. under the
inclusion `𝒜_P(Y) ⊂ 𝒜_1(Y)` of a support filtration) to `±` the class of a chain model whose terms
eventually have signature `±1`, then `σ_tail` of `z` pushed to the point is a sign tail. -/
theorem isSignTail_σtail_map_forgetControl {Y : Type} [PseudoEMetricSpace Y] [MulAction H Y]
    [IsIsometricSMul H Y] {B : InvCat} (Φ : B ⟶ asymptoticInvCat (scalarHom H) Y)
    (z : 𝕃.L B 4) {A : ControlledSeq Y} {hN : A.DimLE 4} (P : A.SymDuality 4 hN) (u : ℤˣ)
    (hz : 𝕃.map Φ 4 z = u • 𝕃.cls _ 4 (Lconc.cls (P.symPoincare (scalarHom H))))
    (h : ∀ᶠ i in atTop, IsUnit (P.term i).basedSig) :
    IsSignTail (𝕃.σtail (scalarHom H) (𝕃.map (Φ ≫ forgetControl (scalarHom H) Y) 4 z)) := by
  rw [← map_map, hz, Units.smul_def, map_zsmul, map_zsmul, ← Units.smul_def]
  exact (𝕃.isSignTail_σtail_forgetControl P h).units_smul u

/-- **The last stage of `CubeCutSteps`**: if `z` maps to `±[pt ⊗ CPcell]` (the constant sequence
`CPcell` at points `ℓ i` of `Y`), then `σ_tail` of `z` pushed to the point is a sign tail. -/
theorem isSignTail_σtail_map_forgetControl_cpConst {Y : Type} [PseudoEMetricSpace Y]
    [MulAction H Y] [IsIsometricSMul H Y] {B : InvCat} (Φ : B ⟶ asymptoticInvCat (scalarHom H) Y)
    (z : 𝕃.L B 4) (ℓ : ℕ → Y) (u : ℤˣ)
    (hz : 𝕃.map Φ 4 z = u • 𝕃.cls _ 4 (Lconc.cls ((cpConstDuality ℓ).symPoincare (scalarHom H)))) :
    IsSignTail (𝕃.σtail (scalarHom H) (𝕃.map (Φ ≫ forgetControl (scalarHom H) Y) 4 z)) :=
  𝕃.isSignTail_σtail_map_forgetControl Φ z _ u hz
    (Eventually.of_forall fun _ ↦ CPcell.basedSig_duality ▸ isUnit_one)

end HSFormal.LTheory.LowerLTheory
