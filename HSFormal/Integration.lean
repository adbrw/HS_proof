import HSFormal.IntegrationControl
import HSFormal.IntegrationDuality

/-!
# Integration: forgetting the action, push-forward, and the functor `U`

* Forgetting the action (l.70, l.129): `𝒜_G(X) → 𝒜_1(X)`, reindexing `Fin n × G_i` as the scalar
  basis `Fin (n |G_i|)`, with no factor `1/|G|`; additive, `ℚ`-linear, duality-preserving, and
  compatible with supports: on `𝒜`, `𝒜_S`, `ℬ_Z`, `𝒜_A/𝒜_Y` (commuting with excision), and as a
  map of support filtrations.  Restriction to the subgroups `P_i` is not used by the manuscript
  (l.444–454 only evaluate characters), so it is not formalized.
* Uniformly continuous equivariant push-forward on `𝒜_S` and `ℬ_Z` (l.70).
* `FixedData.U` (l.873): forget the group and `T`, `ℬ_{G,Z}(T × Sⁿ) → ℬ_{1,Z₀}(Sⁿ)`.
-/

noncomputable section

namespace HSFormal

open Filter Matrix CategoryTheory CategoryTheory.Limits Metric LTheory Compression
open scoped Classical ENNReal Topology Pointwise

universe u v

/-! ### Forgetting the action, `𝒜_G(X) → 𝒜_1(X)` (l.70, l.129) -/

theorem prop_submatrix_equiv {A B A' B' Y : Type*} [PseudoEMetricSpace Y] (u : Matrix B A ℚ)
    (source : A → Y) (target : B → Y) (e : A' ≃ A) (e' : B' ≃ B) :
    prop (u.submatrix e' e) (source ∘ e) (target ∘ e') = prop u source target := by
  refine le_antisymm (prop_submatrix_le _ _) (prop_le_iff.mpr fun b a h ↦ ?_)
  simpa using edist_le_prop (u := u.submatrix e' e) (source := source ∘ e)
    (target := target ∘ e') (b := e'.symm b) (a := e.symm a) (by simpa using h)

section Forget

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  {π : ∀ i, G i →* H} {X : Type u} [MulAction H X] [PseudoEMetricSpace X]

namespace AsymptoticObject

/-- Forgetting the action: the free basis `Fin n × G_i`, reindexed as the scalar basis
`Fin (n |G_i|)`, each basis vector keeping its label. -/
@[reducible]
def forgetObj (M : AsymptoticObject π X) : AsymptoticObject (scalarHom H) X where
  rank i := M.rank i * Fintype.card (G i)
  label i r := M.fullLabel i ((tensorIdx (G i) (M.rank i)).symm r)

/-- The scalar basis of the forgotten object is the free basis `Fin n × G_i`. -/
def forgetCoord (M : AsymptoticObject π X) (i : ℕ) :
    Fin ((forgetObj M).rank i) × Unit ≃ Fin (M.rank i) × G i :=
  (Equiv.prodPUnit _).trans (tensorIdx (G i) (M.rank i)).symm

omit [PseudoEMetricSpace X] in
theorem fullLabel_forgetObj (M : AsymptoticObject π X) (i : ℕ)
    (b : Fin ((forgetObj M).rank i) × Unit) :
    (forgetObj M).fullLabel i b = M.fullLabel i (forgetCoord M i b) := by
  simp [fullLabel, forgetObj, forgetCoord]

omit [PseudoEMetricSpace X] in
theorem fullLabel_forgetObj_comp (M : AsymptoticObject π X) (i : ℕ) :
    (forgetObj M).fullLabel i = M.fullLabel i ∘ forgetCoord M i :=
  funext (fullLabel_forgetObj M i)

theorem supportDist_forgetObj (S : Set X) (M : AsymptoticObject π X) (i : ℕ) :
    (forgetObj M).supportDist S i = M.supportDist S i := by
  simp only [supportDist, fullLabel_forgetObj]
  exact (forgetCoord M i).iSup_comp (g := fun b ↦ infEDist (M.fullLabel i b) S)

theorem isSupported_forgetObj_iff {S : Set X} {M : AsymptoticObject π X} :
    (forgetObj M).IsSupported S ↔ M.IsSupported S := by
  simp only [IsSupported, funext (supportDist_forgetObj S M)]

variable {M N P : AsymptoticObject π X}

/-- The matrices of a family, read in the forgotten scalar bases. -/
def forgetMatrix (f : Family M N) : Family (forgetObj M) (forgetObj N) :=
  fun i ↦ (f i).submatrix (forgetCoord N i) (forgetCoord M i)

theorem propSeq_forgetMatrix (f : Family M N) (i : ℕ) :
    propSeq (forgetObj M) (forgetObj N) (forgetMatrix f) i = propSeq M N f i := by
  simp only [propSeq, forgetMatrix, fullLabel_forgetObj_comp]
  exact prop_submatrix_equiv _ _ _ _ _

/-- The forgotten morphism. -/
def forgetHom (f : M ⟶ N) : forgetObj M ⟶ forgetObj N :=
  ⟨forgetMatrix f.1, (⟨fun _ _ _ _ ↦ rfl, (tendsto_propSeq f).congr fun i ↦
    (propSeq_forgetMatrix f.1 i).symm⟩ :
      IsControlled (forgetObj M) (forgetObj N) (forgetMatrix f.1))⟩

@[simp]
theorem forgetHom_val (f : M ⟶ N) (i : ℕ) :
    (forgetHom f).1 i = (f.1 i).submatrix (forgetCoord N i) (forgetCoord M i) :=
  rfl

variable (π X) in
/-- **Forgetting the action** on controlled families. -/
@[simps obj]
def forgetFunctor : AsymptoticObject π X ⥤ AsymptoticObject (scalarHom H) X where
  obj := forgetObj
  map := forgetHom
  map_id M := hom_ext fun i ↦ by
    ext a b
    simp only [forgetHom_val, id_val, submatrix_apply, one_apply, EmbeddingLike.apply_eq_iff_eq]
    congr
  map_comp f g := hom_ext fun i ↦ (submatrix_mul_equiv _ _ _ _ _).symm

instance forgetFunctor_additive : (forgetFunctor π X).Additive where
  map_add := rfl

instance forgetFunctor_linear : (forgetFunctor π X).Linear ℚ where
  map_smul _ _ := rfl

/-- Forgetting preserves duality, with no factor `1/|G|` (l.129). -/
theorem forgetHom_transpose (f : M ⟶ N) :
    forgetHom (transpose f) = transpose (forgetHom f) :=
  hom_ext fun _ ↦ (transpose_submatrix _ _ _).symm

end AsymptoticObject

open AsymptoticObject

namespace AsymptoticCategory

variable (π X) in
/-- **Forgetting the action** `𝒜_G(X) → 𝒜_1(X)`. -/
def forget : AsymptoticCategory π X ⥤ AsymptoticCategory (scalarHom H) X :=
  CategoryTheory.Quotient.lift _ (forgetFunctor π X ⋙ functor) fun _ _ _ _ h ↦
    (functor_map_eq_iff _ _).mpr <| h.mono fun i hi ↦ by
      change (forgetHom _).1 i = (forgetHom _).1 i
      simp only [forgetHom_val, hi]

theorem forget_obj (A : AsymptoticCategory π X) :
    (forget π X).obj A = functor.obj (forgetObj A.as) :=
  rfl

theorem forget_map_functor_map {M N : AsymptoticObject π X} (f : M ⟶ N) :
    (forget π X).map (functor.map f) = functor.map (forgetHom f) :=
  rfl

instance forget_additive : (forget π X).Additive :=
  QuotientLift.additive _ _

instance forget_linear : (forget π X).Linear ℚ :=
  QuotientLift.linear ℚ _ _

theorem forget_map_transpose {A B : AsymptoticCategory π X} (φ : A ⟶ B) :
    (forget π X).map (transpose φ) = transpose ((forget π X).map φ) := by
  obtain ⟨f, rfl⟩ := exists_rep φ
  exact congrArg functor.map (forgetHom_transpose f)

/-- Forgetting the action as a strictly duality-preserving functor. -/
def forgetInv : InvFunctor (involution π X) (involution (scalarHom H) X) where
  F := forget π X
  map_star := forget_map_transpose

variable {S : Set X}

theorem supportProperty_forget_obj_iff {A : AsymptoticCategory π X} :
    supportProperty S ((forget π X).obj A) ↔ supportProperty S A :=
  isSupported_forgetObj_iff

/-- Forgetting the action preserves the ideal `I_S`. -/
theorem InIdeal.forget_map {A B : AsymptoticCategory π X} {φ : A ⟶ B} (h : InIdeal S φ) :
    InIdeal S ((forget π X).map φ) := by
  obtain ⟨W, hW, u, v, rfl⟩ := h
  exact ⟨(forget π X).obj W, supportProperty_forget_obj_iff.mpr hW, (forget π X).map u,
    (forget π X).map v, by simp⟩

variable (π S) in
/-- Forgetting the action on support categories, `𝒜_{G,S}(X) → 𝒜_{1,S}(X)`. -/
def supportForget : SupportCategory π S ⥤ SupportCategory (scalarHom H) S :=
  (supportProperty S).lift ((supportProperty S).ι ⋙ forget π X) fun A ↦
    supportProperty_forget_obj_iff.mpr A.property

@[simp]
theorem supportForget_map_hom {A B : SupportCategory π S} (f : A ⟶ B) :
    ((supportForget π S).map f).hom = (forget π X).map f.hom :=
  rfl

instance supportForget_additive : (supportForget π S).Additive where
  map_add := by intros; ext1; exact (forget π X).map_add

instance supportForget_linear : (supportForget π S).Linear ℚ where
  map_smul _ _ := by ext1; exact (forget π X).map_smul _ _

/-- Forgetting the action on `𝒜_S(X)`, duality-preserving. -/
def supportForgetInv : InvFunctor (supportInvolution π S) (supportInvolution (scalarHom H) S) where
  F := supportForget π S
  map_star f := by ext1; exact forget_map_transpose f.hom

theorem supportForget_comp_ι :
    supportForget π S ⋙ (supportProperty S).ι = (supportProperty S).ι ⋙ forget π X :=
  rfl

end AsymptoticCategory

namespace ExteriorCategory

variable (π) in
/-- Forgetting the action on exterior quotients, `ℬ_{G,Z}(X) → ℬ_{1,Z}(X)`. -/
def forget (Z : Set X) : ExteriorCategory π Z ⥤ ExteriorCategory (scalarHom H) Z :=
  CategoryTheory.Quotient.lift _ (AsymptoticCategory.forget π X ⋙ functor) fun _ _ _ _ h ↦
    (functor_map_eq_iff _ _).mpr (by rw [← Functor.map_sub]; exact h.forget_map)

variable {Z : Set X}

theorem forget_map_functor_map {A B : AsymptoticCategory π X} (φ : A ⟶ B) :
    (forget π Z).map (functor.map φ) = functor.map ((AsymptoticCategory.forget π X).map φ) :=
  rfl

theorem functor_comp_forget :
    functor ⋙ forget π Z = AsymptoticCategory.forget π X ⋙ functor :=
  CategoryTheory.Quotient.lift_spec _ _ _

instance forget_additive : (forget π Z).Additive :=
  QuotientLift.additive _ _

instance forget_linear : (forget π Z).Linear ℚ :=
  QuotientLift.linear ℚ _ _

theorem forget_map_transpose {A B : ExteriorCategory π Z} (φ : A ⟶ B) :
    (forget π Z).map (transpose φ) = transpose ((forget π Z).map φ) := by
  obtain ⟨f, rfl⟩ := functor.map_surjective φ
  exact congrArg functor.map (AsymptoticCategory.forget_map_transpose f)

/-- Forgetting the action on `ℬ_Z(X)`, duality-preserving. -/
def forgetInv : InvFunctor (involution π Z) (involution (scalarHom H) Z) where
  F := forget π Z
  map_star := forget_map_transpose

end ExteriorCategory

end Forget

section ForgetFiltration

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  {π : ∀ i, G i →* H} {X : Type} [MulAction H X] [PseudoEMetricSpace X]

variable (π) in
/-- Forgetting the action as a map of support filtrations `(𝒜_{G,S} ⊂ 𝒜_G) → (𝒜_{1,S} ⊂ 𝒜_1)`. -/
def forgetFiltrationHom (S : Set X) :
    FiltrationHom (supportKaroubiFiltration π S) (supportKaroubiFiltration (scalarHom H) S) :=
  ⟨AsymptoticCategory.forgetInv, fun _ hA ↦
    AsymptoticCategory.supportProperty_forget_obj_iff.mpr hA⟩

theorem forgetFiltrationHom_quot (Z : Set X) :
    (forgetFiltrationHom π Z).quot.F = ExteriorCategory.forget π Z :=
  rfl

end ForgetFiltration

/-! ### Forgetting the action on `𝒜_A/𝒜_Y`, compatible with excision -/

section ForgetQuotient

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  {π : ∀ i, G i →* H} {X : Type} [MulAction H X] [PseudoEMetricSpace X]

namespace AsymptoticCategory

variable (π) in
/-- Forgetting the action on `𝒜_A/𝒜_Y`. -/
def SupportQuotient.forget (A Y : Set X) :
    SupportQuotient π A Y ⥤ SupportQuotient (scalarHom H) A Y :=
  CategoryTheory.Quotient.lift _ (supportForget π A ⋙ SupportQuotient.functor) fun _ _ _ _ h ↦
    CategoryTheory.Quotient.sound _ <| by
      have := h.forget_map
      rw [Functor.map_sub] at this
      exact this

variable {A Y B : Set X}

theorem SupportQuotient.functor_comp_forget :
    SupportQuotient.functor ⋙ SupportQuotient.forget π A Y =
      supportForget π A ⋙ SupportQuotient.functor :=
  CategoryTheory.Quotient.lift_spec _ _ _

instance SupportQuotient.forget_additive : (SupportQuotient.forget π A Y).Additive :=
  QuotientLift.additive _ _

instance SupportQuotient.forget_linear : (SupportQuotient.forget π A Y).Linear ℚ :=
  QuotientLift.linear ℚ _ _

/-- Forgetting the action on `𝒜_A/𝒜_Y`, duality-preserving. -/
def SupportQuotient.forgetInv :
    InvFunctor (SupportQuotient.involution π A Y) (SupportQuotient.involution (scalarHom H) A Y)
    where
  F := SupportQuotient.forget π A Y
  map_star φ := by
    obtain ⟨f, rfl⟩ := SupportQuotient.functor.map_surjective φ
    exact congrArg SupportQuotient.functor.map ((supportForgetInv (π := π) (S := A)).map_star f)

/-- Forgetting the action commutes with the excision functor of Lemma 2.2. -/
theorem excisionFunctor_comp_forget :
    excisionFunctor A B ⋙ ExteriorCategory.forget π B =
      SupportQuotient.forget π A (A ∩ B) ⋙ excisionFunctor A B := by
  refine CategoryTheory.Quotient.lift_unique' _ _ _ ?_
  rw [← Functor.assoc, ← Functor.assoc, functor_comp_excisionFunctor,
    SupportQuotient.functor_comp_forget, Functor.assoc, Functor.assoc,
    ExteriorCategory.functor_comp_forget, functor_comp_excisionFunctor, ← Functor.assoc,
    ← Functor.assoc, supportForget_comp_ι]

end AsymptoticCategory

end ForgetQuotient

/-! ### Push-forward on support and exterior categories -/

section Push

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  {π : ∀ i, G i →* H} {X : Type u} [MulAction H X] [PseudoEMetricSpace X]
  {Y : Type v} [MulAction H Y] [PseudoEMetricSpace Y] {j : Y → X}
  (hjeq : ∀ (h : H) (y : Y), j (h • y) = h • j y)

omit [MulAction H X] [MulAction H Y] in
theorem exists_infEDist_lt_of_uniformContinuous (hj : UniformContinuous j) {Z : Set Y}
    {Z' : Set X} (hZ : Set.MapsTo j Z Z') {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y, infEDist y Z < δ → infEDist (j y) Z' < ε := by
  obtain ⟨δ, hδ, h⟩ := EMetric.uniformContinuous_iff.mp hj ε hε
  refine ⟨δ, hδ, fun y hy ↦ ?_⟩
  obtain ⟨z, hz, hyz⟩ := infEDist_lt_iff.mp hy
  exact (infEDist_le_edist_of_mem (hZ hz)).trans_lt (h hyz)

omit [∀ i, Fintype (G i)] in
include hjeq in
/-- Uniformly continuous push-forward with `j(Z) ⊆ Z'` maps `𝒜_Z(Y)` into `𝒜_{Z'}(X)`. -/
theorem AsymptoticObject.IsSupported.push (hj : UniformContinuous j) {Z : Set Y} {Z' : Set X}
    (hZ : Set.MapsTo j Z Z') {M : AsymptoticObject π Y} (hM : M.IsSupported Z) :
    (M.push j).IsSupported Z' := by
  refine ENNReal.tendsto_nhds_zero.mpr fun ε hε ↦ ?_
  obtain ⟨δ, hδ, h⟩ := exists_infEDist_lt_of_uniformContinuous hj hZ hε
  filter_upwards [(tendsto_order.1 hM).2 δ hδ] with i hi
  refine iSup_le fun b ↦ ?_
  rw [AsymptoticObject.fullLabel_push hjeq]
  exact (h _ ((AsymptoticObject.infEDist_le_supportDist (M := M) i b).trans_lt hi)).le

namespace AsymptoticCategory

variable (hj : UniformContinuous j) {Z : Set Y} {Z' : Set X} (hZ : Set.MapsTo j Z Z')
include hZ

theorem supportProperty_pushTail_obj {A : AsymptoticCategory π Y} (hA : supportProperty Z A) :
    supportProperty Z' ((pushTail hjeq hj).obj A) :=
  AsymptoticObject.IsSupported.push hjeq hj hZ hA

theorem InIdeal.pushTail_map {A B : AsymptoticCategory π Y} {φ : A ⟶ B} (h : InIdeal Z φ) :
    InIdeal Z' ((pushTail hjeq hj).map φ) := by
  obtain ⟨W, hW, u, v, rfl⟩ := h
  exact ⟨(pushTail hjeq hj).obj W, supportProperty_pushTail_obj hjeq hj hZ hW,
    (pushTail hjeq hj).map u, (pushTail hjeq hj).map v, by simp⟩

end AsymptoticCategory

namespace ExteriorCategory

variable (hj : UniformContinuous j) {Z : Set Y} {Z' : Set X} (hZ : Set.MapsTo j Z Z')

/-- Push-forward `ℬ_Z(Y) → ℬ_{Z'}(X)` along a uniformly continuous equivariant `j` with
`j(Z) ⊆ Z'`. -/
def push : ExteriorCategory π Z ⥤ ExteriorCategory π Z' :=
  CategoryTheory.Quotient.lift _ (AsymptoticCategory.pushTail hjeq hj ⋙ functor)
    fun _ _ _ _ h ↦ (functor_map_eq_iff _ _).mpr (by
      rw [← Functor.map_sub]; exact AsymptoticCategory.InIdeal.pushTail_map hjeq hj hZ h)

instance push_additive : (push (π := π) hjeq hj hZ).Additive :=
  QuotientLift.additive _ _

instance push_linear : (push (π := π) hjeq hj hZ).Linear ℚ :=
  QuotientLift.linear ℚ _ _

theorem push_map_transpose {A B : ExteriorCategory π Z} (φ : A ⟶ B) :
    (push hjeq hj hZ).map (transpose φ) = transpose ((push hjeq hj hZ).map φ) := by
  obtain ⟨f, rfl⟩ := functor.map_surjective φ
  exact congrArg functor.map (AsymptoticCategory.pushTail_transpose hjeq hj f)

/-- Push-forward of exterior quotients, duality-preserving (l.70). -/
def pushInv : InvFunctor (involution π Z) (involution π Z') where
  F := push hjeq hj hZ
  map_star := push_map_transpose hjeq hj hZ

end ExteriorCategory

variable (π X) in
/-- Forget the action and push to a point, `𝒜_G(X) → 𝒜_1(pt)` (l.1121): the functor behind
`σ_tail(α) = σ_tail(U_*α)`. -/
def AsymptoticCategory.toPointInv :
    InvFunctor (AsymptoticCategory.involution π X)
      (AsymptoticCategory.involution (scalarHom H) Unit) :=
  AsymptoticCategory.forgetInv.comp
    (AsymptoticCategory.pushTailInv (j := fun _ : X ↦ ()) (fun _ _ ↦ rfl) uniformContinuous_const)

end Push

section PushFiltration

variable {H : Type*} [Group H] {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  {π : ∀ i, G i →* H} {X : Type} [MulAction H X] [PseudoEMetricSpace X]
  {Y : Type} [MulAction H Y] [PseudoEMetricSpace Y] {j : Y → X}

/-- Push-forward as a map of support filtrations `(𝒜_Z(Y) ⊂ 𝒜(Y)) → (𝒜_{Z'}(X) ⊂ 𝒜(X))`. -/
def pushFiltrationHom (hjeq : ∀ (h : H) (y : Y), j (h • y) = h • j y) (hj : UniformContinuous j)
    {Z : Set Y} {Z' : Set X} (hZ : Set.MapsTo j Z Z') :
    FiltrationHom (supportKaroubiFiltration π Z) (supportKaroubiFiltration π Z') :=
  ⟨AsymptoticCategory.pushTailInv hjeq hj, fun _ hA ↦
    AsymptoticCategory.supportProperty_pushTail_obj hjeq hj hZ hA⟩

end PushFiltration

/-! ### The functor `U` of l.873 -/

namespace FixedData

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {M : Type*} [TopologicalSpace M] [AddAction ℤ_[p] M]
  (d : FixedData p n M) {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  (π : ∀ i, G i →* d.Cp)

/-- **The functor `U`** (l.873): forget the group and `T`, retaining the sphere coordinate,
`ℬ_{G,Z}(T × Sⁿ) → ℬ_{1,Z₀}(Sⁿ)`; strictly duality-preserving. -/
def U : InvFunctor (ExteriorCategory.involution π d.ZS)
    (ExteriorCategory.involution (scalarHom d.Cp) d.Z₀S) :=
  (ExteriorCategory.forgetInv (π := π) (Z := d.ZS)).comp
    (ExteriorCategory.pushInv (j := Prod.snd) (fun _ _ ↦ rfl) uniformContinuous_snd
      fun _ hx ↦ hx.2)

/-- `U` as the composite of the maps of support filtrations; it is induced on `ℬ` by
`InvCat`-morphisms of `𝒜`. -/
theorem U_eq : (d.U π).F = ((forgetFiltrationHom π d.ZS).comp (pushFiltrationHom
    (j := Prod.snd) (fun _ _ ↦ rfl) uniformContinuous_snd fun _ hx ↦ hx.2)).quot.F := by
  rw [FiltrationHom.comp_quot]
  rfl

end FixedData

end HSFormal
