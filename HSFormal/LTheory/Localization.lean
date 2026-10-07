import HSFormal.LTheory.Interface
import HSFormal.MVNilpotence
import HSFormal.IntegrationDuality

/-!
# Localization sequences, Mayer–Vietoris and boundary cuts (L-theory module M7, general part)

Consequences of the hypotheses H1, H2, H4 of `LowerLTheory` over arbitrary `InvCat`s
(manuscript §4, l.181–240); the support categories are instantiated in
`LTheory.LocalizationSupport`.

* Degrees (design I7): `castDeg`, `bdryOf` (the boundary from a degree `m = n + 1`), and
  `iterDown`, composites `L (C n) (n + d) → ⋯ → L (C 0) d` defined by recursion on `n : ℕ`, with
  `iterDown_natural`.
* `isLES`, `isLES_iso`: the localization sequence (H1), also with `F.sub` replaced by an
  isomorphic `InvCat`.
* `IsUnitaryEquiv` (equivalence up to unitary natural isomorphisms) and the induced `equivOf` on
  `L`, natural by `equivOf_symm_natural`; criteria `FiltrationHom.isUnitaryEquiv_quot`,
  `isUnitaryEquiv_comp_proj`.
* Restrictions to full subcategories (`InvCat.subMap`, `InvCat.subRestrict`,
  `KaroubiFiltration.restrictMap`, `restrictTo`, `restrictEndo`) with excision criteria
  `isUnitaryEquiv_restrictMap`, `isUnitaryEquiv_restrictTo`, `isUnitaryEquiv_subMap_proj`.  All
  identifications between objects of different subcategories are proved here, for abstract
  object properties (for concrete support conditions the kernel unfolds them expensively).
* Mayer–Vietoris through Barratt–Whitehead: `isLES_mayerVietoris`, and for restrictions
  `isLES_mayerVietoris_restrict` (`U ⊂ V`, `U' ⊂ V'`) and `isLES_mayerVietoris_restrictTo`
  (`U ⊂ V`, `U' ⊂ A`); boundaries commute with endomorphisms preserving the data, including the
  excision (`mvBdryOf_restrict_comm`) and with maps of ladders (`mvBdry_natural`).
* Lemma 4.1 (`bdry_symm_cls`, `bdry_symm_proj_cls`, `mvBdryOf_cls`): `∂` of a closed complex
  which modulo `U'` is isometric to the image of a pair with boundary in `U` is `bsign` times the
  class of that boundary (H2 with `SymPair.toQuot_map`).
* `projSepOf` (separated projections) and `cutOf`, `∂ ∘ e⁻¹ ∘ q`, natural by `cutOf_natural`
  (the squares of (11.2)).
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HSFormal.MVNilpotence

noncomputable section

variable {A B C : InvCat}

/-- `Φ` is an equivalence up to unitary natural isomorphisms. -/
def IsUnitaryEquiv (Φ : A ⟶ B) : Prop :=
  ∃ Ψ : B ⟶ A, Nonempty (InvCat.UnitaryIso (Φ ≫ Ψ) (𝟙 A)) ∧
    Nonempty (InvCat.UnitaryIso (Ψ ≫ Φ) (𝟙 B))

theorem IsUnitaryEquiv.of_iso (u : A ≅ B) : IsUnitaryEquiv u.hom :=
  ⟨u.inv, ⟨u.hom_inv_id ▸ InvCat.UnitaryIso.refl _⟩, ⟨u.inv_hom_id ▸ InvCat.UnitaryIso.refl _⟩⟩

/-! ### Naturality of the Mayer–Vietoris boundary -/

section MVNatural

variable {A₁ C₁ C₁' B₁' A₂ C₂ C₂' B₂' : ℤ → Type*} [∀ n, AddCommGroup (A₁ n)]
  [∀ n, AddCommGroup (C₁ n)] [∀ n, AddCommGroup (C₁' n)] [∀ n, AddCommGroup (B₁' n)]
  [∀ n, AddCommGroup (A₂ n)] [∀ n, AddCommGroup (C₂ n)] [∀ n, AddCommGroup (C₂' n)]
  [∀ n, AddCommGroup (B₂' n)]
  {δ₁ : ∀ n, C₁ (n + 1) →+ A₁ n} {j₁ : ∀ n, B₁' n →+ C₁' n} {h₁ : ∀ n, C₁ n ≃+ C₁' n}
  {δ₂ : ∀ n, C₂ (n + 1) →+ A₂ n} {j₂ : ∀ n, B₂' n →+ C₂' n} {h₂ : ∀ n, C₂ n ≃+ C₂' n}

/-- The Mayer–Vietoris boundary `δ ∘ h⁻¹ ∘ j` is natural for maps of the three pieces. -/
theorem mvBdry_natural {n : ℤ} (a : A₁ n →+ A₂ n) (c : C₁ (n + 1) →+ C₂ (n + 1))
    (c' : C₁' (n + 1) →+ C₂' (n + 1)) (b : B₁' (n + 1) →+ B₂' (n + 1))
    (hδ : a.comp (δ₁ n) = (δ₂ n).comp c)
    (hh : (h₂ (n + 1)).toAddMonoidHom.comp c = c'.comp (h₁ (n + 1)).toAddMonoidHom)
    (hj : (j₂ (n + 1)).comp b = c'.comp (j₁ (n + 1))) :
    a.comp (mvBdry δ₁ j₁ h₁ n) = (mvBdry δ₂ j₂ h₂ n).comp b := by
  ext x
  simp only [AddMonoidHom.comp_apply, mvBdry_apply]
  have e₂ : (h₂ (n + 1)).symm (c' (j₁ (n + 1) x)) = c ((h₁ (n + 1)).symm (j₁ (n + 1) x)) := by
    rw [AddEquiv.symm_apply_eq]
    simpa using (DFunLike.congr_fun hh ((h₁ (n + 1)).symm (j₁ (n + 1) x))).symm
  rw [show j₂ (n + 1) (b x) = c' (j₁ (n + 1) x) from DFunLike.congr_fun hj x, e₂]
  exact DFunLike.congr_fun hδ _

end MVNatural

namespace LowerLTheory

variable (𝕃 : LowerLTheory)

/-! ### Degree transport (design I7) -/

section Degree

/-- Transport of `L A` along an equality of degrees. -/
def castDeg (A : InvCat) {m n : ℤ} (h : m = n) : 𝕃.L A m ≃+ 𝕃.L A n :=
  h ▸ AddEquiv.refl _

@[simp]
theorem castDeg_rfl (A : InvCat) (n : ℤ) : 𝕃.castDeg A (rfl : n = n) = AddEquiv.refl _ := rfl

@[simp]
theorem castDeg_symm (A : InvCat) {m n : ℤ} (h : m = n) :
    (𝕃.castDeg A h).symm = 𝕃.castDeg A h.symm := by
  subst h
  rfl

@[simp]
theorem castDeg_trans (A : InvCat) {l m n : ℤ} (h : l = m) (h' : m = n) (x : 𝕃.L A l) :
    𝕃.castDeg A h' (𝕃.castDeg A h x) = 𝕃.castDeg A (h.trans h') x := by
  subst h h'
  rfl

theorem map_castDeg (Φ : A ⟶ B) {m n : ℤ} (h : m = n) (x : 𝕃.L A m) :
    𝕃.map Φ n (𝕃.castDeg A h x) = 𝕃.castDeg B h (𝕃.map Φ m x) := by
  subst h
  rfl

theorem natDeg_succ (k : ℕ) (d : ℤ) : ((k + 1 : ℕ) : ℤ) + d = (k : ℤ) + d + 1 := by
  push_cast
  ring

/-- The localization boundary from a degree `m = n + 1` (H1). -/
def bdryOf (F : KaroubiFiltration A) {m n : ℤ} (h : m = n + 1) : 𝕃.L F.quot m →+ 𝕃.L F.sub n :=
  (𝕃.bdry F n).comp (𝕃.castDeg F.quot h).toAddMonoidHom

@[simp]
theorem bdryOf_rfl (F : KaroubiFiltration A) (n : ℤ) :
    𝕃.bdryOf F (rfl : n + 1 = n + 1) = 𝕃.bdry F n :=
  rfl

theorem bdryOf_natural {F : KaroubiFiltration A} {F' : KaroubiFiltration B} (Φ : FiltrationHom F F')
    {m n : ℤ} (h : m = n + 1) :
    (𝕃.bdryOf F' h).comp (𝕃.map Φ.quot m) = (𝕃.map Φ.sub n).comp (𝕃.bdryOf F h) := by
  subst h
  exact 𝕃.bdry_natural Φ n

/-- The composite `L (C n) (n + d) → ⋯ → L (C 0) d` of degree-lowering maps
`f k : L (C (k + 1)) (k + d + 1) → L (C k) (k + d)`, by recursion on `n : ℕ` (e.g. `Δ_T` of
(11.1) with `d = 4`). -/
def iterDown (C : ℕ → InvCat) (d : ℤ)
    (f : ∀ k : ℕ, 𝕃.L (C (k + 1)) ((k : ℤ) + d + 1) →+ 𝕃.L (C k) ((k : ℤ) + d)) :
    ∀ n : ℕ, 𝕃.L (C n) ((n : ℤ) + d) →+ 𝕃.L (C 0) d
  | 0 => (𝕃.castDeg (C 0) (by simp)).toAddMonoidHom
  | n + 1 => (iterDown C d f n).comp ((f n).comp (𝕃.castDeg _ (natDeg_succ n d)).toAddMonoidHom)

/-- Naturality of iterated boundaries (the squares of (11.2)). -/
theorem iterDown_natural {C C' : ℕ → InvCat} (Φ : ∀ k, C k ⟶ C' k) (d : ℤ)
    {f : ∀ k : ℕ, 𝕃.L (C (k + 1)) ((k : ℤ) + d + 1) →+ 𝕃.L (C k) ((k : ℤ) + d)}
    {f' : ∀ k : ℕ, 𝕃.L (C' (k + 1)) ((k : ℤ) + d + 1) →+ 𝕃.L (C' k) ((k : ℤ) + d)}
    (hf : ∀ k, (𝕃.map (Φ k) _).comp (f k) = (f' k).comp (𝕃.map (Φ (k + 1)) _)) (n : ℕ) :
    (𝕃.map (Φ 0) d).comp (𝕃.iterDown C d f n) = (𝕃.iterDown C' d f' n).comp (𝕃.map (Φ n) _) := by
  induction n with
  | zero => ext x; exact 𝕃.map_castDeg _ _ x
  | succ n ih =>
    ext x
    simp only [iterDown, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
    rw [← AddMonoidHom.comp_apply (𝕃.map (Φ 0) d), ih, AddMonoidHom.comp_apply,
      ← AddMonoidHom.comp_apply (𝕃.map (Φ n) _), hf, AddMonoidHom.comp_apply, map_castDeg]

end Degree

/-! ### Localization sequences -/

section LES

/-- **H1** as a long exact sequence. -/
theorem isLES (F : KaroubiFiltration A) :
    IsLES (fun n ↦ 𝕃.map F.incl n) (fun n ↦ 𝕃.map F.proj n) (𝕃.bdry F) :=
  ⟨𝕃.exact_A F, 𝕃.exact_Q F, 𝕃.exact_U F⟩

/-- The endomorphism of `L_n(A)` induced by an endomorphism of `A`. -/
abbrev mapEnd (Φ : A ⟶ A) (n : ℤ) : AddMonoid.End (𝕃.L A n) := 𝕃.map Φ n

/-- A strict isomorphism of `InvCat`s induces an isomorphism of L-groups. -/
@[simps]
def mapIso (u : A ≅ B) (n : ℤ) : 𝕃.L A n ≃+ 𝕃.L B n where
  toFun := 𝕃.map u.hom n
  invFun := 𝕃.map u.inv n
  left_inv x := by rw [← AddMonoidHom.comp_apply, ← 𝕃.map_comp, u.hom_inv_id, 𝕃.map_id]; rfl
  right_inv x := by rw [← AddMonoidHom.comp_apply, ← 𝕃.map_comp, u.inv_hom_id, 𝕃.map_id]; rfl
  map_add' := map_add _

theorem map_comp_apply (Φ : A ⟶ B) (Ψ : B ⟶ C) (n : ℤ) (x : 𝕃.L A n) :
    𝕃.map Ψ n (𝕃.map Φ n x) = 𝕃.map (Φ ≫ Ψ) n x := by
  rw [𝕃.map_comp]
  rfl

theorem map_comp_eq {B' : InvCat} {Φ : A ⟶ B} {Ψ : B ⟶ C} {Φ' : A ⟶ B'} {Ψ' : B' ⟶ C}
    (h : Φ ≫ Ψ = Φ' ≫ Ψ') (n : ℤ) :
    (𝕃.map Ψ n).comp (𝕃.map Φ n) = (𝕃.map Ψ' n).comp (𝕃.map Φ' n) := by
  rw [← 𝕃.map_comp, ← 𝕃.map_comp, h]

/-- The localization sequence of `F` with `F.sub` replaced along an isomorphism `u`. -/
theorem isLES_iso (F : KaroubiFiltration A) {C : InvCat} (u : F.sub ≅ C) (ι : C ⟶ A)
    (h : u.hom ≫ ι = F.incl) :
    IsLES (fun n ↦ 𝕃.map ι n) (fun n ↦ 𝕃.map F.proj n)
      (fun n ↦ (𝕃.map u.hom n).comp (𝕃.bdry F n)) where
  exact_ij n := Function.Exact.of_ladder_addEquiv_of_exact (𝕃.mapIso u n) (AddEquiv.refl _)
    (AddEquiv.refl _) (by ext x; exact (𝕃.map_comp_apply _ _ _ x).trans (by rw [h]; rfl))
    rfl (𝕃.exact_A F n)
  exact_jδ n := Function.Exact.of_ladder_addEquiv_of_exact (AddEquiv.refl _) (AddEquiv.refl _)
    (𝕃.mapIso u n) rfl rfl (𝕃.exact_Q F n)
  exact_δi n := Function.Exact.of_ladder_addEquiv_of_exact (AddEquiv.refl _) (𝕃.mapIso u n)
    (AddEquiv.refl _) rfl
    (by ext x; exact (𝕃.map_comp_apply _ _ _ x).trans (by rw [h]; rfl)) (𝕃.exact_U F n)

end LES

/-! ### Unitary equivalences -/

section Equiv

theorem map_bijective {Φ : A ⟶ B} (hΦ : IsUnitaryEquiv Φ) (n : ℤ) :
    Function.Bijective (𝕃.map Φ n) := by
  obtain ⟨Ψ, ⟨h₁⟩, ⟨h₂⟩⟩ := hΦ
  exact (𝕃.mapAddEquiv Φ Ψ h₁ h₂ n).bijective

/-- The isomorphism of L-groups induced by a unitary equivalence. -/
def equivOf {Φ : A ⟶ B} (hΦ : IsUnitaryEquiv Φ) (n : ℤ) : 𝕃.L A n ≃+ 𝕃.L B n :=
  AddEquiv.ofBijective (𝕃.map Φ n) (𝕃.map_bijective hΦ n)

@[simp]
theorem equivOf_apply {Φ : A ⟶ B} (hΦ : IsUnitaryEquiv Φ) (n : ℤ) (x : 𝕃.L A n) :
    𝕃.equivOf hΦ n x = 𝕃.map Φ n x :=
  rfl

theorem equivOf_symm_map {Φ : A ⟶ B} (hΦ : IsUnitaryEquiv Φ) (n : ℤ) (x : 𝕃.L A n) :
    (𝕃.equivOf hΦ n).symm (𝕃.map Φ n x) = x :=
  (𝕃.equivOf hΦ n).symm_apply_apply x

/-- Inverses of induced isomorphisms are natural. -/
theorem equivOf_symm_natural {A₂ B₂ : InvCat} {Φ : A ⟶ B} {Φ₂ : A₂ ⟶ B₂} (hΦ : IsUnitaryEquiv Φ)
    (hΦ₂ : IsUnitaryEquiv Φ₂) (a : A ⟶ A₂) (b : B ⟶ B₂) (h : Φ ≫ b = a ≫ Φ₂) (n : ℤ)
    (y : 𝕃.L B n) :
    (𝕃.equivOf hΦ₂ n).symm (𝕃.map b n y) = 𝕃.map a n ((𝕃.equivOf hΦ n).symm y) := by
  rw [AddEquiv.symm_apply_eq, equivOf_apply, map_comp_apply, ← h, ← map_comp_apply,
    ← equivOf_apply 𝕃 hΦ, AddEquiv.apply_symm_apply]

end Equiv

end LowerLTheory

/-! ### Criteria for unitary equivalences of quotients -/

section Criteria

variable {F : KaroubiFiltration A} {F' : KaroubiFiltration B}

/-- A map of filtrations induces a unitary equivalence of quotients if it is full, reflects the
ideals, and every object of `B` is unitarily isomorphic modulo `U'` to an image. -/
theorem FiltrationHom.isUnitaryEquiv_quot (Φ : FiltrationHom F F') [Φ.toHom.F.Full]
    (hrefl : ∀ {X Y : A} (f : X ⟶ Y), FactorsThrough F'.U (Φ.toHom.F.map f) → FactorsThrough F.U f)
    (hess : ∀ Y : B, ∃ (X : A) (u : Φ.toHom.F.obj X ⟶ Y) (v : Y ⟶ Φ.toHom.F.obj X),
      B.inv.star u = v ∧ FactorsThrough F'.U (u ≫ v - 𝟙 _) ∧
        FactorsThrough F'.U (v ≫ u - 𝟙 _)) :
    IsUnitaryEquiv Φ.quot := by
  haveI : Φ.quot.F.Full := ⟨fun {X Y} g ↦ by
    obtain ⟨g, rfl⟩ := (Quotient.functor (factorRel F'.U)).map_surjective g
    exact ⟨(Quotient.functor _).map (Φ.toHom.F.preimage g), by
      change (Quotient.functor _).map (Φ.toHom.F.map _) = _
      rw [Functor.map_preimage]⟩⟩
  haveI : Φ.quot.F.Faithful := ⟨fun {X Y} f g hfg ↦ by
    obtain ⟨f, rfl⟩ := (Quotient.functor (factorRel F.U)).map_surjective f
    obtain ⟨g, rfl⟩ := (Quotient.functor (factorRel F.U)).map_surjective g
    change (Quotient.functor _).map (Φ.toHom.F.map f) =
      (Quotient.functor _).map (Φ.toHom.F.map g) at hfg
    rw [quot_map_eq_iff, ← Functor.map_sub] at hfg
    exact (quot_map_eq_iff _ _).mpr (hrefl _ hfg)⟩
  refine UnitaryInverse.invCat_equiv (A := F.quot) (B := F'.quot) (Φ := Φ.quot) fun Y ↦ ?_
  obtain ⟨X, u, v, huv, h₁, h₂⟩ := hess Y.as
  refine ⟨⟨X⟩, ⟨(Quotient.functor _).map u, (Quotient.functor _).map v, ?_, ?_⟩, ?_⟩
  · erw [← Functor.map_comp]
    exact ((quot_map_eq_iff _ (𝟙 _)).mpr h₁).trans ((Quotient.functor _).map_id _)
  · erw [← Functor.map_comp]
    exact (quot_map_eq_iff _ _).mpr h₂
  · change (Quotient.functor _).map (B.inv.star u) = _
    rw [huv]

/-- `ι ≫ F'.proj : V → B/U'` is a unitary equivalence if `ι` is full, `I_{U'}` meets `V` only in
`0`, and every object of `B` is unitarily isomorphic modulo `U'` to an image. -/
theorem isUnitaryEquiv_comp_proj {V : InvCat} (ι : V ⟶ B) [ι.F.Full]
    (hrefl : ∀ {X Y : V} (f : X ⟶ Y), FactorsThrough F'.U (ι.F.map f) → f = 0)
    (hess : ∀ Y : B, ∃ (X : V) (u : ι.F.obj X ⟶ Y) (v : Y ⟶ ι.F.obj X),
      B.inv.star u = v ∧ FactorsThrough F'.U (u ≫ v - 𝟙 _) ∧
        FactorsThrough F'.U (v ≫ u - 𝟙 _)) :
    IsUnitaryEquiv (ι ≫ F'.proj) := by
  haveI : (ι ≫ F'.proj).F.Full := ⟨fun {X Y} g ↦ by
    obtain ⟨g, rfl⟩ := (Quotient.functor (factorRel F'.U)).map_surjective g
    exact ⟨ι.F.preimage g, by
      change (Quotient.functor _).map (ι.F.map _) = _
      rw [Functor.map_preimage]⟩⟩
  haveI : (ι ≫ F'.proj).F.Faithful := ⟨fun {X Y} f g hfg ↦ by
    change (Quotient.functor _).map (ι.F.map f) = (Quotient.functor _).map (ι.F.map g) at hfg
    rw [quot_map_eq_iff, ← Functor.map_sub] at hfg
    exact sub_eq_zero.mp (hrefl _ hfg)⟩
  refine UnitaryInverse.invCat_equiv (A := V) (B := F'.quot) (Φ := ι ≫ F'.proj) fun Y ↦ ?_
  obtain ⟨X, u, v, huv, h₁, h₂⟩ := hess Y.as
  refine ⟨X, ⟨(Quotient.functor _).map u, (Quotient.functor _).map v, ?_, ?_⟩, ?_⟩
  · erw [← Functor.map_comp]
    exact ((quot_map_eq_iff _ (𝟙 _)).mpr h₁).trans ((Quotient.functor _).map_id _)
  · erw [← Functor.map_comp]
    exact (quot_map_eq_iff _ _).mpr h₂
  · change (Quotient.functor _).map (B.inv.star u) = _
    rw [huv]

end Criteria

/-! ### Restrictions to subcategories

Everything comparing objects of different full subcategories is proved here for abstract object
properties; instantiating it with support categories avoids costly definitional unfolding of
the concrete support conditions. -/

namespace InvCat

variable (A)

/-- The inclusion `A.sub V → A.sub V'` for `V ≤ V'`. -/
def subMap {V V' : ObjectProperty A} [IsAdditiveSub V] [IsAdditiveSub V'] (h : ∀ X, V X → V' X) :
    A.sub V ⟶ A.sub V' where
  F := ObjectProperty.ιOfLE h
  additive := ⟨ObjectProperty.hom_ext _ rfl⟩
  map_star _ := rfl

instance {V V' : ObjectProperty A} [IsAdditiveSub V] [IsAdditiveSub V'] (h : ∀ X, V X → V' X) :
    (A.subMap h).F.Full :=
  inferInstanceAs (ObjectProperty.ιOfLE h).Full

/-- The restriction to `A.sub V` of an endomorphism `T` preserving `V`. -/
def subRestrict (T : A ⟶ A) {V : ObjectProperty A} [IsAdditiveSub V]
    (hT : ∀ X, V X → V (T.F.obj X)) : A.sub V ⟶ A.sub V where
  F := V.lift (V.ι ⋙ T.F) fun X ↦ hT _ X.2
  additive := ⟨ObjectProperty.hom_ext _ T.F.map_add⟩
  map_star f := ObjectProperty.hom_ext _ (T.map_star f.hom)

variable {A}

theorem subRestrict_comp_subMap (T : A ⟶ A) {V V' : ObjectProperty A} [IsAdditiveSub V]
    [IsAdditiveSub V'] (hT : ∀ X, V X → V (T.F.obj X)) (hT' : ∀ X, V' X → V' (T.F.obj X))
    (h : ∀ X, V X → V' X) : A.subRestrict T hT ≫ A.subMap h = A.subMap h ≫ A.subRestrict T hT' :=
  rfl

/-- `A.sub V ≅ A` if every object lies in `V`. -/
def subTopIso (V : ObjectProperty A) [IsAdditiveSub V] (hV : ∀ X, V X) : A.sub V ≅ A where
  hom := A.subIncl V
  inv :=
    { F := V.lift (𝟭 A) hV
      additive := ⟨ObjectProperty.hom_ext _ rfl⟩
      map_star _ := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

theorem subTopIso_hom_comp (T : A ⟶ A) (V : ObjectProperty A) [IsAdditiveSub V] (hV : ∀ X, V X) :
    A.subRestrict T (fun X _ ↦ hV (T.F.obj X)) ≫ (subTopIso V hV).hom = (subTopIso V hV).hom ≫ T :=
  rfl

end InvCat

theorem factorsThrough_sub_of_eq {U : ObjectProperty A} [IsAdditiveSub U] {X Y : A}
    {f g : X ⟶ Y} (h : f = g) : FactorsThrough U (f - g) := by
  rw [h, sub_self]
  exact FactorsThrough.zero

namespace KaroubiFiltration

variable (F F' : KaroubiFiltration A) {V V' : ObjectProperty A} [IsAdditiveSub V]
  [V.IsStableUnderRetracts] [IsAdditiveSub V'] [V'.IsStableUnderRetracts]

theorem factorsThrough_restrict_iff (hFV : ∀ X, F.U X → V X) {X Y : A.sub V} (f : X ⟶ Y) :
    FactorsThrough (F.restrict V).U f ↔ FactorsThrough F.U f.hom := by
  constructor
  · rintro ⟨W, hW, u, v, rfl⟩
    exact ⟨W.obj, hW, u.hom, v.hom, rfl⟩
  · rintro ⟨W, hW, u, v, h⟩
    exact ⟨⟨W, hFV _ hW⟩, hW, ObjectProperty.homMk u, ObjectProperty.homMk v,
      ObjectProperty.hom_ext _ h⟩

/-- The map of restricted filtrations `(U ∩ V ⊂ V) → (U' ∩ V' ⊂ V')` for `U ≤ U'`, `V ≤ V'`. -/
def restrictMap (hU : ∀ X, F.U X → F'.U X) (hV : ∀ X, V X → V' X) :
    FiltrationHom (F.restrict V) (F'.restrict V') :=
  ⟨A.subMap hV, fun _ h ↦ hU _ h⟩

/-- The map of filtrations `(U ∩ V ⊂ V) → (U' ⊂ A)` for `U ≤ U'`. -/
def restrictTo (hU : ∀ X, F.U X → F'.U X) : FiltrationHom (F.restrict V) F' :=
  ⟨A.subIncl V, fun _ h ↦ hU _ h⟩

instance : (A.subIncl V).F.Full := inferInstanceAs V.ι.Full

/-- The restriction of an endomorphism preserving `U` and `V`, as a map of filtrations. -/
def restrictEndo (T : A ⟶ A) (hTU : ∀ X, F.U X → F.U (T.F.obj X))
    (hTV : ∀ X, V X → V (T.F.obj X)) : FiltrationHom (F.restrict V) (F.restrict V) :=
  ⟨A.subRestrict T hTV, fun _ h ↦ hTU _ h⟩

variable {F F'}

theorem restrictSubIso_hom_comp (hFV : ∀ X, F.U X → V X) :
    (F.restrictSubIso V hFV).hom ≫ A.subMap hFV = (F.restrict V).incl :=
  rfl

theorem restrictTo_sub_comp (hU : ∀ X, F.U X → F'.U X) (hFV : ∀ X, F.U X → V X) :
    (F.restrictTo F' (V := V) hU).sub ≫ (Iso.refl F'.sub).hom =
      (F.restrictSubIso V hFV).hom ≫ A.subMap hU :=
  rfl

theorem restrictMap_sub_comp (hU : ∀ X, F.U X → F'.U X) (hV : ∀ X, V X → V' X)
    (hFV : ∀ X, F.U X → V X) (hF'V' : ∀ X, F'.U X → V' X) :
    (F.restrictMap F' hU hV).sub ≫ (F'.restrictSubIso V' hF'V').hom =
      (F.restrictSubIso V hFV).hom ≫ A.subMap hU :=
  rfl

theorem restrictEndo_sub_comp (T : A ⟶ A) (hTU : ∀ X, F.U X → F.U (T.F.obj X))
    (hTV : ∀ X, V X → V (T.F.obj X)) (hFV : ∀ X, F.U X → V X) :
    (F.restrictEndo T hTU hTV).sub ≫ (F.restrictSubIso V hFV).hom =
      (F.restrictSubIso V hFV).hom ≫ A.subRestrict T hTU :=
  rfl

theorem restrictEndo_comp_restrictMap (T : A ⟶ A) (hU : ∀ X, F.U X → F'.U X)
    (hV : ∀ X, V X → V' X) (hTU : ∀ X, F.U X → F.U (T.F.obj X))
    (hTV : ∀ X, V X → V (T.F.obj X)) (hTU' : ∀ X, F'.U X → F'.U (T.F.obj X))
    (hTV' : ∀ X, V' X → V' (T.F.obj X)) :
    (F.restrictEndo T hTU hTV).comp (F.restrictMap F' hU hV) =
      (F.restrictMap F' hU hV).comp (F'.restrictEndo T hTU' hTV') :=
  rfl

/-- Boundary lifts to `U ∩ V` and to `U' ∩ V'` agree in `U'`. -/
theorem bdLift_map_restrictSubIso (hU : ∀ X, F.U X → F'.U X) (hFV : ∀ X, F.U X → V X)
    (hF'V : ∀ X, F'.U X → V X) {N : ℤ} (X : SymPair (A.sub V).inv N)
    (hY : ∀ r, (F.restrict V).U (X.bd.C.X r)) :
    ((X.bdLift (F.restrict V) hY).map (F.restrictSubIso V hFV).hom).map (A.subMap hU) =
      (X.bdLift (F'.restrict V) fun r ↦ hU _ (hY r)).map (F'.restrictSubIso V hF'V).hom :=
  rfl

/-- Excision criterion for `restrictMap`: it reflects the ideals on `V`, and every object of `V'`
splits unitarily, modulo `U'`, off an object of `V`. -/
theorem isUnitaryEquiv_restrictMap (hU : ∀ X, F.U X → F'.U X) (hV : ∀ X, V X → V' X)
    (hFV : ∀ X, F.U X → V X) (hF'V' : ∀ X, F'.U X → V' X)
    (hrefl : ∀ {X Y : A} (f : X ⟶ Y), V X → V Y → FactorsThrough F'.U f → FactorsThrough F.U f)
    (hess : ∀ Y : A, V' Y → ∃ (X : A) (_ : V X) (u : X ⟶ Y) (v : Y ⟶ X),
      A.inv.star u = v ∧ u ≫ v = 𝟙 X ∧ FactorsThrough F'.U (v ≫ u - 𝟙 Y)) :
    IsUnitaryEquiv (F.restrictMap F' hU hV).quot := by
  haveI : (F.restrictMap F' hU hV).toHom.F.Full := inferInstanceAs (A.subMap hV).F.Full
  refine FiltrationHom.isUnitaryEquiv_quot _ (fun {X Y} f hf ↦ ?_) fun Y ↦ ?_
  · rw [factorsThrough_restrict_iff F' hF'V'] at hf
    exact (factorsThrough_restrict_iff F hFV f).mpr (hrefl f.hom X.2 Y.2 hf)
  · obtain ⟨X, hX, u, v, huv, h₁, h₂⟩ := hess Y.obj Y.2
    refine ⟨⟨X, hX⟩, ObjectProperty.homMk u, ObjectProperty.homMk v,
      ObjectProperty.hom_ext _ huv, ?_, (factorsThrough_restrict_iff F' hF'V' _).mpr h₂⟩
    exact factorsThrough_sub_of_eq (ObjectProperty.hom_ext _ h₁)

/-- Excision criterion for `restrictTo`. -/
theorem isUnitaryEquiv_restrictTo (hU : ∀ X, F.U X → F'.U X) (hFV : ∀ X, F.U X → V X)
    (hrefl : ∀ {X Y : A} (f : X ⟶ Y), V X → V Y → FactorsThrough F'.U f → FactorsThrough F.U f)
    (hess : ∀ Y : A, ∃ (X : A) (_ : V X) (u : X ⟶ Y) (v : Y ⟶ X),
      A.inv.star u = v ∧ u ≫ v = 𝟙 X ∧ FactorsThrough F'.U (v ≫ u - 𝟙 Y)) :
    IsUnitaryEquiv (F.restrictTo F' (V := V) hU).quot := by
  haveI : (F.restrictTo F' (V := V) hU).toHom.F.Full := inferInstanceAs (A.subIncl V).F.Full
  refine FiltrationHom.isUnitaryEquiv_quot _ (fun {X Y} f hf ↦ ?_) fun Y ↦ ?_
  · exact (factorsThrough_restrict_iff F hFV f).mpr (hrefl f.hom X.2 Y.2 hf)
  · obtain ⟨X, hX, u, v, huv, h₁, h₂⟩ := hess Y
    refine ⟨⟨X, hX⟩, u, v, huv, ?_, h₂⟩
    exact factorsThrough_sub_of_eq h₁

omit [V.IsStableUnderRetracts] in
/-- Separation criterion: `V → V' → V'/(U' ∩ V')` is a unitary equivalence if `I_{U'}` meets
`V` only in `0` and every object of `V'` splits unitarily, modulo `U'`, off an object of `V`. -/
theorem isUnitaryEquiv_subMap_proj (hV : ∀ X, V X → V' X) (hF'V' : ∀ X, F'.U X → V' X)
    (hrefl : ∀ {X Y : A} (f : X ⟶ Y), V X → V Y → FactorsThrough F'.U f → f = 0)
    (hess : ∀ Y : A, V' Y → ∃ (X : A) (_ : V X) (u : X ⟶ Y) (v : Y ⟶ X),
      A.inv.star u = v ∧ u ≫ v = 𝟙 X ∧ FactorsThrough F'.U (v ≫ u - 𝟙 Y)) :
    IsUnitaryEquiv (A.subMap hV ≫ (F'.restrict V').proj) := by
  refine isUnitaryEquiv_comp_proj _ (fun {X Y} f hf ↦ ?_) fun Y ↦ ?_
  · rw [factorsThrough_restrict_iff F' hF'V'] at hf
    exact ObjectProperty.hom_ext _ (hrefl f.hom X.2 Y.2 hf)
  · obtain ⟨X, hX, u, v, huv, h₁, h₂⟩ := hess Y.obj Y.2
    refine ⟨⟨X, hX⟩, ObjectProperty.homMk u, ObjectProperty.homMk v,
      ObjectProperty.hom_ext _ huv, ?_, (factorsThrough_restrict_iff F' hF'V' _).mpr h₂⟩
    exact factorsThrough_sub_of_eq (ObjectProperty.hom_ext _ h₁)

end KaroubiFiltration

namespace LowerLTheory

variable (𝕃 : LowerLTheory)

/-! ### Mayer–Vietoris -/

section MayerVietoris

variable {F : KaroubiFiltration A} {F' : KaroubiFiltration B} (Φ : FiltrationHom F F')
  (hΦ : IsUnitaryEquiv Φ.quot) {C₁ C₂ : InvCat} (u₁ : F.sub ≅ C₁) (u₂ : F'.sub ≅ C₂)
  (ι₁ : C₁ ⟶ A) (ι₂ : C₂ ⟶ B) (k : C₁ ⟶ C₂)

/-- The Mayer–Vietoris boundary `L_{n+1}(B) → L_{n+1}(B/U') ≅ L_{n+1}(A/U) → L_n(U) ≅ L_n(C₁)`,
(4.1). -/
def mvBdryOf (n : ℤ) : 𝕃.L B (n + 1) →+ 𝕃.L C₁ n :=
  mvBdry (fun n ↦ (𝕃.map u₁.hom n).comp (𝕃.bdry F n)) (fun n ↦ 𝕃.map F'.proj n)
    (𝕃.equivOf hΦ) n

/-- **Mayer–Vietoris** (§4, l.215): the localization sequences of `U ⊂ A` and `U' ⊂ B`, a map
of filtrations `Φ` inducing a unitary equivalence of quotients (excision), and identifications
`U ≅ C₁`, `U' ≅ C₂` compatible with `ι₁, ι₂, k` give the exact sequence
`L_n(C₁) → L_n(A) × L_n(C₂) → L_n(B) → L_{n-1}(C₁)`. -/
theorem isLES_mayerVietoris (h₁ : u₁.hom ≫ ι₁ = F.incl) (h₂ : u₂.hom ≫ ι₂ = F'.incl)
    (hk : Φ.sub ≫ u₂.hom = u₁.hom ≫ k) :
    IsLES (mvIn (fun n ↦ 𝕃.map ι₁ n) (fun n ↦ 𝕃.map k n))
      (mvOut (fun n ↦ 𝕃.map ι₂ n) (fun n ↦ 𝕃.map Φ.toHom n)) (𝕃.mvBdryOf Φ hΦ u₁) := by
  have hι : ι₁ ≫ Φ.toHom = k ≫ ι₂ := by
    rw [← cancel_epi u₁.hom, ← assoc, h₁, Φ.incl_comp, ← h₂, ← assoc, hk, assoc]
  refine IsLES.mayerVietoris (𝕃.isLES_iso F u₁ ι₁ h₁) (𝕃.isLES_iso F' u₂ ι₂ h₂)
    (fun n ↦ 𝕃.map_comp_eq hι n) (fun n ↦ 𝕃.map_comp_eq Φ.comp_proj n) fun n ↦ ?_
  ext x
  change 𝕃.map k n (𝕃.map u₁.hom n (𝕃.bdry F n x)) =
    𝕃.map u₂.hom n (𝕃.bdry F' n (𝕃.map Φ.quot (n + 1) x))
  rw [← AddMonoidHom.comp_apply (𝕃.bdry F' n), 𝕃.bdry_natural, AddMonoidHom.comp_apply,
    map_comp_apply, map_comp_apply, hk]

end MayerVietoris

/-! ### Lemma 4.1: boundary representatives -/

section Representatives

variable {F : KaroubiFiltration A} {F' : KaroubiFiltration B} (Φ : FiltrationHom F F')

/-- **Lemma 4.1** (l.217–237), relative form: let `X` be a pair over `A` with boundary in `U`
and `Q` a closed complex over `B/U'` isometric to the image of `X` (for a union `X ∪_∂ X'` with
`X'` in `U'`, by `SymPair.isometric_toQuot`).  If `e` is the map induced by `Φ` on quotients,
then `∂ e⁻¹ [Q] = bsign · [∂X]`. -/
theorem bdry_symm_cls (e : ∀ n, 𝕃.L F.quot n ≃+ 𝕃.L F'.quot n)
    (he : ∀ n x, e n x = 𝕃.map Φ.quot n x) {N : ℤ} (X : SymPair A.inv N)
    (hU : ∀ r, F.U (X.bd.C.X r)) (Q : SymPoincare F'.quot.inv (N + 1))
    (hQ : SymPoincare.Isometric ((X.map Φ.toHom).toQuot F' fun r ↦ Φ.map_mem _ (hU r)) Q) :
    𝕃.bdry F N ((e (N + 1)).symm (𝕃.cls F'.quot (N + 1) (Lconc.cls Q))) =
      𝕃.bsign N • 𝕃.cls F.sub N (Lconc.cls (X.bdLift F hU)) := by
  have : 𝕃.cls F'.quot (N + 1) (Lconc.cls Q) =
      e (N + 1) (𝕃.cls F.quot (N + 1) (Lconc.cls (X.toQuot F hU))) := by
    rw [he, ← 𝕃.cls_map, Lconc.map_cls, SymPair.toQuot_map F X hU Φ fun r ↦ Φ.map_mem _ (hU r),
      Lconc.cls_eq_of_isometric hQ]
  rw [this, AddEquiv.symm_apply_apply, 𝕃.bdry_pair]

/-- **Lemma 4.1** (l.217–237): as `bdry_symm_cls`, for a closed complex `P` over `B` whose image
modulo `U'` is isometric to the image of `X`. -/
theorem bdry_symm_proj_cls (e : ∀ n, 𝕃.L F.quot n ≃+ 𝕃.L F'.quot n)
    (he : ∀ n x, e n x = 𝕃.map Φ.quot n x) {N : ℤ} (X : SymPair A.inv N)
    (hU : ∀ r, F.U (X.bd.C.X r)) (P : SymPoincare B.inv (N + 1))
    (hP : SymPoincare.Isometric ((X.map Φ.toHom).toQuot F' fun r ↦ Φ.map_mem _ (hU r))
      (P.map F'.proj)) :
    𝕃.bdry F N ((e (N + 1)).symm (𝕃.map F'.proj (N + 1) (𝕃.cls B (N + 1) (Lconc.cls P)))) =
      𝕃.bsign N • 𝕃.cls F.sub N (Lconc.cls (X.bdLift F hU)) := by
  rw [← 𝕃.cls_map, Lconc.map_cls, 𝕃.bdry_symm_cls Φ e he X hU _ hP]

variable (hΦ : IsUnitaryEquiv Φ.quot) {C₁ : InvCat} (u₁ : F.sub ≅ C₁)

/-- **Lemma 4.1** for the Mayer–Vietoris boundary (4.1): `∂_{A,B} [V_A ∪_P V_B] = bsign · [P]`. -/
theorem mvBdryOf_cls {N : ℤ} (X : SymPair A.inv N) (hU : ∀ r, F.U (X.bd.C.X r))
    (P : SymPoincare B.inv (N + 1))
    (hP : SymPoincare.Isometric ((X.map Φ.toHom).toQuot F' fun r ↦ Φ.map_mem _ (hU r))
      (P.map F'.proj)) :
    𝕃.mvBdryOf Φ hΦ u₁ N (𝕃.cls B (N + 1) (Lconc.cls P)) =
      𝕃.bsign N • 𝕃.cls C₁ N (Lconc.cls ((X.bdLift F hU).map u₁.hom)) := by
  change 𝕃.map u₁.hom N (𝕃.bdry F N ((𝕃.equivOf hΦ (N + 1)).symm
    (𝕃.map F'.proj (N + 1) (𝕃.cls B (N + 1) (Lconc.cls P))))) = _
  rw [𝕃.bdry_symm_proj_cls Φ _ (fun _ _ ↦ rfl) X hU P hP, Units.smul_def, Units.smul_def,
    map_zsmul, ← 𝕃.cls_map, Lconc.map_cls]

end Representatives

/-! ### Mayer–Vietoris for restrictions, natural endomorphisms, separated projections -/

section Restrict

variable {F F' : KaroubiFiltration A} {V V' : ObjectProperty A} [IsAdditiveSub V]
  [V.IsStableUnderRetracts] [IsAdditiveSub V'] [V'.IsStableUnderRetracts]
  (hU : ∀ X, F.U X → F'.U X) (hV : ∀ X, V X → V' X) (hFV : ∀ X, F.U X → V X)
  (hF'V' : ∀ X, F'.U X → V' X) (hΦ : IsUnitaryEquiv (F.restrictMap F' hU hV).quot)

/-- **Mayer–Vietoris** for `U ⊂ V`, `U' ⊂ V'` with `U ≤ U'`, `V ≤ V'` and excision `hΦ`:
`L_n(U) → L_n(V) × L_n(U') → L_n(V') → L_{n-1}(U)`. -/
theorem isLES_mayerVietoris_restrict :
    IsLES (mvIn (fun n ↦ 𝕃.map (A.subMap hFV) n) (fun n ↦ 𝕃.map (A.subMap hU) n))
      (mvOut (fun n ↦ 𝕃.map (A.subMap hF'V') n) (fun n ↦ 𝕃.map (A.subMap hV) n))
      (𝕃.mvBdryOf (F.restrictMap F' hU hV) hΦ (F.restrictSubIso V hFV)) :=
  𝕃.isLES_mayerVietoris _ hΦ _ (F'.restrictSubIso V' hF'V') _ _ _
    (KaroubiFiltration.restrictSubIso_hom_comp hFV)
    (KaroubiFiltration.restrictSubIso_hom_comp hF'V')
    (KaroubiFiltration.restrictMap_sub_comp hU hV hFV hF'V')

/-- **Mayer–Vietoris (4.1)** for a cover `A ∪ B = X`: excision `V/(U ∩ V) ≃ A/U'` gives
`L_n(U) → L_n(V) × L_n(U') → L_n(A) → L_{n-1}(U)`. -/
theorem isLES_mayerVietoris_restrictTo
    (hΦ : IsUnitaryEquiv (F.restrictTo F' (V := V) hU).quot) :
    IsLES (mvIn (fun n ↦ 𝕃.map (A.subMap hFV) n) (fun n ↦ 𝕃.map (A.subMap hU) n))
      (mvOut (fun n ↦ 𝕃.map F'.incl n) (fun n ↦ 𝕃.map (A.subIncl V) n))
      (𝕃.mvBdryOf (F.restrictTo F' hU) hΦ (F.restrictSubIso V hFV)) :=
  𝕃.isLES_mayerVietoris _ hΦ _ (Iso.refl F'.sub) _ _ _
    (KaroubiFiltration.restrictSubIso_hom_comp hFV) (Category.id_comp _)
    (KaroubiFiltration.restrictTo_sub_comp hU hFV)

/-- The Mayer–Vietoris boundary commutes with an endomorphism preserving `U, V, U', V'`
(l.239; for `τ ⊗ −` this includes commuting with the excision `hΦ`). -/
theorem mvBdryOf_restrict_comm (T : A ⟶ A) (hTU : ∀ X, F.U X → F.U (T.F.obj X))
    (hTV : ∀ X, V X → V (T.F.obj X)) (hTU' : ∀ X, F'.U X → F'.U (T.F.obj X))
    (hTV' : ∀ X, V' X → V' (T.F.obj X)) (n : ℤ) (x : 𝕃.L (A.sub V') (n + 1)) :
    𝕃.mvBdryOf (F.restrictMap F' hU hV) hΦ (F.restrictSubIso V hFV) n
        (𝕃.map (A.subRestrict T hTV') (n + 1) x) =
      𝕃.map (A.subRestrict T hTU) n
        (𝕃.mvBdryOf (F.restrictMap F' hU hV) hΦ (F.restrictSubIso V hFV) n x) := by
  refine mvBdry_comm (νC := 𝕃.map (F.restrictEndo T hTU hTV).quot (n + 1))
    (νC' := 𝕃.map (F'.restrictEndo T hTU' hTV').quot (n + 1)) (fun c ↦ ?_) (fun c ↦ ?_)
    (fun b ↦ ?_) x
  · change 𝕃.map _ n (𝕃.bdry _ n (𝕃.map _ (n + 1) c)) = 𝕃.map _ n (𝕃.map _ n (𝕃.bdry _ n c))
    rw [← AddMonoidHom.comp_apply (𝕃.bdry _ n), 𝕃.bdry_natural, AddMonoidHom.comp_apply,
      map_comp_apply, map_comp_apply, KaroubiFiltration.restrictEndo_sub_comp T hTU hTV hFV]
  · change 𝕃.map _ (n + 1) (𝕃.map _ (n + 1) c) = 𝕃.map _ (n + 1) (𝕃.map _ (n + 1) c)
    rw [map_comp_apply, map_comp_apply, ← FiltrationHom.comp_quot, ← FiltrationHom.comp_quot,
      KaroubiFiltration.restrictEndo_comp_restrictMap T hU hV hTU hTV hTU' hTV']
  · rw [map_comp_apply, map_comp_apply]
    exact congrArg (fun Θ ↦ 𝕃.map Θ (n + 1) b) (F'.restrictEndo T hTU' hTV').comp_proj

omit [V.IsStableUnderRetracts] in
/-- The separated projection `L(V') → L(V'/(U' ∩ V')) ≅ L(V)`. -/
def projSepOf (hS : IsUnitaryEquiv (A.subMap hV ≫ (F'.restrict V').proj)) (n : ℤ) :
    𝕃.L (A.sub V') n →+ 𝕃.L (A.sub V) n :=
  (𝕃.equivOf hS n).symm.toAddMonoidHom.comp (𝕃.map (F'.restrict V').proj n)

omit [V.IsStableUnderRetracts] in
theorem projSepOf_subMap (hS : IsUnitaryEquiv (A.subMap hV ≫ (F'.restrict V').proj)) (n : ℤ)
    (x : 𝕃.L (A.sub V) n) : 𝕃.projSepOf hV hS n (𝕃.map (A.subMap hV) n x) = x := by
  simp only [projSepOf, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, map_comp_apply]
  exact 𝕃.equivOf_symm_map hS n x

end Restrict

/-! ### Cut boundaries and their naturality (the squares of (11.2)) -/

section Cut

variable {F : KaroubiFiltration A} {F' : KaroubiFiltration B} {Φ : FiltrationHom F F'}

theorem _root_.HSFormal.LTheory.FiltrationHom.ext' {Ψ₁ Ψ₂ : FiltrationHom F F'}
    (h : Ψ₁.toHom = Ψ₂.toHom) : Ψ₁ = Ψ₂ := by
  cases Ψ₁
  cases Ψ₂
  cases h
  rfl

/-- A cut boundary `L_{n+1}(Q₀) → L_{n+1}(B/U') ≅ L_{n+1}(A/U) → L_n(U)`, `∂ ∘ e⁻¹ ∘ q`, for an
excision `Φ` (the shape of (4.1) and (4.2)). -/
def cutOf (hΦ : IsUnitaryEquiv Φ.quot) {Q₀ : InvCat} (q : Q₀ ⟶ F'.quot) (n : ℤ) :
    𝕃.L Q₀ (n + 1) →+ 𝕃.L F.sub n :=
  (𝕃.bdry F n).comp ((𝕃.equivOf hΦ (n + 1)).symm.toAddMonoidHom.comp (𝕃.map q (n + 1)))

/-- **Naturality of cut boundaries** (l.239): maps of filtrations `α : F → F₂`, `β : F' → F₂'`
compatible with the excisions and with `q`, `q₂` give `α_* ∘ ∂ = ∂₂ ∘ γ_*`. -/
theorem cutOf_natural {A₂ B₂ : InvCat} {F₂ : KaroubiFiltration A₂} {F₂' : KaroubiFiltration B₂}
    {Φ₂ : FiltrationHom F₂ F₂'} (hΦ : IsUnitaryEquiv Φ.quot) (hΦ₂ : IsUnitaryEquiv Φ₂.quot)
    {Q₀ Q₂ : InvCat} (q : Q₀ ⟶ F'.quot) (q₂ : Q₂ ⟶ F₂'.quot) (α : FiltrationHom F F₂)
    (β : FiltrationHom F' F₂') (γ : Q₀ ⟶ Q₂) (hαβ : Φ.toHom ≫ β.toHom = α.toHom ≫ Φ₂.toHom)
    (hq : q ≫ β.quot = γ ≫ q₂) (n : ℤ) :
    (𝕃.map α.sub n).comp (𝕃.cutOf hΦ q n) = (𝕃.cutOf hΦ₂ q₂ n).comp (𝕃.map γ (n + 1)) := by
  have hquot : Φ.quot ≫ β.quot = α.quot ≫ Φ₂.quot := by
    rw [← FiltrationHom.comp_quot, ← FiltrationHom.comp_quot,
      FiltrationHom.ext' (Ψ₁ := Φ.comp β) (Ψ₂ := α.comp Φ₂) hαβ]
  ext x
  simp only [cutOf, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  rw [map_comp_apply, ← hq, ← map_comp_apply,
    𝕃.equivOf_symm_natural hΦ hΦ₂ α.quot β.quot hquot, ← AddMonoidHom.comp_apply (𝕃.map α.sub n),
    ← 𝕃.bdry_natural, AddMonoidHom.comp_apply]

end Cut

end LowerLTheory

end

end HSFormal.LTheory
