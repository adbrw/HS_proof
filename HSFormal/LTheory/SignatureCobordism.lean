import HSFormal.LTheory.MiddleForm
import HSFormal.LTheory.ConcreteL

/-!
# Cobordism invariance of `Sign_G` (L-theory module M9b)

`PermRep G S` has unitary biproducts (block sums, `PermRep.unitaryBicone`), so it is an `InvCat`
(`PermRep.invCat`; `Free(ℚ[G])` for `S = G`).

For an `(N+1)`-dimensional Poincaré pair `X = (j : C ⟶ D, (δφ, φ))` over `PermRep G S` with
`m = N - m`, the image `L` of `j^* : H^m(D, p_D) → H^m(C, p)` (`SymPair.lagrangian`) is a
`G`-invariant Lagrangian of the middle form of `∂X` ("half lives, half dies", issue I5):
* `L` is isotropic: `⟨j^* y, φ j^* y'⟩ = ⟨y, j φ j^* y'⟩` and `j φ j^* = dδφ + δφδ`;
* `L^⊥ ⊆ L` (`SymPair.mem_lagrangian_of_forall`): for `x ⊥ L`, `j φ x = dw` by Kronecker duality
  over `ℚ`; `ι x = (x, 0)` is a cocycle of `Cone(j)^{N+1-*}` with `Ψ ι x = -dw`, so the homotopy
  inverse of `Ψ` makes `ι p^* x` a coboundary of the cone, and exactness of
  `H^m(D) → H^m(C) → H^{m+1}(D, C)` on cochains (`PermRep.exists_of_bdInc_eq_d`) gives
  `p^* x = j^* β + δα`.

Hence `L = L^⊥`, `2 dim L = dim H^m(C, p)` (`SymPair.two_mul_finrank_lagrangian`) and
`Sign_G(∂X) = 0` for even `m` (`SymPair.sign_bd`).  Only `X.poincare` is used (no separate duality
statement for the pair).  `PermRep.signHom` is `Sign_G` on `Lconc (invCat G S) N` (`sign₄Hom` for
`N = 4`); its value at `1` is the ordinary signature (`signHom_cls_one`) and is unchanged by the
functor `PermRep.forget` to the trivial group, the identity on matrices
(`signHom_map_forget_one`; no factor `1 / |G|`).
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression
open LinearMap (BilinForm)
open scoped Matrix

noncomputable section

namespace PermRep

variable {G S : Type} [Group G] [MulAction G S] [Fintype S] [DecidableEq S]

section Biprod

@[simp] lemma add_val {X Y : PermRep G S} (f g : X ⟶ Y) : (f + g).1 = f.1 + g.1 := rfl

/-- The morphism sending the basis vector `(i, s)` to `(e i, s)`. -/
def ofFin {X Y : PermRep G S} (e : Fin X.rank → Fin Y.rank) : X ⟶ Y :=
  ⟨Matrix.of fun y x ↦ if y = (e x.1, x.2) then 1 else 0, fun g i s j t ↦ by
    simp [Prod.ext_iff, smul_left_cancel_iff]⟩

lemma ofFin_val {X Y : PermRep G S} (e : Fin X.rank → Fin Y.rank) (y : Y.Idx) (x : X.Idx) :
    (ofFin e).1 y x = if y = (e x.1, x.2) then 1 else 0 := rfl

lemma ofFin_comp_star_self {X Y : PermRep G S} {e : Fin X.rank → Fin Y.rank}
    (he : Function.Injective e) : ofFin e ≫ (inv G S).star (ofFin e) = 𝟙 X := by
  ext x x'
  simp only [comp_val, star_val, id_val, Matrix.mul_apply, Matrix.transpose_apply, ofFin_val,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Matrix.one_apply]
  simp [Prod.ext_iff, he.eq_iff]

lemma ofFin_comp_star_eq_zero {X Y Z : PermRep G S} {e : Fin X.rank → Fin Z.rank}
    {e' : Fin Y.rank → Fin Z.rank} (h : ∀ i i', e i ≠ e' i') :
    ofFin e ≫ (inv G S).star (ofFin e') = 0 := by
  ext x x'
  simp only [comp_val, star_val, Matrix.mul_apply, Matrix.transpose_apply, ofFin_val,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp [Prod.ext_iff, Ne.symm (h _ _)]

lemma sum_ofFin_val {X Y : PermRep G S} {e : Fin X.rank → Fin Y.rank} (he : Function.Injective e)
    (i : Fin X.rank) (s : S) (z : Y.Idx) :
    ∑ x : X.Idx, (ofFin e).1 (e i, s) x * (ofFin e).1 z x = if z = (e i, s) then 1 else 0 := by
  have h (x : X.Idx) : ((e i, s) = (e x.1, x.2)) ↔ (i, s) = x := by simp [Prod.ext_iff, he.eq_iff]
  simp only [ofFin_val, h, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

lemma sum_ofFin_val_eq_zero {X Y : PermRep G S} {e : Fin X.rank → Fin Y.rank} {k : Fin Y.rank}
    (hk : ∀ i, e i ≠ k) (s : S) (z : Y.Idx) :
    ∑ x : X.Idx, (ofFin e).1 (k, s) x * (ofFin e).1 z x = 0 :=
  Finset.sum_eq_zero fun x _ ↦ by simp [ofFin_val, Prod.ext_iff, Ne.symm (hk _)]

lemma castAdd_ne_natAdd {a b : ℕ} (i : Fin a) (j : Fin b) : Fin.castAdd b i ≠ Fin.natAdd a j :=
  fun h ↦ by have := congrArg Fin.val h; simp at this; omega

variable (X Y : PermRep G S)

/-- The block sum `ℚ^{(a + b) × S}`. -/
abbrev blockSum : PermRep G S := ⟨X.rank + Y.rank⟩

lemma total : (inv G S).star (ofFin (Y := X.blockSum Y) (Fin.castAdd Y.rank)) ≫
      ofFin (Fin.castAdd Y.rank) + (inv G S).star (ofFin (Y := X.blockSum Y) (Fin.natAdd X.rank)) ≫
      ofFin (Fin.natAdd X.rank) = 𝟙 _ := by
  ext ⟨k, s⟩ z
  simp only [add_val, comp_val, star_val, id_val, Matrix.one_apply, Matrix.add_apply,
    Matrix.mul_apply, Matrix.transpose_apply]
  induction k using Fin.addCases with
  | left i =>
    rw [sum_ofFin_val (Fin.castAdd_injective _ _), sum_ofFin_val_eq_zero fun _ ↦
      (castAdd_ne_natAdd _ _).symm, add_zero]
    simp [eq_comm]
  | right i =>
    rw [sum_ofFin_val (Fin.natAdd_injective _ _), sum_ofFin_val_eq_zero fun _ ↦
      castAdd_ne_natAdd _ _, zero_add]
    simp [eq_comm]

/-- The block sum with the basis inclusions and their transposes: a unitary bicone. -/
def unitaryBicone : UnitaryBicone (inv G S) X Y where
  pt := X.blockSum Y
  fst := (inv G S).star (ofFin (Fin.castAdd Y.rank))
  snd := (inv G S).star (ofFin (Fin.natAdd X.rank))
  inl := ofFin (Fin.castAdd Y.rank)
  inr := ofFin (Fin.natAdd X.rank)
  inl_fst := ofFin_comp_star_self (Fin.castAdd_injective _ _)
  inl_snd := ofFin_comp_star_eq_zero castAdd_ne_natAdd
  inr_fst := ofFin_comp_star_eq_zero fun _ _ ↦ (castAdd_ne_natAdd _ _).symm
  inr_snd := ofFin_comp_star_self (Fin.natAdd_injective _ _)
  isBilimit := isBinaryBilimitOfTotal _ (total X Y)
  star_inl := rfl
  star_inr := rfl

instance : HasZeroObject (PermRep G S) :=
  ⟨⟨⟨0⟩, (IsZero.iff_id_eq_zero _).mpr (hom_ext (Matrix.ext fun i _ ↦ i.1.elim0))⟩⟩

instance : HasBinaryBiproducts (PermRep G S) :=
  ⟨fun X Y ↦ .mk ⟨_, (unitaryBicone X Y).isBilimit⟩⟩

instance : HasFiniteBiproducts (PermRep G S) := hasFiniteBiproducts_of_binary

end Biprod

variable (G S) in
/-- `PermRep G S` as a category with involution; for `S = G` this is `Free(ℚ[G])`. -/
@[reducible] def invCat : InvCat where
  carrier := PermRep G S
  inv := inv G S
  unitary X Y := ⟨unitaryBicone X Y⟩

section Exactness

open homotopyCofiber

variable {N : ℤ} {C D : ChainComplex (PermRep G S) ℤ} (j : C ⟶ D)

/-- The restriction `Cone(j)^{N+1-*} ⟶ D^{N+1-*}`, dual to `D ⟶ Cone(j)`. -/
abbrev coneRes : dualComplex (inv G S) (N + 1) (cone j) ⟶ dualComplex (inv G S) (N + 1) D :=
  dualHom (inv G S) (N + 1) (inr j)

/-- A degreewise retraction of `bdInc`. -/
def bdRet (r : ℤ) :
    (dualComplex (inv G S) (N + 1) (cone j)).X r ⟶ (dualComplex (inv G S) N C).X r :=
  r.negOnePow • (inv G S).star (inlX j (N - r) (N + 1 - r) (down_rel_sub N r))

/-- A degreewise section of `coneRes`. -/
def coneSec (r : ℤ) :
    (dualComplex (inv G S) (N + 1) D).X r ⟶ (dualComplex (inv G S) (N + 1) (cone j)).X r :=
  (inv G S).star (sndX j (N + 1 - r))

lemma bdInc_f_comp_bdRet (r : ℤ) : (bdInc j).f r ≫ bdRet (N := N) j r = 𝟙 _ := by
  simp [bdRet, smul_smul]

lemma bdInc_comp_coneRes : bdInc (J := inv G S) (N := N) j ≫ coneRes j = 0 := by
  ext r
  simp

lemma bdRet_comp_bdInc_add (r : ℤ) :
    bdRet (N := N) j r ≫ (bdInc j).f r + (coneRes j).f r ≫ coneSec j r = 𝟙 _ := by
  simp only [bdRet, coneSec, bdInc_f, dualHom_f, inr_f, Linear.units_smul_comp,
    Linear.comp_units_smul, smul_smul, Int.units_mul_self, one_smul]
  rw [← (inv G S).star_comp, ← (inv G S).star_comp, ← (inv G S).star_add,
    ← cone.id_X j _ _ (down_rel_sub N r)]
  exact (inv G S).star_id _

variable (N D) in
/-- The identification `(D^{N+1-*})_{m+1} = (D^{N-*})_m`. -/
def shiftIso (m : ℤ) :
    (dualComplex (inv G S) (N + 1) D).X (m + 1) ⟶ (dualComplex (inv G S) N D).X m :=
  (D.XIsoOfEq (by omega : N + 1 - (m + 1) = N - m)).hom

lemma shiftIso_comp_d (m : ℤ) :
    shiftIso N D m ≫ (dualComplex (inv G S) N D).d m (m - 1) =
      (dualComplex (inv G S) (N + 1) D).d (m + 1) m ≫
        (-(D.XIsoOfEq (by omega : N + 1 - m = N - (m - 1))).hom) := by
  simp [shiftIso, XIsoOfEq_star_d D (by omega : N + 1 - m = N - (m - 1))
    (by omega : N + 1 - (m + 1) = N - m), Int.negOnePow_succ]

lemma coneSec_d_bdRet (m : ℤ) :
    coneSec j (m + 1) ≫ (dualComplex (inv G S) (N + 1) (cone j)).d (m + 1) m ≫ bdRet j m =
      -(shiftIso N D m ≫ (dualHom (inv G S) N j).f m) := by
  have h₀ : N + 1 - (m + 1) = N - m := by omega
  have hi : (ComplexShape.down ℤ).Rel (N + 1 - m) (N + 1 - (m + 1)) := by simp; omega
  simp only [coneSec, bdRet, dualComplex_d, Linear.units_smul_comp, Linear.comp_units_smul,
    cone.star_sndX_d_assoc j _ _ hi, add_comp, assoc, cone.star_fstX_inlX' j hi (down_rel_sub N m),
    cone.star_sndX_inlX, comp_zero, add_zero, star_f_XIsoOfEq, dualHom_f, smul_smul]
  rw [Int.negOnePow_succ, mul_neg, Int.units_mul_self, Units.neg_smul, one_smul]
  rfl

/-- Exactness of `H^m(D) → H^m(C) → H^{m+1}(D, C)` on cochains: if `ι x` is a coboundary in
`Cone(j)^{N+1-*}`, then `x = j^* β + δ α` for a cocycle `β` of `D^{N-*}`. -/
lemma exists_of_bdInc_eq_d (m : ℤ) {x : ((dualComplex (inv G S) N C).X m).Sp}
    {z : ((dualComplex (inv G S) (N + 1) (cone j)).X (m + 1)).Sp}
    (h : toLin ((bdInc j).f m) x =
      toLin ((dualComplex (inv G S) (N + 1) (cone j)).d (m + 1) m) z) :
    ∃ β ∈ cycles (dualComplex (inv G S) N D) m, ∃ α, x =
      toLin ((dualHom (inv G S) N j).f m) β +
        toLin ((dualComplex (inv G S) N C).d (m + 1) m) α := by
  have hz : z = toLin ((bdInc j).f (m + 1)) (toLin (bdRet j (m + 1)) z) +
      toLin (coneSec j (m + 1)) (toLin ((coneRes j).f (m + 1)) z) := by
    rw [← toLin_comp, ← toLin_comp, ← toLin_add, bdRet_comp_bdInc_add, toLin_id]
  have hb : toLin ((dualComplex (inv G S) (N + 1) D).d (m + 1) m)
      (toLin ((coneRes j).f (m + 1)) z) = 0 := by
    rw [← toLin_comp, (coneRes j).comm, toLin_comp, ← h, ← toLin_comp, ← comp_f,
      bdInc_comp_coneRes, zero_f, toLin_zero]
  refine ⟨-toLin (shiftIso N D m) (toLin ((coneRes j).f (m + 1)) z), neg_mem ?_,
    toLin (bdRet j (m + 1)) z, ?_⟩
  · rw [cycles, LinearMap.mem_ker, ← toLin_comp, shiftIso_comp_d, toLin_comp, hb, map_zero]
  · have e₁ (a) : toLin (bdRet j m) (toLin ((dualComplex (inv G S) (N + 1) (cone j)).d (m + 1) m)
        (toLin ((bdInc j).f (m + 1)) a)) = toLin ((dualComplex (inv G S) N C).d (m + 1) m) a := by
      rw [toLin_comp_eq ((bdInc j).comm (m + 1) m), ← toLin_comp, bdInc_f_comp_bdRet, toLin_id]
    have e₂ (b) : toLin (bdRet j m) (toLin ((dualComplex (inv G S) (N + 1) (cone j)).d (m + 1) m)
        (toLin (coneSec j (m + 1)) b)) =
          -toLin ((dualHom (inv G S) N j).f m) (toLin (shiftIso N D m) b) := by
      rw [← toLin_comp, ← toLin_comp, coneSec_d_bdRet, toLin_neg, toLin_comp]
    have hx := congrArg (toLin (bdRet j m)) h
    rw [← toLin_comp, bdInc_f_comp_bdRet, toLin_id, hz, map_add, map_add, e₁, e₂] at hx
    rw [hx, map_neg, add_comm]

end Exactness

end PermRep

open PermRep

namespace SymPair

variable {G S : Type} [Group G] [MulAction G S] [Fintype S] [DecidableEq S] {N : ℤ}
  (X : SymPair (inv G S) N) (m : ℤ)

/-- The restriction `j^* : H^m(D, p_D) → H^m(C, p)` to the boundary. -/
def restrict :
    karHomology (dualComplex (inv G S) N X.D) (dualHom (inv G S) N X.pD) m →ₗ[ℚ] X.bd.middle m :=
  karMap m (dualHom (inv G S) N X.j)
    (by rw [← dualHom_comp, ← dualHom_comp, X.j_comp_pD, X.p_comp_j])

/-- The Lagrangian `L = im(j^*) ⊆ H^m(C, p)`. -/
def lagrangian : Submodule ℚ (X.bd.middle m) :=
  LinearMap.range (X.restrict m)

lemma lagrangian_le_comap (g : G) :
    X.lagrangian m ≤ (X.lagrangian m).comap (X.bd.middleRep m g) := by
  rintro _ ⟨y, rfl⟩
  exact ⟨karRep _ _ m g y, karMap_karRep m _ _ g y⟩

variable (hm : m = N - m)

/-- `L` is isotropic: `⟨j^* y, φ j^* y'⟩ = ⟨y, j φ j^* y'⟩` and `j φ j^* = dδφ + δφδ`. -/
theorem lagrangian_isotropic :
    ∀ u ∈ X.lagrangian m, ∀ v ∈ X.lagrangian m, X.bd.middleForm m hm u v = 0 := by
  rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  obtain ⟨y', rfl⟩ := Submodule.Quotient.mk_surjective _ v
  change pairing m hm X.bd.φ (toLin ((dualHom (inv G S) N X.j).f m) y.1)
    (toLin ((dualHom (inv G S) N X.j).f m) y'.1) = 0
  rw [← pairing_conj, pairing_homotopy m hm X.δφ y.2 y'.2, pairing_apply, zero_f, toLin_zero,
    dotProduct_zero]

/-- The cocycle `x` of `C^{N-*}` pairing trivially with `j^*` of all cocycles of `D^{N-*}` is
`j^*` of a cocycle modulo `karBoundaries`: `j φ x` is then a boundary `dw` (Kronecker duality), so
`(x, 0)` is a cocycle of `Cone(j)^{N+1-*}` with `Ψ(x, 0) = -dw`, hence `p^* x` is a coboundary
of the cone (`Ψ` is a Kar homotopy equivalence), and exactness gives `p^* x = j^* β + δα`. -/
theorem exists_sub_mem_karBoundaries {x : ((dualComplex (inv G S) N X.bd.C).X m).Sp}
    (hx : x ∈ cycles (dualComplex (inv G S) N X.bd.C) m)
    (h : ∀ y ∈ cycles (dualComplex (inv G S) N X.D) m,
      pairing m hm X.bd.φ (toLin ((dualHom (inv G S) N X.j).f m) y) x = 0) :
    ∃ y ∈ cycles (dualComplex (inv G S) N X.D) m, x - toLin ((dualHom (inv G S) N X.j).f m) y ∈
      karBoundaries (dualComplex (inv G S) N X.bd.C) (dualHom (inv G S) N X.bd.p) m := by
  obtain ⟨w, hw⟩ : ∃ w, toLin ((X.bd.φ ≫ X.j).f m) x = toLin (X.D.d (m + 1) m) w := by
    have key : ∀ u, (X.D.d (N - (m - 1)) (N - m)).1ᵀ *ᵥ u = 0 →
        toLin (eqToHom (congrArg X.D.X hm)) (toLin ((X.bd.φ ≫ X.j).f m) x) ⬝ᵥ u = 0 := by
      intro u hu
      have hy : u ∈ cycles (dualComplex (inv G S) N X.D) m := by
        rw [PermRep.cycles, LinearMap.mem_ker, dualComplex_d]
        erw [toLin_units_smul, toLin_apply, star_val, hu, smul_zero]
      have := h u hy
      simp only [pairing_apply, dualHom_f, toLin_star_dotProduct, ← toLin_comp] at this
      erw [assoc, ← comp_f, ← f_comp_eqToHom (X.bd.φ ≫ X.j) hm, toLin_comp] at this
      rwa [dotProduct_comm]
    obtain ⟨w, hw⟩ := exists_transpose_mulVec_eq _ key
    refine ⟨toLin (eqToHom (congrArg X.D.X (show N - (m - 1) = m + 1 by omega))) w, ?_⟩
    rw [Matrix.transpose_transpose, ← toLin_apply] at hw
    rw [← toLin_comp_eq (eqToHom_naturality₂ X.D.d (by omega) hm.symm), hw, toLin_eqToHom_trans,
      eqToHom_refl, toLin_id]
  obtain ⟨g, -, -, ⟨K⟩⟩ := X.poincare
  have hv : toLin ((dualComplex (inv G S) (N + 1) (cone X.j)).d m (m - 1))
      (toLin ((bdInc X.j).f m) x) = 0 := by
    rw [← toLin_comp, (bdInc X.j).comm, toLin_comp, LinearMap.mem_ker.mp hx, map_zero]
  have hΨ : toLin (X.Ψ.f m) (toLin ((bdInc X.j).f m) x) = -toLin (X.D.d (m + 1) m) w := by
    rw [← toLin_comp, ← comp_f, X.bdInc_comp_Ψ, neg_f_apply, toLin_neg, hw]
  have hc := congrArg (fun f ↦ toLin f (toLin ((bdInc X.j).f m) x)) (K.comm m)
  rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel m (m - 1) by simp),
    prevD_eq _ (show (ComplexShape.down ℤ).Rel (m + 1) m by simp)] at hc
  simp only [comp_f, toLin_add, toLin_comp, hv, map_zero, zero_add, hΨ, map_neg] at hc
  rw [← toLin_comp_eq (g.comm (m + 1) m)] at hc
  have hz : toLin ((bdInc X.j).f m) (toLin ((dualHom (inv G S) N X.bd.p).f m) x) =
      toLin ((dualComplex (inv G S) (N + 1) (cone X.j)).d (m + 1) m)
        (-toLin (g.f (m + 1)) w - toLin (K.hom m (m + 1)) (toLin ((bdInc X.j).f m) x)) := by
    rw [← toLin_comp, ← comp_f,
      ← bdInc_comp_dualHom_coneMap (comm_of_kar X.bd.p_idem X.pD_idem X.j_kar), comp_f,
      toLin_comp, map_sub, map_neg, hc]
    abel
  obtain ⟨β, hβ, α, hα⟩ := exists_of_bdInc_eq_d X.j m hz
  refine ⟨β, hβ, ?_⟩
  have e : x - toLin ((dualHom (inv G S) N X.j).f m) β =
      (x - toLin ((dualHom (inv G S) N X.bd.p).f m) x) +
        toLin ((dualComplex (inv G S) N X.bd.C).d (m + 1) m) α := by
    rw [hα]
    abel
  rw [e]
  refine add_mem (Submodule.mem_sup_right ?_) (Submodule.mem_sup_left ⟨α, rfl⟩)
  rw [LinearMap.mem_ker, map_sub, ← toLin_comp, ← comp_f, ← dualHom_comp, X.bd.p_idem, sub_self]

/-- Half lives, half dies: `L^⊥ ⊆ L`. -/
theorem mem_lagrangian_of_forall (u : X.bd.middle m)
    (h : ∀ v ∈ X.lagrangian m, X.bd.middleForm m hm v u = 0) : u ∈ X.lagrangian m := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  obtain ⟨y, hy, hxy⟩ := X.exists_sub_mem_karBoundaries m hm x.2 fun y hy ↦
    h _ ⟨Submodule.Quotient.mk ⟨y, hy⟩, rfl⟩
  refine ⟨Submodule.Quotient.mk ⟨y, hy⟩, (Submodule.Quotient.eq _).mpr ?_⟩
  rw [Submodule.mem_comap, ← neg_sub]
  exact neg_mem hxy

/-- `L = L^⊥` for the middle form of the boundary. -/
theorem orthogonal_lagrangian :
    (X.bd.middleForm m hm).orthogonal (X.lagrangian m) = X.lagrangian m :=
  le_antisymm (fun u hu ↦ X.mem_lagrangian_of_forall m hm u hu)
    fun u hu v hv ↦ X.lagrangian_isotropic m hm v hv u hu

include hm in
/-- `2 · dim L = dim H^m(C, p)`. -/
theorem two_mul_finrank_lagrangian :
    2 * Module.finrank ℚ (X.lagrangian m) = Module.finrank ℚ (X.bd.middle m) := by
  have h₁ := LinearMap.BilinForm.finrank_orthogonal (X.bd.middleForm_nondegenerate m hm)
    (X.lagrangian m)
  have h₂ := Submodule.finrank_le (X.lagrangian m)
  rw [X.orthogonal_lagrangian m hm] at h₁
  omega

/-- The boundary of a Poincaré pair has `Sign_G = 0`. -/
theorem sign_bd [Finite G] (he : Even m) : X.bd.sign m hm = 0 :=
  ratEquivariantSignature_eq_zero_of_isotropic (X.bd.isInvariantForm_middleForm m hm he)
    (X.lagrangian_le_comap m) (X.lagrangian_isotropic m hm) (X.two_mul_finrank_lagrangian m hm)

end SymPair

namespace SymPoincare

variable {G S : Type} [Group G] [MulAction G S] [Fintype S] [DecidableEq S] [Finite G] {N : ℤ}
  (m : ℤ) (hm : m = N - m)

/-- A null-cobordant complex has `Sign_G = 0`. -/
theorem sign_eq_zero_of_nullCobordant {P : SymPoincare (inv G S) N} (hP : NullCobordant P)
    (he : Even m) : P.sign m hm = 0 := by
  obtain ⟨X, rfl⟩ := hP
  exact X.sign_bd m hm he

/-- Cobordism invariance of `Sign_G`. -/
theorem sign_eq_of_cobordant {P Q : SymPoincare (inv G S) N} (h : Cobordant P Q) (he : Even m) :
    P.sign m hm = Q.sign m hm := by
  obtain ⟨b, hb⟩ := h
  have := sign_eq_zero_of_nullCobordant m hm hb he
  rwa [sign_sum _ _ m hm _ he, sign_neg _ m hm he, add_neg_eq_zero] at this

end SymPoincare

section RatSign

variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℚ V₁] [FiniteDimensional ℚ V₁]
  [AddCommGroup V₂] [Module ℚ V₂] [FiniteDimensional ℚ V₂] {b₁ : BilinForm ℚ V₁}
  {b₂ : BilinForm ℚ V₂}

/-- The rational signature is an isometry invariant. -/
theorem ratSignature_congr (hb₁ : b₁.IsSymm) (hnd₁ : b₁.Nondegenerate) (hb₂ : b₂.IsSymm)
    (hnd₂ : b₂.Nondegenerate) (e : V₁ ≃ₗ[ℚ] V₂) (he : ∀ v w, b₂ (e v) (e w) = b₁ v w) :
    ratSignature b₂ = ratSignature b₁ := by
  have h := ratEquivariantSignature_congr (G := Unit) (ρ₁ := 1) (ρ₂ := 1)
    ⟨hb₁, hnd₁, fun _ _ _ ↦ rfl⟩ e (fun _ _ ↦ rfl) he
  have h₁ := ratEquivariantSignature_one (G := Unit) (ρ := 1) hb₁ hnd₁ fun _ _ _ ↦ rfl
  have h₂ := ratEquivariantSignature_one (G := Unit) (ρ := 1) hb₂ hnd₂ fun _ _ _ ↦ rfl
  exact_mod_cast h₂.symm.trans ((congrFun h 1).trans h₁)

end RatSign

namespace PermRep

variable {G S : Type} [Group G] [MulAction G S] [Fintype S] [DecidableEq S] {N : ℤ}

variable (G S) in
/-- Forgetting the group: `PermRep G S → PermRep 1 S`, the identity on matrices. -/
@[simps]
def forget : invCat G S ⟶ invCat Unit S where
  F :=
    { obj X := ⟨X.rank⟩
      map f := ⟨f.1, fun _ _ _ _ _ ↦ rfl⟩
      map_id _ := rfl
      map_comp _ _ := rfl }
  additive := ⟨rfl⟩
  map_star _ := rfl

lemma toLin_eqToHom_map_forget (P : SymPoincare (inv G S) N) {a b : ℤ} (h : a = b)
    (v : ((dualComplex (inv G S) N P.C).X a).Sp) :
    toLin (eqToHom (congrArg (dualComplex (inv Unit S) N (P.map (forget G S)).C).X h)) v =
      toLin (eqToHom (congrArg (dualComplex (inv G S) N P.C).X h)) v := by
  subst h
  simp
  erw [toLin_id]

/-- Forgetting the group is the identity on `H^m(C, p)`. -/
def middleForget (P : SymPoincare (inv G S) N) (m : ℤ) :
    (P.map (forget G S)).middle m ≃ₗ[ℚ] P.middle m :=
  LinearEquiv.refl ℚ (P.middle m)

lemma middleForm_middleForget (P : SymPoincare (inv G S) N) (m : ℤ) (hm : m = N - m)
    (u v : (P.map (forget G S)).middle m) :
    P.middleForm m hm (middleForget P m u) (middleForget P m v) =
      (P.map (forget G S)).middleForm m hm u v := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  change pairing m hm P.φ x.1 y.1 = pairing m hm (P.map (forget G S)).φ x.1 y.1
  erw [pairing_apply, pairing_apply, toLin_eqToHom_map_forget P hm]
  rfl

variable [Finite G]

/-- Forgetting the group does not change the signature at `1` (no factor `1 / |G|`). -/
theorem sign_map_forget_one (m : ℤ) (hm : m = N - m) (he : Even m)
    (P : SymPoincare (inv G S) N) : (P.map (forget G S)).sign m hm 1 = P.sign m hm 1 := by
  rw [SymPoincare.sign_one _ m hm he]
  erw [SymPoincare.sign_one _ m hm he]
  have h₁ := P.isInvariantForm_middleForm m hm he
  have h₂ := (P.map (forget G S)).isInvariantForm_middleForm m hm he
  exact congrArg _ (ratSignature_congr h₂.isSymm h₂.nondegenerate h₁.isSymm h₁.nondegenerate
    (middleForget P m) (middleForm_middleForget P m hm)).symm

/-- `Sign_G` descends to the concrete L-group (manuscript (3.1) on `L_N`, issue I5). -/
def signHom (m : ℤ) (hm : m = N - m) (he : Even m) : Lconc (invCat G S) N →+ (G → ℂ) :=
  Lconc.lift (fun P ↦ SymPoincare.sign P m hm) (fun P Q _ ↦ P.sign_sum Q m hm _ he)
    fun _ hP ↦ SymPoincare.sign_eq_zero_of_nullCobordant m hm hP he

@[simp]
lemma signHom_cls (m : ℤ) (hm : m = N - m) (he : Even m) (P : SymPoincare (invCat G S).inv N) :
    signHom m hm he (Lconc.cls P) = P.sign m hm :=
  Lconc.lift_cls _ _ _ P

/-- The value at `1` is the ordinary signature of the middle form. -/
theorem signHom_cls_one (m : ℤ) (hm : m = N - m) (he : Even m)
    (P : SymPoincare (invCat G S).inv N) :
    signHom m hm he (Lconc.cls P) 1 = ratSignature (P.middleForm m hm) := by
  rw [signHom_cls, P.sign_one m hm he]

/-- Naturality at `1` under forgetting the group: `Sign_1(U_* α)(1) = Sign_G(α)(1)`. -/
theorem signHom_map_forget_one (m : ℤ) (hm : m = N - m) (he : Even m)
    (x : Lconc (invCat G S) N) :
    signHom m hm he (Lconc.map (forget G S) x) 1 = signHom m hm he x 1 := by
  obtain ⟨P, rfl⟩ := Lconc.cls_surjective x
  rw [Lconc.map_cls, signHom_cls, signHom_cls]
  exact sign_map_forget_one m hm he P

/-- `Sign_G` on `L_4`, read off `H^2` (manuscript (3.1)). -/
abbrev sign₄Hom : Lconc (invCat G S) 4 →+ (G → ℂ) :=
  signHom 2 (by norm_num) even_two

end PermRep

end

end HSFormal.LTheory
