import HSFormal.LTheory.SignatureCobordism
import HSFormal.LTheory.PointCategory
import HSFormal.TailGroups

/-!
# The tail signature (L-theory module M10)

Manuscript §3, (3.3)–(3.5), and the signature step of Theorem 6.3.

* `PermRep.TensorData`: `ℚ[Q] ⊗ −` from `PermRep G S` to `PermRep G S'` along equivariant bases
  `Fin (r n) × S' ≃ Q × (Fin n × S)` (diagonal action); `TensorData.sign_map`:
  `Sign_G(ℚ[Q] ⊗ P) = Sign_G(P) · χ_Q`, from `H^m(ℚ[Q] ⊗ C) ≅ H^m(C) ⊗ ℚ[Q]` (`toTensor`), an
  equivariant isometry onto `b ⊗ (orthonormal form)`, and `ratEquivariantSignature_tprod`.
  `TensorData.free` is the tensor basis of `AsymptoticObject.tensorCoord`, `TensorData.flatten`
  the reindexing `ℚ^{n × S} = ℚ^{n |S|}` of `forgetCoord`.
* `PermRep.sigHom`: the integer signature on `Lconc`, the value of `signHom` at `1`
  (`signHom_apply_one`); `prime_dvd_sigHom` (Lemma 3.1) and
  `prime_dvd_sigHom_of_nu_pow_eq_zero` (Theorem 6.3 at one index).
* `FreeQG.factor`, `FreeQG.factorFS`: the `i`-th factor of `∏ⱼ Free(ℚ[Gⱼ])`, and
  `finSuppFreeQG G {i}`, as `PermRep.invCat (G i) (G i)` (strict functors).  `FreeQG.tensorQG`:
  `τ ⊗ −` index by index, `IsIndexwise`, lifting `AsymptoticCategory.tensorInv`
  (`toPoint_tensorInv`, a strict square).  Forgetting the group is `PermRep.forget` and
  `flatten` at each index (`restrict_forgetQG_factorFS`).
* `LowerLTheory.SignTail : L_4(V_G) →+ Tail (fun i ↦ G i → ℂ)` and
  `LowerLTheory.σtail : L_4(V_G) →+ Filter.Germ atTop ℤ` through `LowerLTheory.tail`;
  `SignTail_tensor`, `σtail_forget` (no factor `1 / |Gᵢ|`), `SignTail_one`, the relation (6.3)
  `eventually_nu_pow_coord_eq_zero`, and Theorem 6.3 at this level, `σtail_liftPred_dvd`
  (`σtail_liftPred_dvd_of_fixedData` for the groups of §7).
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression Filter
open LinearMap (BilinForm)
open scoped Matrix Kronecker TensorProduct

noncomputable section

namespace InvFunctor

variable {V W : Type*} [Category V] [Preadditive V] [Category W] [Preadditive W]
  {J : StrictInvolution V} {J' : StrictInvolution W} (Φ : InvFunctor J J') {N : ℤ}

lemma dualComplex_mapC_d (C : ChainComplex V ℤ) (r r' : ℤ) :
    (dualComplex J' N (Φ.mapC C)).d r r' = Φ.F.map ((dualComplex J N C).d r r') := by
  simp [Φ.map_star]

lemma dualHom_mapH_f {C D : ChainComplex V ℤ} (f : C ⟶ D) (r : ℤ) :
    (dualHom J' N (Φ.mapH f)).f r = Φ.F.map ((dualHom J N f).f r) := by
  simp [Φ.map_star]

end InvFunctor

namespace PermRep

/-- `ℚ[Q] ⊗ −` from `PermRep G S` to `PermRep G S'`: ranks `r n` and `G`-equivariant
identifications `Fin (r n) × S' ≃ Q × (Fin n × S)` of the bases (diagonal action on the right). -/
structure TensorData (G S S' Q : Type) [Group G] [MulAction G S] [MulAction G S']
    [MulAction G Q] where
  r : ℕ → ℕ
  e : ∀ n, Fin (r n) × S' ≃ Q × (Fin n × S)
  e_smul : ∀ n (g : G) (k : Fin (r n)) (s : S'),
    e n (k, g • s) = (g • (e n (k, s)).1, (e n (k, s)).2.1, g • (e n (k, s)).2.2)

section PermChar

variable (G Q : Type) [Group G] [MulAction G Q] [Fintype Q]

/-- The permutation character `g ↦ tr(g | ℚ[Q])`. -/
def permChar (g : G) : ℂ :=
  (LinearMap.trace ℚ (MonoidAlgebra ℚ Q) (Representation.ofMulAction ℚ G Q g) : ℂ)

variable {G Q}

lemma permChar_eq_zero {g : G} (h : ∀ q : Q, g • q ≠ q) : permChar G Q g = 0 := by
  classical
  simp [permChar, trace_ofMulAction, h]

end PermChar

lemma permChar_unit : permChar Unit Unit = 1 := by
  funext g
  simp [permChar, trace_ofMulAction]

namespace TensorData

variable {G S S' Q : Type} [Group G] [MulAction G S] [MulAction G S'] [MulAction G Q]
  (D : TensorData G S S' Q)

lemma e_symm_smul (n : ℕ) (g : G) (a : Q × (Fin n × S)) :
    (D.e n).symm (g • a.1, a.2.1, g • a.2.2) =
      (((D.e n).symm a).1, g • ((D.e n).symm a).2) := by
  rw [Equiv.symm_apply_eq, D.e_smul, Prod.mk.eta, Equiv.apply_symm_apply]

variable [DecidableEq Q]

/-- The matrix `1_{ℚ[Q]} ⊗ f` in the bases `e`. -/
def mat {m n : ℕ} (f : Matrix (Fin n × S) (Fin m × S) ℚ) :
    Matrix (Fin (D.r n) × S') (Fin (D.r m) × S') ℚ :=
  ((1 : Matrix Q Q ℚ) ⊗ₖ f).submatrix (D.e n) (D.e m)

lemma mat_apply {m n : ℕ} (f : Matrix (Fin n × S) (Fin m × S) ℚ) (b' : Fin (D.r n) × S')
    (b : Fin (D.r m) × S') :
    D.mat f b' b = if (D.e n b').1 = (D.e m b).1 then f (D.e n b').2 (D.e m b).2 else 0 := by
  simp [mat, Matrix.one_apply]

lemma mat_transpose {m n : ℕ} (f : Matrix (Fin n × S) (Fin m × S) ℚ) :
    D.mat fᵀ = (D.mat f)ᵀ := by
  simp only [mat, Matrix.transpose_submatrix, ← Matrix.kroneckerMap_transpose,
    Matrix.transpose_one]

lemma mat_add {m n : ℕ} (f g : Matrix (Fin n × S) (Fin m × S) ℚ) :
    D.mat (f + g) = D.mat f + D.mat g := by
  ext
  simp only [Matrix.add_apply, mat_apply]
  split_ifs <;> simp

lemma mat_zero {m n : ℕ} : D.mat (0 : Matrix (Fin n × S) (Fin m × S) ℚ) = 0 := by
  ext
  simp [mat_apply]

variable [Fintype S] [Fintype S'] [Fintype Q]

lemma mat_mul {l m n : ℕ} (f : Matrix (Fin m × S) (Fin l × S) ℚ)
    (g : Matrix (Fin n × S) (Fin m × S) ℚ) : D.mat (g * f) = D.mat g * D.mat f := by
  simp only [mat, Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul, one_mul]

variable [DecidableEq S] [DecidableEq S']

omit [Fintype S] [Fintype S'] [Fintype Q] in
lemma mat_one (n : ℕ) : D.mat (1 : Matrix (Fin n × S) (Fin n × S) ℚ) = 1 := by
  simp only [mat, Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]

omit [Fintype S'] [Fintype Q] [DecidableEq S'] in
lemma mat_mem {X Y : PermRep G S} (f : X ⟶ Y) :
    D.mat f.1 ∈ homSubmodule (⟨D.r X.rank⟩ : PermRep G S') ⟨D.r Y.rank⟩ := by
  intro g i s j t
  rw [mat_apply, mat_apply, D.e_smul, D.e_smul]
  simp only [smul_left_cancel_iff]
  split_ifs
  exacts [f.2 g _ _ _ _, rfl]

/-- `ℚ[Q] ⊗ −`, a strictly duality-preserving functor. -/
@[reducible] def functor : invCat G S ⟶ invCat G S' where
  F :=
    { obj X := ⟨D.r X.rank⟩
      map f := ⟨D.mat f.1, D.mat_mem f⟩
      map_id X := hom_ext (D.mat_one X.rank)
      map_comp f g := hom_ext (D.mat_mul f.1 g.1) }
  additive := ⟨fun {_ _ f g} ↦ hom_ext (D.mat_add f.1 g.1)⟩
  map_star f := hom_ext (D.mat_transpose f.1)

@[simp] lemma functor_obj (X : PermRep G S) : (D.functor.F.obj X).rank = D.r X.rank := rfl

@[simp] lemma functor_map_val {X Y : PermRep G S} (f : X ⟶ Y) :
    (D.functor.F.map f).1 = D.mat f.1 := rfl

/-! ### The summands `e_q ⊗ X` -/

/-- `v ↦ e_q ⊗ v`. -/
def inj (X : PermRep G S) (q : Q) : X.Sp →ₗ[ℚ] (D.functor.F.obj X).Sp where
  toFun v b := if (D.e X.rank b).1 = q then v (D.e X.rank b).2 else 0
  map_add' v w := funext fun b ↦ by by_cases h : (D.e X.rank b).1 = q <;> simp [h]
  map_smul' c v := funext fun b ↦ by by_cases h : (D.e X.rank b).1 = q <;> simp [h]

/-- The component of `e_q`. -/
def proj (X : PermRep G S) (q : Q) : (D.functor.F.obj X).Sp →ₗ[ℚ] X.Sp :=
  LinearMap.funLeft ℚ ℚ fun a ↦ (D.e X.rank).symm (q, a)

lemma inj_apply (X : PermRep G S) (q : Q) (v : X.Sp) (b) :
    D.inj X q v b = if (D.e X.rank b).1 = q then v (D.e X.rank b).2 else 0 := rfl

lemma proj_apply (X : PermRep G S) (q : Q) (w : (D.functor.F.obj X).Sp) (a) :
    D.proj X q w a = w ((D.e X.rank).symm (q, a)) := rfl

lemma inj_symm_apply (X : PermRep G S) (q q' : Q) (v : X.Sp) (a) :
    D.inj X q v ((D.e X.rank).symm (q', a)) = if q' = q then v a else 0 := by
  rw [inj_apply, Equiv.apply_symm_apply]

lemma sum_e (X : PermRep G S) (φ : (D.functor.F.obj X).Idx → ℚ) :
    ∑ b, φ b = ∑ q, ∑ a, φ ((D.e X.rank).symm (q, a)) := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (D.e X.rank) _ _ fun b ↦ by simp

lemma toLin_map_inj {X Y : PermRep G S} (f : X ⟶ Y) (q : Q) (v : X.Sp) :
    toLin (D.functor.F.map f) (D.inj X q v) = D.inj Y q (toLin f v) := by
  funext b'
  simp only [toLin_apply, Matrix.mulVec, dotProduct, functor_map_val]
  erw [sum_e]
  simp only [Equiv.apply_symm_apply, mat_apply]
  rw [Finset.sum_eq_single (D.e Y.rank b').1 (fun q' _ h ↦ Finset.sum_eq_zero fun a _ ↦ by
    rw [ite_eq_right (Ne.symm h), zero_mul]) (by simp)]
  rw [inj_apply]
  split_ifs with h₁ h₂
  · show _ = ∑ a, (f.1 : Matrix _ _ ℚ) (D.e Y.rank b').2 a * v a
    exact Finset.sum_congr rfl fun a _ ↦ by rw [inj_symm_apply, if_pos h₂]
  · exact Finset.sum_eq_zero fun a _ ↦ by rw [inj_symm_apply, if_neg h₂, mul_zero]
  · exact absurd rfl h₁
  · exact absurd rfl h₁

lemma proj_toLin_map {X Y : PermRep G S} (f : X ⟶ Y) (q : Q) (w : (D.functor.F.obj X).Sp) :
    D.proj Y q (toLin (D.functor.F.map f) w) = toLin f (D.proj X q w) := by
  funext a'
  rw [proj_apply]
  simp only [toLin_apply, Matrix.mulVec, dotProduct, functor_map_val]
  erw [sum_e]
  simp only [Equiv.apply_symm_apply, mat_apply]
  rw [Finset.sum_eq_single q (fun q' _ h ↦ Finset.sum_eq_zero fun a _ ↦ by
    rw [ite_eq_right (Ne.symm h), zero_mul]) (by simp)]
  simp
  rfl

lemma proj_inj (X : PermRep G S) (q q' : Q) (v : X.Sp) :
    D.proj X q (D.inj X q' v) = if q = q' then v else 0 := by
  funext a
  rw [proj_apply, inj_symm_apply]
  split_ifs <;> rfl

lemma dotProduct_eq_sum (X : PermRep G S) (w w' : (D.functor.F.obj X).Sp) :
    w ⬝ᵥ w' = ∑ q, D.proj X q w ⬝ᵥ D.proj X q w' := by
  simp only [dotProduct, proj_apply]
  exact sum_e D X _

lemma proj_act (X : PermRep G S) (g : G) (q : Q) (w : (D.functor.F.obj X).Sp) :
    D.proj X (g • q) ((D.functor.F.obj X).act g w) = X.act g (D.proj X q w) := by
  funext ⟨j, s⟩
  rw [proj_apply, act_apply, act_apply, proj_apply]
  congr 1
  have := D.e_symm_smul X.rank g⁻¹ (g • q, j, s)
  simp only [inv_smul_smul] at this
  rw [this]

/-! ### `H^m(ℚ[Q] ⊗ C) = ℚ[Q] ⊗ H^m(C)` -/

variable {N : ℤ} (m : ℤ)

lemma toLin_dual_d_inj (C : ChainComplex (PermRep G S) ℤ) (r r' : ℤ) (q : Q)
    (v : ((dualComplex (inv G S) N C).X r).Sp) :
    toLin ((dualComplex (inv G S') N (D.functor.mapC C)).d r r')
      (D.inj ((dualComplex (inv G S) N C).X r) q v) =
      D.inj ((dualComplex (inv G S) N C).X r') q
        (toLin ((dualComplex (inv G S) N C).d r r') v) := by
  erw [InvFunctor.dualComplex_mapC_d]
  exact D.toLin_map_inj _ q v

lemma proj_toLin_dual_d (C : ChainComplex (PermRep G S) ℤ) (r r' : ℤ) (q : Q)
    (w : ((dualComplex (inv G S') N (D.functor.mapC C)).X r).Sp) :
    D.proj ((dualComplex (inv G S) N C).X r') q
      (toLin ((dualComplex (inv G S') N (D.functor.mapC C)).d r r') w) =
      toLin ((dualComplex (inv G S) N C).d r r')
        (D.proj ((dualComplex (inv G S) N C).X r) q w) := by
  erw [InvFunctor.dualComplex_mapC_d]
  exact D.proj_toLin_map _ q w

lemma toLin_dualHom_inj {C : ChainComplex (PermRep G S) ℤ} (p : C ⟶ C) (r : ℤ) (q : Q)
    (v : ((dualComplex (inv G S) N C).X r).Sp) :
    toLin ((dualHom (inv G S') N (D.functor.mapH p)).f r)
      (D.inj ((dualComplex (inv G S) N C).X r) q v) =
      D.inj ((dualComplex (inv G S) N C).X r) q (toLin ((dualHom (inv G S) N p).f r) v) := by
  erw [InvFunctor.dualHom_mapH_f]
  exact D.toLin_map_inj _ q v

lemma proj_toLin_dualHom {C : ChainComplex (PermRep G S) ℤ} (p : C ⟶ C) (r : ℤ) (q : Q)
    (w : ((dualComplex (inv G S') N (D.functor.mapC C)).X r).Sp) :
    D.proj ((dualComplex (inv G S) N C).X r) q
      (toLin ((dualHom (inv G S') N (D.functor.mapH p)).f r) w) =
      toLin ((dualHom (inv G S) N p).f r) (D.proj ((dualComplex (inv G S) N C).X r) q w) := by
  erw [InvFunctor.dualHom_mapH_f]
  exact D.proj_toLin_map _ q w

variable {C : ChainComplex (PermRep G S) ℤ} (p : C ⟶ C)

lemma inj_mem_cycles (q : Q) {v : ((dualComplex (inv G S) N C).X m).Sp}
    (hv : v ∈ cycles (dualComplex (inv G S) N C) m) :
    D.inj ((dualComplex (inv G S) N C).X m) q v ∈
      cycles (dualComplex (inv G S') N (D.functor.mapC C)) m := by
  rw [cycles, LinearMap.mem_ker] at hv ⊢
  exact (D.toLin_dual_d_inj _ m (m - 1) q v).trans (by rw [hv, map_zero])

lemma proj_mem_cycles (q : Q) {w : ((dualComplex (inv G S') N (D.functor.mapC C)).X m).Sp}
    (hw : w ∈ cycles (dualComplex (inv G S') N (D.functor.mapC C)) m) :
    D.proj ((dualComplex (inv G S) N C).X m) q w ∈ cycles (dualComplex (inv G S) N C) m := by
  rw [cycles, LinearMap.mem_ker] at hw ⊢
  exact (D.proj_toLin_dual_d _ m (m - 1) q w).symm.trans (by rw [hw, map_zero])

lemma inj_mem_karBoundaries (q : Q) {v : ((dualComplex (inv G S) N C).X m).Sp}
    (hv : v ∈ karBoundaries (dualComplex (inv G S) N C) (dualHom (inv G S) N p) m) :
    D.inj ((dualComplex (inv G S) N C).X m) q v ∈
      karBoundaries (dualComplex (inv G S') N (D.functor.mapC C))
        (dualHom (inv G S') N (D.functor.mapH p)) m := by
  obtain ⟨_, ⟨w, rfl⟩, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add]
  refine Submodule.add_mem_sup ⟨_, D.toLin_dual_d_inj _ (m + 1) m q w⟩ ?_
  rw [LinearMap.mem_ker] at hz ⊢
  exact (D.toLin_dualHom_inj p m q z).trans (by rw [hz, map_zero])

lemma proj_mem_karBoundaries (q : Q)
    {w : ((dualComplex (inv G S') N (D.functor.mapC C)).X m).Sp}
    (hw : w ∈ karBoundaries (dualComplex (inv G S') N (D.functor.mapC C))
      (dualHom (inv G S') N (D.functor.mapH p)) m) :
    D.proj ((dualComplex (inv G S) N C).X m) q w ∈
      karBoundaries (dualComplex (inv G S) N C) (dualHom (inv G S) N p) m := by
  obtain ⟨_, ⟨x, rfl⟩, z, hz, rfl⟩ := Submodule.mem_sup.mp hw
  rw [map_add]
  refine Submodule.add_mem_sup ⟨_, (D.proj_toLin_dual_d _ (m + 1) m q x).symm⟩ ?_
  rw [LinearMap.mem_ker] at hz ⊢
  exact (D.proj_toLin_dualHom p m q z).symm.trans (by rw [hz, map_zero])

variable (P : SymPoincare (inv G S) N)

/-- `x ↦ e_q ⊗ x` on `H^m(C, p)`. -/
def middleInj (q : Q) : P.middle m →ₗ[ℚ] (P.map D.functor).middle m :=
  Submodule.mapQ _ _ ((D.inj _ q).restrict fun _ ↦ D.inj_mem_cycles m q)
    fun _ hv ↦ D.inj_mem_karBoundaries m P.p q hv

/-- The component of `e_q` on `H^m(ℚ[Q] ⊗ C, p)`. -/
def middleProj (q : Q) : (P.map D.functor).middle m →ₗ[ℚ] P.middle m :=
  Submodule.mapQ _ _ ((D.proj _ q).restrict fun _ ↦ D.proj_mem_cycles m q)
    fun _ hw ↦ D.proj_mem_karBoundaries m P.p q hw

lemma toLin_eqToHom_mapC (C : ChainComplex (PermRep G S) ℤ) {a b : ℤ} (h : a = b)
    (w : ((dualComplex (inv G S') N (D.functor.mapC C)).X a).Sp) :
    toLin (eqToHom (congrArg (dualComplex (inv G S') N (D.functor.mapC C)).X h)) w =
      toLin (D.functor.F.map (eqToHom (congrArg (dualComplex (inv G S) N C).X h))) w := by
  subst h
  simp only [eqToHom_refl]
  exact congrArg (fun f ↦ toLin f w) (D.functor.F.map_id _).symm

lemma pairing_map (hm : m = N - m) (x y : ((P.map D.functor).C.X (N - m)).Sp) :
    pairing m hm (P.map D.functor).φ x y =
      ∑ q, pairing m hm P.φ (D.proj (P.C.X (N - m)) q x) (D.proj (P.C.X (N - m)) q y) := by
  erw [pairing_apply, D.dotProduct_eq_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [pairing_apply]
  congr 1
  exact (congrArg (fun z ↦ D.proj _ q (toLin (D.functor.F.map (P.φ.f (N - m))) z))
    (D.toLin_eqToHom_mapC P.C hm y)).trans
      ((D.proj_toLin_map _ q _).trans (congrArg _ (D.proj_toLin_map _ q y)))

lemma middleForm_map (hm : m = N - m) (u v : (P.map D.functor).middle m) :
    (P.map D.functor).middleForm m hm u v =
      ∑ q, P.middleForm m hm (D.middleProj m P q u) (D.middleProj m P q v) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  exact D.pairing_map m P hm x.1 y.1

lemma middleProj_middleInj (q q' : Q) (u : P.middle m) :
    D.middleProj m P q (D.middleInj m P q' u) = if q = q' then u else 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  split_ifs with h
  · subst h
    exact congrArg Submodule.Quotient.mk (Subtype.ext ((D.proj_inj _ q q x.1).trans (ite_eq_left rfl)))
  · exact (congrArg Submodule.Quotient.mk (Subtype.ext ((D.proj_inj _ q q' x.1).trans
      (ite_eq_right h)))).trans (Submodule.Quotient.mk_zero _)

lemma middleProj_middleRep (g : G) (q : Q) (u : (P.map D.functor).middle m) :
    D.middleProj m P (g • q) ((P.map D.functor).middleRep m g u) =
      P.middleRep m g (D.middleProj m P q u) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  exact congrArg Submodule.Quotient.mk (Subtype.ext (D.proj_act _ g q x.1))

/-- `H^m(ℚ[Q] ⊗ C, p) → H^m(C, p) ⊗ ℚ[Q]`, `x ↦ ∑_q x_q ⊗ e_q`. -/
def toTensor : (P.map D.functor).middle m →ₗ[ℚ] P.middle m ⊗[ℚ] MonoidAlgebra ℚ Q :=
  ∑ q, (TensorProduct.mk ℚ _ _).flip (MonoidAlgebra.single q 1) ∘ₗ D.middleProj m P q

lemma toTensor_apply (u : (P.map D.functor).middle m) :
    D.toTensor m P u = ∑ q, D.middleProj m P q u ⊗ₜ MonoidAlgebra.single q 1 := by
  simp [toTensor]

lemma toTensor_middleInj (q : Q) (u : P.middle m) :
    D.toTensor m P (D.middleInj m P q u) = u ⊗ₜ MonoidAlgebra.single q 1 := by
  rw [toTensor_apply, Finset.sum_eq_single q (fun q' _ h ↦ by
    rw [middleProj_middleInj, ite_eq_right h, TensorProduct.zero_tmul]) (by simp),
    middleProj_middleInj, ite_eq_left rfl]

lemma toTensor_isometry (hm : m = N - m) (u v : (P.map D.functor).middle m) :
    (P.middleForm m hm).tmul (permForm ℚ Q) (D.toTensor m P u) (D.toTensor m P v) =
      (P.map D.functor).middleForm m hm u v := by
  rw [middleForm_map, toTensor_apply, toTensor_apply]
  simp only [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [Finset.sum_eq_single q (fun q' _ h ↦ by
    simp [MonoidAlgebra.coeff_single, Finsupp.single_apply, h]) (by simp)]
  simp [MonoidAlgebra.coeff_single, Finsupp.single_apply]

lemma toTensor_middleRep (g : G) (u : (P.map D.functor).middle m) :
    D.toTensor m P ((P.map D.functor).middleRep m g u) =
      ((P.middleRep m).tprod (Representation.ofMulAction ℚ G Q)) g (D.toTensor m P u) := by
  rw [toTensor_apply, toTensor_apply, map_sum, ← Equiv.sum_comp (MulAction.toPerm g)]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [MulAction.toPerm_apply, middleProj_middleRep, Representation.tprod_apply,
    TensorProduct.map_tmul, Representation.ofMulAction_single]

lemma toTensor_bijective (hm : m = N - m) : Function.Bijective (D.toTensor m P) := by
  refine ⟨injective_of_isometry ((P.map D.functor).middleForm_nondegenerate m hm).1
    (D.toTensor_isometry m P hm), LinearMap.range_eq_top.mp (eq_top_iff.mpr
      ((TensorProduct.span_tmul_eq_top ℚ _ _).symm.le.trans (Submodule.span_le.mpr ?_)))⟩
  rintro _ ⟨u, w, rfl⟩
  induction w using MonoidAlgebra.induction_linear with
  | zero => simp
  | add w w' hw hw' => rw [TensorProduct.tmul_add]; exact add_mem hw hw'
  | single q a =>
    refine ⟨a • D.middleInj m P q u, ?_⟩
    rw [map_smul, toTensor_middleInj, ← TensorProduct.tmul_smul, MonoidAlgebra.smul_single',
      mul_one]

/-- **Tensoring with a permutation module multiplies `Sign_G` by its character**
(manuscript (6.3), "taking equivariant signatures"). -/
theorem sign_map [Finite G] (hm : m = N - m) (he : Even m) (g : G) :
    (P.map D.functor).sign m hm g =
      P.sign m hm g * (LinearMap.trace ℚ (MonoidAlgebra ℚ Q) (Representation.ofMulAction ℚ G Q g) :
        ℂ) := by
  have hb := P.isInvariantForm_middleForm m hm he
  rw [SymPoincare.sign, SymPoincare.sign, ← ratEquivariantSignature_tprod hb permForm_isSymm
    permForm_pos g, ← ratEquivariantSignature_congr
      ((P.map D.functor).isInvariantForm_middleForm m hm he)
      (LinearEquiv.ofBijective _ (D.toTensor_bijective m P hm)) (D.toTensor_middleRep m P)
      (D.toTensor_isometry m P hm)]

variable [Finite G]

/-- `Sign_G(ℚ[Q] ⊗ x) = χ_Q · Sign_G(x)` on `L_N`. -/
theorem signHom_map (hm : m = N - m) (he : Even m) (x : Lconc (invCat G S) N) :
    signHom m hm he (Lconc.map D.functor x) = permChar G Q * signHom m hm he x := by
  obtain ⟨P, rfl⟩ := Lconc.cls_surjective x
  rw [Lconc.map_cls, signHom_cls, signHom_cls]
  funext g
  rw [Pi.mul_apply, mul_comm]
  exact D.sign_map m P hm he g

end TensorData

/-- The data of `ℚ[Q] ⊗ −` on `Free(ℚ[G])`, `G` acting diagonally: the orbit `(k, q)` of
`ℚ[Q] ⊗ ℚ[G]^n` is `Fin (n |Q|)` (`tensorIdx`) and `g • (e_q ⊗ m_k) = e_{g q} ⊗ m_{(k, g)}`, as for
`AsymptoticObject.tensorCoord`. -/
def TensorData.free (G Q : Type) [Group G] [MulAction G Q] [Fintype Q] :
    TensorData G G G Q where
  r n := n * Fintype.card Q
  e n :=
    { toFun b := (b.2 • ((tensorIdx Q n).symm b.1).2, ((tensorIdx Q n).symm b.1).1, b.2)
      invFun a := (tensorIdx Q n (a.2.1, a.2.2⁻¹ • a.1), a.2.2)
      left_inv b := by simp
      right_inv a := by simp }
  e_smul n g k s := by simp [mul_smul]

/-- The reindexing `ℚ^{n} ⊗ ℚ^S = ℚ^{n |S|}` behind forgetting the group (`forgetCoord`). -/
def TensorData.flatten (S : Type) [Fintype S] : TensorData Unit S Unit Unit where
  r n := n * Fintype.card S
  e n := (Equiv.prodPUnit _).trans ((tensorIdx S n).symm.trans (Equiv.punitProd _).symm)
  e_smul _ _ _ _ := rfl

variable {G S : Type} [Group G] [MulAction G S] [Fintype S] [DecidableEq S] {N : ℤ}

/-- `ℚ^S` with trivial action, reindexed as `ℚ^{|S|}`, has the same `Sign`. -/
theorem signHom_map_flatten (m : ℤ) (hm : m = N - m) (he : Even m)
    (x : Lconc (invCat Unit S) N) :
    signHom m hm he (Lconc.map (TensorData.flatten S).functor x) = signHom m hm he x := by
  rw [TensorData.signHom_map _ m hm he, permChar_unit, one_mul]

variable [Finite G]

/-- The ordinary signature `σ(H^m(C, p))` on `L_N`, `N = 2m`, `m` even. -/
def sigHom (m : ℤ) (hm : m = N - m) (he : Even m) : Lconc (invCat G S) N →+ ℤ :=
  Lconc.lift (fun P ↦ ratSignature (P.middleForm m hm))
    (fun P Q b ↦ Int.cast_injective (α := ℂ) <| by
      push_cast
      erw [← P.sign_one m hm he, ← Q.sign_one m hm he, ← SymPoincare.sign_one _ m hm he,
        P.sign_sum Q m hm _ he]
      rfl)
    fun P hP ↦ Int.cast_injective (α := ℂ) <| by
      rw [Int.cast_zero, ← P.sign_one m hm he, SymPoincare.sign_eq_zero_of_nullCobordant m hm hP he]
      rfl

@[simp]
lemma sigHom_cls (m : ℤ) (hm : m = N - m) (he : Even m) (P : SymPoincare (invCat G S).inv N) :
    sigHom m hm he (Lconc.cls P) = ratSignature (P.middleForm m hm) :=
  Lconc.lift_cls _ _ _ P

lemma signHom_apply_one (m : ℤ) (hm : m = N - m) (he : Even m) (x : Lconc (invCat G S) N) :
    signHom m hm he x 1 = sigHom m hm he x := by
  obtain ⟨P, rfl⟩ := Lconc.cls_surjective x
  rw [signHom_cls_one, sigHom_cls]

lemma sigHom_map_forget (m : ℤ) (hm : m = N - m) (he : Even m) (x : Lconc (invCat G S) N) :
    sigHom m hm he (Lconc.map (forget G S) x) = sigHom m hm he x := by
  apply Int.cast_injective (α := ℂ)
  rw [← signHom_apply_one, ← signHom_apply_one, signHom_map_forget_one]

/-- **Lemma 3.1 on `L_N`**: for `|G| = p ^ (k + 1)`, `Sign_G(x)(g) = 0` implies `p ∣ σ(x)`. -/
theorem prime_dvd_sigHom [Fintype G] {m : ℤ} {hm : m = N - m} {he : Even m} {p k : ℕ}
    (hp : p.Prime) (hG : Fintype.card G = p ^ (k + 1)) {g : G} {x : Lconc (invCat G S) N}
    (hx : signHom m hm he x g = 0) : (p : ℤ) ∣ sigHom m hm he x := by
  obtain ⟨P, rfl⟩ := Lconc.cls_surjective x
  rw [signHom_cls] at hx
  rw [sigHom_cls]
  have hb := P.isInvariantForm_middleForm m hm he
  exact prime_dvd_ratSignature hb.isSymm hb.nondegenerate hb.map_map hp hG hx

/-- **Theorem 6.3 at one index**: if `(p - T) ^ s` kills `x` and `T` multiplies `Sign_G` by a
character vanishing at `g`, then `p ∣ σ(x)`. -/
theorem prime_dvd_sigHom_of_nu_pow_eq_zero [Fintype G] {m : ℤ} {hm : m = N - m} {he : Even m}
    {p k s : ℕ} (hp : p.Prime) (hG : Fintype.card G = p ^ (k + 1)) {g : G} {A : Type*}
    [AddCommGroup A] (f : A →+ Lconc (invCat G S) N) (T : AddMonoid.End A) (χ : G → ℂ)
    (hχ : χ g = 0) (hT : ∀ y, signHom m hm he (f (T y)) = χ * signHom m hm he (f y)) {x : A}
    (hx : (((p : AddMonoid.End A) - T) ^ s) x = 0) : (p : ℤ) ∣ sigHom m hm he (f x) := by
  have h := map_nu_pow ((signHom m hm he).comp f) T χ hT p s x
  rw [hx, map_zero] at h
  refine prime_dvd_sigHom hp hG (g := g)
    (character_vanishes_of_prime_power_annihilation p s hp (signHom m hm he (f x) g) ?_)
  simpa [hχ] using (congrFun h g).symm

end PermRep

/-! ### `∏ᵢ Free(ℚ[Gᵢ])`: factors, `τ ⊗ −` and forgetting the group -/

/-- `f ((p - T_A)^s a) = (p - T_B)^s (f a)` for `f T_A = T_B f`. -/
lemma map_nu_pow_comm {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (TA : AddMonoid.End A) (TB : AddMonoid.End B) (h : ∀ a, f (TA a) = TB (f a)) (p s : ℕ)
    (a : A) :
    f ((((p : AddMonoid.End A) - TA) ^ s) a) = (((p : AddMonoid.End B) - TB) ^ s) (f a) := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [pow_succ', pow_succ']
    change f (((p : AddMonoid.End A) - TA) ((((p : AddMonoid.End A) - TA) ^ s) a)) =
      ((p : AddMonoid.End B) - TB) ((((p : AddMonoid.End B) - TB) ^ s) (f a))
    erw [AddMonoidHom.sub_apply, AddMonoidHom.sub_apply, AddMonoid.End.natCast_apply,
      AddMonoid.End.natCast_apply, map_sub, map_nsmul, h, ih]
    rfl

lemma one_eq_one {n : Type*} [Fintype n] {d₁ d₂ : DecidableEq n} :
    @OfNat.ofNat (Matrix n n ℚ) 1 (@One.toOfNat1 _ (@Matrix.one n ℚ d₁ _ _)) =
      @OfNat.ofNat (Matrix n n ℚ) 1 (@One.toOfNat1 _ (@Matrix.one n ℚ d₂ _ _)) := by
  cases Subsingleton.elim d₁ d₂
  rfl

namespace FreeQG

open AsymptoticObject PermRep
open scoped Classical

variable {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)] [∀ i, DecidableEq (G i)]

variable (G) in
/-- **The `i`-th factor** of `∏ⱼ Free(ℚ[Gⱼ])` is `Free(ℚ[Gᵢ]) = PermRep (G i) (G i)` (the
control condition is vacuous over a point). -/
@[implicit_reducible] def factor (i : ℕ) : prodFreeQG G ⟶ PermRep.invCat (G i) (G i) where
  F :=
    { obj M := ⟨M.rank i⟩
      map f := ⟨f.1 i, fun g a s b t ↦ AsymptoticObject.equivariant f i g (a, s) (b, t)⟩
      map_id _ := PermRep.hom_ext one_eq_one
      map_comp _ _ := PermRep.hom_ext rfl }
  additive := ⟨PermRep.hom_ext rfl⟩
  map_star _ := PermRep.hom_ext rfl

variable (G) in
/-- `L^p_*(ℚ[Gᵢ])`: `finSuppFreeQG G {i}` as `Free(ℚ[Gᵢ])`, so that `sign₄Hom` applies. -/
abbrev factorFS (i : ℕ) : finSuppFreeQG G {i} ⟶ PermRep.invCat (G i) (G i) :=
  (prodFreeQG G).subIncl _ ≫ factor G i

variable (G) (Q : Type) [Fintype Q] [∀ i, MulAction (G i) Q]

/-- `τ ⊗ −` on `∏ᵢ Free(ℚ[Gᵢ])` for `τᵢ = ℚ[Q]` (manuscript (6.1)): index-wise
`TensorData.free`, on objects `AsymptoticObject.tensorObj`. -/
def tensorQG : prodFreeQG G ⟶ prodFreeQG G where
  F :=
    { obj M := M.tensorObj Q
      map {M N} f := ⟨fun i ↦ (TensorData.free (G i) Q).mat (f.1 i),
        (⟨fun i g b' b ↦ (TensorData.free (G i) Q).mat_mem ((factor G i).F.map f) g b'.1 b'.2
            b.1 b.2, tendsto_zero_of_forall_eq_zero fun _ ↦ prop_punit _ _ _⟩ :
          IsControlled (M.tensorObj Q) (N.tensorObj Q) _)⟩
      map_id _ := AsymptoticObject.hom_ext fun i ↦ (congrArg (TensorData.free (G i) Q).mat
        one_eq_one).trans (((TensorData.free (G i) Q).mat_one _).trans one_eq_one)
      map_comp _ _ := AsymptoticObject.hom_ext fun i ↦ (TensorData.free (G i) Q).mat_mul _ _ }
  additive := ⟨fun {_ _ f g} ↦ AsymptoticObject.hom_ext fun i ↦
    (TensorData.free (G i) Q).mat_add (f.1 i) (g.1 i)⟩
  map_star f := AsymptoticObject.hom_ext fun i ↦ (TensorData.free (G i) Q).mat_transpose (f.1 i)

lemma isIndexwise_tensorQG : IsIndexwise (tensorQG G Q) := fun M s ↦
  AsymptoticObject.hom_ext fun j ↦ by
    change (TensorData.free (G j) Q).mat ((idem M s).1 j) = (idem (M.tensorObj Q) s).1 j
    erw [idem_val, idem_val]
    split_ifs
    exacts [(congrArg (TensorData.free (G j) Q).mat one_eq_one).trans
      (((TensorData.free (G j) Q).mat_one _).trans one_eq_one), (TensorData.free (G j) Q).mat_zero]

lemma restrict_tensorQG_factorFS (i : ℕ) :
    (isIndexwise_tensorQG G Q).restrict {i} ≫ factorFS G i =
      factorFS G i ≫ (TensorData.free (G i) Q).functor :=
  rfl

/-- The functor `τ ⊗ −` of `TensorTriviality` on `V_G = 𝒜_G(pt)` lifts to `tensorQG`, `Gᵢ`
acting on `Q` through `ρ ∘ πᵢ` (strict square). -/
theorem toPoint_tensorInv {H : Type*} [Group H] (π : ∀ i, G i →* H) {Q : Type} [Fintype Q]
    (ρ : H →* Equiv.Perm Q) :
    letI : ∀ i, MulAction (G i) Q := fun i ↦ MulAction.compHom Q (ρ.comp (π i))
    toPoint G π ≫ (AsymptoticCategory.tensorInv ρ : asymptoticInvCat π PUnit ⟶ _) =
      tensorQG G Q ≫ toPoint G π :=
  rfl

variable {G}

/-- Forgetting the group at index `i` is `PermRep.forget` followed by `ℚ^{n × Gᵢ} = ℚ^{n |Gᵢ|}`. -/
lemma restrict_forgetQG_factorFS (i : ℕ) :
    isIndexwise_forgetQG.restrict {i} ≫ factorFS (fun _ ↦ Unit) i =
      factorFS G i ≫ PermRep.forget (G i) (G i) ≫ (TensorData.flatten (G i)).functor := by
  refine InvCat.hom_ext (CategoryTheory.Functor.ext (fun _ ↦ rfl) fun M N f ↦ ?_)
  erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
  refine PermRep.hom_ext (Matrix.ext fun b' b ↦ ?_)
  change ((f.hom.1 i).submatrix (forgetCoord N.obj i) (forgetCoord M.obj i)) b' b =
    (TensorData.flatten (G i)).mat (f.hom.1 i) b' b
  simp [TensorData.mat, TensorData.flatten, forgetCoord]
  erw [Matrix.submatrix_apply, Matrix.submatrix_apply]
  simp [Matrix.kroneckerMap_apply]
  rfl

/-! ### Signatures of the factors -/

variable (G) in
/-- `Sign_{Gᵢ}` on `L^p_4(ℚ[Gᵢ]) = Lconc (finSuppFreeQG G {i}) 4`. -/
def signAt (i : ℕ) : Lconc (finSuppFreeQG G {i}) 4 →+ (G i → ℂ) :=
  sign₄Hom.comp (Lconc.map (factorFS G i))

variable (G) in
/-- The ordinary signature on `L^p_4(ℚ[Gᵢ])`. -/
def sigAt (i : ℕ) : Lconc (finSuppFreeQG G {i}) 4 →+ ℤ :=
  (sigHom 2 (by norm_num) even_two).comp (Lconc.map (factorFS G i))

lemma signAt_apply_one (i : ℕ) (w : Lconc (finSuppFreeQG G {i}) 4) :
    signAt G i w 1 = sigAt G i w :=
  signHom_apply_one _ _ even_two _

variable (G) in
/-- **`SignTail` on `∏ᵢ L^p_4(ℚ[Gᵢ])`**, index by index; it descends to the tails as
`Tail.map (signAt G)`. -/
def signSeq : (∀ i, Lconc (finSuppFreeQG G {i}) 4) →+ ∀ i, G i → ℂ :=
  AddMonoidHom.pi fun i ↦ (signAt G i).comp (Pi.evalAddMonoidHom _ i)

lemma map_signAt_mk (w : ∀ i, Lconc (finSuppFreeQG G {i}) 4) :
    Tail.map (signAt G) (QuotientAddGroup.mk w) = QuotientAddGroup.mk (signSeq G w) :=
  rfl

/-- `Sign(τ ⊗ x) = χ_τ · Sign(x)` at each index. -/
lemma signAt_restrict_tensorQG (i : ℕ) (w : Lconc (finSuppFreeQG G {i}) 4) :
    signAt G i (Lconc.map ((isIndexwise_tensorQG G Q).restrict {i}) w) =
      permChar (G i) Q * signAt G i w := by
  rw [signAt, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ← AddMonoidHom.comp_apply
    (Lconc.map _), ← Lconc.map_comp, restrict_tensorQG_factorFS, Lconc.map_comp,
    AddMonoidHom.comp_apply]
  exact TensorData.signHom_map _ 2 _ even_two _

variable (G) in
/-- `τᵢ ⊗ −` on `L^p_4(ℚ[Gᵢ])`. -/
def tensorAt (i : ℕ) : AddMonoid.End (Lconc (finSuppFreeQG G {i}) 4) :=
  Lconc.map ((isIndexwise_tensorQG G Q).restrict {i})

/-- `σ` does not see forgetting the group (no factor `1 / |Gᵢ|`). -/
lemma sigAt_restrict_forgetQG (i : ℕ) (w : Lconc (finSuppFreeQG G {i}) 4) :
    sigAt (fun _ ↦ Unit) i (Lconc.map (isIndexwise_forgetQG.restrict {i}) w) = sigAt G i w := by
  rw [sigAt, sigAt, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ← AddMonoidHom.comp_apply
    (Lconc.map _), ← Lconc.map_comp, restrict_forgetQG_factorFS, Lconc.map_comp,
    Lconc.map_comp, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
    ← sigHom_map_forget 2 _ even_two (Lconc.map (factorFS G i) w)]
  apply Int.cast_injective (α := ℂ)
  rw [← signHom_apply_one, ← signHom_apply_one, signHom_map_flatten]

end FreeQG

namespace Tail

/-- `∏ ℤ / ⊕ ℤ = Filter.Germ atTop ℤ`, the tail group of (3.5). -/
def germEquiv : Tail (fun _ : ℕ ↦ ℤ) ≃+ Germ (atTop : Filter ℕ) ℤ :=
  (QuotientAddGroup.quotientAddEquivOfEq (AddSubgroup.ext fun _ ↦ Germ.coe_eq.symm)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (Germ.coeAddHom atTop)
      fun g ↦ Germ.inductionOn g fun f ↦ ⟨f, rfl⟩)

@[simp]
lemma germEquiv_mk (x : ℕ → ℤ) : germEquiv (QuotientAddGroup.mk x) = (x : Germ atTop ℤ) :=
  rfl

end Tail

namespace LowerLTheory

open FreeQG PermRep

variable (𝕃 : LowerLTheory) {G : ℕ → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)]
  [∀ i, DecidableEq (G i)] {H : Type*} [Group H] (π : ∀ i, G i →* H)

omit [∀ i, DecidableEq (G i)] in
/-- Every class of `L_4(V_G)` lifts to `L_4(∏ᵢ Free(ℚ[Gᵢ]))`. -/
lemma toPoint_surjective₄ : Function.Surjective (𝕃.map (toPoint G π) 4) :=
  𝕃.toPoint_surjective π (n := 3) (by norm_num)

/-- **`SignTail`** (Prop. 3.2, (3.5)): `L_4(V_G) → ∏ᵢ ℂ^{Gᵢ} / ⊕ᵢ ℂ^{Gᵢ}`, the equivariant
signatures of the forms extracted at the indices. -/
def SignTail : 𝕃.L (asymptoticInvCat π PUnit) 4 →+ Tail fun i ↦ G i → ℂ :=
  (Tail.map (signAt G)).comp (𝕃.tail π (n := 3) (by norm_num))

/-- **`σ_tail`** (3.5): `L_4(V_G) → ℤ^ℕ / ℤ^(ℕ) = Filter.Germ atTop ℤ`. -/
def σtail : 𝕃.L (asymptoticInvCat π PUnit) 4 →+ Germ (atTop : Filter ℕ) ℤ :=
  Tail.germEquiv.toAddMonoidHom.comp
    ((Tail.map (sigAt G)).comp (𝕃.tail π (n := 3) (by norm_num)))

lemma SignTail_toPoint (y : 𝕃.L (prodFreeQG G) 4) :
    𝕃.SignTail π (𝕃.map (toPoint G π) 4 y) =
      QuotientAddGroup.mk fun i ↦ signAt G i (𝕃.coord (by norm_num) y i) :=
  congrArg (Tail.map (signAt G)) (𝕃.tail_toPoint π (n := 3) (by norm_num) y)

lemma σtail_toPoint (y : 𝕃.L (prodFreeQG G) 4) :
    𝕃.σtail π (𝕃.map (toPoint G π) 4 y) =
      ((fun i ↦ sigAt G i (𝕃.coord (by norm_num) y i) : ℕ → ℤ) : Germ atTop ℤ) :=
  congrArg (Tail.germEquiv.toAddMonoidHom.comp (Tail.map (sigAt G)))
    (𝕃.tail_toPoint π (n := 3) (by norm_num) y)

/-- `σ_tail` is the value of `SignTail` at `1`. -/
theorem SignTail_one (x : 𝕃.L (asymptoticInvCat π PUnit) 4) :
    Tail.map (fun i ↦ Pi.evalAddMonoidHom (fun _ : G i ↦ ℂ) 1) (𝕃.SignTail π x) =
      Tail.map (fun _ ↦ Int.castAddHom ℂ) (Tail.germEquiv.symm (𝕃.σtail π x)) := by
  obtain ⟨y, rfl⟩ := 𝕃.toPoint_surjective₄ π x
  rw [SignTail_toPoint, σtail_toPoint, ← Tail.germEquiv_mk, AddEquiv.symm_apply_apply,
    Tail.map_mk, Tail.map_mk]
  simp [signAt_apply_one]

/-- **`SignTail_tensor`**: for a functor `Ψ` on `V_G` lifting to `τ ⊗ −` on `∏ᵢ Free(ℚ[Gᵢ])`
(e.g. `AsymptoticCategory.tensorInv`, `toPoint_tensorInv`), `Sign(τ ⊗ x) = χ_τ · Sign(x)`. -/
theorem SignTail_tensor (Q : Type) [Fintype Q] [∀ i, MulAction (G i) Q]
    (Ψ : asymptoticInvCat π PUnit ⟶ asymptoticInvCat π PUnit)
    (hΨ : toPoint G π ≫ Ψ = tensorQG G Q ≫ toPoint G π)
    (x : 𝕃.L (asymptoticInvCat π PUnit) 4) :
    𝕃.SignTail π (𝕃.map Ψ 4 x) =
      Tail.map (fun i ↦ AddMonoidHom.mulLeft (permChar (G i) Q)) (𝕃.SignTail π x) := by
  obtain ⟨y, rfl⟩ := 𝕃.toPoint_surjective₄ π x
  rw [map_map, hΨ, ← map_map, SignTail_toPoint, SignTail_toPoint, Tail.map_mk]
  congr 1
  funext i
  rw [𝕃.coord_map (isIndexwise_tensorQG G Q), signAt_restrict_tensorQG]
  rfl

/-- **`σtail_forget`**: `σ_tail(U_* x) = σ_tail(x)`, with no factor `1 / |Gᵢ|` (S12b). -/
theorem σtail_forget (x : 𝕃.L (asymptoticInvCat π PUnit) 4) :
    𝕃.σtail (scalarHom H)
        (𝕃.map (AsymptoticCategory.forgetInv : asymptoticInvCat π PUnit ⟶ _) 4 x) =
      𝕃.σtail π x := by
  obtain ⟨y, rfl⟩ := 𝕃.toPoint_surjective₄ π x
  erw [map_map, toPoint_forget, ← map_map, σtail_toPoint, σtail_toPoint]
  congr 1
  funext i
  rw [𝕃.coord_map isIndexwise_forgetQG, sigAt_restrict_forgetQG]

/-- **(6.3)**: if `(p - τ ⊗)^s` kills the class of `y` in `L_4(V_G)`, then `(p - τᵢ)^s` kills the
`i`-th coordinate of `y` in `L^p_4(ℚ[Gᵢ])` for all large `i`. -/
theorem eventually_nu_pow_coord_eq_zero (Q : Type) [Fintype Q] [∀ i, MulAction (G i) Q]
    (Ψ : asymptoticInvCat π PUnit ⟶ asymptoticInvCat π PUnit)
    (hΨ : toPoint G π ≫ Ψ = tensorQG G Q ≫ toPoint G π)
    (T : AddMonoid.End (𝕃.L (asymptoticInvCat π PUnit) 4)) (hT : ∀ z, T z = 𝕃.map Ψ 4 z)
    {p s : ℕ} (y : 𝕃.L (prodFreeQG G) 4)
    (hy : (((p : AddMonoid.End (𝕃.L (asymptoticInvCat π PUnit) 4)) - T) ^ s)
      (𝕃.map (toPoint G π) 4 y) = 0) :
    ∀ᶠ i in atTop, (((p : AddMonoid.End (Lconc (finSuppFreeQG G {i}) 4)) - tensorAt G Q i) ^ s)
      (𝕃.coord (by norm_num) y i) = 0 := by
  let TP : AddMonoid.End (𝕃.L (prodFreeQG G) 4) := 𝕃.map (tensorQG G Q) 4
  set z := (((p : AddMonoid.End (𝕃.L (prodFreeQG G) 4)) - TP) ^ s) y
  have h₁ : 𝕃.map (toPoint G π) 4 z = 0 :=
    (map_nu_pow_comm _ TP T (fun a ↦ by erw [hT, map_map, map_map, hΨ]) p s y).trans hy
  have h₂ : (QuotientAddGroup.mk (𝕃.coord (by norm_num) z) : Tail _) = 0 :=
    (𝕃.tail_toPoint π (n := 3) (by norm_num) _).symm.trans
      ((congrArg (𝕃.tail π (n := 3) (by norm_num)) h₁).trans (map_zero _))
  have h₃ : ∀ᶠ i in atTop, 𝕃.coord (by norm_num) z i = 0 := (QuotientAddGroup.eq_zero_iff _).mp h₂
  refine h₃.mono fun i hi ↦ ?_
  exact (map_nu_pow_comm ((Pi.evalAddMonoidHom _ i).comp (𝕃.coord (by norm_num))) TP
    (tensorAt G Q i) (fun a ↦ 𝕃.coord_map (isIndexwise_tensorQG G Q) (by norm_num) a i) p s
    y).symm.trans hi

/-- **Theorem 6.3** (proper-family signature divisibility): if `(p - τ ⊗)^s x = 0` in `L_4(V_G)`,
`|Gᵢ| = p ^ (kᵢ + 1)` and `gᵢ` acts on `Q` without fixed points (so `χ_τ(gᵢ) = 0`), then `σ_tail(x)`
is divisible by `p` at every large index, i.e. lies in `∏ pℤ / ⊕ pℤ`. -/
theorem σtail_liftPred_dvd (Q : Type) [Fintype Q] [∀ i, MulAction (G i) Q]
    (Ψ : asymptoticInvCat π PUnit ⟶ asymptoticInvCat π PUnit)
    (hΨ : toPoint G π ≫ Ψ = tensorQG G Q ≫ toPoint G π)
    (T : AddMonoid.End (𝕃.L (asymptoticInvCat π PUnit) 4)) (hT : ∀ z, T z = 𝕃.map Ψ 4 z)
    {p s : ℕ} (hp : p.Prime) (k : ℕ → ℕ) (hG : ∀ i, Fintype.card (G i) = p ^ (k i + 1))
    (g : ∀ i, G i) (hg : ∀ i (q : Q), g i • q ≠ q) (x : 𝕃.L (asymptoticInvCat π PUnit) 4)
    (hx : (((p : AddMonoid.End (𝕃.L (asymptoticInvCat π PUnit) 4)) - T) ^ s) x = 0) :
    (𝕃.σtail π x).LiftPred fun z ↦ (p : ℤ) ∣ z := by
  obtain ⟨y, rfl⟩ := 𝕃.toPoint_surjective₄ π x
  rw [σtail_toPoint, Germ.liftPred_coe]
  filter_upwards [𝕃.eventually_nu_pow_coord_eq_zero π Q Ψ hΨ T hT y hx] with i hi
  exact prime_dvd_sigHom_of_nu_pow_eq_zero (he := even_two) hp (hG i) (Lconc.map (factorFS G i))
    _ _ (permChar_eq_zero (hg i)) (signAt_restrict_tensorQG Q i) hi

/-- **Theorem 6.3 for the tail groups of §7**: `Gᵢ = H/Kᵢ`, `τᵢ = ℚ[C_p]` through `πᵢ` (the functor
`AsymptoticCategory.tensorInv (tauAction C_p)` of Lemma 6.1) and the generator `gen i ∉ Pᵢ`. -/
theorem σtail_liftPred_dvd_of_fixedData {p n : ℕ} [Fact p.Prime] {M : Type*} [TopologicalSpace M]
    [AddAction ℤ_[p] M] (d : FixedData p n M) [Fintype d.Cp]
    (T : AddMonoid.End (𝕃.L (asymptoticInvCat d.π PUnit) 4))
    (hT : ∀ z, T z = 𝕃.map (AsymptoticCategory.tensorInv (tauAction d.Cp) :
      asymptoticInvCat d.π PUnit ⟶ asymptoticInvCat d.π PUnit) 4 z)
    {s : ℕ} (x : 𝕃.L (asymptoticInvCat d.π PUnit) 4)
    (hx : (((p : AddMonoid.End (𝕃.L (asymptoticInvCat d.π PUnit) 4)) - T) ^ s) x = 0) :
    (𝕃.σtail d.π x).LiftPred fun z ↦ (p : ℤ) ∣ z :=
  letI : ∀ i, MulAction (d.G i) d.Cp := fun i ↦ MulAction.compHom _ ((tauAction d.Cp).comp (d.π i))
  𝕃.σtail_liftPred_dvd d.π d.Cp _ (toPoint_tensorInv _ d.π (tauAction d.Cp)) T hT Fact.out
    (fun i ↦ i) d.card_G d.gen (fun i q h ↦ d.π_gen_ne_one i (mul_eq_right.mp
      (show d.π i (d.gen i) * q = q from h))) x hx

end LowerLTheory

end

end HSFormal.LTheory
