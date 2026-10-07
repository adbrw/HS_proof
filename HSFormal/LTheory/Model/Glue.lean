import HSFormal.LTheory.Model.GlueHomotopy

/-!
# Gluing symmetric Poincaré pairs along a boundary component (Ran80I §3)

For a Poincaré pair `W = (j_W : C_P ⟶ D_W, (δφ_W, φ_P))` whose boundary splits as
`P ≅ A ⊕ B` (`BdSplit`: Kar maps `ι_A, ι_B, π_A, π_B`, `φ_P = ι_A φ_A ι_A^* + ι_B φ_B ι_B^*`) and
a pair `Y = (j_Y : C_B ⟶ D_Y, (δφ_Y, -φ_B))` with boundary `-B`, the **union**

  `U = D_W ∪_{C_B} D_Y = Cone(u)`,  `u = (ι_B j_W, j_Y) : C_B ⟶ D_W ⊕ D_Y`,

with boundary map `a' : C_A ⟶ D_W ⟶ U` is a Poincaré pair with boundary `A` (`PairOn.glue`).

* **Structure.** With `K' : β' ≃ -c'` the cone null-homotopy of `u` (`β' = ι_B j_W`,
  `c' = j_Y`, into `U`), the union structure is
  `Hns = ι_W δφ_W ι_W^* + (K'^*(-φ_B)β' + c'^* φ_B K') + ι_Y δφ_Y ι_Y^*` (`Glue.Hns`), the
  relative boundary of `a'` (signs: M2 conventions of `Pairs.lean`, `δφ : Homotopy (jφj^*) 0`).
* **Poincaré duality** (`Glue.poincare_Hns`): R2 (middle) on the strictly commuting ladder
  `0 ⟶ Cone(j_W)^{N+1-*} ⟶ Cone(a')^{N+1-*} ⟶ D_Y^{N+1-*} ⟶ 0` over
  `0 ⟶ D_W ⟶ U ⟶ Cone(j_Y) ⟶ 0` with verticals `Ψ_W`, `Ψ_Z`, `TΨ_Y`
  (`square_left`, `square_right`); R2 in `Kar V` is transported to `Karoubi V`
  (`GlueKar.lean`).
* **Strict symmetry.** `Hns` is not `T`-invariant (Ranicki's union structure has a `φ_1`); the
  pair uses its symmetrization `δφZ = ½(Hns + T Hns)`, whose relative duality map is homotopic
  to that of `Hns` because `T Hns - Hns = dL - Ld` with `L = -½ K'^*(-φ_B)K'`
  (`relDualityδφZHomotopy`). So the strict-symmetry Karoubi encoding needs **no change**.

The closed union `D ∪_C D'` (both pairs on the whole boundary) and the cobordism consequences
are in `Model/Cobordism.lean`.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex homotopyCofiber
  HSFormal.Compression

noncomputable section

universe v u

variable {V : Type u} [Category.{v} V] [Preadditive V] {J : StrictInvolution V} {N : ℤ}

variable [HasBinaryBiproducts V]

/-! ### Pairs with prescribed boundary, and splittings of the boundary -/

/-- A Poincaré pair with prescribed boundary `P`: the fields of `SymPair` other than `bd`
(`SymPair.bd` is a field, so `NullCobordant (A.sum B b)` cannot be destructured by `subst`). -/
structure PairOn (P : SymPoincare J N) where
  D : ChainComplex V ℤ
  pD : D ⟶ D
  pD_idem : pD ≫ pD = pD
  support : SupportedIn pD 0 (N + 1)
  j : P.C ⟶ D
  j_kar : P.p ≫ j ≫ pD = j
  δφ : Homotopy (dualHom J N j ≫ P.φ ≫ j) 0
  δφ_kar : ∀ r r', (dualHom J N pD).f r ≫ δφ.hom r r' ≫ pD.f r' = δφ.hom r r'
  symm : IsSymmHomotopy J N δφ
  poincare : IsKarEquiv (dualHom J (N + 1) (coneMap P.p pD (comm_of_kar P.p_idem pD_idem j_kar)))
    pD (relDuality δφ)

namespace PairOn

variable {P : SymPoincare J N}

/-- The pair with boundary `P`. -/
@[simps]
def toPair (T : PairOn P) : SymPair J N :=
  ⟨P, T.D, T.pD, T.pD_idem, T.support, T.j, T.j_kar, T.δφ, T.δφ_kar, T.symm, T.poincare⟩

end PairOn

/-- A pair, as a pair on its boundary. -/
def SymPair.toPairOn (T : SymPair J N) : PairOn T.bd :=
  ⟨T.D, T.pD, T.pD_idem, T.support, T.j, T.j_kar, T.δφ, T.δφ_kar, T.symm, T.poincare⟩

lemma nullCobordant_iff_nonempty_pairOn {P : SymPoincare J N} :
    NullCobordant P ↔ Nonempty (PairOn P) :=
  ⟨fun ⟨T, hT⟩ ↦ hT ▸ ⟨T.toPairOn⟩, fun ⟨T⟩ ↦ ⟨T.toPair, rfl⟩⟩

/-- A splitting `P ≅ A ⊕ B` of a Poincaré complex by Kar maps: `ι_A π_A + ι_B π_B = p_P`,
orthogonality, and `φ_P = ι_A φ_A ι_A^* + ι_B φ_B ι_B^*`. -/
structure BdSplit (P A B : SymPoincare J N) where
  ιA : A.C ⟶ P.C
  ιB : B.C ⟶ P.C
  πA : P.C ⟶ A.C
  πB : P.C ⟶ B.C
  ιA_kar : A.p ≫ ιA ≫ P.p = ιA
  ιB_kar : B.p ≫ ιB ≫ P.p = ιB
  πA_kar : P.p ≫ πA ≫ A.p = πA
  πB_kar : P.p ≫ πB ≫ B.p = πB
  ιA_πA : ιA ≫ πA = A.p
  ιB_πB : ιB ≫ πB = B.p
  ιA_πB : ιA ≫ πB = 0
  ιB_πA : ιB ≫ πA = 0
  total : πA ≫ ιA + πB ≫ ιB = P.p
  φ_eq : P.φ = dualHom J N ιA ≫ A.φ ≫ ιA + dualHom J N ιB ≫ B.φ ≫ ιB

namespace PairOn

variable {P : SymPoincare J N} (T : PairOn P)

@[reassoc (attr := simp)]
lemma pD_idem_f (n : ℤ) : T.pD.f n ≫ T.pD.f n = T.pD.f n := idem_f T.pD_idem n

@[reassoc (attr := simp)]
lemma j_pD_f (n : ℤ) : T.j.f n ≫ T.pD.f n = T.j.f n := by
  rw [← comp_f]; exact congrArg (fun f ↦ f.f n) T.toPair.j_comp_pD

@[reassoc (attr := simp)]
lemma p_j_f (n : ℤ) : P.p.f n ≫ T.j.f n = T.j.f n := by
  rw [← comp_f]; exact congrArg (fun f ↦ f.f n) T.toPair.p_comp_j

/-- The idempotent `p_P ⊕ p_D` of `Cone(j)`. -/
abbrev coneIdem : cone T.j ⟶ cone T.j :=
  coneMap P.p T.pD (comm_of_kar P.p_idem T.pD_idem T.j_kar)

end PairOn

namespace BdSplit

variable {P A B : SymPoincare J N} (σ : BdSplit P A B) (n : ℤ)

omit [HasBinaryBiproducts V]

@[reassoc (attr := simp)]
lemma ιA_πA_f : σ.ιA.f n ≫ σ.πA.f n = A.p.f n := by rw [← comp_f, σ.ιA_πA]
@[reassoc (attr := simp)]
lemma ιB_πB_f : σ.ιB.f n ≫ σ.πB.f n = B.p.f n := by rw [← comp_f, σ.ιB_πB]
@[reassoc (attr := simp)]
lemma ιA_πB_f : σ.ιA.f n ≫ σ.πB.f n = 0 := by rw [← comp_f, σ.ιA_πB, zero_f]
@[reassoc (attr := simp)]
lemma ιB_πA_f : σ.ιB.f n ≫ σ.πA.f n = 0 := by rw [← comp_f, σ.ιB_πA, zero_f]
@[reassoc (attr := simp)]
lemma p_ιA_f : A.p.f n ≫ σ.ιA.f n = σ.ιA.f n := kar_left_f A.p_idem σ.ιA_kar n
@[reassoc (attr := simp)]
lemma ιA_p_f : σ.ιA.f n ≫ P.p.f n = σ.ιA.f n := kar_right_f P.p_idem σ.ιA_kar n
@[reassoc (attr := simp)]
lemma p_ιB_f : B.p.f n ≫ σ.ιB.f n = σ.ιB.f n := kar_left_f B.p_idem σ.ιB_kar n
@[reassoc (attr := simp)]
lemma ιB_p_f : σ.ιB.f n ≫ P.p.f n = σ.ιB.f n := kar_right_f P.p_idem σ.ιB_kar n
@[reassoc (attr := simp)]
lemma p_πA_f : P.p.f n ≫ σ.πA.f n = σ.πA.f n := kar_left_f P.p_idem σ.πA_kar n
@[reassoc (attr := simp)]
lemma πA_p_f : σ.πA.f n ≫ A.p.f n = σ.πA.f n := kar_right_f A.p_idem σ.πA_kar n
@[reassoc (attr := simp)]
lemma p_πB_f : P.p.f n ≫ σ.πB.f n = σ.πB.f n := kar_left_f P.p_idem σ.πB_kar n
@[reassoc (attr := simp)]
lemma πB_p_f : σ.πB.f n ≫ B.p.f n = σ.πB.f n := kar_right_f B.p_idem σ.πB_kar n

lemma total_f : σ.πA.f n ≫ σ.ιA.f n + σ.πB.f n ≫ σ.ιB.f n = P.p.f n := by
  rw [← comp_f, ← comp_f, ← add_f_apply, σ.total]

end BdSplit

/-! ### The union `D_W ∪_B D_Y` -/

namespace Glue

variable {P A B : SymPoincare J N} (σ : BdSplit P A B) (W : PairOn P) (Y : PairOn B.neg)

/-- The bicones of `D_W ⊕ D_Y`. -/
abbrev bS (r : ℤ) : BinaryBicone (W.D.X r) (Y.D.X r) := BinaryBiproduct.bicone _ _

/-- `D_W ⊕ D_Y`. -/
abbrev S : ChainComplex V ℤ := sumComplex (bS W Y)

/-- `β = ι_B j_W : C_B ⟶ D_W`. -/
def β : B.C ⟶ W.D := σ.ιB ≫ W.j

/-- `a = ι_A j_W : C_A ⟶ D_W`. -/
def a : A.C ⟶ W.D := σ.ιA ≫ W.j

/-- `j_Y : C_B ⟶ D_Y` (the boundary of `Y` is `-B`, with underlying complex `C_B`). -/
def jY : B.C ⟶ Y.D := Y.j

lemma jY_f (r : ℤ) : (jY Y).f r = Y.j.f r := rfl

/-- `u = (β, j_Y) : C_B ⟶ D_W ⊕ D_Y`. -/
def u : B.C ⟶ S W Y := β σ W ≫ sumInl (bS W Y) + jY Y ≫ sumInr (bS W Y)

/-- **The union** `U = D_W ∪_{C_B} D_Y = Cone(u)`. -/
abbrev U : ChainComplex V ℤ := cone (u σ W Y)

/-- `D_W ⟶ U`. -/
def ιW : W.D ⟶ U σ W Y := sumInl (bS W Y) ≫ inr (u σ W Y)

/-- `D_Y ⟶ U`. -/
def ιY : Y.D ⟶ U σ W Y := sumInr (bS W Y) ≫ inr (u σ W Y)

/-- The idempotent `p_W ⊕ p_Y` of `D_W ⊕ D_Y`. -/
def pS : S W Y ⟶ S W Y :=
  sumFst (bS W Y) ≫ W.pD ≫ sumInl (bS W Y) + sumSnd (bS W Y) ≫ Y.pD ≫ sumInr (bS W Y)

lemma W_j_comp_pD : W.j ≫ W.pD = W.j := W.toPair.j_comp_pD
lemma Y_j_comp_pD : jY Y ≫ Y.pD = jY Y := Y.toPair.j_comp_pD
lemma p_comp_W_j : P.p ≫ W.j = W.j := W.toPair.p_comp_j
lemma p_comp_Y_j : B.p ≫ jY Y = jY Y := Y.toPair.p_comp_j

omit [HasBinaryBiproducts V] in
include σ in
lemma p_comp_ιB : B.p ≫ σ.ιB = σ.ιB := kar_left B.p_idem σ.ιB_kar

lemma β_pD : β σ W ≫ W.pD = β σ W := by rw [β, assoc, W_j_comp_pD]

lemma p_β : B.p ≫ β σ W = β σ W := by rw [β, ← assoc, p_comp_ιB]

lemma u_pS : B.p ≫ u σ W Y = u σ W Y ≫ pS W Y := by
  simp only [u, pS, comp_add, add_comp, assoc, sumInl_sumFst_assoc, sumInl_sumSnd_assoc,
    sumInr_sumFst_assoc, sumInr_sumSnd_assoc, zero_comp, comp_zero, add_zero, zero_add]
  rw [reassoc_of% (p_β σ W), reassoc_of% (p_comp_Y_j Y), reassoc_of% (β_pD σ W),
    reassoc_of% (Y_j_comp_pD Y)]

/-- The idempotent `p_B ⊕ p_W ⊕ p_Y` of the union. -/
abbrev pU : U σ W Y ⟶ U σ W Y := coneMap B.p (pS W Y) (u_pS σ W Y)

lemma pS_idem : pS W Y ≫ pS W Y = pS W Y := by
  simp [pS, add_comp, comp_add, reassoc_of% W.pD_idem, reassoc_of% Y.pD_idem]

lemma pU_idem : pU σ W Y ≫ pU σ W Y = pU σ W Y := coneMap_idem _ B.p_idem (pS_idem W Y)

lemma inr_coneMap {B' D' B'' D'' : ChainComplex V ℤ} {j : B' ⟶ D'} {j' : B'' ⟶ D''}
    {m : B' ⟶ B''} {n : D' ⟶ D''} (h : m ≫ j' = j ≫ n) : inr j ≫ coneMap m n h = n ≫ inr j' := by
  ext i; simp

@[reassoc]
lemma ιW_pU : ιW σ W Y ≫ pU σ W Y = W.pD ≫ ιW σ W Y := by
  rw [ιW, assoc, inr_coneMap, ← assoc, ← assoc]
  congr 1
  simp [pS, comp_add]

@[reassoc]
lemma ιY_pU : ιY σ W Y ≫ pU σ W Y = Y.pD ≫ ιY σ W Y := by
  rw [ιY, assoc, inr_coneMap, ← assoc, ← assoc]
  congr 1
  simp [pS, comp_add]

/-- The boundary inclusion `a' : C_A ⟶ D_W ⟶ U` of the glued pair. -/
@[implicit_reducible] def a' : A.C ⟶ U σ W Y := a σ W ≫ ιW σ W Y

/-- `β' : C_B ⟶ D_W ⟶ U`. -/
@[implicit_reducible] def β' : B.C ⟶ U σ W Y := β σ W ≫ ιW σ W Y

/-- `c' : C_B ⟶ D_Y ⟶ U`. -/
@[implicit_reducible] def c' : B.C ⟶ U σ W Y := jY Y ≫ ιY σ W Y

include σ in
omit [HasBinaryBiproducts V] in
lemma p_comp_ιA : A.p ≫ σ.ιA = σ.ιA := kar_left A.p_idem σ.ιA_kar

lemma a'_kar : A.p ≫ a' σ W Y ≫ pU σ W Y = a' σ W Y := by
  rw [a', a, assoc, assoc, ιW_pU, reassoc_of% (W_j_comp_pD W), ← assoc, p_comp_ιA, assoc]

lemma β'_pU : β' σ W Y ≫ pU σ W Y = β' σ W Y := by
  rw [β', assoc, ιW_pU, reassoc_of% (β_pD σ W)]

lemma c'_pU : c' σ W Y ≫ pU σ W Y = c' σ W Y := by
  rw [c', assoc, ιY_pU, reassoc_of% (Y_j_comp_pD Y)]

lemma u_comp_inr : u σ W Y ≫ inr (u σ W Y) = β' σ W Y + c' σ W Y := by
  simp [u, β', c', ιW, ιY, add_comp]
  rfl

/-- The cone null-homotopy `β' + c' ≃ 0`, as `K' : β' ≃ -c'` (its components are
`inlX : C_B ⟶ Σ C_B ⊂ U`). -/
def K' : Homotopy (β' σ W Y) (-c' σ W Y) :=
  homotopyCongr ((inrCompHomotopy (u σ W Y) down_exists_rel).add (Homotopy.refl (-c' σ W Y)))
    (by rw [u_comp_inr]; abel) (by simp)

lemma K'_hom (i k : ℤ) :
    (K' σ W Y).hom i k = (inrCompHomotopy (u σ W Y) down_exists_rel).hom i k := by
  simp [K']

lemma K'_hom_pU (i k : ℤ) :
    (K' σ W Y).hom i k ≫ (pU σ W Y).f k = B.p.f i ≫ (K' σ W Y).hom i k := by
  by_cases h : (ComplexShape.down ℤ).Rel k i
  · rw [K'_hom, inrCompHomotopy_hom _ _ _ _ h]
    simp
  · rw [K'_hom, (inrCompHomotopy _ _).zero _ _ h]
    simp

/-- The `D_W`-part `ι_W δφ_W ι_W^*` of the union structure. -/
def HW : Homotopy (dualHom J N (ιW σ W Y) ≫ (dualHom J N W.j ≫ P.φ ≫ W.j) ≫ ιW σ W Y)
    (dualHom J N (ιW σ W Y) ≫ 0 ≫ ιW σ W Y) :=
  (W.δφ.compRight (ιW σ W Y)).compLeft (dualHom J N (ιW σ W Y))

/-- The `D_Y`-part `ι_Y δφ_Y ι_Y^*` of the union structure. -/
def HY : Homotopy (dualHom J N (ιY σ W Y) ≫ (dualHom J N Y.j ≫ B.neg.φ ≫ Y.j) ≫ ιY σ W Y)
    (dualHom J N (ιY σ W Y) ≫ 0 ≫ ιY σ W Y) :=
  (Y.δφ.compRight (ιY σ W Y)).compLeft (dualHom J N (ιY σ W Y))

/-- The cross term: the conjugation homotopy `β' (-φ_B) β'^* ≃ c' (-φ_B) c'^*` of `K'`. -/
def G : Homotopy (dualHom J N (β' σ W Y) ≫ (-B.φ) ≫ β' σ W Y)
    (dualHom J N (-c' σ W Y) ≫ (-B.φ) ≫ (-c' σ W Y)) :=
  conjHomotopy (K' σ W Y) (Homotopy.refl (-B.φ))

/-- The (non-symmetric) union structure `δφ_W ∪_{φ_B} δφ_Y` on `U`, a relative boundary for
`a' : C_A ⟶ U`: `ι_W δφ_W ι_W^* + (K'^* (-φ_B) β' + c'^* φ_B K') + ι_Y δφ_Y ι_Y^*`. -/
def Hns : Homotopy (dualHom J N (a' σ W Y) ≫ A.φ ≫ a' σ W Y) 0 :=
  homotopyCongr ((HW σ W Y).add ((G σ W Y).trans (homotopyCongr (HY σ W Y)
    (by simp [c', jY]) rfl)))
    (by rw [σ.φ_eq]; simp [a', β', a, β, add_comp, comp_add]) (by simp)

lemma Hns_hom (i k : ℤ) : (Hns σ W Y).hom i k =
    (HW σ W Y).hom i k + ((G σ W Y).hom i k + (HY σ W Y).hom i k) := by
  simp [Hns]

lemma Hns_kar (r r' : ℤ) :
    (dualHom J N (pU σ W Y)).f r ≫ (Hns σ W Y).hom r r' ≫ (pU σ W Y).f r' =
      (Hns σ W Y).hom r r' := by
  have hW : (dualHom J N (pU σ W Y)).f r ≫ (HW σ W Y).hom r r' ≫ (pU σ W Y).f r' =
      (HW σ W Y).hom r r' := kar_conjMap (ιW σ W Y) (ιW_pU σ W Y) W.δφ W.δφ_kar r r'
  have hY : (dualHom J N (pU σ W Y)).f r ≫ (HY σ W Y).hom r r' ≫ (pU σ W Y).f r' =
      (HY σ W Y).hom r r' := kar_conjMap (ιY σ W Y) (ιY_pU σ W Y) Y.δφ Y.δφ_kar r r'
  have hG : (dualHom J N (pU σ W Y)).f r ≫ (G σ W Y).hom r r' ≫ (pU σ W Y).f r' =
      (G σ W Y).hom r r' := kar_conjHomotopy (K' σ W Y) (K'_hom_pU σ W Y) (β'_pU σ W Y)
    (by rw [neg_comp, c'_pU]) (-B.φ) (by simp) (by simp) r r'
  rw [Hns_hom]
  simp only [comp_add, add_comp, hW, hG, hY]

lemma HW_symm : IsSymmHomotopy J N (HW σ W Y) := W.symm.conjMap _

lemma HY_symm : IsSymmHomotopy J N (HY σ W Y) := Y.symm.conjMap _

lemma transposeHomotopy_Hns_hom (i k : ℤ) :
    (transposeHomotopy J N (Hns σ W Y)).hom i k =
      (HW σ W Y).hom i k + ((transposeHomotopy J N (G σ W Y)).hom i k + (HY σ W Y).hom i k) := by
  have e : (Hns σ W Y).hom = (HW σ W Y).hom + ((G σ W Y).hom + (HY σ W Y).hom) := by
    funext i k; exact Hns_hom σ W Y i k
  have hW := HW_symm σ W Y
  have hY := HY_symm σ W Y
  rw [IsSymmHomotopy, transposeHomotopy_hom] at hW hY
  rw [transposeHomotopy_hom, e, transposeHomFamily_add, transposeHomFamily_add, hW, hY,
    ← transposeHomotopy_hom]
  rfl

variable [Linear ℚ V]

omit [Linear ℚ V] in
lemma isStrictSymm_a' : IsStrictSymm J N (dualHom J N (a' σ W Y) ≫ A.φ ≫ a' σ W Y) :=
  A.symm.conj _

omit [Linear ℚ V] in
lemma isStrictSymm_zero : IsStrictSymm J N (0 : dualComplex J N (U σ W Y) ⟶ U σ W Y) := by
  simp [IsStrictSymm]

/-- **The union structure** `δφ_W ∪_{φ_B} δφ_Y`: the symmetrization of `Hns`, a symmetric
relative boundary for `a' : C_A ⟶ U`. -/
def δφZ : Homotopy (dualHom J N (a' σ W Y) ≫ A.φ ≫ a' σ W Y) 0 :=
  symmHomotopy (isStrictSymm_a' σ W Y) (isStrictSymm_zero σ W Y) (Hns σ W Y)

lemma δφZ_symm : IsSymmHomotopy J N (δφZ σ W Y) := isSymmHomotopy_symmHomotopy _ _ _

lemma δφZ_kar (r r' : ℤ) :
    (dualHom J N (pU σ W Y)).f r ≫ (δφZ σ W Y).hom r r' ≫ (pU σ W Y).f r' =
      (δφZ σ W Y).hom r r' :=
  kar_symmHomotopy_hom (pU_idem σ W Y) _ _ _ (Hns_kar σ W Y) r r'

/-- The symmetrization changes the relative duality map only up to homotopy: the defect is
`d L - L d` with `L = -½ K'^* (-φ_B) K'`. -/
def relDualityδφZHomotopy : Homotopy (relDuality (δφZ σ W Y)) (relDuality (Hns σ W Y)) :=
  relDualityHomotopy _ _ (relTopDiffHomotopy _ _
    (fun i k ↦ (-(1 / 2 : ℚ)) • conjL (-B.φ) (K' σ W Y) i k) (by
      intro i i₀ i₁ i₂ h₀ h₁ h₂
      have h := conjHomotopy_sub_transpose (-B.φ) (K' σ W Y) B.symm.neg i i₀ i₁ i₂ h₀ h₁ h₂
      rw [δφZ, symmHomotopy_hom, ← transposeHomotopy_hom]
      simp only [Pi.smul_apply, Pi.add_apply, transposeHomotopy_Hns_hom, Hns_hom]
      change (G σ W Y).hom i i₁ - (transposeHomotopy J N (G σ W Y)).hom i i₁ = _ at h
      rw [Linear.smul_comp, Linear.comp_smul, ← smul_sub, ← h]
      module))

/-! #### The ladder -/

omit [Linear ℚ V]

/-- `n_W : U ⟶ Cone(j_W)`, `(x_B, y_W, y_Y) ↦ (ι_B x_B, y_W)`. -/
def nW : U σ W Y ⟶ cone W.j :=
  coneMap (j := u σ W Y) (j' := W.j) σ.ιB (sumFst (bS W Y)) (by simp [u, β])

lemma ιW_nW : ιW σ W Y ≫ nW σ W Y = inr W.j := by
  rw [ιW, nW, assoc, inr_coneMap, sumInl_sumFst_assoc]

lemma ιY_nW : ιY σ W Y ≫ nW σ W Y = 0 := by
  rw [ιY, nW, assoc, inr_coneMap, sumInr_sumFst_assoc, zero_comp]

/-- The null-homotopy `a' n_W = ι_A j_W inr ≃ 0`. -/
def hπ : Homotopy (a' σ W Y ≫ nW σ W Y) 0 :=
  homotopyCongr ((inrCompHomotopy W.j down_exists_rel).compLeft σ.ιA)
    (by rw [a', a, assoc, assoc, ιW_nW]) (by simp)

/-- `π : Cone(a') ⟶ Cone(j_W)`, `(x_A, x_B, y_W, y_Y) ↦ (ι_A x_A + ι_B x_B, y_W)`. -/
def π : cone (a' σ W Y) ⟶ cone W.j := desc (a' σ W Y) (nW σ W Y) (hπ σ W Y)

@[reassoc (attr := simp)]
lemma inlX_π (i k : ℤ) (h : (ComplexShape.down ℤ).Rel k i) :
    inlX (a' σ W Y) i k h ≫ (π σ W Y).f k = σ.ιA.f i ≫ inlX W.j i k h := by
  rw [π, inlX_desc_f _ _ _ _ _ h, hπ, homotopyCongr_hom, Homotopy.compLeft_hom,
    inrCompHomotopy_hom _ _ _ _ h]

@[reassoc (attr := simp)]
lemma inrX_π (i : ℤ) : inrX (a' σ W Y) i ≫ (π σ W Y).f i = (nW σ W Y).f i := by
  rw [π, inrX_desc_f]

/-- `ι_Y' : D_Y ⟶ U ⟶ Cone(a')`. -/
def ιY' : Y.D ⟶ cone (a' σ W Y) := ιY σ W Y ≫ inr (a' σ W Y)

/-- `ρ : U ⟶ Cone(j_Y)`, `(x_B, y_W, y_Y) ↦ (x_B, y_Y)`. -/
def ρ : U σ W Y ⟶ cone Y.j :=
  coneMap (j := u σ W Y) (j' := Y.j) (𝟙 B.C) (sumSnd (bS W Y)) (by simp [u, jY])

/-- The idempotent of `Cone(a')`. -/
abbrev pM : cone (a' σ W Y) ⟶ cone (a' σ W Y) :=
  coneMap A.p (pU σ W Y) (comm_of_kar A.p_idem (pU_idem σ W Y) (a'_kar σ W Y))

/-- The degreewise split sequence `0 ⟶ D_Y ⟶ Cone(a') ⟶ Cone(j_W) ⟶ 0` (Kar). -/
def splitTop : KarSplit Y.pD (pM σ W Y) W.coneIdem (ιY' σ W Y) (π σ W Y) where
  t n := sndX (a' σ W Y) n ≫ sndX (u σ W Y) n ≫ (bS W Y n).snd ≫ Y.pD.f n
  s n := fstX W.j n (n - 1) (down_rel_pred n) ≫ (σ.πA.f (n - 1) ≫
      inlX (a' σ W Y) (n - 1) n (down_rel_pred n) + σ.πB.f (n - 1) ≫
      inlX (u σ W Y) (n - 1) n (down_rel_pred n) ≫ inrX (a' σ W Y) n) +
    sndX W.j n ≫ W.pD.f n ≫ (bS W Y n).inl ≫ inrX (u σ W Y) n ≫ inrX (a' σ W Y) n
  t_kar n := by simp [pS]
  s_kar n := by simp [pS]
  it n := by simp [ιY', ιY]
  sq n := by
    rw [coneMap_f _ n (n - 1) (down_rel_pred n), ← σ.total_f]
    simp [nW, add_comp, comp_add]
  total n := by
    apply ext_from_X (a' σ W Y) (n - 1) n (down_rel_pred n)
    · simp [ιY']
    · apply ext_from_X (u σ W Y) (n - 1) n (down_rel_pred n)
      · simp [ιY', nW]
      · apply biprod.hom_ext'
        · simp [ιY', nW, pS]
        · simp [ιY', ιY, nW, pS]

/-- The degreewise split sequence `0 ⟶ D_W ⟶ U ⟶ Cone(j_Y) ⟶ 0` (Kar). -/
def splitBot : KarSplit W.pD (pU σ W Y) Y.coneIdem (ιW σ W Y) (ρ σ W Y) where
  t n := sndX (u σ W Y) n ≫ (bS W Y n).fst ≫ W.pD.f n
  s n := fstX Y.j n (n - 1) (down_rel_pred n) ≫ B.p.f (n - 1) ≫
      inlX (u σ W Y) (n - 1) n (down_rel_pred n) +
    sndX Y.j n ≫ Y.pD.f n ≫ (bS W Y n).inr ≫ inrX (u σ W Y) n
  t_kar n := by simp [pS]
  s_kar n := by simp [pS]
  it n := by simp [ιW]
  sq n := by
    rw [coneMap_f _ n (n - 1) (down_rel_pred n)]
    simp [ρ, add_comp]
  total n := by
    apply ext_from_X (u σ W Y) (n - 1) n (down_rel_pred n)
    · simp [ιW, ρ]
    · apply biprod.hom_ext'
      · simp [ιW, ρ, pS]
      · simp [ιW, ρ, pS]

/-! #### The left square -/

@[reassoc (attr := simp)]
lemma star_π_inrX (k : ℤ) :
    J.star ((π σ W Y).f k) ≫ J.star (inrX (a' σ W Y) k) = J.star ((nW σ W Y).f k) := by
  rw [← J.star_comp, inrX_π]

@[reassoc (attr := simp)]
lemma star_π_inlX (m k : ℤ) (h : (ComplexShape.down ℤ).Rel k m) :
    J.star ((π σ W Y).f k) ≫ J.star (inlX (a' σ W Y) m k h) =
      J.star (inlX W.j m k h) ≫ J.star (σ.ιA.f m) := by
  rw [← J.star_comp, inlX_π, J.star_comp]

@[reassoc (attr := simp)]
lemma star_nW_ιW (k : ℤ) :
    J.star ((nW σ W Y).f k) ≫ J.star ((ιW σ W Y).f k) = J.star (inrX W.j k) := by
  rw [← J.star_comp, ← comp_f, ιW_nW, inr_f]

@[reassoc (attr := simp)]
lemma star_nW_ιY (k : ℤ) : J.star ((nW σ W Y).f k) ≫ J.star ((ιY σ W Y).f k) = 0 := by
  rw [← J.star_comp, ← comp_f, ιY_nW, zero_f, J.star_zero]

@[reassoc (attr := simp)]
lemma star_nW_inlX (m k : ℤ) (h : (ComplexShape.down ℤ).Rel k m) :
    J.star ((nW σ W Y).f k) ≫ J.star (inlX (u σ W Y) m k h) =
      J.star (inlX W.j m k h) ≫ J.star (σ.ιB.f m) := by
  rw [← J.star_comp, nW, inlX_coneMap_f, J.star_comp]

@[reassoc]
lemma XIsoOfEq_star_inrX {B' D' : ChainComplex V ℤ} (j : B' ⟶ D') {k k' : ℤ} (h : k = k') :
    ((cone j).XIsoOfEq h).hom ≫ J.star (inrX j k') = J.star (inrX j k) ≫ (D'.XIsoOfEq h).hom := by
  subst h; simp

@[reassoc]
lemma XIsoOfEq_star_inlX {B' D' : ChainComplex V ℤ} (j : B' ⟶ D') {m k k' : ℤ} (h : k = k')
    (hk : (ComplexShape.down ℤ).Rel k m) (hk' : (ComplexShape.down ℤ).Rel k' m) :
    ((cone j).XIsoOfEq h).hom ≫ J.star (inlX j m k' hk') = J.star (inlX j m k hk) := by
  subst h; simp

lemma square_left : dualHom J (N + 1) (π σ W Y) ≫ relDuality (Hns σ W Y) =
    relDuality W.δφ ≫ ιW σ W Y := by
  ext r
  have hk : N + 1 - r = N - (r - 1) := by omega
  simp only [comp_f, dualHom_f, relDuality_f, comp_add, add_comp, assoc, Linear.comp_units_smul,
    Linear.units_smul_comp, star_π_inrX_assoc, star_π_inlX_assoc, relTop, Hns_hom]
  have hrel : (ComplexShape.down ℤ).Rel (N - (r - 1)) (N - r) := by simp; omega
  rw [star_f_XIsoOfEq_assoc (nW σ W Y) hk, star_f_XIsoOfEq_assoc (nW σ W Y) hk,
    star_f_XIsoOfEq_assoc (nW σ W Y) hk, G, conjHomotopy_refl_hom, dualHomotopy_hom, K'_hom,
    inrCompHomotopy_hom _ _ _ _ hrel]
  have hφ : P.φ.f r = J.star (σ.ιA.f (N - r)) ≫ A.φ.f r ≫ σ.ιA.f r +
      J.star (σ.ιB.f (N - r)) ≫ B.φ.f r ≫ σ.ιB.f r := by
    rw [σ.φ_eq]; simp
  rw [hφ]
  simp only [HW, HY, Homotopy.compLeft_hom, Homotopy.compRight_hom, dualHom_f, star_nW_ιW_assoc,
    star_nW_ιY_assoc, zero_comp, comp_zero, add_zero, XIsoOfEq_star_inrX_assoc, comp_add,
    Linear.comp_units_smul, Linear.units_smul_comp, star_nW_inlX_assoc,
    XIsoOfEq_star_inlX_assoc (h := hk) (hk := down_rel_sub N r), c', comp_f, J.star_comp,
    neg_comp, J.star_neg, neg_f_apply, β', a', a, β, assoc, sub_add_cancel, comp_neg, neg_zero,
    add_comp, Int.negOnePow_succ, Units.neg_smul, smul_add]
  abel

/-! #### The right square -/

@[reassoc (attr := simp)]
lemma ιW_f_fstX (r k : ℤ) (h : (ComplexShape.down ℤ).Rel r k) :
    (ιW σ W Y).f r ≫ fstX (u σ W Y) r k h = 0 := by
  simp [ιW]

@[reassoc (attr := simp)]
lemma ιY_f_fstX (r k : ℤ) (h : (ComplexShape.down ℤ).Rel r k) :
    (ιY σ W Y).f r ≫ fstX (u σ W Y) r k h = 0 := by
  simp [ιY]

@[reassoc (attr := simp)]
lemma ιW_f_sndX (r : ℤ) : (ιW σ W Y).f r ≫ sndX (u σ W Y) r = biprod.inl := by
  simp [ιW]

@[reassoc (attr := simp)]
lemma ιY_f_sndX (r : ℤ) : (ιY σ W Y).f r ≫ sndX (u σ W Y) r = biprod.inr := by
  simp [ιY]

lemma square_right : dualHom J (N + 1) (ιY' σ W Y) ≫ transposeHom J (N + 1) (relDuality Y.δφ) =
    relDuality (Hns σ W Y) ≫ ρ σ W Y := by
  ext r
  have hk : N + 1 - r = N - (r - 1) := by omega
  have hrel : (ComplexShape.down ℤ).Rel r (r - 1) := down_rel_pred r
  apply ext_to_X Y.j r (r - 1) hrel
  · rw [comp_f, assoc, transposeHom_relDuality_f_fstX _ (B.neg.symm), comp_f, assoc, ρ,
      coneMap_f_fstX]
    simp only [relDuality_f, add_comp, assoc, relTop, Hns_hom, comp_add, Linear.units_smul_comp,
      HW, HY, G, conjHomotopy_refl_hom, K'_hom, inrCompHomotopy_hom _ _ _ _ hrel,
      Homotopy.compLeft_hom, Homotopy.compRight_hom, dualHom_f, a', β', c', comp_f, ιW_f_fstX,
      ιY_f_fstX, comp_zero, zero_add, add_zero, smul_zero, inlX_fstX, comp_id, ιY', inr_f,
      J.star_comp, neg_f_apply, J.star_neg, neg_comp, comp_neg, neg_neg, SymPoincare.neg_φ,
      jY_f, id_f, neg_zero]
    rw [star_f_XIsoOfEq_assoc (ιY σ W Y) hk]
  · rw [comp_f, assoc, transposeHom_relDuality_f_sndX _ Y.symm, comp_f, assoc, ρ,
      coneMap_f_sndX]
    simp only [relDuality_f, add_comp, assoc, relTop, Hns_hom, comp_add, Linear.units_smul_comp,
      HW, HY, G, conjHomotopy_refl_hom, K'_hom, inrCompHomotopy_hom _ _ _ _ hrel,
      Homotopy.compLeft_hom, Homotopy.compRight_hom, dualHom_f, a', β', c', comp_f,
      ιW_f_sndX_assoc, ιY_f_sndX_assoc, inlX_sndX_assoc, comp_zero, zero_add, add_zero, smul_zero,
      ιY', inr_f, J.star_comp, sumSnd_f, BinaryBiproduct.bicone_snd, biprod.inl_snd,
      biprod.inr_snd, comp_id, zero_comp]
    rw [star_f_XIsoOfEq_assoc (ιY σ W Y) hk]

/-! #### Poincaré duality of the union -/

lemma nW_comm : pU σ W Y ≫ nW σ W Y = nW σ W Y ≫ W.coneIdem := by
  rw [nW, coneMap_comp, coneMap_comp]
  congr 1
  · rw [p_comp_ιB, kar_right P.p_idem σ.ιB_kar]
  · ext r : 1; simp [pS]

lemma π_comm : pM σ W Y ≫ π σ W Y = π σ W Y ≫ W.coneIdem := by
  ext n
  apply ext_from_X (a' σ W Y) (n - 1) n (down_rel_pred n)
  · simp
  · have h := congrArg (fun f ↦ f.f n) (nW_comm σ W Y)
    simp only [comp_f] at h
    simp [h]

lemma ιY'_comm : Y.pD ≫ ιY' σ W Y = ιY' σ W Y ≫ pM σ W Y := by
  rw [ιY', assoc, inr_coneMap, ← assoc, ← assoc, ιY_pU]

lemma ρ_comm : pU σ W Y ≫ ρ σ W Y = ρ σ W Y ≫ Y.coneIdem := by
  rw [ρ, coneMap_comp, coneMap_comp]
  congr 1
  · simp
  · ext r : 1; simp [pS]

lemma coneIdem_idem {Q : SymPoincare J N} (T : PairOn Q) : T.coneIdem ≫ T.coneIdem = T.coneIdem :=
  coneMap_idem _ Q.p_idem T.pD_idem

lemma pM_idem : pM σ W Y ≫ pM σ W Y = pM σ W Y := coneMap_idem _ A.p_idem (pU_idem σ W Y)

variable [HasFiniteBiproducts V]

/-- **The non-symmetric union is Poincaré**, by R2 on the ladder
`0 ⟶ Cone(j_W)^{N+1-*} ⟶ Cone(a')^{N+1-*} ⟶ D_Y^{N+1-*} ⟶ 0` over
`0 ⟶ D_W ⟶ U ⟶ Cone(j_Y) ⟶ 0` with vertical maps `Ψ_W`, `Ψ_Z` and `TΨ_Y`. -/
theorem poincare_Hns :
    IsKarEquiv (dualHom J (N + 1) (pM σ W Y)) (pU σ W Y) (relDuality (Hns σ W Y)) := by
  have hcW := coneIdem_idem W
  have hcY := coneIdem_idem Y
  refine isKarEquiv_middle_of_comm (dualHom_idem hcW) (dualHom_idem (pM_idem σ W Y))
    (dualHom_idem Y.pD_idem) W.pD_idem (pU_idem σ W Y) hcY ?_ ?_ ?_ (ρ_comm σ W Y)
    ((splitTop σ W Y).dual J (N + 1)) (splitBot σ W Y)
    (relDuality_kar W.δφ W.pD_idem _ (W_j_comp_pD W) W.toPair.bd.dualHom_p_comp_φ W.δφ_kar)
    (relDuality_kar (Hns σ W Y) (pU_idem σ W Y) _ ?_ A.dualHom_p_comp_φ (Hns_kar σ W Y))
    (transposeHom_kar (relDuality_kar Y.δφ Y.pD_idem _ (Y_j_comp_pD Y)
      Y.toPair.bd.dualHom_p_comp_φ Y.δφ_kar)) (square_left σ W Y) (square_right σ W Y)
    W.poincare (Y.poincare.transposeHom hcY Y.pD_idem)
  · rw [← dualHom_comp, ← dualHom_comp, π_comm]
  · rw [← dualHom_comp, ← dualHom_comp, ιY'_comm]
  · exact (ιW_pU σ W Y).symm
  · exact kar_right (pU_idem σ W Y) (a'_kar σ W Y)

omit [HasFiniteBiproducts V] in
lemma pU_support : SupportedIn (pU σ W Y) 0 (N + 1) := by
  intro r hr
  rw [coneMap_f _ r (r - 1) (down_rel_pred r), B.support (r - 1) (by omega)]
  simp [pS, W.support r hr, Y.support r hr]

variable [Linear ℚ V]

/-- **The union is Poincaré** (with the symmetrized structure). -/
theorem poincare_δφZ :
    IsKarEquiv (dualHom J (N + 1) (pM σ W Y)) (pU σ W Y) (relDuality (δφZ σ W Y)) :=
  (poincare_Hns σ W Y).of_homotopy (relDualityδφZHomotopy σ W Y).symm

end Glue

variable [HasFiniteBiproducts V] [Linear ℚ V]

/-- **Gluing Poincaré pairs along a boundary component** (Ran80I §3, union of cobordisms): for
a pair `W` with boundary `P ≅ A ⊕ B` and a pair `Y` with boundary `-B`, the union
`D_W ∪_{C_B} D_Y = Cone(C_B ⟶ D_W ⊕ D_Y)` with boundary map `C_A ⟶ D_W ⟶ D_W ∪ D_Y` and the
symmetrized union structure `δφ_W ∪_{φ_B} δφ_Y` is a Poincaré pair with boundary `A`. -/
def PairOn.glue {P A B : SymPoincare J N} (σ : BdSplit P A B) (W : PairOn P) (Y : PairOn B.neg) :
    PairOn A where
  D := Glue.U σ W Y
  pD := Glue.pU σ W Y
  pD_idem := Glue.pU_idem σ W Y
  support := Glue.pU_support σ W Y
  j := Glue.a' σ W Y
  j_kar := Glue.a'_kar σ W Y
  δφ := Glue.δφZ σ W Y
  δφ_kar := Glue.δφZ_kar σ W Y
  symm := Glue.δφZ_symm σ W Y
  poincare := Glue.poincare_δφZ σ W Y


end

end HSFormal.LTheory
