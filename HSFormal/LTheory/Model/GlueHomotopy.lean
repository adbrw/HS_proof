import HSFormal.LTheory.Model.GlueKar
import Mathlib.Tactic.Module

/-!
# Homotopy lemmas for gluing Poincaré pairs

Generic support for `Model/Glue.lean`:

* `transposeHomFamily_conjMap`, `IsSymmHomotopy.conjMap`: `T` commutes with conjugation by a
  chain map; `conjHomotopy_refl_hom`, `transposeHomotopy_conjHomotopy_hom`: the transpose of the
  conjugation homotopy `K^* ψ f + f'^* ψ K` of `K : f ≃ f'` is the other ordering, and
  `conjHomotopy_sub_transpose`: they differ by the boundary of `L = K^* ψ K` (`conjL`).
* `relTopDiff`, `relDualityHomotopy`, `relTopDiffHomotopy`: two relative boundaries differing by
  a boundary `dL - Ld` have homotopic relative duality maps (used to symmetrize the union).
* `transposeHom_relDuality_f_sndX`/`_fstX`: the components `δφ`, `-φ j^*` of `TΨ`.
* `KarSplit.compress`, `isKarEquiv_middle_of_comm`: R2 (middle) for ladders whose row maps
  commute with the Kar idempotents.
* `kar_conjMap`, `kar_conjHomotopy`: Kar compatibility of conjugated homotopies.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex homotopyCofiber
  HSFormal.Compression

noncomputable section

universe v u

variable {V : Type u} [Category.{v} V] [Preadditive V] {J : StrictInvolution V} {N : ℤ}

/-! ### Transposes of conjugated homotopies -/

section TransposeConj

variable {B D U : ChainComplex V ℤ}

/-- `T` commutes with conjugation by a chain map `ι`: `T(ι h ι^*) = ι (T h) ι^*`. -/
lemma transposeHomFamily_conjMap (ι : D ⟶ U) (h : ∀ i k, (dualComplex J N D).X i ⟶ D.X k) :
    transposeHomFamily J N (C := U) (D := U)
        (fun i k ↦ (dualHom J N ι).f i ≫ h i k ≫ ι.f k) =
      fun i k ↦ (dualHom J N ι).f i ≫ transposeHomFamily J N h i k ≫ ι.f k := by
  funext r r'
  simp only [transposeHomFamily, dualHom_f, J.star_comp, J.star_star, bidual_hom_f,
    Linear.units_smul_comp, Linear.comp_units_smul, assoc, f_comp_eqToHom ι (sub_sub_cancel N r')]

/-- Conjugating a symmetric homotopy by a chain map gives a symmetric homotopy. -/
lemma IsSymmHomotopy.conjMap {φ φ' : dualComplex J N D ⟶ D} {H : Homotopy φ φ'}
    (hH : IsSymmHomotopy J N H) (ι : D ⟶ U) :
    IsSymmHomotopy J N ((H.compRight ι).compLeft (dualHom J N ι)) := by
  rw [IsSymmHomotopy, transposeHomotopy_hom] at hH ⊢
  have e : ((H.compRight ι).compLeft (dualHom J N ι)).hom =
      fun i k ↦ (dualHom J N ι).f i ≫ H.hom i k ≫ ι.f k := by
    funext i k; simp
  rw [e, transposeHomFamily_conjMap, hH]

lemma dualHomotopy_compLeft_hom {C : ChainComplex V ℤ} {f g : D ⟶ U} (H : Homotopy f g)
    (e : C ⟶ D) (r r' : ℤ) :
    (dualHomotopy J N (H.compLeft e)).hom r r' =
      (dualHomotopy J N H).hom r r' ≫ (dualHom J N e).f r' := by
  simp [J.star_comp]

lemma dualHomotopy_trans_hom {f g h : D ⟶ U} (H₁ : Homotopy f g) (H₂ : Homotopy g h) (r r' : ℤ) :
    (dualHomotopy J N (H₁.trans H₂)).hom r r' =
      (dualHomotopy J N H₁).hom r r' + (dualHomotopy J N H₂).hom r r' := by
  simp [J.star_add]

variable (ψ : dualComplex J N B ⟶ B) {f f' : B ⟶ U} (K : Homotopy f f')

/-- The conjugation homotopy `f ψ f^* ≃ f' ψ f'^*` of `K : f ≃ f'` (with `ψ` fixed) is
`K^* ψ f + f'^* ψ K` (one of the two orderings). -/
lemma conjHomotopy_refl_hom (i k : ℤ) :
    (conjHomotopy K (Homotopy.refl ψ)).hom i k =
      (dualHomotopy J N K).hom i k ≫ ψ.f k ≫ f.f k + (dualHom J N f').f i ≫ ψ.f i ≫ K.hom i k := by
  simp [conjHomotopy, Homotopy.comp]

/-- The transpose of the conjugation homotopy is the other ordering `f^* ψ K + K^* ψ f'`. -/
lemma transposeHomotopy_conjHomotopy_hom (hψ : IsStrictSymm J N ψ) (i k : ℤ) :
    (transposeHomotopy J N (conjHomotopy K (Homotopy.refl ψ))).hom i k =
      (dualHom J N f).f i ≫ ψ.f i ≫ K.hom i k + (dualHomotopy J N K).hom i k ≫ ψ.f k ≫ f'.f k := by
  have hψ' (r : ℤ) : (dualHom J N ψ).f r ≫ (bidual J N B).hom.f r = ψ.f r := by
    rw [← comp_f]; exact congrArg (fun φ ↦ φ.f r) hψ
  have hf' : (dualHom J N (dualHom J N f')).f k ≫ (bidual J N U).hom.f k =
      (bidual J N B).hom.f k ≫ f'.f k := by
    rw [← comp_f, dualHom_dualHom_comp_bidual_hom, comp_f]
  simp only [transposeHomotopy, Homotopy.compRight_hom, conjHomotopy, Homotopy.comp,
    dualHomotopy_trans_hom, dualHomotopy_compRight_hom, dualHomotopy_compLeft_hom, add_comp,
    assoc, dualHomotopy_dualHomotopy_hom_comp, comp_f, dualHom_comp, hf']
  simp only [Homotopy.refl, Homotopy.ofEq, dualHomotopy_hom, Pi.zero_apply, J.star_zero,
    smul_zero, zero_comp, comp_zero, zero_add, ← assoc, hψ']

/-- The second-order homotopy `L = K^* ψ K` between the two orderings of the conjugation
homotopy. -/
def conjL (i k : ℤ) : (dualComplex J N U).X i ⟶ U.X k :=
  (dualHomotopy J N K).hom i (i + 1) ≫ ψ.f (i + 1) ≫ K.hom (i + 1) k

/-- The two orderings of the conjugation homotopy differ by the boundary `dL - Ld` of
`L = K^* ψ K`. -/
lemma conjHomotopy_sub_transpose (hψ : IsStrictSymm J N ψ) (i i₀ i₁ i₂ : ℤ) (h₀ : i₀ + 1 = i)
    (h₁ : i + 1 = i₁) (h₂ : i₁ + 1 = i₂) :
    (conjHomotopy K (Homotopy.refl ψ)).hom i i₁ -
        (transposeHomotopy J N (conjHomotopy K (Homotopy.refl ψ))).hom i i₁ =
      conjL ψ K i i₂ ≫ U.d i₂ i₁ - (dualComplex J N U).d i i₀ ≫ conjL ψ K i₀ i₁ := by
  subst h₀ h₁ h₂
  rw [conjHomotopy_refl_hom, transposeHomotopy_conjHomotopy_hom ψ K hψ]
  have cK := homotopy_comm K (i₀ + 1 + 1) (i₀ + 1) (i₀ + 1 + 1 + 1) (by simp) (by simp)
  have cD := homotopy_comm (dualHomotopy J N K) (i₀ + 1) i₀ (i₀ + 1 + 1) (by simp) (by simp)
  have cψ : (dualComplex J N B).d (i₀ + 1 + 1) (i₀ + 1) ≫ ψ.f (i₀ + 1) =
      ψ.f (i₀ + 1 + 1) ≫ B.d (i₀ + 1 + 1) (i₀ + 1) := (ψ.comm _ _).symm
  rw [cK, cD]
  simp only [conjL, add_comp, comp_add, assoc, reassoc_of% cψ]
  abel

end TransposeConj

/-! ### Changing the relative boundary by a second-order homotopy -/

section RelTopDiff

variable {C D : ChainComplex V ℤ} {j : C ⟶ D} {φ : dualComplex J N C ⟶ C}
  (H₁ H₂ : Homotopy (dualHom J N j ≫ φ ≫ j) 0)

/-- The difference `δφ₁ - δφ₂` of two relative boundaries is a chain map
`D^{N+1-*} ⟶ D`. -/
def relTopDiff : dualComplex J (N + 1) D ⟶ D where
  f r := relTop H₁ r - relTop H₂ r
  comm' r r' h := by
    rw [sub_comp, relTop_comm H₁ r r' h, relTop_comm H₂ r r' h, comp_sub]
    abel

@[simp]
lemma relTopDiff_f (r : ℤ) : (relTopDiff H₁ H₂).f r = relTop H₁ r - relTop H₂ r := rfl

variable [HasBinaryBiproducts V]

lemma relDuality_eq_add :
    relDuality H₁ = relDuality H₂ + dualHom J (N + 1) (inr j) ≫ relTopDiff H₁ H₂ := by
  ext r
  simp only [relDuality_f, add_f_apply, comp_f, dualHom_f, inr_f, relTopDiff_f, comp_sub]
  abel

/-- Relative boundaries whose difference is null-homotopic have homotopic relative duality
maps. -/
def relDualityHomotopy (hΔ : Homotopy (relTopDiff H₁ H₂) 0) :
    Homotopy (relDuality H₁) (relDuality H₂) :=
  homotopyCongr ((Homotopy.refl (relDuality H₂)).add (hΔ.compLeft (dualHom J (N + 1) (inr j))))
    (relDuality_eq_add H₁ H₂).symm (by simp)

omit [HasBinaryBiproducts V] in
/-- If `δφ₁ - δφ₂ = dL - Ld` for a degree-two family `L`, then `δφ₁ - δφ₂ ≃ 0` as chain maps
`D^{N+1-*} ⟶ D`. -/
def relTopDiffHomotopy (L : ∀ i k, (dualComplex J N D).X i ⟶ D.X k)
    (hL : ∀ i i₀ i₁ i₂, i₀ + 1 = i → i + 1 = i₁ → i₁ + 1 = i₂ →
      H₁.hom i i₁ - H₂.hom i i₁ = L i i₂ ≫ D.d i₂ i₁ - (dualComplex J N D).d i i₀ ≫ L i₀ i₁) :
    Homotopy (relTopDiff H₁ H₂) 0 :=
  homotopyCongr (Homotopy.nullHomotopy' fun r r' _ ↦
    (D.XIsoOfEq (by omega : N + 1 - r = N - (r - 1))).hom ≫ L (r - 1) r') (by
      ext r
      rw [Homotopy.nullHomotopicMap'_f (down_rel_succ r) (down_rel_pred r)]
      have h := hL (r - 1) (r - 1 - 1) r (r + 1) (by omega) (by omega) (by omega)
      have e := XIsoOfEq_star_d (J := J) D (by omega : N + 1 - (r - 1) = N - (r - 1 - 1))
        (by omega : N + 1 - r = N - (r - 1))
      simp only [relTopDiff_f, relTop]
      rw [← comp_sub, h]
      simp only [comp_sub, dualComplex_d, Linear.units_smul_comp, Linear.comp_units_smul,
        reassoc_of% e]
      rw [show (r - 1).negOnePow = -r.negOnePow by rw [Int.negOnePow_sub, Int.negOnePow_one]; simp]
      simp only [Units.neg_smul, sub_neg_eq_add, assoc]
      abel) rfl

end RelTopDiff

variable [HasBinaryBiproducts V]

/-! ### The transpose of a relative duality map -/

section TransposeRelDuality

variable {C D : ChainComplex V ℤ} {j : C ⟶ D} {φ : dualComplex J N C ⟶ C}
  (H : Homotopy (dualHom J N j ≫ φ ≫ j) 0)

@[reassoc]
lemma eqToHom_sndX {a b : ℤ} (h : a = b) (h' : (cone j).X a = (cone j).X b) :
    eqToHom h' ≫ sndX j b = sndX j a ≫ eqToHom (congrArg D.X h) := by
  subst h; simp

@[reassoc]
lemma eqToHom_fstX {a b a' b' : ℤ} (h : a = b) (h' : (cone j).X a = (cone j).X b)
    (ha : (ComplexShape.down ℤ).Rel a a') (hb : (ComplexShape.down ℤ).Rel b b') :
    eqToHom h' ≫ fstX j b b' hb =
      fstX j a a' ha ≫ eqToHom (congrArg C.X (by simp at ha hb; omega : a' = b')) := by
  subst h
  obtain rfl : a' = b' := by simp at ha hb; omega
  simp

lemma star_relDuality_f (r : ℤ) :
    J.star ((relDuality H).f r) = J.star (relTop H r) ≫ inrX j (N + 1 - r) +
      (r + 1).negOnePow • J.star (j.f r) ≫ J.star (φ.f r) ≫ inlX j (N - r) (N + 1 - r)
        (down_rel_sub N r) := by
  simp [J.star_add, J.star_comp]

/-- The `D`-component of the transposed relative duality map is `δφ` (by `T δφ = δφ`). -/
lemma transposeHom_relDuality_f_sndX (hH : IsSymmHomotopy J N H) (r : ℤ) :
    (transposeHom J (N + 1) (relDuality H)).f r ≫ sndX j r = relTop H r := by
  rw [transposeHom_f, Linear.units_smul_comp, assoc, eqToHom_sndX (sub_sub_cancel (N + 1) r),
    star_relDuality_f]
  simp only [add_comp, assoc, inrX_sndX_assoc, Linear.units_smul_comp, inlX_sndX_assoc, zero_comp,
    comp_zero, smul_zero, add_zero]
  exact relTop_transpose H hH r

omit [HasBinaryBiproducts V] in
lemma XIsoOfEq_star_j_star_φ {a b m : ℤ} (h : a = b) (e₁ : C.X (N - b) = C.X m)
    (e₂ : C.X (N - a) = C.X m) :
    (D.XIsoOfEq h).hom ≫ J.star (j.f b) ≫ J.star (φ.f b) ≫ eqToHom e₁ =
      J.star (j.f a) ≫ J.star (φ.f a) ≫ eqToHom e₂ := by
  subst h; simp

/-- The `ΣC`-component of the transposed relative duality map is `-φ j^*`. -/
lemma transposeHom_relDuality_f_fstX (hφ : IsStrictSymm J N φ) (r : ℤ) :
    (transposeHom J (N + 1) (relDuality H)).f r ≫ fstX j r (r - 1) (down_rel_pred r) =
      -((D.XIsoOfEq (by omega : N + 1 - r = N - (r - 1))).hom ≫ J.star (j.f (N - (r - 1))) ≫
        φ.f (r - 1)) := by
  rw [transposeHom_f, Linear.units_smul_comp, assoc,
    eqToHom_fstX (sub_sub_cancel (N + 1) r) _ (down_rel_sub N (N + 1 - r)), star_relDuality_f]
  simp only [add_comp, assoc, inrX_fstX_assoc, zero_comp, comp_zero, zero_add,
    Linear.units_smul_comp, inlX_fstX_assoc]
  have hφ' := congrArg (fun ψ ↦ ψ.f (r - 1)) hφ
  simp only [transposeHom_f] at hφ'
  rw [← hφ', Linear.comp_units_smul, Linear.comp_units_smul,
    XIsoOfEq_star_j_star_φ (e₂ := congrArg C.X (by omega)),
    smul_smul, ← Int.negOnePow_add, ← Units.neg_smul, ← Int.negOnePow_succ]
  congr 1
  exact negOnePow_eq_of_eq (N + 1 - r) (by ring)

/-- The relative duality map of a Kar relative boundary is a Kar morphism. -/
lemma relDuality_kar {pB : C ⟶ C} {pD : D ⟶ D} (hpD : pD ≫ pD = pD) (h : pB ≫ j = j ≫ pD)
    (hj : j ≫ pD = j) (hφ : dualHom J N pB ≫ φ = φ)
    (hH : ∀ r r', (dualHom J N pD).f r ≫ H.hom r r' ≫ pD.f r' = H.hom r r') :
    dualHom J (N + 1) (coneMap pB pD h) ≫ relDuality H ≫ pD = relDuality H := by
  have hL (r r' : ℤ) : (dualHom J N pD).f r ≫ H.hom r r' = H.hom r r' := by
    conv_lhs => rw [← hH]
    rw [← assoc, ← comp_f, ← dualHom_comp, hpD, hH]
  have hR (r r' : ℤ) : H.hom r r' ≫ pD.f r' = H.hom r r' := by
    conv_lhs => rw [← hH]
    rw [assoc, assoc, ← comp_f, hpD, hH]
  have hj' (r : ℤ) : j.f r ≫ pD.f r = j.f r := by rw [← comp_f, hj]
  rw [← assoc, dualHom_coneMap_comp_relDuality h H hφ hL]
  ext r
  simp [relTop, hR, hj']

omit [HasBinaryBiproducts V] in
/-- The transpose of a Kar morphism `(C^{N-*}, e^*) ⟶ (D, e')` is a Kar morphism. -/
lemma transposeHom_kar {X Y : ChainComplex V ℤ} {e : X ⟶ X} {e' : Y ⟶ Y}
    {f : dualComplex J N X ⟶ Y} (hf : dualHom J N e ≫ f ≫ e' = f) :
    dualHom J N e' ≫ transposeHom J N f ≫ e = transposeHom J N f := by
  rw [← transposeHom_comp, hf]

end TransposeRelDuality

/-! ### R2 (middle) for maps commuting with the idempotents -/

section CompressSplit

variable {K M Q K' M' Q' : ChainComplex V ℤ} {eK : K ⟶ K} {eM : M ⟶ M} {eQ : Q ⟶ Q}
  {eK' : K' ⟶ K'} {eM' : M' ⟶ M'} {eQ' : Q' ⟶ Q'} {i : K ⟶ M} {q : M ⟶ Q} {i' : K' ⟶ M'}
  {q' : M' ⟶ Q'}

omit [HasBinaryBiproducts V] in
/-- Compressing the maps of a Kar split sequence whose maps commute with the idempotents. -/
def KarSplit.compress (S : KarSplit eK eM eQ i q) (heK : eK ≫ eK = eK) (heM : eM ≫ eM = eM)
    (heQ : eQ ≫ eQ = eQ) (hq : eM ≫ q = q ≫ eQ) : KarSplit eK eM eQ (eK ≫ i) (eM ≫ q) where
  t := S.t
  s := S.s
  t_kar := S.t_kar
  s_kar := S.s_kar
  it n := by rw [comp_f, assoc, S.it, idem_f heK]
  sq n := by
    have : S.s n ≫ eM.f n = S.s n := by rw [← S.s_kar n]; simp [idem_f heM]
    rw [comp_f, reassoc_of% this, S.sq]
  total n := by
    have h₁ : S.t n ≫ eK.f n = S.t n := by rw [← S.t_kar n]; simp [idem_f heK]
    have h₂ : eQ.f n ≫ S.s n = S.s n := by rw [← S.s_kar n]; simp [idem_f_assoc heQ]
    have h₃ : eM.f n ≫ q.f n = q.f n ≫ eQ.f n := by rw [← comp_f, hq, comp_f]
    simp only [comp_f, assoc, reassoc_of% h₁, reassoc_of% h₃, h₂, S.total]

variable [HasFiniteBiproducts V]

omit [HasBinaryBiproducts V] in
/-- **R2, middle, in `Kar V`**, for maps of the rows commuting with the idempotents. -/
theorem isKarEquiv_middle_of_comm (heK : eK ≫ eK = eK) (heM : eM ≫ eM = eM)
    (heQ : eQ ≫ eQ = eQ) (heK' : eK' ≫ eK' = eK') (heM' : eM' ≫ eM' = eM')
    (heQ' : eQ' ≫ eQ' = eQ') (hi : eK ≫ i = i ≫ eM) (hq : eM ≫ q = q ≫ eQ)
    (hi' : eK' ≫ i' = i' ≫ eM') (hq' : eM' ≫ q' = q' ≫ eQ') (S : KarSplit eK eM eQ i q)
    (S' : KarSplit eK' eM' eQ' i' q') {l : K ⟶ K'} {m : M ⟶ M'} {r : Q ⟶ Q'}
    (hl : eK ≫ l ≫ eK' = l) (hm : eM ≫ m ≫ eM' = m) (hr : eQ ≫ r ≫ eQ' = r)
    (h₁ : i ≫ m = l ≫ i') (h₂ : q ≫ r = m ≫ q') (el : IsKarEquiv eK eK' l)
    (er : IsKarEquiv eQ eQ' r) : IsKarEquiv eM eM' m := by
  have kar_of_comm {X Y : ChainComplex V ℤ} {e : X ⟶ X} {e' : Y ⟶ Y} {f : X ⟶ Y}
      (he : e ≫ e = e) (he' : e' ≫ e' = e') (h : e ≫ f = f ≫ e') : e ≫ (e ≫ f) ≫ e' = e ≫ f := by
    rw [assoc, ← h, reassoc_of% he, reassoc_of% he]
  refine isKarEquiv_middle heK heM heQ heK' heM' heQ' (kar_of_comm heK heM hi)
    (kar_of_comm heM heQ hq) (kar_of_comm heK' heM' hi') (kar_of_comm heM' heQ' hq')
    (S.compress heK heM heQ hq) (S'.compress heK' heM' heQ' hq') hl hm hr ?_ ?_ el er
  · rw [assoc, h₁]
    simp only [← assoc, kar_left heK hl, kar_right heK' hl]
  · rw [assoc, h₂]
    simp only [← assoc, kar_left heM hm, kar_right heM' hm]

end CompressSplit

/-! ### Kar compatibility of conjugated homotopies -/

section KarConj

variable {B D U : ChainComplex V ℤ}

omit [HasBinaryBiproducts V] in
lemma kar_conjMap {pD : D ⟶ D} {pU : U ⟶ U} (ι : D ⟶ U) (hι : ι ≫ pU = pD ≫ ι)
    {φ φ' : dualComplex J N D ⟶ D} (H : Homotopy φ φ')
    (hH : ∀ r r', (dualHom J N pD).f r ≫ H.hom r r' ≫ pD.f r' = H.hom r r') (r r' : ℤ) :
    (dualHom J N pU).f r ≫ ((H.compRight ι).compLeft (dualHom J N ι)).hom r r' ≫ pU.f r' =
      ((H.compRight ι).compLeft (dualHom J N ι)).hom r r' := by
  have h₁ : (dualHom J N pU).f r ≫ (dualHom J N ι).f r =
      (dualHom J N ι).f r ≫ (dualHom J N pD).f r := by
    rw [← comp_f, ← dualHom_comp, hι, dualHom_comp, comp_f]
  have h₂ : ι.f r' ≫ pU.f r' = pD.f r' ≫ ι.f r' := by rw [← comp_f, hι, comp_f]
  simp only [Homotopy.compLeft_hom, Homotopy.compRight_hom, assoc, h₂, reassoc_of% h₁]
  rw [← assoc (H.hom r r'), ← assoc ((dualHom J N pD).f r), hH]

omit [HasBinaryBiproducts V] in
lemma kar_conjHomotopy {pB : B ⟶ B} {pU : U ⟶ U} {f f' : B ⟶ U} (K : Homotopy f f')
    (hK : ∀ i k, K.hom i k ≫ pU.f k = pB.f i ≫ K.hom i k) (hf : f ≫ pU = f) (hf' : f' ≫ pU = f')
    (ψ : dualComplex J N B ⟶ B) (hψ : dualHom J N pB ≫ ψ = ψ) (hψ' : ψ ≫ pB = ψ) (r r' : ℤ) :
    (dualHom J N pU).f r ≫ (conjHomotopy K (Homotopy.refl ψ)).hom r r' ≫ pU.f r' =
      (conjHomotopy K (Homotopy.refl ψ)).hom r r' := by
  have h₁ : (dualHom J N pU).f r ≫ (dualHomotopy J N K).hom r r' =
      (dualHomotopy J N K).hom r r' ≫ (dualHom J N pB).f r' := by
    simp only [dualHom_f, dualHomotopy_hom, Linear.comp_units_smul, Linear.units_smul_comp,
      ← J.star_comp, hK]
  have h₂ : (dualHom J N pU).f r ≫ (dualHom J N f').f r = (dualHom J N f').f r := by
    rw [← comp_f, ← dualHom_comp, hf']
  have h₃ (k : ℤ) : (dualHom J N pB).f k ≫ ψ.f k = ψ.f k := by rw [← comp_f, hψ]
  have h₄ (k : ℤ) : ψ.f k ≫ pB.f k = ψ.f k := by rw [← comp_f, hψ']
  have h₅ (k : ℤ) : f.f k ≫ pU.f k = f.f k := by rw [← comp_f, hf]
  have h₃' (k : ℤ) {Z : V} (x : B.X k ⟶ Z) : (dualHom J N pB).f k ≫ ψ.f k ≫ x = ψ.f k ≫ x := by
    rw [← assoc, h₃]
  simp only [conjHomotopy_refl_hom, add_comp, comp_add, assoc, h₅, hK, reassoc_of% h₄,
    reassoc_of% h₁, reassoc_of% h₂, h₃']

end KarConj

end

end HSFormal.LTheory
