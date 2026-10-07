import HSFormal.LTheory.Model.HalfLineUnion

/-!
# The half-line splitting (half-line splitting, part 6)

For `Q : SymPoincare A.inv N`, the negative half-line pair `Y = (CZ.negLine A).pair Q` on
`Q` placed at `0` and the reversed positive half-line pair `Z` on `-(Q at 0)`
(`Model/HalfLineUnion.lean`) glue to `Y ∪ Z ≃ (CZ.lineData A).sym Q = Q ⊗ ℝ`:

* `splitYZ`: the honest sequence `0 ⟶ Q at 0 ⟶ Y ⊕ Z ⟶ L(Q) ⟶ 0` (`u = (j_Y, j_Z)`,
  `α = (aY, aZ)`) is degreewise split, so `Cone(u) ⟶ L(Q)` is a homotopy equivalence
  (`coneToCokerEquiv`);
* `isKarEquiv_of_homotopyEquiv`: an honest homotopy equivalence commuting with idempotents is a
  Kar equivalence; the union `Y ∪ Z = Cone(p u)` is strictly Kar isomorphic to `Cone(u)`
  (`isKarEquiv_unionΦ`), so `p_∪ F : Y ∪ Z ⟶ L(Q)` is a Kar equivalence (`isKarEquiv_unionF`);
* with `unionConj` (pushforward of the union structure along `F` is `θ_{1/2,1/2} ≫ L(φ)`), this
  gives `nonempty_union_isometry`, hence `[Y ∪ Z] = tensorLine [Q]` and **`halfLineSplitKar`**.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression
  homotopyCofiber

noncomputable section

attribute [local implicit_reducible] PairOn.toPair SymPair.neg SymPair.toPairOn PairOn.union PairOn.glue
  SymPair.closedOfIsZero CZ.lineData InvFunctor.comp HalfLineData.pair

namespace CZ

/-! ### Cut identities -/

section SplitRel
variable {A : InvCat} (X : A)

@[reassoc]
lemma cut_ιE_πE (Y : A.cz) (p : ℤ → Prop) [DecidablePred p] :
    (cut Y p).ιE ≫ (cut Y p).πE = 𝟙 _ := (cut Y p).ιE_πE

/-- `ι_p π_q = 0` for disjoint `p`, `q`. -/
@[reassoc]
lemma ιπ_eq_zero (p q : ℤ → Prop) [DecidablePred p] [DecidablePred q] (h : ∀ v, ¬ (p v ∧ q v)) :
    (cut ((Δc A).F.obj X) p).ιE ≫ (cut ((Δc A).F.obj X) q).πE = 0 := by
  apply cut_ext
  simp only [assoc, πE_ιE_assoc, comp_zero, zero_comp]
  rw [πE_ιE, idem_idem X p q (fun _ ↦ False) (fun v ↦ ⟨fun h' ↦ h v h', False.elim⟩),
    idem_eq_zero X _ (fun _ h ↦ h)]

/-- `ι_p π_q ι_q = ι_p` for `p ⊆ q`. -/
@[reassoc]
lemma ιπι_of_le (p q : ℤ → Prop) [DecidablePred p] [DecidablePred q] (h : ∀ v, p v → q v) :
    (cut ((Δc A).F.obj X) p).ιE ≫ (cut ((Δc A).F.obj X) q).πE ≫ (cut ((Δc A).F.obj X) q).ιE =
      (cut ((Δc A).F.obj X) p).ιE := by
  rw [πE_ιE, ← ιE_idem_assoc p, idem_idem X p q p (fun v ↦ ⟨fun h' ↦ h'.1, fun h' ↦ ⟨h', h v h'⟩⟩),
    ιE_idem]

lemma cut_zero_le_zero : (cut ((Δc A).F.obj X) (fun v ↦ v = 0)).ιE ≫
    (cut ((Δc A).F.obj X) (fun v ↦ v ≤ 0)).πE ≫
    (cut ((Δc A).F.obj X) (fun v ↦ v ≤ 0)).ιE ≫
        (cut ((Δc A).F.obj X) (fun v ↦ v = 0)).πE = 𝟙 _ := by
  rw [ιπι_of_le_assoc X _ _ (fun v h ↦ by omega), Splitting.ιE_πE]

@[reassoc]
lemma cut_ge_eq_sub_le : (cut ((Δc A).F.obj X) (fun v ↦ 0 ≤ v)).πE ≫
    (cut ((Δc A).F.obj X) (fun v ↦ 0 ≤ v)).ιE =
    𝟙 _ - (cut ((Δc A).F.obj X) (fun v ↦ v ≤ -1)).πE ≫
        (cut ((Δc A).F.obj X) (fun v ↦ v ≤ -1)).ιE := by
  rw [πE_ιE, πE_ιE, ← idem_le_add_idem_ge X (-1)]
  abel

@[reassoc]
lemma cut_le_zero_split : (cut ((Δc A).F.obj X) (fun v ↦ v ≤ 0)).ιE ≫
    (cut ((Δc A).F.obj X) (fun v ↦ v ≤ -1)).πE ≫
    (cut ((Δc A).F.obj X) (fun v ↦ v ≤ -1)).ιE ≫ (cut ((Δc A).F.obj X) (fun v ↦ v ≤ 0)).πE =
    𝟙 _ - (cut ((Δc A).F.obj X) (fun v ↦ v ≤ 0)).ιE ≫ (cut ((Δc A).F.obj X) (fun v ↦ v = 0)).πE ≫
      (cut ((Δc A).F.obj X) (fun v ↦ v = 0)).ιE ≫ (cut ((Δc A).F.obj X) (fun v ↦ v ≤ 0)).πE := by
  apply cut_ext
  simp only [assoc, πE_ιE_assoc, comp_sub, sub_comp, id_comp]
  try rw [πE_ιE]
  rw [idem_idem_assoc X _ _ (fun v ↦ v ≤ -1) (fun v ↦ by (try dsimp only); omega),
    idem_idem X _ _ (fun v ↦ v ≤ -1) (fun v ↦ by (try dsimp only); omega),
    idem_idem_assoc X _ _ (fun v ↦ v = 0) (fun v ↦ by (try dsimp only); omega),
    idem_idem X _ _ (fun v ↦ v = 0) (fun v ↦ by (try dsimp only); omega)]
  rw [eq_sub_iff_add_eq, idem_add_idem X (fun v ↦ v ≤ -1) (fun v ↦ v = 0) (fun v ↦ v ≤ 0)
    (fun v ↦ by (try dsimp only); omega) (fun v ↦ by (try dsimp only); omega)]

@[reassoc]
lemma cut_le_ge_via_zero : (cut ((Δc A).F.obj X) (fun v ↦ v ≤ 0)).ιE ≫
    (cut ((Δc A).F.obj X) (fun v ↦ 0 ≤ v)).πE =
    (cut ((Δc A).F.obj X) (fun v ↦ v ≤ 0)).ιE ≫ (cut ((Δc A).F.obj X) (fun v ↦ v = 0)).πE ≫
      (cut ((Δc A).F.obj X) (fun v ↦ v = 0)).ιE ≫ (cut ((Δc A).F.obj X) (fun v ↦ 0 ≤ v)).πE := by
  apply cut_ext
  simp only [assoc, πE_ιE_assoc]
  try rw [πE_ιE]
  rw [idem_idem X _ _ (fun v ↦ v = 0) (fun v ↦ by (try dsimp only); omega),
    idem_idem_assoc X _ _ (fun v ↦ v = 0) (fun v ↦ by (try dsimp only); omega),
    idem_idem X _ _ (fun v ↦ v = 0) (fun v ↦ by (try dsimp only); omega)]

end SplitRel

section Honest

lemma _root_.HSFormal.LTheory.HalfLineData.aMap_f' {A B : InvCat} {H : HalfLineData A B}
    {L : LineData A B} {κE : H.E.F ⟶ L.Δ.F} {κV : H.V.F ⟶ L.Δ.F}
    (hκ : ∀ X, κE.app X ≫ L.s.iso.hom.app X - κE.app X = (H.u.app X - H.w.app X) ≫ κV.app X)
    (C : ChainComplex A ℤ) (i : ℤ) :
    (H.aMap L κE κV hκ C).f i = fstX (H.g C) i (i - 1) (by simp) ≫ κE.app (C.X (i - 1)) ≫
      inlX (L.g C) (i - 1) i (by simp) + sndX (H.g C) i ≫ κV.app (C.X i) ≫ inrX (L.g C) i := by
  apply ext_from_X (H.g C) (i - 1) i (by simp) <;> simp

variable {A : InvCat} {N : ℤ} (Q : SymPoincare A.inv N)

/-- The honest union map `u = (j_Y, j_Z) : C at 0 ⟶ Y(C) ⊕ Z(C)`. -/
def uh : (Q.map (atZero A)).C ⟶ Glue.S (pairY Q) (pairZ Q) :=
  (negLine A).jC Q.C ≫ sumInl _ + (posLine A).jC Q.C ≫ sumInr _

/-- **The half-lines cover the line**: `0 ⟶ C at 0 ⟶ Y(C) ⊕ Z(C) ⟶ L(C) ⟶ 0` is degreewise
split. -/
def splitYZ : DegreewiseSplit (uh Q) (unionα Q) where
  t n := (sumFst (Glue.bS (pairY Q) (pairZ Q))).f n ≫ sndX ((negLine A).g Q.C) n ≫
    (cut ((Δc A).F.obj (Q.C.X n)) (fun v ↦ v ≤ 0)).ιE ≫
        (cut ((Δc A).F.obj (Q.C.X n)) (fun v ↦ v = 0)).πE
  s n := fstX ((lineData A).g Q.C) n (n - 1) (by simp) ≫
      ((cut ((Δc A).F.obj (Q.C.X (n - 1))) (fun v ↦ v ≤ -1)).πE ≫
          inlX ((negLine A).g Q.C) (n - 1) n (by simp) ≫
              (sumInl (Glue.bS (pairY Q) (pairZ Q))).f n +
        (cut ((Δc A).F.obj (Q.C.X (n - 1))) (fun v ↦ 0 ≤ v)).πE ≫
          inlX ((posLine A).g Q.C) (n - 1) n (by simp) ≫
              (sumInr (Glue.bS (pairY Q) (pairZ Q))).f n) +
    sndX ((lineData A).g Q.C) n ≫
      ((cut ((Δc A).F.obj (Q.C.X n)) (fun v ↦ v ≤ -1)).πE ≫
          (cut ((Δc A).F.obj (Q.C.X n)) (fun v ↦ v ≤ -1)).ιE ≫
          (cut ((Δc A).F.obj (Q.C.X n)) (fun v ↦ v ≤ 0)).πE ≫
          inrX ((negLine A).g Q.C) n ≫ (sumInl (Glue.bS (pairY Q) (pairZ Q))).f n -
        (cut ((Δc A).F.obj (Q.C.X n)) (fun v ↦ 0 ≤ v)).πE ≫ inrX ((posLine A).g Q.C) n ≫
          (sumInr (Glue.bS (pairY Q) (pairZ Q))).f n)
  it n := by
    simp only [uh, add_f_apply, comp_f, add_comp, assoc, sumInl_f_sumFst_f_assoc,
      sumInr_f_sumFst_f_assoc, zero_comp, comp_zero, add_zero, HalfLineData.jC_f, inrX_sndX_assoc]
    simp only [βNat_app, id_comp, assoc]
    exact cut_zero_le_zero _
  sq n := by
    rw [unionα, add_f_apply, comp_f, comp_f, HalfLineData.aMap_f', HalfLineData.aMap_f']
    simp only [comp_add, add_comp, comp_sub, sub_comp, assoc, sumInl_f_sumFst_f_assoc,
      sumInr_f_sumFst_f_assoc, sumInl_f_sumSnd_f_assoc, sumInr_f_sumSnd_f_assoc, zero_comp,
      comp_zero, add_zero, zero_add, sub_zero, zero_sub, inlX_fstX_assoc, inlX_sndX_assoc,
      inrX_fstX_assoc, inrX_sndX_assoc, κ_app, NatTrans.app_neg, neg_comp, comp_neg, neg_neg]
    rw [cut_ge_eq_sub_le_assoc, cut_ge_eq_sub_le_assoc,
        ιπι_of_le_assoc (Q.C.X n) (fun v ↦ v ≤ -1) (fun v ↦ v ≤ 0)
      (fun v h ↦ by (try dsimp only at h ⊢); omega)]
    simp only [sub_comp, comp_sub, id_comp, assoc]
    rw [cone.id_X _ n (n - 1) (by simp)]
    abel
  total n := by
    have h3 : (sumFst (Glue.bS (pairY Q) (pairZ Q))).f n ≫
        (sumInl (Glue.bS (pairY Q) (pairZ Q))).f n +
        (sumSnd (Glue.bS (pairY Q) (pairZ Q))).f n ≫
            (sumInr (Glue.bS (pairY Q) (pairZ Q))).f n = 𝟙 _ := by
      simp only [sumFst_f, sumInl_f, sumSnd_f, sumInr_f]
      rw [add_comm]; exact bicone_total' _ _
    have h1 : 𝟙 ((pairY Q).D.X n) = fstX ((negLine A).g Q.C) n (n - 1) (by simp) ≫
        inlX ((negLine A).g Q.C) (n - 1) n (by simp) + sndX ((negLine A).g Q.C) n ≫
          inrX ((negLine A).g Q.C) n := cone.id_X _ n (n - 1) (by simp)
    have h2 : 𝟙 ((pairZ Q).D.X n) = fstX ((posLine A).g Q.C) n (n - 1) (by simp) ≫
        inlX ((posLine A).g Q.C) (n - 1) n (by simp) + sndX ((posLine A).g Q.C) n ≫
          inrX ((posLine A).g Q.C) n := cone.id_X _ n (n - 1) (by simp)
    conv_rhs => rw [← h3, ← id_comp ((sumInl (Glue.bS (pairY Q) (pairZ Q))).f n),
      ← id_comp ((sumInr (Glue.bS (pairY Q) (pairZ Q))).f n), h1, h2]
    rw [uh, unionα, add_f_apply, add_f_apply, comp_f, comp_f, comp_f, comp_f, HalfLineData.aMap_f',
      HalfLineData.aMap_f', HalfLineData.jC_f, HalfLineData.jC_f]
    simp only [comp_add, add_comp, comp_sub, sub_comp, assoc,
      zero_comp,
      comp_zero, add_zero, zero_add, inlX_fstX_assoc, inlX_sndX_assoc,
      inrX_fstX_assoc, inrX_sndX_assoc, κ_app, βNat_app, NatTrans.app_neg, neg_comp, comp_neg,
      id_comp, cut_ιE_πE_assoc,
      ιπ_eq_zero_assoc _ (fun v ↦ 0 ≤ v) (fun v ↦ v ≤ -1) (fun v ↦ by (try dsimp only); omega),
      ιπ_eq_zero_assoc _ (fun v ↦ v ≤ -1) (fun v ↦ 0 ≤ v) (fun v ↦ by (try dsimp only); omega),
      cut_le_zero_split_assoc, cut_le_ge_via_zero_assoc, neg_zero]
    abel

end Honest

/-! ### Transfer of honest equivalences to Kar equivalences -/

lemma isKarEquiv_of_homotopyEquiv {V : Type*} [Category V] [Preadditive V]
    {X Y : ChainComplex V ℤ} (e : HomotopyEquiv X Y) {p : X ⟶ X} {q : Y ⟶ Y} (hp : p ≫ p = p)
    (hq : q ≫ q = q) (h : p ≫ e.hom = e.hom ≫ q) : IsKarEquiv p q (p ≫ e.hom) := by
  refine ⟨q ≫ e.inv ≫ p, by simp [reassoc_of% hq, hp], ⟨?_⟩, ⟨?_⟩⟩
  · refine homotopyCongr ((e.homotopyInvHomId.compRight q).compLeft q) ?_ (by simp [hq])
    simp only [assoc, reassoc_of% h, h, hq]
  · refine homotopyCongr ((e.homotopyHomInvId.compRight p).compLeft p) ?_ (by simp [hp])
    simp only [assoc, ← reassoc_of% h, reassoc_of% hp]

/-! ### The comparison map is a Kar equivalence -/

section KarUnion

variable {A : InvCat} {N : ℤ} (Q : SymPoincare A.inv N)

lemma u_eq_uh : Glue.u (σQ Q) (pairY Q) (pairZ Q) = uh Q ≫ Glue.pS (pairY Q) (pairZ Q) := by
  have hY : (σQ Q).ιB ≫ (pairY Q).j = (negLine A).jC Q.C ≫ (pairY Q).pD :=
    Glue.p_comp_W_j (pairY Q)
  have hZ : Glue.jY (pairZ Q) = (posLine A).jC Q.C ≫ (pairZ Q).pD := rfl
  rw [Glue.u, Glue.β, hY, hZ, uh, Glue.pS]
  simp only [comp_add, add_comp, assoc, sumInl_sumFst_assoc, sumInl_sumSnd_assoc,
    sumInr_sumFst_assoc, sumInr_sumSnd_assoc, zero_comp, comp_zero, add_zero, zero_add]

lemma p_uh : (Q.map (atZero A)).p ≫ uh Q = uh Q ≫ Glue.pS (pairY Q) (pairZ Q) := by
  have h₁ : (Q.map (atZero A)).p ≫ (negLine A).jC Q.C = (negLine A).jC Q.C ≫ (pairY Q).pD :=
    (negLine A).jC_natural Q.p
  have h₂ : (Q.map (atZero A)).p ≫ (posLine A).jC Q.C = (posLine A).jC Q.C ≫ (pairZ Q).pD :=
    (posLine A).jC_natural Q.p
  rw [uh, Glue.pS]
  simp only [comp_add, add_comp, assoc, sumInl_sumFst_assoc, sumInl_sumSnd_assoc,
    sumInr_sumFst_assoc, sumInr_sumSnd_assoc, zero_comp, comp_zero, add_zero, zero_add,
    reassoc_of% h₁, reassoc_of% h₂]

lemma pS_unionα : Glue.pS (pairY Q) (pairZ Q) ≫ unionα Q = unionα Q ≫ (lineData A).map Q.p := by
  have h₁ : (pairY Q).pD ≫ aY A Q.C = aY A Q.C ≫ (lineData A).map Q.p :=
    HalfLineData.aMap_natural _ _
  have h₂ : (pairZ Q).pD ≫ aZ A Q.C = aZ A Q.C ≫ (lineData A).map Q.p :=
    HalfLineData.aMap_natural _ _
  rw [unionα, Glue.pS]
  simp only [comp_add, add_comp, assoc, sumInl_sumFst_assoc, sumInl_sumSnd_assoc,
    sumInr_sumFst_assoc, sumInr_sumSnd_assoc, zero_comp, comp_zero, add_zero, zero_add, h₁, h₂]

/-- The idempotent of the honest union `Cone(u_h)`. -/
abbrev ph : cone (uh Q) ⟶ cone (uh Q) :=
  coneMap (Q.map (atZero A)).p (Glue.pS (pairY Q) (pairZ Q)) (p_uh Q)

lemma ph_idem : ph Q ≫ ph Q = ph Q :=
  coneMap_idem _ (Q.map (atZero A)).p_idem (Glue.pS_idem _ _)

/-- `Y ∪ Z ⟶ Cone(u_h)`. -/
abbrev unionΦ : Glue.U (σQ Q) (pairY Q) (pairZ Q) ⟶ cone (uh Q) :=
  coneMap (Q.map (atZero A)).p (Glue.pS (pairY Q) (pairZ Q))
    (by rw [u_eq_uh, assoc, Glue.pS_idem, p_uh])

/-- `Cone(u_h) ⟶ Y ∪ Z`. -/
abbrev unionΨ : cone (uh Q) ⟶ Glue.U (σQ Q) (pairY Q) (pairZ Q) :=
  coneMap (Q.map (atZero A)).p (Glue.pS (pairY Q) (pairZ Q))
    (by rw [u_eq_uh, ← assoc, p_uh, assoc, Glue.pS_idem])

lemma isKarEquiv_unionΦ :
    IsKarEquiv (Glue.pU (σQ Q) (pairY Q) (pairZ Q)) (ph Q) (unionΦ Q) :=
  ⟨unionΨ Q, by simp only [coneMap_comp, (Q.map (atZero A)).p_idem, Glue.pS_idem],
    ⟨Homotopy.ofEq (by simp only [coneMap_comp, (Q.map (atZero A)).p_idem, Glue.pS_idem])⟩,
    ⟨Homotopy.ofEq (by simp only [coneMap_comp, (Q.map (atZero A)).p_idem, Glue.pS_idem])⟩⟩

lemma ph_coneToCoker : ph Q ≫ coneToCoker (splitYZ Q) =
    coneToCoker (splitYZ Q) ≫ (lineData A).map Q.p := by
  ext n : 1
  apply ext_from_X (uh Q) (n - 1) n (by simp)
  · simp
  · have := congrArg (fun f ↦ f.f n) (pS_unionα Q)
    simp only [comp_f] at this
    simp [this]

lemma unionΦ_coneToCoker : unionΦ Q ≫ ph Q ≫ coneToCoker (splitYZ Q) =
    Glue.pU (σQ Q) (pairY Q) (pairZ Q) ≫ unionF Q := by
  ext n : 1
  apply ext_from_X (Glue.u (σQ Q) (pairY Q) (pairZ Q)) (n - 1) n (by simp)
  · simp [unionF, Homotopy.ofEq]
  · have := congrArg (fun f ↦ f.f n) (Glue.pS_idem (pairY Q) (pairZ Q))
    simp only [comp_f] at this
    simp [unionF, reassoc_of% this]

lemma isKarEquiv_unionF :
    IsKarEquiv (Glue.pU (σQ Q) (pairY Q) (pairZ Q)) ((lineData A).map Q.p)
      (Glue.pU (σQ Q) (pairY Q) (pairZ Q) ≫ unionF Q) := by
  rw [← unionΦ_coneToCoker]
  exact (isKarEquiv_unionΦ Q).comp (isKarEquiv_of_homotopyEquiv (coneToCokerEquiv (splitYZ Q))
    (ph_idem Q) ((lineData A).sym Q).p_idem (ph_coneToCoker Q)) (Glue.pU_idem _ _ _) (ph_idem Q)
    ((lineData A).sym Q).p_idem

lemma pU_unionΦ : Glue.pU (σQ Q) (pairY Q) (pairZ Q) ≫ unionΦ Q = unionΦ Q := by
  simp only [coneMap_comp, (Q.map (atZero A)).p_idem, Glue.pS_idem]

lemma unionF_kar : Glue.pU (σQ Q) (pairY Q) (pairZ Q) ≫
    (Glue.pU (σQ Q) (pairY Q) (pairZ Q) ≫ unionF Q) ≫ (lineData A).map Q.p =
      Glue.pU (σQ Q) (pairY Q) (pairZ Q) ≫ unionF Q := by
  rw [← unionΦ_coneToCoker]
  simp only [assoc]
  rw [← ph_coneToCoker, reassoc_of% (ph_idem Q), reassoc_of% (pU_unionΦ Q)]

/-- The union structure pushed forward along `p_∪ ≫ F` is homotopic to `θ_{1/2,1/2} ≫ L(φ)`. -/
def unionConjKar : Homotopy (dualHom A.cz.inv (N + 1) (Glue.pU (σQ Q) (pairY Q) (pairZ Q) ≫
    unionF Q) ≫ ((pairY Q).union (pairZ Q)).φ ≫ (Glue.pU (σQ Q) (pairY Q) (pairZ Q) ≫ unionF Q))
      ((lineData A).sym Q).φ :=
  homotopyCongr (unionConj Q) (by
    have hk : dualHom A.cz.inv (N + 1) (Glue.pU (σQ Q) (pairY Q) (pairZ Q)) ≫
        unionφ (pairY Q) (pairZ Q) ≫ Glue.pU (σQ Q) (pairY Q) (pairZ Q) =
          unionφ (pairY Q) (pairZ Q) := ((pairY Q).union (pairZ Q)).φ_kar
    rw [dualHom_comp]
    simp only [assoc]
    rw [reassoc_of% hk]) rfl

end KarUnion

/-! ### The half-line splitting -/

section Main

variable {A : InvCat} {N : ℤ} (Q : SymPoincare A.inv N)

/-- **`Y ∪ Z ≃ Q ⊗ ℝ`**: the union of the two half-line pairs is homotopy isometric to the line
complex `(lineData A).sym Q`. -/
theorem nonempty_union_isometry :
    Nonempty (((pairY Q).union (pairZ Q)).HomotopyIsometry ((lineData A).sym Q)) := by
  obtain ⟨g, hg, ⟨H₁⟩, ⟨H₂⟩⟩ := isKarEquiv_unionF Q
  exact ⟨⟨_, g, unionF_kar Q, hg, H₂, H₁, unionConjKar Q⟩⟩

theorem cls_union_pairY_pairZ :
    Lconc.cls ((pairY Q).union (pairZ Q)) = Lconc.tensorLine A N (Lconc.cls Q) := by
  obtain ⟨e⟩ := nonempty_union_isometry Q
  rw [Lconc.cls_eq_of_isometry e, Lconc.tensorLine_cls]

lemma negHalf_pairY (r : ℤ) : negHalf A ((pairY Q).D.X r) :=
  cone_X_mem (negHalf A) ((negLine A).g Q.C)
    (fun _ ↦ Exists.intro (-1) fun _ hv ↦ isZero_cut_E _ _ (by omega))
    (fun _ ↦ Exists.intro 0 fun _ hv ↦ isZero_cut_E _ _ (by omega)) r

lemma posHalf_pairZ (r : ℤ) : posHalf A ((pairZ Q).D.X r) :=
  cone_X_mem (posHalf A) ((posLine A).g Q.C)
    (fun _ ↦ Exists.intro 0 fun _ hv ↦ isZero_cut_E _ _ (by omega))
    (fun _ ↦ Exists.intro 0 fun _ hv ↦ isZero_cut_E _ _ (by omega)) r

end Main

end CZ

/-- **The half-line splitting** (Kar form): every `N`-dimensional Poincaré complex `Q` over `A`
splits, placed at `0`, into a negative half-line pair `Y` and a positive half-line pair `Z` on
`-Q` with `[Y ∪ Z] = [Q ⊗ ℝ]`. -/
theorem halfLineSplitKar (A : InvCat) (N : ℤ) : HalfLineSplitKar A N := fun Q ↦
  ⟨CZ.pairY Q, CZ.pairZ Q, CZ.negHalf_pairY Q, CZ.posHalf_pairZ Q,
    Or.inl (CZ.cls_union_pairY_pairZ Q)⟩

/-- **The half-line splitting** (free form). -/
theorem halfLineSplit (A : InvCat) (N : ℤ) : HalfLineSplit A N := fun Q _ ↦
  halfLineSplitKar A N Q

end

end HSFormal.LTheory
