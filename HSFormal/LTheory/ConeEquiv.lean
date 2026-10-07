import HSFormal.LTheory.Pairs

/-!
# Mapping cones, homotopy equivalences and two-out-of-three (R2)

For chain complexes over a preadditive category with binary biproducts (no Kar idempotents):

* `homotopyEquivOfCone`/`coneContraction`: `f` is a homotopy equivalence iff `Cone(f)` is
  contractible (the forward direction uses the coherence-corrected homotopy `adjHomotopy`).
* `DegreewiseSplit i q`: degreewise split short exact sequences `0 ⟶ K ⟶ M ⟶ Q ⟶ 0`;
  `contractionLeft`/`contractionRight`: contractibility two-out-of-three, with explicit
  contractions.
* `DegreewiseSplit.cone`: the cones of a strictly commuting ladder form a degreewise split
  sequence; hence **R2** `homotopyEquivLeft`/`homotopyEquivRight` (cubical-review fix 4: via
  `0 ⟶ Cone(l) ⟶ Cone(m) ⟶ Cone(r) ⟶ 0`, not via `trianglehOfDegreewiseSplit`).
* `coneToCokerEquiv`: for degreewise split `j`, `Cone(j) ⟶ D/C` is a homotopy equivalence
  (manuscript l. 1009–1013: `τ = (s, -e)`, `h = k(1 - τq)`).
* `DegreewiseSplit.dual`, `dualHomotopyEquiv`: duals in the `Compression` conventions.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex homotopyCofiber

noncomputable section

universe v u

variable {V : Type u} [Category.{v} V] [Preadditive V] [HasBinaryBiproducts V]

lemma down_rel_succ (i : ℤ) : (ComplexShape.down ℤ).Rel (i + 1) i := by simp

lemma down_rel_pred (i : ℤ) : (ComplexShape.down ℤ).Rel i (i - 1) := by simp

section ConeContraction

variable {X Y : ChainComplex V ℤ} {f : X ⟶ Y} (H : Homotopy (𝟙 (cone f)) 0)

omit [HasBinaryBiproducts V] in
/-- The relation `ds + sd = 1` of a contraction. -/
lemma contraction_comm {K : ChainComplex V ℤ} (H : Homotopy (𝟙 K) 0) (i k l : ℤ)
    (hk : (ComplexShape.down ℤ).Rel i k) (hl : (ComplexShape.down ℤ).Rel l i) :
    𝟙 (K.X i) = K.d i k ≫ H.hom k i + H.hom i l ≫ K.d l i := by
  have h := H.comm i
  rw [dNext_eq _ hk, prevD_eq _ hl] at h
  simpa using h

/-- The homotopy inverse `g = inr^* s inl` extracted from a contraction `s` of `Cone(f)`. -/
@[simps]
def coneInv : Y ⟶ X where
  f i := inrX f i ≫ H.hom i (i + 1) ≫ fstX f (i + 1) i (down_rel_succ i)
  comm' i i' h := by
    obtain rfl : i = i' + 1 := by simp at h; omega
    have e := congrArg (fun φ ↦ inrX f (i' + 1) ≫ φ ≫ fstX f (i' + 1) i' (down_rel_succ i'))
      (contraction_comm H (i' + 1) i' (i' + 1 + 1) (down_rel_succ i') (down_rel_succ (i' + 1)))
    simp [d_fstX f _ _ _ (down_rel_succ (i' + 1)) (down_rel_succ i')] at e
    simp only [assoc]
    exact (add_neg_eq_zero.mp e.symm).symm

/-- `fg ≃ 1` from a contraction `s` of `Cone(f)`: the homotopy is `inl^* s inl`. -/
def coneInvHomotopyX : Homotopy (f ≫ coneInv H) (𝟙 X) :=
  homotopyCongr ((Homotopy.nullHomotopy' fun i j h ↦ inlX f i j h ≫ H.hom j (j + 1) ≫
    fstX f (j + 1) j (down_rel_succ j)).add (Homotopy.refl (𝟙 X))) (by
      ext i
      have e := congrArg (fun φ ↦ inlX f i (i + 1) (down_rel_succ i) ≫ φ ≫
        fstX f (i + 1) i (down_rel_succ i))
        (contraction_comm H (i + 1) i (i + 1 + 1) (down_rel_succ i) (down_rel_succ (i + 1)))
      simp [inlX_d_assoc f (i + 1) i (i - 1) (down_rel_succ i) (down_rel_pred i),
        d_fstX f _ _ _ (down_rel_succ (i + 1)) (down_rel_succ i)] at e
      rw [add_f_apply, Homotopy.nullHomotopicMap'_f (down_rel_succ i) (down_rel_pred i)]
      simp only [comp_f, coneInv_f, id_f, e, assoc]
      abel) (zero_add _)

/-- `gf ≃ 1` from a contraction `s` of `Cone(f)`: the homotopy is `-inr^* s inr`. -/
def coneInvHomotopyY : Homotopy (coneInv H ≫ f) (𝟙 Y) :=
  homotopyCongr ((Homotopy.nullHomotopy' fun i j _ ↦ -(inrX f i ≫ H.hom i j ≫
    sndX f j)).add (Homotopy.refl (𝟙 Y))) (by
      ext i
      have e := congrArg (fun φ ↦ inrX f i ≫ φ ≫ sndX f i)
        (contraction_comm H i (i - 1) (i + 1) (down_rel_pred i) (down_rel_succ i))
      simp [d_sndX f (i + 1) i (down_rel_succ i)] at e
      rw [add_f_apply, Homotopy.nullHomotopicMap'_f (down_rel_succ i) (down_rel_pred i)]
      simp only [comp_f, coneInv_f, id_f, e, assoc, comp_neg, neg_comp]
      abel) (zero_add _)

/-- **A map with contractible cone is a homotopy equivalence.** -/
@[simps]
def homotopyEquivOfCone : HomotopyEquiv X Y where
  hom := f
  inv := coneInv H
  homotopyHomInvId := coneInvHomotopyX H
  homotopyInvHomId := coneInvHomotopyY H

end ConeContraction

omit [HasBinaryBiproducts V] in
/-- The relation `φ - ψ = dH + Hd` of a homotopy, at chosen neighbouring indices. -/
lemma homotopy_comm {K L : ChainComplex V ℤ} {φ ψ : K ⟶ L} (H : Homotopy φ ψ) (i k l : ℤ)
    (hk : (ComplexShape.down ℤ).Rel i k) (hl : (ComplexShape.down ℤ).Rel l i) :
    φ.f i = K.d i k ≫ H.hom k i + H.hom i l ≫ L.d l i + ψ.f i := by
  rw [H.comm i, dNext_eq _ hk, prevD_eq _ hl]

section ConeOfEquiv

variable {X Y : ChainComplex V ℤ} (e : HomotopyEquiv X Y)

omit [HasBinaryBiproducts V] in
/-- The coherence-corrected homotopy `fg ≃ 1`, `h₂ + f h₁ g - h₂ f g` (Vogt's lemma). -/
def adjHomotopy : Homotopy (e.hom ≫ e.inv) (𝟙 X) :=
  let T₃ : Homotopy (e.hom ≫ e.inv ≫ e.hom ≫ e.inv) (e.hom ≫ e.inv) :=
    homotopyCongr (e.homotopyHomInvId.compRight (e.hom ≫ e.inv)) (by simp) (by simp)
  let T₂ : Homotopy (e.hom ≫ e.inv ≫ e.hom ≫ e.inv) (e.hom ≫ e.inv) :=
    homotopyCongr ((e.homotopyInvHomId.compLeft e.hom).compRight e.inv) (by simp) (by simp)
  (T₃.symm.trans T₂).trans e.homotopyHomInvId

omit [HasBinaryBiproducts V] in
lemma adjHomotopy_hom (i j : ℤ) :
    (adjHomotopy e).hom i j = -(e.homotopyHomInvId.hom i j ≫ e.hom.f j ≫ e.inv.f j) +
      e.hom.f i ≫ e.homotopyInvHomId.hom i j ≫ e.inv.f j + e.homotopyHomInvId.hom i j := by
  simp [adjHomotopy]

omit [HasBinaryBiproducts V] in
/-- The defect `f h₁ - h₂ f`, a degree-one cycle. -/
def defect (a b : ℤ) : X.X a ⟶ Y.X b :=
  e.hom.f a ≫ e.homotopyInvHomId.hom a b - e.homotopyHomInvId.hom a b ≫ e.hom.f b

omit [HasBinaryBiproducts V] in
lemma defect_anticomm (a b c : ℤ) (hab : (ComplexShape.down ℤ).Rel b a)
    (hca : (ComplexShape.down ℤ).Rel a c) :
    X.d a c ≫ defect e c a + defect e a b ≫ Y.d b a = 0 := by
  have h₁ := homotopy_comm e.homotopyInvHomId a c b hca hab
  have h₂ := homotopy_comm e.homotopyHomInvId a c b hca hab
  simp only [defect, comp_sub, sub_comp, assoc, ← e.hom.comm_assoc, e.hom.comm]
  simp only [comp_f, id_f] at h₁ h₂
  have : e.hom.f a ≫ (Y.d a c ≫ e.homotopyInvHomId.hom c a +
      e.homotopyInvHomId.hom a b ≫ Y.d b a) - (X.d a c ≫ e.homotopyHomInvId.hom c a +
      e.homotopyHomInvId.hom a b ≫ X.d b a) ≫ e.hom.f a = 0 := by
    rw [← sub_eq_iff_eq_add.mpr h₁, ← sub_eq_iff_eq_add.mpr h₂]
    simp
  rw [← this]
  simp only [comp_add, add_comp, assoc]
  abel

/-- The contraction of `Cone(f)` built from a homotopy equivalence. -/
def coneContractionHom (i j : ℤ) (h : (ComplexShape.down ℤ).Rel j i) :
    (cone e.hom).X i ⟶ (cone e.hom).X j :=
  fstX e.hom i (i - 1) (down_rel_pred i) ≫ ((adjHomotopy e).hom (i - 1) i ≫ inlX e.hom i j h -
      defect e (i - 1) i ≫ e.homotopyInvHomId.hom i j ≫ inrX e.hom j) +
    sndX e.hom i ≫ (e.inv.f i ≫ inlX e.hom i j h - e.homotopyInvHomId.hom i j ≫ inrX e.hom j)

lemma nullHomotopicMap'_coneContractionHom :
    Homotopy.nullHomotopicMap' (coneContractionHom e) = 𝟙 (cone e.hom) := by
  ext i
  rw [Homotopy.nullHomotopicMap'_f (down_rel_succ i) (down_rel_pred i)]
  apply ext_from_X e.hom (i - 1) i (down_rel_pred i)
  · apply ext_to_X e.hom i (i - 1) (down_rel_pred i)
    · simp [coneContractionHom, inlX_d_assoc e.hom i (i - 1) (i - 1 - 1) (down_rel_pred i)
        (down_rel_pred (i - 1)), d_fstX e.hom _ _ _ (down_rel_succ i) (down_rel_pred i)]
      have h := homotopy_comm (adjHomotopy e) (i - 1) (i - 1 - 1) i (down_rel_pred _)
        (down_rel_pred i)
      simp only [comp_f, id_f] at h
      rw [h]
      abel
    · simp [coneContractionHom, inlX_d_assoc e.hom i (i - 1) (i - 1 - 1) (down_rel_pred i)
        (down_rel_pred (i - 1)), d_sndX e.hom _ _ (down_rel_succ i)]
      have α := defect_anticomm e (i - 1) i (i - 1 - 1) (down_rel_pred i) (down_rel_pred (i - 1))
      have β := homotopy_comm e.homotopyInvHomId i (i - 1) (i + 1) (down_rel_pred i)
        (down_rel_succ i)
      simp only [comp_f, id_f] at β
      have β' : Y.d i (i - 1) ≫ e.homotopyInvHomId.hom (i - 1) i = e.inv.f i ≫ e.hom.f i -
          e.homotopyInvHomId.hom i (i + 1) ≫ Y.d (i + 1) i - 𝟙 _ := by
        rw [β]; abel
      rw [← assoc, eq_neg_of_add_eq_zero_left α]
      simp only [neg_comp, assoc, β']
      simp only [defect, adjHomotopy_hom, comp_sub, sub_comp, add_comp, assoc, neg_comp, comp_id]
      abel
  · apply ext_to_X e.hom i (i - 1) (down_rel_pred i)
    · simp [coneContractionHom, d_fstX e.hom _ _ _ (down_rel_succ i) (down_rel_pred i)]
    · simp [coneContractionHom, d_sndX e.hom _ _ (down_rel_succ i)]
      have β := homotopy_comm e.homotopyInvHomId i (i - 1) (i + 1) (down_rel_pred i)
        (down_rel_succ i)
      simp only [comp_f, id_f] at β
      rw [β]
      abel

/-- **The cone of a homotopy equivalence is contractible.** -/
def coneContraction : Homotopy (𝟙 (cone e.hom)) 0 :=
  homotopyCongr (Homotopy.nullHomotopy' (coneContractionHom e))
    (nullHomotopicMap'_coneContractionHom e) rfl

end ConeOfEquiv

section DegreewiseSplit

/-- A degreewise split short exact sequence `0 ⟶ K ⟶ M ⟶ Q ⟶ 0` of chain complexes: chain maps
`i`, `q` with a degreewise retraction `t` of `i` and section `s` of `q`, `ti + qs = 1`. -/
structure DegreewiseSplit {K M Q : ChainComplex V ℤ} (i : K ⟶ M) (q : M ⟶ Q) where
  t : ∀ n, M.X n ⟶ K.X n
  s : ∀ n, Q.X n ⟶ M.X n
  it : ∀ n, i.f n ≫ t n = 𝟙 _
  sq : ∀ n, s n ≫ q.f n = 𝟙 _
  total : ∀ n, t n ≫ i.f n + q.f n ≫ s n = 𝟙 _

namespace DegreewiseSplit

attribute [reassoc (attr := simp)] it sq

variable {K M Q : ChainComplex V ℤ} {i : K ⟶ M} {q : M ⟶ Q} (S : DegreewiseSplit i q)

omit [HasBinaryBiproducts V] in
@[simp]
lemma total_assoc (n : ℤ) {Z : V} (h : M.X n ⟶ Z) :
    S.t n ≫ i.f n ≫ h + q.f n ≫ S.s n ≫ h = h := by
  rw [← assoc, ← assoc, ← add_comp, S.total, id_comp]

include S in
omit [HasBinaryBiproducts V] in
@[reassoc (attr := simp)]
lemma i_q (n : ℤ) : i.f n ≫ q.f n = 0 := by
  have h : i.f n ≫ q.f n = i.f n ≫ q.f n + i.f n ≫ q.f n := by
    conv_lhs => rw [← id_comp (q.f n), ← S.total n]
    simp [add_comp]
  simpa using h

omit [HasBinaryBiproducts V] in
@[reassoc (attr := simp)]
lemma s_t (n : ℤ) : S.s n ≫ S.t n = 0 := by
  have h : S.s n ≫ S.t n = S.s n ≫ (S.t n ≫ i.f n + q.f n ≫ S.s n) ≫ S.t n := by
    rw [S.total, id_comp]
  simpa [comp_add, add_comp] using h

omit [HasBinaryBiproducts V] in
/-- `d t = t d + q s d t`. -/
lemma d_t (a b : ℤ) : M.d a b ≫ S.t b = S.t a ≫ K.d a b + q.f a ≫ S.s a ≫ M.d a b ≫ S.t b := by
  conv_lhs => rw [← id_comp (M.d a b), ← S.total a]
  simp [add_comp]

omit [HasBinaryBiproducts V] in
/-- `s d = d s + s d t i`. -/
lemma s_d (a b : ℤ) : S.s a ≫ M.d a b = Q.d a b ≫ S.s b + S.s a ≫ M.d a b ≫ S.t b ≫ i.f b := by
  conv_lhs => rw [← comp_id (M.d a b), ← S.total b, comp_add, comp_add, ← q.comm_assoc,
    S.sq_assoc]
  rw [add_comm]

omit [HasBinaryBiproducts V] in
include S in
/-- `g = i h_M q` anticommutes with the differentials. -/
@[reassoc]
lemma d_i_h_q (hM : Homotopy (𝟙 M) 0) (a b c : ℤ) (hab : (ComplexShape.down ℤ).Rel a b)
    (hca : (ComplexShape.down ℤ).Rel c a) :
    K.d a b ≫ i.f b ≫ hM.hom b a ≫ q.f a = -(i.f a ≫ hM.hom a c ≫ q.f c ≫ Q.d c a) := by
  have c₁ := contraction_comm hM a b c hab hca
  rw [← i.comm_assoc, ← assoc (M.d a b), eq_sub_of_add_eq c₁.symm]
  simp [sub_comp, q.comm, S.i_q]

omit [HasBinaryBiproducts V] in
/-- `θ = s d t` anticommutes with the differentials. -/
@[reassoc]
lemma s_d_t_d (a b c : ℤ) :
    S.s a ≫ M.d a b ≫ S.t b ≫ K.d b c = -(Q.d a b ≫ S.s b ≫ M.d b c ≫ S.t c) := by
  have e : S.t b ≫ K.d b c = M.d b c ≫ S.t c - q.f b ≫ S.s b ≫ M.d b c ≫ S.t c :=
    eq_sub_of_add_eq (S.d_t b c).symm
  rw [e, comp_sub, comp_sub, M.d_comp_d_assoc, ← q.comm_assoc, S.sq_assoc]
  simp

/-- **Two-out-of-three, left**: if `M` and `Q` are contractible, so is `K`. -/
def contractionLeft (hM : Homotopy (𝟙 M) 0) (hQ : Homotopy (𝟙 Q) 0) : Homotopy (𝟙 K) 0 :=
  homotopyCongr (Homotopy.nullHomotopy' fun a b _ ↦ i.f a ≫ hM.hom a b ≫ S.t b -
    i.f a ≫ hM.hom a b ≫ q.f b ≫ hQ.hom b (b + 1) ≫ S.s (b + 1) ≫ M.d (b + 1) b ≫ S.t b) (by
      ext n
      rw [Homotopy.nullHomotopicMap'_f (down_rel_succ n) (down_rel_pred n)]
      have c₁ := contraction_comm hM n (n - 1) (n + 1) (down_rel_pred n) (down_rel_succ n)
      have c₂ := contraction_comm hQ (n + 1) n (n + 1 + 1) (down_rel_succ n)
        (down_rel_succ (n + 1))
      have e₁ : S.t (n + 1) ≫ K.d (n + 1) n = M.d (n + 1) n ≫ S.t n -
          q.f (n + 1) ≫ S.s (n + 1) ≫ M.d (n + 1) n ≫ S.t n :=
        eq_sub_of_add_eq (S.d_t (n + 1) n).symm
      have I : K.d n (n - 1) ≫ i.f (n - 1) ≫ hM.hom (n - 1) n ≫ S.t n +
          i.f n ≫ hM.hom n (n + 1) ≫ S.t (n + 1) ≫ K.d (n + 1) n = 𝟙 _ -
          i.f n ≫ hM.hom n (n + 1) ≫ q.f (n + 1) ≫ S.s (n + 1) ≫ M.d (n + 1) n ≫ S.t n := by
        rw [← i.comm_assoc, e₁, ← assoc (M.d n (n - 1)), eq_sub_of_add_eq c₁.symm]
        simp only [sub_comp, comp_sub, assoc, id_comp, S.it]
        abel
      have II : K.d n (n - 1) ≫ i.f (n - 1) ≫ hM.hom (n - 1) n ≫ q.f n ≫ hQ.hom n (n + 1) ≫
          S.s (n + 1) ≫ M.d (n + 1) n ≫ S.t n + i.f n ≫ hM.hom n (n + 1) ≫ q.f (n + 1) ≫
          hQ.hom (n + 1) (n + 1 + 1) ≫ S.s (n + 1 + 1) ≫ M.d (n + 1 + 1) (n + 1) ≫ S.t (n + 1) ≫
          K.d (n + 1) n = -(i.f n ≫ hM.hom n (n + 1) ≫ q.f (n + 1) ≫ S.s (n + 1) ≫
          M.d (n + 1) n ≫ S.t n) := by
        rw [S.d_i_h_q_assoc hM n (n - 1) (n + 1) (down_rel_pred n) (down_rel_succ n),
          S.s_d_t_d]
        conv_rhs => rw [← id_comp (S.s (n + 1)), c₂]
        simp only [add_comp, comp_add, assoc, neg_comp, comp_neg]
        abel
      simp only [comp_sub, sub_comp, assoc, id_f]
      rw [sub_add_sub_comm, I, II]
      abel) (by simp)

/-- **Two-out-of-three, right**: if `K` and `M` are contractible, so is `Q`. -/
def contractionRight (hK : Homotopy (𝟙 K) 0) (hM : Homotopy (𝟙 M) 0) : Homotopy (𝟙 Q) 0 :=
  homotopyCongr (Homotopy.nullHomotopy' fun a b _ ↦ S.s a ≫ hM.hom a b ≫ q.f b -
    S.s a ≫ M.d a (a - 1) ≫ S.t (a - 1) ≫ hK.hom (a - 1) a ≫ i.f a ≫ hM.hom a b ≫ q.f b) (by
      ext n
      rw [Homotopy.nullHomotopicMap'_f (down_rel_succ n) (down_rel_pred n)]
      have c₁ := contraction_comm hM n (n - 1) (n + 1) (down_rel_pred n) (down_rel_succ n)
      have c₃ := contraction_comm hK (n - 1) (n - 1 - 1) n (down_rel_pred (n - 1))
        (down_rel_pred n)
      have e₁ : Q.d n (n - 1) ≫ S.s (n - 1) = S.s n ≫ M.d n (n - 1) -
          S.s n ≫ M.d n (n - 1) ≫ S.t (n - 1) ≫ i.f (n - 1) :=
        eq_sub_of_add_eq (S.s_d n (n - 1)).symm
      have I : Q.d n (n - 1) ≫ S.s (n - 1) ≫ hM.hom (n - 1) n ≫ q.f n +
          S.s n ≫ hM.hom n (n + 1) ≫ q.f (n + 1) ≫ Q.d (n + 1) n = 𝟙 _ -
          S.s n ≫ M.d n (n - 1) ≫ S.t (n - 1) ≫ i.f (n - 1) ≫ hM.hom (n - 1) n ≫ q.f n := by
        rw [← assoc, e₁, q.comm, ← assoc (hM.hom n (n + 1)), ← assoc (S.s n),
          eq_sub_of_add_eq' c₁.symm]
        simp only [sub_comp, comp_sub, assoc, id_comp, S.sq]
        abel
      have e₂ : Q.d n (n - 1) ≫ S.s (n - 1) ≫ M.d (n - 1) (n - 1 - 1) ≫ S.t (n - 1 - 1) =
          -(S.s n ≫ M.d n (n - 1) ≫ S.t (n - 1) ≫ K.d (n - 1) (n - 1 - 1)) := by
        rw [S.s_d_t_d, neg_neg]
      have e₃ : i.f n ≫ hM.hom n (n + 1) ≫ q.f (n + 1) ≫ Q.d (n + 1) n =
          -(K.d n (n - 1) ≫ i.f (n - 1) ≫ hM.hom (n - 1) n ≫ q.f n) := by
        rw [S.d_i_h_q hM n (n - 1) (n + 1) (down_rel_pred n) (down_rel_succ n), neg_neg]
      have II : Q.d n (n - 1) ≫ S.s (n - 1) ≫ M.d (n - 1) (n - 1 - 1) ≫ S.t (n - 1 - 1) ≫
          hK.hom (n - 1 - 1) (n - 1) ≫ i.f (n - 1) ≫ hM.hom (n - 1) n ≫ q.f n +
          S.s n ≫ M.d n (n - 1) ≫ S.t (n - 1) ≫ hK.hom (n - 1) n ≫ i.f n ≫ hM.hom n (n + 1) ≫
          q.f (n + 1) ≫ Q.d (n + 1) n = -(S.s n ≫ M.d n (n - 1) ≫ S.t (n - 1) ≫ i.f (n - 1) ≫
          hM.hom (n - 1) n ≫ q.f n) := by
        rw [e₃, reassoc_of% e₂]
        conv_rhs => rw [← id_comp (i.f (n - 1)), c₃]
        simp only [add_comp, comp_add, assoc, neg_comp, comp_neg]
        abel
      simp only [comp_sub, sub_comp, assoc, id_f]
      rw [sub_add_sub_comm, I, II]
      abel) (by simp)

end DegreewiseSplit

end DegreewiseSplit



section Ladder

variable {K M Q K' M' Q' : ChainComplex V ℤ} {i : K ⟶ M} {q : M ⟶ Q} {i' : K' ⟶ M'}
  {q' : M' ⟶ Q'} (S : DegreewiseSplit i q) (S' : DegreewiseSplit i' q')

/-- The cones of a strictly commuting ladder of degreewise split sequences form a degreewise split
sequence `0 ⟶ Cone(l) ⟶ Cone(m) ⟶ Cone(r) ⟶ 0`. -/
@[simps]
def DegreewiseSplit.cone {l : K ⟶ K'} {m : M ⟶ M'} {r : Q ⟶ Q'} (h₁ : i ≫ m = l ≫ i')
    (h₂ : q ≫ r = m ≫ q') :
    DegreewiseSplit (coneMap (j := l) (j' := m) i i' h₁) (coneMap (j := m) (j' := r) q q' h₂) where
  t n := fstX m n (n - 1) (down_rel_pred n) ≫ S.t (n - 1) ≫ inlX l (n - 1) n (down_rel_pred n) +
    sndX m n ≫ S'.t n ≫ inrX l n
  s n := fstX r n (n - 1) (down_rel_pred n) ≫ S.s (n - 1) ≫ inlX m (n - 1) n (down_rel_pred n) +
    sndX r n ≫ S'.s n ≫ inrX m n
  it n := by apply ext_from_X l (n - 1) n (down_rel_pred n) <;> simp
  sq n := by apply ext_from_X r (n - 1) n (down_rel_pred n) <;> simp
  total n := by
    apply ext_from_X m (n - 1) n (down_rel_pred n)
    · simp [add_comp]
    · simp [add_comp]

/-- **Two-out-of-three (R2), left**: for a strictly commuting ladder of degreewise split
sequences whose middle and right maps are homotopy equivalences, the left map `l` is one
(cubical-review fix 4: via `0 ⟶ Cone(l) ⟶ Cone(m) ⟶ Cone(r) ⟶ 0`). -/
def homotopyEquivLeft (em : HomotopyEquiv M M') (er : HomotopyEquiv Q Q') (l : K ⟶ K')
    (h₁ : i ≫ em.hom = l ≫ i') (h₂ : q ≫ er.hom = em.hom ≫ q') : HomotopyEquiv K K' :=
  homotopyEquivOfCone ((S.cone S' h₁ h₂).contractionLeft (coneContraction em)
    (coneContraction er))

@[simp]
lemma homotopyEquivLeft_hom (em : HomotopyEquiv M M') (er : HomotopyEquiv Q Q') (l : K ⟶ K')
    (h₁ : i ≫ em.hom = l ≫ i') (h₂ : q ≫ er.hom = em.hom ≫ q') :
    (homotopyEquivLeft S S' em er l h₁ h₂).hom = l := rfl

/-- **Two-out-of-three (R2), right**: if the left and middle maps of the ladder are homotopy
equivalences, so is the right map `r`. -/
def homotopyEquivRight (el : HomotopyEquiv K K') (em : HomotopyEquiv M M') (r : Q ⟶ Q')
    (h₁ : i ≫ em.hom = el.hom ≫ i') (h₂ : q ≫ r = em.hom ≫ q') : HomotopyEquiv Q Q' :=
  homotopyEquivOfCone ((S.cone S' h₁ h₂).contractionRight (coneContraction el)
    (coneContraction em))

@[simp]
lemma homotopyEquivRight_hom (el : HomotopyEquiv K K') (em : HomotopyEquiv M M') (r : Q ⟶ Q')
    (h₁ : i ≫ em.hom = el.hom ≫ i') (h₂ : q ≫ r = em.hom ≫ q') :
    (homotopyEquivRight S S' el em r h₁ h₂).hom = r := rfl

end Ladder

section SplitMono

variable {C D R : ChainComplex V ℤ} {j : C ⟶ D} {q : D ⟶ R} (S : DegreewiseSplit j q)

/-- The projection `Cone(j) ⟶ R = D/C`, `(x, c) ↦ q x`. -/
@[simps]
def coneToCoker : cone j ⟶ R where
  f n := sndX j n ≫ q.f n
  comm' n n' h := by simp [d_sndX_assoc j n n' h, S.i_q]

/-- The inverse `τ = (s, -e)` with `je = d s - s d` (l. 1009). -/
@[simps]
def cokerToCone : R ⟶ cone j where
  f n := S.s n ≫ inrX j n - (S.s n ≫ D.d n (n - 1) ≫ S.t (n - 1)) ≫ inlX j (n - 1) n
    (down_rel_pred n)
  comm' n n' h := by
    obtain rfl : n' = n - 1 := by simp at h; omega
    apply ext_to_X j (n - 1) (n - 1 - 1) (down_rel_pred _)
    · simp [d_fstX j n (n - 1) (n - 1 - 1) h (down_rel_pred _), S.s_d_t_d]
    · simp [d_sndX j n (n - 1) h, S.s_d n (n - 1)]

lemma cokerToCone_coneToCoker : cokerToCone S ≫ coneToCoker S = 𝟙 R := by
  ext n; simp

/-- **The cone of a degreewise split mono is its cokernel**: `Cone(j) ⟶ D/C` is a homotopy
equivalence, with homotopy `h = k(1 - τq)`, `k(x, c) = (0, t x)` (l. 1009–1013). -/
def coneToCokerEquiv : HomotopyEquiv (cone j) R where
  hom := coneToCoker S
  inv := cokerToCone S
  homotopyHomInvId := homotopyCongr ((Homotopy.nullHomotopy' fun a b h ↦
    -(sndX j a ≫ S.t a ≫ inlX j a b h)).add (Homotopy.refl (𝟙 (cone j)))) (by
      ext n
      rw [add_f_apply, Homotopy.nullHomotopicMap'_f (down_rel_succ n) (down_rel_pred n)]
      apply ext_from_X j (n - 1) n (down_rel_pred n)
      · apply ext_to_X j n (n - 1) (down_rel_pred n)
        · simp [inlX_d_assoc j n (n - 1) (n - 1 - 1) (down_rel_pred n) (down_rel_pred _)]
        · simp [inlX_d_assoc j n (n - 1) (n - 1 - 1) (down_rel_pred n) (down_rel_pred _)]
      · apply ext_to_X j n (n - 1) (down_rel_pred n)
        · simp [d_fstX j _ _ _ (down_rel_succ n) (down_rel_pred n)]
          nth_rewrite 1 [S.d_t n (n - 1)]
          abel
        · simp [d_sndX j _ _ (down_rel_succ n)]
          rw [← S.total n]
          abel) (zero_add _)
  homotopyInvHomId := Homotopy.ofEq (cokerToCone_coneToCoker S)

end SplitMono

section Dual

open HSFormal.Compression

variable (J : StrictInvolution V) (N : ℤ)

omit [HasBinaryBiproducts V] in
/-- The `N`-dual of a degreewise split sequence `0 ⟶ K ⟶ M ⟶ Q ⟶ 0` is the degreewise split
sequence `0 ⟶ Q^{N-*} ⟶ M^{N-*} ⟶ K^{N-*} ⟶ 0`. -/
@[simps]
def DegreewiseSplit.dual {K M Q : ChainComplex V ℤ} {i : K ⟶ M} {q : M ⟶ Q}
    (S : DegreewiseSplit i q) : DegreewiseSplit (dualHom J N q) (dualHom J N i) where
  t n := J.star (S.s (N - n))
  s n := J.star (S.t (N - n))
  it n := by simp [← J.star_comp]
  sq n := by simp [← J.star_comp]
  total n := by
    simp only [dualHom_f, ← J.star_comp, ← J.star_add]
    rw [add_comm, S.total]
    exact J.star_id _

omit [HasBinaryBiproducts V] in
/-- The dual `Y^{N-*} ≃ X^{N-*}` of a homotopy equivalence. -/
@[simps]
def dualHomotopyEquiv {X Y : ChainComplex V ℤ} (e : HomotopyEquiv X Y) :
    HomotopyEquiv (dualComplex J N Y) (dualComplex J N X) where
  hom := dualHom J N e.hom
  inv := dualHom J N e.inv
  homotopyHomInvId := homotopyCongr (dualHomotopy J N e.homotopyInvHomId) (by simp) (by simp)
  homotopyInvHomId := homotopyCongr (dualHomotopy J N e.homotopyHomInvId) (by simp) (by simp)

end Dual

end

end HSFormal.LTheory
