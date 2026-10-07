import HSFormal.LTheory.Model.Transport
import HSFormal.LTheory.Model.GlueHomotopy

/-!
# Cones of degreewise split surjections and pairs with vanishing relative structure

Support for the union relation (R) (`Model/UnionRel.lean`).

* `KarSplit.d_t`, `KarSplit.s_d_t_d`, …: the identities of a Kar degreewise split sequence
  `0 ⟶ K ⟶ M ⟶ Q ⟶ 0` (Kar versions of `DegreewiseSplit.d_t`, …).
* `KarSplit.isKarEquiv_coneDualFst` (**G1**): for such a sequence, the restriction
  `Cone(q)^{n+1-*} ⟶ K^{n-*}` to the kernel (`coneDualFst`) is a Kar equivalence
  (`Cone(q) ≃ ΣK`; the inverse is the dual of `(x, w) ↦ t x + t d s w`, the homotopy the dual of
  `(x, w) ↦ (s w, 0)`).
* `KarSplit.relDuality_eq` (**P2**): if a structure `φ : M^{n-*} ⟶ M` satisfies
  `q^* φ q = 0`, the relative duality map of the pair `(q : M ⟶ Q, (0, φ))` factors strictly as
  `-(coneDualFst ≫ λ)` with `λ = t^* φ q : K^{n-*} ⟶ Q` (a chain map), so the pair is Poincaré
  as soon as `λ` is a Kar equivalence (`KarSplit.isKarEquiv_relDuality`).
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex homotopyCofiber
  HSFormal.Compression

noncomputable section

universe v u

variable {V : Type u} [Category.{v} V] [Preadditive V]

namespace KarSplit

variable {K M Q : ChainComplex V ℤ} {eK : K ⟶ K} {eM : M ⟶ M} {eQ : Q ⟶ Q} {i : K ⟶ M}
  {q : M ⟶ Q} (S : KarSplit eK eM eQ i q)

section Identities

variable (heK : eK ≫ eK = eK) (heM : eM ≫ eM = eM) (heQ : eQ ≫ eQ = eQ)
  (hi : eK ≫ i ≫ eM = i) (hq : eM ≫ q ≫ eQ = q)

include heK in
@[reassoc]
lemma t_eK (n : ℤ) : S.t n ≫ eK.f n = S.t n := by
  rw [← S.t_kar n]; simp [idem_f heK]

include heM in
@[reassoc]
lemma eM_t (n : ℤ) : eM.f n ≫ S.t n = S.t n := by
  rw [← S.t_kar n]; simp [idem_f_assoc heM]

include heM in
@[reassoc]
lemma s_eM (n : ℤ) : S.s n ≫ eM.f n = S.s n := by
  rw [← S.s_kar n]; simp [idem_f heM]

include heQ in
@[reassoc]
lemma eQ_s (n : ℤ) : eQ.f n ≫ S.s n = S.s n := by
  rw [← S.s_kar n]; simp [idem_f_assoc heQ]

include heK heM heQ in
@[reassoc]
lemma s_t (n : ℤ) : S.s n ≫ S.t n = 0 := by
  have h : S.s n ≫ S.t n = S.s n ≫ (S.t n ≫ i.f n + q.f n ≫ S.s n) ≫ S.t n := by
    rw [S.total, S.s_eM_assoc heM]
  rw [add_comp, comp_add, assoc, assoc, S.it, S.t_eK heK, ← assoc (S.s n) (q.f n), S.sq,
    S.eQ_s_assoc heQ] at h
  simpa using h

include heK hi in
@[reassoc]
lemma i_t (n : ℤ) : eK.f n ≫ i.f n = i.f n := kar_left_f heK hi n

include heM hi in
@[reassoc]
lemma i_eM (n : ℤ) : i.f n ≫ eM.f n = i.f n := kar_right_f heM hi n

include heQ hq in
@[reassoc]
lemma q_eQ (n : ℤ) : q.f n ≫ eQ.f n = q.f n := kar_right_f heQ hq n

include heM hq in
@[reassoc]
lemma eM_q (n : ℤ) : eM.f n ≫ q.f n = q.f n := kar_left_f heM hq n

include S heK heM heQ hi hq in
@[reassoc]
lemma i_q (n : ℤ) : i.f n ≫ q.f n = 0 := by
  have h : i.f n ≫ q.f n = i.f n ≫ (S.t n ≫ i.f n + q.f n ≫ S.s n) ≫ q.f n := by
    rw [S.total, i_eM_assoc heM hi]
  rw [add_comp, comp_add, assoc, assoc, ← assoc (i.f n) (S.t n), S.it, i_t_assoc heK hi,
    S.sq, q_eQ heQ hq] at h
  simpa using h

include heK heM in
/-- `d t = t d + q s d t`. -/
lemma d_t (a b : ℤ) : M.d a b ≫ S.t b = S.t a ≫ K.d a b + q.f a ≫ S.s a ≫ M.d a b ≫ S.t b := by
  have h : M.d a b ≫ S.t b = eM.f a ≫ M.d a b ≫ S.t b := by
    rw [Hom.comm_assoc, S.eM_t heM]
  have h₂ : S.t a ≫ i.f a ≫ M.d a b ≫ S.t b = S.t a ≫ K.d a b := by
    rw [Hom.comm_assoc, S.it, ← Hom.comm, S.t_eK_assoc heK]
  conv_lhs => rw [h, ← S.total a, add_comp, assoc, assoc, h₂]

include heK heM in
/-- `t d = d t - q s d t`. -/
lemma t_d (a b : ℤ) : S.t a ≫ K.d a b = M.d a b ≫ S.t b - q.f a ≫ S.s a ≫ M.d a b ≫ S.t b :=
  eq_sub_of_add_eq (S.d_t heK heM a b).symm

include heK heM heQ in
/-- `θ = s d t` anticommutes with the differentials. -/
@[reassoc]
lemma s_d_t_d (a b c : ℤ) :
    S.s a ≫ M.d a b ≫ S.t b ≫ K.d b c = -(Q.d a b ≫ S.s b ≫ M.d b c ≫ S.t c) := by
  rw [S.t_d heK heM b c, comp_sub, comp_sub, M.d_comp_d_assoc, ← q.comm_assoc, ← assoc (S.s a) (q.f a), S.sq,
    Hom.comm_assoc, S.eQ_s_assoc heQ]
  simp

include heM heQ in
/-- `s d = d s + s d t i`. -/
@[reassoc]
lemma d_s (a b : ℤ) :
    S.s a ≫ M.d a b = Q.d a b ≫ S.s b + S.s a ≫ M.d a b ≫ S.t b ≫ i.f b := by
  have h : S.s a ≫ M.d a b = S.s a ≫ M.d a b ≫ eM.f b := by
    rw [← Hom.comm, S.s_eM_assoc heM]
  rw [h, ← S.total b, comp_add, comp_add, ← q.comm_assoc, ← assoc (S.s a) (q.f a), S.sq,
    Hom.comm_assoc, S.eQ_s heQ, add_comm]

end Identities

/-! ### The cone of `q` and the suspension of the kernel -/

section Cone

variable [HasBinaryBiproducts V] (heK : eK ≫ eK = eK) (heM : eM ≫ eM = eM)
  (heQ : eQ ≫ eQ = eQ) (hi : eK ≫ i ≫ eM = i) (hq : eM ≫ q ≫ eQ = q)

/-- The component `(x, w) ↦ t x + t d s w` of the retraction `Cone(q)_a ⟶ K_b` (`a = b + 1`). -/
def ρ (a b : ℤ) (h : (ComplexShape.down ℤ).Rel a b) : (cone q).X a ⟶ K.X b :=
  fstX q a b h ≫ S.t b + sndX q a ≫ S.s a ≫ M.d a b ≫ S.t b

lemma ρ_eq (a b b' : ℤ) (h : (ComplexShape.down ℤ).Rel a b)
    (h' : (ComplexShape.down ℤ).Rel a b') :
    S.ρ a b' h' = S.ρ a b h ≫ (K.XIsoOfEq (by simp at h h'; omega : b = b')).hom := by
  obtain rfl : b' = b := by simp at h h'; omega
  simp

@[reassoc (attr := simp)]
lemma inlX_ρ (a b : ℤ) (h : (ComplexShape.down ℤ).Rel a b) :
    inlX q b a h ≫ S.ρ a b h = S.t b := by
  simp [ρ]

@[reassoc (attr := simp)]
lemma inrX_ρ (a b : ℤ) (h : (ComplexShape.down ℤ).Rel a b) :
    inrX q a ≫ S.ρ a b h = S.s a ≫ M.d a b ≫ S.t b := by
  simp [ρ]

include heK heM heQ in
/-- `ρ` anticommutes with the differentials (it is a chain map `Cone(q) ⟶ ΣK`). -/
lemma d_ρ (a b c : ℤ) (hab : (ComplexShape.down ℤ).Rel a b)
    (hbc : (ComplexShape.down ℤ).Rel b c) :
    (cone q).d a b ≫ S.ρ b c hbc = -(S.ρ a b hab ≫ K.d b c) := by
  apply ext_from_X q b a hab
  · rw [homotopyCofiber_d, inlX_d_assoc q a b c hab hbc]
    simp only [add_comp, assoc, inlX_ρ, inrX_ρ, neg_comp, inlX_ρ_assoc, comp_neg]
    rw [S.t_d heK heM b c]
    abel
  · rw [homotopyCofiber_d, inrX_d_assoc]
    simp only [inrX_ρ, inrX_ρ_assoc, comp_neg]
    rw [S.s_d_t_d heK heM heQ]
    simp

include heM heQ in
lemma coneMap_ρ (hc : eM ≫ q = q ≫ eQ) (a b : ℤ) (h : (ComplexShape.down ℤ).Rel a b) :
    (coneMap eM eQ hc).f a ≫ S.ρ a b h = S.ρ a b h := by
  simp [ρ, coneMap_f_fstX_assoc, coneMap_f_sndX_assoc, S.eM_t heM, S.eQ_s_assoc heQ]

include heK in
lemma ρ_eK (a b : ℤ) (h : (ComplexShape.down ℤ).Rel a b) :
    S.ρ a b h ≫ eK.f b = S.ρ a b h := by
  simp [ρ, add_comp, S.t_eK heK]

/-- The null-homotopy `(x, w) ↦ (s w, 0)`. -/
def hcone (a b : ℤ) (h : (ComplexShape.down ℤ).Rel b a) : (cone q).X a ⟶ (cone q).X b :=
  sndX q a ≫ S.s a ≫ inlX q a b h

/-- `Π = p_{Cone} - (dh + hd)`, the composite `Cone(q) ⟶ ΣK ⟶ Cone(q)`. -/
def conePi (hc : eM ≫ q = q ≫ eQ) : cone q ⟶ cone q :=
  coneMap eM eQ hc - Homotopy.nullHomotopicMap' S.hcone

include heM heQ in
lemma conePi_f (hc : eM ≫ q = q ≫ eQ) (m m' : ℤ) (h : (ComplexShape.down ℤ).Rel m m') :
    (S.conePi hc).f m = S.ρ m m' h ≫ i.f m' ≫ inlX q m' m h := by
  obtain rfl : m' = m - 1 := by simp at h; omega
  rw [conePi, sub_f_apply, Homotopy.nullHomotopicMap'_f (down_rel_succ m) (down_rel_pred m)]
  apply ext_from_X q (m - 1) m h
  · simp only [hcone, comp_sub, comp_add, inlX_coneMap_f, homotopyCofiber_d,
      inlX_d_assoc q m (m - 1) (m - 1 - 1) h (down_rel_pred (m - 1)), add_comp, neg_comp, assoc,
      inlX_sndX_assoc, zero_comp, inrX_sndX_assoc, comp_zero, neg_zero, zero_add, add_zero,
      inlX_ρ_assoc]
    rw [← S.total (m - 1), add_comp, assoc, assoc]
    exact add_sub_cancel_right _ _
  · simp only [hcone, comp_sub, comp_add, inrX_coneMap_f, homotopyCofiber_d, inrX_d_assoc,
      inrX_sndX_assoc, assoc, inlX_d q (m + 1) m (m - 1) (down_rel_succ m) h, comp_neg,
      inrX_ρ_assoc]
    rw [S.d_s_assoc heM heQ m (m - 1) (inlX q (m - 1) m h), ← assoc (S.s m) (q.f m), S.sq]
    simp only [add_comp, assoc, neg_add]
    rw [sub_eq_iff_eq_add]
    abel

/-- `p_{Cone(q)} ≃ Π` by the null-homotopy `(x, w) ↦ (s w, 0)`. -/
def conePiHomotopy (hc : eM ≫ q = q ≫ eQ) : Homotopy (coneMap eM eQ hc) (S.conePi hc) :=
  homotopyCongr ((Homotopy.nullHomotopy' S.hcone).add (Homotopy.refl (S.conePi hc)))
    (by rw [conePi]; abel) (zero_add _)

end Cone

/-! ### G1: `Cone(q)^{n+1-*} ≃ K^{n-*}` -/

section Dual

variable [HasBinaryBiproducts V] {J : StrictInvolution V} {n : ℤ} (heK : eK ≫ eK = eK)
  (heM : eM ≫ eM = eM) (heQ : eQ ≫ eQ = eQ)

include heK heM heQ in
/-- The dual `(-1)^r ρ^*` of the retraction `Cone(q) ⟶ ΣK`: a chain map
`K^{n-*} ⟶ Cone(q)^{n+1-*}`. -/
def coneDualInv : dualComplex J n K ⟶ dualComplex J (n + 1) (cone q) where
  f r := r.negOnePow • J.star (S.ρ (n + 1 - r) (n - r) (down_rel_sub n r))
  comm' r r' h := by
    obtain rfl : r = r' + 1 := by simp at h; omega
    have hab : (ComplexShape.down ℤ).Rel (n + 1 - r') (n + 1 - (r' + 1)) := by simp; omega
    simp only [dualComplex_d, Linear.units_smul_comp, Linear.comp_units_smul, smul_smul,
      ← J.star_comp]
    rw [S.d_ρ heK heM heQ _ _ _ hab (down_rel_sub n (r' + 1)),
      S.ρ_eq _ _ _ hab (down_rel_sub n r'), assoc, XIsoOfEq_hom_comp_d, J.star_neg, smul_neg,
      Int.units_mul_self, Int.negOnePow_succ, mul_neg, Int.units_mul_self, Units.neg_smul]

@[simp]
lemma coneDualInv_f (r : ℤ) : (S.coneDualInv heK heM heQ (J := J) (n := n)).f r =
    r.negOnePow • J.star (S.ρ (n + 1 - r) (n - r) (down_rel_sub n r)) := rfl

variable (hi : eK ≫ i ≫ eM = i) (hq : eM ≫ q ≫ eQ = q)

lemma coneDualInv_comp_coneDualFst (hiq : i ≫ q = 0) :
    S.coneDualInv heK heM heQ ≫ coneDualFst (J := J) (N := n) q i hiq = dualHom J n eK := by
  ext r
  simp only [comp_f, coneDualInv_f, coneDualFst_f, Linear.units_smul_comp, Linear.comp_units_smul,
    smul_smul, Int.units_mul_self, one_smul, ← J.star_comp, assoc, inlX_ρ, S.it, dualHom_f]

lemma coneDualFst_comp_coneDualInv (hc : eM ≫ q = q ≫ eQ) (hiq : i ≫ q = 0) :
    coneDualFst (J := J) (N := n) q i hiq ≫ S.coneDualInv heK heM heQ =
      dualHom J (n + 1) (S.conePi hc) := by
  ext r
  simp only [comp_f, coneDualInv_f, coneDualFst_f, Linear.units_smul_comp, Linear.comp_units_smul,
    smul_smul, Int.units_mul_self, one_smul, ← J.star_comp, assoc, dualHom_f,
    S.conePi_f heM heQ hc (n + 1 - r) (n - r) (down_rel_sub n r)]

include S heK heM heQ in
/-- **G1**: for a Kar degreewise split sequence `0 ⟶ K ⟶ M ⟶ Q ⟶ 0`, the restriction
`Cone(q)^{n+1-*} ⟶ K^{n-*}` to the kernel is a Kar equivalence (`Cone(q) ≃ ΣK`). -/
theorem isKarEquiv_coneDualFst (hc : eM ≫ q = q ≫ eQ) (hiq : i ≫ q = 0) :
    IsKarEquiv (dualHom J (n + 1) (coneMap eM eQ hc)) (dualHom J n eK)
      (coneDualFst (J := J) (N := n) q i hiq) := by
  refine ⟨S.coneDualInv heK heM heQ, ?_,
    ⟨Homotopy.ofEq (S.coneDualInv_comp_coneDualFst heK heM heQ hiq)⟩, ⟨?_⟩⟩
  · ext r
    simp only [comp_f, coneDualInv_f, dualHom_f, Linear.units_smul_comp, Linear.comp_units_smul,
      ← J.star_comp, assoc, S.ρ_eK heK, S.coneMap_ρ heM heQ hc]
  · rw [S.coneDualFst_comp_coneDualInv heK heM heQ hc hiq]
    exact (dualHomotopy J (n + 1) (S.conePiHomotopy hc)).symm

/-! ### P2: pairs with vanishing relative structure -/

variable (φ : dualComplex J n M ⟶ M) (hφ0 : dualHom J n q ≫ φ ≫ q = 0)

include hφ0 in
lemma star_q_φ_q (r : ℤ) : J.star (q.f (n - r)) ≫ φ.f r ≫ q.f r = 0 := by
  have := congrArg (fun f ↦ f.f r) hφ0
  simpa only [comp_f, dualHom_f, zero_f] using this

include heK heM hφ0 in
/-- `λ = t^* φ q : K^{n-*} ⟶ Q`, a chain map since `q^* φ q = 0`. -/
def lam : dualComplex J n K ⟶ Q where
  f r := J.star (S.t (n - r)) ≫ φ.f r ≫ q.f r
  comm' r r' h := by
    obtain rfl : r = r' + 1 := by simp at h; omega
    have e : J.star (S.t (n - (r' + 1))) ≫ J.star (M.d (n - r') (n - (r' + 1))) =
        J.star (K.d (n - r') (n - (r' + 1))) ≫ J.star (S.t (n - r')) +
          (J.star (S.t (n - (r' + 1))) ≫ J.star (M.d (n - r') (n - (r' + 1))) ≫
            J.star (S.s (n - r'))) ≫ J.star (q.f (n - r')) := by
      conv_lhs => rw [← J.star_comp, S.d_t heK heM, J.star_add]
      simp only [J.star_comp, assoc]
    simp only [assoc]
    rw [Hom.comm, Hom.comm_assoc φ]
    simp only [dualComplex_d]
    rw [Linear.units_smul_comp, Linear.units_smul_comp, Linear.comp_units_smul, reassoc_of% e]
    simp only [add_comp, assoc, star_q_φ_q (q := q) φ hφ0, comp_zero, add_zero]

@[simp]
lemma lam_f (r : ℤ) :
    (S.lam heK heM φ hφ0).f r = J.star (S.t (n - r)) ≫ φ.f r ≫ q.f r := rfl

include heQ hq in
lemma lam_kar : dualHom J n eK ≫ S.lam heK heM φ hφ0 ≫ eQ = S.lam heK heM φ hφ0 := by
  ext r
  simp only [comp_f, dualHom_f, lam_f, assoc, q_eQ heQ hq]
  rw [← assoc, ← J.star_comp, S.t_eK heK]

include heQ in
/-- **P2**: the relative duality map of `(q : M ⟶ Q, (0, φ))` is `-(coneDualFst ≫ λ)`. -/
lemma relDuality_eq (hφ : dualHom J n eM ≫ φ = φ) (hiq : i ≫ q = 0)
    (H : Homotopy (dualHom J n q ≫ φ ≫ q) 0) (hH : ∀ a b, H.hom a b = 0) :
    relDuality H = -(coneDualFst (J := J) (N := n) q i hiq ≫ S.lam heK heM φ hφ0) := by
  have hφr (r : ℤ) {Z : V} (x : M.X r ⟶ Z) : J.star (eM.f (n - r)) ≫ φ.f r ≫ x = φ.f r ≫ x := by
    rw [← dualHom_f, ← comp_f_assoc, hφ]
  have e (r : ℤ) : J.star (i.f (n - r)) ≫ J.star (S.t (n - r)) ≫ φ.f r ≫ q.f r =
      φ.f r ≫ q.f r := by
    rw [← assoc, ← J.star_comp, eq_sub_of_add_eq (S.total (n - r)), J.star_sub, sub_comp,
      J.star_comp, assoc, star_q_φ_q (q := q) φ hφ0, comp_zero, sub_zero, hφr]
  ext r
  simp only [relDuality_f, relTop, hH, comp_zero, add_comp, zero_add, neg_f_apply, comp_f,
    coneDualFst_f, lam_f, Linear.units_smul_comp, assoc, e, Int.negOnePow_succ, Units.neg_smul]

include S heK heM heQ hi hq in
lemma i_comp_q_cone : i ≫ q = 0 := by
  ext n
  exact S.i_q heK heM heQ hi hq n

include heQ hi hq in
/-- **A pair `(q : M ⟶ Q, (0, φ))` over a Kar degreewise split surjection is Poincaré** as soon
as `λ = t^* φ q : K^{n-*} ⟶ Q` is a Kar equivalence (P2 and G1). -/
theorem isKarEquiv_relDuality (hc : eM ≫ q = q ≫ eQ) (hφ : dualHom J n eM ≫ φ = φ)
    (H : Homotopy (dualHom J n q ≫ φ ≫ q) 0) (hH : ∀ a b, H.hom a b = 0)
    (hlam : IsKarEquiv (dualHom J n eK) eQ (S.lam heK heM φ hφ0)) :
    IsKarEquiv (dualHom J (n + 1) (coneMap eM eQ hc)) eQ (relDuality H) := by
  have hiq := i_comp_q_cone S heK heM heQ hi hq
  rw [S.relDuality_eq heK heM heQ φ hφ0 hφ hiq H hH]
  exact ((S.isKarEquiv_coneDualFst heK heM heQ hc hiq).comp hlam
    (dualHom_idem (coneMap_idem hc heM heQ)) (dualHom_idem heK) heQ).neg

end Dual

end KarSplit

end

end HSFormal.LTheory
