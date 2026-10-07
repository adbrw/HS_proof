import HSFormal.LTheory.BoundaryPoincare
import Mathlib.CategoryTheory.Idempotents.Biproducts

/-!
# Two-out-of-three in the middle, and Kar complexes as complexes in `Karoubi V`

Support for `Model/Glue.lean` (gluing Poincaré pairs).

* `DegreewiseSplit.contractionMiddle`, `homotopyEquivMiddle`: **R2, middle** — for a strictly
  commuting ladder of degreewise split sequences whose outer maps are homotopy equivalences, the
  middle map is one (the cones form a degreewise split sequence with contractible ends).
* `karCx`, `karMap`: a Kar complex `(X, e)` (a chain idempotent `e`) as a complex in
  `Karoubi V`; `isKarEquiv_iff`: `IsKarEquiv e e' f` iff `karMap f` is a homotopy equivalence.
* `KarSplit`: degreewise split sequences of Kar complexes; `isKarEquiv_middle`: **R2, middle,
  in `Kar V`** (by transport to `Karoubi V`), and its dual `KarSplit.dual`.
* `IsKarEquiv.dualHom`, `IsKarEquiv.transposeHom`: duals and transposes of Kar equivalences.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex homotopyCofiber
  HSFormal.Compression

noncomputable section

universe v u

variable {V : Type u} [Category.{v} V] [Preadditive V]

section Middle

variable [HasBinaryBiproducts V] {K M Q : ChainComplex V ℤ} {i : K ⟶ M} {q : M ⟶ Q}
  (S : DegreewiseSplit i q)

/-- **Two-out-of-three, middle**: an extension of contractible complexes along a degreewise split
sequence is contractible; with `θ = s d t`, the contraction is
`t h_K i + q h_Q s - q h_Q θ h_K i`. -/
def DegreewiseSplit.contractionMiddle (hK : Homotopy (𝟙 K) 0) (hQ : Homotopy (𝟙 Q) 0) :
    Homotopy (𝟙 M) 0 :=
  homotopyCongr (Homotopy.nullHomotopy' fun a b _ ↦ S.t a ≫ hK.hom a b ≫ i.f b +
    q.f a ≫ hQ.hom a b ≫ S.s b -
      q.f a ≫ hQ.hom a b ≫ S.s b ≫ M.d b a ≫ S.t a ≫ hK.hom a b ≫ i.f b) (by
      ext n
      rw [Homotopy.nullHomotopicMap'_f (down_rel_succ n) (down_rel_pred n)]
      have cK := contraction_comm hK n (n - 1) (n + 1) (down_rel_pred n) (down_rel_succ n)
      have cQ := contraction_comm hQ n (n - 1) (n + 1) (down_rel_pred n) (down_rel_succ n)
      have e₁ := S.d_t n (n - 1)
      have e₄ := S.s_d (n + 1) n
      have e₇ := S.s_d_t_d (n + 1) n (n - 1)
      have e₃ : M.d n (n - 1) ≫ q.f (n - 1) = q.f n ≫ Q.d n (n - 1) := (q.comm _ _).symm
      have e₂ : i.f (n + 1) ≫ M.d (n + 1) n = K.d (n + 1) n ≫ i.f n := i.comm _ _
      have eK : hK.hom n (n + 1) ≫ K.d (n + 1) n ≫ i.f n =
          i.f n - K.d n (n - 1) ≫ hK.hom (n - 1) n ≫ i.f n := by
        have := congrArg (· ≫ i.f n) cK
        simp only [id_comp, add_comp, assoc] at this
        exact eq_sub_of_add_eq' this.symm
      have tK : S.t n ≫ i.f n = S.t n ≫ K.d n (n - 1) ≫ hK.hom (n - 1) n ≫ i.f n +
          S.t n ≫ hK.hom n (n + 1) ≫ K.d (n + 1) n ≫ i.f n := by
        have := congrArg (fun x ↦ S.t n ≫ x ≫ i.f n) cK
        simpa only [id_comp, add_comp, comp_add, assoc] using this
      have sQ : q.f n ≫ S.s n = q.f n ≫ Q.d n (n - 1) ≫ hQ.hom (n - 1) n ≫ S.s n +
          q.f n ≫ hQ.hom n (n + 1) ≫ Q.d (n + 1) n ≫ S.s n := by
        have := congrArg (fun x ↦ q.f n ≫ x ≫ S.s n) cQ
        simpa only [id_comp, add_comp, comp_add, assoc] using this
      have θQ (Z : V) (x : Q.X n ⟶ Z) : x = Q.d n (n - 1) ≫ hQ.hom (n - 1) n ≫ x +
          hQ.hom n (n + 1) ≫ Q.d (n + 1) n ≫ x := by
        conv_lhs => rw [← id_comp x, cQ]
        simp only [add_comp, assoc]
      have eA : M.d n (n - 1) ≫ S.t (n - 1) ≫ hK.hom (n - 1) n ≫ i.f n +
          S.t n ≫ hK.hom n (n + 1) ≫ i.f (n + 1) ≫ M.d (n + 1) n =
          S.t n ≫ i.f n + q.f n ≫ S.s n ≫ M.d n (n - 1) ≫ S.t (n - 1) ≫ hK.hom (n - 1) n ≫
            i.f n := by
        conv_lhs => rw [← assoc (M.d n (n - 1)), e₁, e₂]
        rw [tK]
        simp only [add_comp, assoc]
        abel
      have eB : M.d n (n - 1) ≫ q.f (n - 1) ≫ hQ.hom (n - 1) n ≫ S.s n +
          q.f n ≫ hQ.hom n (n + 1) ≫ S.s (n + 1) ≫ M.d (n + 1) n =
          q.f n ≫ S.s n + q.f n ≫ hQ.hom n (n + 1) ≫ S.s (n + 1) ≫ M.d (n + 1) n ≫ S.t n ≫
            i.f n := by
        conv_lhs => rw [← assoc (M.d n (n - 1)), e₃, e₄]
        rw [sQ]
        simp only [comp_add, assoc]
        abel
      have eC : M.d n (n - 1) ≫ q.f (n - 1) ≫ hQ.hom (n - 1) n ≫ S.s n ≫ M.d n (n - 1) ≫
          S.t (n - 1) ≫ hK.hom (n - 1) n ≫ i.f n +
          q.f n ≫ hQ.hom n (n + 1) ≫ S.s (n + 1) ≫ M.d (n + 1) n ≫ S.t n ≫ hK.hom n (n + 1) ≫
            i.f (n + 1) ≫ M.d (n + 1) n =
          q.f n ≫ S.s n ≫ M.d n (n - 1) ≫ S.t (n - 1) ≫ hK.hom (n - 1) n ≫ i.f n +
            q.f n ≫ hQ.hom n (n + 1) ≫ S.s (n + 1) ≫ M.d (n + 1) n ≫ S.t n ≫ i.f n := by
        have e₇' : S.s (n + 1) ≫ M.d (n + 1) n ≫ S.t n ≫ K.d n (n - 1) ≫ hK.hom (n - 1) n ≫
            i.f n = -(Q.d (n + 1) n ≫ S.s n ≫ M.d n (n - 1) ≫ S.t (n - 1) ≫ hK.hom (n - 1) n ≫
            i.f n) := by
          simp only [← assoc] at e₇ ⊢
          rw [e₇, neg_comp, neg_comp]
        conv_lhs => rw [← assoc (M.d n (n - 1)), e₃, e₂, eK]
        conv_rhs => rw [θQ _ (S.s n ≫ M.d n (n - 1) ≫ S.t (n - 1) ≫ hK.hom (n - 1) n ≫ i.f n)]
        simp only [comp_sub, comp_add, assoc, e₇', comp_neg]
        abel
      have hsum := sub_eq_zero.mpr (congr_arg₂ (fun x y => x - y) (congr_arg₂ (· + ·) eA eB) eC)
      beta_reduce at hsum
      simp only [comp_add, comp_sub, add_comp, sub_comp, assoc, id_f]
      rw [← S.total n, ← sub_eq_zero]
      refine Eq.trans ?_ hsum
      abel) (by simp)

variable {K' M' Q' : ChainComplex V ℤ} {i' : K' ⟶ M'} {q' : M' ⟶ Q'} (S' : DegreewiseSplit i' q')

/-- **Two-out-of-three (R2), middle**: for a strictly commuting ladder of degreewise split
sequences whose outer maps are homotopy equivalences, the middle map `m` is one. -/
def homotopyEquivMiddle (el : HomotopyEquiv K K') (er : HomotopyEquiv Q Q') (m : M ⟶ M')
    (h₁ : i ≫ m = el.hom ≫ i') (h₂ : q ≫ er.hom = m ≫ q') : HomotopyEquiv M M' :=
  homotopyEquivOfCone ((S.cone S' h₁ h₂).contractionMiddle (coneContraction el)
    (coneContraction er))

@[simp]
lemma homotopyEquivMiddle_hom (el : HomotopyEquiv K K') (er : HomotopyEquiv Q Q') (m : M ⟶ M')
    (h₁ : i ≫ m = el.hom ≫ i') (h₂ : q ≫ er.hom = m ≫ q') :
    (homotopyEquivMiddle S S' el er m h₁ h₂).hom = m := rfl

end Middle

/-! ### Kar complexes as complexes in `Karoubi V` -/

section Kar

open Idempotents

variable {X Y Z : ChainComplex V ℤ} {e : X ⟶ X} {e' : Y ⟶ Y} {e'' : Z ⟶ Z}

@[reassoc (attr := simp)]
lemma idem_f (he : e ≫ e = e) (r : ℤ) : e.f r ≫ e.f r = e.f r := by rw [← comp_f, he]

lemma kar_left {f : X ⟶ Y} (he : e ≫ e = e) (hf : e ≫ f ≫ e' = f) : e ≫ f = f :=
  calc e ≫ f = e ≫ e ≫ f ≫ e' := by rw [hf]
  _ = e ≫ f ≫ e' := by rw [← assoc, he]
  _ = f := hf

lemma kar_right {f : X ⟶ Y} (he' : e' ≫ e' = e') (hf : e ≫ f ≫ e' = f) : f ≫ e' = f :=
  calc f ≫ e' = (e ≫ f ≫ e') ≫ e' := by rw [hf]
  _ = e ≫ f ≫ e' := by simp only [assoc, he']
  _ = f := hf

@[reassoc]
lemma kar_left_f {f : X ⟶ Y} (he : e ≫ e = e) (hf : e ≫ f ≫ e' = f) (r : ℤ) :
    e.f r ≫ f.f r = f.f r := by
  rw [← comp_f, kar_left he hf]

@[reassoc]
lemma kar_right_f {f : X ⟶ Y} (he' : e' ≫ e' = e') (hf : e ≫ f ≫ e' = f) (r : ℤ) :
    f.f r ≫ e'.f r = f.f r := by
  rw [← comp_f, kar_right he' hf]

lemma kar_f {f : X ⟶ Y} (hf : e ≫ f ≫ e' = f) (r : ℤ) : e.f r ≫ f.f r ≫ e'.f r = f.f r := by
  rw [← comp_f, ← comp_f, hf]

variable (e) in
/-- The Kar complex `(X, e)` as a complex in `Karoubi V`: `(X_r, e_r)` with differential
`e_r d = d e_{r-1}`. -/
@[reducible] def karCx (he : e ≫ e = e) : ChainComplex (Karoubi V) ℤ where
  X r := ⟨X.X r, e.f r, idem_f he r⟩
  d r r' := ⟨e.f r ≫ X.d r r', by simp [e.comm_assoc, he]⟩
  shape r r' h := by ext; simp [X.shape r r' h]
  d_comp_d' r r' r'' _ _ := by ext; simp [e.comm_assoc]

@[simp]
lemma karCx_X_p (he : e ≫ e = e) (r : ℤ) : ((karCx e he).X r).p = e.f r := rfl

@[simp]
lemma karCx_d_f (he : e ≫ e = e) (r r' : ℤ) : ((karCx e he).d r r').f = e.f r ≫ X.d r r' := rfl

/-- A Kar chain map `f : (X, e) ⟶ (Y, e')` (`e f e' = f`) as a chain map in `Karoubi V`. -/
def karMap (he : e ≫ e = e) (he' : e' ≫ e' = e') (f : X ⟶ Y) (hf : e ≫ f ≫ e' = f) :
    karCx e he ⟶ karCx e' he' where
  f r := ⟨f.f r, kar_f hf r⟩
  comm' r r' _ := by
    ext
    simp only [Karoubi.comp_f, karCx_d_f, assoc]
    rw [← Hom.comm, kar_left_f_assoc he hf, kar_right_f_assoc he' hf]

@[simp]
lemma karMap_f_f (he : e ≫ e = e) (he' : e' ≫ e' = e') (f : X ⟶ Y) (hf : e ≫ f ≫ e' = f)
    (r : ℤ) : ((karMap he he' f hf).f r).f = f.f r := rfl

lemma kar_comp (he : e ≫ e = e) (he'' : e'' ≫ e'' = e'') {f : X ⟶ Y} (hf : e ≫ f ≫ e' = f) {g : Y ⟶ Z} (hg : e' ≫ g ≫ e'' = g) :
    e ≫ (f ≫ g) ≫ e'' = f ≫ g := by
  rw [assoc, kar_right he'' hg, ← assoc, kar_left he hf]

variable (he : e ≫ e = e) (he' : e' ≫ e' = e') (he'' : e'' ≫ e'' = e'')

lemma karMap_comp (f : X ⟶ Y) (hf : e ≫ f ≫ e' = f) (g : Y ⟶ Z) (hg : e' ≫ g ≫ e'' = g) :
    karMap he he' f hf ≫ karMap he' he'' g hg = karMap he he'' (f ≫ g) (kar_comp he he'' hf hg) := by
  ext; rfl

lemma karMap_id : karMap he he e (by simp [he]) = 𝟙 _ := by
  ext; rfl

lemma karMap_congr {f g : X ⟶ Y} (hf : e ≫ f ≫ e' = f) (hg : e ≫ g ≫ e' = g) (h : f = g) :
    karMap he he' f hf = karMap he he' g hg := by
  subst h; rfl

/-- The underlying chain map in `V` of a chain map in `Karoubi V`. -/
def ofKar (g : karCx e he ⟶ karCx e' he') : X ⟶ Y where
  f r := (g.f r).f
  comm' r r' _ := by
    have := congrArg Karoubi.Hom.f (g.comm r r')
    simp only [karCx_d_f, Karoubi.comp_f, assoc] at this
    have h₁ : e.f r ≫ X.d r r' ≫ (g.f r').f = X.d r r' ≫ (g.f r').f := by
      rw [← assoc, Hom.comm, assoc]
      congr 1
      exact Karoubi.p_comp (g.f r')
    have h₂ : (g.f r).f ≫ e'.f r = (g.f r).f := Karoubi.comp_p (g.f r)
    rw [← h₁, ← this, reassoc_of% h₂]

@[simp]
lemma ofKar_f (g : karCx e he ⟶ karCx e' he') (r : ℤ) : (ofKar he he' g).f r = (g.f r).f := rfl

lemma ofKar_kar (g : karCx e he ⟶ karCx e' he') : e ≫ ofKar he he' g ≫ e' = ofKar he he' g := by
  ext r
  exact (g.f r).comm

lemma karMap_ofKar (g : karCx e he ⟶ karCx e' he') :
    karMap he he' (ofKar he he' g) (ofKar_kar he he' g) = g := by
  ext; rfl

/-- A homotopy of Kar chain maps in `V` gives a homotopy in `Karoubi V`. -/
def karHomotopy' {f g : X ⟶ Y} (hf : e ≫ f ≫ e' = f) (hg : e ≫ g ≫ e' = g) (H : Homotopy f g) :
    Homotopy (karMap he he' f hf) (karMap he he' g hg) where
  hom i j := ⟨e.f i ≫ H.hom i j ≫ e'.f j, by simp [he, he']⟩
  zero i j h := by ext; simp [H.zero i j h]
  comm i := by
    have h := H.comm i
    rw [dNext_eq _ (down_rel_pred i), prevD_eq _ (down_rel_succ i)] at h ⊢
    ext
    have h' := congrArg (fun x ↦ e.f i ≫ x ≫ e'.f i) h
    simp only [comp_add, add_comp, assoc, kar_f hf, kar_f hg] at h'
    simp only [karMap_f_f, add_def, Karoubi.comp_f, karCx_d_f, assoc]
    rw [h', ← Hom.comm_assoc e, idem_f_assoc he, ← Hom.comm e', idem_f_assoc he']

/-- A homotopy in `Karoubi V` gives a homotopy of the underlying chain maps in `V`. -/
def homotopyOfKar {f g : X ⟶ Y} (hf : e ≫ f ≫ e' = f) (hg : e ≫ g ≫ e' = g)
    (H : Homotopy (karMap he he' f hf) (karMap he he' g hg)) : Homotopy f g where
  hom i j := (H.hom i j).f
  zero i j h := by rw [H.zero i j h]; rfl
  comm i := by
    have h := congrArg Karoubi.Hom.f (H.comm i)
    rw [dNext_eq _ (down_rel_pred i), prevD_eq _ (down_rel_succ i)] at h ⊢
    simp only [karMap_f_f, add_def, Karoubi.comp_f, karCx_d_f, assoc] at h
    have h₁ : e.f (i - 1) ≫ (H.hom (i - 1) i).f = (H.hom (i - 1) i).f :=
      Karoubi.p_comp (H.hom (i - 1) i)
    have h₂ : (H.hom i (i + 1)).f ≫ e'.f (i + 1) = (H.hom i (i + 1)).f :=
      Karoubi.comp_p (H.hom i (i + 1))
    rw [h, Hom.comm_assoc, h₁, reassoc_of% h₂]

/-- **Kar equivalences are homotopy equivalences in `Karoubi V`.** -/
theorem isKarEquiv_iff {f : X ⟶ Y} (hf : e ≫ f ≫ e' = f) :
    IsKarEquiv e e' f ↔ ∃ E : HomotopyEquiv (karCx e he) (karCx e' he'), E.hom = karMap he he' f hf := by
  constructor
  · rintro ⟨g, hg, ⟨H₁⟩, ⟨H₂⟩⟩
    refine ⟨⟨karMap he he' f hf, karMap he' he g hg,
      homotopyCongr (karHomotopy' he he (kar_comp he he hf hg) (by simp [he]) H₂)
        (karMap_comp he he' he _ _ _ _).symm (karMap_id he),
      homotopyCongr (karHomotopy' he' he' (kar_comp he' he' hg hf) (by simp [he']) H₁)
        (karMap_comp he' he he' _ _ _ _).symm (karMap_id he')⟩, rfl⟩
  · rintro ⟨E, hE⟩
    have hinv := karMap_ofKar he' he E.inv
    refine ⟨ofKar he' he E.inv, ofKar_kar he' he E.inv, ⟨homotopyOfKar he' he'
      (kar_comp he' he' (ofKar_kar he' he E.inv) hf) (by simp [he']) (homotopyCongr
        E.homotopyInvHomId ?_ (karMap_id he').symm)⟩, ⟨homotopyOfKar he he
      (kar_comp he he hf (ofKar_kar he' he E.inv)) (by simp [he]) (homotopyCongr
        E.homotopyHomInvId ?_ (karMap_id he).symm)⟩⟩
    · rw [hE]
      conv_lhs => rw [← hinv]
      exact karMap_comp he' he he' _ _ _ _
    · rw [hE]
      conv_lhs => rw [← hinv]
      exact karMap_comp he he' he _ _ _ _

end Kar

/-! ### Degreewise split sequences of Kar complexes and R2 in `Kar V` -/

section KarSplit

variable {K M Q K' M' Q' : ChainComplex V ℤ} {eK : K ⟶ K} {eM : M ⟶ M} {eQ : Q ⟶ Q}
  {eK' : K' ⟶ K'} {eM' : M' ⟶ M'} {eQ' : Q' ⟶ Q'}

variable (eK eM eQ) in
/-- A degreewise split short exact sequence `0 ⟶ (K, e_K) ⟶ (M, e_M) ⟶ (Q, e_Q) ⟶ 0` of Kar
complexes: Kar chain maps `i`, `q` with a degreewise Kar retraction `t` of `i` and Kar section
`s` of `q`, `ti + qs = e_M`. -/
structure KarSplit (i : K ⟶ M) (q : M ⟶ Q) where
  t : ∀ n, M.X n ⟶ K.X n
  s : ∀ n, Q.X n ⟶ M.X n
  t_kar : ∀ n, eM.f n ≫ t n ≫ eK.f n = t n
  s_kar : ∀ n, eQ.f n ≫ s n ≫ eM.f n = s n
  it : ∀ n, i.f n ≫ t n = eK.f n
  sq : ∀ n, s n ≫ q.f n = eQ.f n
  total : ∀ n, t n ≫ i.f n + q.f n ≫ s n = eM.f n

variable {i : K ⟶ M} {q : M ⟶ Q} {i' : K' ⟶ M'} {q' : M' ⟶ Q'}

open Idempotents in
/-- A Kar degreewise split sequence is a degreewise split sequence in `Karoubi V`. -/
def KarSplit.toKaroubi (S : KarSplit eK eM eQ i q) (heK : eK ≫ eK = eK) (heM : eM ≫ eM = eM)
    (heQ : eQ ≫ eQ = eQ) (hi : eK ≫ i ≫ eM = i) (hq : eM ≫ q ≫ eQ = q) :
    DegreewiseSplit (karMap heK heM i hi) (karMap heM heQ q hq) where
  t n := ⟨S.t n, S.t_kar n⟩
  s n := ⟨S.s n, S.s_kar n⟩
  it n := by ext; exact S.it n
  sq n := by ext; exact S.sq n
  total n := by ext; exact S.total n

variable [HasFiniteBiproducts V]

/-- **R2, middle, in `Kar V`**: for a strictly commuting ladder of Kar degreewise split
sequences whose outer maps are Kar equivalences, the middle map is a Kar equivalence. -/
theorem isKarEquiv_middle (heK : eK ≫ eK = eK) (heM : eM ≫ eM = eM) (heQ : eQ ≫ eQ = eQ)
    (heK' : eK' ≫ eK' = eK') (heM' : eM' ≫ eM' = eM') (heQ' : eQ' ≫ eQ' = eQ')
    (hi : eK ≫ i ≫ eM = i) (hq : eM ≫ q ≫ eQ = q) (hi' : eK' ≫ i' ≫ eM' = i')
    (hq' : eM' ≫ q' ≫ eQ' = q') (S : KarSplit eK eM eQ i q) (S' : KarSplit eK' eM' eQ' i' q')
    {l : K ⟶ K'} {m : M ⟶ M'} {r : Q ⟶ Q'} (hl : eK ≫ l ≫ eK' = l) (hm : eM ≫ m ≫ eM' = m)
    (hr : eQ ≫ r ≫ eQ' = r) (h₁ : i ≫ m = l ≫ i') (h₂ : q ≫ r = m ≫ q')
    (el : IsKarEquiv eK eK' l) (er : IsKarEquiv eQ eQ' r) : IsKarEquiv eM eM' m := by
  haveI : HasBinaryBiproducts (Idempotents.Karoubi V) := hasBinaryBiproducts_of_finite_biproducts _
  obtain ⟨El, hEl⟩ := (isKarEquiv_iff heK heK' hl).1 el
  obtain ⟨Er, hEr⟩ := (isKarEquiv_iff heQ heQ' hr).1 er
  refine (isKarEquiv_iff heM heM' hm).2 ⟨homotopyEquivMiddle (S.toKaroubi heK heM heQ hi hq)
    (S'.toKaroubi heK' heM' heQ' hi' hq') El Er (karMap heM heM' m hm) ?_ ?_, rfl⟩
  · rw [hEl, karMap_comp, karMap_comp]
    exact karMap_congr _ _ _ _ h₁
  · rw [hEr, karMap_comp, karMap_comp]
    exact karMap_congr _ _ _ _ h₂

end KarSplit

/-! ### Duals -/

section Dual

variable (J : StrictInvolution V) (N : ℤ)

variable {K M Q : ChainComplex V ℤ} {eK : K ⟶ K} {eM : M ⟶ M} {eQ : Q ⟶ Q} {i : K ⟶ M}
  {q : M ⟶ Q}

/-- The `N`-dual of a Kar degreewise split sequence. -/
def KarSplit.dual (S : KarSplit eK eM eQ i q) :
    KarSplit (dualHom J N eQ) (dualHom J N eM) (dualHom J N eK) (dualHom J N q)
      (dualHom J N i) where
  t n := J.star (S.s (N - n))
  s n := J.star (S.t (N - n))
  t_kar n := by simp only [dualHom_f, ← J.star_comp, assoc, S.s_kar]
  s_kar n := by simp only [dualHom_f, ← J.star_comp, assoc, S.t_kar]
  it n := by simp only [dualHom_f, ← J.star_comp, S.sq]
  sq n := by simp only [dualHom_f, ← J.star_comp, S.it]
  total n := by
    simp only [dualHom_f, ← J.star_comp, ← J.star_add]
    rw [add_comm, S.total]

variable {J N}

lemma dualHom_idem {X : ChainComplex V ℤ} {e : X ⟶ X} (he : e ≫ e = e) :
    dualHom J N e ≫ dualHom J N e = dualHom J N e := by
  rw [← dualHom_comp, he]

lemma dualHom_kar {X Y : ChainComplex V ℤ} {e : X ⟶ X} {e' : Y ⟶ Y} {f : X ⟶ Y}
    (hf : e ≫ f ≫ e' = f) : dualHom J N e' ≫ dualHom J N f ≫ dualHom J N e = dualHom J N f := by
  rw [← dualHom_comp, ← dualHom_comp, assoc, hf]

/-- The dual of a Kar equivalence is a Kar equivalence. -/
lemma IsKarEquiv.dualHom {X Y : ChainComplex V ℤ} {e : X ⟶ X} {e' : Y ⟶ Y} {f : X ⟶ Y}
    (h : IsKarEquiv e e' f) :
    IsKarEquiv (HSFormal.Compression.dualHom J N e') (HSFormal.Compression.dualHom J N e)
      (HSFormal.Compression.dualHom J N f) := by
  obtain ⟨g, hg, ⟨H₁⟩, ⟨H₂⟩⟩ := h
  exact ⟨HSFormal.Compression.dualHom J N g, dualHom_kar hg,
    ⟨homotopyCongr (dualHomotopy J N H₂) (dualHom_comp _ _ _ _) rfl⟩,
    ⟨homotopyCongr (dualHomotopy J N H₁) (dualHom_comp _ _ _ _) rfl⟩⟩

/-- The bidual isomorphism is a Kar equivalence `(C^{**}, e^{**}) ⟶ (C, e)`. -/
lemma isKarEquiv_bidual {X : ChainComplex V ℤ} {e : X ⟶ X} (he : e ≫ e = e) :
    IsKarEquiv (HSFormal.Compression.dualHom J N (HSFormal.Compression.dualHom J N e)) e
      (bidual J N X).hom := by
  refine ⟨e ≫ (bidual J N X).inv, ?_, ⟨Homotopy.ofEq ?_⟩, ⟨Homotopy.ofEq ?_⟩⟩
  · rw [← cancel_mono (bidual J N X).hom]
    simp [dualHom_dualHom_comp_bidual_hom, he]
  · simp
  · rw [← assoc, ← dualHom_dualHom_comp_bidual_hom, assoc, Iso.hom_inv_id, comp_id]

/-- The transpose of a Kar equivalence `φ : (C^{N-*}, e^*) ⟶ (D, e')` is a Kar equivalence
`Tφ : (D^{N-*}, e'^*) ⟶ (C, e)`. -/
lemma IsKarEquiv.transposeHom {X Y : ChainComplex V ℤ} {e : X ⟶ X} {e' : Y ⟶ Y}
    {f : dualComplex J N X ⟶ Y} (he : e ≫ e = e) (he' : e' ≫ e' = e')
    (h : IsKarEquiv (HSFormal.Compression.dualHom J N e) e' f) :
    IsKarEquiv (HSFormal.Compression.dualHom J N e') e (HSFormal.LTheory.transposeHom J N f) :=
  h.dualHom.comp (isKarEquiv_bidual he) (dualHom_idem he') (dualHom_idem (dualHom_idem he)) he

end Dual


end

end HSFormal.LTheory
