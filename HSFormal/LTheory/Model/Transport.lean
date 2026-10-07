import HSFormal.LTheory.ConcreteL
import HSFormal.LTheory.Model.GlueKar

/-!
# Transport of Poincaré complexes and pairs along Kar homotopy equivalences (L-model 11)

`blueprint/lower-L-construction.md` §4, row 11 (used by `Domination`, `FreeLine`, `Wall`).

* `KarHtpyEquiv p p'`: a chain homotopy equivalence `(C, p) ≃ (C', p')` in `Kar V` (data);
  `refl`, `symm`, `trans`, `dual`, `ofIsKarEquiv`.
* `SymPoincare.transport`: `(C', p', f φ f^*)` (strictly symmetric by construction, Poincaré as a
  composite of equivalences), `transportIsometry`, `Lconc.cls_transport`.
* **Truncation.** `truncHi`/`truncLo`: if `(C', p') ≃ (C, p)` with `(C, p)` supported in
  `[lo, hi]`, then `p'` is homotopic to a sub-idempotent `q ≤ p'` (same underlying complex `C'`)
  supported in `[lo, hi]` (`p' + (dT + Td)` for the truncated contraction `T`);
  `KarHtpyEquiv.trunc`, `SymPoincare.transportTrunc`, `Lconc.cls_transportTrunc`.
* **Cones.** `coneKarSplit`: `0 ⟶ D ⟶ Cone(j) ⟶ ΣB ⟶ 0` in `Kar V`; `isKarEquiv_coneMap`: the
  five lemma for cones of strict squares (via `isKarEquiv_middle`).
* **Pairs.** `SymPair.transportD` (target: `j' = j ≫ f`, `δφ' = f δφ f^*`, `Ψ' = c^* Ψ f`),
  `SymPair.transportBd` (boundary: `j' = g ≫ j`, `δφ' = j W j^* + δφ` with `W : gfφ(gf)^* ≃ φ`
  symmetrized over `ℚ`, `c^* Ψ' ≃ Ψ` by `transportRelDualityHomotopy`), `SymPair.transport` (both, with
  the homotopy-commuting square `transportSquare`), truncated versions, `NullCobordant.transport`.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HomologicalComplex HSFormal.Compression

noncomputable section

universe v u

variable {V : Type u} [Category.{v} V] [Preadditive V]

/-! ### Kar homotopy equivalences -/

section KarHtpyEquiv

variable {C C' C'' : ChainComplex V ℤ}

/-- A chain homotopy equivalence `(C, p) ≃ (C', p')` in `Kar V`: Kar chain maps `f`, `g` with
homotopies (in `V`) `fg ≃ p` and `gf ≃ p'`. -/
structure KarHtpyEquiv (p : C ⟶ C) (p' : C' ⟶ C') where
  f : C ⟶ C'
  g : C' ⟶ C
  pf : p ≫ f = f
  fp : f ≫ p' = f
  pg : p' ≫ g = g
  gp : g ≫ p = g
  fg : Homotopy (f ≫ g) p
  gf : Homotopy (g ≫ f) p'

namespace KarHtpyEquiv

attribute [reassoc (attr := simp)] pf fp pg gp

variable {p : C ⟶ C} {p' : C' ⟶ C'} {p'' : C'' ⟶ C''} (e : KarHtpyEquiv p p')

lemma f_kar : p ≫ e.f ≫ p' = e.f := by simp

lemma g_kar : p' ≫ e.g ≫ p = e.g := by simp

lemma isKarEquiv : IsKarEquiv p p' e.f := ⟨e.g, e.g_kar, ⟨e.gf⟩, ⟨e.fg⟩⟩

/-- The identity of `(C, p)`. -/
@[simps]
def refl (hp : p ≫ p = p) : KarHtpyEquiv p p where
  f := p
  g := p
  pf := hp
  fp := hp
  pg := hp
  gp := hp
  fg := .ofEq hp
  gf := .ofEq hp

/-- The inverse equivalence. -/
@[simps]
def symm : KarHtpyEquiv p' p := ⟨e.g, e.f, e.pg, e.gp, e.pf, e.fp, e.gf, e.fg⟩

/-- Composition of equivalences. -/
@[simps]
def trans (e' : KarHtpyEquiv p' p'') : KarHtpyEquiv p p'' where
  f := e.f ≫ e'.f
  g := e'.g ≫ e.g
  pf := by simp
  fp := by simp
  pg := by simp
  gp := by simp
  fg := (homotopyCongr ((Homotopy.refl e.f).comp (e'.fg.comp (Homotopy.refl e.g))) (by simp)
    (by simp)).trans e.fg
  gf := (homotopyCongr ((Homotopy.refl e'.g).comp (e.gf.comp (Homotopy.refl e'.f))) (by simp)
    (by simp)).trans e'.gf

variable (J : StrictInvolution V) (N : ℤ) in
/-- The dual equivalence `(C'^{N-*}, p'^*) ≃ (C^{N-*}, p^*)`. -/
@[simps]
def dual : KarHtpyEquiv (dualHom J N p') (dualHom J N p) where
  f := dualHom J N e.f
  g := dualHom J N e.g
  pf := by rw [← dualHom_comp, e.fp]
  fp := by rw [← dualHom_comp, e.pf]
  pg := by rw [← dualHom_comp, e.gp]
  gp := by rw [← dualHom_comp, e.pg]
  fg := homotopyCongr (dualHomotopy J N e.gf) (dualHom_comp _ _ _ _) rfl
  gf := homotopyCongr (dualHomotopy J N e.fg) (dualHom_comp _ _ _ _) rfl

/-- Choose the data of an `IsKarEquiv`. -/
def ofIsKarEquiv {f : C ⟶ C'} (h : IsKarEquiv p p' f) (hf : p ≫ f ≫ p' = f) (hp : p ≫ p = p)
    (hp' : p' ≫ p' = p') : KarHtpyEquiv p p' where
  f := f
  g := h.choose
  pf := kar_left hp hf
  fp := kar_right hp' hf
  pg := kar_left hp' h.choose_spec.1
  gp := kar_right hp h.choose_spec.1
  fg := h.choose_spec.2.2.some
  gf := h.choose_spec.2.1.some

/-- The homotopy `gf ≃ p'` compressed to a Kar homotopy `p' H p'`. -/
def karGf (hp' : p' ≫ p' = p') : Homotopy (e.g ≫ e.f) p' :=
  karHomotopy (p := p') (q := p') e.gf (by simp) (by simp [hp'])

lemma karGf_kar (hp' : p' ≫ p' = p') (i j : ℤ) :
    p'.f i ≫ (e.karGf hp').hom i j ≫ p'.f j = (e.karGf hp').hom i j := by
  simp [karGf, idem_f hp', reassoc_of% (idem_f hp' i)]

/-- `gf` vanishes where `(C, p)` does. -/
lemma gf_f_eq_zero {r : ℤ} (hr : p.f r = 0) : (e.g ≫ e.f).f r = 0 := by
  rw [comp_f, ← e.gp, comp_f, hr, comp_zero, zero_comp]

end KarHtpyEquiv

end KarHtpyEquiv

/-! ### Truncation -/

section Trunc

variable {C : ChainComplex V ℤ} {p x : C ⟶ C}

@[reassoc]
lemma kar_hom_left {H : Homotopy x p} (hp : p ≫ p = p)
    (hH : ∀ i j, p.f i ≫ H.hom i j ≫ p.f j = H.hom i j) (i j : ℤ) :
    p.f i ≫ H.hom i j = H.hom i j := by
  rw [← hH, ← assoc, idem_f hp]

@[reassoc]
lemma kar_hom_right {H : Homotopy x p} (hp : p ≫ p = p)
    (hH : ∀ i j, p.f i ≫ H.hom i j ≫ p.f j = H.hom i j) (i j : ℤ) :
    H.hom i j ≫ p.f j = H.hom i j := by
  rw [← hH, assoc, assoc, idem_f hp]

/-- The homotopy `H : x ≃ p` cut off below source degree `hi`. -/
def truncHiHom (H : Homotopy x p) (hi i j : ℤ) : C.X i ⟶ C.X j :=
  if hi ≤ i then H.hom i j else 0

/-- The homotopy `H : x ≃ p` cut off above target degree `lo`. -/
def truncLoHom (H : Homotopy x p) (lo i j : ℤ) : C.X i ⟶ C.X j :=
  if j ≤ lo then H.hom i j else 0

/-- **Truncation above `hi`**: `p + dT + Td` with `T` the part of `H` starting in degrees `≥ hi`.
If `x` vanishes above `hi`, this is a sub-idempotent of `p`, homotopic to `p`, vanishing above
`hi`, and equal to `p + H d` in degree `hi`. -/
def truncHi (H : Homotopy x p) (hi : ℤ) : C ⟶ C :=
  p + Homotopy.nullHomotopicMap (truncHiHom H hi)

/-- **Truncation below `lo`**: `p + dT + Td` with `T` the part of `H` ending in degrees `≤ lo`. -/
def truncLo (H : Homotopy x p) (lo : ℤ) : C ⟶ C :=
  p + Homotopy.nullHomotopicMap (truncLoHom H lo)

lemma truncHi_f (H : Homotopy x p) (hi r : ℤ) : (truncHi H hi).f r =
    p.f r + (C.d r (r - 1) ≫ truncHiHom H hi (r - 1) r + truncHiHom H hi r (r + 1) ≫
      C.d (r + 1) r) := by
  rw [truncHi, add_f_apply, Homotopy.nullHomotopicMap_f (down_rel_succ r) (down_rel_pred r)]

lemma truncLo_f (H : Homotopy x p) (lo r : ℤ) : (truncLo H lo).f r =
    p.f r + (C.d r (r - 1) ≫ truncLoHom H lo (r - 1) r + truncLoHom H lo r (r + 1) ≫
      C.d (r + 1) r) := by
  rw [truncLo, add_f_apply, Homotopy.nullHomotopicMap_f (down_rel_succ r) (down_rel_pred r)]

/-- `p + dH + Hd = x` in each degree. -/
lemma p_add_dH_Hd (H : Homotopy x p) (r : ℤ) :
    p.f r + (C.d r (r - 1) ≫ H.hom (r - 1) r + H.hom r (r + 1) ≫ C.d (r + 1) r) = x.f r := by
  rw [homotopy_comm H r (r - 1) (r + 1) (down_rel_pred r) (down_rel_succ r)]; abel

variable (H : Homotopy x p)

lemma truncHi_f_above {hi r : ℤ} (hx : x.f r = 0) (hr : hi < r) : (truncHi H hi).f r = 0 := by
  rw [truncHi_f, truncHiHom, truncHiHom, if_pos (by omega), if_pos (by omega), p_add_dH_Hd, hx]

lemma truncHi_f_self (hi : ℤ) :
    (truncHi H hi).f hi = p.f hi + H.hom hi (hi + 1) ≫ C.d (hi + 1) hi := by
  rw [truncHi_f, truncHiHom, truncHiHom, if_neg (by omega), if_pos le_rfl, comp_zero, zero_add]

lemma truncHi_f_below {hi r : ℤ} (hr : r < hi) : (truncHi H hi).f r = p.f r := by
  rw [truncHi_f, truncHiHom, truncHiHom, if_neg (by omega), if_neg (by omega)]; simp

lemma truncLo_f_below {lo r : ℤ} (hx : x.f r = 0) (hr : r < lo) : (truncLo H lo).f r = 0 := by
  rw [truncLo_f, truncLoHom, truncLoHom, if_pos (by omega), if_pos (by omega), p_add_dH_Hd, hx]

lemma truncLo_f_self (lo : ℤ) :
    (truncLo H lo).f lo = p.f lo + C.d lo (lo - 1) ≫ H.hom (lo - 1) lo := by
  rw [truncLo_f, truncLoHom, truncLoHom, if_pos le_rfl, if_neg (by omega), zero_comp, add_zero]

lemma truncLo_f_above {lo r : ℤ} (hr : lo < r) : (truncLo H lo).f r = p.f r := by
  rw [truncLo_f, truncLoHom, truncLoHom, if_neg (by omega), if_neg (by omega)]; simp

/-- The truncation is homotopic to `p`. -/
def truncHiHomotopy (hi : ℤ) : Homotopy (truncHi H hi) p :=
  homotopyCongr ((Homotopy.nullHomotopy (truncHiHom H hi) (fun i j h ↦ by
    simp only [truncHiHom]; split_ifs <;> simp [H.zero i j h])).add (Homotopy.refl p))
    (add_comm _ _) (zero_add p)

/-- The truncation is homotopic to `p`. -/
def truncLoHomotopy (lo : ℤ) : Homotopy (truncLo H lo) p :=
  homotopyCongr ((Homotopy.nullHomotopy (truncLoHom H lo) (fun i j h ↦ by
    simp only [truncLoHom]; split_ifs <;> simp [H.zero i j h])).add (Homotopy.refl p))
    (add_comm _ _) (zero_add p)

variable {H} (hp : p ≫ p = p) (hH : ∀ i j, p.f i ≫ H.hom i j ≫ p.f j = H.hom i j)
include hp hH

lemma truncHi_comp_p {hi : ℤ} (hx : ∀ r, hi < r → x.f r = 0) : truncHi H hi ≫ p = truncHi H hi := by
  ext r
  rcases lt_trichotomy r hi with hr | rfl | hr
  · simp [truncHi_f_below H hr, idem_f hp]
  · simp only [comp_f, truncHi_f_self, add_comp, assoc, idem_f hp, ← p.comm,
      kar_hom_right_assoc hp hH]
  · simp [truncHi_f_above H (hx r hr) hr]

lemma p_comp_truncHi {hi : ℤ} (hx : ∀ r, hi < r → x.f r = 0) : p ≫ truncHi H hi = truncHi H hi := by
  ext r
  rcases lt_trichotomy r hi with hr | rfl | hr
  · simp [truncHi_f_below H hr, idem_f hp]
  · simp only [comp_f, truncHi_f_self, comp_add, idem_f hp, kar_hom_left_assoc hp hH]
  · simp [truncHi_f_above H (hx r hr) hr]

lemma truncHi_idem {hi : ℤ} (hx : ∀ r, hi < r → x.f r = 0) :
    truncHi H hi ≫ truncHi H hi = truncHi H hi := by
  ext r
  rcases lt_trichotomy r hi with hr | rfl | hr
  · simp [truncHi_f_below H hr, idem_f hp]
  · have hk : C.d (r + 1) r ≫ H.hom r (r + 1) ≫ C.d (r + 1) r = -(p.f (r + 1) ≫ C.d (r + 1) r) := by
      have h := homotopy_comm H (r + 1) r (r + 1 + 1) (down_rel_succ r) (down_rel_succ (r + 1))
      rw [hx (r + 1) (by omega)] at h
      rw [← assoc, show C.d (r + 1) r ≫ H.hom r (r + 1) = -(H.hom (r + 1) (r + 1 + 1) ≫
        C.d (r + 1 + 1) (r + 1)) - p.f (r + 1) by rw [← sub_eq_zero, h]; abel]
      simp
    simp only [comp_f, truncHi_f_self, add_comp, comp_add, assoc, idem_f hp, ← p.comm,
      kar_hom_left_assoc hp hH, kar_hom_right_assoc hp hH, hk, comp_neg]
    abel
  · simp [truncHi_f_above H (hx r hr) hr]

lemma truncLo_comp_p {lo : ℤ} (hx : ∀ r, r < lo → x.f r = 0) : truncLo H lo ≫ p = truncLo H lo := by
  ext r
  rcases lt_trichotomy r lo with hr | rfl | hr
  · simp [truncLo_f_below H (hx r hr) hr]
  · simp only [comp_f, truncLo_f_self, add_comp, assoc, idem_f hp, kar_hom_right hp hH]
  · simp [truncLo_f_above H hr, idem_f hp]

lemma p_comp_truncLo {lo : ℤ} (hx : ∀ r, r < lo → x.f r = 0) : p ≫ truncLo H lo = truncLo H lo := by
  ext r
  rcases lt_trichotomy r lo with hr | rfl | hr
  · simp [truncLo_f_below H (hx r hr) hr]
  · simp only [comp_f, truncLo_f_self, comp_add, idem_f hp, p.comm_assoc, kar_hom_left hp hH]
  · simp [truncLo_f_above H hr, idem_f hp]

lemma truncLo_idem {lo : ℤ} (hx : ∀ r, r < lo → x.f r = 0) :
    truncLo H lo ≫ truncLo H lo = truncLo H lo := by
  ext r
  rcases lt_trichotomy r lo with hr | rfl | hr
  · simp [truncLo_f_below H (hx r hr) hr]
  · have hk : C.d r (r - 1) ≫ H.hom (r - 1) r ≫ C.d r (r - 1) = -(C.d r (r - 1) ≫ p.f (r - 1)) := by
      have h := homotopy_comm H (r - 1) (r - 1 - 1) r (down_rel_pred (r - 1)) (down_rel_pred r)
      rw [hx (r - 1) (by omega)] at h
      rw [show H.hom (r - 1) r ≫ C.d r (r - 1) = -(C.d (r - 1) (r - 1 - 1) ≫
        H.hom (r - 1 - 1) (r - 1)) - p.f (r - 1) by rw [← sub_eq_zero, h]; abel]
      simp
    simp only [comp_f, truncLo_f_self, add_comp, comp_add, assoc, idem_f hp, p.comm_assoc,
      kar_hom_right hp hH, reassoc_of% hk, neg_comp]
    abel
  · simp [truncLo_f_above H hr, idem_f hp]

/-- `(C, p) ≃ (C, truncHi H hi)` via the sub-idempotent itself. -/
@[simps]
def truncHiEquiv {hi : ℤ} (hx : ∀ r, hi < r → x.f r = 0) : KarHtpyEquiv p (truncHi H hi) where
  f := truncHi H hi
  g := truncHi H hi
  pf := p_comp_truncHi hp hH hx
  fp := truncHi_idem hp hH hx
  pg := truncHi_idem hp hH hx
  gp := truncHi_comp_p hp hH hx
  fg := (Homotopy.ofEq (truncHi_idem hp hH hx)).trans (truncHiHomotopy H hi)
  gf := Homotopy.ofEq (truncHi_idem hp hH hx)

/-- `(C, p) ≃ (C, truncLo H lo)` via the sub-idempotent itself. -/
@[simps]
def truncLoEquiv {lo : ℤ} (hx : ∀ r, r < lo → x.f r = 0) : KarHtpyEquiv p (truncLo H lo) where
  f := truncLo H lo
  g := truncLo H lo
  pf := p_comp_truncLo hp hH hx
  fp := truncLo_idem hp hH hx
  pg := truncLo_idem hp hH hx
  gp := truncLo_comp_p hp hH hx
  fg := (Homotopy.ofEq (truncLo_idem hp hH hx)).trans (truncLoHomotopy H lo)
  gf := Homotopy.ofEq (truncLo_idem hp hH hx)

end Trunc

namespace KarHtpyEquiv

variable {C C' : ChainComplex V ℤ} {p : C ⟶ C} {p' : C' ⟶ C'} (e : KarHtpyEquiv p p')
  (hp' : p' ≫ p' = p')

/-- Truncate the target of `e` above `hi` (where `(C, p)` vanishes above `hi`). -/
def cutHi (hi : ℤ) (hs : ∀ r, hi < r → p.f r = 0) : KarHtpyEquiv p (truncHi (e.karGf hp') hi) :=
  e.trans (truncHiEquiv hp' (e.karGf_kar hp') fun r hr ↦ e.gf_f_eq_zero (hs r hr))

lemma cutHi_idem (hi : ℤ) (hs : ∀ r, hi < r → p.f r = 0) :
    truncHi (e.karGf hp') hi ≫ truncHi (e.karGf hp') hi = truncHi (e.karGf hp') hi :=
  truncHi_idem hp' (e.karGf_kar hp') fun r hr ↦ e.gf_f_eq_zero (hs r hr)

/-- The target idempotent `p'` truncated to `[lo, hi]` (where `(C, p)` is supported): a
sub-idempotent of `p'` on the same complex `C'`. -/
def truncIdem (lo hi : ℤ) (hs : SupportedIn p lo hi) : C' ⟶ C' :=
  truncLo ((e.cutHi hp' hi fun r hr ↦ hs r (Or.inr hr)).karGf
    (e.cutHi_idem hp' hi fun r hr ↦ hs r (Or.inr hr))) lo

variable (lo hi : ℤ) (hs : SupportedIn p lo hi)

private lemma hx_lo : ∀ r, r < lo → ((e.cutHi hp' hi fun r hr ↦ hs r (Or.inr hr)).g ≫
    (e.cutHi hp' hi fun r hr ↦ hs r (Or.inr hr)).f).f r = 0 :=
  fun r hr ↦ KarHtpyEquiv.gf_f_eq_zero _ (hs r (Or.inl hr))

lemma truncIdem_idem : e.truncIdem hp' lo hi hs ≫ e.truncIdem hp' lo hi hs =
    e.truncIdem hp' lo hi hs :=
  truncLo_idem (e.cutHi_idem hp' hi fun r hr ↦ hs r (Or.inr hr)) (KarHtpyEquiv.karGf_kar _ _) (e.hx_lo hp' lo hi hs)

/-- **Truncation**: `(C, p) ≃ (C', truncIdem)`. -/
def trunc : KarHtpyEquiv p (e.truncIdem hp' lo hi hs) :=
  (e.cutHi hp' hi fun r hr ↦ hs r (Or.inr hr)).trans
    (truncLoEquiv (e.cutHi_idem hp' hi fun r hr ↦ hs r (Or.inr hr)) (KarHtpyEquiv.karGf_kar _ _) (e.hx_lo hp' lo hi hs))

lemma supportedIn_truncIdem : SupportedIn (e.truncIdem hp' lo hi hs) lo hi := by
  intro r hr
  rcases hr with hr | hr
  · exact truncLo_f_below _ (e.hx_lo hp' lo hi hs r hr) hr
  · rw [truncIdem, ← p_comp_truncLo (e.cutHi_idem hp' hi fun r hr ↦ hs r (Or.inr hr)) (KarHtpyEquiv.karGf_kar _ _)
      (e.hx_lo hp' lo hi hs), comp_f, truncHi_f_above _ (e.gf_f_eq_zero (hs r (Or.inr hr))) hr,
      zero_comp]

/-- The truncated idempotent is a summand of `p'`. -/
lemma p_comp_truncIdem : p' ≫ e.truncIdem hp' lo hi hs = e.truncIdem hp' lo hi hs := by
  rw [truncIdem, ← p_comp_truncLo (e.cutHi_idem hp' hi fun r hr ↦ hs r (Or.inr hr)) (KarHtpyEquiv.karGf_kar _ _)
      (e.hx_lo hp' lo hi hs), ← assoc, p_comp_truncHi hp' (e.karGf_kar hp')
      fun r hr ↦ e.gf_f_eq_zero (hs r (Or.inr hr))]

lemma truncIdem_comp_p : e.truncIdem hp' lo hi hs ≫ p' = e.truncIdem hp' lo hi hs := by
  rw [truncIdem, ← truncLo_comp_p (e.cutHi_idem hp' hi fun r hr ↦ hs r (Or.inr hr)) (KarHtpyEquiv.karGf_kar _ _)
      (e.hx_lo hp' lo hi hs), assoc, truncHi_comp_p hp' (e.karGf_kar hp')
      fun r hr ↦ e.gf_f_eq_zero (hs r (Or.inr hr))]

end KarHtpyEquiv

/-! ### Transport of Poincaré complexes -/

namespace SymPoincare

variable {J : StrictInvolution V} {N : ℤ}

/-- Transport of `P = (C, p, φ)` along a Kar equivalence `e : (C, p) ≃ (C', p')`:
`(C', p', f φ f^*)`. -/
@[simps, implicit_reducible]
def transport (P : SymPoincare J N) {C' : ChainComplex V ℤ} {p' : C' ⟶ C'} (hp' : p' ≫ p' = p')
    (hs : SupportedIn p' 0 N) (e : KarHtpyEquiv P.p p') : SymPoincare J N where
  C := C'
  p := p'
  p_idem := hp'
  support := hs
  φ := dualHom J N e.f ≫ P.φ ≫ e.f
  φ_kar := by simp only [assoc, e.fp]; rw [← assoc, ← dualHom_comp, e.fp]
  symm := P.symm.conj e.f
  poincare := (e.dual J N).isKarEquiv.comp (IsKarEquiv.comp P.poincare e.isKarEquiv
    (dualHom_idem P.p_idem) P.p_idem hp') (dualHom_idem hp') (dualHom_idem P.p_idem) hp'

/-- `P` is homotopy isometric to its transport. -/
@[simps]
def transportIsometry (P : SymPoincare J N) {C' : ChainComplex V ℤ} {p' : C' ⟶ C'}
    (hp' : p' ≫ p' = p') (hs : SupportedIn p' 0 N) (e : KarHtpyEquiv P.p p') :
    HomotopyIsometry P (P.transport hp' hs e) :=
  ⟨e.f, e.g, e.f_kar, e.g_kar, e.fg, e.gf, Homotopy.refl _⟩

lemma isometric_transport (P : SymPoincare J N) {C' : ChainComplex V ℤ} {p' : C' ⟶ C'}
    (hp' : p' ≫ p' = p') (hs : SupportedIn p' 0 N) (e : KarHtpyEquiv P.p p') :
    Isometric P (P.transport hp' hs e) :=
  ⟨P.transportIsometry hp' hs e⟩

/-- Transport along a Kar equivalence `(C, p) ≃ (C', p')` with `(C', p')` arbitrary: the
target idempotent is first truncated to `[0, N]` (`KarHtpyEquiv.trunc`). -/
abbrev transportTrunc (P : SymPoincare J N) {C' : ChainComplex V ℤ} {p' : C' ⟶ C'}
    (hp' : p' ≫ p' = p') (e : KarHtpyEquiv P.p p') : SymPoincare J N :=
  P.transport (e.truncIdem_idem hp' 0 N P.support) (e.supportedIn_truncIdem hp' 0 N P.support)
    (e.trunc hp' 0 N P.support)

lemma isometric_transportTrunc (P : SymPoincare J N) {C' : ChainComplex V ℤ} {p' : C' ⟶ C'}
    (hp' : p' ≫ p' = p') (e : KarHtpyEquiv P.p p') : Isometric P (P.transportTrunc hp' e) :=
  P.isometric_transport _ _ _

/-- A homotopy isometry as a Kar equivalence. -/
@[simps]
def HomotopyIsometry.toKarHtpyEquiv {P Q : SymPoincare J N} (e : HomotopyIsometry P Q) :
    KarHtpyEquiv P.p Q.p :=
  ⟨e.f, e.g, e.p_comp_f, e.f_comp_p, e.p_comp_g, e.g_comp_p, e.fg, e.gf⟩

end SymPoincare

lemma Lconc.cls_transport {A : InvCat} {N : ℤ} (P : SymPoincare A.inv N)
    {C' : ChainComplex A ℤ} {p' : C' ⟶ C'} (hp' : p' ≫ p' = p') (hs : SupportedIn p' 0 N)
    (e : KarHtpyEquiv P.p p') : cls (P.transport hp' hs e) = cls P :=
  (cls_eq_of_isometry (P.transportIsometry hp' hs e)).symm

lemma Lconc.cls_transportTrunc {A : InvCat} {N : ℤ} (P : SymPoincare A.inv N)
    {C' : ChainComplex A ℤ} {p' : C' ⟶ C'} (hp' : p' ≫ p' = p') (e : KarHtpyEquiv P.p p') :
    cls (P.transportTrunc hp' e) = cls P :=
  cls_transport _ _ _ _

/-! ### The five lemma for cones in `Kar V` -/

section Susp

variable {B B' : ChainComplex V ℤ}

/-- The suspension `ΣB`: `(ΣB)_n = B_{n-1}`, `d = -d`. -/
@[simps, implicit_reducible]
def susp (B : ChainComplex V ℤ) : ChainComplex V ℤ where
  X n := B.X (n - 1)
  d n n' := -B.d (n - 1) (n' - 1)
  shape n n' h := by
    rw [B.shape, neg_zero]
    simp only [ComplexShape.down_Rel] at h ⊢
    omega
  d_comp_d' n n' n'' _ _ := by simp

/-- The suspension of a chain map. -/
@[simps]
def suspMap (f : B ⟶ B') : susp B ⟶ susp B' where
  f n := f.f (n - 1)

@[simp]
lemma suspMap_comp {B'' : ChainComplex V ℤ} (f : B ⟶ B') (g : B' ⟶ B'') :
    suspMap (f ≫ g) = suspMap f ≫ suspMap g := rfl

/-- The suspension of a homotopy. -/
def suspHomotopy {f g : B ⟶ B'} (H : Homotopy f g) : Homotopy (suspMap f) (suspMap g) where
  hom n m := -H.hom (n - 1) (m - 1)
  zero n m h := by
    rw [H.zero, neg_zero]
    simp only [ComplexShape.down_Rel] at h ⊢
    omega
  comm n := by
    rw [dNext_eq _ (down_rel_pred n), prevD_eq _ (down_rel_succ n)]
    have h := homotopy_comm H (n - 1) (n - 1 - 1) (n + 1 - 1) (down_rel_pred _)
      (by simp only [ComplexShape.down_Rel]; omega)
    simp only [susp_d, suspMap_f, neg_comp, comp_neg, neg_neg, h]

lemma isKarEquiv_suspMap {e : B ⟶ B} {e' : B' ⟶ B'} {m : B ⟶ B'} (h : IsKarEquiv e e' m) :
    IsKarEquiv (suspMap e) (suspMap e') (suspMap m) := by
  obtain ⟨g, hg, ⟨H₁⟩, ⟨H₂⟩⟩ := h
  exact ⟨suspMap g, by rw [← suspMap_comp, ← suspMap_comp, hg], ⟨suspHomotopy H₁⟩,
    ⟨suspHomotopy H₂⟩⟩

end Susp

section ConeSplit

open homotopyCofiber

variable [HasBinaryBiproducts V] {B D : ChainComplex V ℤ} (j : B ⟶ D)

/-- The projection `Cone(j) ⟶ ΣB`, `(x, c) ↦ x`. -/
@[simps]
def coneToSusp : cone j ⟶ susp B where
  f n := fstX j n (n - 1) (down_rel_pred n)
  comm' n n' h := by
    obtain rfl : n' = n - 1 := by simp only [ComplexShape.down_Rel] at h; omega
    simp [d_fstX j n (n - 1) (n - 1 - 1) (down_rel_pred n) (down_rel_pred (n - 1))]

variable {j} {pB : B ⟶ B} {pD : D ⟶ D} (hB : pB ≫ pB = pB) (hD : pD ≫ pD = pD)
  (hj : pB ≫ j ≫ pD = j)

/-- The degreewise split sequence `0 ⟶ (D, p_D) ⟶ (Cone(j), p_B ⊕ p_D) ⟶ (ΣB, Σp_B) ⟶ 0` in
`Kar V`. -/
def coneKarSplit : KarSplit pD (coneMap pB pD (comm_of_kar hB hD hj)) (suspMap pB) (pD ≫ inr j)
    (coneToSusp j ≫ suspMap pB) where
  t n := sndX j n ≫ pD.f n
  s n := pB.f (n - 1) ≫ inlX j (n - 1) n (down_rel_pred n)
  t_kar n := by simp [idem_f hD]
  s_kar n := by simp [idem_f_assoc hB]
  it n := by simp [idem_f hD]
  sq n := by simp [idem_f hB]
  total n := by
    rw [coneMap_f _ n (n - 1) (down_rel_pred n)]
    simp [idem_f_assoc hB, idem_f_assoc hD, add_comm]

end ConeSplit

section ConeFive

variable [HasFiniteBiproducts V] [HasBinaryBiproducts V] {B D B' D' : ChainComplex V ℤ}
  {j : B ⟶ D} {j' : B' ⟶ D'} {pB : B ⟶ B} {pD : D ⟶ D} {pB' : B' ⟶ B'} {pD' : D' ⟶ D'}

/-- **The five lemma for cones** in `Kar V`: a strictly commuting square of Kar maps whose sides
are Kar equivalences induces a Kar equivalence of cones. -/
theorem isKarEquiv_coneMap (hB : pB ≫ pB = pB) (hD : pD ≫ pD = pD) (hB' : pB' ≫ pB' = pB')
    (hD' : pD' ≫ pD' = pD') (hj : pB ≫ j ≫ pD = j) (hj' : pB' ≫ j' ≫ pD' = j') {m : B ⟶ B'}
    {n : D ⟶ D'} (hm : pB ≫ m ≫ pB' = m) (hn : pD ≫ n ≫ pD' = n) (h : m ≫ j' = j ≫ n)
    (em : IsKarEquiv pB pB' m) (en : IsKarEquiv pD pD' n) :
    IsKarEquiv (coneMap pB pD (comm_of_kar hB hD hj)) (coneMap pB' pD' (comm_of_kar hB' hD' hj'))
      (coneMap m n h) := by
  have hm₁ := kar_left hB hm
  have hm₂ := kar_right hB' hm
  have hn₁ := kar_left hD hn
  have hn₂ := kar_right hD' hn
  refine isKarEquiv_middle hD (coneMap_idem _ hB hD) (by rw [← suspMap_comp, hB]) hD'
    (coneMap_idem _ hB' hD') (by rw [← suspMap_comp, hB']) ?_ ?_ ?_ ?_ (coneKarSplit hB hD hj)
    (coneKarSplit hB' hD' hj') hn ?_ ?_ ?_ ?_ en (isKarEquiv_suspMap em)
  · ext i; simp [idem_f_assoc hD]
  · ext i; simp [idem_f hB]
  · ext i; simp [idem_f_assoc hD']
  · ext i; simp [idem_f hB']
  · rw [coneMap_comp, coneMap_comp]; congr 1
  · rw [← suspMap_comp, ← suspMap_comp, hm]
  · ext i; simp [← comp_f_assoc, hn₁, hn₂]
  · ext i
    have e₁ : pB.f (i - 1) ≫ m.f (i - 1) = m.f (i - 1) := by rw [← comp_f, hm₁]
    have e₂ : m.f (i - 1) ≫ pB'.f (i - 1) = m.f (i - 1) := by rw [← comp_f, hm₂]
    simp only [comp_f, coneToSusp_f, suspMap_f, coneMap_f_fstX_assoc, assoc, e₁, e₂]

end ConeFive

/-! ### Transport of Poincaré pairs -/

section PairLemmas

variable {J : StrictInvolution V} {N : ℤ}

/-- Ranicki's `T` commutes with conjugation: `T(a^* h a) = a^* (T h) a`. -/
lemma transposeHomFamily_conj' {C D : ChainComplex V ℤ} (a : C ⟶ D)
    (h : ∀ i k, (dualComplex J N C).X i ⟶ C.X k) :
    transposeHomFamily J N (C := D) (D := D) (fun i k ↦ (dualHom J N a).f i ≫ h i k ≫ a.f k) =
      fun i k ↦ (dualHom J N a).f i ≫ transposeHomFamily J N h i k ≫ a.f k := by
  funext r r'
  simp only [transposeHomFamily, dualHom_f, J.star_comp, J.star_star, bidual_hom_f,
    Linear.units_smul_comp, Linear.comp_units_smul, assoc, f_comp_eqToHom a (sub_sub_cancel N r')]

lemma transposeHomFamily_eq {C : ChainComplex V ℤ} {φ φ' : dualComplex J N C ⟶ C}
    {H : Homotopy φ φ'} (hH : IsSymmHomotopy J N H) : transposeHomFamily J N H.hom = H.hom := by
  rwa [IsSymmHomotopy, transposeHomotopy_hom] at hH

/-- Two out of three for Kar equivalences: if `a` and `a ≫ b` are, so is `b`. -/
lemma IsKarEquiv.of_comp_left {X Y Z : ChainComplex V ℤ} {e : X ⟶ X} {e' : Y ⟶ Y} {e'' : Z ⟶ Z}
    {a : X ⟶ Y} {b : Y ⟶ Z} (ha : IsKarEquiv e e' a) (ha' : e ≫ a ≫ e' = a)
    (hab : IsKarEquiv e e'' (a ≫ b)) (hb : e' ≫ b ≫ e'' = b) (he : e ≫ e = e)
    (he' : e' ≫ e' = e') (he'' : e'' ≫ e'' = e'') : IsKarEquiv e' e'' b := by
  obtain ⟨a', ha'', ⟨H₁⟩, ⟨H₂⟩⟩ := ha
  have hinv : IsKarEquiv e' e a' := ⟨a, ha', ⟨H₂⟩, ⟨H₁⟩⟩
  exact (hinv.comp hab he' he he'').of_homotopy
    (homotopyCongr (H₁.compRight b) (assoc _ _ _) (kar_left he' hb))

section RelDuality

variable [HasBinaryBiproducts V] {B D : ChainComplex V ℤ} {j : B ⟶ D}
  {φ₁ φ₂ : dualComplex J N B ⟶ B}

open homotopyCofiber in
/-- Changing `(φ, δφ)` along a homotopy `W : φ₁ ≃ φ₂` with `δφ₁ = j W j^* + δφ₂` changes the
relative duality map `Ψ` by the homotopy `K(α, β) = ± j W β`. -/
def transportRelDualityHomotopy (W : Homotopy φ₁ φ₂) (H₁ : Homotopy (dualHom J N j ≫ φ₁ ≫ j) 0)
    (H₂ : Homotopy (dualHom J N j ≫ φ₂ ≫ j) 0)
    (hH : ∀ r r', H₁.hom r r' = (dualHom J N j).f r ≫ W.hom r r' ≫ j.f r' + H₂.hom r r') :
    Homotopy (relDuality H₁) (relDuality H₂) where
  hom r r' := (r + 1).negOnePow •
    J.star (inlX j (N - r) (N + 1 - r) (down_rel_sub N r)) ≫ W.hom r r' ≫ j.f r'
  zero r r' h := by rw [W.zero r r' h]; simp
  comm r := by
    rw [dNext_eq _ (down_rel_pred r), prevD_eq _ (down_rel_succ r)]
    have hW := homotopy_comm W r (r - 1) (r + 1) (down_rel_pred r) (down_rel_succ r)
    have hR : relTop H₁ r = (D.XIsoOfEq (by omega : N + 1 - r = N - (r - 1))).hom ≫
        (dualHom J N j).f (r - 1) ≫ W.hom (r - 1) r ≫ j.f r + relTop H₂ r := by
      simp [relTop, hH]
    have hrel : (ComplexShape.down ℤ).Rel (N + 1 - (r - 1)) (N + 1 - r) := by
      simp only [ComplexShape.down_Rel]; omega
    apply cone.ext_star (J := J) j (N + 1 - r) (N - r) (down_rel_sub N r)
    · simp only [relDuality_f, dualComplex_d, comp_add, add_comp, assoc, Linear.comp_units_smul,
        Linear.units_smul_comp, cone.star_fstX_inrX_assoc, cone.star_fstX_inlX_assoc, zero_comp,
        zero_add, cone.star_fstX_d_assoc j _ _ _ hrel, neg_comp,
        cone.star_fstX_inlX'_assoc j hrel (down_rel_sub N (r - 1)), hW, Hom.comm]
      rw [sub_add_cancel, star_d_XIsoOfEq_assoc]
      simp [Int.negOnePow_succ, smul_add, smul_smul]
    · simp only [relDuality_f, dualComplex_d, comp_add, add_comp, assoc, Linear.comp_units_smul,
        Linear.units_smul_comp, cone.star_sndX_inrX_assoc, cone.star_sndX_inlX_assoc, zero_comp,
        add_zero, cone.star_sndX_d_assoc j _ _ hrel, hR,
        cone.star_fstX_inlX'_assoc j hrel (down_rel_sub N (r - 1)), comp_zero, smul_zero]
      rw [sub_add_cancel, star_f_XIsoOfEq_assoc]
      simp [smul_smul]

lemma relDuality_comp_pD {pD : D ⟶ D} (hj : j ≫ pD = j) (H : Homotopy (dualHom J N j ≫ φ₁ ≫ j) 0)
    (hH : ∀ r r', H.hom r r' ≫ pD.f r' = H.hom r r') : relDuality H ≫ pD = relDuality H := by
  have hj' (i : ℤ) : j.f i ≫ pD.f i = j.f i := by rw [← comp_f, hj]
  ext r
  simp [relTop, hH, hj']

end RelDuality

end PairLemmas

namespace SymPair

open homotopyCofiber

variable [HasBinaryBiproducts V] {J : StrictInvolution V} {N : ℤ}

section TransportD

variable (X : SymPair J N) {D' : ChainComplex V ℤ} {pD' : D' ⟶ D'} (e : KarHtpyEquiv X.pD pD')

/-- The relative structure `f δφ f^*` on `j f`. -/
def transportDδφ : Homotopy (dualHom J N (X.j ≫ e.f) ≫ X.bd.φ ≫ X.j ≫ e.f) 0 :=
  homotopyCongr ((X.δφ.compRight e.f).compLeft (dualHom J N e.f)) (by simp) (by simp)

@[simp]
lemma transportDδφ_hom (r r' : ℤ) : (X.transportDδφ e).hom r r' =
    (dualHom J N e.f).f r ≫ X.δφ.hom r r' ≫ e.f.f r' := rfl

lemma relTop_transportDδφ (r : ℤ) :
    relTop (X.transportDδφ e) r = J.star (e.f.f (N + 1 - r)) ≫ relTop X.δφ r ≫ e.f.f r := by
  simp only [relTop, transportDδφ_hom, dualHom_f, assoc, star_f_XIsoOfEq_assoc]

/-- `Ψ' = c^* Ψ f` for the cone map `c = p_C ⊕ f : Cone(j) ⟶ Cone(j f)`. -/
lemma relDuality_transportDδφ (hc : X.bd.p ≫ X.j ≫ e.f = X.j ≫ e.f) :
    relDuality (X.transportDδφ e) = dualHom J (N + 1) (coneMap _ _ hc) ≫ X.Ψ ≫ e.f := by
  ext r
  have hφ : J.star (X.bd.p.f (N - r)) ≫ X.bd.φ.f r = X.bd.φ.f r := by
    rw [← dualHom_f, ← comp_f, X.bd.dualHom_p_comp_φ]
  simp [star_coneMap_f hc _ _ (down_rel_sub N r), relTop_transportDδφ, reassoc_of% hφ, add_comm]

lemma transportDδφ_kar (r r' : ℤ) :
    (dualHom J N pD').f r ≫ (X.transportDδφ e).hom r r' ≫ pD'.f r' = (X.transportDδφ e).hom r r' := by
  have h₁ : (dualHom J N pD').f r ≫ (dualHom J N e.f).f r = (dualHom J N e.f).f r := by
    rw [← comp_f, ← dualHom_comp, e.fp]
  have h₂ : e.f.f r' ≫ pD'.f r' = e.f.f r' := by rw [← comp_f, e.fp]
  simp only [transportDδφ_hom, assoc, h₂, reassoc_of% h₁]

lemma isSymmHomotopy_transportDδφ : IsSymmHomotopy J N (X.transportDδφ e) := by
  rw [IsSymmHomotopy, transposeHomotopy_hom]
  have e₁ : (X.transportDδφ e).hom =
      fun r r' ↦ (dualHom J N e.f).f r ≫ X.δφ.hom r r' ≫ e.f.f r' := rfl
  rw [e₁, transposeHomFamily_conj', transposeHomFamily_eq X.symm]

variable [HasFiniteBiproducts V]

/-- **Transport of a pair along a target equivalence** `e : (D, p_D) ≃ (D', p_D')`:
`(j f : C ⟶ D', (f δφ f^*, φ))`, with the same boundary.  Poincaré since
`Ψ' = c^* Ψ f` with `c = p_C ⊕ f` an equivalence of cones. -/
@[simps, implicit_reducible]
def transportD (hpD' : pD' ≫ pD' = pD') (hs : SupportedIn pD' 0 (N + 1)) : SymPair J N where
  bd := X.bd
  D := D'
  pD := pD'
  pD_idem := hpD'
  support := hs
  j := X.j ≫ e.f
  j_kar := by simp
  δφ := X.transportDδφ e
  δφ_kar := X.transportDδφ_kar e
  symm := X.isSymmHomotopy_transportDδφ e
  poincare := by
    have hc : X.bd.p ≫ X.j ≫ e.f = X.j ≫ e.f := by simp
    rw [relDuality_transportDδφ X e hc]
    have hC := isKarEquiv_coneMap X.bd.p_idem X.pD_idem X.bd.p_idem hpD' X.j_kar
      (j' := X.j ≫ e.f) (by simp) (by simp) e.f_kar hc
      (KarHtpyEquiv.refl X.bd.p_idem).isKarEquiv e.isKarEquiv
    exact hC.dualHom.comp (X.poincare.comp e.isKarEquiv (dualHom_coneIdem_idem X) X.pD_idem hpD')
      (dualHom_idem (coneMap_idem _ X.bd.p_idem hpD')) (dualHom_coneIdem_idem X) hpD'

end TransportD

section TransportBd

variable [Linear ℚ V] (X : SymPair J N) {C' : ChainComplex V ℤ} {p' : C' ⟶ C'}
  (e : KarHtpyEquiv X.bd.p p')

/-- The Kar homotopy `(gf) φ (gf)^* ≃ φ` on the boundary, before symmetrization. -/
def bdW₀ : Homotopy (dualHom J N (e.f ≫ e.g) ≫ X.bd.φ ≫ e.f ≫ e.g) X.bd.φ :=
  karHomotopy (p := dualHom J N X.bd.p) (q := X.bd.p)
    (homotopyCongr (conjHomotopy e.fg (Homotopy.refl X.bd.φ)) rfl X.bd.φ_kar)
    (by simp only [assoc, e.gp]; rw [← assoc (dualHom J N X.bd.p), ← dualHom_comp, assoc, e.gp])
    X.bd.φ_kar

omit [Linear ℚ V] in
lemma bdW₀_kar (r r' : ℤ) : (dualHom J N X.bd.p).f r ≫ (X.bdW₀ e).hom r r' ≫ X.bd.p.f r' =
    (X.bdW₀ e).hom r r' := by
  have h₁ (i : ℤ) : X.bd.p.f i ≫ X.bd.p.f i = X.bd.p.f i := idem_f X.bd.p_idem i
  have h₂ : J.star (X.bd.p.f (N - r)) ≫ J.star (X.bd.p.f (N - r)) = J.star (X.bd.p.f (N - r)) := by
    rw [← J.star_comp, h₁]
  simp [bdW₀, h₁, reassoc_of% h₂]

/-- The symmetrized Kar homotopy `W : (gf) φ (gf)^* ≃ φ` on the boundary. -/
def bdW : Homotopy (dualHom J N (e.f ≫ e.g) ≫ X.bd.φ ≫ e.f ≫ e.g) X.bd.φ :=
  symmHomotopy (X.bd.symm.conj _) X.bd.symm (X.bdW₀ e)

lemma bdW_kar (r r' : ℤ) : (dualHom J N X.bd.p).f r ≫ (X.bdW e).hom r r' ≫ X.bd.p.f r' =
    (X.bdW e).hom r r' :=
  kar_symmHomotopy_hom X.bd.p_idem _ _ _ (X.bdW₀_kar e) r r'

/-- The relative structure `j W j^* + δφ` on `j` for the boundary structure `(gf) φ (gf)^*`. -/
def transportBdδφ₀ :
    Homotopy (dualHom J N X.j ≫ (dualHom J N (e.f ≫ e.g) ≫ X.bd.φ ≫ e.f ≫ e.g) ≫ X.j) 0 :=
  (((X.bdW e).compRight X.j).compLeft (dualHom J N X.j)).trans X.δφ

/-- The relative structure of the transported pair, on `j' = g j`. -/
def transportBdδφ : Homotopy (dualHom J N (e.g ≫ X.j) ≫ (dualHom J N e.f ≫ X.bd.φ ≫ e.f) ≫
    e.g ≫ X.j) 0 :=
  homotopyCongr (X.transportBdδφ₀ e) (by simp) rfl

lemma transportBdδφ_hom : (X.transportBdδφ e).hom =
    (fun r r' ↦ (dualHom J N X.j).f r ≫ (X.bdW e).hom r r' ≫ X.j.f r') + X.δφ.hom := rfl

lemma transportBdδφ_kar (r r' : ℤ) : (dualHom J N X.pD).f r ≫ (X.transportBdδφ e).hom r r' ≫
    X.pD.f r' = (X.transportBdδφ e).hom r r' := by
  have h₁ : (dualHom J N X.pD).f r ≫ (dualHom J N X.j).f r = (dualHom J N X.j).f r := by
    rw [← comp_f, ← dualHom_comp, X.j_comp_pD]
  have h₂ : X.j.f r' ≫ X.pD.f r' = X.j.f r' := by rw [← comp_f, X.j_comp_pD]
  simp only [transportBdδφ_hom, Pi.add_apply, comp_add, add_comp, assoc, h₂, reassoc_of% h₁,
    X.δφ_kar]

lemma isSymmHomotopy_transportBdδφ : IsSymmHomotopy J N (X.transportBdδφ e) := by
  rw [IsSymmHomotopy, transposeHomotopy_hom, transportBdδφ_hom, transposeHomFamily_add,
    transposeHomFamily_conj', transposeHomFamily_eq (show IsSymmHomotopy J N (X.bdW e) from
      isSymmHomotopy_symmHomotopy _ _ _), transposeHomFamily_eq X.symm]

variable [HasFiniteBiproducts V]

lemma isKarEquiv_transportBd (hp' : p' ≫ p' = p') (hj : p' ≫ (e.g ≫ X.j) ≫ X.pD = e.g ≫ X.j) :
    IsKarEquiv (dualHom J (N + 1) (coneMap p' X.pD (comm_of_kar hp' X.pD_idem hj))) X.pD
      (relDuality (X.transportBdδφ e)) := by
  have hc : e.g ≫ X.j = (e.g ≫ X.j) ≫ X.pD := by simp
  have hC := isKarEquiv_coneMap hp' X.pD_idem X.bd.p_idem X.pD_idem hj X.j_kar e.g_kar
    (by simp) hc e.symm.isKarEquiv (KarHtpyEquiv.refl X.pD_idem).isKarEquiv
  have hl (r r' : ℤ) : (dualHom J N X.pD).f r ≫ (X.transportBdδφ e).hom r r' =
      (X.transportBdδφ e).hom r r' := by
    conv_lhs => rw [← X.transportBdδφ_kar e]
    rw [← assoc, ← comp_f, ← dualHom_comp, X.pD_idem, X.transportBdδφ_kar]
  have hr (r r' : ℤ) : (X.transportBdδφ e).hom r r' ≫ X.pD.f r' = (X.transportBdδφ e).hom r r' := by
    conv_lhs => rw [← X.transportBdδφ_kar e]
    rw [assoc, assoc, ← comp_f, X.pD_idem, X.transportBdδφ_kar]
  have hid : dualHom J (N + 1) (coneMap _ _ hc) ≫ relDuality (X.transportBdδφ e) =
      relDuality (X.transportBdδφ₀ e) := by
    ext r
    simp [star_coneMap_f hc _ _ (down_rel_sub N r), star_comp_relTop _ hl]
    rfl
  have hΨ := X.poincare.of_homotopy (homotopyCongr (transportRelDualityHomotopy (X.bdW e)
    (X.transportBdδφ₀ e) X.δφ fun _ _ ↦ rfl).symm rfl hid.symm)
  refine IsKarEquiv.of_comp_left hC.dualHom (dualHom_kar ?_) hΨ ?_
    (dualHom_coneIdem_idem X) (dualHom_idem (coneMap_idem _ hp' X.pD_idem)) X.pD_idem
  · rw [coneMap_comp, coneMap_comp]; congr 1 <;> simp
  · have hφ' : dualHom J N p' ≫ (dualHom J N e.f ≫ X.bd.φ ≫ e.f) =
        dualHom J N e.f ≫ X.bd.φ ≫ e.f := by rw [← assoc, ← dualHom_comp, e.fp]
    rw [← assoc, dualHom_coneMap_comp_relDuality _ _ hφ' hl, relDuality_comp_pD (by simp) _ hr]

/-- **Transport of a pair along a boundary equivalence** `e : (C, p_C) ≃ (C', p')`:
`(g j : C' ⟶ D, (j W j^* + δφ, f φ f^*))`, with boundary `bd.transport e` and the same target;
`W : (gf) φ (gf)^* ≃ φ` is the `ℚ`-symmetrized Kar homotopy.  Poincaré since
`c^* Ψ' ≃ Ψ` for the cone equivalence `c = g ⊕ p_D` (`transportRelDualityHomotopy`). -/
@[simps, implicit_reducible]
def transportBd (hp' : p' ≫ p' = p') (hs : SupportedIn p' 0 N) : SymPair J N where
  bd := X.bd.transport hp' hs e
  D := X.D
  pD := X.pD
  pD_idem := X.pD_idem
  support := X.support
  j := e.g ≫ X.j
  j_kar := by simp
  δφ := X.transportBdδφ e
  δφ_kar := X.transportBdδφ_kar e
  symm := X.isSymmHomotopy_transportBdδφ e
  poincare := X.isKarEquiv_transportBd e hp' (by simp)

/-- Transport along a boundary equivalence with arbitrary target idempotent, truncated to
`[0, N]` first. -/
abbrev transportBdTrunc (hp' : p' ≫ p' = p') : SymPair J N :=
  X.transportBd (e.trunc hp' 0 N X.bd.support) (e.truncIdem_idem hp' 0 N X.bd.support)
    (e.supportedIn_truncIdem hp' 0 N X.bd.support)

end TransportBd

section TransportBoth

variable [Linear ℚ V] [HasFiniteBiproducts V] (X : SymPair J N) {C' D' : ChainComplex V ℤ}
  {p' : C' ⟶ C'} {pD' : D' ⟶ D'} (e : KarHtpyEquiv X.bd.p p') (eD : KarHtpyEquiv X.pD pD')

/-- **Transport of a pair along an equivalence of pairs** `(e, e_D)`: boundary `bd.transport e`,
target `(D', p_D')`, map `g_C j f_D`. -/
abbrev transport (hp' : p' ≫ p' = p') (hs : SupportedIn p' 0 N) (hpD' : pD' ≫ pD' = pD')
    (hsD : SupportedIn pD' 0 (N + 1)) : SymPair J N :=
  (X.transportBd e hp' hs).transportD eD hpD' hsD

lemma transport_bd (hp' : p' ≫ p' = p') (hs : SupportedIn p' 0 N) (hpD' : pD' ≫ pD' = pD')
    (hsD : SupportedIn pD' 0 (N + 1)) :
    (X.transport e eD hp' hs hpD' hsD).bd = X.bd.transport hp' hs e := rfl

lemma transport_j (hp' : p' ≫ p' = p') (hs : SupportedIn p' 0 N) (hpD' : pD' ≫ pD' = pD')
    (hsD : SupportedIn pD' 0 (N + 1)) :
    (X.transport e eD hp' hs hpD' hsD).j = (e.g ≫ X.j) ≫ eD.f := rfl

/-- The square of the equivalence of pairs commutes up to homotopy: `f_C (g_C j f_D) ≃ j f_D`. -/
def transportSquare (hp' : p' ≫ p' = p') (hs : SupportedIn p' 0 N) (hpD' : pD' ≫ pD' = pD')
    (hsD : SupportedIn pD' 0 (N + 1)) :
    Homotopy (e.f ≫ (X.transport e eD hp' hs hpD' hsD).j) (X.j ≫ eD.f) :=
  homotopyCongr ((e.fg.compRight X.j).compRight eD.f) (by simp) (by simp)

/-- Transport along an equivalence of pairs with arbitrary idempotents, both truncated first. -/
abbrev transportTrunc (hp' : p' ≫ p' = p') (hpD' : pD' ≫ pD' = pD') : SymPair J N :=
  X.transport (e.trunc hp' 0 N X.bd.support) (eD.trunc hpD' 0 (N + 1) X.support)
    (e.truncIdem_idem hp' 0 N X.bd.support) (e.supportedIn_truncIdem hp' 0 N X.bd.support)
    (eD.truncIdem_idem hpD' 0 (N + 1) X.support) (eD.supportedIn_truncIdem hpD' 0 (N + 1) X.support)

end TransportBoth

end SymPair

/-- Null-cobordism is invariant under transport. -/
lemma NullCobordant.transport [HasFiniteBiproducts V] [HasBinaryBiproducts V] [Linear ℚ V]
    {J : StrictInvolution V} {N : ℤ} {P : SymPoincare J N} (h : NullCobordant P)
    {C' : ChainComplex V ℤ} {p' : C' ⟶ C'} (hp' : p' ≫ p' = p') (hs : SupportedIn p' 0 N)
    (e : KarHtpyEquiv P.p p') : NullCobordant (P.transport hp' hs e) := by
  obtain ⟨X, rfl⟩ := h
  exact ⟨X.transportBd e hp' hs, rfl⟩

end

end HSFormal.LTheory
