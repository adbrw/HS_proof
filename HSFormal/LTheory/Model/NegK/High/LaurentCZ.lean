import HSFormal.LTheory.Model.NegK.High.Laurent
import HSFormal.LTheory.Model.NegK.High.StablyIso

/-!
# Supports and half-line absorption in `L^l(C_ℤ Y)` (NegKHigh, module N3)

`blueprint/negK-high.md` §2 "Bounded categories", §3.6 (Lemma H), §7 row N3.

Throughout, `Y` is an `InvCat`, `𝒞 = C_ℤ(Y)` and morphisms live in `L^l 𝒞 = Lpow l Y.cz`.  Objects
of `L^l 𝒞` are objects of `𝒞` (`Lpow_carrier`), so cuts and half-line conditions apply verbatim.

* `PropLE' f b`: every coefficient of `f` has propagation `≤ b` (`exists_propLE'`, `PropLE'.comp`,
  `PropLE'.add`, ...).
* `chi X p = ι (cut X p).idem`: the degree-`0` cut idempotents (`chi_idem`, `chi_comp_chi`,
  `chi_comp_eq`, `comp_chi_eq`: a map of propagation `b` moves supports by at most `b`).
* `SuppIn p f`: `chi p ≫ f ≫ chi p = f` (support in `p × p`); stable under `+`, `-`, enlarging
  `p`, and composition with bounded maps after thickening (`SuppIn.comp_right`, `comp_left`).
  `LeftSupp f` (some `(-∞, c]`) and `RightSupp f` (some `[c, ∞)`) are two-sided ideals
  (`LeftSupp.comp_right`, ...).
* `extend_chi`, `PropLE'.extend`, `SuppIn.extend`, `LeftSupp.extend`, `RightSupp.extend`: these
  notions are compatible with the old-variable inclusion `L^l 𝒞 ⥤ L^{l+1} 𝒞` (`Lpow.extend`), and
  `w` has propagation `0` (`PropLE'.w`).
* **Lemma H.**  `InvCat.Swindle.karAbsorbs_lpow`: an Eilenberg swindle on `A` makes every Kar
  object of `L^l A` absorbed by a free object; hence every Kar object of `L^l 𝒞` supported in a
  half-line is absorbed (`karAbsorbs_lpow_of_negHalf`, `karAbsorbs_lpow_of_posHalf`), and so is
  every left- or right-supported idempotent (`karAbsorbs_of_leftSupp`,
  `karAbsorbs_of_rightSupp`).  Free objects of `L^l 𝒞` are absorbed (`karAbsorbs_lpow_id`).
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive Idempotents

noncomputable section

/-! ### The swindle in Laurent extensions (Lemma H, generic part) -/

namespace InvCat.Swindle

variable {A : InvCat}

/-- **Lemma H (generic).**  For an Eilenberg swindle `s` on `A`, every Kar object `(M, e)` of
`L^l A` is absorbed by the free object `Σ M`: the swindle data are the degree-`0` images of those
of `A` (`InvCat.Swindle.karAbsorbs`), natural for `L^l Σ` by `Lpow.mapNatTrans`. -/
theorem karAbsorbs_lpow (s : A.Swindle) (l : ℕ) {M : Lpow l (A : AddCat)}
    {e : (Lpow l (A : AddCat)).Mor M M} (he : e ≫ e = e) :
    KarAbsorbs e ((Lpow.map l s.sum.F).obj M) := by
  let φ₀ : InvCat.UnitaryIso (s.summand false) (𝟙 A) := s.summandIsoId
  let φ₁ : InvCat.UnitaryIso (s.summand true) s.sum := s.summandIsoShift.trans s.sumShiftIso
  let η₀ : 𝟭 A.carrier ⟶ s.sum.F := φ₀.iso.inv ≫ s.isFinSum.inc false
  let η₁ : s.sum.F ⟶ s.sum.F := φ₁.iso.inv ≫ s.isFinSum.inc true
  -- the base identities, as in `InvCat.Swindle.karAbsorbs`
  have hs₀ : A.inv.star (η₀.app M) = A.inv.star ((s.isFinSum.inc false).app M) ≫
      φ₀.iso.hom.app M := by
    erw [A.inv.star_comp, φ₀.star_inv]
    try rfl
  have hs₁ : A.inv.star (η₁.app M) = A.inv.star ((s.isFinSum.inc true).app M) ≫
      φ₁.iso.hom.app M := by
    erw [A.inv.star_comp, φ₁.star_inv]
    try rfl
  have h₀₀ : η₀.app M ≫ A.inv.star (η₀.app M) = 𝟙 _ := by
    erw [hs₀, assoc, ← assoc ((s.isFinSum.inc false).app M), s.isFinSum.inc_star_self false M,
      id_comp]
    exact φ₀.iso.inv_hom_id_app M
  have h₁₁ : η₁.app M ≫ A.inv.star (η₁.app M) = 𝟙 _ := by
    erw [hs₁, assoc, ← assoc ((s.isFinSum.inc true).app M), s.isFinSum.inc_star_self true M,
      id_comp]
    exact φ₁.iso.inv_hom_id_app M
  have h₀₁ : η₀.app M ≫ A.inv.star (η₁.app M) = 0 := by
    erw [hs₁, assoc, ← assoc ((s.isFinSum.inc false).app M),
      s.isFinSum.inc_star_ne false true (by simp) M, zero_comp, comp_zero]
  have h₁₀ : η₁.app M ≫ A.inv.star (η₀.app M) = 0 := by
    erw [hs₀, assoc, ← assoc ((s.isFinSum.inc true).app M),
      s.isFinSum.inc_star_ne true false (by simp) M, zero_comp, comp_zero]
  have htot : A.inv.star (η₀.app M) ≫ η₀.app M + A.inv.star (η₁.app M) ≫ η₁.app M = 𝟙 _ := by
    erw [hs₀, hs₁, assoc, assoc, φ₀.iso.hom_inv_id_app_assoc, φ₁.iso.hom_inv_id_app_assoc,
      ← s.isFinSum.total M, Fintype.sum_bool, add_comm]
  -- lift them along the degree-`0` inclusion
  have hn₀ := (Lpow.mapNatTrans l η₀).naturality e
  rw [Lpow.map_id_map] at hn₀
  have hn₁ := (Lpow.mapNatTrans l η₁).naturality e
  simp only [Lpow.mapNatTrans_app] at hn₀ hn₁
  refine karAbsorbs_of_swindle he (by rw [← Functor.map_comp, he])
    ((Lpow.incl (A : AddCat) l).map (η₀.app M))
    ((Lpow.incl (A : AddCat) l).map (A.inv.star (η₀.app M)))
    ((Lpow.incl (A : AddCat) l).map (η₁.app M))
    ((Lpow.incl (A : AddCat) l).map (A.inv.star (η₁.app M))) ?_ ?_ ?_ ?_ ?_ hn₀.symm hn₁.symm
  · rw [← Functor.map_comp, h₀₀]; exact (Lpow.incl (A : AddCat) l).map_id _
  · rw [← Functor.map_comp, h₁₁]; exact (Lpow.incl (A : AddCat) l).map_id _
  · rw [← Functor.map_comp, h₀₁, Functor.map_zero]
  · rw [← Functor.map_comp, h₁₀, Functor.map_zero]
  · rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_add, htot]
    exact (Lpow.incl (A : AddCat) l).map_id _

end InvCat.Swindle

namespace CZ.Lpow

variable {Y : InvCat} {l : ℕ}

/-! ### Propagation -/

/-- `f : X ⟶ Z` in `L^l(C_ℤ Y)` has propagation `≤ b`: every coefficient does. -/
def PropLE' {X Z : Lpow l (Y.cz : AddCat)} (f : (Lpow l (Y.cz : AddCat)).Mor X Z) (b : ℕ) :
    Prop :=
  ∀ γ, CZ.PropLE (Lpow.coeff γ f).1 b

variable {X Z T : Lpow l (Y.cz : AddCat)}

/-- Propagation-`≤ (b + c)` morphisms, as an additive submonoid of `Hom_𝒞(X, Z)`. -/
def propLESubmonoid (X Z : Y.cz) (b : ℕ) : AddSubmonoid (X ⟶ Z) where
  carrier := {f | CZ.PropLE f.1 b}
  zero_mem' := CZ.PropLE.zero b
  add_mem' {_ _} hf hg := (max_self b) ▸ CZ.PropLE.add hf hg

lemma PropLE'.mono {f : (Lpow l (Y.cz : AddCat)).Mor X Z} {b c : ℕ} (hf : PropLE' f b)
    (h : b ≤ c) : PropLE' f c := fun γ ↦ (hf γ).mono h

/-- Every morphism of `L^l(C_ℤ Y)` has finite propagation (finitely many coefficients). -/
lemma exists_propLE' (f : (Lpow l (Y.cz : AddCat)).Mor X Z) : ∃ b, PropLE' f b :=
  Lpow.exists_bound_coeff (D := (Y.cz : AddCat))
    (fun b (g : (Y.cz : AddCat).Mor X Z) ↦ CZ.PropLE (Subtype.val g) b) (fun h hg ↦ hg.mono h)
    (fun b ↦ CZ.PropLE.zero b) (fun g ↦ g.2) f

lemma PropLE'.add {f g : (Lpow l (Y.cz : AddCat)).Mor X Z} {b c : ℕ} (hf : PropLE' f b)
    (hg : PropLE' g c) : PropLE' (f + g) (max b c) := fun γ ↦ by
  rw [Lpow.coeff_add]
  exact (hf γ).add (hg γ)

lemma PropLE'.neg {f : (Lpow l (Y.cz : AddCat)).Mor X Z} {b : ℕ} (hf : PropLE' f b) :
    PropLE' (-f) b := fun γ ↦ by
  rw [Lpow.coeff_neg]
  exact fun w v h ↦ by rw [CZ.neg_apply, hf γ w v h, neg_zero]

lemma PropLE'.sub {f g : (Lpow l (Y.cz : AddCat)).Mor X Z} {b c : ℕ} (hf : PropLE' f b)
    (hg : PropLE' g c) : PropLE' (f - g) (max b c) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

lemma PropLE'.comp {f : (Lpow l (Y.cz : AddCat)).Mor X Z} {g : (Lpow l (Y.cz : AddCat)).Mor Z T}
    {b c : ℕ} (hf : PropLE' f b) (hg : PropLE' g c) : PropLE' (f ≫ g) (b + c) :=
  Lpow.coeff_comp_mem f g (propLESubmonoid X T (b + c)) fun α β ↦ (hf α).matComp (hg β)

lemma propLE'_incl {X Z : Y.cz} (a : X ⟶ Z) {b : ℕ} (ha : CZ.PropLE a.1 b) :
    PropLE' ((Lpow.incl (Y.cz : AddCat) l).map a) b := fun γ ↦ by
  rw [Lpow.coeff_incl]
  split_ifs
  · exact ha
  · exact CZ.PropLE.zero b

/-! ### Degree-`0` cut idempotents -/

/-- The degree-`0` cut idempotent `χ_p = ι (cut X p).idem` on `X`. -/
def chi (X : Lpow l (Y.cz : AddCat)) (p : ℤ → Prop) [DecidablePred p] :
    (Lpow l (Y.cz : AddCat)).Mor X X :=
  (Lpow.incl (Y.cz : AddCat) l).map (CZ.cut X p).idem

variable (p p' : ℤ → Prop) [DecidablePred p] [DecidablePred p']

lemma cut_idem_idem (X : Y.cz) : (CZ.cut X p).idem ≫ (CZ.cut X p).idem = (CZ.cut X p).idem :=
  SplitKar.idem_idem _

lemma chi_idem (X : Lpow l (Y.cz : AddCat)) : chi X p ≫ chi X p = chi X p := by
  rw [chi, ← Functor.map_comp, cut_idem_idem]

variable {p p'}

lemma chi_comp_chi_of_le (X : Lpow l (Y.cz : AddCat)) (h : ∀ v, p v → p' v) :
    chi X p ≫ chi X p' = chi X p := by
  rw [chi, chi, ← Functor.map_comp, (CZ.idemLE_cut X h).1]

lemma chi_comp_chi_of_le' (X : Lpow l (Y.cz : AddCat)) (h : ∀ v, p v → p' v) :
    chi X p' ≫ chi X p = chi X p := by
  rw [chi, chi, ← Functor.map_comp, (CZ.idemLE_cut X h).2]

/-- In `𝒞`: a map of propagation `b` out of `X|_p` lands in `p'` if `p'` contains the
`b`-thickening of `p`. -/
lemma cut_comp_eq_base {X Z : Y.cz} (g : X ⟶ Z) {b : ℕ} (hg : CZ.PropLE g.1 b)
    (h : ∀ v w, p v → |w - v| ≤ b → p' w) :
    (CZ.cut X p).idem ≫ g ≫ (CZ.cut Z p').idem = (CZ.cut X p).idem ≫ g := by
  rw [← assoc]
  refine CZ.comp_cut_idem _ p' fun w v hw ↦ ?_
  rw [CZ.cut_idem, CZ.diag_comp_apply]
  by_cases hv : p v
  · rw [ite_eq_left hv, id_comp]
    exact hg w v (lt_of_not_ge fun hle ↦ hw (h v w hv hle))
  · rw [ite_eq_right hv, zero_comp]

/-- In `𝒞`: a map of propagation `b` into `Z|_p` comes from `p'` if `p'` contains the
`b`-thickening of `p`. -/
lemma comp_cut_eq_base {X Z : Y.cz} (g : X ⟶ Z) {b : ℕ} (hg : CZ.PropLE g.1 b)
    (h : ∀ v w, p v → |w - v| ≤ b → p' w) :
    (CZ.cut X p').idem ≫ g ≫ (CZ.cut Z p).idem = g ≫ (CZ.cut Z p).idem := by
  refine CZ.cut_idem_comp _ p' fun w v hv ↦ ?_
  rw [CZ.cut_idem, CZ.comp_diag_apply]
  by_cases hw : p w
  · rw [ite_eq_left hw, comp_id]
    refine hg w v (lt_of_not_ge fun hle ↦ hv (h w v hw ?_))
    rwa [abs_sub_comm]
  · rw [ite_eq_right hw, comp_zero]

/-- A map of propagation `b` out of `X|_p` lands in `p'` (`p' ⊇` the `b`-thickening of `p`). -/
lemma chi_comp_eq {g : (Lpow l (Y.cz : AddCat)).Mor X Z} {b : ℕ} (hg : PropLE' g b)
    (h : ∀ v w, p v → |w - v| ≤ b → p' w) : chi X p ≫ g ≫ chi Z p' = chi X p ≫ g :=
  Lpow.ext fun γ ↦ by
    rw [chi, chi, Lpow.coeff_incl_comp, Lpow.coeff_comp_incl, Lpow.coeff_incl_comp,
      cut_comp_eq_base _ (hg γ) h]

/-- A map of propagation `b` into `Z|_p` comes from `p'` (`p' ⊇` the `b`-thickening of `p`). -/
lemma comp_chi_eq {g : (Lpow l (Y.cz : AddCat)).Mor X Z} {b : ℕ} (hg : PropLE' g b)
    (h : ∀ v w, p v → |w - v| ≤ b → p' w) : chi X p' ≫ g ≫ chi Z p = g ≫ chi Z p :=
  Lpow.ext fun γ ↦ by
    rw [chi, chi, Lpow.coeff_incl_comp, Lpow.coeff_comp_incl, comp_cut_eq_base _ (hg γ) h]

/-! ### Supports -/

variable (p) in
/-- `f` is supported in `p × p`: `χ_p ≫ f ≫ χ_p = f`. -/
def SuppIn (f : (Lpow l (Y.cz : AddCat)).Mor X Z) : Prop := chi X p ≫ f ≫ chi Z p = f

lemma SuppIn.comp_chi {f : (Lpow l (Y.cz : AddCat)).Mor X Z} (hf : SuppIn p f) :
    f ≫ chi Z p = f := by
  rw [← hf]; simp only [assoc, chi_idem]

lemma SuppIn.chi_comp {f : (Lpow l (Y.cz : AddCat)).Mor X Z} (hf : SuppIn p f) :
    chi X p ≫ f = f := by
  rw [← hf, ← assoc, chi_idem]

lemma SuppIn.mono {f : (Lpow l (Y.cz : AddCat)).Mor X Z} (hf : SuppIn p f)
    (h : ∀ v, p v → p' v) : SuppIn p' f := by
  have h₁ : chi X p' ≫ f = f := by
    rw [← hf.chi_comp, ← assoc, chi_comp_chi_of_le' X h]
  have h₂ : f ≫ chi Z p' = f := by
    rw [← hf.comp_chi, assoc, chi_comp_chi_of_le Z h]
  rw [SuppIn, h₂, h₁]

lemma SuppIn.zero : SuppIn p (0 : (Lpow l (Y.cz : AddCat)).Mor X Z) := by
  simp [SuppIn]

lemma SuppIn.add {f g : (Lpow l (Y.cz : AddCat)).Mor X Z} (hf : SuppIn p f) (hg : SuppIn p g) :
    SuppIn p (f + g) := by
  rw [SuppIn, add_comp, comp_add, hf, hg]

lemma SuppIn.neg {f : (Lpow l (Y.cz : AddCat)).Mor X Z} (hf : SuppIn p f) : SuppIn p (-f) := by
  rw [SuppIn, neg_comp, comp_neg, hf]

lemma SuppIn.sub {f g : (Lpow l (Y.cz : AddCat)).Mor X Z} (hf : SuppIn p f) (hg : SuppIn p g) :
    SuppIn p (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

/-- `SuppIn p f` and `g` of propagation `b`: `f ≫ g` is supported in any `p' ⊇ p` containing the
`b`-thickening of `p`. -/
lemma SuppIn.comp_right {f : (Lpow l (Y.cz : AddCat)).Mor X Z}
    {g : (Lpow l (Y.cz : AddCat)).Mor Z T} (hf : SuppIn p f) {b : ℕ} (hg : PropLE' g b)
    (hpp' : ∀ v, p v → p' v) (h : ∀ v w, p v → |w - v| ≤ b → p' w) : SuppIn p' (f ≫ g) := by
  have h₁ : chi X p' ≫ f = f := by
    rw [← hf.chi_comp, ← assoc, chi_comp_chi_of_le' X hpp']
  have h₂ : f ≫ g ≫ chi T p' = f ≫ g := by
    conv_lhs => rw [← hf.comp_chi]
    rw [assoc, chi_comp_eq hg h, ← assoc, hf.comp_chi]
  rw [SuppIn, assoc, ← assoc (chi X p'), h₁, h₂]

/-- `SuppIn p f` and `g` of propagation `b`: `g ≫ f` is supported in any `p' ⊇ p` containing the
`b`-thickening of `p`. -/
lemma SuppIn.comp_left {f : (Lpow l (Y.cz : AddCat)).Mor Z T}
    {g : (Lpow l (Y.cz : AddCat)).Mor X Z} (hf : SuppIn p f) {b : ℕ} (hg : PropLE' g b)
    (hpp' : ∀ v, p v → p' v) (h : ∀ v w, p v → |w - v| ≤ b → p' w) : SuppIn p' (g ≫ f) := by
  have h₁ : f ≫ chi T p' = f := by
    rw [← hf.comp_chi, assoc, chi_comp_chi_of_le T hpp']
  have h₂ : chi X p' ≫ g ≫ f = g ≫ f := by
    conv_lhs => rw [← hf.chi_comp]
    rw [← assoc g, ← assoc, comp_chi_eq hg h, assoc, hf.chi_comp]
  rw [SuppIn, assoc, h₁, h₂]

/-! ### Left- and right-supported maps -/

/-- `f` is **left-supported**: supported in `(-∞, c]²` for some `c`. -/
def LeftSupp (f : (Lpow l (Y.cz : AddCat)).Mor X Z) : Prop := ∃ c : ℤ, SuppIn (· ≤ c) f

/-- `f` is **right-supported**: supported in `[c, ∞)²` for some `c`. -/
def RightSupp (f : (Lpow l (Y.cz : AddCat)).Mor X Z) : Prop := ∃ c : ℤ, SuppIn (c ≤ ·) f

namespace LeftSupp

lemma zero : LeftSupp (0 : (Lpow l (Y.cz : AddCat)).Mor X Z) := ⟨0, SuppIn.zero⟩

lemma add {f g : (Lpow l (Y.cz : AddCat)).Mor X Z} (hf : LeftSupp f) (hg : LeftSupp g) :
    LeftSupp (f + g) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨d, hd⟩ := hg
  exact ⟨max c d, (hc.mono fun v hv ↦ le_max_of_le_left hv).add
    (hd.mono fun v hv ↦ le_max_of_le_right hv)⟩

lemma neg {f : (Lpow l (Y.cz : AddCat)).Mor X Z} (hf : LeftSupp f) : LeftSupp (-f) :=
  let ⟨c, hc⟩ := hf; ⟨c, hc.neg⟩

lemma sub {f g : (Lpow l (Y.cz : AddCat)).Mor X Z} (hf : LeftSupp f) (hg : LeftSupp g) :
    LeftSupp (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

/-- Left-supported maps form a right ideal. -/
lemma comp_right {f : (Lpow l (Y.cz : AddCat)).Mor X Z} (hf : LeftSupp f)
    (g : (Lpow l (Y.cz : AddCat)).Mor Z T) : LeftSupp (f ≫ g) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨b, hb⟩ := exists_propLE' g
  exact ⟨c + b, hc.comp_right hb (fun v hv ↦ by omega) fun v w hv hw ↦ by
    have := (abs_le.mp hw).2; omega⟩

/-- Left-supported maps form a left ideal. -/
lemma comp_left {f : (Lpow l (Y.cz : AddCat)).Mor Z T} (hf : LeftSupp f)
    (g : (Lpow l (Y.cz : AddCat)).Mor X Z) : LeftSupp (g ≫ f) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨b, hb⟩ := exists_propLE' g
  exact ⟨c + b, hc.comp_left hb (fun v hv ↦ by omega) fun v w hv hw ↦ by
    have := (abs_le.mp hw).2; omega⟩

end LeftSupp

namespace RightSupp

lemma zero : RightSupp (0 : (Lpow l (Y.cz : AddCat)).Mor X Z) := ⟨0, SuppIn.zero⟩

lemma add {f g : (Lpow l (Y.cz : AddCat)).Mor X Z} (hf : RightSupp f) (hg : RightSupp g) :
    RightSupp (f + g) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨d, hd⟩ := hg
  exact ⟨min c d, (hc.mono fun v hv ↦ min_le_of_left_le hv).add
    (hd.mono fun v hv ↦ min_le_of_right_le hv)⟩

lemma neg {f : (Lpow l (Y.cz : AddCat)).Mor X Z} (hf : RightSupp f) : RightSupp (-f) :=
  let ⟨c, hc⟩ := hf; ⟨c, hc.neg⟩

lemma sub {f g : (Lpow l (Y.cz : AddCat)).Mor X Z} (hf : RightSupp f) (hg : RightSupp g) :
    RightSupp (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

/-- Right-supported maps form a right ideal. -/
lemma comp_right {f : (Lpow l (Y.cz : AddCat)).Mor X Z} (hf : RightSupp f)
    (g : (Lpow l (Y.cz : AddCat)).Mor Z T) : RightSupp (f ≫ g) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨b, hb⟩ := exists_propLE' g
  exact ⟨c - b, hc.comp_right hb (fun v hv ↦ by omega) fun v w hv hw ↦ by
    have := (abs_le.mp hw).1; omega⟩

/-- Right-supported maps form a left ideal. -/
lemma comp_left {f : (Lpow l (Y.cz : AddCat)).Mor Z T} (hf : RightSupp f)
    (g : (Lpow l (Y.cz : AddCat)).Mor X Z) : RightSupp (g ≫ f) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨b, hb⟩ := exists_propLE' g
  exact ⟨c - b, hc.comp_left hb (fun v hv ↦ by omega) fun v w hv hw ↦ by
    have := (abs_le.mp hw).1; omega⟩

end RightSupp

/-! ### Transfer to `L^{l+1}(C_ℤ Y)` along the old variables -/

lemma extend_chi (X : Lpow l (Y.cz : AddCat)) (p : ℤ → Prop) [DecidablePred p] :
    (Lpow.extend (Y.cz : AddCat) l).map (chi X p) = chi (l := l + 1) X p :=
  Lpow.extend_incl l _

lemma PropLE'.extend {f : (Lpow l (Y.cz : AddCat)).Mor X Z} {b : ℕ} (hf : PropLE' f b) :
    PropLE' (l := l + 1) ((Lpow.extend (Y.cz : AddCat) l).map f) b := fun γ ↦ by
  rw [← Fin.cons_self_tail γ, Lpow.coeff_extend]
  split_ifs
  · exact hf _
  · exact CZ.PropLE.zero b

lemma SuppIn.extend {p : ℤ → Prop} [DecidablePred p] {f : (Lpow l (Y.cz : AddCat)).Mor X Z}
    (hf : SuppIn p f) : SuppIn (l := l + 1) p ((Lpow.extend (Y.cz : AddCat) l).map f) := by
  change chi (l := l + 1) X p ≫ (Lpow.extend _ l).map f ≫ chi (l := l + 1) Z p = _
  rw [← extend_chi X p, ← extend_chi Z p, ← Functor.map_comp, ← Functor.map_comp, hf]

lemma LeftSupp.extend {f : (Lpow l (Y.cz : AddCat)).Mor X Z} (hf : LeftSupp f) :
    LeftSupp (l := l + 1) ((Lpow.extend (Y.cz : AddCat) l).map f) :=
  let ⟨c, hc⟩ := hf; ⟨c, hc.extend⟩

lemma RightSupp.extend {f : (Lpow l (Y.cz : AddCat)).Mor X Z} (hf : RightSupp f) :
    RightSupp (l := l + 1) ((Lpow.extend (Y.cz : AddCat) l).map f) :=
  let ⟨c, hc⟩ := hf; ⟨c, hc.extend⟩

lemma PropLE'.w (n : ℤ) (X : Lpow (l + 1) (Y.cz : AddCat)) :
    PropLE' (Lpow.w l n X) 0 := fun γ ↦ by
  rw [← Fin.cons_self_tail γ, Lpow.coeff_cons, Lpow.w, Lpow.coeff_incl]
  split_ifs
  · rw [Laurent.T, Laurent.coeff_single]
    split_ifs
    · exact CZ.propLE_diagMat _
    · exact CZ.PropLE.zero 0
  · rw [Laurent.coeff_zero]; exact CZ.PropLE.zero 0

/-! ### Lemma H: half-line absorption -/

variable (l) in
/-- **Lemma H** (negative half-line): every Kar object of `L^l 𝒞` on an object supported in a
half-line `(-∞, c]` is absorbed by a free object. -/
theorem karAbsorbs_lpow_of_negHalf {M : Lpow l (Y.cz : AddCat)} (hM : CZ.negHalf Y M)
    {e : (Lpow l (Y.cz : AddCat)).Mor M M} (he : e ≫ e = e) :
    ∃ F : Lpow l (Y.cz : AddCat), KarAbsorbs e F := by
  let ι : (Y.cz.sub (CZ.negHalf Y) : AddCat).carrier ⥤ (Y.cz : AddCat).carrier :=
    (Y.cz.subIncl (CZ.negHalf Y)).F
  let hFF : (Lpow.map l ι).FullyFaithful :=
    Lpow.fullyFaithfulMap l (F := ι) (ObjectProperty.fullyFaithfulι (CZ.negHalf Y))
  let M' : Lpow l (Y.czNeg : AddCat) := (⟨M, hM⟩ : (CZ.negHalf Y).FullSubcategory)
  let e' : (Lpow l (Y.czNeg : AddCat)).Mor M' M' := hFF.preimage e
  have he' : e' ≫ e' = e' := hFF.map_injective (by simp [e', he])
  have h := ((CZ.negSwindle Y).karAbsorbs_lpow l he').map (Lpow.map l ι)
  rw [hFF.map_preimage] at h
  exact ⟨_, h⟩

variable (l) in
/-- **Lemma H** (positive half-line). -/
theorem karAbsorbs_lpow_of_posHalf {M : Lpow l (Y.cz : AddCat)} (hM : CZ.posHalf Y M)
    {e : (Lpow l (Y.cz : AddCat)).Mor M M} (he : e ≫ e = e) :
    ∃ F : Lpow l (Y.cz : AddCat), KarAbsorbs e F := by
  let ι : (Y.cz.sub (CZ.posHalf Y) : AddCat).carrier ⥤ (Y.cz : AddCat).carrier :=
    (Y.cz.subIncl (CZ.posHalf Y)).F
  let hFF : (Lpow.map l ι).FullyFaithful :=
    Lpow.fullyFaithfulMap l (F := ι) (ObjectProperty.fullyFaithfulι (CZ.posHalf Y))
  let M' : Lpow l (Y.czPos : AddCat) := (⟨M, hM⟩ : (CZ.posHalf Y).FullSubcategory)
  let e' : (Lpow l (Y.czPos : AddCat)).Mor M' M' := hFF.preimage e
  have he' : e' ≫ e' = e' := hFF.map_injective (by simp [e', he])
  have h := ((CZ.posSwindle Y).karAbsorbs_lpow l he').map (Lpow.map l ι)
  rw [hFF.map_preimage] at h
  exact ⟨_, h⟩

/-- Free objects of `L^l 𝒞` are absorbed by free objects (Lemma D for `d = 1`, in degree `0`). -/
theorem karAbsorbs_lpow_id (X : Lpow l (Y.cz : AddCat)) :
    ∃ G : Lpow l (Y.cz : AddCat), KarAbsorbs (𝟙 X) G := by
  obtain ⟨G, hG⟩ := CZ.karAbsorbs_id (B := Y) X
  have h := hG.map (Lpow.incl (Y.cz : AddCat) l)
  rw [CategoryTheory.Functor.map_id] at h
  exact ⟨_, h⟩

/-- The restriction `ιE e πE` of an idempotent supported in `p × p` to the cut `X|_p` is
idempotent. -/
lemma cut_restrict_idem {M : Lpow l (Y.cz : AddCat)} {e : (Lpow l (Y.cz : AddCat)).Mor M M}
    (he : e ≫ e = e) (hs : SuppIn p e) :
    ((Lpow.incl (Y.cz : AddCat) l).map (CZ.cut M p).ιE ≫ e ≫
      (Lpow.incl (Y.cz : AddCat) l).map (CZ.cut M p).πE) ≫
    ((Lpow.incl (Y.cz : AddCat) l).map (CZ.cut M p).ιE ≫ e ≫
      (Lpow.incl (Y.cz : AddCat) l).map (CZ.cut M p).πE) =
    (Lpow.incl (Y.cz : AddCat) l).map (CZ.cut M p).ιE ≫ e ≫
      (Lpow.incl (Y.cz : AddCat) l).map (CZ.cut M p).πE := by
  have hχ : (Lpow.incl (Y.cz : AddCat) l).map (CZ.cut M p).πE ≫
      (Lpow.incl (Y.cz : AddCat) l).map (CZ.cut M p).ιE = chi M p := by
    rw [← Functor.map_comp]; rfl
  simp only [assoc]
  rw [reassoc_of% hχ, ← assoc (chi M p), hs.chi_comp, reassoc_of% he]

/-- An idempotent supported in `p × p` is Kar-isomorphic to its restriction to the cut
`X|_p`. -/
def karIsoCut {M : Lpow l (Y.cz : AddCat)} {e : (Lpow l (Y.cz : AddCat)).Mor M M}
    (he : e ≫ e = e) (hs : SuppIn p e) :
    Wall.KarIso e ((Lpow.incl (Y.cz : AddCat) l).map (CZ.cut M p).ιE ≫ e ≫
      (Lpow.incl (Y.cz : AddCat) l).map (CZ.cut M p).πE) := by
  have hχ : (Lpow.incl (Y.cz : AddCat) l).map (CZ.cut M p).πE ≫
      (Lpow.incl (Y.cz : AddCat) l).map (CZ.cut M p).ιE = chi M p := by
    rw [← Functor.map_comp]; rfl
  refine CZ.karIsoOfFactor he (cut_restrict_idem he hs)
    (e ≫ (Lpow.incl (Y.cz : AddCat) l).map (CZ.cut M p).πE)
    ((Lpow.incl (Y.cz : AddCat) l).map (CZ.cut M p).ιE ≫ e) ?_ ?_
  · simp only [assoc]
    rw [reassoc_of% hχ, hs.chi_comp, he]
  · simp only [assoc]
    rw [reassoc_of% he]

/-- **Left-supported idempotents are absorbed** (`blueprint/negK-high.md` §3.6, corollary). -/
theorem karAbsorbs_of_leftSupp {M : Lpow l (Y.cz : AddCat)} {e : (Lpow l (Y.cz : AddCat)).Mor M M}
    (he : e ≫ e = e) (hs : LeftSupp e) : ∃ F : Lpow l (Y.cz : AddCat), KarAbsorbs e F := by
  obtain ⟨c, hc⟩ := hs
  obtain ⟨F, hF⟩ := karAbsorbs_lpow_of_negHalf l (M := (CZ.cut M (· ≤ c)).E)
    ⟨c, fun v hv ↦ CZ.isZero_cut_E M _ (by omega)⟩ (cut_restrict_idem he hc)
  exact ⟨F, hF.of_karIso (karIsoCut he hc)⟩

/-- **Right-supported idempotents are absorbed.** -/
theorem karAbsorbs_of_rightSupp {M : Lpow l (Y.cz : AddCat)}
    {e : (Lpow l (Y.cz : AddCat)).Mor M M} (he : e ≫ e = e) (hs : RightSupp e) :
    ∃ F : Lpow l (Y.cz : AddCat), KarAbsorbs e F := by
  obtain ⟨c, hc⟩ := hs
  obtain ⟨F, hF⟩ := karAbsorbs_lpow_of_posHalf l (M := (CZ.cut M (c ≤ ·)).E)
    ⟨c, fun v hv ↦ CZ.isZero_cut_E M _ (by omega)⟩ (cut_restrict_idem he hc)
  exact ⟨F, hF.of_karIso (karIsoCut he hc)⟩

open ZeroObject

/-- Left-supported idempotents are stably zero. -/
theorem stablyIso_zero_of_leftSupp {M : Lpow l (Y.cz : AddCat)}
    {e : (Lpow l (Y.cz : AddCat)).Mor M M} (he : e ≫ e = e) (hs : LeftSupp e) :
    StablyIso (⟨M, e, he⟩ : Karoubi (Lpow l (Y.cz : AddCat)).carrier) 0 :=
  let ⟨_, hF⟩ := karAbsorbs_of_leftSupp he hs
  StablyIso.of_karAbsorbs (P := ⟨M, e, he⟩) hF

/-- Right-supported idempotents are stably zero. -/
theorem stablyIso_zero_of_rightSupp {M : Lpow l (Y.cz : AddCat)}
    {e : (Lpow l (Y.cz : AddCat)).Mor M M} (he : e ≫ e = e) (hs : RightSupp e) :
    StablyIso (⟨M, e, he⟩ : Karoubi (Lpow l (Y.cz : AddCat)).carrier) 0 :=
  let ⟨_, hF⟩ := karAbsorbs_of_rightSupp he hs
  StablyIso.of_karAbsorbs (P := ⟨M, e, he⟩) hF

end CZ.Lpow

end

end HSFormal.LTheory
