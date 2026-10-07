import HSFormal.LTheory.Model.Swindle

/-!
# Bounded objects of `C_ℤ(B)` and the window equivalence `C_ℤ^{bdd}(B) ≃ B`

Lower L-theory model, module 22 (`DecBij`), part 1 (`blueprint/lower-L-construction.md` §3.2
"H5 from NegK").  This file is independent of `LineComplex`/`Triads`.

* `CZ.bdd B`: the objects of `C_ℤ(B)` supported in a finite window (`posHalf ∧ negHalf`).  They
  form a replete additive subcategory closed under retracts; `InvCat.czBdd B` is the full
  sub-`InvCat`.  `CZ.bddFiltration B` is the Karoubi filtration of `C_ℤ(B)` by bounded objects
  (splittings: the self-dual window cuts `X = X|_{[-c, c]} ⊕ X|_{ℤ ∖ [-c, c]}`; a map of
  propagation `b` into or out of an object supported in `[a, c]` factors through the cut at
  `[a - b, c + b]`).  Its `sub` is `czBdd` by `rfl`; its quotient is the category of germs at
  both ends.  Bounded objects lie in both half-lines (`bddToPos`, `bddToNeg`).
* **The window equivalence.**  `CZ.Window.sumF : B.czBdd ⟶ B` sums the entries of a bounded
  object over its chosen support window with the iterated unitary biproducts `CZ.Tower`:
  `(ΣX) = ⊕_{lo X ≤ u ≤ hi X} X_u`, `(Σf) = ∑_{v, w} π_v f_{w v} ι_w`.  `CZ.Window.ofBase :
  B ⟶ B.czBdd` puts an object at position `0` (the `E`-part of the cut of the constant object
  at `{0}`).  Both are strict `InvFunctor`s, and there are unitary natural isomorphisms
  `ofBase ≫ sumF ≅ 𝟙` (`ofBaseSumIso`) and `sumF ≫ ofBase ≅ 𝟙` (`sumOfBaseIso`): the
  components are `X_u → ΣX` (resp. `ΣX → X_u`) assembled into a matrix supported in row `0`.
* `Lconc.czBddEquiv : Lconc B.czBdd N ≃+ Lconc B N` (H4 for `Lconc`, via
  `Lconc.map_eq_of_unitaryIso`).  `CZ.atZero : B ⟶ B.cz` is the inclusion at position `0`.

This realizes "the bounded-window category `≃ B` by summing entries" of the blueprint; a
Kar complex over `C_ℤ(B)` all of whose chain objects are bounded is a Kar complex over `B` up
to unitary isomorphism.
-/

namespace HSFormal.LTheory

open CategoryTheory Category Limits Preadditive HSFormal.Compression

noncomputable section

attribute [local implicit_reducible] CZ.cut CZ.diagSplitting

namespace CZ

variable {B : InvCat}

/-! ### Bounded objects -/

variable (B) in
/-- The objects of `C_ℤ(B)` supported in a finite window. -/
def bdd : ObjectProperty B.cz := fun X ↦ posHalf B X ∧ negHalf B X

lemma bdd_iff {X : B.cz} : bdd B X ↔ ∃ a c : ℤ, ∀ v, v < a ∨ c < v → IsZero (X.obj v) := by
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨c, hc⟩⟩
    exact ⟨a, c, fun v hv ↦ hv.elim (ha v) (hc v)⟩
  · rintro ⟨a, c, h⟩
    exact ⟨⟨a, fun v hv ↦ h v (Or.inl hv)⟩, ⟨c, fun v hv ↦ h v (Or.inr hv)⟩⟩

open ZeroObject in
instance : IsAdditiveSub (bdd B) where
  of_iso e h := ⟨(posHalf B).prop_of_iso e h.1, (negHalf B).prop_of_iso e h.2⟩
  exists_zero := ⟨zeroObj, isZero_of_forall fun _ ↦ isZero_zero _,
    ⟨0, fun _ _ ↦ isZero_zero _⟩, ⟨0, fun _ _ ↦ isZero_zero _⟩⟩
  biprod_mem b hb hX hY :=
    ⟨IsAdditiveSub.biprod_mem b hb hX.1 hY.1, IsAdditiveSub.biprod_mem b hb hX.2 hY.2⟩

instance : (bdd B).IsStableUnderRetracts where
  of_retract r h := ⟨posHalf_of_comp_eq_id r.i r.r r.retract h.1,
    negHalf_of_comp_eq_id r.i r.r r.retract h.2⟩

/-- A morphism whose matrix vanishes outside the target rows `[lo, hi]` factors through a bounded
object (the `E`-part of the cut of its target at `[lo, hi]`). -/
lemma factorsThrough_bdd_of_rows {X Y : B.cz} (f : X ⟶ Y) (lo hi : ℤ)
    (h : ∀ w v, w < lo ∨ hi < w → f.1 w v = 0) : FactorsThrough (bdd B) f :=
  ⟨(cut Y (fun v ↦ lo ≤ v ∧ v ≤ hi)).E,
    bdd_iff.2 ⟨lo, hi, fun v hv ↦ isZero_cut_E Y _ (by omega)⟩,
    f ≫ (cut Y (fun v ↦ lo ≤ v ∧ v ≤ hi)).πE, (cut Y (fun v ↦ lo ≤ v ∧ v ≤ hi)).ιE, by
      rw [assoc, ← Splitting.idem, comp_cut_idem f _ fun w v hw ↦ h w v (by omega)]⟩

/-- A morphism whose matrix vanishes outside the source columns `[lo, hi]` factors through a
bounded object. -/
lemma factorsThrough_bdd_of_cols {X Y : B.cz} (f : X ⟶ Y) (lo hi : ℤ)
    (h : ∀ w v, v < lo ∨ hi < v → f.1 w v = 0) : FactorsThrough (bdd B) f :=
  ⟨(cut X (fun v ↦ lo ≤ v ∧ v ≤ hi)).E,
    bdd_iff.2 ⟨lo, hi, fun v hv ↦ isZero_cut_E X _ (by omega)⟩,
    (cut X (fun v ↦ lo ≤ v ∧ v ≤ hi)).πE, (cut X (fun v ↦ lo ≤ v ∧ v ≤ hi)).ιE ≫ f, by
      rw [← assoc, ← Splitting.idem, cut_idem_comp f _ fun w v hv ↦ h w v (by omega)]⟩

variable (B) in
/-- **The bounded Karoubi filtration** `C_ℤ^{bdd}(B) ⊂ C_ℤ(B)` ([CP95, 1.27]): splittings
`X = X|_{[-c, c]} ⊕ X|_{ℤ ∖ [-c, c]}`; a map of propagation `b` into or out of an object
supported in `[a, c]` factors through the window cut at `[a - b, c + b]`.  Its `sub` is
`B.czBdd`; its quotient is the category of germs at `±∞`. -/
def bddFiltration : KaroubiFiltration B.cz :=
  cutFiltration (bdd B) (fun c v ↦ -c ≤ v ∧ v ≤ c)
    (fun X c ↦ bdd_iff.2 ⟨-c, c, fun v hv ↦ isZero_cut_E X _ (by omega)⟩)
    (fun c₁ c₂ ↦ ⟨max c₁ c₂, fun v h ↦ by omega, fun v h ↦ by omega⟩)
    (fun {W X} hW f ↦ by
      obtain ⟨a, c, hc⟩ := bdd_iff.1 hW
      obtain ⟨b, hb⟩ := f.2
      refine ⟨max (b - a) (c + b), fun w v hw ↦ ?_⟩
      by_cases h : (b : ℤ) < |w - v|
      · exact hb w v h
      · exact (hc v (by rw [not_lt, abs_le] at h; omega)).eq_of_src _ _)
    (fun {X W} hW f ↦ by
      obtain ⟨a, c, hc⟩ := bdd_iff.1 hW
      obtain ⟨b, hb⟩ := f.2
      refine ⟨max (b - a) (c + b), fun w v hv ↦ ?_⟩
      by_cases h : (b : ℤ) < |w - v|
      · exact hb w v h
      · exact (hc w (by rw [not_lt, abs_le] at h; omega)).eq_of_tgt _ _)

lemma bddFiltration_U : (bddFiltration B).U = bdd B := rfl

end CZ

/-- `C_ℤ^{bdd}(B)`: the full sub-`InvCat` of bounded objects of `C_ℤ(B)`. -/
abbrev InvCat.czBdd (B : InvCat) : InvCat := B.cz.sub (CZ.bdd B)

namespace CZ

variable {B : InvCat}

lemma bddFiltration_sub : (bddFiltration B).sub = B.czBdd := rfl

variable (B) in
/-- Bounded objects are in the positive half-line category. -/
def bddToPos : B.czBdd ⟶ B.czPos :=
  InvCat.subHom (bdd B) (posHalf B) (𝟙 B.cz) fun _ h ↦ h.1

variable (B) in
/-- Bounded objects are in the negative half-line category. -/
def bddToNeg : B.czBdd ⟶ B.czNeg :=
  InvCat.subHom (bdd B) (negHalf B) (𝟙 B.cz) fun _ h ↦ h.2

/-! ### Entries of cuts -/

lemma cut_πE_eq_diag (X : B.cz) (p : ℤ → Prop) [DecidablePred p] :
    (cut X p).πE = diag fun v ↦ (if p v then splitE (X.obj v) else splitU (X.obj v)).πE := rfl

lemma cut_ιE_eq_diag (X : B.cz) (p : ℤ → Prop) [DecidablePred p] :
    (cut X p).ιE = diag fun v ↦ (if p v then splitE (X.obj v) else splitU (X.obj v)).ιE := rfl

lemma cut_πU_eq_diag (X : B.cz) (p : ℤ → Prop) [DecidablePred p] :
    (cut X p).πU = diag fun v ↦ (if p v then splitE (X.obj v) else splitU (X.obj v)).πU := rfl

lemma cut_ιU_eq_diag (X : B.cz) (p : ℤ → Prop) [DecidablePred p] :
    (cut X p).ιU = diag fun v ↦ (if p v then splitE (X.obj v) else splitU (X.obj v)).ιU := rfl

lemma star_cut_πE (X : B.cz) (p : ℤ → Prop) [DecidablePred p] :
    B.cz.inv.star (cut X p).πE = (cut X p).ιE := by
  rw [← star_cut_ιE, B.cz.inv.star_star]

lemma star_cut_idem (X : B.cz) (p : ℤ → Prop) [DecidablePred p] :
    B.cz.inv.star (cut X p).idem = (cut X p).idem := by
  rw [Splitting.idem, B.cz.inv.star_comp, star_cut_ιE, star_cut_πE]

/-! ### The window sum `C_ℤ^{bdd}(B) ⟶ B` -/

namespace Window

/-- The chosen lower end of the support of a bounded object. -/
def lo (X : B.czBdd) : ℤ := Classical.choose X.property.1

/-- The chosen upper end of the support of a bounded object. -/
def hi (X : B.czBdd) : ℤ := Classical.choose X.property.2

lemma isZero_of_lt (X : B.czBdd) {v : ℤ} (h : v < lo X) : IsZero (X.obj.obj v) :=
  Classical.choose_spec X.property.1 v h

lemma isZero_of_gt (X : B.czBdd) {v : ℤ} (h : hi X < v) : IsZero (X.obj.obj v) :=
  Classical.choose_spec X.property.2 v h

lemma isZero_of_not_mem (X : B.czBdd) {v : ℤ} (h : ¬ (lo X ≤ v ∧ v ≤ hi X)) :
    IsZero (X.obj.obj v) := by
  by_cases h' : v < lo X
  · exact isZero_of_lt X h'
  · exact isZero_of_gt X (by omega)

/-- The support window `[lo X, hi X]`. -/
def supp (X : B.czBdd) : Finset ℤ := Finset.Icc (lo X) (hi X)

lemma mem_supp {X : B.czBdd} {v : ℤ} : v ∈ supp X ↔ lo X ≤ v ∧ v ≤ hi X := Finset.mem_Icc

lemma isZero_of_not_mem_supp (X : B.czBdd) {v : ℤ} (h : v ∉ supp X) : IsZero (X.obj.obj v) :=
  isZero_of_not_mem X (mem_supp.not.mp h)

/-- The number of summands. -/
def len (X : B.czBdd) : ℕ := (hi X - lo X + 1).toNat

/-- `ΣX = ⊕_{lo X ≤ u ≤ hi X} X_u`, a chosen iterated unitary sum. -/
def pt (X : B.czBdd) : B := Tower.obj X.obj.obj (lo X) (len X)

/-- The inclusion `X_u → ΣX` (zero outside the window). -/
def ι (X : B.czBdd) (u : ℤ) : X.obj.obj u ⟶ pt X := Tower.inc X.obj.obj (lo X) (len X) u

/-- The projection `ΣX → X_u`, the dual of `ι`. -/
def π (X : B.czBdd) (u : ℤ) : pt X ⟶ X.obj.obj u := B.inv.star (ι X u)

lemma star_π (X : B.czBdd) (u : ℤ) : B.inv.star (π X u) = ι X u := B.inv.star_star _

lemma star_ι (X : B.czBdd) (u : ℤ) : B.inv.star (ι X u) = π X u := rfl

@[reassoc (attr := simp)]
lemma ι_π_self (X : B.czBdd) (u : ℤ) : ι X u ≫ π X u = 𝟙 _ := by
  by_cases h : lo X ≤ u ∧ u ≤ hi X
  · exact Tower.inc_star_self _ _ _ h.1 (by unfold len; omega)
  · exact (isZero_of_not_mem X h).eq_of_src _ _

@[reassoc]
lemma ι_π_ne (X : B.czBdd) {u u' : ℤ} (h : u ≠ u') : ι X u ≫ π X u' = 0 :=
  Tower.inc_star_ne _ _ _ h

lemma total (X : B.czBdd) (T : Finset ℤ) (hT : supp X ⊆ T) :
    ∑ u ∈ T, π X u ≫ ι X u = 𝟙 (pt X) := by
  have hsub : Finset.Ico (lo X) (lo X + len X) ⊆ T := fun u hu ↦ by
    simp only [Finset.mem_Ico] at hu
    exact hT (mem_supp.2 ⟨hu.1, by unfold len at hu; omega⟩)
  rw [← Finset.sum_subset hsub fun u _ hu ↦ ?_]
  · exact Tower.total _ _ _
  · simp only [Finset.mem_Ico, not_and_or, not_le, not_lt] at hu
    have h0 : ι X u = 0 := Tower.inc_eq_zero _ _ _ hu
    rw [h0, comp_zero]

/-- The absorption rule `ι_a ≫ ∑_u π_u ≫ G_u = G_a` (for `T ⊇ supp X`). -/
lemma ι_comp_sum (X : B.czBdd) (a : ℤ) (T : Finset ℤ) (hT : supp X ⊆ T) {Q : B}
    (G : ∀ u, X.obj.obj u ⟶ Q) : ι X a ≫ ∑ u ∈ T, π X u ≫ G u = G a := by
  by_cases ha : a ∈ T
  · rw [comp_sum, Finset.sum_eq_single a
      (fun u _ hu ↦ by rw [ι_π_ne_assoc X (Ne.symm hu), zero_comp])
      (fun h ↦ absurd ha h), ι_π_self_assoc]
  · exact (isZero_of_not_mem_supp X fun h ↦ ha (hT h)).eq_of_src _ _

/-- The dual absorption rule `(∑_u G_u ≫ ι_u) ≫ π_a = G_a` (for `T ⊇ supp X`). -/
lemma sum_comp_π (X : B.czBdd) (a : ℤ) (T : Finset ℤ) (hT : supp X ⊆ T) {Q : B}
    (G : ∀ u, Q ⟶ X.obj.obj u) : (∑ u ∈ T, G u ≫ ι X u) ≫ π X a = G a := by
  by_cases ha : a ∈ T
  · rw [sum_comp, Finset.sum_eq_single a
      (fun u _ hu ↦ by rw [assoc, ι_π_ne X hu, comp_zero])
      (fun h ↦ absurd ha h), assoc, ι_π_self, comp_id]
  · exact (isZero_of_not_mem_supp X fun h ↦ ha (hT h)).eq_of_tgt _ _

/-- `π_a ≫ ι_a = 𝟙` if all other entries vanish. -/
lemma π_ι_eq_id (X : B.czBdd) (a : ℤ) (h : ∀ v, v ≠ a → IsZero (X.obj.obj v)) :
    π X a ≫ ι X a = 𝟙 (pt X) := by
  classical
  rw [← total X (insert a (supp X)) (Finset.subset_insert _ _), Finset.sum_eq_single a
    (fun u _ hu ↦ by rw [(h u hu).eq_of_tgt (π X u) 0, zero_comp])
    (fun h' ↦ absurd (Finset.mem_insert_self a _) h')]

/-- The window sum of a morphism, `Σf = ∑_{v, w} π_v f_{w v} ι_w`. -/
def sumHom {X Y : B.czBdd} (f : X ⟶ Y) : pt X ⟶ pt Y :=
  ∑ v ∈ supp X, ∑ w ∈ supp Y, π X v ≫ f.hom.1 w v ≫ ι Y w

lemma sumHom_eq {X Y : B.czBdd} (f : X ⟶ Y) (S T : Finset ℤ) (hS : supp X ⊆ S)
    (hT : supp Y ⊆ T) : sumHom f = ∑ v ∈ S, ∑ w ∈ T, π X v ≫ f.hom.1 w v ≫ ι Y w := by
  rw [sumHom, Finset.sum_subset hS fun v _ hv ↦ Finset.sum_eq_zero fun w _ ↦ by
    rw [(isZero_of_not_mem_supp X hv).eq_of_tgt (π X v) 0, zero_comp]]
  refine Finset.sum_congr rfl fun v _ ↦ Finset.sum_subset hT fun w _ hw ↦ ?_
  rw [(isZero_of_not_mem_supp Y hw).eq_of_src (ι Y w) 0, comp_zero, comp_zero]

@[reassoc]
lemma ι_sumHom {X Y : B.czBdd} (f : X ⟶ Y) (a : ℤ) :
    ι X a ≫ sumHom f = ∑ w ∈ supp Y, f.hom.1 w a ≫ ι Y w := by
  rw [sumHom]
  simp_rw [← comp_sum]
  exact ι_comp_sum X a _ subset_rfl (fun v ↦ ∑ w ∈ supp Y, f.hom.1 w v ≫ ι Y w)

@[reassoc]
lemma sumHom_π {X Y : B.czBdd} (f : X ⟶ Y) (a : ℤ) :
    sumHom f ≫ π Y a = ∑ v ∈ supp X, π X v ≫ f.hom.1 a v := by
  rw [sumHom, sum_comp]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [← sum_comp_π Y a _ subset_rfl (fun w ↦ π X v ≫ f.hom.1 w v)]
  simp only [assoc]

lemma sumHom_id (X : B.czBdd) : sumHom (𝟙 X) = 𝟙 (pt X) := by
  rw [← total X (supp X) subset_rfl, sumHom]
  refine Finset.sum_congr rfl fun v hv ↦ ?_
  rw [Finset.sum_eq_single v (fun w _ hw ↦ by
      change π X v ≫ (𝟙 X.obj : X.obj ⟶ X.obj).1 w v ≫ ι X w = 0
      rw [id_apply_ne _ (Ne.symm hw), zero_comp, comp_zero]) (fun h ↦ absurd hv h)]
  change π X v ≫ (𝟙 X.obj : X.obj ⟶ X.obj).1 v v ≫ ι X v = _
  rw [id_apply_self, id_comp]

lemma sumHom_comp {X Y Z : B.czBdd} (f : X ⟶ Y) (g : Y ⟶ Z) :
    sumHom (f ≫ g) = sumHom f ≫ sumHom g := by
  rw [sumHom, sumHom, sum_comp]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [sum_comp]
  simp only [assoc, ι_sumHom, comp_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  have e : (f.hom ≫ g.hom).1 u v = ∑ w ∈ supp Y, f.hom.1 w v ≫ g.hom.1 u w :=
    matComp_eq_sum (supp Y) fun w hw ↦ by
      rw [(isZero_of_not_mem_supp Y hw).eq_of_tgt (f.hom.1 w v) 0, zero_comp]
  change π X v ≫ (f.hom ≫ g.hom).1 u v ≫ ι Z u = _
  rw [e]
  simp only [sum_comp, comp_sum, assoc]

lemma sumHom_add {X Y : B.czBdd} (f g : X ⟶ Y) : sumHom (f + g) = sumHom f + sumHom g := by
  simp only [sumHom, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ ↦ Finset.sum_congr rfl fun w _ ↦ ?_
  change π X v ≫ (f.hom + g.hom).1 w v ≫ ι Y w = _
  rw [add_apply, add_comp, comp_add]

lemma sumHom_star {X Y : B.czBdd} (f : X ⟶ Y) :
    sumHom (B.czBdd.inv.star f) = B.inv.star (sumHom f) := by
  rw [sumHom, sumHom, star_finsetSum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [star_finsetSum]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  change π Y w ≫ B.inv.star (f.hom.1 w v) ≫ ι X v = _
  rw [B.inv.star_comp, B.inv.star_comp, star_π, star_ι, assoc]

variable (B) in
/-- **The window sum** `Σ : C_ℤ^{bdd}(B) ⟶ B`, `ΣX = ⊕_u X_u`, a strict `InvFunctor`. -/
@[implicit_reducible]
def sumF : B.czBdd ⟶ B where
  F :=
    { obj := pt
      map := sumHom
      map_id := sumHom_id
      map_comp := sumHom_comp }
  additive := ⟨fun {_ _ f g} ↦ sumHom_add f g⟩
  map_star := sumHom_star

@[simp] lemma sumF_obj (X : B.czBdd) : (sumF B).F.obj X = pt X := rfl

@[simp] lemma sumF_map {X Y : B.czBdd} (f : X ⟶ Y) : (sumF B).F.map f = sumHom f := rfl

/-! ### The inclusion at position `0` -/

/-- The constant object `(X)_{v ∈ ℤ}`. -/
@[implicit_reducible]
def constObj (X : B) : B.cz := ⟨fun _ ↦ X⟩

/-- The diagonal morphism of constant objects. -/
def constHom {X Y : B} (f : X ⟶ Y) : constObj X ⟶ constObj Y := diag fun _ ↦ f

/-- The splitting of the constant object at position `0`. -/
abbrev cut0 (X : B) : Splitting (constObj X) := cut (constObj X) (fun v ↦ v = 0)

/-- `X` placed at position `0`. -/
@[implicit_reducible]
def obj0 (X : B) : B.cz := (cut0 X).E

lemma isZero_obj0 (X : B) {v : ℤ} (h : v ≠ 0) : IsZero ((obj0 X).obj v) :=
  isZero_cut_E _ _ h

lemma bdd_obj0 (X : B) : bdd B (obj0 X) :=
  bdd_iff.2 ⟨0, 0, fun v hv ↦ isZero_obj0 X (by omega)⟩

lemma constHom_cut0_idem {X Y : B} (f : X ⟶ Y) :
    constHom f ≫ (cut0 Y).idem = (cut0 X).idem ≫ constHom f := by
  rw [cut_idem, cut_idem, constHom, diag_comp_diag, diag_comp_diag]
  exact diag_ext fun v ↦ by split_ifs <;> simp

/-- `f` placed at position `0`. -/
def hom0 {X Y : B} (f : X ⟶ Y) : obj0 X ⟶ obj0 Y := (cut0 X).ιE ≫ constHom f ≫ (cut0 Y).πE

lemma constHom_id (X : B) : constHom (𝟙 X) = 𝟙 (constObj X) := diag_id (constObj X)

lemma constHom_comp {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    constHom (f ≫ g) = constHom f ≫ constHom g := by
  rw [constHom, constHom, constHom, diag_comp_diag]

lemma hom0_id (X : B) : hom0 (𝟙 X) = 𝟙 (obj0 X) := by
  rw [hom0, constHom_id, id_comp]
  exact (cut0 X).ιE_πE

lemma hom0_comp {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) : hom0 (f ≫ g) = hom0 f ≫ hom0 g := by
  have h2 : (cut0 X).ιE ≫ (cut0 X).idem = (cut0 X).ιE := by
    rw [Splitting.idem, ← assoc, (cut0 X).ιE_πE, id_comp]
  rw [hom0, hom0, hom0, constHom_comp]
  simp only [assoc]
  rw [← assoc (cut0 Y).πE, ← Splitting.idem, show constHom f ≫ (cut0 Y).idem ≫ constHom g ≫
    (cut0 Z).πE = (cut0 X).idem ≫ constHom f ≫ constHom g ≫ (cut0 Z).πE by
      rw [← assoc, constHom_cut0_idem, assoc], reassoc_of% h2]

lemma hom0_add {X Y : B} (f g : X ⟶ Y) : hom0 (f + g) = hom0 f + hom0 g := by
  have h : constHom (f + g) = constHom f + constHom g := by
    rw [constHom, constHom, constHom, ← diag_add]
  simp [hom0, h, add_comp, comp_add]

lemma star_constHom {X Y : B} (f : X ⟶ Y) :
    B.cz.inv.star (constHom f) = constHom (B.inv.star f) := by
  rw [constHom, constHom, star_diag]

lemma hom0_star {X Y : B} (f : X ⟶ Y) : hom0 (B.inv.star f) = B.cz.inv.star (hom0 f) := by
  rw [hom0, hom0, B.cz.inv.star_comp, B.cz.inv.star_comp, star_constHom, star_cut_ιE,
    star_cut_πE, assoc]

variable (B) in
/-- **The inclusion at position `0`**, `B ⟶ C_ℤ^{bdd}(B)`, a strict `InvFunctor`. -/
@[implicit_reducible]
def ofBase : B ⟶ B.czBdd where
  F :=
    { obj := fun X ↦ ⟨obj0 X, bdd_obj0 X⟩
      map := fun f ↦ ObjectProperty.homMk (hom0 f)
      map_id := fun X ↦ ObjectProperty.hom_ext _ (hom0_id X)
      map_comp := fun f g ↦ ObjectProperty.hom_ext _ (hom0_comp f g) }
  additive := ⟨fun {_ _ f g} ↦ ObjectProperty.hom_ext _ (hom0_add f g)⟩
  map_star f := ObjectProperty.hom_ext _ (hom0_star f)

@[simp] lemma ofBase_obj_obj (X : B) : ((ofBase B).F.obj X).obj = obj0 X := rfl

@[simp] lemma ofBase_map_hom {X Y : B} (f : X ⟶ Y) : ((ofBase B).F.map f).hom = hom0 f := rfl

/-- The component `X ⟶ (X at 0)_0`. -/
def u0 (X : B) : X ⟶ (obj0 X).obj 0 := (cut0 X).πE.1 0 0

/-- The component `(X at 0)_0 ⟶ X`. -/
def u0' (X : B) : (obj0 X).obj 0 ⟶ X := (cut0 X).ιE.1 0 0

@[reassoc (attr := simp)]
lemma u0_u0' (X : B) : u0 X ≫ u0' X = 𝟙 X := by
  have h := congrArg (fun g ↦ g.1 0 0) (cut_idem (constObj X) (fun v ↦ v = 0))
  simp only [Splitting.idem, cut_πE_eq_diag, diag_comp_apply, diag_apply_self, if_true] at h
  rw [u0, u0', cut_πE_eq_diag, diag_apply_self]
  exact h

@[reassoc (attr := simp)]
lemma u0'_u0 (X : B) : u0' X ≫ u0 X = 𝟙 _ := by
  have h := congrArg (fun g ↦ g.1 0 0) (cut0 X).ιE_πE
  simp only [cut_ιE_eq_diag, diag_comp_apply] at h
  rw [u0, u0', cut_ιE_eq_diag, diag_apply_self]
  exact h.trans (id_apply_self _ _)

lemma star_u0' (X : B) : B.inv.star (u0' X) = u0 X := by
  have h := congrArg (fun g ↦ g.1 0 0) (star_cut_ιE (constObj X) (fun v ↦ v = 0))
  simpa [u0, u0'] using h

lemma hom0_apply_zero {X Y : B} (f : X ⟶ Y) : (hom0 f).1 0 0 = u0' X ≫ f ≫ u0 Y := by
  rw [hom0, cut_ιE_eq_diag, diag_comp_apply, constHom, diag_comp_apply, cut_πE_eq_diag,
    diag_apply_self, u0', u0, cut_ιE_eq_diag, cut_πE_eq_diag, diag_apply_self, diag_apply_self]

/-- `Σ f` computed over any windows outside of which the objects vanish. -/
lemma sumHom_eq_of_isZero {X Y : B.czBdd} (f : X ⟶ Y) (S T : Finset ℤ)
    (hS : ∀ v ∉ S, IsZero (X.obj.obj v)) (hT : ∀ w ∉ T, IsZero (Y.obj.obj w)) :
    sumHom f = ∑ v ∈ S, ∑ w ∈ T, π X v ≫ f.hom.1 w v ≫ ι Y w := by
  classical
  rw [sumHom_eq f (supp X ∪ S) (supp Y ∪ T) Finset.subset_union_left Finset.subset_union_left]
  symm
  rw [Finset.sum_subset Finset.subset_union_right fun v _ hv ↦ Finset.sum_eq_zero fun w _ ↦ by
    rw [(hS v hv).eq_of_tgt (π X v) 0, zero_comp]]
  refine Finset.sum_congr rfl fun v _ ↦ Finset.sum_subset Finset.subset_union_right
    fun w _ hw ↦ ?_
  rw [(hT w hw).eq_of_src (ι Y w) 0, comp_zero, comp_zero]

lemma isZero_ofBase_obj (X : B) {v : ℤ} (h : v ∉ ({0} : Finset ℤ)) :
    IsZero (((ofBase B).F.obj X).obj.obj v) :=
  isZero_obj0 X (by simpa using h)

lemma sumHom_ofBase {X Y : B} (f : X ⟶ Y) :
    sumHom ((ofBase B).F.map f) =
      π ((ofBase B).F.obj X) 0 ≫ (u0' X ≫ f ≫ u0 Y) ≫ ι ((ofBase B).F.obj Y) 0 := by
  rw [sumHom_eq_of_isZero _ {0} {0} (fun _ h ↦ isZero_ofBase_obj X h)
    (fun _ h ↦ isZero_ofBase_obj Y h)]
  simp only [Finset.sum_singleton, ofBase_map_hom, hom0_apply_zero]

variable (B) in
/-- **`ofBase ≫ Σ ≅ 𝟙`** (unitary): `Σ(X at 0) ≅ X` via `π_0`, `ι_0`. -/
def ofBaseSumIso : InvCat.UnitaryIso (ofBase B ≫ sumF B) (𝟙 B) where
  iso := NatIso.ofComponents
    (fun X ↦
      { hom := π ((ofBase B).F.obj X) 0 ≫ u0' X
        inv := u0 X ≫ ι ((ofBase B).F.obj X) 0
        hom_inv_id := by
          erw [assoc]
          erw [u0'_u0_assoc]
          exact π_ι_eq_id _ 0 fun v hv ↦ isZero_obj0 X hv
        inv_hom_id := by
          erw [assoc]
          erw [ι_π_self_assoc]
          exact u0_u0' X })
    (fun {X Y} f ↦ by
      change sumHom ((ofBase B).F.map f) ≫ π ((ofBase B).F.obj Y) 0 ≫ u0' Y =
        (π ((ofBase B).F.obj X) 0 ≫ u0' X) ≫ f
      rw [sumHom_ofBase]
      simp only [assoc]
      erw [ι_π_self_assoc, u0_u0', comp_id])
  star_hom X := by
    change B.inv.star (π ((ofBase B).F.obj X) 0 ≫ u0' X) = u0 X ≫ ι ((ofBase B).F.obj X) 0
    rw [B.inv.star_comp, star_u0', star_π]

/-! #### `Σ ≫ ofBase ≅ 𝟙` -/

/-- A bound for the support window. -/
def bound (X : B.czBdd) : ℕ := (hi X).toNat + (-lo X).toNat

/-- The row matrix `X ⟶ const(ΣX)`, `(w, v) ↦ [w = 0] ι_v`. -/
def rowMat (X : B.czBdd) : Mat X.obj (constObj (pt X)) := fun w v ↦ if w = 0 then ι X v else 0

/-- The column matrix `const(ΣX) ⟶ X`, `(w, v) ↦ [v = 0] π_w`. -/
def colMat (X : B.czBdd) : Mat (constObj (pt X)) X.obj := fun w v ↦ if v = 0 then π X w else 0

lemma propLE_rowMat (X : B.czBdd) : PropLE (rowMat X) (bound X) := fun w v h ↦ by
  unfold rowMat
  split_ifs with hw
  · subst hw
    by_cases hv : lo X ≤ v ∧ v ≤ hi X
    · exfalso
      rw [lt_abs] at h
      unfold bound at h
      omega
    · exact (isZero_of_not_mem X hv).eq_of_src _ _
  · rfl

lemma propLE_colMat (X : B.czBdd) : PropLE (colMat X) (bound X) := fun w v h ↦ by
  unfold colMat
  split_ifs with hv
  · subst hv
    by_cases hw : lo X ≤ w ∧ w ≤ hi X
    · exfalso
      rw [lt_abs] at h
      unfold bound at h
      omega
    · exact (isZero_of_not_mem X hw).eq_of_tgt _ _
  · rfl

/-- The row morphism `X ⟶ const(ΣX)`. -/
def rowHom (X : B.czBdd) : X.obj ⟶ constObj (pt X) := homMk (rowMat X) _ (propLE_rowMat X)

/-- The column morphism `const(ΣX) ⟶ X`. -/
def colHom (X : B.czBdd) : constObj (pt X) ⟶ X.obj := homMk (colMat X) _ (propLE_colMat X)

lemma star_rowHom (X : B.czBdd) : B.cz.inv.star (rowHom X) = colHom X := by
  ext w v
  change B.inv.star (rowMat X v w) = colMat X w v
  unfold rowMat colMat
  split_ifs <;> simp [star_ι]

lemma rowHom_colHom (X : B.czBdd) : rowHom X ≫ colHom X = 𝟙 X.obj := by
  ext w v
  rw [comp_apply, rowHom, colHom]
  change matComp (rowMat X) (colMat X) w v = _
  rw [matComp_eq_sum {0} fun u hu ↦ by
    simp only [rowMat, if_neg (show u ≠ 0 by simpa using hu), zero_comp]]
  simp only [Finset.sum_singleton, rowMat, colMat, if_true]
  by_cases h : v = w
  · subst h; rw [ι_π_self, id_apply_self]
  · rw [ι_π_ne X h, id_apply_ne _ h]

lemma colHom_rowHom (X : B.czBdd) : colHom X ≫ rowHom X = (cut0 (pt X)).idem := by
  ext w v
  rw [comp_apply, rowHom, colHom, cut_idem]
  change matComp (colMat X) (rowMat X) w v = _
  rw [matComp_eq_sum (supp X) fun u hu ↦ by
    simp only [colMat, rowMat]
    split_ifs <;> simp [(isZero_of_not_mem_supp X hu).eq_of_tgt (π X u) 0]]
  simp only [colMat, rowMat]
  by_cases h : v = w
  · subst h
    rw [diag_apply_self]
    split_ifs with h0
    · exact total X _ subset_rfl
    · simp
  · rw [diag_apply_ne _ h]
    refine Finset.sum_eq_zero fun u _ ↦ ?_
    split_ifs <;> first | (exfalso; omega) | simp

@[reassoc]
lemma rowHom_cut0_idem (X : B.czBdd) : rowHom X ≫ (cut0 (pt X)).idem = rowHom X :=
  comp_cut_idem _ _ fun w v hw ↦ by simp [rowHom, rowMat, hw]

@[reassoc]
lemma cut0_idem_colHom (X : B.czBdd) : (cut0 (pt X)).idem ≫ colHom X = colHom X :=
  cut_idem_comp _ _ fun w v hv ↦ by simp [colHom, colMat, hv]

/-- `ΣX` at position `0`, back to `X`: `(w, ·) ↦ π_w`. -/
def fromSum (X : B.czBdd) : obj0 (pt X) ⟶ X.obj := (cut0 (pt X)).ιE ≫ colHom X

/-- `X ⟶ ΣX` at position `0`: `(·, v) ↦ ι_v`. -/
def toSum (X : B.czBdd) : X.obj ⟶ obj0 (pt X) := rowHom X ≫ (cut0 (pt X)).πE

lemma toSum_fromSum (X : B.czBdd) : toSum X ≫ fromSum X = 𝟙 X.obj := by
  rw [toSum, fromSum, assoc, ← assoc (cut0 _).πE, ← Splitting.idem, rowHom_cut0_idem_assoc,
    rowHom_colHom]

lemma fromSum_toSum (X : B.czBdd) : fromSum X ≫ toSum X = 𝟙 _ := by
  rw [toSum, fromSum, assoc, reassoc_of% colHom_rowHom, Splitting.idem]
  rw [← assoc, ← assoc, Splitting.ιE_πE]
  erw [id_comp]
  exact Splitting.ιE_πE _

lemma star_fromSum (X : B.czBdd) : B.cz.inv.star (fromSum X) = toSum X := by
  rw [fromSum, B.cz.inv.star_comp, ← star_rowHom, B.cz.inv.star_star, star_cut_ιE, toSum]

lemma constHom_colHom {X Y : B.czBdd} (f : X ⟶ Y) :
    constHom (sumHom f) ≫ colHom Y = colHom X ≫ f.hom := by
  ext w v
  rw [constHom, diag_comp_apply, comp_apply, colHom, colHom]
  change sumHom f ≫ colMat Y w v = matComp (colMat X) f.hom.1 w v
  rw [matComp_eq_sum (supp X) fun u hu ↦ by
    simp only [colMat]
    split_ifs <;> simp [(isZero_of_not_mem_supp X hu).eq_of_tgt (π X u) 0]]
  simp only [colMat]
  split_ifs with h
  · rw [sumHom_π]
  · simp

variable (B) in
/-- **`Σ ≫ ofBase ≅ 𝟙`** (unitary): `X ≅ (ΣX at 0)` via the row/column matrices of the `ι_v`,
`π_w`. -/
def sumOfBaseIso : InvCat.UnitaryIso (sumF B ≫ ofBase B) (𝟙 B.czBdd) where
  iso := NatIso.ofComponents
    (fun X ↦
      { hom := ObjectProperty.homMk (fromSum X)
        inv := ObjectProperty.homMk (toSum X)
        hom_inv_id := ObjectProperty.hom_ext _ (fromSum_toSum X)
        inv_hom_id := ObjectProperty.hom_ext _ (toSum_fromSum X) })
    (fun {X Y} f ↦ ObjectProperty.hom_ext _ (by
      change hom0 (sumHom f) ≫ fromSum Y = fromSum X ≫ f.hom
      rw [hom0, fromSum, fromSum]
      simp only [assoc]
      rw [← assoc (cut0 (pt Y)).πE, ← Splitting.idem, cut0_idem_colHom, constHom_colHom]))
  star_hom X := ObjectProperty.hom_ext _ (star_fromSum X)

end Window

/-- The inclusion `B ⟶ C_ℤ(B)` at position `0`. -/
abbrev atZero (B : InvCat) : B ⟶ B.cz := Window.ofBase B ≫ B.cz.subIncl (bdd B)

end CZ

/-! ### `Lconc` of the bounded category -/

namespace Lconc

variable (B : InvCat) (N : ℤ)

/-- **`Lconc (C_ℤ^{bdd} B) N ≅ Lconc B N`** via the window sum (inverse: inclusion at `0`). -/
def czBddEquiv : Lconc B.czBdd N ≃+ Lconc B N where
  toFun := map (CZ.Window.sumF B)
  invFun := map (CZ.Window.ofBase B)
  left_inv x := by
    rw [← AddMonoidHom.comp_apply, ← map_comp, map_eq_of_unitaryIso (CZ.Window.sumOfBaseIso B),
      map_id, AddMonoidHom.id_apply]
  right_inv x := by
    rw [← AddMonoidHom.comp_apply, ← map_comp, map_eq_of_unitaryIso (CZ.Window.ofBaseSumIso B),
      map_id, AddMonoidHom.id_apply]
  map_add' := map_add _

@[simp]
lemma czBddEquiv_apply (x : Lconc B.czBdd N) : czBddEquiv B N x = map (CZ.Window.sumF B) x := rfl

@[simp]
lemma czBddEquiv_symm_apply (x : Lconc B N) :
    (czBddEquiv B N).symm x = map (CZ.Window.ofBase B) x := rfl

end Lconc

end

end HSFormal.LTheory
